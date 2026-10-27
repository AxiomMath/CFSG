module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.Quasithin

namespace SBd5

open Matrix

section Field2

variable {F : Type} [Field F] [Fintype F]

theorem eq_zero_or_one_of_card_two (hF : Fintype.card F = 2) (x : F) : x = 0 ∨ x = 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hx0, hx1⟩ := h
  have h3 : ({0, 1, x} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hx1.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, hx0.symm⟩
  have := Finset.card_le_univ ({0, 1, x} : Finset F)
  omega

theorem schur_vec (hF : Fintype.card F = 2) (Φ : (Fin 3 → F) →+ (Fin 3 → F))
    (hΦ : ∀ g : SpecialLinearGroup (Fin 3) F, ∀ x : Fin 3 → F,
      Φ ((g : Matrix (Fin 3) (Fin 3) F).mulVec x) = (g : Matrix (Fin 3) (Fin 3) F).mulVec (Φ x)) :
    ∃ c : F, ∀ x, Φ x = c • x := by
  classical
  let Φl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := Φ
      map_add' := Φ.map_add
      map_smul' := fun r x => by
        rcases eq_zero_or_one_of_card_two hF r with rfl | rfl
        · simp
        · simp }
  have hMx : ∀ x, (LinearMap.toMatrix' Φl).mulVec x = Φ x := fun x => LinearMap.toMatrix'_mulVec Φl x
  have hcomm : ∀ t : TransvectionStruct (Fin 3) F, Commute t.toMatrix (LinearMap.toMatrix' Φl) := by
    intro t
    let g : SpecialLinearGroup (Fin 3) F := ⟨t.toMatrix, t.det⟩
    refine Matrix.ext_of_mulVec_single (fun i => ?_)
    have h1 := hΦ g (Pi.single i 1)
    show (t.toMatrix * LinearMap.toMatrix' Φl) *ᵥ Pi.single i 1 =
      (LinearMap.toMatrix' Φl * t.toMatrix) *ᵥ Pi.single i 1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hMx, hMx]
    exact h1.symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct hcomm
  refine ⟨c, fun x => ?_⟩
  rw [← hMx x, ← hc]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem block_structure (hF : Fintype.card F = 2) {k : ℕ}
    (Φ : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F))
    (hΦ : ∀ g : SpecialLinearGroup (Fin 3) F, ∀ x : Fin k → Fin 3 → F,
      Φ (fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (x i)) =
        fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (Φ x i)) :
    ∃ φ : Matrix (Fin k) (Fin k) F, ∀ (x : Fin k → Fin 3 → F) (i : Fin k),
      Φ x i = ∑ j, φ i j • x j := by
  classical
  have key : ∀ i j : Fin k, ∃ c : F, ∀ v : Fin 3 → F, Φ (Pi.single j v) i = c • v := by
    intro i j
    let Φij : (Fin 3 → F) →+ (Fin 3 → F) :=
      (Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i).comp
        (Φ.comp (AddMonoidHom.single (fun _ : Fin k => Fin 3 → F) j))
    have hij : ∀ (g : SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F),
        Φij ((g : Matrix (Fin 3) (Fin 3) F).mulVec v) =
          (g : Matrix (Fin 3) (Fin 3) F).mulVec (Φij v) := by
      intro g v
      have h1 := hΦ g (Pi.single j v)
      have h2 : (fun l => (g : Matrix (Fin 3) (Fin 3) F).mulVec ((Pi.single j v : Fin k → Fin 3 → F) l)) =
          Pi.single j ((g : Matrix (Fin 3) (Fin 3) F).mulVec v) := by
        funext l
        by_cases hl : l = j
        · subst hl; simp
        · simp [Pi.single_eq_of_ne hl]
      rw [h2] at h1
      exact congrFun h1 i
    obtain ⟨c, hc⟩ := schur_vec hF Φij hij
    exact ⟨c, hc⟩
  choose c hc using key
  refine ⟨Matrix.of c, fun x i => ?_⟩
  have hx : x = ∑ j, Pi.single j (x j) := (Finset.univ_sum_single x).symm
  conv_lhs => rw [hx]
  rw [map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hc i j (x j))

set_option maxRecDepth 4000 in
theorem zmod2_pow_six : ∀ φ : Matrix (Fin 2) (Fin 2) (ZMod 2), φ.det ≠ 0 → φ ^ 6 = 1 := by decide

set_option maxRecDepth 4000 in
theorem zmod2_pow_three : ∀ φ : Matrix (Fin 2) (Fin 2) (ZMod 2), φ ^ 3 = 1 →
    φ = 1 ∨ ∀ w : Fin 2 → ZMod 2, φ.mulVec w = w → w = 0 := by decide

theorem mat2_odd_pow (hF : Fintype.card F = 2) {m : ℕ} (hm : Odd m) (φ : Matrix (Fin 2) (Fin 2) F)
    (h : φ ^ m = 1) : φ = 1 ∨ ∀ w : Fin 2 → F, φ.mulVec w = w → w = 0 := by
  classical
  let e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])
  let ψ : Matrix (Fin 2) (Fin 2) (ZMod 2) := e.mapMatrix φ
  have hψm : ψ ^ m = 1 := by
    show (e.mapMatrix φ) ^ m = 1
    rw [← map_pow, h, map_one]
  have hm0 : m ≠ 0 := by
    obtain ⟨k, rfl⟩ := hm
    omega
  have hdet : ψ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hψm
    rw [Matrix.det_pow, h0, zero_pow hm0, Matrix.det_one] at h1
    exact zero_ne_one h1
  have h6 := zmod2_pow_six ψ hdet
  have h3 : ψ ^ 3 = 1 := by
    have hg := pow_gcd_eq_one.mpr ⟨h6, hψm⟩
    have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
    have h63 : Nat.gcd 6 m = Nat.gcd 3 m := by
      have := Nat.Coprime.gcd_mul_left_cancel 3 hcop
      simpa using this
    rw [h63] at hg
    have hd : orderOf ψ ∣ 3 := (orderOf_dvd_of_pow_eq_one hg).trans (Nat.gcd_dvd_left 3 m)
    exact orderOf_dvd_iff_pow_eq_one.mp hd
  rcases zmod2_pow_three ψ h3 with h1 | h2
  · left
    exact e.mapMatrix.injective (by rw [map_one]; exact h1)
  · right
    intro w hw
    have hψ : ψ.mulVec (e ∘ w) = e ∘ w := by
      funext i
      have := RingHom.map_mulVec (e : F →+* ZMod 2) φ w i
      simp only [RingEquiv.coe_toRingHom] at this
      show (φ.map e).mulVec (e ∘ w) i = (e ∘ w) i
      rw [← this, hw]
      rfl
    have := h2 (e ∘ w) hψ
    funext i
    have hi := congrFun this i
    exact e.injective (by simpa using hi)

omit [Fintype F] in
theorem iterate_block {k : ℕ} (Φ : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F))
    (φ : Matrix (Fin k) (Fin k) F) (hφ : ∀ (x : Fin k → Fin 3 → F) (i : Fin k),
      Φ x i = ∑ j, φ i j • x j) :
    ∀ (n : ℕ) (x : Fin k → Fin 3 → F) (i : Fin k), (Φ^[n]) x i = ∑ j, (φ ^ n) i j • x j := by
  classical
  intro n
  induction n with
  | zero =>
    intro x i
    simp [Matrix.one_apply]
  | succ n ih =>
    intro x i
    rw [Function.iterate_succ_apply', hφ]
    have : ∀ j, (Φ^[n]) x j = ∑ l, (φ ^ n) j l • x l := fun j => ih x j
    simp only [this, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [pow_succ', Matrix.mul_apply, Finset.sum_smul]

theorem fixed_or_id (hF : Fintype.card F = 2) {k : ℕ} (hk : k = 1 ∨ k = 2) {m : ℕ} (hm : Odd m)
    (Φ : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F))
    (hΦ : ∀ g : SpecialLinearGroup (Fin 3) F, ∀ x : Fin k → Fin 3 → F,
      Φ (fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (x i)) =
        fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (Φ x i))
    (hΦm : ∀ x, (Φ^[m]) x = x) :
    (∀ x, Φ x = x) ∨ (k = 2 ∧ ∀ x, Φ x = x → x = 0) := by
  classical
  obtain ⟨φ, hφ⟩ := block_structure hF Φ hΦ
  have hit := iterate_block Φ φ hφ
  have hφm : φ ^ m = 1 := by
    ext i j
    let x : Fin k → Fin 3 → F := fun l _ => if l = j then 1 else 0
    have h1 := congrFun (congrFun (hΦm x) i) 0
    have h2 := congrFun (hit m x i) 0
    rw [h2] at h1
    have h3 : (∑ l, (φ ^ m) i l • x l) 0 = (φ ^ m) i j := by
      rw [Finset.sum_apply]
      simp [x]
    rw [h3] at h1
    rw [h1, Matrix.one_apply]
  have hm0 : m ≠ 0 := by
    obtain ⟨k, rfl⟩ := hm
    omega
  have hdet : φ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hφm
    rw [Matrix.det_pow, h0, zero_pow hm0, Matrix.det_one] at h1
    exact zero_ne_one h1
  rcases hk with rfl | rfl
  · left
    have hφ1 : φ = 1 := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi hj
      rcases eq_zero_or_one_of_card_two hF (φ 0 0) with h0 | h0
      · exfalso
        apply hdet
        rw [Matrix.det_unique]
        simpa using h0
      · simpa using h0
    intro x
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rw [hφ x 0, hφ1]
    simp [Matrix.one_apply]
  · rcases mat2_odd_pow hF hm φ hφm with h1 | h2
    · left
      intro x
      funext i r
      rw [hφ x i, h1]
      fin_cases i <;> simp [Matrix.one_apply]
    · right
      refine ⟨rfl, ?_⟩
      intro x hx
      funext i r
      have hw : φ.mulVec (fun j => x j r) = fun j => x j r := by
        funext l
        have := congrFun (congrFun (hx) l) r
        rw [hφ x l] at this
        simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using this
      have := h2 _ hw
      exact congrFun this i

end Field2

section Group

variable {G : Type} [Group G]

theorem kc_nat {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) {k : ℕ}
    (hk : k = 1 ∨ k = 2) {L Z : Subgroup G} {y : G}
    (act : ↥L → Matrix (Fin 3) (Fin 3) F)
    (hsurj : ∀ g : SpecialLinearGroup (Fin 3) F, ∃ l : ↥L, act l = (g : Matrix (Fin 3) (Fin 3) F))
    (β : ↥Z →* Multiplicative (Fin k → Fin 3 → F)) (hβs : Function.Surjective β)
    (hβi : Function.Injective β) (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hβe : ∀ (a : ↥L) (u v : ↥Z), (v : G) = a * u * a⁻¹ → ∀ i,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i))
    (hyZ : y ∈ Subgroup.normalizer (Z : Set G))
    (hyL : ∀ l : ↥L, ∃ o : ↥L, (o : G) = y * l * y⁻¹ * (l : G)⁻¹ ∧ act o = 1)
    (hodd : Odd (orderOf y)) :
    (∀ z ∈ Z, y * z * y⁻¹ = z) ∨ (∀ z ∈ Z, y * z * y⁻¹ = z → z = 1) := by
  classical
  let cy : MulAut ↥Z := Z.normalizerMonoidHom ⟨y, hyZ⟩
  have hcy : ∀ u : ↥Z, ((cy u : ↥Z) : G) = y * u * y⁻¹ := fun u => rfl
  let eβ : ↥Z ≃* Multiplicative (Fin k → Fin 3 → F) := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let Φ : MulAut (Multiplicative (Fin k → Fin 3 → F)) := MulAut.congr eβ cy
  have hΦ : ∀ u : ↥Z, Φ (β u) = β (cy u) := by
    intro u
    show eβ (cy (eβ.symm (β u))) = β (cy u)
    have : eβ.symm (β u) = u := eβ.symm_apply_apply u
    rw [this]
    rfl
  let Φa : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F) :=
    AddMonoidHom.mk' (fun x => Multiplicative.toAdd (Φ (Multiplicative.ofAdd x))) (fun a b => by
      rw [ofAdd_add, map_mul, toAdd_mul])
  have hΦa : ∀ u : ↥Z, Φa (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (cy u)) := by
    intro u
    show Multiplicative.toAdd (Φ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))) = _
    rw [ofAdd_toAdd, hΦ]
  have hcomm : ∀ (l : ↥L) (u v : ↥Z), (v : G) = l * u * l⁻¹ → ∀ i,
      Multiplicative.toAdd (β (cy v)) i = (act l).mulVec (Multiplicative.toAdd (β (cy u)) i) := by
    intro l u v hv
    obtain ⟨o, ho, hact⟩ := hyL l
    have hu'Z : ((cy u : ↥Z) : G) ∈ Z := (cy u).2
    have hv'mem : (l : G) * ((cy u : ↥Z) : G) * (l : G)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hLZ l.2) _).mp hu'Z
    let v' : ↥Z := ⟨(l : G) * ((cy u : ↥Z) : G) * (l : G)⁻¹, hv'mem⟩
    have hotriv : ∀ w : ↥Z, ∀ (hw : (o : G) * w * (o : G)⁻¹ ∈ Z),
        (⟨(o : G) * w * (o : G)⁻¹, hw⟩ : ↥Z) = w := by
      intro w hw
      apply hβi
      ext i
      rw [hβe o w ⟨(o : G) * w * (o : G)⁻¹, hw⟩ rfl i, hact]
      simp
    have hcv : cy v = v' := by
      have hvz : ((v : ↥Z) : G) = l * u * l⁻¹ := hv
      have hv'Z : (o : G) * ((v' : ↥Z) : G) * (o : G)⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hLZ o.2) _).mp v'.2
      have h1 := hotriv v' hv'Z
      apply Subtype.ext
      rw [hcy]
      have h2 := congrArg (fun w : ↥Z => (w : G)) h1
      simp only at h2
      rw [← h2]
      have hv'val : ((v' : ↥Z) : G) = (l : G) * (y * u * y⁻¹) * (l : G)⁻¹ := rfl
      rw [hv'val, hvz, ho]
      simp only [Subgroup.coe_inv]
      group
    rw [hcv]
    exact hβe l (cy u) v' rfl
  have hΦcomm : ∀ g : SpecialLinearGroup (Fin 3) F, ∀ x : Fin k → Fin 3 → F,
      Φa (fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (x i)) =
        fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (Φa x i) := by
    intro g x
    obtain ⟨l, hl⟩ := hsurj g
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    have hlZ : (l : G) * (u : G) * (l : G)⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hLZ l.2) _).mp u.2
    let v : ↥Z := ⟨(l : G) * (u : G) * (l : G)⁻¹, hlZ⟩
    have hv : (fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (x i)) = Multiplicative.toAdd (β v) := by
      funext i
      rw [hβe l u v rfl i, hl, hx]
    rw [hv, hΦa v, hx, hΦa u]
    funext i
    rw [hcomm l u v rfl i, hl]
  have hm : Odd (orderOf y) := hodd
  have hpow : cy ^ orderOf y = 1 := by
    have : (Z.normalizerMonoidHom) ((⟨y, hyZ⟩ : ↥(Subgroup.normalizer (Z : Set G))) ^ orderOf y) = 1 := by
      have h1 : (⟨y, hyZ⟩ : ↥(Subgroup.normalizer (Z : Set G))) ^ orderOf y = 1 :=
        Subtype.ext (pow_orderOf_eq_one y)
      rw [h1, map_one]
    rwa [map_pow] at this
  have hiter : ∀ (n : ℕ) (x : Fin k → Fin 3 → F),
      (Φa^[n]) x = Multiplicative.toAdd ((Φ ^ n) (Multiplicative.ofAdd x)) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply, ih, pow_succ]
      rfl
  have hΦpow : Φ ^ orderOf y = 1 := by
    have : Φ ^ orderOf y = MulAut.congr eβ (cy ^ orderOf y) := (map_pow (MulAut.congr eβ) cy _).symm
    rw [this, hpow, map_one]
  have hΦm : ∀ x, (Φa^[orderOf y]) x = x := by
    intro x
    rw [hiter, hΦpow]
    rfl
  rcases fixed_or_id hF hk hm Φa hΦcomm hΦm with h1 | ⟨-, h2⟩
  · left
    intro z hz
    have := h1 (Multiplicative.toAdd (β ⟨z, hz⟩))
    rw [hΦa] at this
    have h3 : cy ⟨z, hz⟩ = ⟨z, hz⟩ := hβi (by simpa using this)
    have := congrArg (fun w : ↥Z => (w : G)) h3
    simpa [hcy] using this
  · right
    intro z hz hyz
    have h3 : cy ⟨z, hz⟩ = ⟨z, hz⟩ := Subtype.ext (by rw [hcy]; exact hyz)
    have h4 := h2 (Multiplicative.toAdd (β ⟨z, hz⟩)) (by rw [hΦa, h3])
    have h5 : β ⟨z, hz⟩ = 1 := by
      have := congrArg Multiplicative.ofAdd h4
      simpa using this
    have h6 : (⟨z, hz⟩ : ↥Z) = 1 := hβi (by rw [h5, map_one])
    exact congrArg (fun w : ↥Z => (w : G)) h6

theorem eq_of_card_two {H : Type} [Group H] [Finite H] (h : Nat.card H = 2) {a b : H} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have := Fintype.ofFinite H
  have h3 : ({1, a, b} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ha.symm, hb.symm⟩
  have h4 := Finset.card_le_univ ({1, a, b} : Finset H)
  rw [← Nat.card_eq_fintype_card, h] at h4
  omega

theorem kc_case5 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {L Q C A : Subgroup G} {y : G}
    (act : ↥L → Matrix (Fin 3) (Fin 3) F)
    (hsurj : ∀ g : SpecialLinearGroup (Fin 3) F, ∃ l : ↥L, act l = (g : Matrix (Fin 3) (Fin 3) F))
    (β : ↥Q →* Multiplicative (Fin 1 → Fin 3 → F)) (hβs : Function.Surjective β)
    (hker : β.ker = C.subgroupOf Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hβe : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i))
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) (hyC : y ∈ Subgroup.normalizer (C : Set G))
    (hyL : ∀ l : ↥L, ∃ o : ↥L, (o : G) = y * l * y⁻¹ * (l : G)⁻¹ ∧ act o = 1)
    (hC2 : Nat.card C = 2) (hodd : Odd (orderOf y)) (hAQ : A ≤ Q)
    (hAc : ∀ a ∈ A, ∀ q ∈ Q, a * q = q * a) [Finite G] :
    ∀ a ∈ A, y * a * y⁻¹ = a := by
  classical
  let cyQ : MulAut ↥Q := Q.normalizerMonoidHom ⟨y, hyQ⟩
  have hcyQ : ∀ u : ↥Q, ((cyQ u : ↥Q) : G) = y * u * y⁻¹ := fun u => rfl
  have hkerQ : ∀ q : ↥Q, β q = 1 ↔ ((q : ↥Q) : G) ∈ C := by
    intro q
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hwd : ∀ q q' : ↥Q, β q = β q' → β (cyQ q) = β (cyQ q') := by
    intro q q' h
    have h1 : β (q⁻¹ * q') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : ((q⁻¹ * q' : ↥Q) : G) ∈ C := (hkerQ _).mp h1
    have h3 : y * ((q⁻¹ * q' : ↥Q) : G) * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hyC _).mp h2
    have h4 : β (cyQ (q⁻¹ * q')) = 1 := (hkerQ _).mpr (by rw [hcyQ]; exact h3)
    rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_one] at h4
    exact h4
  let σ : Multiplicative (Fin 1 → Fin 3 → F) → ↥Q := Function.surjInv hβs
  have hσ : ∀ z, β (σ z) = z := Function.surjInv_eq hβs
  let Φa : (Fin 1 → Fin 3 → F) →+ (Fin 1 → Fin 3 → F) :=
    AddMonoidHom.mk' (fun x => Multiplicative.toAdd (β (cyQ (σ (Multiplicative.ofAdd x)))))
      (fun a b => by
        have h1 : β (σ (Multiplicative.ofAdd (a + b))) =
            β (σ (Multiplicative.ofAdd a) * σ (Multiplicative.ofAdd b)) := by
          rw [hσ, map_mul, hσ, hσ]; rfl
        rw [hwd _ _ h1, map_mul, map_mul, toAdd_mul])
  have hΦa : ∀ q : ↥Q, Φa (Multiplicative.toAdd (β q)) = Multiplicative.toAdd (β (cyQ q)) := by
    intro q
    show Multiplicative.toAdd (β (cyQ (σ (Multiplicative.ofAdd (Multiplicative.toAdd (β q)))))) = _
    rw [ofAdd_toAdd, hwd _ _ (hσ (β q))]
  have hcomm : ∀ (l : ↥L) (u v : ↥Q), (v : G) = l * u * l⁻¹ → ∀ i,
      Multiplicative.toAdd (β (cyQ v)) i = (act l).mulVec (Multiplicative.toAdd (β (cyQ u)) i) := by
    intro l u v hv
    obtain ⟨o, ho, hact⟩ := hyL l
    have hu'Q : ((cyQ u : ↥Q) : G) ∈ Q := (cyQ u).2
    have hv'mem : (l : G) * ((cyQ u : ↥Q) : G) * (l : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp hu'Q
    let v' : ↥Q := ⟨(l : G) * ((cyQ u : ↥Q) : G) * (l : G)⁻¹, hv'mem⟩
    have hwmem : (o : G) * ((v' : ↥Q) : G) * (o : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ o.2) _).mp v'.2
    let w : ↥Q := ⟨(o : G) * ((v' : ↥Q) : G) * (o : G)⁻¹, hwmem⟩
    have hcv : cyQ v = w := by
      have hvz : ((v : ↥Q) : G) = l * u * l⁻¹ := hv
      apply Subtype.ext
      rw [hcyQ]
      have hv'val : ((v' : ↥Q) : G) = (l : G) * (y * u * y⁻¹) * (l : G)⁻¹ := rfl
      show y * ((v : ↥Q) : G) * y⁻¹ = (o : G) * ((v' : ↥Q) : G) * (o : G)⁻¹
      rw [hv'val, hvz, ho]
      simp only [Subgroup.coe_inv]
      group
    have hβw : ∀ i, Multiplicative.toAdd (β w) i = Multiplicative.toAdd (β v') i := by
      intro i
      rw [hβe o v' w rfl i, hact]
      simp
    rw [hcv]
    intro i
    rw [hβw i]
    exact hβe l (cyQ u) v' rfl i
  have hΦcomm : ∀ g : SpecialLinearGroup (Fin 3) F, ∀ x : Fin 1 → Fin 3 → F,
      Φa (fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (x i)) =
        fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (Φa x i) := by
    intro g x
    obtain ⟨l, hl⟩ := hsurj g
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    have hlQ : (l : G) * (u : G) * (l : G)⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ l.2) _).mp u.2
    let v : ↥Q := ⟨(l : G) * (u : G) * (l : G)⁻¹, hlQ⟩
    have hv : (fun i => (g : Matrix (Fin 3) (Fin 3) F).mulVec (x i)) = Multiplicative.toAdd (β v) := by
      funext i
      rw [hβe l u v rfl i, hl, hx]
    rw [hv, hΦa v, hx, hΦa u]
    funext i
    rw [hcomm l u v rfl i, hl]
  have hiter : ∀ (n : ℕ) (q : ↥Q), (Φa^[n]) (Multiplicative.toAdd (β q)) =
      Multiplicative.toAdd (β ((cyQ ^ n) q)) := by
    intro n
    induction n with
    | zero => intro q; rfl
    | succ n ih =>
      intro q
      rw [Function.iterate_succ_apply', ih, hΦa, pow_succ']
      rfl
  have hpow : cyQ ^ orderOf y = 1 := by
    have : (Q.normalizerMonoidHom) ((⟨y, hyQ⟩ : ↥(Subgroup.normalizer (Q : Set G))) ^ orderOf y) = 1 := by
      have h1 : (⟨y, hyQ⟩ : ↥(Subgroup.normalizer (Q : Set G))) ^ orderOf y = 1 :=
        Subtype.ext (pow_orderOf_eq_one y)
      rw [h1, map_one]
    rwa [map_pow] at this
  have hΦm : ∀ x, (Φa^[orderOf y]) x = x := by
    intro x
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β q) := by rw [hq]; rfl
    rw [hx, hiter, hpow]
    rfl
  have hfix : ∀ x, Φa x = x := by
    rcases fixed_or_id hF (Or.inl rfl) hodd Φa hΦcomm hΦm with h1 | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 (by norm_num)
  have hβcy : ∀ q : ↥Q, β (cyQ q) = β q := by
    intro q
    have := hfix (Multiplicative.toAdd (β q))
    rw [hΦa] at this
    exact Multiplicative.toAdd.injective this
  have hCfix : ∀ c ∈ C, y * c * y⁻¹ = c := by
    intro c hc
    by_cases hc1 : c = 1
    · subst hc1; simp
    · have hc' : y * c * y⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hyC c).mp hc
      have hne : (⟨y * c * y⁻¹, hc'⟩ : ↥C) ≠ 1 := by
        intro h
        apply hc1
        have := congrArg (fun z : ↥C => (z : G)) h
        simp only [OneMemClass.coe_one] at this
        simpa using this
      have hne2 : (⟨c, hc⟩ : ↥C) ≠ 1 := fun h => hc1 (by simpa using congrArg (fun z : ↥C => (z : G)) h)
      have := eq_of_card_two hC2 hne hne2
      exact congrArg (fun z : ↥C => (z : G)) this
  intro a ha
  have haQ : a ∈ Q := hAQ ha
  let qa : ↥Q := ⟨a, haQ⟩
  set κ : G := y * a * y⁻¹ * a⁻¹ with hκ
  have hκQ : κ ∈ Q := by
    have h1 : y * a * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hyQ a).mp haQ
    exact Q.mul_mem h1 (Q.inv_mem haQ)
  have hκC : κ ∈ C := by
    have h1 : β ⟨κ, hκQ⟩ = 1 := by
      have : (⟨κ, hκQ⟩ : ↥Q) = cyQ qa * qa⁻¹ := by
        apply Subtype.ext
        simp [hcyQ, qa, hκ]
      rw [this, map_mul, map_inv, hβcy, mul_inv_cancel]
    exact (hkerQ _).mp h1
  have hκc : y * κ * y⁻¹ = κ := hCfix κ hκC
  have hκa : κ * a = a * κ := (hAc a ha κ hκQ).symm
  have hya : y * a * y⁻¹ = κ * a := by simp [hκ]
  have hpowconj : ∀ n : ℕ, y ^ n * a * (y ^ n)⁻¹ = κ ^ n * a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : y ^ (n + 1) * a * (y ^ (n + 1))⁻¹ = y * (y ^ n * a * (y ^ n)⁻¹) * y⁻¹ := by group
      rw [e1, ih]
      have e2 : y * (κ ^ n * a) * y⁻¹ = (y * κ * y⁻¹) ^ n * (y * a * y⁻¹) := by
        rw [conj_pow]; group
      rw [e2, hκc, hya, pow_succ']
      group
  have hκ2 : κ ^ 2 = 1 := by
    have h1 : (⟨κ, hκC⟩ : ↥C) ^ Nat.card C = 1 := pow_card_eq_one'
    rw [hC2] at h1
    simpa using congrArg (fun z : ↥C => (z : G)) h1
  have hκm : κ ^ orderOf y = 1 := by
    have h1 := hpowconj (orderOf y)
    rw [pow_orderOf_eq_one] at h1
    simpa using h1.symm
  obtain ⟨j, hj⟩ := hodd
  have hκ1 : κ = 1 := by
    have : κ ^ orderOf y = κ := by
      rw [hj, pow_succ, pow_mul, hκ2, one_pow, one_mul]
    rw [← this]
    exact hκm
  rw [hya, hκ1, one_mul]

end Group

end SBd5

end CFSG.Quasithin
