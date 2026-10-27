module

public import CFSG.Quasithin.EmptyFaithful.SBd5Nat

public section

namespace CFSG.Quasithin

namespace SBd6

open Matrix CFSG.Quasithin.SBd5

section Finite

set_option maxRecDepth 100000 in
theorem zmod2_vec_trans : ∀ u w : Fin 3 → ZMod 2, u ≠ 0 → w ≠ 0 →
    ∃ g : SpecialLinearGroup (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = w := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem zmod2_cent_three : ∀ σ A : SpecialLinearGroup (Fin 3) (ZMod 2),
    σ ^ 3 = 1 → σ ≠ 1 → σ * A = A * σ → A ^ 3 = 1 := by
  decide +kernel

end Finite

section Transport

variable {F : Type} [Field F] [Fintype F]

noncomputable def eZ2 (hF : Fintype.card F = 2) : F ≃+* ZMod 2 :=
  FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])

theorem map_eZ2_injective (hF : Fintype.card F = 2) :
    Function.Injective (SpecialLinearGroup.map (eZ2 hF : F →+* ZMod 2) :
      SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  intro A B h
  apply Subtype.ext
  have h1 := congrArg (fun X : SpecialLinearGroup (Fin 3) (ZMod 2) =>
    (X : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  exact (eZ2 hF).injective h2

theorem irreducible_vec (hF : Fintype.card F = 2) (X : AddSubgroup (Fin 3 → F))
    (hX : ∀ g : SpecialLinearGroup (Fin 3) F, ∀ x ∈ X,
      (g : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ X) :
    X = ⊥ ∨ X = ⊤ := by
  by_cases hbot : X = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x₀, hx₀, hne⟩ : ∃ x₀ ∈ X, x₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot (eq_bot_iff.mpr (fun x hx => by simpa using h x hx))
  rw [eq_top_iff]
  intro w _
  by_cases hw : w = 0
  · rw [hw]; exact X.zero_mem
  let e : F ≃+* ZMod 2 := eZ2 hF
  have hu : (e ∘ x₀) ≠ 0 := by
    intro h
    apply hne
    funext i
    have := congrFun h i
    simpa using this
  have hw' : (e ∘ w) ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa using this
  obtain ⟨g', hg'⟩ := zmod2_vec_trans (e ∘ x₀) (e ∘ w) hu hw'
  let g : SpecialLinearGroup (Fin 3) F := SpecialLinearGroup.map (e.symm : ZMod 2 →+* F) g'
  have hgm : (g : Matrix (Fin 3) (Fin 3) F) = (g' : Matrix (Fin 3) (Fin 3) (ZMod 2)).map e.symm := rfl
  have hg : (g : Matrix (Fin 3) (Fin 3) F).mulVec x₀ = w := by
    funext i
    apply e.injective
    have h1 := RingHom.map_mulVec (e : F →+* ZMod 2) (g : Matrix (Fin 3) (Fin 3) F) x₀ i
    have h2 : (g : Matrix (Fin 3) (Fin 3) F).map e = (g' : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [hgm]
      ext a b
      simp
    simp only [RingEquiv.coe_toRingHom] at h1
    rw [h2] at h1
    rw [h1, hg']
    rfl
  have := hX g x₀ hx₀
  rwa [hg] at this

theorem cent_three (hF : Fintype.card F = 2) (σ A : SpecialLinearGroup (Fin 3) F) (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) (hc : σ * A = A * σ) : A ^ 3 = 1 := by
  let f : SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    SpecialLinearGroup.map (eZ2 hF : F →+* ZMod 2)
  have := zmod2_cent_three (f σ) (f A) (by rw [← map_pow, h3, map_one])
    (fun h => h1 (map_eZ2_injective hF (by rw [h, map_one])))
    (by rw [← map_mul, ← map_mul, hc])
  exact map_eZ2_injective hF (by rw [map_pow, this, map_one])

end Transport

section Twist

variable {F : Type} [Field F] [Fintype F] {G : Type} [Group G]

theorem exists_matrix_of_add (hF : Fintype.card F = 2) (φ : (Fin 3 → F) →+ (Fin 3 → F)) :
    ∃ A : Matrix (Fin 3) (Fin 3) F, ∀ v, A.mulVec v = φ v := by
  classical
  let φl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r x => by
        rcases eq_zero_or_one_of_card_two hF r with rfl | rfl
        · simp
        · simp }
  exact ⟨LinearMap.toMatrix' φl, fun v => LinearMap.toMatrix'_mulVec φl v⟩

theorem twist_matrix (hF : Fintype.card F = 2) {k : ℕ} (hk : 0 < k) {L Z : Subgroup G} {r : G}
    (act : ↥L → Matrix (Fin 3) (Fin 3) F)
    (hsurj : ∀ g : SpecialLinearGroup (Fin 3) F, ∃ l : ↥L, act l = (g : Matrix (Fin 3) (Fin 3) F))
    (β : ↥Z →* Multiplicative (Fin k → Fin 3 → F)) (hβs : Function.Surjective β)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hβe : ∀ (a : ↥L) (u v : ↥Z), (v : G) = a * u * a⁻¹ → ∀ i,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i))
    (hrZ : r ∈ Subgroup.normalizer (Z : Set G)) (hrL : r ∈ Subgroup.normalizer (L : Set G))
    (hker : ∀ (u : ↥Z) (hu : r * u * r⁻¹ ∈ Z), β ⟨r * u * r⁻¹, hu⟩ = 1 ↔ β u = 1) :
    ∃ A : SpecialLinearGroup (Fin 3) F, ∀ (l : ↥L) (hl : r * l * r⁻¹ ∈ L),
      act ⟨r * l * r⁻¹, hl⟩ * (A : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * act l := by
  classical
  let cyZ : MulAut ↥Z := Z.normalizerMonoidHom ⟨r, hrZ⟩
  have hcy : ∀ u : ↥Z, ((cyZ u : ↥Z) : G) = r * u * r⁻¹ := fun u => rfl
  have hkerZ : ∀ u : ↥Z, β (cyZ u) = 1 ↔ β u = 1 := fun u => hker u (cyZ u).2
  have hwd : ∀ u u' : ↥Z, β u = β u' → β (cyZ u) = β (cyZ u') := by
    intro u u' h
    have h1 : β (u'⁻¹ * u) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h4 : β (cyZ (u'⁻¹ * u)) = 1 := (hkerZ _).mpr h1
    rw [map_mul, map_inv, map_mul, map_inv, inv_mul_eq_one] at h4
    exact h4.symm
  let σ : Multiplicative (Fin k → Fin 3 → F) → ↥Z := Function.surjInv hβs
  have hσ : ∀ z, β (σ z) = z := Function.surjInv_eq hβs
  let Φ : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F) :=
    AddMonoidHom.mk' (fun x => Multiplicative.toAdd (β (cyZ (σ (Multiplicative.ofAdd x)))))
      (fun a b => by
        have h1 : β (σ (Multiplicative.ofAdd (a + b))) =
            β (σ (Multiplicative.ofAdd a) * σ (Multiplicative.ofAdd b)) := by
          rw [hσ, map_mul, hσ, hσ]; rfl
        rw [hwd _ _ h1, map_mul, map_mul, toAdd_mul])
  have hΦa : ∀ u : ↥Z, Φ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (cyZ u)) := by
    intro u
    show Multiplicative.toAdd (β (cyZ (σ (Multiplicative.ofAdd (Multiplicative.toAdd (β u)))))) = _
    rw [ofAdd_toAdd, hwd _ _ (hσ (β u))]
  have hstar : ∀ (l : ↥L) (hl : r * l * r⁻¹ ∈ L) (x : Fin k → Fin 3 → F),
      Φ (fun i => (act l).mulVec (x i)) = fun i => (act ⟨r * l * r⁻¹, hl⟩).mulVec (Φ x i) := by
    intro l hl x
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    have hlZ : (l : G) * (u : G) * (l : G)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hLZ l.2) _).mp u.2
    let v : ↥Z := ⟨(l : G) * (u : G) * (l : G)⁻¹, hlZ⟩
    have hv : (fun i => (act l).mulVec (x i)) = Multiplicative.toAdd (β v) := by
      funext i
      rw [hβe l u v rfl i, hx]
    rw [hv, hΦa v, hx, hΦa u]
    funext i
    have hcv : ((cyZ v : ↥Z) : G) =
        (r * (l : G) * r⁻¹) * ((cyZ u : ↥Z) : G) * (r * (l : G) * r⁻¹)⁻¹ := by
      show r * ((l : G) * (u : G) * (l : G)⁻¹) * r⁻¹ = _
      rw [hcy]
      group
    exact hβe ⟨r * l * r⁻¹, hl⟩ (cyZ u) (cyZ v) hcv i
  have hΦinj : ∀ x : Fin k → Fin 3 → F, Φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
    have hx' : x = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    rw [hx', hΦa] at hx
    have h1 : β (cyZ u) = 1 := by
      have := congrArg Multiplicative.ofAdd hx
      simpa using this
    have h2 : β u = 1 := (hkerZ u).mp h1
    rw [hx', h2]
    rfl
  let j0 : Fin k := ⟨0, hk⟩
  let v0 : Fin 3 → F := Pi.single 0 1
  have hv0 : v0 ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [v0] at this
  have hx0 : (Pi.single j0 v0 : Fin k → Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun h j0
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hv0 this
  have hΦx0 := fun h => hx0 (hΦinj _ h)
  have hex : ∃ i, Φ (Pi.single j0 v0) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hΦx0 (funext h)
  obtain ⟨i0, hi0⟩ := hex
  let φ : (Fin 3 → F) →+ (Fin 3 → F) :=
    (Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i0).comp
      (Φ.comp (AddMonoidHom.single (fun _ : Fin k => Fin 3 → F) j0))
  have hφv0 : φ v0 ≠ 0 := hi0
  have hφ : ∀ (l : ↥L) (hl : r * l * r⁻¹ ∈ L) (v : Fin 3 → F),
      φ ((act l).mulVec v) = (act ⟨r * l * r⁻¹, hl⟩).mulVec (φ v) := by
    intro l hl v
    have h1 := hstar l hl (Pi.single j0 v)
    have h2 : (fun i => (act l).mulVec ((Pi.single j0 v : Fin k → Fin 3 → F) i)) =
        Pi.single j0 ((act l).mulVec v) := by
      funext a
      by_cases ha : a = j0
      · subst ha; simp
      · simp [Pi.single_eq_of_ne ha]
    rw [h2] at h1
    exact congrFun h1 i0
  have hker0 : φ.ker = ⊥ := by
    have hinv : ∀ g : SpecialLinearGroup (Fin 3) F, ∀ x ∈ φ.ker,
        (g : Matrix (Fin 3) (Fin 3) F).mulVec x ∈ φ.ker := by
      intro g x hx
      obtain ⟨l, hl⟩ := hsurj g
      have hl' : r * (l : G) * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrL l).mp l.2
      rw [AddMonoidHom.mem_ker] at hx ⊢
      rw [← hl, hφ l hl', hx]
      simp
    rcases irreducible_vec hF φ.ker hinv with h | h
    · exact h
    · exfalso
      apply hφv0
      have : v0 ∈ φ.ker := by rw [h]; exact AddSubgroup.mem_top _
      exact this
  have hφinj : Function.Injective φ := (AddMonoidHom.ker_eq_bot_iff φ).mp hker0
  obtain ⟨A, hA⟩ := exists_matrix_of_add hF φ
  have hAinj : Function.Injective A.mulVec := by
    intro a b hab
    apply hφinj
    rw [← hA a, ← hA b]
    exact hab
  have hAu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hAinj
  have hdet : A.det = 1 := by
    have h1 : A.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det A).mp hAu |>.ne_zero
    rcases eq_zero_or_one_of_card_two hF A.det with h | h
    · exact absurd h h1
    · exact h
  refine ⟨⟨A, hdet⟩, fun l hl => ?_⟩
  refine Matrix.ext_of_mulVec_single (fun b => ?_)
  show (act ⟨r * l * r⁻¹, hl⟩ * A) *ᵥ Pi.single b 1 = (A * act l) *ᵥ Pi.single b 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, ← hφ l hl]

theorem twist_trivial (hF : Fintype.card F = 2) {k : ℕ} (hk : 0 < k) {L Z : Subgroup G} {r : G}
    (act : ↥L → Matrix (Fin 3) (Fin 3) F) (hdet : ∀ l, (act l).det = 1)
    (hsurj : ∀ g : SpecialLinearGroup (Fin 3) F, ∃ l : ↥L, act l = (g : Matrix (Fin 3) (Fin 3) F))
    (β : ↥Z →* Multiplicative (Fin k → Fin 3 → F)) (hβs : Function.Surjective β)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hβe : ∀ (a : ↥L) (u v : ↥Z), (v : G) = a * u * a⁻¹ → ∀ i,
      Multiplicative.toAdd (β v) i = (act a).mulVec (Multiplicative.toAdd (β u) i))
    (hrZ : r ∈ Subgroup.normalizer (Z : Set G)) (hrL : r ∈ Subgroup.normalizer (L : Set G))
    (hker : ∀ (u : ↥Z) (hu : r * u * r⁻¹ ∈ Z), β ⟨r * u * r⁻¹, hu⟩ = 1 ↔ β u = 1)
    {y : G} (hy : y ∈ L) (hyr : r * y = y * r) (hσ3 : (act ⟨y, hy⟩) ^ 3 = 1)
    (hσ1 : act ⟨y, hy⟩ ≠ 1) {m : ℕ} (hm : r ^ (2 ^ m) = 1) :
    ∀ (l : ↥L) (hl : r * l * r⁻¹ ∈ L), act ⟨r * l * r⁻¹, hl⟩ = act l := by
  classical
  obtain ⟨A, hA⟩ := twist_matrix hF hk act hsurj β hβs hLZ hβe hrZ hrL hker
  let σ : SpecialLinearGroup (Fin 3) F := ⟨act ⟨y, hy⟩, hdet _⟩
  have hryr : r * y * r⁻¹ = y := by
    calc r * y * r⁻¹ = y * r * r⁻¹ := by rw [hyr]
      _ = y := by group
  have hσ3' : σ ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact hσ3
  have hσ1' : σ ≠ 1 := fun h => hσ1 (congrArg Subtype.val h)
  have hcomm : σ * A = A * σ := by
    apply Subtype.ext
    have hl : r * ((⟨y, hy⟩ : ↥L) : G) * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hrL y).mp hy
    have h1 := hA ⟨y, hy⟩ hl
    have h2 : (⟨r * ((⟨y, hy⟩ : ↥L) : G) * r⁻¹, hl⟩ : ↥L) = ⟨y, hy⟩ := Subtype.ext hryr
    rw [h2] at h1
    exact h1
  have hA3 : A ^ 3 = 1 := cent_three hF σ A hσ3' hσ1' hcomm
  have hA3m : (A : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
    have := congrArg Subtype.val hA3
    rwa [Matrix.SpecialLinearGroup.coe_pow] at this
  have hrn : ∀ n : ℕ, r ^ n ∈ Subgroup.normalizer (L : Set G) := fun n => pow_mem hrL n
  let conjL : ℕ → ↥L → ↥L := fun n l =>
    ⟨r ^ n * (l : G) * (r ^ n)⁻¹, (Subgroup.mem_normalizer_iff.mp (hrn n) l).mp l.2⟩
  have hconj_succ : ∀ (n : ℕ) (l : ↥L), conjL (n + 1) l =
      ⟨r * (conjL n l : G) * r⁻¹, (Subgroup.mem_normalizer_iff.mp hrL _).mp (conjL n l).2⟩ := by
    intro n l
    apply Subtype.ext
    show r ^ (n + 1) * (l : G) * (r ^ (n + 1))⁻¹ = r * (r ^ n * (l : G) * (r ^ n)⁻¹) * r⁻¹
    rw [pow_succ']
    group
  have hconj_add : ∀ (n n' : ℕ) (l : ↥L), conjL (n + n') l = conjL n (conjL n' l) := by
    intro n n' l
    apply Subtype.ext
    show r ^ (n + n') * (l : G) * (r ^ (n + n'))⁻¹ =
      r ^ n * (r ^ n' * (l : G) * (r ^ n')⁻¹) * (r ^ n)⁻¹
    rw [pow_add]
    group
  have hconj_zero : ∀ l : ↥L, conjL 0 l = l := fun l => Subtype.ext (by simp [conjL])
  have hR2 : ∀ (n : ℕ) (l : ↥L), act (conjL n l) * (A : Matrix (Fin 3) (Fin 3) F) ^ n =
      (A : Matrix (Fin 3) (Fin 3) F) ^ n * act l := by
    intro n
    induction n with
    | zero => intro l; rw [hconj_zero]; simp
    | succ n ih =>
      intro l
      rw [hconj_succ n l]
      have h1 := hA (conjL n l) ((Subgroup.mem_normalizer_iff.mp hrL _).mp (conjL n l).2)
      rw [pow_succ', ← Matrix.mul_assoc, h1, Matrix.mul_assoc, ih l, ← Matrix.mul_assoc]
  have hR3 : ∀ l : ↥L, act (conjL 3 l) = act l := by
    intro l
    have := hR2 3 l
    rwa [hA3m, Matrix.mul_one, Matrix.one_mul] at this
  have hR3a : ∀ (a : ℕ) (l : ↥L), act (conjL (3 * a) l) = act l := by
    intro a
    induction a with
    | zero => intro l; rw [Nat.mul_zero, hconj_zero]
    | succ a ih =>
      intro l
      rw [show 3 * (a + 1) = 3 + 3 * a by ring, hconj_add, hR3, ih]
  intro l hl
  by_cases hm0 : m = 0
  · subst hm0
    have hr1 : r = 1 := by simpa using hm
    subst hr1
    have : (⟨1 * (l : G) * (1 : G)⁻¹, hl⟩ : ↥L) = l := Subtype.ext (by simp)
    rw [this]
  · have hk2 : 1 < 2 ^ m := Nat.one_lt_two_pow hm0
    obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime (k := 2 ^ m) (n := 3)
      (Nat.Coprime.pow_right m (by norm_num)) hk2
    have hra : r ^ (3 * a) = r := by
      calc r ^ (3 * a) = r ^ (2 ^ m * (3 * a / 2 ^ m) + 3 * a % 2 ^ m) := by rw [Nat.div_add_mod]
        _ = (r ^ (2 ^ m)) ^ (3 * a / 2 ^ m) * r ^ (3 * a % 2 ^ m) := by rw [pow_add, pow_mul]
        _ = r := by rw [hm, one_pow, one_mul, ha, pow_one]
    have hc : conjL (3 * a) l = ⟨r * (l : G) * r⁻¹, hl⟩ := by
      apply Subtype.ext
      show r ^ (3 * a) * (l : G) * (r ^ (3 * a))⁻¹ = r * (l : G) * r⁻¹
      rw [hra]
    rw [← hc]
    exact hR3a a l

end Twist

end SBd6

end CFSG.Quasithin
