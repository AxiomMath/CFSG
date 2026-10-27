module

public import CFSG.Quasithin.Background.SmithB57B
public import CFSG.Quasithin.Background.HSL

public section

namespace CFSG.Quasithin

namespace SmithB57

open CFSG.Timmesfeld CFSG.Assembly.LowTwoRank FFC.B59

section Helpers

variable {V : Type} [CommGroup V]

theorem cs_mul_le (y z : MulAut V) : cs (y * z) ≤ cs y ⊔ cs z := by
  rintro _ ⟨v, rfl⟩
  have h : commMap (y * z) v = (y (z v) * (z v)⁻¹) * (z v * v⁻¹) := by
    rw [commMap_apply, MulAut.mul_apply]
    group
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨z v, rfl⟩) (Subgroup.mem_sup_right ⟨v, rfl⟩)

theorem cs_pow_le (y : MulAut V) (n : ℕ) : cs (y ^ n) ≤ cs y := by
  induction n with
  | zero =>
    rintro _ ⟨v, rfl⟩
    rw [commMap_apply, pow_zero, MulAut.one_apply, mul_inv_cancel]
    exact Subgroup.one_mem _
  | succ n ih =>
    rw [pow_succ']
    exact (cs_mul_le y (y ^ n)).trans (sup_le le_rfl ih)

theorem cs_conj (g y : MulAut V) : cs (g * y * g⁻¹) = (cs y).map g.toMonoidHom := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨y (g⁻¹ v) * (g⁻¹ v)⁻¹, ⟨g⁻¹ v, rfl⟩, ?_⟩
    simp [commMap_apply, MulAut.mul_apply, map_mul, map_inv]
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨g v, ?_⟩
    simp [commMap_apply, MulAut.mul_apply, map_mul, map_inv]

variable [Finite V]

omit [Finite V] in
theorem commV_inv_of_comm {L : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ l ∈ L, g * l = l * g) : ∀ w ∈ commV L, g w ∈ commV L := by
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, v, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨l, hl, g v, ?_⟩
    rw [map_mul, map_inv, ← MulAut.mul_apply, ← hg l hl, MulAut.mul_apply]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

omit [Finite V] in
theorem rk_cs_conj (g y : MulAut V) : rk (cs (g * y * g⁻¹)) = rk (cs y) := by
  unfold rk
  rw [cs_conj, Subgroup.card_map_of_injective g.injective]

theorem rk_sup_le (H K : Subgroup V) : rk ↥(H ⊔ K) ≤ rk H + rk K := by
  have := rk_sup_add_rk_inf H K
  omega

theorem rk_cs_add_le {y : MulAut V} {A : Subgroup (MulAut V)} (hy : y ∈ A) :
    rk (cs y) + rk (fixV A) ≤ rk V := by
  have h1 := rk_cs_add y
  have h2 : rk (fixV A) ≤ rk (fixV (Subgroup.zpowers y)) :=
    rk_mono (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hy))
  omega

theorem rk_le_inf_add (N W : Subgroup V) : rk N + rk W ≤ rk ↥(N ⊓ W) + rk V := by
  have h1 := rk_sup_add_rk_inf N W
  have h2 : rk ↥(N ⊔ W) ≤ rk V := by
    have := rk_mono (le_top : N ⊔ W ≤ ⊤)
    rwa [rk_top] at this
  omega

end Helpers

section Transport

variable {V : Type} [CommGroup V]

theorem charP_two_of_card {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) : CharP F 2 := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨k, hk, hpk⟩ := FiniteField.card F p
  have h1 : p ^ (k : ℕ) = 2 ^ n := by rw [← hpk, hF]
  have : p ∣ 2 ^ n := by
    rw [← h1]
    exact dvd_pow_self p k.pos.ne'
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow this)
  subst hp2
  exact hp

theorem card_le_of_elemAbelian_sub {L E : Subgroup (MulAut V)} {F : Type} [Field F] [Fintype F]
    [CharP F 2] (πL : ↥(StatedSL 3 F) ≃* ↥L) (hEL : E ≤ L) (hE : IsElemAbelian2 E) :
    Nat.card E ≤ Fintype.card F ^ 2 := by
  set E₂ : Subgroup ↥(StatedSL 3 F) := (E.subgroupOf L).map πL.symm.toMonoidHom with hE₂
  set E₃ : Subgroup (GL (Fin 3) F) := E₂.map (StatedSL 3 F).subtype with hE₃
  have hc1 : Nat.card E₃ = Nat.card E := by
    rw [hE₃, Subgroup.card_map_of_injective (StatedSL 3 F).subtype_injective, hE₂,
      Subgroup.card_map_of_injective πL.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hmem : ∀ A ∈ E₃, ∃ e : ↥L, (e : MulAut V) ∈ E ∧
      ((πL.symm e : ↥(StatedSL 3 F)) : GL (Fin 3) F) = A := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, rfl⟩
  have hsq : ∀ A ∈ E₃, A * A = 1 := by
    intro A hA
    obtain ⟨e, he, rfl⟩ := hmem A hA
    have h1 : e * e = 1 := by
      apply Subtype.ext
      simpa [sq] using hE.2 _ he
    have := congrArg (fun x : ↥L => ((πL.symm x : ↥(StatedSL 3 F)) : GL (Fin 3) F)) h1
    simpa using this
  have hcomm : ∀ A ∈ E₃, ∀ B ∈ E₃, A * B = B * A := by
    intro A hA B hB
    obtain ⟨e, he, rfl⟩ := hmem A hA
    obtain ⟨f, hf, rfl⟩ := hmem B hB
    have h1 : e * f = f * e := Subtype.ext (hE.1 _ he _ hf)
    have := congrArg (fun x : ↥L => ((πL.symm x : ↥(StatedSL 3 F)) : GL (Fin 3) F)) h1
    simpa using this
  have := H.card_le_of_elemAbelian_GL3 E₃ hsq hcomm
  rw [hc1, Nat.card_eq_fintype_card (α := F)] at this
  exact this

theorem mem_statedSL_of_det {F : Type} [Field F] {g : GL (Fin 3) F}
    (h : (g : Matrix (Fin 3) (Fin 3) F).det = 1) : g ∈ StatedSL 3 F :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

end Transport

section Steps

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_lpart {L A : Subgroup (MulAut V)} {U : Subgroup V}
    (hUL : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (hfaith : ∀ l ∈ L, (∀ u ∈ U, l u = u) → l = 1)
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ u ∈ U, a u = l u) :
    ∃ φ : ↥A →* ↥L, ∀ a : ↥A, ∀ u ∈ U, (a : MulAut V) u = (φ a : MulAut V) u := by
  have huniq : ∀ l l' : MulAut V, l ∈ L → l' ∈ L → (∀ u ∈ U, l u = l' u) → l = l' := by
    intro l l' hl hl' h
    have h1 : l'⁻¹ * l = 1 := hfaith _ (L.mul_mem (L.inv_mem hl') hl) (fun u hu => by
      rw [MulAut.mul_apply, h u hu, MulAut.inv_apply_self])
    calc l = l' * (l'⁻¹ * l) := by group
      _ = l' := by rw [h1, mul_one]
  choose f hfL hfU using hinner
  refine ⟨{ toFun := fun a => ⟨f a a.2, hfL a a.2⟩
            map_one' := ?_
            map_mul' := ?_ }, fun a u hu => hfU a a.2 u hu⟩
  · apply Subtype.ext
    exact huniq _ _ (hfL _ _) L.one_mem (fun u hu => (hfU _ _ u hu).symm)
  · intro a b
    apply Subtype.ext
    refine huniq _ _ (hfL _ _) (L.mul_mem (hfL _ _) (hfL _ _)) (fun u hu => ?_)
    rw [← hfU _ _ u hu]
    show (a * b : MulAut V) u = (f a a.2 * f b b.2) u
    rw [MulAut.mul_apply, MulAut.mul_apply, hfU b b.2 u hu,
      hfU a a.2 _ (hUL _ (hfL b b.2) u hu)]

variable {m r : ℕ}

theorem centralizes_of_rk_le (hV : ∀ v : V, v ^ 2 = 1) (hm : 0 < m)
    (hr : IsPrimitivePrimeDivisor r (3 * m)) {L K : Subgroup (MulAut V)}
    {F' : Type} [Field F'] [Fintype F'] [CharP F' 2] (πK : ↥(StatedSL 3 F') ≃* ↥K)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hLK : ∀ l ∈ L, ∀ x ∈ K, l * x = x * l) {s : MulAut V} (hsL : s ∈ L) (hs : s ^ r = 1)
    (hsz : ∃ l ∈ L, l * s ≠ s * l) (hrk : rk (cs s) ≤ 6 * m) :
    ∀ x ∈ K, ∀ w ∈ commV L, x w = w := by
  let t : ∀ (i j : Fin 3), i ≠ j → MulAut V := fun i j h =>
    ((πK ⟨tv i j h, mem_statedSL_of_det (det_tv i j h)⟩ : ↥K) : MulAut V)
  have htK : ∀ i j h, t i j h ∈ K := fun i j h => (πK _).2
  have ht_mul : ∀ (a b : ↥(StatedSL 3 F')), ((πK (a * b) : ↥K) : MulAut V) =
      (πK a : MulAut V) * (πK b : MulAut V) := fun a b => by rw [map_mul, Subgroup.coe_mul]
  have hsq : ∀ i j h, t i j h * t i j h = 1 := by
    intro i j h
    have : (⟨tv i j h, mem_statedSL_of_det (det_tv i j h)⟩ : ↥(StatedSL 3 F')) *
        ⟨tv i j h, mem_statedSL_of_det (det_tv i j h)⟩ = 1 :=
      Subtype.ext (tv_mul_self i j h)
    show ((πK _ : ↥K) : MulAut V) * (πK _ : MulAut V) = 1
    rw [← ht_mul, this, map_one, Subgroup.coe_one]
  have hsq3 : t 0 1 (by decide) * t 1 2 (by decide) * t 0 1 (by decide) * t 1 2 (by decide) =
      t 0 2 (by decide) := by
    simp only [t]
    rw [← ht_mul, ← ht_mul, ← ht_mul]
    congr 2
    exact Subtype.ext tv_comm_square
  have hc31 : t 0 2 (by decide) * t 0 1 (by decide) = t 0 1 (by decide) * t 0 2 (by decide) := by
    simp only [t]
    rw [← ht_mul, ← ht_mul]
    congr 2
    exact Subtype.ext tv02_comm_tv01
  have hc32 : t 0 2 (by decide) * t 1 2 (by decide) = t 1 2 (by decide) * t 0 2 (by decide) := by
    simp only [t]
    rw [← ht_mul, ← ht_mul]
    congr 2
    exact Subtype.ext tv02_comm_tv12
  have hnc : t 0 2 (by decide) * t 2 1 (by decide) ≠ t 2 1 (by decide) * t 0 2 (by decide) := by
    simp only [t]
    rw [← ht_mul, ← ht_mul]
    intro h
    have h1 := πK.injective (Subtype.ext h)
    exact tv02_not_comm_tv21 (congrArg Subtype.val h1)
  have hcs : ∀ i j h, t i j h * s = s * t i j h := fun i j h => (hLK s hsL _ (htK i j h)).symm
  have hfix3 := fix_of_comm_square hV hm hr hs hrk (hcs _ _ _) (hcs _ _ _) (hsq _ _ _)
    (hsq _ _ _) (hsq 0 2 (by decide)) hsq3 hc31 hc32
  set K₀ : Subgroup ↥K := (centSub (cs s)).subgroupOf K with hK₀
  have hK₀n : K₀.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hK₀, Subgroup.mem_subgroupOf] at hx ⊢
    intro w hw
    have hg' : (g : MulAut V)⁻¹ * s = s * (g : MulAut V)⁻¹ :=
      (hLK s hsL _ (K.inv_mem g.2)).symm
    have hw' : (g : MulAut V)⁻¹ w ∈ cs s := cs_inv_of_comm hg' w hw
    show (g : MulAut V) ((x : MulAut V) ((g : MulAut V)⁻¹ w)) = w
    rw [hx _ hw', MulAut.apply_inv_self]
  have h3K₀ : (⟨t 0 2 (by decide), htK 0 2 _⟩ : ↥K) ∈ K₀ := by
    rw [hK₀, Subgroup.mem_subgroupOf]
    exact hfix3
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKq K₀ with h | h
  · exfalso
    have hc := Subgroup.mem_center_iff.mp (h h3K₀) ⟨t 2 1 (by decide), htK 2 1 _⟩
    exact hnc (congrArg Subtype.val hc).symm
  ·
    have hKs : cs s ≤ fixV K := by
      intro w hw x hx
      have : (⟨x, hx⟩ : ↥K) ∈ K₀ := h ▸ Subgroup.mem_top _
      rw [hK₀, Subgroup.mem_subgroupOf] at this
      exact this w hw
    have hY : ∀ l ∈ L, ∀ y ∈ fixV K, l y ∈ fixV K := by
      intro l hl y hy x hx
      rw [← MulAut.mul_apply, ← hLK l hl x hx, MulAut.mul_apply, hy x hx]
    have := commV_le_of_cs_le hLq hsL hsz hY hKs
    intro x hx w hw
    exact this hw x hx

end Steps

section Main

variable {V : Type} [CommGroup V] [Finite V]

theorem rk_le_of_card_le {A : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hA : IsElemAbelian2 A) (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) :
    rk V ≤ rk A + rk (fixV A) := by
  have h1 : Nat.card V = 2 ^ rk V := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have h2 : Nat.card A = 2 ^ rk A := card_eq_two_pow_of_isPGroup hA.isPGroup
  rw [h1, h2, card_eq_two_pow hV, ← pow_add] at hoff
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hoff

theorem rk_le_of_card_le_sq {X : Subgroup (MulAut V)} (hX : IsElemAbelian2 X) {n : ℕ}
    (h : Nat.card X ≤ (2 ^ n) ^ 2) : rk X ≤ 2 * n := by
  rw [card_eq_two_pow_of_isPGroup hX.isPGroup, ← pow_mul, mul_comm] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

theorem counting_false (hV : ∀ v : V, v ^ 2 = 1) {L K A : Subgroup (MulAut V)} {U : Subgroup V}
    {F F' : Type} [Field F] [Fintype F] [Field F'] [Fintype F'] {m k : ℕ} (hm : Odd m)
    (hF : Fintype.card F = 2 ^ m) (hF' : Fintype.card F' = 2 ^ k) (hkm : k ≤ m)
    (πL : ↥(StatedSL 3 F) ≃* ↥L) (πK : ↥(StatedSL 3 F') ≃* ↥K)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hLK : ∀ l ∈ L, ∀ x ∈ K, l * x = x * l) (hAel : IsElemAbelian2 A)
    (hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A)) (hUrk : rk U = 3 * m)
    (hUfix : ∀ l ∈ L, l ≠ 1 → rk ↥(U ⊓ fixV (Subgroup.zpowers l)) ≤ 2 * m)
    (φ : ↥A →* ↥L) (hφU : ∀ a : ↥A, ∀ u ∈ U, (a : MulAut V) u = (φ a : MulAut V) u)
    (hφK : ∀ a : ↥A, (φ a : MulAut V)⁻¹ * a ∈ K)
    (hW0 : ∀ w : V, (∀ a : ↥A, ((φ a : MulAut V)⁻¹ * a) w = w) → ∀ l ∈ L, l w * w⁻¹ ∈ U)
    (hAU : ∃ a : ↥A, φ a ≠ 1) (hnc : ¬ ∀ x ∈ K, ∀ w ∈ commV L, x w = w) : False := by
  have hm0 : 0 < m := hm.pos
  have : CharP F 2 := charP_two_of_card hF
  have : CharP F' 2 := charP_two_of_card hF'
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 3 * m) (by omega) (by
    obtain ⟨j, hj⟩ := hm
    omega)
  have : Fact r.Prime := ⟨hr.prime⟩
  have hodd : Odd r := hr.prime.odd_of_ne_two (ppd_ne_two hm0 hr)
  have hψmul : ∀ a b : ↥A, (φ (a * b) : MulAut V)⁻¹ * (a * b : ↥A) =
      ((φ a : MulAut V)⁻¹ * a) * ((φ b : MulAut V)⁻¹ * b) := by
    intro a b
    have hc : ((φ a : MulAut V)⁻¹ * a) * (φ b : MulAut V)⁻¹ =
        (φ b : MulAut V)⁻¹ * ((φ a : MulAut V)⁻¹ * a) :=
      (hLK _ (L.inv_mem (φ b).2) _ (hφK a)).symm
    rw [map_mul, Subgroup.coe_mul, Subgroup.coe_mul, mul_inv_rev]
    calc (φ b : MulAut V)⁻¹ * (φ a : MulAut V)⁻¹ * ((a : MulAut V) * b) =
        (φ b : MulAut V)⁻¹ * ((φ a : MulAut V)⁻¹ * a) * b := by group
      _ = ((φ a : MulAut V)⁻¹ * a) * (φ b : MulAut V)⁻¹ * b := by rw [hc]
      _ = _ := by group
  let ψ : ↥A →* MulAut V :=
    { toFun := fun a => (φ a : MulAut V)⁻¹ * a
      map_one' := by simp
      map_mul' := hψmul }
  have hψ : ∀ a : ↥A, ψ a = (φ a : MulAut V)⁻¹ * a := fun a => rfl
  have hdec : ∀ a : ↥A, (a : MulAut V) = φ a * ψ a := fun a => by rw [hψ]; group
  have hψK : ∀ a : ↥A, ψ a ∈ K := hφK
  have hψU : ∀ a : ↥A, ∀ u ∈ U, ψ a u = u := by
    intro a u hu
    rw [hψ, MulAut.mul_apply, hφU a u hu, MulAut.inv_apply_self]
  have hAsq : ∀ a : ↥A, a * a = 1 := fun a => Subtype.ext (by simpa [sq] using hAel.2 a a.2)
  have hφsq : ∀ a : ↥A, (φ a : MulAut V) * φ a = 1 := by
    intro a
    rw [← Subgroup.coe_mul, ← map_mul, hAsq, map_one, Subgroup.coe_one]
  have hψsq : ∀ a : ↥A, ψ a * ψ a = 1 := by
    intro a
    rw [← map_mul, hAsq, map_one]
  set AL : Subgroup (MulAut V) := φ.range.map L.subtype with hAL
  set AK : Subgroup (MulAut V) := ψ.range with hAK
  set B : Subgroup (MulAut V) := φ.ker.map A.subtype with hB
  have hAcomm : ∀ a b : ↥A, a * b = b * a := fun a b => Subtype.ext (hAel.1 _ a.2 _ b.2)
  have hALel : IsElemAbelian2 AL := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩ _ ⟨_, ⟨b, rfl⟩, rfl⟩
      simp only [Subgroup.coe_subtype]
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hAcomm]
    · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      simp only [Subgroup.coe_subtype]
      rw [sq, hφsq]
  have hAKel : IsElemAbelian2 AK := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul, hAcomm]
    · rintro _ ⟨a, rfl⟩
      rw [sq, hψsq]
  have hBel : IsElemAbelian2 B := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
      exact hAel.1 _ a.2 _ b.2
    · rintro _ ⟨a, -, rfl⟩
      exact hAel.2 _ a.2
  have hALL : AL ≤ L := Subgroup.map_subtype_le _
  have hAKK : AK ≤ K := by rintro _ ⟨a, rfl⟩; exact hψK a
  have hBAK : B ≤ AK := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ?_⟩
    rw [hψ, MonoidHom.mem_ker.mp ha, Subgroup.coe_one, inv_one, one_mul]
    rfl
  have hBK : B ≤ K := hBAK.trans hAKK
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBU : ∀ b ∈ B, ∀ u ∈ U, b u = u := by
    rintro _ ⟨a, ha, rfl⟩ u hu
    rw [Subgroup.coe_subtype, hφU a u hu, MonoidHom.mem_ker.mp ha, Subgroup.coe_one,
      MulAut.one_apply]
  have hrkA : rk A = rk AL + rk B := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card AL = Nat.card φ.range := Subgroup.card_map_of_injective L.subtype_injective
    have h3 : Nat.card B = Nat.card φ.ker := Subgroup.card_map_of_injective A.subtype_injective
    unfold rk
    rw [h2, h3, ← padicValNat.mul (card_subgroup_pos _).ne' (card_subgroup_pos _).ne', mul_comm,
      h1]
  have hrkAL : rk AL ≤ 2 * m := by
    refine rk_le_of_card_le_sq hALel ?_
    rw [← hF]
    exact card_le_of_elemAbelian_sub πL hALL hALel
  have hrkAK : rk AK ≤ 2 * k := by
    refine rk_le_of_card_le_sq hAKel ?_
    rw [← hF']
    exact card_le_of_elemAbelian_sub πK hAKK hAKel
  have hrkB : rk B ≤ rk AK := rk_mono hBAK
  have hrkV : rk V ≤ rk A + rk (fixV A) := rk_le_of_card_le hV hAel hoff
  obtain ⟨a₀, ha₀⟩ := hAU
  set τ : GL (Fin 3) F := (πL.symm (φ a₀)).1 with hτ
  have hτ2 : τ * τ = 1 := by
    have h1 : φ a₀ * φ a₀ = 1 := Subtype.ext (hφsq a₀)
    have := congrArg (fun x : ↥L => ((πL.symm x : ↥(StatedSL 3 F)) : GL (Fin 3) F)) h1
    simpa [hτ] using this
  have hτ1 : τ ≠ 1 := by
    intro h
    apply ha₀
    have h1 : πL.symm (φ a₀) = 1 := Subtype.ext h
    have := congrArg πL h1
    simpa using this
  obtain ⟨g, h, hgd, hhd, hord⟩ := exists_conj_product hF hm0 hr hτ2 hτ1
  set τ' : ↥(StatedSL 3 F) := πL.symm (φ a₀) with hτ'
  set gS : ↥(StatedSL 3 F) := ⟨g, mem_statedSL_of_det hgd⟩ with hgS
  set hS : ↥(StatedSL 3 F) := ⟨h, mem_statedSL_of_det hhd⟩ with hhS
  set y' : ↥(StatedSL 3 F) := τ' * (gS * τ' * gS⁻¹) * (hS * τ' * hS⁻¹) with hy'
  have hy'ord : orderOf y' = r := by
    rw [← Subgroup.orderOf_coe, ← hord]
    rfl
  set g' : ↥L := πL gS with hg'
  set h' : ↥L := πL hS with hh'
  set sL : ↥L := πL y' with hsL
  have hsL_eq : sL = φ a₀ * (g' * φ a₀ * g'⁻¹) * (h' * φ a₀ * h'⁻¹) := by
    rw [hsL, hy', map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hτ',
      MulEquiv.apply_symm_apply]
  set s : MulAut V := (sL : MulAut V) with hs
  have hsLmem : s ∈ L := sL.2
  have hsord : orderOf s = r := by
    rw [hs, Subgroup.orderOf_coe, hsL, MulEquiv.orderOf_eq, hy'ord]
  have hspow : s ^ r = 1 := by rw [← hsord]; exact pow_orderOf_eq_one s
  have hsz : ∃ l ∈ L, l * s ≠ s * l := by
    refine ⟨(πL ⟨E02, mem_statedSL_of_det (det_tv 0 2 (by decide))⟩ : MulAut V),
      (πL _).2, ?_⟩
    intro hc
    have hyord : orderOf (y' : GL (Fin 3) F) = r := by rw [Subgroup.orderOf_coe, hy'ord]
    apply not_comm_E02 hF hm0 hr hyord
    have h1 : πL ⟨E02, mem_statedSL_of_det (det_tv 0 2 (by decide))⟩ * sL =
        sL * πL ⟨E02, mem_statedSL_of_det (det_tv 0 2 (by decide))⟩ := Subtype.ext hc
    rw [hsL, ← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val (πL.injective h1)
    exact h2.symm
  set a : MulAut V := (a₀ : MulAut V) with ha
  set p : MulAut V := (φ a₀ : MulAut V) with hp
  set c : MulAut V := ψ a₀ with hcdef
  set gg : MulAut V := (g' : MulAut V) with hgg
  set hh : MulAut V := (h' : MulAut V) with hhh
  have hcL : ∀ l ∈ L, l * c = c * l := fun l hl => hLK l hl c (hψK a₀)
  have hac : a = p * c := hdec a₀
  have hcc : c * c = 1 := hψsq a₀
  have hs_eq : s = p * (gg * p * gg⁻¹) * (hh * p * hh⁻¹) := by
    rw [hs, hsL_eq]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hp, hgg, hhh]
  have hconj : ∀ l ∈ L, l * a * l⁻¹ = (l * p * l⁻¹) * c := by
    intro l hl
    have h1 := hcL _ (L.inv_mem hl)
    calc l * a * l⁻¹ = l * p * (c * l⁻¹) := by rw [hac]; group
      _ = l * p * (l⁻¹ * c) := by rw [h1]
      _ = (l * p * l⁻¹) * c := by group
  set x₃ : MulAut V := a * (gg * a * gg⁻¹) * (hh * a * hh⁻¹) with hx₃
  have hx₃s : x₃ = s * c := by
    have hP1 : gg * p * gg⁻¹ ∈ L := L.mul_mem (L.mul_mem g'.2 (φ a₀).2) (L.inv_mem g'.2)
    rw [hx₃, hconj _ g'.2, hconj _ h'.2, hac, hs_eq]
    have h1 := hcL _ hP1
    calc p * c * ((gg * p * gg⁻¹) * c) * ((hh * p * hh⁻¹) * c) =
        p * (c * (gg * p * gg⁻¹)) * c * ((hh * p * hh⁻¹) * c) := by group
      _ = p * ((gg * p * gg⁻¹) * c) * c * ((hh * p * hh⁻¹) * c) := by rw [h1]
      _ = p * (gg * p * gg⁻¹) * (c * c) * ((hh * p * hh⁻¹) * c) := by group
      _ = p * (gg * p * gg⁻¹) * (hh * p * hh⁻¹) * c := by rw [hcc, mul_one]; group
  have hx₃sq : x₃ ^ 2 = s ^ 2 := by
    rw [sq, sq, hx₃s]
    have h1 := hcL s hsLmem
    calc s * c * (s * c) = s * (c * s) * c := by group
      _ = s * (s * c) * c := by rw [h1]
      _ = s * s * (c * c) := by group
      _ = s * s := by rw [hcc, mul_one]
  have hcs_le : cs s ≤ cs x₃ := by
    obtain ⟨j, hj⟩ := hodd
    have hpow : (s ^ 2) ^ (j + 1) = s := by
      rw [← pow_mul, show 2 * (j + 1) = r + 1 by omega, pow_succ, hspow, one_mul]
    calc cs s = cs ((s ^ 2) ^ (j + 1)) := by rw [hpow]
      _ ≤ cs (s ^ 2) := cs_pow_le _ _
      _ = cs (x₃ ^ 2) := by rw [hx₃sq]
      _ ≤ cs x₃ := cs_pow_le _ _
  have hrk_cs : rk (cs s) ≤ 3 * rk (cs a) := by
    have h1 : cs x₃ ≤ cs a ⊔ cs (gg * a * gg⁻¹) ⊔ cs (hh * a * hh⁻¹) := by
      rw [hx₃]
      exact (cs_mul_le _ _).trans (sup_le_sup_right (cs_mul_le _ _) _)
    have h2 := rk_mono (hcs_le.trans h1)
    have h3 := rk_sup_le (cs a ⊔ cs (gg * a * gg⁻¹)) (cs (hh * a * hh⁻¹))
    have h4 := rk_sup_le (cs a) (cs (gg * a * gg⁻¹))
    rw [rk_cs_conj] at h3 h4
    omega
  have hrk_a : rk (cs a) + rk (fixV A) ≤ rk V := rk_cs_add_le a₀.2
  have hdvd : 3 * m ∣ rk (cs s) := three_mul_dvd_rk_of_le_cs hV hm0 hr hspow (cs_inv s) le_rfl
  have hgt : 6 * m < rk (cs s) := by
    by_contra hle
    push Not at hle
    exact hnc (centralizes_of_rk_le hV hm0 hr πK hLq hKq hLK hsLmem hspow hsz hle)
  have h9 : 9 * m ≤ rk (cs s) := by
    obtain ⟨j, hj⟩ := hdvd
    rw [hj] at hgt ⊢
    have : 2 < j := by
      by_contra h
      push Not at h
      have : 3 * m * j ≤ 3 * m * 2 := Nat.mul_le_mul_left _ h
      omega
    calc 9 * m = 3 * m * 3 := by ring
      _ ≤ 3 * m * j := Nat.mul_le_mul_left _ this
  have hBne : B ≠ ⊥ := by
    intro hB0
    have : rk B = 0 := by rw [hB0, rk_bot]
    omega
  have hLB : ¬ commV L ≤ fixV B := by
    intro hle
    set K₁ : Subgroup ↥K := (centSub (commV L)).subgroupOf K with hK₁
    have hK₁n : K₁.Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [hK₁, Subgroup.mem_subgroupOf] at hx ⊢
      intro w hw
      have hg' : ∀ l ∈ L, (g : MulAut V)⁻¹ * l = l * (g : MulAut V)⁻¹ :=
        fun l hl => (hLK l hl _ (K.inv_mem g.2)).symm
      have hw' := commV_inv_of_comm hg' w hw
      show (g : MulAut V) ((x : MulAut V) ((g : MulAut V)⁻¹ w)) = w
      rw [hx _ hw', MulAut.apply_inv_self]
    obtain ⟨⟨b, hbB⟩, hb1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
    have hb1 : b ≠ 1 := fun h => hb1' (Subtype.ext h)
    have hbK₁ : (⟨b, hBK hbB⟩ : ↥K) ∈ K₁ := by
      rw [hK₁, Subgroup.mem_subgroupOf]
      intro w hw
      exact hle hw b hbB
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hKq K₁ with h | h
    ·
      have hbc := Subgroup.mem_center_iff.mp (h hbK₁)
      set z : GL (Fin 3) F' := (πK.symm ⟨b, hBK hbB⟩).1 with hz
      have hb2 : (⟨b, hBK hbB⟩ : ↥K) * ⟨b, hBK hbB⟩ = 1 :=
        Subtype.ext (by simpa [sq] using hBel.2 b hbB)
      refine not_central_involution (z := z) ?_ ?_ ?_
      · have h1 : πK.symm ⟨b, hBK hbB⟩ * πK.symm ⟨b, hBK hbB⟩ = 1 := by
          rw [← map_mul, hb2, map_one]
        exact congrArg Subtype.val h1
      · intro hz1
        apply hb1
        have h1 : πK.symm ⟨b, hBK hbB⟩ = 1 := Subtype.ext hz1
        have := congrArg (fun x => ((πK x : ↥K) : MulAut V)) h1
        simpa using this
      · intro g hg
        have h1 := hbc (πK ⟨g, mem_statedSL_of_det hg⟩)
        have h2 := congrArg (fun x => ((πK.symm x : ↥(StatedSL 3 F')) : GL (Fin 3) F')) h1
        simpa [hz] using h2
    · apply hnc
      intro x hx w hw
      have : (⟨x, hx⟩ : ↥K) ∈ K₁ := h ▸ Subgroup.mem_top _
      rw [hK₁, Subgroup.mem_subgroupOf] at this
      exact this w hw
  have hBinv : ∀ l ∈ L, ∀ y ∈ fixV B, l y ∈ fixV B := by
    intro l hl y hy b hb
    rw [← MulAut.mul_apply, ← hLK l hl b (hBK hb), MulAut.mul_apply, hy b hb]
  have hcsB : ¬ cs s ≤ fixV B := fun hle => hLB (commV_le_of_cs_le hLq hsLmem hsz hBinv hle)
  have hrkB1 : rk (fixV B) + 3 * m ≤ rk V := by
    set N₁ := cs s ⊓ fixV B with hN₁
    have hN₁s : ∀ v ∈ N₁, s v ∈ N₁ := fun v hv => ⟨cs_inv s v hv.1, hBinv s hsLmem v hv.2⟩
    have hdN := three_mul_dvd_rk_of_le_cs hV hm0 hr hspow hN₁s inf_le_left
    have hlt : rk N₁ < rk (cs s) := by
      by_contra hge
      push Not at hge
      exact hcsB (by rw [← eq_of_le_of_rk_le hV inf_le_left hge]; exact inf_le_right)
    have hle := rk_le_inf_add (cs s) (fixV B)
    obtain ⟨j₁, hj₁⟩ := hdN
    obtain ⟨j₂, hj₂⟩ := hdvd
    rw [hj₁, hj₂] at hlt
    have hjj : j₁ + 1 ≤ j₂ := Nat.lt_of_mul_lt_mul_left hlt
    have : 3 * m * (j₁ + 1) ≤ 3 * m * j₂ := Nat.mul_le_mul_left _ hjj
    rw [← hN₁] at hle
    rw [hj₁, hj₂] at hle
    nlinarith
  have hrkB2 : rk (fixV A) + m ≤ rk (fixV B) := by
    have hUB : U ≤ fixV B := fun u hu b hb => hBU b hb u hu
    have hAB : fixV A ≤ fixV B := B1.fixV_le_fixV hBA
    have hp1 : p ≠ 1 := fun h => ha₀ (Subtype.ext h)
    have hUA : U ⊓ fixV A ≤ U ⊓ fixV (Subgroup.zpowers p) := by
      rintro u ⟨hu, huA⟩
      refine ⟨hu, mem_fixV_zpowers.mpr ?_⟩
      rw [← hφU a₀ u hu]
      exact huA _ a₀.2
    have h1 : rk ↥(U ⊓ fixV A) ≤ rk ↥(U ⊓ fixV (Subgroup.zpowers p)) := rk_mono hUA
    have h2 : rk ↥(U ⊓ fixV (Subgroup.zpowers p)) ≤ 2 * m := hUfix p (φ a₀).2 hp1
    have h3 : rk ↥(U ⊔ fixV A) + rk ↥(U ⊓ fixV A) = rk U + rk (fixV A) :=
      rk_sup_add_rk_inf U (fixV A)
    have h4 : rk ↥(U ⊔ fixV A) ≤ rk (fixV B) := rk_mono (sup_le hUB hAB)
    omega
  have hrkA4 : 4 * m ≤ rk A := by omega
  have hrkB2m : 2 * m ≤ rk B := by omega
  have hBAKeq : B = AK := by
    have h2k : 2 * k ≤ 2 * m := by omega
    refine Subgroup.eq_of_le_of_card_ge hBAK ?_
    rw [card_eq_two_pow_of_isPGroup hAKel.isPGroup, card_eq_two_pow_of_isPGroup hBel.isPGroup]
    exact Nat.pow_le_pow_right (by norm_num) (le_trans hrkAK (le_trans h2k hrkB2m))
  have hrkV3 : rk V ≤ 3 * m + rk (fixV B) := by omega
  have hfixW : ∀ w ∈ fixV B, ∀ l ∈ L, l w * w⁻¹ ∈ U := by
    intro w hw l hl
    refine hW0 w (fun a' => ?_) l hl
    have : ψ a' ∈ B := by rw [hBAKeq]; exact ⟨a', rfl⟩
    exact hw _ this
  have hmapU : (fixV B).map (commMap s) ≤ U := by
    rintro _ ⟨w, hw, rfl⟩
    exact hfixW w hw s hsLmem
  have hinfU : cs s ⊓ fixV B ≤ U := fun w hw =>
    hmapU (mem_map_of_mem_cs hV hspow hodd (hBinv s hsLmem) hw.2 hw.1)
  have h6 : rk (cs s) ≤ 6 * m := by
    have h1 := rk_le_inf_add (cs s) (fixV B)
    have h2 := rk_mono hinfU
    omega
  omega

end Main

end SmithB57

end CFSG.Quasithin
