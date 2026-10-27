module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3Semi
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.L3 CFSG.Quasithin.SL2Semilinear

section FieldFour

variable {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] in
theorem pow_four_of_card_four (hF : Nat.card F = 4) (t : F) : t ^ 4 = t := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card t
  rwa [← Nat.card_eq_fintype_card, hF] at h

theorem sq_add_self_add_one_of_card_four (hF : Nat.card F = 4) {t : F} (h0 : t ≠ 0)
    (h1 : t ≠ 1) : t ^ 2 + t + 1 = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h4 := pow_four_of_card_four hF t
  have hprod : t * (t + 1) * (t ^ 2 + t + 1) = 0 := by
    linear_combination h4 + h2 * (t ^ 3 + t ^ 2 + t)
  have ht1 : t + 1 ≠ 0 := by
    intro h
    apply h1
    linear_combination h - h2
  rcases mul_eq_zero.mp hprod with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h h0
    · exact absurd h ht1
  · exact h

theorem eq_of_card_four (hF : Nat.card F = 4) {t : F} (h0 : t ≠ 0) (h1 : t ≠ 1) (s : F) :
    s = 0 ∨ s = 1 ∨ s = t ∨ s = t + 1 := by
  by_cases hs0 : s = 0
  · exact Or.inl hs0
  by_cases hs1 : s = 1
  · exact Or.inr (Or.inl hs1)
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hs := sq_add_self_add_one_of_card_four hF hs0 hs1
  have ht := sq_add_self_add_one_of_card_four hF h0 h1
  have hst : (s + t) * (s + t + 1) = 0 := by linear_combination hs + ht + h2 * (s * t - 1)
  rcases mul_eq_zero.mp hst with h | h
  · exact Or.inr (Or.inr (Or.inl (by linear_combination h - h2 * t)))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h - h2 * (t + 1))))

omit [CharP F 2] in
theorem exists_ne_zero_one_of_card_four (hF : Nat.card F = 4) : ∃ t : F, t ≠ 0 ∧ t ≠ 1 := by
  classical
  have := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun s _ => by
    by_cases h : s = 0
    · simp [h]
    · simp [hcon s h]
  have h4 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at h4
  have : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

theorem ringHom_eq_id_or_sq (hF : Nat.card F = 4) (σ : F →+* F) :
    (∀ s, σ s = s) ∨ ∀ s, σ s = s ^ 2 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨t, h0, h1⟩ := exists_ne_zero_one_of_card_four hF
  have ht := sq_add_self_add_one_of_card_four hF h0 h1
  have hσ0 : σ t ≠ 0 := fun h => h0 (σ.injective (by rw [h, map_zero]))
  have hσ1 : σ t ≠ 1 := fun h => h1 (σ.injective (by rw [h, map_one]))
  have hall := eq_of_card_four hF h0 h1
  rcases hall (σ t) with h | h | h | h
  · exact absurd h hσ0
  · exact absurd h hσ1
  · left
    intro s
    rcases hall s with hs | hs | hs | hs <;> rw [hs]
    · exact map_zero σ
    · exact map_one σ
    · exact h
    · rw [map_add, map_one, h]
  · right
    intro s
    rcases hall s with hs | hs | hs | hs <;> rw [hs]
    · simp
    · simp
    · rw [h]
      linear_combination -ht + h2 * (t + 1)
    · rw [map_add, map_one, h]
      linear_combination -ht + h2

theorem ringHom_apply_apply_of_card_four (hF : Nat.card F = 4) (σ : F →+* F) (s : F) :
    σ (σ s) = s := by
  rcases ringHom_eq_id_or_sq hF σ with h | h
  · rw [h, h]
  · rw [h, h, ← pow_mul]
    exact pow_four_of_card_four hF s

theorem ringHom_eq_sq_of_ne (hF : Nat.card F = 4) {σ : F →+* F} (hσ : ∃ c, σ c ≠ c) (s : F) :
    σ s = s ^ 2 := by
  rcases ringHom_eq_id_or_sq hF σ with h | h
  · obtain ⟨c, hc⟩ := hσ
    exact absurd (h c) hc
  · exact h s

theorem eq_zero_or_one_of_fix (hF : Nat.card F = 4) {σ : F →+* F} (hσ : ∃ c, σ c ≠ c) {μ : F}
    (hμ : σ μ = μ) : μ = 0 ∨ μ = 1 := by
  rw [ringHom_eq_sq_of_ne hF hσ] at hμ
  have hm : μ * (μ - 1) = 0 := by linear_combination hμ
  rcases mul_eq_zero.mp hm with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

end FieldFour

section Lower

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] [Finite F]

omit [Finite F] in
theorem V1Coords.sigma_fix_of_lower {G₁ B₁ L V₁ V₂ Z : Subgroup G}
    (C : V1Coords G₁ B₁ L V₁ V₂ Z F) {x h : G}
    (hxV : x ∈ Subgroup.normalizer (V₁ : Set G)) (hhV : h ∈ Subgroup.normalizer (V₁ : Set G))
    {τ : F × F ≃+ F × F} {σ : F →+* F} (hτ : ∀ p, C.ι (τ p) = x * C.ι p * x⁻¹)
    (hσ : ∀ (c : F) (p : F × F), τ (c • p) = σ c • τ p) (hZ : (τ (0, 1)).1 = 0)
    {μ β : F} (hμ : μ ≠ 0) (hh : ∀ u v, h * C.ι (u, v) * h⁻¹ = C.ι (μ * u, β * u + v))
    {k : ℕ} (hk : (x * h * x⁻¹ * h⁻¹) ^ 2 ^ k = 1) : σ μ = μ := by
  set c := x * h * x⁻¹ * h⁻¹ with hc
  have hcV : c ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxV hhV) (Subgroup.inv_mem _ hxV))
      (Subgroup.inv_mem _ hhV)
  obtain ⟨τc, hτc⟩ := C.exists_conj_equiv hcV
  set a := (τ (1, 0)).1 with ha
  have hfst := fst_of_semilinear hσ hZ
  have hrel : ∀ p, τc (μ * (τ p).1, β * (τ p).1 + (τ p).2) = τ (μ * p.1, β * p.1 + p.2) :=
    fun p => C.inj (by
      rw [hτc, ← hh, hτ, hτ, ← hh]
      rw [hc]
      group)
  have hν : ∀ w : F × F, (τc w).1 = (σ μ * μ⁻¹) * w.1 := by
    intro w
    obtain ⟨w₁, w₂⟩ := w
    set p := τ.symm (μ⁻¹ * w₁, w₂ - β * (μ⁻¹ * w₁)) with hp
    have hτp : τ p = (μ⁻¹ * w₁, w₂ - β * (μ⁻¹ * w₁)) := τ.apply_symm_apply _
    have h1 : μ⁻¹ * w₁ = σ p.1 * a := by
      have := hfst p
      rw [hτp] at this
      exact this
    have e : ((w₁, w₂) : F × F) = (μ * (τ p).1, β * (τ p).1 + (τ p).2) := by
      rw [hτp]
      ext
      · show w₁ = μ * (μ⁻¹ * w₁)
        field_simp
      · show w₂ = β * (μ⁻¹ * w₁) + (w₂ - β * (μ⁻¹ * w₁))
        ring
    have h2 : (τc (w₁, w₂)).1 = σ (μ * p.1) * a := by
      rw [e, hrel, hfst]
    rw [h2, map_mul, mul_assoc, ← h1]
    field_simp
  have := C.eq_one_of_two_power hτc hν hk
  field_simp at this
  linear_combination this

end Lower

section Linear

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}
  {F : Type} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] [Finite F] in
theorem mem_S_of_linear (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {G₁ B₁ L' V₁ V₂ : Subgroup G} (C : V1Coords G₁ B₁ L' V₁ V₂ (sec53ZS T L) F)
    {z : G} (hz : z ∈ sec53ZS T L) (hzT : z ∈ centerOf T) (hz1 : z ≠ 1) {t : G} (htT : t ∈ T)
    {τ : F × F ≃+ F × F} (hτ : ∀ p, C.ι (τ p) = t * C.ι p * t⁻¹)
    (hlin : ∀ (c : F) (p : F × F), τ (c • p) = c • τ p) : t ∈ sec53S T L := by
  obtain ⟨c₀, rfl⟩ := (C.center z).mp hz
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hz1
    have := C.add 0 0
    rw [add_zero] at this
    have h0 : C.ι ((0 : F), (0 : F)) = C.ι 0 := rfl
    rw [h0]
    exact mul_eq_left.mp this.symm
  have hfix0 : τ (0, c₀) = (0, c₀) := C.inj (by
    rw [hτ]
    have hc := Subgroup.mem_centralizer_iff.mp
      ((inf_le_right : centerOf T ≤ Subgroup.centralizer (T : Set G)) hzT) t htT
    calc t * C.ι (0, c₀) * t⁻¹ = C.ι (0, c₀) * t * t⁻¹ := by rw [hc]
      _ = C.ι (0, c₀) := by group)
  have hfix : ∀ c : F, τ (0, c) = (0, c) := by
    intro c
    have e : ((0 : F), c) = (c * c₀⁻¹) • ((0 : F), c₀) := by
      ext
      · simp
      · show c = c * c₀⁻¹ * c₀
        field_simp
    rw [e, hlin, hfix0]
  have htC : t ∈ Subgroup.centralizer (sec53ZS T L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := (C.center y).mp hy
    have h3 : t * C.ι (0, c) * t⁻¹ = C.ι (0, c) := by rw [← hτ, hfix]
    calc C.ι (0, c) * t = t * C.ι (0, c) * t⁻¹ * t := by rw [h3]
      _ = t * C.ι (0, c) := by group
  rw [← l3facts_one h527 h531 hyp hty hf]
  exact Subgroup.mem_inf.mpr ⟨htT, htC⟩

omit [CharP F 2] [Finite F] in
theorem exists_sigma_ne (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : 2 ≤ f) {G₁ B₁ L' V₁ V₂ : Subgroup G} (C : V1Coords G₁ B₁ L' V₁ V₂ (sec53ZS T L) F)
    {z : G} (hz : z ∈ sec53ZS T L) (hzT : z ∈ centerOf T) (hz1 : z ≠ 1) {t : G} (htT : t ∈ T)
    (htS : t ∉ sec53S T L) {τ : F × F ≃+ F × F} {σ : F →+* F}
    (hτ : ∀ p, C.ι (τ p) = t * C.ι p * t⁻¹) (hσ : ∀ (c : F) (p : F × F), τ (c • p) = σ c • τ p) :
    ∃ c, σ c ≠ c := by
  by_contra hcon
  push Not at hcon
  exact htS (mem_S_of_linear h527 h531 hyp hty hf C hz hzT hz1 htT hτ (fun c p => by
    rw [hσ, hcon]))

theorem mul_mem_S (h527 : Stmt5_2_7) (h531 : Stmt5_3_1) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (hty : IsOfLieType52 M L H B D T .PSL 3 f) (hf : 2 ≤ f) {G₁ B₁ L' V₁ V₂ : Subgroup G}
    (C : V1Coords G₁ B₁ L' V₁ V₂ (sec53ZS T L) F) (hF : Nat.card F = 4) (hLG : L' ≤ G₁)
    (hV₂L : V₂ ≤ L') (hTL : T ≤ Subgroup.normalizer (L' : Set G))
    (hTV : T ≤ Subgroup.normalizer (V₁ : Set G)) {z : G} (hz : z ∈ sec53ZS T L)
    (hzT : z ∈ centerOf T) (hz1 : z ≠ 1) {t x : G} (htT : t ∈ T) (htS : t ∉ sec53S T L)
    (hxT : x ∈ T) (hxS : x ∉ sec53S T L) : t * x ∈ sec53S T L := by
  obtain ⟨τt, σt, hτt, hσt⟩ := C.exists_semilinear hLG hV₂L (hTL htT) (hTV htT)
  obtain ⟨τx, σx, hτx, hσx⟩ := C.exists_semilinear hLG hV₂L (hTL hxT) (hTV hxT)
  have et := ringHom_eq_sq_of_ne hF
    (exists_sigma_ne h527 h531 hyp hty hf C hz hzT hz1 htT htS hτt hσt)
  have ex := ringHom_eq_sq_of_ne hF
    (exists_sigma_ne h527 h531 hyp hty hf C hz hzT hz1 hxT hxS hτx hσx)
  refine mem_S_of_linear h527 h531 hyp hty hf C hz hzT hz1 (T.mul_mem htT hxT)
    (τ := τx.trans τt) (fun p => ?_) (fun c p => ?_)
  · show C.ι (τt (τx p)) = _
    rw [hτt, hτx]
    group
  · show τt (τx (c • p)) = c • τt (τx p)
    have hc4 : (c ^ 2) ^ 2 = c := by
      rw [← pow_mul]
      exact pow_four_of_card_four hF c
    rw [hσx, hσt, ex, et, hc4]

end Linear

variable {G : Type} [Group G] [Finite G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

theorem exc_mul_mem_S (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : f = 2) {z : G} (hz : z ∈ sec53ZS T L) (hzT : z ∈ centerOf T) (hz1 : z ≠ 1) {t x : G}
    (htT : t ∈ T) (htS : t ∉ sec53S T L) (hxT : x ∈ T) (hxS : x ∉ sec53S T L) :
    t * x ∈ sec53S T L := by
  have hf2 : 2 ≤ f := hf.ge
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  obtain ⟨F, _, _, _, hFcard, ⟨C⟩⟩ := exists_v1Coords h527 hyp hty hf2
  have hF : Nat.card F = 4 := by rw [hFcard, hf]; norm_num
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans (sup_sec53 h527 hyp hty hf2).le).trans inf_le_right
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  exact mul_mem_S h527 h531 hyp hty hf2 C hF hLG hV₂L hTL
    (hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)) hz hzT hz1 htT htS
    hxT hxS

theorem le_normalizer_sec53S (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    T ≤ Subgroup.normalizer (sec53S T L : Set G) := by
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have htL : t ∈ Subgroup.normalizer (L : Set G) := h.normal (h.T_le ht)
  constructor
  · rintro ⟨hyT, hyL⟩
    exact ⟨T.mul_mem (T.mul_mem ht hyT) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp htL y).mp hyL⟩
  · rintro ⟨hyT, hyL⟩
    refine ⟨?_, (Subgroup.mem_normalizer_iff.mp htL y).mpr hyL⟩
    have := T.mul_mem (T.mul_mem (T.inv_mem ht) hyT) ht
    simpa [mul_assoc] using this

theorem exc_inf_centralizer_eq (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : f = 2) {z : G} (hz : z ∈ sec53ZS T L) (hzT : z ∈ centerOf T) (hz1 : z ≠ 1)
    (hO : pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G)) ≠ sec53S T L) :
    sec53M12 L H ⊓ Subgroup.centralizer ({z} : Set G) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := hf.ge
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hpar : IsSec53Param .PSL 3 f := ⟨hf2, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, ⟨hCT, hO2, -, -⟩, ⟨hN, -, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨h5a, -⟩ := l3facts_five h527 h531 hyp hty hf2 z hz hz1
  set X := sec53M12 L H ⊓ Subgroup.centralizer ({z} : Set G) with hX
  have hX1 : sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G) = X :=
    le_antisymm (le_inf h5a inf_le_right) (inf_le_inf_right _ inf_le_left)
  rw [hX1] at hO
  have hzS : z ∈ sec53S T L := (inf_le_left : centerOf (sec53S T L) ≤ sec53S T L) hz
  have hTN := le_normalizer_sec53S (L := L) hyp
  have hTX : T ≤ X := by
    intro t ht
    refine Subgroup.mem_inf.mpr ⟨by rw [← hN]; exact hTN ht, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ((inf_le_right : centerOf T ≤
      Subgroup.centralizer (T : Set G)) hzT) t ht)
  have hSP : sec53S T L ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (by rw [← hN]; exact Subgroup.le_normalizer) ?_)
      (inf_le_left.trans hN.symm.le) (h.sylow.1.to_le (inf_le_left : sec53S T L ≤ T))
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp ((inf_le_right : centerOf (sec53S T L) ≤
      Subgroup.centralizer (sec53S T L : Set G)) hz) s hs)
  have hPT : pCoreOf 2 X ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo h.sylow hTX)
  obtain ⟨x, hxP, hxS⟩ : ∃ x ∈ pCoreOf 2 X, x ∉ sec53S T L := by
    by_contra hcon
    push Not at hcon
    exact hO (le_antisymm (fun y hy => hcon y hy) hSP)
  have hxT : x ∈ T := hPT hxP
  have hxX : x ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X hxP
  obtain ⟨F, _, _, _, hFcard, ⟨C⟩⟩ := exists_v1Coords h527 hyp hty hf2
  have hF : Nat.card F = 4 := by rw [hFcard, hf]; norm_num
  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L :=
    (le_sup_right.trans (sup_sec53 h527 hyp hty hf2).le).trans inf_le_right
  have hXL : ∀ g ∈ X, g ∈ Subgroup.normalizer (L : Set G) := fun g hg =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
  have hXV : ∀ g ∈ X, g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun g hg =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hXL g hg)
  obtain ⟨τ, σ, hτ, hσ⟩ := C.exists_semilinear hLG hV₂L (hXL x hxX) (hXV x hxX)
  have hσne := exists_sigma_ne h527 h531 hyp hty hf2 C hz hzT hz1 hxT hxS hτ hσ
  have hZ : (τ (0, 1)).1 = 0 := by
    have h1 : C.ι (τ (0, 1)) ∈ sec53ZS T L := by
      rw [hτ]
      exact conj_mem_centerOf (hTN hxT) ((C.center _).mpr ⟨1, rfl⟩)
    obtain ⟨c, hc⟩ := (C.center _).mp h1
    rw [C.inj hc]
  obtain ⟨c₀, hc₀z⟩ := (C.center z).mp hz
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hz1
    rw [hc₀z]
    have := C.add 0 0
    rw [add_zero] at this
    have h0 : C.ι ((0 : F), (0 : F)) = C.ι 0 := rfl
    rw [h0]
    exact mul_eq_left.mp this.symm
  have hPX : ∀ g ∈ X, ∀ y ∈ pCoreOf 2 X, g * y * g⁻¹ ∈ pCoreOf 2 X := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hg) y).mp hy
  have hP2 := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hX2 : IsPGroup 2 X := by
    rintro ⟨g, hg⟩
    obtain ⟨τg, σg, hτg, hσg⟩ := C.exists_semilinear hLG hV₂L (hXL g hg) (hXV g hg)
    have hgz : g * z = z * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hg).2
    have hτ₂ : ∀ p, C.ι ((τg.trans τg) p) = (g * g) * C.ι p * (g * g)⁻¹ := fun p => by
      show C.ι (τg (τg p)) = _
      rw [hτg, hτg]
      group
    have hlin₂ : ∀ (c : F) (p : F × F), (τg.trans τg) (c • p) = c • (τg.trans τg) p :=
      fun c p => by
        show τg (τg (c • p)) = c • τg (τg p)
        rw [hσg, hσg, ringHom_apply_apply_of_card_four hF]
    have hfix0 : (τg.trans τg) (0, c₀) = (0, c₀) := C.inj (by
      rw [hτ₂, ← hc₀z]
      have e : g * g * z = z * (g * g) := by
        rw [mul_assoc, hgz, ← mul_assoc, hgz, mul_assoc]
      calc g * g * z * (g * g)⁻¹ = z * (g * g) * (g * g)⁻¹ := by rw [e]
        _ = z := by group)
    have hfix : ∀ c : F, (τg.trans τg) (0, c) = (0, c) := by
      intro c
      have e : ((0 : F), c) = (c * c₀⁻¹) • ((0 : F), c₀) := by
        ext
        · simp
        · show c = c * c₀⁻¹ * c₀
          field_simp
      rw [e, hlin₂, hfix0]
    obtain ⟨μ, β, hμβ⟩ : ∃ μ β : F, (τg.trans τg) (1, 0) = (μ, β) := ⟨_, _, rfl⟩
    have hform : ∀ u v : F, (τg.trans τg) (u, v) = (μ * u, β * u + v) := by
      intro u v
      have e : ((u, v) : F × F) = u • ((1 : F), (0 : F)) + v • ((0 : F), (1 : F)) := by
        ext <;> simp
      rw [e, map_add, hlin₂, hlin₂, hfix, hμβ]
      ext <;> simp <;> ring
    have hμ0 : μ ≠ 0 := by
      intro h0
      have e1 : (τg.trans τg) (1, 0) = (τg.trans τg) (0, β) := by
        rw [hform, hform, h0]
        ext <;> simp
      have := congrArg Prod.fst ((τg.trans τg).injective e1)
      exact one_ne_zero this
    have hh : ∀ u v, (g * g) * C.ι (u, v) * (g * g)⁻¹ = C.ι (μ * u, β * u + v) :=
      fun u v => by rw [← hτ₂, hform]
    have hgX2 : g * g ∈ X := X.mul_mem hg hg
    have hcomm : x * (g * g) * x⁻¹ * (g * g)⁻¹ ∈ pCoreOf 2 X := by
      have := hPX (g * g) hgX2 x⁻¹ (Subgroup.inv_mem _ hxP)
      have := (pCoreOf 2 X).mul_mem hxP this
      simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := hP2 ⟨_, hcomm⟩
    have hk' : (x * (g * g) * x⁻¹ * (g * g)⁻¹) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hμσ := C.sigma_fix_of_lower (hXV x hxX) (hXV _ hgX2) hτ hσ hZ hμ0 hh hk'
    have hμ1 : μ = 1 := by
      rcases eq_zero_or_one_of_fix hF hσne hμσ with h0 | h1
      · exact absurd h0 hμ0
      · exact h1
    have hg4 : g * g * (g * g) ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨⟨u, v⟩, rfl⟩ := C.surj y hy
      have h3 : (g * g) * ((g * g) * C.ι (u, v) * (g * g)⁻¹) * (g * g)⁻¹ = C.ι (u, v) := by
        rw [hh, hh, hμ1]
        congr 1
        have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
        ext
        · show 1 * (1 * u) = u
          ring
        · show β * (1 * u) + (β * u + v) = v
          linear_combination h2 * (β * u)
      have h4 : (g * g * (g * g)) * C.ι (u, v) * (g * g * (g * g))⁻¹ = C.ι (u, v) := by
        calc (g * g * (g * g)) * C.ι (u, v) * (g * g * (g * g))⁻¹ =
            (g * g) * ((g * g) * C.ι (u, v) * (g * g)⁻¹) * (g * g)⁻¹ := by group
          _ = C.ι (u, v) := h3
      calc C.ι (u, v) * (g * g * (g * g)) =
          (g * g * (g * g)) * C.ι (u, v) * (g * g * (g * g))⁻¹ * (g * g * (g * g)) := by
            rw [h4]
        _ = (g * g * (g * g)) * C.ι (u, v) := by group
    have hgM : g ∈ sec53M1 L := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hg).1).1
    have hg4M : g * g * (g * g) ∈ sec53M1 L :=
      (sec53M1 L).mul_mem ((sec53M1 L).mul_mem hgM hgM) ((sec53M1 L).mul_mem hgM hgM)
    have hg4V : g * g * (g * g) ∈ pCoreOf 2 L := by
      rw [← hO2]
      refine hCT (Subgroup.mem_inf.mpr ⟨hg4M, ?_⟩)
      rw [hO2]
      exact hg4
    obtain ⟨k', hk'⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hg4V⟩
    refine ⟨k' + 2, Subtype.ext ?_⟩
    have h4 : (g * g * (g * g)) ^ 2 ^ k' = 1 := by
      have := congrArg Subtype.val hk'
      simpa using this
    have e4 : g ^ 4 = g * g * (g * g) := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq, sq]
    have hexp : 2 ^ (k' + 2) = 4 * 2 ^ k' := by rw [pow_add]; ring
    show g ^ 2 ^ (k' + 2) = 1
    rw [hexp, pow_mul, e4, h4]
  have hXP : X ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hX2
  exact le_antisymm (hXP.trans hPT) hTX

theorem exc_centralizer_eq (h527 : Stmt5_2_7) (h531 : Stmt5_3_1)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : f = 2) {z : G} (hz : z ∈ sec53ZS T L) (hzT : z ∈ centerOf T) (hz1 : z ≠ 1)
    (hO : pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G)) ≠ sec53S T L) :
    sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G) = T ∧
      sec53M2 H ⊓ Subgroup.centralizer ({z} : Set G) = T := by
  have hX := exc_inf_centralizer_eq h527 h531 hyp hty hf hz hzT hz1 hO
  obtain ⟨h5a, h5b⟩ := l3facts_five h527 h531 hyp hty hf.ge z hz hz1
  rw [← hX]
  exact ⟨le_antisymm (le_inf h5a inf_le_right) (inf_le_inf_right _ inf_le_left),
    le_antisymm (le_inf h5b inf_le_right) (inf_le_inf_right _ inf_le_right)⟩

end CFSG.Quasithin.H13.Sec53L3
