module

public import CFSG.Quasithin.EmptyFaithful.S143NK

public section

namespace CFSG.Quasithin

namespace S153E

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152O4 CFSG.Quasithin.T1531O4

section Omega

variable {V : Type} [CommGroup V] [Finite V]

theorem not_even_rk_comm_of_card_two (hexp : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    (g : MulAut V) (h : Nat.card ↥(fixV (Subgroup.zpowers g)) = 2) :
    ¬ Even (rk (commV (Subgroup.zpowers g))) := by
  have hsum := rk_commV_add_rk_fixV g
  rw [rk_V_eq_four hcard] at hsum
  rw [Nat.even_iff]
  have := S152O.rk_eq_of_card_eq hexp (n := 1) (by simpa using h)
  omega

theorem transCount_mul : ∀ γ : Gam, Fintype.card {v : Vec // transV (act γ v) = v} = 2 ∨
    Fintype.card {v : Vec // transV (act γ v) = v} = 8 := by decide +kernel

theorem exists_omegaFourPlus_model (hcard : Nat.card V = 16) {q : V → ZMod 2}
    (hq1 : IsQuadraticFormOn q) (hq2 : IsNondegQuadratic q) (hq3 : IsPlusType q) :
    ∃ c : V ≃* Vec, Nat.card (rhoV c).range = 36 ∧ ∀ g : MulAut V,
      g ∈ (rhoV c).range ↔ g ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers g))) := by
  have hexp : ∀ w : V, w * w = 1 := S152O.sq_eq_one_of_nondeg hq1 hq2
  have hexp' : ∀ w : V, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  obtain ⟨U₁, U₂, hinf, hsup, φ₁, φ₂, hqe⟩ :=
    S153.exists_decomposition_of_plusType hexp hcard hq1 hq2 hq3
  let c : V ≃* Vec := (S1417.coordEquiv hinf hsup φ₁ φ₂).trans kappa
  have hqc : ∀ v, q v = detQ (c v) := by
    intro v
    rw [hqe v, quadOf_eq_qFloc hinf hsup φ₁ φ₂ v]
    exact qFloc_eq_detQ _
  have hR_sub : ∀ γ : Gam, rhoV c γ ∈ orthogonalGroupOf q ∧
      Even (rk (commV (Subgroup.zpowers (rhoV c γ)))) := by
    intro γ
    refine ⟨fun v => ?_, ?_⟩
    · rw [hqc, hqc, rhoV_apply, detQ_act]
    · apply even_rk_comm_of_card hexp' hcard
      have := card_fixV_conjBack c (rho γ)
      change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = _ at this
      change Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 1 ∨
        Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 4 ∨
        Nat.card ↥(fixV (Subgroup.zpowers (conjBack c (rho γ)))) = 16
      rw [this]
      exact nat_card_fix γ
  have hR36 : Nat.card (rhoV c).range = 36 := by
    rw [← card_Gam]
    exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective c)).toEquiv).symm
  refine ⟨c, hR36, fun g => ⟨?_, ?_⟩⟩
  · rintro ⟨γ, rfl⟩
    exact hR_sub γ
  · rintro ⟨hgO, hgE⟩
    by_contra hgR
    obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq1 hq2 hq3
    have hO72 : Nat.card (orthogonalGroupOf q) = 72 := hS.card_X
    have hRO : (rhoV c).range ≤ orthogonalGroupOf q := by
      rintro _ ⟨γ, rfl⟩
      exact (hR_sub γ).1
    have hindex : ((rhoV c).range.subgroupOf (orthogonalGroupOf q)).index = 2 := by
      have h1 := Subgroup.card_mul_index ((rhoV c).range.subgroupOf (orthogonalGroupOf q))
      have h2 : Nat.card ((rhoV c).range.subgroupOf (orthogonalGroupOf q)) =
          Nat.card (rhoV c).range :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRO).toEquiv
      rw [h2, hR36, hO72] at h1
      omega
    set g₀ : MulAut V := conjBack c transV with hg₀
    have hg₀O : g₀ ∈ orthogonalGroupOf q := by
      intro v
      rw [hqc, hqc, hg₀, conjBack_apply, detQ_trans]
    have hg₀odd : ¬ Even (rk (commV (Subgroup.zpowers g₀))) := by
      refine not_even_rk_comm_of_card hexp' hcard g₀ ?_
      rw [hg₀, card_fixV_conjBack c transV]
      simp only [Nat.card_eq_fintype_card]
      exact transCount
    have hg₀R : g₀ ∉ (rhoV c).range := by
      rintro ⟨γ, hγ⟩
      exact hg₀odd (hγ ▸ (hR_sub γ).2)
    have key := Subgroup.mul_mem_iff_of_index_two hindex
      (a := (⟨g₀, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹) (b := ⟨g, hgO⟩)
    have hprod : (⟨g₀, hg₀O⟩ : ↥(orthogonalGroupOf q))⁻¹ * ⟨g, hgO⟩ ∈
        (rhoV c).range.subgroupOf (orthogonalGroupOf q) := by
      rw [key]
      constructor
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h)) hg₀R
      · intro h
        exact absurd (Subgroup.mem_subgroupOf.mp h) hgR
    obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.mp hprod
    have hg : g = conjBack c (transV * rho γ) := by
      have h1 : rhoV c γ = g₀⁻¹ * g := by simpa using hγ
      have h2 : g = g₀ * rhoV c γ := by rw [h1]; group
      rw [h2, hg₀, conjBack_mul]
      rfl
    have hcard' := card_fixV_conjBack c (transV * rho γ)
    rw [← hg] at hcard'
    have hct : Fintype.card {v : Vec // transV (act γ v) = v} = 2 ∨
        Fintype.card {v : Vec // transV (act γ v) = v} = 8 := transCount_mul γ
    rcases hct with h2 | h8
    · refine not_even_rk_comm_of_card_two hexp' hcard g ?_ hgE
      rw [hcard']
      simp only [Nat.card_eq_fintype_card]
      exact h2
    · refine not_even_rk_comm_of_card hexp' hcard g ?_ hgE
      rw [hcard']
      simp only [Nat.card_eq_fintype_card]
      exact h8

theorem exists_omegaFourPlus (hcard : Nat.card V = 16) {q : V → ZMod 2} (hq1 : IsQuadraticFormOn q)
    (hq2 : IsNondegQuadratic q) (hq3 : IsPlusType q) :
    ∃ X : Subgroup (MulAut V), Nat.card X = 36 ∧ ∀ g : MulAut V,
      g ∈ X ↔ g ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers g))) := by
  obtain ⟨c, h36, h⟩ := exists_omegaFourPlus_model hcard hq1 hq2 hq3
  exact ⟨(rhoV c).range, h36, h⟩

end Omega


section DihedralT

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t : MulAut W}
  {T' : Subgroup (MulAut W)} {s₁ s₂ τ : MulAut W} {a₁ a₂ : W}

theorem even_iff_T' (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hT : IsSylowTwoOf T' X) (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {g : MulAut W}
    (hg : g ∈ T') :
    Even (rk (commV (Subgroup.zpowers g))) ↔
      ((g ∈ L₁ ⊔ L₂ → g = 1 ∨ g = s₁ * s₂) ∧ (g ∉ L₁ ⊔ L₂ → g * g = 1)) := by
  rw [even_comm_iff hS]
  obtain ⟨rk1, rk2, rk12, rk0⟩ := rk_fix_S hS hexp hF.sylow
  by_cases hgN : g ∈ L₁ ⊔ L₂
  · rcases (hF.S_eq g).1 ⟨hg, hgN⟩ with h | h | h | h
    · rw [h]
      exact iff_of_true (by rw [rk0]; decide) ⟨fun _ => Or.inl rfl, fun h' => absurd (h ▸ hgN) h'⟩
    · rw [h]
      refine iff_of_false (by rw [rk1]; decide) fun h' => ?_
      rcases h'.1 (h ▸ hgN) with h1 | h1
      · exact hF.sylow.s₁_ne h1
      · exact hF.sylow.s₂_ne (mul_left_cancel (a := s₁) (h1.symm.trans (mul_one s₁).symm))
    · rw [h]
      refine iff_of_false (by rw [rk2]; decide) fun h' => ?_
      rcases h'.1 (h ▸ hgN) with h1 | h1
      · exact hF.sylow.s₂_ne h1
      · exact hF.sylow.s₁_ne (mul_right_cancel (b := s₂) (h1.symm.trans (one_mul s₂).symm))
    · rw [h]
      exact iff_of_true (by rw [rk12]; decide) ⟨fun _ => Or.inr rfl, fun h' => absurd (h ▸ hgN) h'⟩
  · rcases sq_of_swap hS hT hF hg hgN with h | h
    · rw [rk_fixV_swap_one hS hexp (hT.1 hg) hgN h]
      exact iff_of_true (by decide) ⟨fun h' => absurd h' hgN, fun _ => h⟩
    · rw [rk_fixV_swap_s hS hexp hF.sylow (hT.1 hg) hgN h]
      exact iff_of_false (by decide) fun h' => hF.mul_ne (h ▸ h'.2 hgN)

theorem mul_mem_of_normal_ne_bot (hS : OfourStruct X L₁ L₂ t) (hT : IsSylowTwoOf T' X)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {N : Subgroup (MulAut W)} (hNT : N ≤ T')
    (hNn : ∀ h ∈ T', ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hN1 : ∃ n ∈ N, n ≠ 1) : s₁ * s₂ ∈ N := by
  obtain ⟨n, hnN, hn1⟩ := hN1
  have hnT := hNT hnN
  by_cases hnS : n ∈ L₁ ⊔ L₂
  · rcases (hF.S_eq n).1 ⟨hnT, hnS⟩ with h | h | h | h
    · exact absurd h hn1
    · rw [h] at hnN
      have : s₂ ∈ N := hF.τs₁ ▸ hNn τ hF.τ_T s₁ hnN
      exact N.mul_mem hnN this
    · rw [h] at hnN
      have : s₁ ∈ N := hF.τs₂ ▸ hNn τ hF.τ_T s₂ hnN
      exact N.mul_mem this hnN
    · exact h ▸ hnN
  · obtain ⟨c1, -⟩ := conj_swap hS hT hF hnT hnS
    have h1 : s₁ * n⁻¹ * s₁⁻¹ ∈ N := hNn s₁ hF.sylow.s₁_mem_S.1 n⁻¹ (N.inv_mem hnN)
    have h2 : n * (s₁ * n⁻¹ * s₁⁻¹) ∈ N := N.mul_mem hnN h1
    have hs₁inv : s₁⁻¹ = s₁ := inv_eq_of_mul_eq_one_right hF.s₁_sq
    have e : n * (s₁ * n⁻¹ * s₁⁻¹) = s₁ * s₂ := by
      calc n * (s₁ * n⁻¹ * s₁⁻¹) = (n * s₁ * n⁻¹) * s₁⁻¹ := by group
        _ = s₂ * s₁ := by rw [c1, hs₁inv]
        _ = s₁ * s₂ := hF.comm.symm
    rw [← e]
    exact h2

theorem eq_even_of_normal_elemAbelian (hS : OfourStruct X L₁ L₂ t) (hexp : ∀ w : W, w ^ 2 = 1)
    (hT : IsSylowTwoOf T' X) (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂)
    {N : Subgroup (MulAut W)} (hNT : N ≤ T') (hNn : ∀ h ∈ T', ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN2 : ∀ n ∈ N, n * n = 1)
    (hNS : ¬ N ≤ L₁ ⊔ L₂) :
    (∀ g, g ∈ N ↔ g ∈ T' ∧ Even (rk (commV (Subgroup.zpowers g)))) ∧ Nat.card N = 4 := by
  obtain ⟨x, hxN, hxS⟩ := IsConcreteLE.not_le_iff_exists.mp hNS
  have hxT : x ∈ T' := hNT hxN
  have hxS' : x ∉ T' ⊓ (L₁ ⊔ L₂) := fun h => hxS h.2
  have hx1 : x ≠ 1 := fun h => hxS (h ▸ (L₁ ⊔ L₂).one_mem)
  have hrN : s₁ * s₂ ∈ N := mul_mem_of_normal_ne_bot hS hT hF hNT hNn ⟨x, hxN, hx1⟩
  obtain ⟨c1, c2⟩ := conj_swap hS hT hF hxT hxS
  have hxx : x * x = 1 := hN2 x hxN
  have hNS' : ∀ n ∈ N, n ∈ L₁ ⊔ L₂ → n = 1 ∨ n = s₁ * s₂ := by
    intro n hn hnS
    rcases (hF.S_eq n).1 ⟨hNT hn, hnS⟩ with h | h | h | h
    · exact Or.inl h
    · exfalso
      have hc := hNab x hxN n hn
      rw [h] at hc
      apply hF.ne
      calc s₁ = x * s₁ * x⁻¹ := by rw [hc]; group
        _ = s₂ := c1
    · exfalso
      have hc := hNab x hxN n hn
      rw [h] at hc
      apply hF.ne
      calc s₁ = x * s₂ * x⁻¹ := c2.symm
        _ = s₂ := by rw [hc]; group
    · exact Or.inr h
  have hNout : ∀ n ∈ N, n ∉ L₁ ⊔ L₂ → n = x ∨ n = s₁ * s₂ * x := by
    intro n hn hnS
    have hnT := hNT hn
    rcases coset_of_relIndex_two (hS.relIndex_S hT) hnT hxT hxS' with h | h
    · exact absurd h.2 hnS
    · have hy : n * x⁻¹ ∈ N := N.mul_mem hn (N.inv_mem hxN)
      rcases hNS' _ hy h.2 with h1 | h1
      · left
        calc n = (n * x⁻¹) * x := by group
          _ = x := by rw [h1, one_mul]
      · right
        calc n = (n * x⁻¹) * x := by group
          _ = s₁ * s₂ * x := by rw [h1]
  refine ⟨fun g => ⟨fun hg => ⟨hNT hg, ?_⟩, fun ⟨hgT, hge⟩ => ?_⟩, ?_⟩
  · exact (even_iff_T' hS hexp hT hF (hNT hg)).mpr ⟨fun hgS => hNS' g hg hgS, fun _ => hN2 g hg⟩
  · obtain ⟨h1, h2⟩ := (even_iff_T' hS hexp hT hF hgT).mp hge
    by_cases hgS : g ∈ L₁ ⊔ L₂
    · rcases h1 hgS with h | h
      · exact h ▸ N.one_mem
      · exact h ▸ hrN
    · have hgg := h2 hgS
      rcases coset_of_relIndex_two (hS.relIndex_S hT) hgT hxT hxS' with h | h
      · exact absurd h.2 hgS
      · have hgy : g = (g * x⁻¹) * x := by group
        rcases (hF.S_eq _).1 h with h' | h' | h' | h'
        · rw [hgy, h', one_mul]; exact hxN
        · exfalso
          rw [hgy, h'] at hgg
          have : s₁ * x * (s₁ * x) = s₁ * (x * s₁ * x⁻¹) * (x * x) := by group
          rw [this, c1, hxx, mul_one] at hgg
          exact hF.mul_ne hgg
        · exfalso
          rw [hgy, h'] at hgg
          have : s₂ * x * (s₂ * x) = s₂ * (x * s₂ * x⁻¹) * (x * x) := by group
          rw [this, c2, hxx, mul_one] at hgg
          exact hF.mul_ne (hF.comm.trans hgg)
        · rw [hgy, h']; exact N.mul_mem hrN hxN
  · have hset : (N : Set (MulAut W)) = {1, s₁ * s₂, x, s₁ * s₂ * x} := by
      ext n
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hn
        by_cases hnS : n ∈ L₁ ⊔ L₂
        · rcases hNS' n hn hnS with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases hNout n hn hnS with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
      · rintro (h | h | h | h)
        · exact h ▸ N.one_mem
        · exact h ▸ hrN
        · exact h ▸ hxN
        · exact h ▸ N.mul_mem hrN hxN
    have hr1 : s₁ * s₂ ≠ 1 := hF.mul_ne
    have hrS : s₁ * s₂ ∈ L₁ ⊔ L₂ :=
      (L₁ ⊔ L₂).mul_mem hF.sylow.s₁_mem_S.2 hF.sylow.s₂_mem_S.2
    have hxr : x ≠ s₁ * s₂ := fun h => hxS (h ▸ hrS)
    have hrxS : s₁ * s₂ * x ∉ L₁ ⊔ L₂ := fun h => hxS (by
      have e : (s₁ * s₂)⁻¹ * (s₁ * s₂ * x) = x := by group
      rw [← e]
      exact (L₁ ⊔ L₂).mul_mem ((L₁ ⊔ L₂).inv_mem hrS) h)
    have hcard : Nat.card ↥N = (N : Set (MulAut W)).ncard := Nat.card_coe_set_eq _
    have n1 : (1 : MulAut W) ∉ ({s₁ * s₂, x, s₁ * s₂ * x} : Set (MulAut W)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hr1.symm, hx1.symm, fun h => hrxS (h ▸ (L₁ ⊔ L₂).one_mem)⟩
    have n2 : s₁ * s₂ ∉ ({x, s₁ * s₂ * x} : Set (MulAut W)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨hxr.symm, fun h => hx1 ?_⟩
      exact (mul_left_cancel (a := s₁ * s₂) ((mul_one (s₁ * s₂)).trans h)).symm
    have n3 : x ∉ ({s₁ * s₂ * x} : Set (MulAut W)) := by
      simp only [Set.mem_singleton_iff]
      intro h
      apply hr1
      exact mul_right_cancel (b := x) (by rw [one_mul]; exact h.symm)
    rw [hcard, hset, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_singleton]


theorem eq_one_or_mul_of_central (hS : OfourStruct X L₁ L₂ t) (hT : IsSylowTwoOf T' X)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {z : MulAut W} (hz : z ∈ T')
    (hc : ∀ x ∈ T', x * z = z * x) : z = 1 ∨ z = s₁ * s₂ := by
  by_cases hzS : z ∈ L₁ ⊔ L₂
  · rcases (hF.S_eq z).1 ⟨hz, hzS⟩ with h | h | h | h
    · exact Or.inl h
    · exfalso
      have := hc τ hF.τ_T
      rw [h] at this
      have h2 : τ * s₁ * τ⁻¹ = s₁ := by rw [this]; group
      rw [hF.τs₁] at h2
      exact hF.ne h2.symm
    · exfalso
      have := hc τ hF.τ_T
      rw [h] at this
      have h2 : τ * s₂ * τ⁻¹ = s₂ := by rw [this]; group
      rw [hF.τs₂] at h2
      exact hF.ne h2
    · exact Or.inr h
  · exfalso
    obtain ⟨c1, -⟩ := conj_swap hS hT hF hz hzS
    have := hc s₁ hF.sylow.s₁_mem_S.1
    have h2 : z * s₁ * z⁻¹ = s₁ := by
      calc z * s₁ * z⁻¹ = (z * s₁) * z⁻¹ := rfl
        _ = (s₁ * z) * z⁻¹ := by rw [← this]
        _ = s₁ := by group
    rw [c1] at h2
    exact hF.ne h2.symm

theorem mul_inv_of_odd (hS : OfourStruct X L₁ L₂ t) (hT : IsSylowTwoOf T' X)
    (hF : OfourStruct.SylowFacts L₁ L₂ T' s₁ s₂ τ a₁ a₂) {y : MulAut W} (hy : y ∈ X)
    (hodd : Odd (orderOf y)) : (s₁ * s₂) * y * (s₁ * s₂)⁻¹ = y⁻¹ := by
  obtain ⟨r, hrT, hr1, -, hrc, -, hrinv⟩ := hS.exists_central hT
  have hr : r = s₁ * s₂ := by
    rcases eq_one_or_mul_of_central hS hT hF hrT hrc with h | h
    · exact absurd h hr1
    · exact h
  rw [← hr]
  exact hrinv y hy hodd

end DihedralT

section Split

variable {V : Type} [CommGroup V] [Finite V]

theorem comm1_surj_left : ∀ v : Vec, ∃ w : Vec, comm1 (DihedralGroup.r 1, 1) w = v := by
  decide +kernel

theorem comm1_surj_right : ∀ v : Vec, ∃ w : Vec, comm1 (1, DihedralGroup.r 1) w = v := by
  decide +kernel

theorem exists_omegaFourPlus_split (hcard : Nat.card V = 16) {q : V → ZMod 2}
    (hq1 : IsQuadraticFormOn q) (hq2 : IsNondegQuadratic q) (hq3 : IsPlusType q) :
    ∃ N₁ N₂ : Subgroup (MulAut V),
      (∀ g : MulAut V, g ∈ N₁ ⊔ N₂ ↔
        g ∈ orthogonalGroupOf q ∧ Even (rk (commV (Subgroup.zpowers g)))) ∧
      Nat.card ↥(N₁ ⊔ N₂) = 36 ∧ N₁ ⊓ N₂ = ⊥ ∧ (∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a) ∧
      Nonempty (↥N₁ ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (↥N₂ ≃* Equiv.Perm (Fin 3)) ∧
      commV N₁ = ⊤ ∧ commV N₂ = ⊤ := by
  obtain ⟨c, h36, hΩ⟩ := exists_omegaFourPlus_model hcard hq1 hq2 hq3
  let ι₁ : DihedralGroup 3 →* MulAut V := (rhoV c).comp (MonoidHom.inl _ _)
  let ι₂ : DihedralGroup 3 →* MulAut V := (rhoV c).comp (MonoidHom.inr _ _)
  have hι₁ : Function.Injective ι₁ := fun a b h => (Prod.mk.inj (rhoV_injective c h)).1
  have hι₂ : Function.Injective ι₂ := fun a b h => (Prod.mk.inj (rhoV_injective c h)).2
  have hprod : ∀ a b : DihedralGroup 3, rhoV c (a, b) = ι₁ a * ι₂ b := by
    intro a b
    show rhoV c (a, b) = rhoV c (a, 1) * rhoV c (1, b)
    rw [← map_mul]
    simp
  have hsup : ι₁.range ⊔ ι₂.range = (rhoV c).range := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨a, rfl⟩
        exact ⟨(a, 1), rfl⟩
      · rintro _ ⟨b, rfl⟩
        exact ⟨(1, b), rfl⟩
    · rintro _ ⟨⟨a, b⟩, rfl⟩
      rw [hprod]
      exact Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨b, rfl⟩
  refine ⟨ι₁.range, ι₂.range, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [hsup]
    exact hΩ g
  · rw [hsup]
    exact h36
  · rw [eq_bot_iff]
    rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    have h1 : rhoV c (a, 1) = rhoV c (1, b) := by
      have e1 : rhoV c (a, 1) = ι₁ a := rfl
      have e2 : rhoV c (1, b) = ι₂ b := rfl
      rw [e1, e2, hb]
    have h2 := rhoV_injective c h1
    have ha : a = 1 := congrArg Prod.fst h2
    rw [ha, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have h2 : ι₂ b * ι₁ a = rhoV c (a, b) := by
      show rhoV c (1, b) * rhoV c (a, 1) = rhoV c (a, b)
      rw [← map_mul]
      simp
    rw [h2, hprod]
  · exact ⟨(MonoidHom.ofInjective hι₁).symm.trans S143.dihThreeEquivPerm⟩
  · exact ⟨(MonoidHom.ofInjective hι₂).symm.trans S143.dihThreeEquivPerm⟩
  · rw [eq_top_iff]
    intro v _
    obtain ⟨w', hw'⟩ := comm1_surj_left (c v)
    apply Subgroup.subset_closure
    refine ⟨ι₁ (DihedralGroup.r 1), ⟨_, rfl⟩, c.symm w', ?_⟩
    apply c.injective
    rw [map_mul, map_inv]
    have e : c (ι₁ (DihedralGroup.r 1) (c.symm w')) = act (DihedralGroup.r 1, 1) w' := by
      show c (rhoV c (DihedralGroup.r 1, 1) (c.symm w')) = _
      rw [rhoV_apply, MulEquiv.apply_symm_apply]
    rw [e, MulEquiv.apply_symm_apply]
    exact hw'
  · rw [eq_top_iff]
    intro v _
    obtain ⟨w', hw'⟩ := comm1_surj_right (c v)
    apply Subgroup.subset_closure
    refine ⟨ι₂ (DihedralGroup.r 1), ⟨_, rfl⟩, c.symm w', ?_⟩
    apply c.injective
    rw [map_mul, map_inv]
    have e : c (ι₂ (DihedralGroup.r 1) (c.symm w')) = act (1, DihedralGroup.r 1) w' := by
      show c (rhoV c (1, DihedralGroup.r 1) (c.symm w')) = _
      rw [rhoV_apply, MulEquiv.apply_symm_apply]
    rw [e, MulEquiv.apply_symm_apply]
    exact hw'

end Split

end S153E

end CFSG.Quasithin
