module

public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreCent

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.TwistedE6Pilot

private theorem mem_sup_of_commute' {G : Type*} [Group G] {C M : Subgroup G}
    (hcomm : ∀ c ∈ C, ∀ y ∈ M, c * y = y * c) {g : G} (hg : g ∈ C ⊔ M) :
    ∃ c ∈ C, ∃ y ∈ M, g = c * y := by
  let S : Subgroup G :=
    { carrier := {g | ∃ c ∈ C, ∃ y ∈ M, g = c * y}
      mul_mem' := by
        rintro _ _ ⟨c₁, hc₁, y₁, hy₁, rfl⟩ ⟨c₂, hc₂, y₂, hy₂, rfl⟩
        refine ⟨c₁ * c₂, C.mul_mem hc₁ hc₂, y₁ * y₂, M.mul_mem hy₁ hy₂, ?_⟩
        have h := hcomm c₂ hc₂ y₁ hy₁
        calc c₁ * y₁ * (c₂ * y₂) = c₁ * (y₁ * c₂) * y₂ := by group
          _ = c₁ * (c₂ * y₁) * y₂ := by rw [h]
          _ = c₁ * c₂ * (y₁ * y₂) := by group
      one_mem' := ⟨1, C.one_mem, 1, M.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨c, hc, y, hy, rfl⟩
        refine ⟨c⁻¹, C.inv_mem hc, y⁻¹, M.inv_mem hy, ?_⟩
        have h := hcomm c hc y hy
        have h' : c⁻¹ * y⁻¹ = y⁻¹ * c⁻¹ := by
          calc c⁻¹ * y⁻¹ = (y * c)⁻¹ := by group
            _ = (c * y)⁻¹ := by rw [h]
            _ = y⁻¹ * c⁻¹ := by group
        rw [mul_inv_rev, h'] }
  have hCS : C ≤ S := fun c hc => ⟨c, hc, 1, M.one_mem, by simp⟩
  have hMS : M ≤ S := fun y hy => ⟨1, C.one_mem, y, hy, by simp⟩
  exact sup_le hCS hMS hg

private theorem cyclic_cube_mem_zpowers {G : Type*} [Group G] {C : Subgroup G} [IsCyclic C]
    [Finite C] {x : G} (hxC : x ∈ C) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {c : G} (hc : c ∈ C)
    (hc3 : c ^ 3 = 1) : c ∈ zpowers x := by
  classical
  haveI : Fintype C := Fintype.ofFinite C
  let x' : C := ⟨x, hxC⟩
  let c' : C := ⟨c, hc⟩
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  let T : Finset C := Finset.univ.filter (fun a : C => a ^ 3 = 1)
  have hT : T.card ≤ 3 := IsCyclic.card_pow_eq_one_le (α := C) (by norm_num)
  have hx'2 : x' ^ 2 ≠ 1 := by
    intro h
    apply hx'1
    calc x' = x' * x' ^ 2 := by rw [h, mul_one]
      _ = x' ^ 3 := by group
      _ = 1 := hx'3
  have hxx2 : x' ≠ x' ^ 2 := by
    intro h
    apply hx'1
    have h' : x' * x' = x' * 1 := by rw [mul_one, ← pow_two]; exact h.symm
    exact mul_left_cancel h'
  have hsub : ({1, x', x' ^ 2} : Finset C) ⊆ T := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · simp
    · exact hx'3
    · calc (x' ^ 2) ^ 3 = (x' ^ 3) ^ 2 := by group
        _ = 1 := by rw [hx'3, one_pow]
  have hcard3 : ({1, x', x' ^ 2} : Finset C).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, x', x' ^ 2, hx'1.symm, hx'2.symm, hxx2, rfl⟩
  have heq : ({1, x', x' ^ 2} : Finset C) = T :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hc'T : c' ∈ T := by simp [T, hc'3]
  rw [← heq] at hc'T
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc'T
  rcases hc'T with h | h | h
  · have : c = 1 := congrArg Subtype.val h
    rw [this]
    exact one_mem _
  · have : c = x := congrArg Subtype.val h
    rw [this]
    exact Subgroup.mem_zpowers x
  · have : c = x ^ 2 := congrArg Subtype.val h
    rw [this]
    exact pow_mem (Subgroup.mem_zpowers x) 2

theorem exists_cube_decomp_of_cyclic {G : Type*} [Group G] {C M : Subgroup G} [IsCyclic C]
    {m' : ℕ} (hC : Nat.card C = 3 * m') (hm' : ¬ 3 ∣ m') {x : G} (hxC : x ∈ C) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) (hcomm : ∀ c ∈ C, ∀ y ∈ M, c * y = y * c) {g : G} (hg : g ∈ C ⊔ M)
    (hg3 : g ^ 3 = 1) :
    ∃ j ∈ zpowers x, ∃ d ∈ M, g = j * d ∧ d ^ 3 = 1 := by
  classical
  have hm'0 : m' ≠ 0 := fun h => hm' (h ▸ dvd_zero 3)
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; positivity)
  obtain ⟨c, hc, y, hy, rfl⟩ := mem_sup_of_commute' hcomm hg
  have hcy : Commute c y := hcomm c hc y hy
  have hs : m' ^ 2 % 3 = 1 := by
    have h3 : m' % 3 = 1 ∨ m' % 3 = 2 := by omega
    rcases h3 with h | h <;> simp [pow_two, Nat.mul_mod, h]
  obtain ⟨u, hu⟩ : ∃ u, m' ^ 2 = 3 * u + 1 := ⟨m' ^ 2 / 3, by omega⟩
  have hgs : (c * y) ^ (m' ^ 2) = c * y := by
    rw [hu, pow_succ, pow_mul, hg3, one_pow, one_mul]
  have hmul : (c * y) ^ (m' ^ 2) = c ^ (m' ^ 2) * y ^ (m' ^ 2) := hcy.mul_pow _
  have hcN : c ^ (3 * m') = 1 := by
    have h := pow_card_eq_one' (G := C) (x := (⟨c, hc⟩ : C))
    rw [hC] at h
    simpa using congrArg Subtype.val h
  have hz3 : (c ^ m') ^ 3 = 1 := by rw [← pow_mul, mul_comm, hcN]
  have hzC : c ^ m' ∈ C := pow_mem hc m'
  have hzx : c ^ m' ∈ zpowers x := cyclic_cube_mem_zpowers hxC hx3 hx1 hzC hz3
  have hj : c ^ (m' ^ 2) ∈ zpowers x := by
    rw [pow_two, pow_mul]
    exact pow_mem hzx m'
  have hj3 : (c ^ (m' ^ 2)) ^ 3 = 1 := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hj
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  refine ⟨c ^ (m' ^ 2), hj, y ^ (m' ^ 2), pow_mem hy _, by rw [← hmul, hgs], ?_⟩
  have hg3' : (c * y) ^ 3 = 1 := hg3
  have h1 : (c ^ (m' ^ 2) * y ^ (m' ^ 2)) ^ 3 = 1 := by rw [← hmul, ← pow_mul, mul_comm, pow_mul, hg3, one_pow]
  have hcomm' : Commute (c ^ (m' ^ 2)) (y ^ (m' ^ 2)) := (hcy.pow_left _).pow_right _
  rw [hcomm'.mul_pow, hj3, one_mul] at h1
  exact h1

section Model


theorem exists_cube_decomp_of_commute_rho {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) (h3dvd : 3 ∣ 2 ^ f + 1) (h9 : ¬ 9 ∣ 2 ^ f + 1)
    {A : SL2 k} (hA : orderOf A = Nat.card k + 1) {m : ℕ} (hm : orderOf (A ^ m) = 3)
    {g : ModGL TwistTag.E6.tag K} (hgC : g ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (hgx : g * (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) =
      (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m) * g)
    (hg3 : g ^ 3 = 1) :
    ∃ j ∈ zpowers ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) (A ^ m)),
      ∃ d ∈ su6Levi σ, g = j * d ∧ d ^ 3 = 1 := by
  classical
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  haveI : Finite K := finite_of_card hK
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρ
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  have hcent := CFSG.StandardType.TwE6CorootCore.centralizer_pow_inf_eq hf hk hK hσ hA hm.ge
  have hgmem : g ∈ zpowers (ρ A) ⊔ su6Levi σ := by
    rw [← hcent]
    refine ⟨Subgroup.mem_centralizer_iff.2 ?_, hgC⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hgx.symm
  have hAm3 : (A ^ m) ^ 3 = 1 := by
    rw [← hm]
    exact pow_orderOf_eq_one _
  have hx3 : ρ (A ^ m) ^ 3 = 1 := by rw [← map_pow, hAm3, map_one]
  have hx1 : ρ (A ^ m) ≠ 1 := by
    intro h1
    have : A ^ m = 1 := hρinj (by rw [map_one]; exact h1)
    rw [this, orderOf_one] at hm
    omega
  have hxC : ρ (A ^ m) ∈ zpowers (ρ A) := by
    rw [map_pow]
    exact pow_mem (mem_zpowers _) m
  have hC : Nat.card (zpowers (ρ A)) = 3 * ((2 ^ f + 1) / 3) := by
    rw [Nat.card_zpowers, orderOf_injective _ hρinj, hA, hk, Nat.mul_div_cancel' h3dvd]
  have hm' : ¬ 3 ∣ (2 ^ f + 1) / 3 := by
    intro h
    apply h9
    obtain ⟨t, ht⟩ := h3dvd
    rw [ht, Nat.mul_div_cancel_left _ (by norm_num)] at h
    obtain ⟨u, hu⟩ := h
    exact ⟨u, by omega⟩
  have hcomm : ∀ c ∈ zpowers (ρ A), ∀ y ∈ su6Levi σ, c * y = y * c := by
    intro c hc y hy
    obtain ⟨hLc, -⟩ := su6Levi_facts (k := k) hf hk hK hσ
    have hcJ : c ∈ thetaRankOneGroup (algebraMap k K) := by
      rw [thetaRankOneGroup_eq_range hK2 (algebraMap k K)]
      exact (Subgroup.zpowers_le.2 ⟨A, rfl⟩ : zpowers (ρ A) ≤ ρ.range) hc
    exact Subgroup.mem_centralizer_iff.mp (hLc hy) c hcJ
  exact exists_cube_decomp_of_cyclic hC hm' hxC hx3 hx1 hcomm hgmem hg3

end Model

end CFSG.StandardType.LieKnownR2.ExcPos
