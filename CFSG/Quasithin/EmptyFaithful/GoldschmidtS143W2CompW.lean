module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

set_option maxRecDepth 100000 in
theorem sl3_three_factors : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
    ∃ a b c : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ g = a * b * c := by
  decide +kernel

section Top

variable {K : Type*} [Group K] [Finite K]

theorem eq_top_of_odd_and_central (hK : IsZ4StarSL23 K) {u : K} (hu4 : orderOf u = 4)
    (hucen : ∀ g : K, g * u = u * g) {M : Subgroup K}
    (hodd : ∀ k : K, Odd (orderOf k) → k ∈ M) (hu : u ∈ M) : M = ⊤ := by
  obtain ⟨hcard, A, B, hAB, hA4, hAc, ⟨e⟩⟩ := hK
  have hB : B ≤ M := by
    intro b hb
    obtain ⟨a, b', c, ha, hb', hc, habc⟩ := sl3_three_factors (e ⟨b, hb⟩)
    have hodd3 : ∀ s : ↥B, s ^ 3 = 1 → Odd (orderOf (s : K)) := by
      intro s hs
      have : orderOf (s : K) ∣ 3 := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_dvd_of_pow_eq_one hs
      exact Odd.of_dvd_nat (by decide) this
    have hmem : ∀ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), s ^ 3 = 1 →
        ((e.symm s : ↥B) : K) ∈ M := by
      intro s hs
      apply hodd
      apply hodd3
      rw [← map_pow, hs, map_one]
    have hb_eq : (⟨b, hb⟩ : ↥B) = e.symm a * e.symm b' * e.symm c := by
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact habc
    have : b = ((e.symm a : ↥B) : K) * ((e.symm b' : ↥B) : K) * ((e.symm c : ↥B) : K) :=
      congrArg Subtype.val hb_eq
    rw [this]
    exact M.mul_mem (M.mul_mem (hmem a ha) (hmem b' hb')) (hmem c hc)
  have huB : u ∉ B := by
    intro huB
    have hcen : ∀ N : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
        e ⟨u, huB⟩ * N = N * e ⟨u, huB⟩ := by
      intro N
      apply e.symm.injective
      simp only [map_mul, MulEquiv.symm_apply_apply]
      exact Subtype.ext (hucen (e.symm N : ↥B)).symm
    have h2 := sl3_central_sq _ hcen
    have h2' : (⟨u, huB⟩ : ↥B) * ⟨u, huB⟩ = 1 := by
      apply e.injective
      rw [map_mul, h2, map_one]
    have h3 : u * u = 1 := congrArg Subtype.val h2'
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h3)
    rw [hu4] at this
    omega
  have hBcard : Nat.card B = 24 := by
    rw [Nat.card_congr e.toEquiv]; exact SL23.card_sl3
  have hdvd1 : Nat.card B ∣ Nat.card M := Subgroup.card_dvd_of_le hB
  have hdvd2 : Nat.card M ∣ Nat.card K := Subgroup.card_subgroup_dvd_card M
  rw [hBcard] at hdvd1
  rw [hcard] at hdvd2
  have hMcard : Nat.card M = 48 := by
    obtain ⟨m, hm⟩ := hdvd1
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hm' : m = 1 ∨ m = 2 := by
      have : Nat.card M ≤ 48 := Nat.le_of_dvd (by norm_num) hdvd2
      omega
    rcases hm' with rfl | rfl
    · exfalso
      have : B = M := Subgroup.eq_of_le_of_card_ge hB (by rw [hBcard]; omega)
      exact huB (this ▸ hu)
    · omega
  exact Subgroup.eq_top_of_card_eq M (by rw [hMcard, hcard])

end Top

section K0

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem Ctx.u0_central_K0 (h : Ctx T M g A t d x) {k : G} (hk : k ∈ K0 T d x) :
    k * u0Of d x = u0Of d x * k := by
  have hkd : k * d = d * k := Subgroup.mem_centralizer_singleton_iff.mp
    (oTwoUpper_le_centralizer_d h.c h.hD h.hd4 hk.1)
  have hkw : k * wOfX d x = wOfX d x * k := mem_Gw_iff.mp hk.2
  have hu : u0Of d x = d⁻¹ * wOfX d x := by rw [wOfX_eq_mul_u0Of]; group
  have hkd' : k * d⁻¹ = d⁻¹ * k := by
    calc k * d⁻¹ = d⁻¹ * (d * k) * d⁻¹ := by group
      _ = d⁻¹ * (k * d) * d⁻¹ := by rw [hkd]
      _ = d⁻¹ * k := by group
  rw [hu]
  calc k * (d⁻¹ * wOfX d x) = (k * d⁻¹) * wOfX d x := by group
    _ = (d⁻¹ * k) * wOfX d x := by rw [hkd']
    _ = d⁻¹ * (k * wOfX d x) := by group
    _ = d⁻¹ * (wOfX d x * k) := by rw [hkw]
    _ = (d⁻¹ * wOfX d x) * k := by group

theorem K0_le_of_odd_and_u0 (h : Ctx T M g A t d x) {N : Subgroup G}
    (hodd : ∀ k ∈ K0 T d x, Odd (orderOf k) → k ∈ N) (hu : u0Of d x ∈ N) : K0 T d x ≤ N := by
  have hK : IsZ4StarSL23 ↥(K0 T d x) := h.hO
  have hu4 : orderOf (⟨u0Of d x, h.u0_mem_K0⟩ : ↥(K0 T d x)) = 4 := by
    rw [← Subgroup.orderOf_coe]; exact h.orderOf_u0
  have hcen : ∀ k : ↥(K0 T d x), k * (⟨u0Of d x, h.u0_mem_K0⟩ : ↥(K0 T d x)) =
      ⟨u0Of d x, h.u0_mem_K0⟩ * k := fun k => Subtype.ext (h.u0_central_K0 k.2)
  have htop := eq_top_of_odd_and_central hK hu4 hcen
    (M := N.subgroupOf (K0 T d x))
    (fun k hk => Subgroup.mem_subgroupOf.mpr (hodd k k.2 (by rwa [Subgroup.orderOf_coe])))
    (Subgroup.mem_subgroupOf.mpr hu)
  intro k hk
  have : (⟨k, hk⟩ : ↥(K0 T d x)) ∈ N.subgroupOf (K0 T d x) := by rw [htop]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end K0

end InspW2

end S143

end CFSG.Quasithin
