module

public import CFSG.RankThree.PartTwo.Sec21.StronglyEmbedded

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open

variable {G : Type*} [Group G]

theorem smul_mk_eq_iff {N : Subgroup G} (z g : G) :
    z • (g : G ⧸ N) = (g : G ⧸ N) ↔ g⁻¹ * z * g ∈ N := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq,
    show (z * g)⁻¹ * g = (g⁻¹ * z * g)⁻¹ by group, inv_mem_iff]

theorem mk_eq_mk_one_iff {N : Subgroup G} (g : G) :
    (g : G ⧸ N) = ((1 : G) : G ⧸ N) ↔ g ∈ N := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

theorem orderOf_inv_mul_mul (g z : G) : orderOf (g⁻¹ * z * g) = orderOf z := by
  have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulEquiv.injective _) z
  simpa [MulAut.conj_apply] using h

theorem rank3II_23_5 [Finite G] {N : Subgroup G} (h233 : GLBStronglyEmbedded 3 N) {z : G}
    (hzN : z ∈ N) (hz : orderOf z = 2) (h234_1 : Subgroup.centralizer {z} ≤ N)
    (h234_2 : ∀ x ∈ N, orderOf x = 2 →
      3 ∣ Nat.card (N ⊓ Subgroup.centralizer {x} : Subgroup G)) :
    ∀ q : G ⧸ N, z • q = q ↔ q = ((1 : G) : G ⧸ N) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [smul_mk_eq_iff, mk_eq_mk_one_iff]
    constructor
    · intro hx
      by_contra hgN
      have hle : N ⊓ Subgroup.centralizer {g⁻¹ * z * g} ≤ N ⊓ GLBConj g N := by
        intro y hy
        obtain ⟨hyN, hyc⟩ := Subgroup.mem_inf.mp hy
        refine Subgroup.mem_inf.mpr ⟨hyN, mem_glbConj_iff.mpr (h234_1 ?_)⟩
        rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
        calc g * y * g⁻¹ * z = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * z * g * y) * g⁻¹ := by rw [hyc]
          _ = z * (g * y * g⁻¹) := by group
      exact not_dvd_card_inf_conj h233 hgN
        ((h234_2 _ hx ((orderOf_inv_mul_mul g z).trans hz)).trans (Subgroup.card_dvd_of_le hle))
    · intro hg
      exact N.mul_mem (N.mul_mem (N.inv_mem hg) hzN) hg

theorem odd_index_of_unique_fixed [Finite G] {N : Subgroup G} {z : G} (hz : orderOf z = 2)
    (h : ∀ q : G ⧸ N, z • q = q ↔ q = ((1 : G) : G ⧸ N)) : Odd N.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hfix : MulAction.fixedPoints (Subgroup.zpowers z) (G ⧸ N) = {((1 : G) : G ⧸ N)} := by
    ext q
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff, ← h q]
    constructor
    · intro hq
      exact hq ⟨z, Subgroup.mem_zpowers z⟩
    · rintro hq ⟨w, hw⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      have hzq : z ∈ MulAction.stabilizer G q := MulAction.mem_stabilizer_iff.mpr hq
      exact MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer G q).zpow_mem hzq k)
  have hmod := h2.card_modEq_card_fixedPoints (G ⧸ N)
  have h1 : Nat.card ({((1 : G) : G ⧸ N)} : Set (G ⧸ N)) = 1 := Nat.card_unique
  rw [hfix, h1] at hmod
  exact Nat.odd_iff.mpr hmod

theorem exists_sylow_two_eq_map_of_odd_index [Finite G] {N : Subgroup G} (hN : Odd N.index)
    (T : Sylow 2 N) : ∃ S : Sylow 2 G, (S : Subgroup G) = (T : Subgroup N).map N.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ((T : Subgroup N).map N.subtype) := T.isPGroup'.map N.subtype
  have hidx : ¬ 2 ∣ ((T : Subgroup N).map N.subtype).index := by
    rw [Subgroup.index_map_subtype]
    intro h
    rcases (Nat.prime_two.dvd_mul).mp h with h1 | h1
    · exact T.not_dvd_index h1
    · exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hN) h1
  exact ⟨hP.toSylow hidx, rfl⟩

theorem exists_sylow_two_two_central [Finite G] {N : Subgroup G} {z : G} (hz : orderOf z = 2)
    (hfix : ∀ q : G ⧸ N, z • q = q ↔ q = ((1 : G) : G ⧸ N))
    (hT : ∃ T : Sylow 2 N, z ∈ (T : Subgroup N).map N.subtype ∧
      (T : Subgroup N).map N.subtype ≤ Subgroup.centralizer {z}) :
    ∃ S : Sylow 2 G, z ∈ (S : Subgroup G) ∧ (S : Subgroup G) ≤ Subgroup.centralizer {z} := by
  obtain ⟨T, hzT, hTc⟩ := hT
  obtain ⟨S, hS⟩ := exists_sylow_two_eq_map_of_odd_index (odd_index_of_unique_fixed hz hfix) T
  exact ⟨S, hS ▸ hzT, hS ▸ hTc⟩

end CFSG.RankThree.PartTwo.Sec21
