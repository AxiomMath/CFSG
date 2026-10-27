module

public import CFSG.Quasithin.Recognition.J2RecTwoB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

namespace S1421QA17

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_conj_mem_centralizer (h : IsTypeH2 G z) {y : G} (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPC⟩ := h.exists_sylow_le_centralizer
  have hsp : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [pow_two]) hy1, pow_one])
  obtain ⟨T', hT'⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T' P
  have h1 : MulAut.conj g y ∈ MulAut.conj g • (T' : Subgroup G) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ (hT' (Subgroup.mem_zpowers y))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  have hgs : g * y * g⁻¹ ∈ (P : Subgroup G) := by simpa [MulAut.conj_apply] using h1
  exact ⟨g, hPC hgs⟩

omit [Finite G] in
private theorem conj_mul_self {y : G} (hy2 : y * y = 1) (g : G) :
    (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
  calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    _ = 1 := by rw [hy2]; group

omit [Finite G] in
private theorem conj_ne_one {y : G} (hy1 : y ≠ 1) (g : G) : g * y * g⁻¹ ≠ 1 := fun h1 =>
  hy1 (by
    calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)

theorem exists_conj_cover (h : IsTypeH2 G z) :
    ∃ t : G, ∀ y : G, y * y = 1 → y ≠ 1 → IsConj z y ∨ IsConj t y := by
  by_cases hex : ∃ t ∈ Subgroup.centralizer ({z} : Set G), t * t = 1 ∧
      t ∉ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))
  · obtain ⟨t, htC, ht2, htQ⟩ := hex
    obtain ⟨L, hLC, hLQ, hL⟩ := h.exists_complement_of_involution htC ht2 htQ
    obtain ⟨F, -⟩ := J2Frame.exists_frame h hLC hLQ hL
    refine ⟨F.t, fun y hy2 hy1 => ?_⟩
    obtain ⟨g, hg⟩ := exists_conj_mem_centralizer h hy2 hy1
    by_cases hgQ : g * y * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))
    · left
      exact (h.isConj_of_mem_pCoreOf hgQ (conj_mul_self hy2 g) (conj_ne_one hy1 g)).trans
        (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    · right
      obtain ⟨c, -, hc⟩ := F.exists_conj_eq_t hg (conj_mul_self hy2 g) hgQ
      exact isConj_iff.mpr ⟨(c * g)⁻¹, by
        rw [← hc]
        group⟩
  · refine ⟨z, fun y hy2 hy1 => Or.inl ?_⟩
    obtain ⟨g, hg⟩ := exists_conj_mem_centralizer h hy2 hy1
    have hgQ : g * y * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
      by_contra hQ
      exact hex ⟨_, hg, conj_mul_self hy2 g, hQ⟩
    exact (h.isConj_of_mem_pCoreOf hgQ (conj_mul_self hy2 g) (conj_ne_one hy1 g)).trans
      (isConj_iff.mpr ⟨g⁻¹, by group⟩)

theorem involutionClassCount_le_two (h : IsTypeH2 G z) :
    involutionClassCount G = 1 ∨ involutionClassCount G = 2 := by
  obtain ⟨t, ht⟩ := exists_conj_cover h
  set S := {c : ConjClasses G | ∃ x : G, x ^ 2 = 1 ∧ x ≠ 1 ∧ ConjClasses.mk x = c} with hS
  have hsub : S ⊆ {ConjClasses.mk z, ConjClasses.mk t} := by
    rintro _ ⟨x, hx2, hx1, rfl⟩
    rcases ht x (by rwa [pow_two] at hx2) hx1 with h1 | h1
    · exact Or.inl (ConjClasses.mk_eq_mk_iff_isConj.mpr h1).symm
    · exact Or.inr (ConjClasses.mk_eq_mk_iff_isConj.mpr h1).symm
  have h2 : S.ncard ≤ 2 := by
    refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have h1 : 0 < S.ncard :=
    (Set.ncard_pos (Set.toFinite S)).mpr ⟨ConjClasses.mk z, z, h.sq, h.ne_one, rfl⟩
  change S.ncard = 1 ∨ S.ncard = 2
  omega

end S1421QA17

end CFSG.Quasithin
