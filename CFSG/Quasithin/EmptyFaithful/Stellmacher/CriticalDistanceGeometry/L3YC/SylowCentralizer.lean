module

public import CFSG.Quasithin.EmptyFaithful.S153Plus
public import CFSG.Quasithin.EmptyFaithful.S153Baum

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

theorem eq_zpowers_of_card_two {K : Subgroup G} (hK : Nat.card K = 2) {c : G} (hc : c ∈ K)
    (hc1 : c ≠ 1) : K = Subgroup.zpowers c := by
  symm
  refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hc) ?_
  rw [Nat.card_zpowers, hK]
  have h1 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.mp h)
  have h0 : 0 < orderOf c := orderOf_pos c
  omega

omit [Finite G] in
theorem centralizer_zpowers_eq (c : G) :
    Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem isSylowTwoOf_centralizer_singleton (h11 : StageLemma14111) {T Mc M V₁ V₂ : Subgroup G}
    {t : G} (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) {c : G} (hc : c ∈ V₁) (hc1 : c ≠ 1)
    (hcS : c ∈ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G))
    (hcard : Nat.card ↥(V₁ ⊓ Subgroup.centralizer ((Sgp153 T V₁ : Subgroup G) : Set G)) = 2) :
    IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({c} : Set G)) := by
  have h3 := (h.lemma_15_3_6 h11 D).2.2.1
  have hK := eq_zpowers_of_card_two hcard ⟨hc, hcS⟩ hc1
  rw [hK, centralizer_zpowers_eq] at h3
  exact h3

omit [Finite G] in
theorem map_conj_centralizer_singleton (c g : G) :
    (Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * c * g⁻¹} : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : g * (c * y) * g⁻¹ = g * (y * c) * g⁻¹ := by rw [hy]
    calc g * c * g⁻¹ * (g * y * g⁻¹) = g * (c * y) * g⁻¹ := by group
      _ = g * (y * c) * g⁻¹ := h1
      _ = g * y * g⁻¹ * (g * c * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc c * (g⁻¹ * x * g) = g⁻¹ * (g * c * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * c * g⁻¹)) * g := by rw [hx]
      _ = g⁻¹ * x * g * c := by group

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    S.map (MulAut.conj g).toMonoidHom = S := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    exact (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * x * g)).mpr (by rw [e]; exact hx)

omit [Finite G] in
theorem isSylowTwoOf_centralizer_conj {S : Subgroup G} {c : G}
    (hS : IsSylowTwoOf S (Subgroup.centralizer ({c} : Set G))) {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    IsSylowTwoOf S (Subgroup.centralizer ({g * c * g⁻¹} : Set G)) := by
  have hSf := map_conj_eq_of_mem_normalizer hg
  have hHf := map_conj_centralizer_singleton c g
  refine ⟨?_, hS.2.1, ?_⟩
  · rw [← hHf, ← hSf]
    exact Subgroup.map_mono hS.1
  · have : S.relIndex (Subgroup.centralizer ({g * c * g⁻¹} : Set G)) =
        S.relIndex (Subgroup.centralizer ({c} : Set G)) := by
      calc S.relIndex (Subgroup.centralizer ({g * c * g⁻¹} : Set G))
          = (S.map (MulAut.conj g).toMonoidHom).relIndex
              ((Subgroup.centralizer ({c} : Set G)).map (MulAut.conj g).toMonoidHom) := by
            rw [hSf, hHf]
        _ = _ := Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
    change ¬ 2 ∣ S.relIndex (Subgroup.centralizer ({g * c * g⁻¹} : Set G))
    rw [this]
    exact hS.2.2

end Stellmacher.CD.L3YC

end CFSG.Quasithin
