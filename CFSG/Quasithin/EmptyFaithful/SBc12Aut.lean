module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc12

variable {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem autI_le_of_inf_normalizer_le {K K' : Subgroup G}
    (h : K ⊓ Subgroup.normalizer (V : Set G) ≤ K') : autI hV K ≤ autI hV K' := by
  intro φ hφ
  obtain ⟨g, hg, e⟩ := (mem_autI hV).1 hφ
  exact (mem_autI hV).2 ⟨g, h ⟨hg, g.2⟩, e⟩

theorem isPGroup_autI {K : Subgroup G}
    (h : ∀ x ∈ K ⊓ Subgroup.normalizer (V : Set G),
      ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G)) : IsPGroup 2 ↥(autI hV K) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hφ
  obtain ⟨k, hk⟩ := h g ⟨hg, g.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  show (convI hV g) ^ 2 ^ k = 1
  rw [← map_pow]
  exact (convI_eq_one_iff hV (g ^ 2 ^ k)).2 (by simpa using hk)

theorem relIndex_inf_centralizer_le_card_autI [Finite G] {K T : Subgroup G} (hTK : T ≤ K)
    (hTN : T ≤ Subgroup.normalizer (V : Set G)) :
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T ≤ Nat.card ↥(autI hV K) := by
  let f : ↥T →* MulAut (IntMod V hV) := (convI hV).comp (Subgroup.inclusion hTN)
  have hker : f.ker = (T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show convI hV (Subgroup.inclusion hTN x) = 1 ↔ _
    rw [convI_eq_one_iff]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hrange : f.range ≤ autI hV K := by
    rintro _ ⟨x, rfl⟩
    exact convI_mem_autI hV (hTK x.2) (hTN x.2)
  have h1 : f.ker.index = Nat.card f.range := Subgroup.index_ker f
  show ((T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf T).index ≤ _
  rw [← hker, h1]
  exact Subgroup.card_le_of_le hrange

end SBc12

end CFSG.Quasithin
