module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem exists_sc_subgroup_of_mulEquiv {p : ℕ} {R G : Type} [Group R] [Group G] (e : R ≃* G)
    {E : Subgroup R} (hE : IsElemAbelian p E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set R), g ^ p = 1 → g ∈ E) :
    ∃ E' : Subgroup G, IsElemAbelian p E' ∧ Nat.card E' = Nat.card E ∧
      ∀ g ∈ Subgroup.centralizer (E' : Set G), g ^ p = 1 → g ∈ E' := by
  refine ⟨E.map e.toMonoidHom, hE.map e.toMonoidHom,
    Subgroup.card_map_of_injective e.injective, ?_⟩
  intro g hg hgp
  rw [Subgroup.mem_centralizer_iff] at hg
  have hmem : e.symm g ∈ Subgroup.centralizer (E : Set R) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxg : e x * g = g * e x := hg (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    have h := congrArg (fun y => e.symm y) hxg
    simpa using h
  have hpow : (e.symm g) ^ p = 1 := by
    have h : e ((e.symm g) ^ p) = e 1 := by
      rw [map_pow, e.apply_symm_apply, hgp, map_one]
    exact e.injective h
  have hx := hSC (e.symm g) hmem hpow
  rw [Subgroup.mem_map]
  exact ⟨e.symm g, hx, e.apply_symm_apply g⟩

end CFSG.StandardType
