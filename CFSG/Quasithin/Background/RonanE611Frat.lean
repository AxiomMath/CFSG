module

public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.ONanE68LieBar
public import CFSG.Quasithin.Background.ONanE68LieSinger
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127EvenMain
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E6.E68Proof

variable {G : Type} [Group G] [Finite G]

theorem frattini_normalizer {H L S : Subgroup G} (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) (hS : IsSylowTwoOf S L) {g : G} (hg : g ∈ H) :
    ∃ l ∈ L, l⁻¹ * g ∈ Subgroup.normalizer (S : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgN : g ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).1 hLn hg
  set S' : Subgroup G := S.map (MulAut.conj g).toMonoidHom with hS'def
  have hL' : L.map (MulAut.conj g).toMonoidHom = L := by
    have h1 : CFSG.conjugate L g⁻¹ = L :=
      BenderBranch.conjugate_eq_iff_mem_normalizer.2 (Subgroup.inv_mem _ hgN)
    rw [CFSG.conjugate, inv_inv] at h1
    exact h1
  have hS' : IsSylowTwoOf S' L := by
    have h1 : IsSylowTwoOf S' (L.map (MulAut.conj g).toMonoidHom) := F7.isSylowTwoOf_conj hS g
    rw [hL'] at h1
    exact h1
  have hS0 : IsSylowTwoOf (S.subgroupOf L) ⊤ := isSylowTwoOf_subgroupOf_top_of hS
  have hS'0 : IsSylowTwoOf (S'.subgroupOf L) ⊤ := isSylowTwoOf_subgroupOf_top_of hS'
  obtain ⟨l, hl⟩ := L246C127.exists_conj_of_isSylowTwoOf' hS0 hS'0
  refine ⟨l, l.2, ?_⟩
  refine mem_normalizer_of_conj_le fun s hs => ?_
  have hsS' : g * s * g⁻¹ ∈ S' := ⟨s, hs, rfl⟩
  have hsL : g * s * g⁻¹ ∈ L := hS'.1 hsS'
  have hmem : (⟨g * s * g⁻¹, hsL⟩ : ↥L) ∈ S'.subgroupOf L := hsS'
  rw [← hl] at hmem
  obtain ⟨y, hy, hyeq⟩ := hmem
  have h1 : (l : G) * (y : G) * (l : G)⁻¹ = g * s * g⁻¹ := congrArg Subtype.val hyeq
  have h2 : (l : G)⁻¹ * g * s * ((l : G)⁻¹ * g)⁻¹ = (y : G) := by
    have : (y : G) = (l : G)⁻¹ * (g * s * g⁻¹) * l := by rw [← h1]; group
    rw [this]
    group
  rw [h2]
  exact Subgroup.mem_subgroupOf.1 hy

theorem generalizedFitting_eq_of_unique_component {H L : Subgroup G}
    (hL : IsComponentIn L H) (huniq : ∀ K : Subgroup G, IsComponentIn K H → K = L)
    (hodd : oddCoreIn H = ⊥) :
    (CFSG.generalizedFitting ↥H).map H.subtype = pCoreOf 2 H ⊔ L := by
  classical
  have hlayer : CFSG.layer ↥H = L.subgroupOf H := by
    rw [CFSG.layer.eq_sSup]
    apply le_antisymm
    · apply sSup_le
      intro K hK
      have hKc : IsComponentIn (K.map H.subtype) H := by
        refine ⟨?_, ?_⟩
        · rintro _ ⟨x, -, rfl⟩
          exact x.2
        · rw [show (K.map H.subtype).subgroupOf H = K from
            Subgroup.comap_map_eq_self_of_injective H.subtype_injective K]
          exact hK
      have := huniq _ hKc
      intro x hx
      rw [Subgroup.mem_subgroupOf, ← this]
      exact ⟨x, hx, rfl⟩
    · exact le_sSup hL.2
  have hfit : CFSG.fittingSubgroup ↥H ≤ CFSG.pCore 2 ↥H ⊔ CFSG.oddCore ↥H :=
    CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore
  have hodd' : (CFSG.oddCore ↥H).map H.subtype = ⊥ := hodd
  have hodd'' : CFSG.oddCore ↥H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).1 hodd'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : CFSG.fittingSubgroup ↥H = CFSG.pCore 2 ↥H := by
    refine le_antisymm ?_ (CFSG.pCore_le_fitting _ _)
    rw [hodd'', sup_bot_eq] at hfit
    exact hfit
  rw [CFSG.generalizedFitting.eq_sup, hF, hlayer, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hL.1]
  rfl

end CFSG.Quasithin.RonanE611
