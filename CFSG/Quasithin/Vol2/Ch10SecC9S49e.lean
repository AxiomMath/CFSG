module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122APerfect
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem isQuasisimple_autI_of_central {X J : Subgroup G} (hJ : J ∈ cComp X)
    (hJN : J ≤ Subgroup.normalizer (V : Set G)) (hJC : ¬ J ≤ Subgroup.centralizer (V : Set G))
    (hcen : autI hV (solvRad J) ≤
      Subgroup.centralizer (autI hV J : Set (MulAut (IntMod V hV)))) :
    CFSG.Open.IsQuasisimple ↥(autI hV J) := by
  set ψ := convHom hV J hJN
  have hrange : ψ.range = autI hV J := range_convHom hV J hJN
  let ψ' : ↥J →* ↥(autI hV J) := ψ.codRestrict (autI hV J) fun j => hrange ▸ ⟨j, rfl⟩
  have hψ' : Function.Surjective ψ' := by
    rintro ⟨φ, hφ⟩
    rw [← hrange] at hφ
    obtain ⟨j, rfl⟩ := hφ
    exact ⟨j, rfl⟩
  have hperf : commutator ↥J = ⊤ := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_subtype_commutator, perfect_of_mem_cComp hJ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hcomm : commutator ↥(autI hV J) = ⊤ := by
    have h1 : (⊤ : Subgroup ↥(autI hV J)) = (⊤ : Subgroup ↥J).map ψ' := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ']
    rw [commutator_def, h1, ← Subgroup.map_commutator, ← commutator_def, hperf, ← h1]
  refine ⟨hcomm, ?_⟩
  set χ : ↥J →* ↥(autI hV J) ⧸ Subgroup.center ↥(autI hV J) :=
    (QuotientGroup.mk' (Subgroup.center ↥(autI hV J))).comp ψ'
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hψ'
  have hnt : Nontrivial (↥(autI hV J) ⧸ Subgroup.center ↥(autI hV J)) := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    have hZ : Subgroup.center ↥(autI hV J) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [← QuotientGroup.eq_one_iff]
      exact Subsingleton.elim _ _
    have hab : commutator ↥(autI hV J) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact Subgroup.mem_center_iff.mp (hZ ▸ Subgroup.mem_top x) y
    rw [hab] at hcomm
    apply hJC
    rw [← autI_eq_bot_iff hV hJN, eq_bot_iff]
    intro φ hφ
    have : (⟨φ, hφ⟩ : ↥(autI hV J)) ∈ (⊥ : Subgroup ↥(autI hV J)) := hcomm ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  refine { exists_pair_ne := hnt.exists_pair_ne, eq_bot_or_eq_top_of_normal := fun N hN => ?_ }
  have : (N.comap χ).Normal := hN.comap χ
  rcases normal_eq_top_or_map_le_solvRad hJ (N.comap χ) with h | h
  · right
    rw [eq_top_iff]
    intro q _
    obtain ⟨j, rfl⟩ := hχ q
    have : j ∈ N.comap χ := h ▸ Subgroup.mem_top j
    exact this
  · left
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨j, rfl⟩ := hχ q
    have hjR : (j : G) ∈ solvRad J := h ⟨j, hq, rfl⟩
    have hmem : ψ j ∈ autI hV (solvRad J) := convI_mem_autI hV hjR (hJN j.2)
    have hc := hcen hmem
    rw [Subgroup.mem_bot]
    show QuotientGroup.mk' _ (ψ' j) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hc y.1 y.2)

end CFSG.Quasithin.Vol2.Ch10.SecC
