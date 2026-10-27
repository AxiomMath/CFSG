module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Setup
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1_cxh_not_mem (S : s16c4v1_Sit D V L hV) {g : G} (hg : s16c4v1_Cex D V g) :
    g ∉ D.M := by
  intro hgM
  apply hg.2
  rw [conjSubgroup_eq_iff_mem_normalizer.2
    (S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer hgM)]
  exact Subgroup.commutator_self_eq_bot_iff.mpr
    S.sect.setting.hyp16.hyp125.pairFacts.elemAbelian.1

theorem s16c4v1_cxh_conj_mem_of_conj_le {g : G}
    (hVn : D.M ≤ Subgroup.normalizer (V : Set G))
    (hA' : conjSubgroup V g⁻¹ ≤ D.M) {x a : G} (hx : x ∈ V)
    (ha : a ∈ conjSubgroup V g) : x * a * x⁻¹ ∈ conjSubgroup V g := by
  have hga : g * a * g⁻¹ ∈ V := (mem_conjSubgroup_iff).1 ha
  have hxm : g * x * g⁻¹ ∈ D.M := by
    refine hA' ?_
    rw [mem_conjSubgroup_iff]
    have h1 : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
    rw [h1]
    exact hx
  have hconj : (g * x * g⁻¹) * (g * a * g⁻¹) * (g * x * g⁻¹)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.1 (hVn hxm) (g * a * g⁻¹)).1 hga
  refine (mem_conjSubgroup_iff).2 ?_
  rw [show g * (x * a * x⁻¹) * g⁻¹ =
      (g * x * g⁻¹) * (g * a * g⁻¹) * (g * x * g⁻¹)⁻¹ by group]
  exact hconj

theorem s16c4v1_cxh_card_barSub (S : s16c4v1_Sit D V L hV) (h1217 : R1217 D)
    {A : Subgroup G} (hA : A ≤ D.M) :
    Nat.card (barSub (v1Sub D.M ⊥ V hV L) V hV A) =
      (Subgroup.centralizer (V : Set G)).relIndex A := by
  have hVn := S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer
  have hV1n : D.M ≤ Subgroup.normalizer (v1Sub D.M ⊥ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub S.sect.setting.hyp16.hyp125 hV
  rw [CFSG.LocalAnalysis.WeakClosure81.card_barSub_eq_relIndex hV hVn hV1n hA]
  have hCT : A ⊓ F11.CTilde D.M (v1Sub D.M ⊥ V hV L) V =
      A ⊓ Subgroup.centralizer (V : Set G) := by
    ext a
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨haA, haC⟩
      obtain ⟨-, h, h1⟩ := (mem_cTilde_iff hV hVn).1 haC
      refine ⟨haA, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have htriv : ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ v1Sub D.M ⊥ V hV L :=
        (actTil_eq_one_iff (v1Sub D.M ⊥ V hV L) V hV ⟨a, h⟩).1 h1
      have hfix := (s16c4v1_centralizes_iff S h1217 (hA haA)).1 htriv
      calc v * a = (a * v * a⁻¹) * a := by rw [hfix v hv]
        _ = a * v := by group
    · rintro ⟨haA, hc⟩
      refine ⟨haA, ?_⟩
      rw [mem_cTilde_iff hV hVn]
      refine ⟨hA haA, s16c4v1_mem_stabTil S (hA haA), ?_⟩
      rw [actTil_eq_one_iff]
      intro v hv
      have hcomm : a * v = v * a := (Subgroup.mem_centralizer_iff.1 hc v hv).symm
      have h1 : a * v * a⁻¹ * v⁻¹ = 1 := by rw [hcomm]; group
      rw [h1]
      exact (v1Sub D.M ⊥ V hV L).one_mem
  rw [hCT, Subgroup.inf_relIndex_left]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
