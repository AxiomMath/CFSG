module

public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.Open.StatedDefs
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.ReflConj
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Derived
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Structure
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Class
import CFSG.OddTranspositions.PartThree.Eleven.FiveMinus.Aut
import CFSG.ClassicalGroups.Orthogonal.FiveSquareModel
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.GroupTheory.CentralizerMapMulEquiv
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.ClassicalGroups.Orthogonal

theorem isFiveReflectionModel_four_true_false_of_derived {G : Type} [Group G] [Finite G] (u : G)
    (hPSp : CFSG.Open.StatedClassicalModel (commutator G) .PSp 2 5 1)
    (hC : Subgroup.centralizer (commutator G : Set G) = ⊥) (hu : orderOf u = 2)
    (hout : u ∉ commutator G) (h13 : 13 ∣ Nat.card (Subgroup.centralizer ({u} : Set G))) :
    IsFiveReflectionModel 4 true false {g | IsConj u g} := by
  unfold IsFiveReflectionModel CFSG.Open.fischerCentralQuotientModel
  have hLie : CFSG.Blueprint.LieModel (commutator G) .PSp 2 5 1 := Or.inl ⟨by decide, hPSp⟩
  have hΩ : CFSG.Open.StatedClassicalModel FiveSquareFrameGeneration.derived .PSp 2 5 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num)
      CFSG.ClassicalGroups.Orthogonal.FiveSquareModel.lieModel_derived
  obtain ⟨e₁⟩ :=
    CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hPSp hΩ
  obtain ⟨e₂⟩ := nonempty_commutator_fiveReflectionGroup_four_true_false_mulEquiv
  have hAutG : Nat.card (MulAut (commutator G)) ≤ 2 * Nat.card (commutator G) :=
    card_mulAut_le_two_mul_card_of_lieModel_psp_two_five hLie
  have hNne : commutator G ≠ ⊤ := by
    intro htop
    exact hout (htop ▸ Subgroup.mem_top u)
  have hGcard : Nat.card G = 2 * Nat.card (commutator G) :=
    card_eq_two_mul_card_of_centralizer_eq_bot hC hAutG hNne
  have hAutR : (commutator (fiveReflectionGroup 4 true false)).index = 2 :=
    index_commutator_fiveReflectionGroup_four_true_false
  have hRcard : Nat.card (fiveReflectionGroup 4 true false) =
      2 * Nat.card (commutator (fiveReflectionGroup 4 true false)) := by
    have h := Subgroup.card_mul_index (commutator (fiveReflectionGroup 4 true false))
    rw [hAutR, mul_comm] at h
    exact h.symm
  have hcardN : Nat.card (commutator G) =
      Nat.card (commutator (fiveReflectionGroup 4 true false)) := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv]
  have hcardG : Nat.card G = Nat.card (fiveReflectionGroup 4 true false) := by
    rw [hGcard, hRcard, hcardN]
  have hAut_le : Nat.card (MulAut (commutator G)) ≤ Nat.card G := by
    rw [hGcard]
    exact hAutG
  have hCR : Subgroup.centralizer (commutator (fiveReflectionGroup 4 true false) :
      Set (fiveReflectionGroup 4 true false)) = ⊥ :=
    centralizer_commutator_fiveReflectionGroup_four_true_false
  obtain ⟨Φ⟩ := nonempty_mulEquiv_of_centralizer_eq_bot_of_card_eq (e₁.trans e₂.symm) hC hCR
    hcardG hAut_le
  have hmem_deriv : ∀ g : G, Φ g ∈ commutator (fiveReflectionGroup 4 true false) ↔
      g ∈ commutator G := by
    intro g
    constructor
    · intro hg
      have hg' : ((MulEquiv.commutatorCongr Φ).symm ⟨Φ g, hg⟩ : G) ∈ commutator G :=
        ((MulEquiv.commutatorCongr Φ).symm ⟨Φ g, hg⟩).2
      have hcoe : ((MulEquiv.commutatorCongr Φ).symm ⟨Φ g, hg⟩ : G) = g := by
        rw [MulEquiv.coe_commutatorCongr_symm_apply]
        simp
      rwa [hcoe] at hg'
    · intro hg
      have hg' : (MulEquiv.commutatorCongr Φ ⟨g, hg⟩ :
          fiveReflectionGroup 4 true false) ∈
          commutator (fiveReflectionGroup 4 true false) :=
        (MulEquiv.commutatorCongr Φ ⟨g, hg⟩).2
      have hcoe : (MulEquiv.commutatorCongr Φ ⟨g, hg⟩ :
          fiveReflectionGroup 4 true false) = Φ g := by
        rw [MulEquiv.coe_commutatorCongr_apply]
      rwa [hcoe] at hg'
  have htu_notmem : Φ u ∉ commutator (fiveReflectionGroup 4 true false) := by
    intro h
    exact hout ((hmem_deriv u).mp h)
  have htdet : Matrix.GeneralLinearGroup.det
      ((Φ u : fiveReflectionGroup 4 true false) : GL (Fin 5) (ZMod 5)) ≠ 1 := by
    intro hdet
    exact htu_notmem
      ((mem_commutator_fiveReflectionGroup_four_true_false_iff (Φ u)).mpr hdet)
  have h13' : 13 ∣ Nat.card (Subgroup.centralizer
      ({(Φ u)} : Set (fiveReflectionGroup 4 true false))) := by
    rw [← CFSG.GroupTheory.card_centralizer_singleton_mulEquiv Φ u]
    exact h13
  have ht2 : orderOf (Φ u) = 2 := by rw [MulEquiv.orderOf_eq Φ u, hu]
  have htref : ((Φ u : fiveReflectionGroup 4 true false) : GL (Fin 5) (ZMod 5)) ∈
      fiveReflections 4 true false :=
    mem_fiveReflections_four_true_false_of_dvd_card_centralizer ht2 htdet h13'
  have hZ : Subgroup.center (fiveReflectionGroup 4 true false) = ⊥ :=
    center_fiveReflectionGroup_four_true_false
  let ψ : G ≃* fiveReflectionGroup 4 true false ⧸
      Subgroup.center (fiveReflectionGroup 4 true false) :=
    Φ.trans (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm))
  have hψ : ∀ g : G, ψ g = (QuotientGroup.mk (Φ g) :
      fiveReflectionGroup 4 true false ⧸
        Subgroup.center (fiveReflectionGroup 4 true false)) := by
    intro g
    rfl
  refine ⟨ψ, fun g => ?_⟩
  rw [Set.mem_setOf_eq]
  constructor
  · intro hconj
    have hconjΦ : IsConj (Φ u) (Φ g) := MonoidHom.map_isConj Φ.toMonoidHom hconj
    obtain ⟨c, hc⟩ := isConj_iff.mp hconjΦ
    refine ⟨Φ g, ?_, hψ g⟩
    have hcoe : ((Φ g : fiveReflectionGroup 4 true false) : GL (Fin 5) (ZMod 5)) =
        (c : GL (Fin 5) (ZMod 5)) * ((Φ u : fiveReflectionGroup 4 true false) :
          GL (Fin 5) (ZMod 5)) * (c : GL (Fin 5) (ZMod 5))⁻¹ := by
      have h := congrArg (fun x : fiveReflectionGroup 4 true false =>
        (x : GL (Fin 5) (ZMod 5))) hc
      simpa using h.symm
    rw [hcoe]
    exact conj_mem_fiveReflections (fiveForm_mulVec_of_mem c.2) htref
  · rintro ⟨h, hhT, hψg⟩
    have hg_eq : Φ g = h := by
      have h1 : ψ g = ψ (Φ.symm h) := by
        rw [hψg, hψ, MulEquiv.apply_symm_apply]
      have h2 : g = Φ.symm h := ψ.injective h1
      rw [h2, MulEquiv.apply_symm_apply]
    have hhT' : ((Φ g : fiveReflectionGroup 4 true false) : GL (Fin 5) (ZMod 5)) ∈
        fiveReflections 4 true false := by
      rw [hg_eq]
      exact hhT
    obtain ⟨c, hc, hconj⟩ :=
      exists_conj_eq_of_mem_fiveReflections_four_true_false htref hhT'
    have hzu : IsConj (Φ u) (Φ g) := by
      refine isConj_iff.mpr ⟨⟨c, hc⟩, ?_⟩
      apply Subtype.ext
      simpa using hconj
    have hmap := MonoidHom.map_isConj
      (Φ.symm : fiveReflectionGroup 4 true false →* G) hzu
    simpa using hmap

end CFSG.OddTranspositions.PartThree
