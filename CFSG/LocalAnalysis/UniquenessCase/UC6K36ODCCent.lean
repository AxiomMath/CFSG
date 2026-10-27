module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCL227
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Defs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273b
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterCoreFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise

theorem ODC.nonempty_mulEquiv_psl2_of_isLTwoTwentySeven {X : Type} [Group X]
    (h : IsLTwoTwentySeven X) :
    Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GaloisField 3 3) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 3 3) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 3 3 (by norm_num)]
    norm_num
  exact ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans
    (CFSG.GorensteinWalter.psl2RingEquiv (FiniteField.ringEquivOfCardEq hcard)))⟩

theorem oddDefCharCentralizer_of_coreFree
    (hIn : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hOut : CFSG.HardMathSupport.Dickson.I271.DefCharOuterCoreFree)
    (hCar : ∀ F, CFSG.HardMathSupport.Dickson.DefCharOuter.Export.CarrierOn F) :
    OddDefCharCentralizer := by
  intro d hodd ε hεp hε1 R hR1 hR2 hRc hRn
  obtain ⟨hfin, hsimp, hnab⟩ :=
    hCar (CFSG.Yardstones.Md42047359a2a.lieFamily d.1) d rfl hodd
  haveI := hfin
  haveI := hsimp
  have hp : d.1.characteristic.Prime := TauCeti.LieTypeIndex.characteristic_prime d.1
  haveI : Fact d.1.characteristic.Prime := ⟨hp⟩
  have hZ : center (CatGrp d) = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.DefChar.center_eq_bot_of_simple hsimp hnab
  have hεo : orderOf ε = d.1.characteristic := orderOf_eq_prime hεp hε1
  haveI hInnN : (innerAut (CatGrp d)).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set H : Subgroup (MulAut (CatGrp d)) := innerAut (CatGrp d) ⊔ R with hH
  have hRle : R ≤ GLAPPrimeCoreOf d.1.characteristic
      (H ⊓ centralizer ({ε} : Set (MulAut (CatGrp d)))) := by
    refine CFSG.HardMathSupport.Dickson.I271.le_glaPPrimeCoreOf_of_normal' hp
      (fun r hr => ⟨mem_sup_right hr, mem_centralizer_singleton_iff.2 (hRc r hr)⟩) ?_ ?_
    · refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨hgH, hgC⟩ := g.2
      have hgH' : (g : MulAut (CatGrp d)) ∈
          ((innerAut (CatGrp d) : Set (MulAut (CatGrp d))) * (R : Set (MulAut (CatGrp d)))) := by
        rw [← normal_mul]
        exact hgH
      obtain ⟨i, hi, r₀, hr₀, hir⟩ := hgH'
      have hgc : Commute (g : MulAut (CatGrp d)) ε := mem_centralizer_singleton_iff.1 hgC
      have hrc : Commute r₀ ε := hRc r₀ hr₀
      have hie : i = (g : MulAut (CatGrp d)) * r₀⁻¹ := eq_mul_inv_of_mul_eq hir
      have hic : Commute i ε := hie ▸ hgc.mul_left hrc.inv_left
      obtain ⟨k, rfl⟩ := hi
      have hk : ε k = k := (CFSG.HardMathSupport.Dickson.I271.conj_mem_centralizer_iff hZ ε k).1
        (mem_centralizer_singleton_iff.2 hic)
      have he : ((g * n * g⁻¹ : ↥(H ⊓ centralizer ({ε} : Set (MulAut (CatGrp d))))) :
          MulAut (CatGrp d)) =
          MulAut.conj k * (r₀ * (n : MulAut (CatGrp d)) * r₀⁻¹) * (MulAut.conj k)⁻¹ := by
        push_cast
        rw [← hir]
        group
      rw [he]
      exact hRn k hk _ (R.mul_mem (R.mul_mem hr₀ hn) (R.inv_mem hr₀))
    · intro hdvd
      obtain ⟨m, hm⟩ := hR2.exists_card_eq
      rw [hm] at hdvd
      exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  by_cases hin : ε ∈ innerAut (CatGrp d)
  · exfalso
    have h0 := hIn (CatGrp d) hsimp hnab d ⟨MulEquiv.refl _⟩ _ hp hodd rfl ε hin hεo H
      le_sup_left
    rw [h0] at hRle
    exact hR1 (eq_bot_iff.2 hRle)
  · by_cases hexc : d.1.characteristic = 3 ∧ IsLTwoTwentySeven (CatGrp d)
    · exact ⟨hexc.1, ODC.nonempty_mulEquiv_psl2_of_isLTwoTwentySeven hexc.2, hin⟩
    · exfalso
      have h0 := hOut (CatGrp d) hsimp hnab d ⟨MulEquiv.refl _⟩ _ hp hodd rfl hexc ε hεo hin H
        le_sup_left
      rw [h0] at hRle
      exact hR1 (eq_bot_iff.2 hRle)

section Holds


theorem oddDefCharCentralizer_holds : OddDefCharCentralizer :=
  oddDefCharCentralizer_of_coreFree
    CFSG.HardMathSupport.Solomon.Coordinator.defCharInnerCoreFree_holds
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273b.defCharOuterCoreFree_holds
    (fun F => (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.outerCentAll_holds F).1)

theorem k36OddDefChar_holds : K36OddDefChar :=
  ⟨oddDefCharCentralizer_holds, l227Generation_holds⟩

end Holds

end CFSG.LocalAnalysis.UniquenessCase.UCK
