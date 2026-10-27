module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.GroupTheory.QuotientCoreFacts
import CFSG.HardMathSupport.Cooperstein.Proving.PCoreSup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddFix
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSimple
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R93c
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem comm_I9_L9_le (S : Slice D L D₃ Y H q) (hI : F09.I9 H ≤ D.M) :
    ⁅F09.I9 H, F09.L9 Y H⁆ ≤ pCoreOf 2 H := by
  have hHI : H ≤ normalizer (F09.I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hO : pCoreOf 2 (F09.I9 H) ≤ pCoreOf 2 H := by
    refine UCK.le_pCoreOf_of_normal ?_ ⟨fun o ho h => ?_⟩ ?_
    · rw [CFSG.openPCoreOf_eq_map_pCore]
      exact (map_subtype_le _).trans (map_subtype_le _)
    · rw [Subgroup.mem_subgroupOf] at ho ⊢
      simpa using CFSG.HardMathSupport.Cooperstein.Proving.conj_mem_pCoreOf (hHI h.2) ho
    · rw [CFSG.openPCoreOf_eq_map_pCore]
      exact CFSG.pCore_isPGroup.map _
  rw [Subgroup.commutator_le]
  intro i hi y hy
  have h := (pCoreOf 2 (F09.I9 H)).inv_mem (S.mul_mul_inv_mul_inv_mem_pCoreOf hI hy hi)
  rw [show (y * i * y⁻¹ * i⁻¹)⁻¹ = ⁅i, y⁆ by rw [commutatorElement_def]; group] at h
  exact hO h

theorem commutator_subgroupOf_L9 (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) :
    ⁅(F09.L9 Y H).subgroupOf H, (F09.L9 Y H).subgroupOf H⁆ = (F09.L9 Y H).subgroupOf H := by
  have hX : ⁅Opp 3 Y, Opp 3 Y⁆ = Opp 3 Y := Subgroup.isPerfect_iff.mp
    (F09.isPerfect_opp (F09.not_hasE9_opp hyp) S.not_isPGroup_barO3_opp)
  have hL : ⁅F09.L9 Y H, F09.L9 Y H⁆ = F09.L9 Y H := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact (F09.L9 Y H).mul_mem ((F09.L9 Y H).mul_mem ((F09.L9 Y H).mul_mem ha hb)
        ((F09.L9 Y H).inv_mem ha)) ((F09.L9 Y H).inv_mem hb)
    · refine iSup_le fun h => ?_
      have hle : (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom ≤ F09.L9 Y H :=
        le_iSup (fun h : ↥H => (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom) h
      calc (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom
          = ⁅(Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom,
              (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom⁆ := by
            rw [← Subgroup.map_commutator, hX]
        _ ≤ ⁅F09.L9 Y H, F09.L9 Y H⁆ := Subgroup.commutator_mono hle hle
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 (L9_le_of_le S.Y_le_H), hL]

theorem nonempty_lbar9_mulEquiv (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M) :
    Nonempty (F09.Lbar9 Y H ≃*
      (↥(barImage H (F09.L9 Y H)) ⧸ Subgroup.center ↥(barImage H (F09.L9 Y H)))) := by
  have hPP := S.commutator_subgroupOf_L9 hyp
  have h23 : CFSG.pCore 2 ↥H ≤ CFSG.pPrimeCore 3 ↥H :=
    CFSG.GroupTheory.pCore_le_pPrimeCore Nat.prime_two Nat.prime_three (by norm_num) ↥H
  let ψ : Bar2 H →* F09.Hbar9 H :=
    QuotientGroup.map (CFSG.pCore 2 ↥H) (CFSG.pPrimeCore 3 ↥H) (MonoidHom.id _) h23
  have hψ : ψ.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) := by
    ext x
    rfl
  have himg : (barImage H (F09.L9 Y H)).map ψ = F09.img9 H (F09.L9 Y H) := by
    rw [barImage, Subgroup.map_map, hψ]
    rfl
  let φ : ↥(barImage H (F09.L9 Y H)) →* F09.Lbar9 Y H :=
    (MulEquiv.subgroupCongr himg).toMonoidHom.comp (ψ.subgroupMap (barImage H (F09.L9 Y H)))
  have hφ : Function.Surjective φ :=
    (MulEquiv.subgroupCongr himg).surjective.comp (ψ.subgroupMap_surjective _)
  haveI : IsSimpleGroup (F09.Lbar9 Y H) := S.isSimpleGroup_Lbar9 hyp
  have hcen : Subgroup.center (F09.Lbar9 Y H) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (F09.Lbar9 Y H)) with h | h
    · exact h
    · exfalso
      haveI : Group.IsPerfect (F09.Lbar9 Y H) := Subgroup.isPerfect_iff.mpr (by
        rw [F09.img9, ← Subgroup.map_commutator, hPP])
      haveI : IsMulCommutative (F09.Lbar9 Y H) := ⟨⟨fun a b =>
        Subgroup.mem_center_iff.mp ((Subgroup.eq_top_iff' _).mp h b) a⟩⟩
      exact Group.IsPerfect.not_isMulCommutative (G := F09.Lbar9 Y H) inferInstance
  have hker : φ.ker = Subgroup.center ↥(barImage H (F09.L9 Y H)) := by
    refine le_antisymm (fun x hx => ?_) (fun z hz => ?_)
    · have hx1 : ψ (x : Bar2 H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      obtain ⟨h₀, hh₀, hx₀⟩ := Subgroup.mem_map.mp x.2
      have hh₀I : (h₀ : G) ∈ F09.I9 H := by
        have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) h₀ = 1 := by
          rw [← hψ, MonoidHom.comp_apply, hx₀, hx1]
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_map_of_mem H.subtype h1
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y₀, hy₀, hw₀⟩ := Subgroup.mem_map.mp w.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx₀, ← hw₀, ← map_mul, ← map_mul,
        QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        show (y₀ * h₀)⁻¹ * (h₀ * y₀) = ⁅h₀⁻¹, y₀⁻¹⁆ by rw [commutatorElement_def]; group]
      have hc := S.comm_I9_L9_le hI (Subgroup.commutator_mem_commutator
        ((F09.I9 H).inv_mem hh₀I) ((F09.L9 Y H).inv_mem (Subgroup.mem_subgroupOf.mp hy₀)))
      rw [CFSG.openPCoreOf_eq_map_pCore] at hc
      refine (Subgroup.mem_map_iff_mem H.subtype_injective).mp ?_
      rw [map_commutatorElement, map_inv, map_inv]
      exact hc
    · rw [MonoidHom.mem_ker]
      have hz' : φ z ∈ Subgroup.center (F09.Lbar9 Y H) := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨w', rfl⟩ := hφ w
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w']
      rwa [hcen, Subgroup.mem_bot] at hz'
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)).symm⟩

theorem isQuasisimple_barImage_L9 (S : Slice D L D₃ Y H q) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M) :
    CFSG.Open.IsQuasisimple ↥(barImage H (F09.L9 Y H)) := by
  obtain ⟨e⟩ := S.nonempty_lbar9_mulEquiv hyp hI
  haveI := S.isSimpleGroup_Lbar9 hyp
  haveI : Group.IsPerfect ↥(barImage H (F09.L9 Y H)) := Subgroup.isPerfect_iff.mpr (by
    rw [barImage, ← Subgroup.map_commutator, S.commutator_subgroupOf_L9 hyp])
  exact ⟨Group.IsPerfect.commutator_eq_top, e.symm.isSimpleGroup⟩

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
