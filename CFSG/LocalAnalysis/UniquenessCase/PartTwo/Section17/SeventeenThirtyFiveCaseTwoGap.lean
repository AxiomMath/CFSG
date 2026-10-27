module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NatSUnTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34ThreeCentralizerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModuleTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalH1EvenHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_35CaseTwo_holds
    (D : Data G) {V₀ V : Subgroup G}
    (h34 : R17_34At D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h869 : F08.R869 D) (hSyl : UCK.U3Syl)
    (hMin : K_SU3MinDegree) (h36 : W4Lem3_6)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D) (hZ : UCK.U3Center)
    (hC : K_U34ThreeCentralizer) (h846 : F08.R846 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D) :
    Gap17_35CaseTwo D V₀ V := by
  intro L n c H I hV0 hH hI hmn
  subst hV0
  subst hH
  classical
  let hV := c.hyp125.isElemAbelian
  let K : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV L
  let Mb : Subgroup (MulAut (Vtil ⊥ V hV)) := Mbar D.M ⊥ V hV
  let Z : Subgroup (Vtil ⊥ V hV) := fixSupConjSet K Mb
  have hLbar_ne : K ≠ ⊥ :=
    barSub_ne_bot_of_v0_bot D h869 h127 hSyl c.hyp125 c.mem_calC c.shape
  have hcomp : K ∈ compBar D.M ⊥ V hV :=
    barSub_mem_compBar_of_ne_bot c.hyp125 c.mem_calC hLbar_ne
  have hSU : IsSU3 ↥K n := isSU3_barSub c.hyp125 c.mem_calC hLbar_ne c.shape
  have hn2 : 2 ≤ n := UCK.u3Range K n hSU
  have hk2 : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split <;> norm_num
  have hmle : mBar D.M ⊥ V c.hyp125.isElemAbelian ≤ n + 2 :=
    (h34.2.2 L n c rfl).trans (by omega)
  rcases twelve_twentyFour D hx h61 h127 h1214 h128 c.hyp125 hcomp rfl with
    h1 | ⟨hsum, -, -, -⟩ | ⟨Y, e, -, hsumY, hsn, hnatY, -⟩
  · exact (false_of_dMinDeg_le_mBar_S17 h34 hMin c hLbar_ne h1).elim
  · obtain ⟨hn, hm4, hIeq, hnat⟩ :=
      caseTwo_three_six c.hyp125 c.mem_calC hLbar_ne rfl rfl hsum hI hmn c.shape hn2 hmle
        h36
    have hm4' : mBar D.M ⊥ V c.hyp125.isElemAbelian = 4 := hm4
    have hk : D.k = 2 := by
      have h := h34.2.2 L n c rfl
      omega
    subst hn
    have hshape2 : IsSU3 (Bar2 L) 2 := c.shape
    have hL : L = UC22.conjClosure D.M L := by
      obtain ⟨l, hnd, hmem, hjoin⟩ := exists_conjSet_list D L
      rcases Nat.lt_or_ge l.length 4 with h4 | h4
      · rcases Nat.lt_or_ge l.length 3 with h3 | h3
        · exact seventeen_thirtyfive_two_L0 D hSg h846 h76 h614 hZ hC L 2 c l rfl rfl hm4 hk
            hnd hmem (by omega)
        · exact absurd (Data.k_eq_one_of_isStronglyPEmbedded D
            (isStronglyPEmbedded_three_of_three_conj D h82 hZ hC c.mem_calC hshape2 hnd
              (by omega) hmem hjoin)) (by omega)
      · exact absurd (Data.k_eq_one_of_isStronglyPEmbedded D
          (isStronglyPEmbedded_three_of_four_conj D hSg hZ hC c.mem_calC hshape2 hnd h4
            (fun K hK => (hmem K).1 hK))) (by omega)
    have hHK : supConjSet K Mb = K := by
      have h := barSub_conjClosure_eq_iSup_conjSet c.hyp125 c.mem_calC.1.le
      rw [← hL] at h
      exact h.symm
    have hKmem : K ∈ conjSet K Mb :=
      ⟨1, Mb.one_mem, by ext x; simp [MulAut.conj_apply]⟩
    have hKleH : K ≤ supConjSet K Mb :=
      le_iSup₂_of_le (f := fun X (_ : X ∈ conjSet K Mb) => X) K hKmem le_rfl
    have hconj : conjSet K Mb = {K} := by
      ext X
      constructor
      · intro hX
        obtain ⟨m, hm, rfl⟩ := hX
        have hle : K.map (MulAut.conj m).toMonoidHom ≤ supConjSet K Mb :=
          le_iSup₂_of_le (f := fun X (_ : X ∈ conjSet K Mb) => X) _ ⟨m, hm, rfl⟩ le_rfl
        rw [hHK] at hle
        have hcard : Nat.card (K.map (MulAut.conj m).toMonoidHom) = Nat.card K :=
          Subgroup.card_map_of_injective (MulAut.conj m).injective
        exact Set.mem_singleton_iff.mpr
          (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm))
      · intro hX
        rw [Set.mem_singleton_iff] at hX
        subst hX
        exact hKmem
    have htop : commV (autQuot K Z) = ⊤ := by
      have h2 : (⨆ X ∈ conjSet K Mb, commV (autQuot X Z)) = ⊤ := by
        rw [iSup_subtype' (p := fun X : Subgroup (MulAut (Vtil ⊥ V hV)) =>
          X ∈ conjSet K Mb) (f := fun X _ => commV (autQuot X Z))]
        exact hsum.2
      rw [hconj] at h2
      simpa using h2
    have htop' : commV (autQuot K Z) = ⊤ := htop
    have hIeq' : I.map (QuotientGroup.mk' Z) = commV (autQuot K Z) := hIeq
    have hIstar : I.map (QuotientGroup.mk' Z) = ⊤ := by
      rw [hIeq', htop']
    have hKZ : K ≤ stabSub Z := by
      rw [show Z = fixV (supConjSet K Mb) from rfl]
      exact hKleH.trans (CFSG.Quasithin.RonanF918.le_stabSub_fixV _)
    have hZK : Z ≤ fixV K := by
      rw [show Z = fixV (supConjSet K Mb) from rfl]
      exact fixV_anti hKleH
    have hZfix : Z = fixV K := by
      rw [show Z = fixV (supConjSet K Mb) from rfl, hHK]
    have hIbot : (I ⊓ fixV K).map (QuotientGroup.mk' Z) = ⊥ := by
      rw [← hZfix, Subgroup.map_eq_bot_iff]
      intro x hx
      exact (QuotientGroup.ker_mk' Z).ge hx.2
    have hCfix : fixV (autSub (autQuot K Z) (I.map (QuotientGroup.mk' Z))) = ⊥ := by
      have hmap := map_subtype_fixV_autSub_autQuot hKZ hZK hI
      rw [hIbot] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _
        (I.map (QuotientGroup.mk' Z)).subtype_injective).mp hmap
    refine ⟨?_, ?_⟩
    · exact natSUn_of_autQuot_autSub_top_bot hIstar hCfix hnat
    · rw [hm4']
  · exact (Inputs1719.false_of_isSubnormal_isNaturalO4Plus_of_isSU3 hSU hsn hnatY).elim

theorem seventeen_thirtyfive_one_of_inputs
    (D : Data G) {V₀ V : Subgroup G}
    (h34 : R17_34At D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h869 : F08.R869 D)
    (h117 : C117 D V₀ V) (hSyl : UCK.U3Syl)
    (hNat : K_SU3NaturalModule) (hH1 : K_SU3NaturalH1) (hMin : K_SU3MinDegree)
    (h36 : W4Lem3_6)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D) (hZ : UCK.U3Center)
    (hC : K_U34ThreeCentralizer) (h846 : F08.R846 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (hG2 : Gap17_35_1_nTwo D V₀ V) :
    R17_35_1At D V₀ V :=
  seventeen_thirtyfive_one D h34 hx h61 h127 h1214 h128 h869 h117 hSyl hNat
    (k_SU3NaturalModuleTwo_of_w4 h128) hH1
    (gap17_35CaseTwo_holds D h34 hx h61 h127 h1214 h128 h869 hSyl hMin h36 hSg h82 hZ hC
      h846 h76 h614) hG2

theorem seventeen_thirtyfive_of_inputs
    (D : Data G) {V₀ V : Subgroup G}
    (h34 : R17_34At D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h128 : W4Lem12_8) (h869 : F08.R869 D)
    (h117 : C117 D V₀ V) (hSyl : UCK.U3Syl)
    (h36 : W4Lem3_6)
    (hSg : UC6S846.SigmaStd D) (h82 : F08.R82 D) (hZ : UCK.U3Center)
    (h846 : F08.R846 D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D)
    (hG2 : Gap17_35_1_nTwo D V₀ V) :
    R17_35At D V₀ V := by
  have hH1 : K_SU3NaturalH1 := Inputs1719.k_SU3NaturalH1_holds
  have hMin : Inputs1719.K_SU3MinDegree := Inputs1719.k_SU3MinDegree_holds
  have hNat : K_SU3NaturalModule := Inputs1719.k_SU3NaturalModule_of_w4_holds h128 h36
  have hC : K_U34ThreeCentralizer := k_U34ThreeCentralizer_holds
  have h35 : R17_35_1At D V₀ V :=
    seventeen_thirtyfive_one_of_inputs D h34 hx h61 h127 h1214 h128 h869 h117 hSyl hNat hH1
      hMin h36 hSg h82 hZ hC h846 h76 h614 hG2
  exact ⟨h35, seventeen_thirtyfive_two D h35 h34 h869 h127 hSyl hSg h82 hZ hC h846 h76 h614⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
