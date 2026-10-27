module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_5_a_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) : Prop :=
  typePDefinitionData M MF U W1 W2 →
    section8FittingSubgroup M = MF ⊔ subgroupCentralizerIn U MF

/-- Peterfalvi `(8.5)(b)`. -/


private theorem section12ComplementIn_isComplement'_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hcomp : section12ComplementIn M MF U)
    [hMFNormal : (MF.subgroupOf M).Normal] :
    (U.subgroupOf M).IsComplement' (MF.subgroupOf M) := by
  rcases hcomp with ⟨hMFM, hUM, hsup, hdisj⟩
  have hsup_local : U.subgroupOf M ⊔ MF.subgroupOf M = ⊤ := by
    calc
      U.subgroupOf M ⊔ MF.subgroupOf M = (U ⊔ MF).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := U) (A' := MF) (B := M) hUM hMFM
      _ = ⊤ := by
        rw [sup_comm, hsup]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxU hxMF
    apply Subtype.ext
    exact hdisj.le_bot ⟨by simpa [Subgroup.mem_subgroupOf] using hxMF,
      by simpa [Subgroup.mem_subgroupOf] using hxU⟩
  · simpa [hsup_local] using
      (Subgroup.mul_normal (U.subgroupOf M) (MF.subgroupOf M)).symm

private theorem typeP_mf_hallSubgroup_in_intermediate
    {G : Type u} [Group G] [Finite G]
    {M MF D : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hMFleD : MF ≤ D) (hDleM : D ≤ M) :
    IsHallSubgroup (subgroupPrimeSet MF) (MF.subgroupOf D) := by
  classical
  rcases hMF.1 with ⟨hMFM, _hMFnormM, _hMFnil, hMFHallM⟩
  let Dsub : Subgroup M := D.subgroupOf M
  have hMFcardM : Nat.card (MF.subgroupOf M) = Nat.card MF :=
    natCard_subgroupOf_eq MF M hMFM
  have hMFcardD : Nat.card (MF.subgroupOf D) = Nat.card MF :=
    natCard_subgroupOf_eq MF D hMFleD
  have hMFsub_le_Dsub : MF.subgroupOf M ≤ Dsub := by
    intro x hx
    exact hMFleD hx
  refine isHallSubgroup_of (G := D) (π := subgroupPrimeSet MF)
    (H := MF.subgroupOf D) ?_ ?_
  · intro p hp
    exact hMFHallM.p_in_pi_of_p_dvd_card p
      (by simpa [hMFcardM, hMFcardD] using hp)
  · intro p hpπ hpidx
    have hrel_eq :
        (MF.subgroupOf D).index = (MF.subgroupOf M).relIndex Dsub := by
      have hsub :=
        Subgroup.relIndex_subgroupOf (H := MF) (K := D) (L := M) hDleM
      simpa [Dsub, Subgroup.relIndex] using hsub.symm
    have hidx_dvd :
        (MF.subgroupOf D).index ∣ (MF.subgroupOf M).index := by
      have hrel_dvd :
          (MF.subgroupOf M).relIndex Dsub ∣ (MF.subgroupOf M).index :=
        Subgroup.relIndex_dvd_index_of_le hMFsub_le_Dsub
      simpa [hrel_eq] using hrel_dvd
    exact (hMFHallM.p_in_pi_of_p_dvd_index p (hpidx.trans hidx_dvd)) hpπ

private theorem typeP_complement_coprime_card
    {G : Type u} [Group G] [Finite G]
    {M MF D U : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hDleM : D ≤ M)
    (hcomp : section12ComplementIn D MF U) :
    Nat.Coprime (Nat.card U) (Nat.card MF) := by
  classical
  rcases hMF.1 with ⟨hMFM, hMFNormalM, _hMFNil, _hMFHallM⟩
  have hMFNormalD : (MF.subgroupOf D).Normal := by
    have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFNormalM
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hcomp.1).2 (hDleM.trans hM_le_norm_MF)
  letI : (MF.subgroupOf D).Normal := hMFNormalD
  have hcomp' : (U.subgroupOf D).IsComplement' (MF.subgroupOf D) :=
    section12ComplementIn_isComplement'_subgroupOf (M := D) (MF := MF) (U := U) hcomp
  have hMFHallD : IsHallSubgroup (subgroupPrimeSet MF) (MF.subgroupOf D) :=
    typeP_mf_hallSubgroup_in_intermediate (M := M) (MF := MF) (D := D) hMF hcomp.1 hDleM
  have hcop : Nat.Coprime (Nat.card (MF.subgroupOf D)) (MF.subgroupOf D).index :=
    hMFHallD.card_coprime_index
  have hidx : (MF.subgroupOf D).index = Nat.card (U.subgroupOf D) :=
    hcomp'.index_eq_card
  have hcardMF : Nat.card (MF.subgroupOf D) = Nat.card MF :=
    natCard_subgroupOf_eq MF D hcomp.1
  have hcardU : Nat.card (U.subgroupOf D) = Nat.card U :=
    natCard_subgroupOf_eq U D hcomp.2.1
  simpa [hcardMF, hidx, hcardU] using hcop.symm

private theorem subgroupCentralizerIn_subgroupOf_normal
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G}
    (hMFM : MF ≤ M) [hMFnormM : (MF.subgroupOf M).Normal] :
    ((subgroupCentralizerIn M MF).subgroupOf M).Normal := by
  classical
  have hCsub_eq :
      (subgroupCentralizerIn M MF).subgroupOf M =
        Subgroup.centralizer ((MF.subgroupOf M : Subgroup M) : Set M) := by
    rw [← subgroupCentralizerIn_subgroupOf_eq (S := M) (H := M) (R := MF) hMFM]
    ext x
    simp [subgroupCentralizerIn]
  rw [hCsub_eq]
  infer_instance

private theorem subgroupCentralizerIn_le_sup_centralizerIn_complement
    {G : Type u} [Group G] [Finite G]
    {M MF D U : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hDleM : D ≤ M)
    (hcomp : section12ComplementIn D MF U)
    (hFitEq : MF ⊔ subgroupCentralizerIn M MF = section8FittingSubgroup M)
    (hFitLeD : section8FittingSubgroup M ≤ D) :
    subgroupCentralizerIn M MF ≤ MF ⊔ subgroupCentralizerIn U MF := by
  classical
  rcases hMF.1 with ⟨hMFM, hMFNormalM, _hMFNil, _hMFHallM⟩
  have hUM : U ≤ M := hcomp.2.1.trans hDleM
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFNormalM
  have hMFNormalD : (MF.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcomp.1).2 (hDleM.trans hM_le_norm_MF)
  have hcopUMF : Nat.Coprime (Nat.card U) (Nat.card MF) :=
    typeP_complement_coprime_card (M := M) (MF := MF) (D := D) (U := U)
      hMF hDleM hcomp
  have hCsubNormal : ((subgroupCentralizerIn M MF).subgroupOf M).Normal := by
    letI : (MF.subgroupOf M).Normal := hMFNormalM
    exact subgroupCentralizerIn_subgroupOf_normal (M := M) (MF := MF) hMFM
  intro g hgC
  let C : Subgroup G := subgroupCentralizerIn M MF
  have hgD : g ∈ D := by
    apply hFitLeD
    rw [← hFitEq]
    exact Subgroup.mem_sup_right hgC
  let gD : D := ⟨g, hgD⟩
  have hsup_local : MF.subgroupOf D ⊔ U.subgroupOf D = ⊤ := by
    calc
      MF.subgroupOf D ⊔ U.subgroupOf D = (MF ⊔ U).subgroupOf D := by
        symm
        exact Subgroup.subgroupOf_sup (A := MF) (A' := U) (B := D) hcomp.1 hcomp.2.1
      _ = ⊤ := by
        rw [hcomp.2.2.1]
        simp
  have hgSupD : gD ∈ MF.subgroupOf D ⊔ U.subgroupOf D := by
    rw [hsup_local]
    exact Subgroup.mem_top gD
  letI : (MF.subgroupOf D).Normal := hMFNormalD
  rcases (Subgroup.mem_sup_of_normal_left (s := MF.subgroupOf D) (t := U.subgroupOf D)
      (x := gD)).1 hgSupD with ⟨hD, hhMFsubD, uD, huUsubD, hmulD⟩
  let h : G := hD
  let u : G := uD
  have hhMF : h ∈ MF := by
    simpa [h, Subgroup.mem_subgroupOf] using hhMFsubD
  have huU : u ∈ U := by
    simpa [u, Subgroup.mem_subgroupOf] using huUsubD
  have hmul : h * u = g := by
    simpa [h, u, gD] using congrArg Subtype.val hmulD
  let Csub : Subgroup M := C.subgroupOf M
  let q : M →* M ⧸ Csub := QuotientGroup.mk' Csub
  haveI : Csub.Normal := by simpa [C, Csub] using hCsubNormal
  let hM : M := ⟨h, hMFM hhMF⟩
  let uM : M := ⟨u, hUM huU⟩
  let gM : M := ⟨g, hgC.1⟩
  have hmulM : hM * uM = gM := by
    apply Subtype.ext
    exact hmul
  have hgM_one : q gM = 1 := by
    exact (QuotientGroup.eq_one_iff (N := Csub) gM).mpr (by
      simpa [C, Csub, Subgroup.mem_subgroupOf] using hgC)
  have hq_mul : q hM * q uM = 1 := by
    rw [← map_mul, hmulM]
    exact hgM_one
  have hq_h_eq_inv : q hM = (q uM)⁻¹ := eq_inv_of_mul_eq_one_left hq_mul
  let Usub : Subgroup M := U.subgroupOf M
  let usub : Usub := ⟨uM, by simpa [Usub, uM, Subgroup.mem_subgroupOf] using huU⟩
  have horderU : orderOf (q uM) ∣ Nat.card U := by
    have hmap : orderOf ((q.comp Usub.subtype) usub) ∣ orderOf usub :=
      orderOf_map_dvd (q.comp Usub.subtype) usub
    have hsub : orderOf usub ∣ Nat.card Usub := orderOf_dvd_natCard usub
    have hcard : Nat.card Usub = Nat.card U := natCard_subgroupOf_eq U M hUM
    simpa [Usub, usub, uM, hcard] using hmap.trans hsub
  let MFsub : Subgroup M := MF.subgroupOf M
  let hsub : MFsub := ⟨hM, by simpa [MFsub, hM, Subgroup.mem_subgroupOf] using hhMF⟩
  have horderH : orderOf (q hM) ∣ Nat.card MF := by
    have hmap : orderOf ((q.comp MFsub.subtype) hsub) ∣ orderOf hsub :=
      orderOf_map_dvd (q.comp MFsub.subtype) hsub
    have hsubdiv : orderOf hsub ∣ Nat.card MFsub := orderOf_dvd_natCard hsub
    have hcard : Nat.card MFsub = Nat.card MF := natCard_subgroupOf_eq MF M hMFM
    simpa [MFsub, hsub, hM, hcard] using hmap.trans hsubdiv
  have horderH_eq : orderOf (q uM) = orderOf (q hM) := by
    rw [hq_h_eq_inv, orderOf_inv]
  have horderH' : orderOf (q uM) ∣ Nat.card MF := by
    simpa [horderH_eq] using horderH
  have horder_one : orderOf (q uM) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopUMF horderU horderH'
  have hqu_one : q uM = 1 := orderOf_eq_one_iff.mp horder_one
  have huCsub : uM ∈ Csub :=
    (QuotientGroup.eq_one_iff (N := Csub) uM).mp hqu_one
  have huC : u ∈ subgroupCentralizerIn M MF := by
    simpa [C, Csub, uM, Subgroup.mem_subgroupOf] using huCsub
  have huCU : u ∈ subgroupCentralizerIn U MF := ⟨huU, huC.2⟩
  rw [← hmul]
  exact Subgroup.mul_mem_sup hhMF huCU

public theorem theorem_8_5_a
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) :
    theorem_8_5_a_statement M MF U W1 W2 := by
  intro hP
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
      hcompDU, _hMFnotcyc, _hM2le, hFitEq, hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hCM_le : subgroupCentralizerIn M MF ≤ MF ⊔ subgroupCentralizerIn U MF :=
    subgroupCentralizerIn_le_sup_centralizerIn_complement
      (M := M) (MF := MF) (D := ambientDerivedSubgroup M) (U := U)
      hMF hDleM hcompDU hFitEq hFitLeD
  apply le_antisymm
  · rw [← hFitEq]
    exact sup_le le_sup_left hCM_le
  · rw [← hFitEq]
    have hCU_le_CM : subgroupCentralizerIn U MF ≤ subgroupCentralizerIn M MF := by
      intro x hx
      exact ⟨hcompDU.2.1.trans hDleM hx.1, hx.2⟩
    exact sup_le le_sup_left (hCU_le_CM.trans le_sup_right)

end CFSG.Section8
