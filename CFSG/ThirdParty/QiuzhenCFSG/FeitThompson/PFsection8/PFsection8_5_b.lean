module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_a

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_5_b_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) : Prop :=
  typePDefinitionData M MF U W1 W2 →
    (_root_.commutator U).map U.subtype ≤ Subgroup.centralizer (MF : Set G) ∧
      (U ≠ ⊥ → ¬ U ≤ subgroupCentralizerIn M MF)

/-- Peterfalvi `(8.5)(c)`. -/


private theorem sup_isNilpotent_of_commuting_nilpotent
    {G : Type u} [Group G] [Finite G]
    {A B : Subgroup G}
    (hAB : A ≤ Subgroup.centralizer (B : Set G))
    (hAnil : Group.IsNilpotent A) (hBnil : Group.IsNilpotent B) :
    Group.IsNilpotent (A ⊔ B : Subgroup G) := by
  classical
  let S : Subgroup G := A ⊔ B
  have hAnormB : A ≤ Subgroup.normalizer (B : Set G) :=
    hAB.trans (centralizer_le_normalizer B)
  haveI : (B.subgroupOf S).Normal := by
    simpa [S] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := A) (N := B) hAnormB)
  let f : A × B →* S := {
    toFun x := ⟨(x.1 : G) * (x.2 : G),
      S.mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' x y := by
      apply Subtype.ext
      change
        (((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G))) =
          (((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)))
      have hcomm : (y.1 : G) * (x.2 : G) = (x.2 : G) * (y.1 : G) := by
        exact (Subgroup.mem_centralizer_iff.mp (hAB y.1.2) (x.2 : G) x.2.2).symm
      calc
        ((x.1 : G) * (y.1 : G)) * ((x.2 : G) * (y.2 : G)) =
            (x.1 : G) * ((y.1 : G) * (x.2 : G)) * (y.2 : G) := by
              group
        _ = (x.1 : G) * ((x.2 : G) * (y.1 : G)) * (y.2 : G) := by rw [hcomm]
        _ = ((x.1 : G) * (x.2 : G)) * ((y.1 : G) * (y.2 : G)) := by
              group
  }
  have hf_surj : Function.Surjective f := by
    intro s
    have hAsBs_top : A.subgroupOf S ⊔ B.subgroupOf S = ⊤ := by
      calc
        A.subgroupOf S ⊔ B.subgroupOf S = S.subgroupOf S := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := A) (A' := B) (B := S)
            (by simp [S])
            (by simp [S])
        _ = ⊤ := by simp
    have hs_mem : s ∈ A.subgroupOf S ⊔ B.subgroupOf S := by
      simp [hAsBs_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := A.subgroupOf S) (t := B.subgroupOf S) (x := s)).1
        hs_mem with ⟨aS, haS, bS, hbS, hab⟩
    let a : A := ⟨(aS : G), by simpa [Subgroup.mem_subgroupOf] using haS⟩
    let b : B := ⟨(bS : G), by simpa [Subgroup.mem_subgroupOf] using hbS⟩
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    have hval := congrArg (fun z : S => (z : G)) hab
    simpa [f, a, b, mul_assoc] using hval
  letI : Group.IsNilpotent A := hAnil
  letI : Group.IsNilpotent B := hBnil
  exact Group.nilpotent_of_surjective f hf_surj

private theorem typeP_complement_eq_bot_of_left_eq
    {G : Type u} [Group G] [Finite G]
    {D MF U : Subgroup G}
    (hcomp : section12ComplementIn D MF U)
    (hD : D = MF) :
    U = ⊥ := by
  rcases hcomp with ⟨_hMFD, hUD, _hsup, hdisj⟩
  apply le_antisymm
  · intro u hu
    have huD : u ∈ D := hUD hu
    have huMF : u ∈ MF := by simpa [hD] using huD
    have huInf : u ∈ MF ⊓ U := ⟨huMF, hu⟩
    simpa [hdisj.eq_bot] using huInf
  · exact bot_le

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

private theorem section12ComplementIn_left_isHall_of_right_hall
    {G : Type u} [Group G] [Finite G]
    {M H R : Subgroup G}
    (hcomp : section12ComplementIn M H R)
    (hHnormal : (H.subgroupOf M).Normal)
    (hRHallOf : section16HallSubgroupOf R M) :
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M) := by
  classical
  letI : (H.subgroupOf M).Normal := hHnormal
  have hcomp' : (R.subgroupOf M).IsComplement' (H.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf (M := M) (MF := H) (U := R) hcomp
  rcases hcomp with ⟨hHM, _hRM, _hsup, _hdisj⟩
  rcases hRHallOf with ⟨hRM, hRHall⟩
  refine isHallSubgroup_of (G := M) (π := subgroupPrimeSet H)
    (H := H.subgroupOf M) ?_ ?_
  · intro p hpH
    have hcardH : Nat.card (H.subgroupOf M) = Nat.card H :=
      natCard_subgroupOf_eq H M hHM
    simpa [subgroupPrimeSet, hcardH] using hpH
  · intro p hpH hpidxH
    have hpRcard : p.val ∣ Nat.card (R.subgroupOf M) := by
      simpa [hcomp'.index_eq_card] using hpidxH
    have hpRπ : p ∈ subgroupPrimeSet R :=
      hRHall.p_in_pi_of_p_dvd_card p hpRcard
    have hpHcard : p.val ∣ Nat.card (H.subgroupOf M) := by
      have hcardH : Nat.card (H.subgroupOf M) = Nat.card H :=
        natCard_subgroupOf_eq H M hHM
      simpa [subgroupPrimeSet, hcardH] using hpH
    have hpRidx : p.val ∣ (R.subgroupOf M).index := by
      simpa [hcomp'.symm.index_eq_card] using hpHcard
    exact (hRHall.p_in_pi_of_p_dvd_index p hpRidx) hpRπ

private theorem ambientDerivedSubgroup_le_subgroupCentralizerIn_of_typeP
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2) :
    ambientDerivedSubgroup U ≤ subgroupCentralizerIn U MF := by
  classical
  have hP0 := hP
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD, _hUnil, _hW1normU,
      hcompDU, _hMFnotcyc, hM2le, hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases hMF.1 with ⟨hMFM, hMFNormalM, _hMFnil, _hMFHallM⟩
  have hDleM : D ≤ M := by
    simpa [D] using section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hM_le_norm_MF : M ≤ Subgroup.normalizer (MF : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFM).1 hMFNormalM
  have hMFNormalD : (MF.subgroupOf D).Normal := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hcompDU.1).2
      (hDleM.trans hM_le_norm_MF)
  have hU'leU : ambientDerivedSubgroup U ≤ U :=
    section12_ambientDerivedSubgroup_le (G := G) (E := U)
  have hU'leM2 :
      ambientDerivedSubgroup U ≤ section16SecondDerivedSubgroup M := by
    simpa [D, section16SecondDerivedSubgroup] using
      section12_ambientDerivedSubgroup_mono (G := G) hUleD
  have hU'leFit : ambientDerivedSubgroup U ≤ section8FittingSubgroup M := by
    have hU'leJoin : ambientDerivedSubgroup U ≤ MF ⊔ subgroupCentralizerIn M MF :=
      hU'leM2.trans hM2le
    intro x hx
    rw [← hFitEq]
    exact hU'leJoin hx
  have hU'leJoinCU :
      ambientDerivedSubgroup U ≤ MF ⊔ subgroupCentralizerIn U MF := by
    intro x hx
    simpa [theorem_8_5_a M MF U W1 W2 hP0] using hU'leFit hx
  intro x hx
  have hxU : x ∈ U := hU'leU hx
  have hxJoin : x ∈ MF ⊔ subgroupCentralizerIn U MF := hU'leJoinCU hx
  let CU : Subgroup G := subgroupCentralizerIn U MF
  have hCUleD : CU ≤ D := by
    intro y hy
    exact hcompDU.2.1 hy.1
  let xD : D := ⟨x, hcompDU.2.1 hxU⟩
  have hxJoinD : xD ∈ MF.subgroupOf D ⊔ CU.subgroupOf D := by
    have hxSub : xD ∈ (MF ⊔ CU).subgroupOf D := by
      simpa [xD, CU, Subgroup.mem_subgroupOf] using hxJoin
    have hsub_eq :
        (MF ⊔ CU).subgroupOf D = MF.subgroupOf D ⊔ CU.subgroupOf D :=
      Subgroup.subgroupOf_sup (A := MF) (A' := CU) (B := D) hcompDU.1 hCUleD
    simpa [hsub_eq] using hxSub
  letI : (MF.subgroupOf D).Normal := hMFNormalD
  rcases (Subgroup.mem_sup_of_normal_left
      (s := MF.subgroupOf D) (t := CU.subgroupOf D) (x := xD)).1 hxJoinD with
    ⟨mD, hmMFsub, cD, hcCUsub, hmulD⟩
  let m : G := mD
  let c : G := cD
  have hmMF : m ∈ MF := by
    simpa [m, Subgroup.mem_subgroupOf] using hmMFsub
  have hcCU : c ∈ CU := by
    simpa [c, Subgroup.mem_subgroupOf] using hcCUsub
  have hcU : c ∈ U := hcCU.1
  have hmul : m * c = x := by
    simpa [m, c, xD] using congrArg (fun z : D => (z : G)) hmulD
  have hmU : m ∈ U := by
    have hx_eq : m = x * c⁻¹ := by
      rw [← hmul]
      group
    rw [hx_eq]
    exact U.mul_mem hxU (U.inv_mem hcU)
  have hm_bot : m ∈ (⊥ : Subgroup G) := by
    have hmInf : m ∈ MF ⊓ U := ⟨hmMF, hmU⟩
    simpa [hcompDU.2.2.2.eq_bot] using hmInf
  have hm_one : m = 1 := by simpa using hm_bot
  have hx_eq_c : x = c := by
    rw [← hmul, hm_one, one_mul]
  rw [hx_eq_c]
  exact hcCU

private theorem typeP_ambientDerived_nilpotentNormalHallIn_of_le_centralizer
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G}
    (hP : typePDefinitionData M MF U W1 W2)
    (hUcent : U ≤ subgroupCentralizerIn M MF) :
    section16NilpotentNormalHallIn (ambientDerivedSubgroup M) M := by
  classical
  rcases hP with
    ⟨hMF, _hW1cyc, _hW1ne, hW1hall, hcompMW1, _hUleD, hUnil, _hW1normU,
      hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
      _hcentW1, _hnormX⟩
  rcases hMF.1 with ⟨_hMFM, _hMFnormM, hMFnil, _hMFHallM⟩
  let D : Subgroup G := ambientDerivedSubgroup M
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (G := G) (E := M)
  have hDnormal : (D.subgroupOf M).Normal := by
    simpa [D] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  have hDnil : Group.IsNilpotent D := by
    have hUcentMF : U ≤ Subgroup.centralizer (MF : Set G) := by
      intro u hu
      exact (hUcent hu).2
    have hsupNil : Group.IsNilpotent (U ⊔ MF : Subgroup G) :=
      sup_isNilpotent_of_commuting_nilpotent hUcentMF hUnil hMFnil
    have hUD_eq_D : U ⊔ MF = D := by
      change U ⊔ MF = ambientDerivedSubgroup M
      rw [hcompDU.2.2.1, sup_comm]
    rw [← hUD_eq_D]
    exact hsupNil
  have hDHall : IsHallSubgroup (subgroupPrimeSet D) (D.subgroupOf M) :=
    section12ComplementIn_left_isHall_of_right_hall
      (M := M) (H := D) (R := W1)
      (by simpa [D] using hcompMW1) hDnormal hW1hall
  exact ⟨by simpa [D] using hDleM, hDnormal, hDnil, hDHall⟩

public theorem theorem_8_5_b
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 : Subgroup G) :
    theorem_8_5_b_statement M MF U W1 W2 := by
  classical
  intro hP
  constructor
  · rw [Subgroup.map_subtype_commutator,
      ← section12_ambientDerivedSubgroup_eq_commutator (G := G) (H := U)]
    intro x hx
    have hxCU := (ambientDerivedSubgroup_le_subgroupCentralizerIn_of_typeP
      (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP) hx
    exact hxCU.2
  · intro hUne hUcent
    have hDHall : section16NilpotentNormalHallIn (ambientDerivedSubgroup M) M :=
      typeP_ambientDerived_nilpotentNormalHallIn_of_le_centralizer
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2) hP hUcent
    rcases hP with
      ⟨hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil, _hW1normU,
        hcompDU, _hMFnotcyc, _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
        _hcentW1, _hnormX⟩
    have hDLeMF : ambientDerivedSubgroup M ≤ MF :=
      hMF.2 (ambientDerivedSubgroup M) hDHall
    have hDeqMF : ambientDerivedSubgroup M = MF := by
      apply le_antisymm
      · exact hDLeMF
      · exact hcompDU.1
    exact hUne (typeP_complement_eq_bot_of_left_eq hcompDU hDeqMF)

end CFSG.Section8
