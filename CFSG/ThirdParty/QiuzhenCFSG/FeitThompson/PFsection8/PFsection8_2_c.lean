module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_5_to_10

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_2_c_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G)
    (θ : Section1.ClassFunction MF) : Prop :=
  typeFData M MF U U1 U0 →
    Section1.IsIrreducibleCharacterOnGroup θ →
      θ ≠ Section1.principalCharacter MF →
        inertiaIntersectionInComplement M MF U U1 θ


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

private theorem typeFData_complement_coprime_card
    {G : Type u} [Group G] [Finite G]
    {M MF U : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hcomp : section12ComplementIn M MF U) :
    Nat.Coprime (Nat.card U) (Nat.card MF) := by
  rcases hMF with ⟨⟨hMFM, hMFNormal, _hMFNil, hMFHall⟩, _hmax⟩
  letI : (MF.subgroupOf M).Normal := hMFNormal
  have hcomp' : (U.subgroupOf M).IsComplement' (MF.subgroupOf M) :=
    section12ComplementIn_isComplement'_subgroupOf (M := M) (MF := MF) (U := U) hcomp
  have hcop : Nat.Coprime (Nat.card (MF.subgroupOf M)) (MF.subgroupOf M).index :=
    hMFHall.card_coprime_index
  have hidx : (MF.subgroupOf M).index = Nat.card (U.subgroupOf M) :=
    hcomp'.index_eq_card
  have hcardMF : Nat.card (MF.subgroupOf M) = Nat.card MF :=
    natCard_subgroupOf_eq MF M hMFM
  have hcardU : Nat.card (U.subgroupOf M) = Nat.card U :=
    natCard_subgroupOf_eq U M hcomp.2.1
  simpa [hcardMF, hidx, hcardU] using hcop.symm

private theorem isIrreducibleCharacterOnGroup_classFunctionOnSubgroupOf
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G} (hMFM : MF ≤ M)
    {θ : Section1.ClassFunction MF}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.IsIrreducibleCharacterOnGroup (classFunctionOnSubgroupOf M MF θ) := by
  rcases hθ with ⟨n, ρ, hρirr, hθeq⟩
  let e : (MF.subgroupOf M) ≃* MF := Subgroup.subgroupOfEquivOfLe hMFM
  let ρsub : Representation ℂ (MF.subgroupOf M) (Fin n → ℂ) := ρ.comp e.toMonoidHom
  refine ⟨n, ρsub, ?_, ?_⟩
  · exact Theory.Representation.RepEquiv.irreducible_of_group_iso
      (ρ := ρ) (σ := ρsub) e.symm (by
        intro g v
        simp [ρsub, e]) hρirr
  · ext h
    rw [hθeq]
    rfl

private theorem classFunctionOnSubgroupOf_ne_principal
    {G : Type u} [Group G] [Finite G]
    {M MF : Subgroup G} (hMFM : MF ≤ M)
    {θ : Section1.ClassFunction MF}
    (hθne : θ ≠ Section1.principalCharacter MF) :
    classFunctionOnSubgroupOf M MF θ ≠
      Section1.principalCharacter (MF.subgroupOf M) := by
  intro hθM
  apply hθne
  ext a
  let aM : MF.subgroupOf M := ⟨⟨a, hMFM a.2⟩, a.2⟩
  have h := congrFun hθM aM
  simpa [aM, classFunctionOnSubgroupOf, Section1.principalCharacter] using h

private theorem centralizerIn_subgroupOf_subsingleton_of_not_mem_U1
    {G : Type u} [Group G] [Finite G]
    {M MF U U1 : Subgroup G}
    (hcent : ∀ x : G, x ∈ MF → x ≠ 1 → elementCentralizerIn U x ≤ U1)
    {m : M}
    (hmU : (m : G) ∈ U)
    (hmnotU1 : (m : G) ∉ U1) :
    Subsingleton (Section2.centralizerIn (MF.subgroupOf M) m) := by
  refine ⟨fun c d => ?_⟩
  have hc_one : c = 1 := by
    apply Subtype.ext
    by_cases hcG : ((c : M) : G) = 1
    · exact Subtype.ext hcG
    · exfalso
      have hcMFsub : (c : M) ∈ MF.subgroupOf M := (Subgroup.mem_inf.mp c.property).1
      have hcMF : ((c : M) : G) ∈ MF := by
        simpa [Subgroup.mem_subgroupOf] using hcMFsub
      have hcCent : (c : M) ∈ Section2.elementCentralizer m :=
        (Subgroup.mem_inf.mp c.property).2
      have hcommM : m * (c : M) = (c : M) * m := by
        unfold Section2.elementCentralizer at hcCent
        rw [Subgroup.mem_centralizer_iff] at hcCent
        exact hcCent m (by simp)
      have hcommG : (m : G) * ((c : M) : G) = ((c : M) : G) * (m : G) :=
        congrArg M.subtype hcommM
      have hmCentral : (m : G) ∈ elementCentralizerIn U ((c : M) : G) := by
        refine Subgroup.mem_inf.mpr ⟨hmU, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hcommG.symm
      exact hmnotU1 (hcent ((c : M) : G) hcMF hcG hmCentral)
  have hd_one : d = 1 := by
    apply Subtype.ext
    by_cases hdG : ((d : M) : G) = 1
    · exact Subtype.ext hdG
    · exfalso
      have hdMFsub : (d : M) ∈ MF.subgroupOf M := (Subgroup.mem_inf.mp d.property).1
      have hdMF : ((d : M) : G) ∈ MF := by
        simpa [Subgroup.mem_subgroupOf] using hdMFsub
      have hdCent : (d : M) ∈ Section2.elementCentralizer m :=
        (Subgroup.mem_inf.mp d.property).2
      have hcommM : m * (d : M) = (d : M) * m := by
        unfold Section2.elementCentralizer at hdCent
        rw [Subgroup.mem_centralizer_iff] at hdCent
        exact hdCent m (by simp)
      have hcommG : (m : G) * ((d : M) : G) = ((d : M) : G) * (m : G) :=
        congrArg M.subtype hcommM
      have hmCentral : (m : G) ∈ elementCentralizerIn U ((d : M) : G) := by
        refine Subgroup.mem_inf.mpr ⟨hmU, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact hcommG.symm
      exact hmnotU1 (hcent ((d : M) : G) hdMF hdG hmCentral)
  rw [hc_one, hd_one]

public theorem theorem_8_2_c
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G)
    (θ : Section1.ClassFunction MF) :
    theorem_8_2_c_statement M MF U U1 U0 θ := by
  intro hF hθirr hθne hMFNormal
  letI : (MF.subgroupOf M).Normal := hMFNormal
  change
    ((Section1.inertiaSubgroup (MF.subgroupOf M)
      (classFunctionOnSubgroupOf M MF θ)).map M.subtype ⊓ U) ≤ U1
  intro g hg
  rcases hF with
    ⟨hsolvM, hoddM, hMF, hMFne, hMFM, hUne, hcomp, hU1leU, hU1comm,
      hU1norm, hcent, hU0leU, hexpU0U, hFrob⟩
  by_contra hgnotU1
  have hgMap :
      g ∈ Subgroup.map M.subtype
        (Section1.inertiaSubgroup (MF.subgroupOf M) (classFunctionOnSubgroupOf M MF θ)) :=
    (Subgroup.mem_inf.mp hg).1
  have hgU : g ∈ U := (Subgroup.mem_inf.mp hg).2
  rcases hgMap with ⟨m, hmI, hmg⟩
  have hmG : (m : G) = g := hmg
  have hmU : (m : G) ∈ U := by simpa [hmG] using hgU
  have hmnotU1 : (m : G) ∉ U1 := by simpa [hmG] using hgnotU1
  have hcopUMF : Nat.Coprime (Nat.card U) (Nat.card MF) :=
    typeFData_complement_coprime_card (M := M) (MF := MF) (U := U) hMF hcomp
  have hcopOrderMF :
      Nat.Coprime (orderOf m) (Nat.card (MF.subgroupOf M)) := by
    have horder_dvd_U : orderOf (m : G) ∣ Nat.card U :=
      Subgroup.orderOf_dvd_natCard U hmU
    have hcardMF : Nat.card (MF.subgroupOf M) = Nat.card MF :=
      natCard_subgroupOf_eq MF M hcomp.1
    have hcop : Nat.Coprime (orderOf (m : G)) (Nat.card MF) :=
      Nat.Coprime.of_dvd_left horder_dvd_U hcopUMF
    simpa [hcardMF] using hcop
  have hcentSubsingleton :
      Subsingleton (Section2.centralizerIn (MF.subgroupOf M) m) :=
    centralizerIn_subgroupOf_subsingleton_of_not_mem_U1
      (M := M) (MF := MF) (U := U) (U1 := U1) hcent hmU hmnotU1
  have hcentCardLe :
      Nat.card (Section2.centralizerIn (MF.subgroupOf M) m) ≤ 1 := by
    have hcard :=
      (Finite.card_le_one_iff_subsingleton
        (α := Section2.centralizerIn (MF.subgroupOf M) m)).2 hcentSubsingleton
    exact hcard
  let θM : Section1.ClassFunction (MF.subgroupOf M) :=
    classFunctionOnSubgroupOf M MF θ
  let fixedSet : Set (Section1.ClassFunction (MF.subgroupOf M)) :=
    {X | Section1.IsIrreducibleCharacterOnGroup X ∧
      Section1.conjugateOnNormal (MF.subgroupOf M) X m = X}
  have hfixed_le_cent :
      Nat.card fixedSet ≤ Nat.card (Section2.centralizerIn (MF.subgroupOf M) m) := by
    simpa [fixedSet] using
      Section4Scratch.fixed_irreducible_card_le_centralizerIn_of_coprime_pf45
        (K := MF.subgroupOf M) (g := (m : M)) hcopOrderMF
  have hfixed_le_one : Nat.card fixedSet ≤ 1 :=
    le_trans hfixed_le_cent hcentCardLe
  haveI : Subsingleton fixedSet :=
    Section4Scratch.fixed_irreducible_subsingleton_of_card_le_one_pf45
      (K := MF.subgroupOf M) (g := (m : M)) (by simpa [fixedSet] using hfixed_le_one)
  have hθM_irr : Section1.IsIrreducibleCharacterOnGroup θM :=
    isIrreducibleCharacterOnGroup_classFunctionOnSubgroupOf
      (M := M) (MF := MF) hcomp.1 hθirr
  have hθM_fix : Section1.conjugateOnNormal (MF.subgroupOf M) θM m = θM := by
    change Section1.conjugateOnNormal (MF.subgroupOf M)
      (classFunctionOnSubgroupOf M MF θ) m = classFunctionOnSubgroupOf M MF θ
    change Section1.conjugateOnNormal (MF.subgroupOf M)
      (classFunctionOnSubgroupOf M MF θ) m = classFunctionOnSubgroupOf M MF θ at hmI
    exact hmI
  have hprincipal_fix :
      Section1.conjugateOnNormal (MF.subgroupOf M)
          (Section1.principalCharacter (MF.subgroupOf M)) m =
        Section1.principalCharacter (MF.subgroupOf M) := by
    ext a
    simp [Section1.conjugateOnNormal, Section1.principalCharacter]
  let θM_fixed : fixedSet := ⟨θM, hθM_irr, hθM_fix⟩
  let principal_fixed : fixedSet :=
    ⟨Section1.principalCharacter (MF.subgroupOf M),
      Section3.principalCharacter_isIrreducibleCharacterOnGroup,
      hprincipal_fix⟩
  have hθM_principal : θM = Section1.principalCharacter (MF.subgroupOf M) := by
    exact congrArg Subtype.val (Subsingleton.elim θM_fixed principal_fixed)
  have hθM_ne_principal :
      θM ≠ Section1.principalCharacter (MF.subgroupOf M) :=
    classFunctionOnSubgroupOf_ne_principal (M := M) (MF := MF) hcomp.1 hθne
  exact hθM_ne_principal hθM_principal

end CFSG.Section8
