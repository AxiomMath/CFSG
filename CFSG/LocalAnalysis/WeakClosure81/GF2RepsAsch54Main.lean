module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Disp
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Psi
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Red
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Shape
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Rank
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Quot
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Top
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54AS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

private theorem isSolvable_autQ_quot {G : Type} [Group G] [Finite G] {X T J : Subgroup G}
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced G X T)
    (hJ : CFSG.Quasithin.E2.E22N.E111R.IsComp X J)
    [((innAutOf ↥J).subgroupOf (autQ T J)).Normal] :
    Group.IsSolvable (↥(autQ T J) ⧸ (innAutOf ↥J).subgroupOf (autQ T J)) := by
  set Lh := (innAutOf ↥J).subgroupOf (autQ T J)
  set Th := (autT T J).subgroupOf (autQ T J)
  have hsup : Lh ⊔ Th = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (innAutOf_le_autQ T J) (autT_le_autQ T J),
      innAutOf_sup_autT, Subgroup.subgroupOf_self]
  have hTs : Group.IsSolvable ↥Th := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (isSylowIn_autT_subgroupOf hR hJ).isPGroup
    haveI : Group.IsNilpotent ↥Th := this.isNilpotent
    infer_instance
  let f : ↥Th →* ↥(autQ T J) ⧸ Lh := (QuotientGroup.mk' Lh).comp Th.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Lh q
    have ha : a ∈ Lh ⊔ Th := by rw [hsup]; exact Subgroup.mem_top a
    obtain ⟨l, hl, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
    refine ⟨⟨t, ht⟩, ?_⟩
    change QuotientGroup.mk' Lh t = QuotientGroup.mk' Lh (l * t)
    have hl1 : QuotientGroup.mk' Lh l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [map_mul, hl1, one_mul]
  exact Group.isSolvable_of_surjective (f := f) hf


theorem asch5_4_of_inputs (hC2 : Asch54Chev2) (hAl : Asch54Alt) (hSp : Asch54Spor)
    (hCO : Asch54ChevOdd) (hA : Asch80ThmA54) (hON : Asch54ONGen) (h22 : Asch2_2Simple) :
    Asch5_4 := by
  intro G _ _ H T hK hT hTH hno
  have hP0 : ∀ (L : Type) [Group L] [Finite L], IsCalL0 L → ∃ a b : L, a * b ≠ b * a :=
    fun L _ _ hL => (isCalL0_nonabelian_not_sectionalTwoRankLE L hL).1
  by_cases h1 : H = lGen IsCalL0 H T
  · exact Or.inl h1
  by_cases hs : Group.IsSolvable ↥H
  · haveI := hs
    exact Or.inr (Or.inr ⟨calNIn_eq_lGen_of_isSolvable' hP0 hTH h1, Or.inl hs⟩)
  have hS : IsSylowIn 2 (T.subgroupOf H) ⊤ := isSylowIn_subgroupOf_top hT
  have hHtop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hnoK : ¬ HasCompFactor (⊤ : Subgroup ↥H) IsCalL0 := fun h => hno (by
    have := (hasCompFactor_map_subtype_iff (⊤ : Subgroup ↥H)).2 h
    rwa [hHtop] at this)
  have hneK : lGen IsCalL0 ⊤ (T.subgroupOf H) ≠ ⊤ := fun h => h1 (by
    rw [lGen_eq_map_lGen_subgroupOf hTH.le, h, hHtop])
  have hRs : Group.IsSolvable ↥(CFSG.solvableRadical ↥H) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  set R := CFSG.solvableRadical ↥H with hRdef
  set π := QuotientGroup.mk' R with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hker : Group.IsSolvable ↥π.ker := by rw [hπdef, QuotientGroup.ker_mk']; exact hRs
  have hrad : CFSG.solvableRadical (↥H ⧸ R) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient
  have hYns : ¬ Group.IsSolvable (↥H ⧸ R) := fun _ => hs (Group.isSolvable_of_subgroup_quotient R)
  obtain ⟨E, hE, hES⟩ :=
    exists_isComponent_comap_sup_eq_top hP0 hS hnoK hneK π hπ hker hrad hYns
  set Sb := (T.subgroupOf H).map π with hSbdef
  have hSb : IsSylowIn 2 Sb ⊤ := isSylowIn_map_top hπ hS
  have hESb : E ⊔ Sb = ⊤ := by
    have h2 := congrArg (Subgroup.map π) hES
    rwa [Subgroup.map_sup, Subgroup.map_comap_eq_self_of_surjective hπ,
      Subgroup.map_top_of_surjective π hπ] at h2
  obtain ⟨hR, hJ⟩ := e111Reduced_normalClosure hrad hE hSb hESb
  obtain ⟨hEs, hEnab⟩ := isSimpleGroup_of_isComponent hrad hE
  have hZ : center ↥E = ⊥ := center_eq_bot_of_isComp hJ
  have hAinn : innAutOf ↥E ≤ autQ Sb E := innAutOf_le_autQ Sb E
  haveI hLn : ((innAutOf ↥E).subgroupOf (autQ Sb E)).Normal :=
    Subgroup.Normal.subgroupOf (innAutOf_normal ↥E) _
  let eL : ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) ≃* ↥E :=
    (Subgroup.subgroupOfEquivOfLe hAinn).trans (innAutOfEquiv hJ)
  haveI := hEs
  have hLs : IsSimpleGroup ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) := eL.isSimpleGroup
  have hLnab : ∃ a b : ↥((innAutOf ↥E).subgroupOf (autQ Sb E)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hEnab
    refine ⟨eL.symm a, eL.symm b, fun h => hab ?_⟩
    simpa using congrArg eL h
  have hLC : centralizer (((innAutOf ↥E).subgroupOf (autQ Sb E) :
      Subgroup ↥(autQ Sb E)) : Set ↥(autQ Sb E)) = ⊥ :=
    centralizer_innAutOf_subgroupOf_eq_bot hZ hAinn
  have hL0 : ¬ IsCalL0 ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) := by
    intro h
    apply hnoK
    have hcfY : E1.IsCompositionFactor (↥H ⧸ R) ↥((innAutOf ↥E).subgroupOf (autQ Sb E)) :=
      CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection hE.2 hLs
        eL.symm.toMonoidHom eL.symm.surjective
    exact ⟨_, inferInstance, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      Subgroup.topEquiv).2
        (CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective π hπ hcfY), h⟩
  have hKY : CFSG.Open.IsKGroup (↥H ⧸ R) := hK.quotient R
  have hKA : CFSG.Open.IsKGroup ↥(autQ Sb E) := isKGroup_autQ hKY Sb E
  have hTh : IsSylowIn 2 ((autT Sb E).subgroupOf (autQ Sb E)) ⊤ := isSylowIn_autT_subgroupOf hR hJ
  rcases asch54_almostSimple hC2 hAl hSp hCO hA hON hKA hLn hLs hLnab hLC hL0 hTh with
    hgen | ⟨p, hp, hp2, h3, h1', hON'⟩ | ⟨M, hM, hMax, hM0, hsh⟩
  ·
    exfalso
    have hYnt : Nontrivial (↥H ⧸ R) := by
      by_contra hnt
      rw [not_nontrivial_iff_subsingleton] at hnt
      exact hYns inferInstance
    exact hneK (lGen_eq_top_of_map hP0 π hπ hker _ hYnt (lGen_eq_top_of_autQ hR hJ hP0 hgen))
  ·
    right; left
    refine ⟨p, hp, hp2, ?_, ?_⟩
    ·
      refine three_lt_pRank_perfectCore_of_section h22 hK (preG_le π E) hEnab (toE π E)
        (toE_surjective hπ E) hp hp2 ?_ ?_
      · have hle := perfectCore_top_le_of_isSolvable_quot
          ((innAutOf ↥E).subgroupOf (autQ Sb E)) (isSolvable_autQ_quot hR hJ)
        have h4 := lt_of_lt_of_le h3 (CFSG.SectionRank.pRank_mono hp.one_lt hle)
        have h5 := pRank_map_subtype (H := (innAutOf ↥E).subgroupOf (autQ Sb E))
          (⊤ : Subgroup ↥((innAutOf ↥E).subgroupOf (autQ Sb E))) p
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h5
        rw [h5, CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eL] at h4
        exact h4
      · rintro - ⟨e⟩
        exact hON' ⟨eL.trans e⟩
    ·
      have h5 := pRank_lGen_le hR hJ hP0 hp hp2
      have h7 : 2 ≤ CFSG.Open.pRank p (lGen IsCalL0 ⊤ Sb) := by omega
      have h6 : 2 ≤ CFSG.Open.pRank p (lGen IsCalL0 ⊤ (T.subgroupOf H)) :=
        two_le_pRank_of_le_map π hp hp2 (lGen_le_map_lGen_of_surjective hP0 π hπ hker _) h7
      rw [lGen_eq_map_lGen_subgroupOf hTH.le, pRank_map_subtype]
      omega
  ·
    have hThM : (autT Sb E).subgroupOf (autQ Sb E) ≤ M :=
      hMax _ le_rfl (autT_subgroupOf_lt_top hR hJ)
    obtain ⟨hlt, hle⟩ := le_liftN_of_isMaxOver hR hJ hM hMax
    have hTX : autT Sb E ≤ M.map (autQ Sb E).subtype := fun x hx =>
      ⟨⟨x, autT_le_autQ Sb E hx⟩, hThM (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hXQ : M.map (autQ Sb E).subtype ≤ autQ Sb E := Subgroup.map_subtype_le M
    have hMY0 : ¬ HasCompFactor (liftN Sb E (M.map (autQ Sb E).subtype)) IsCalL0 := by
      rintro ⟨L, _, hcf, hL⟩
      haveI : Finite L := isCompositionFactor_finite hcf
      have h7 := isCompositionFactor_of_liftN hR hJ hTX hXQ hcf (hP0 L hL)
      exact hM0 ⟨L, inferInstance, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (M.equivMapOfInjective _ (autQ Sb E).subtype_injective)).2 h7, hL⟩
    obtain ⟨hKlt, hKmax, hK0⟩ :=
      uniqueMax_comap hP0 π hπ hker hS hnoK hneK hs hlt (fun X hX hXt => hle X hX hXt) hMY0
    right; right
    refine ⟨calNIn_eq_lGen_of_top hTH h1 hKlt hKmax hK0,
      Or.inr ⟨preG π E, isComponentModN_of_isComponent hE, map_subtype_sup_eq hTH.le hES, ?_⟩⟩
    have hOInf : OInf H = π.ker.map H.subtype := by
      rw [hπdef, QuotientGroup.ker_mk']
      rfl
    have hradA : CFSG.solvableRadical ↥(autQ Sb E) = ⊥ :=
      solvableRadical_eq_bot_of_simple_normal hLs hLnab hLC
    refine shape54_of_surjective (H' := ⊤) (T' := (autT Sb E).subgroupOf (autQ Sb E))
      (L' := (innAutOf ↥E).subgroupOf (autQ Sb E)) ?_ (innPsi π E hAinn)
      (innPsi_surjective hπ E hAinn) ?_ ?_ ?_ hsh
    · rw [hOInf]
      exact Subgroup.map_mono (MonoidHom.ker_le_comap π E)
    · intro l
      rw [hOInf]
      exact innPsi_eq_one_iff π hZ hAinn l
    · intro l hl
      rw [oInf_top_eq_bot hradA, Subgroup.mem_bot] at hl
      exact Subtype.ext hl
    · intro t' ht' _
      obtain ⟨s, hsT, n, hn, hnt⟩ := exists_of_mem_autT π (Subgroup.mem_subgroupOf.mp ht')
      refine ⟨s, hsT, mem_normalizer_preG (hn ▸ n.2), fun l l₂ h => ?_⟩
      apply Subtype.ext
      rw [innPsi_conj π E hAinn hn l l₂ h, hnt]
      rfl

end CFSG.LocalAnalysis.WeakClosure81

end
