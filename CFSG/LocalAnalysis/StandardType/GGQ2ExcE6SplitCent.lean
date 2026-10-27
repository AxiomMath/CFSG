module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitShortWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux6
import CFSG.LocalAnalysis.StandardType.GGQ2ExcInsideMoved
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreCentRaw

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.QTwoCav
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.LangRat

open scoped commutatorElement

noncomputable section


private theorem e6SplitWeyl_mem_rootSpan {L : Type} [Field L]
    {c : Finset (ExcRaw.Root 1)} {i : ExcRaw.Root 1} (hi : i ∈ c) :
    e6SplitWeyl L i ∈ rootSpan .E6 L (e6SplitCodeRoots c) := by
  have hsub : ({e6SplitRoot i, -e6SplitRoot i} : Set (Fin Tag.E6.rank → ℤ)) ⊆
      e6SplitCodeRoots c := by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr (Or.inl rfl)⟩
  have hsubσ : ({permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i),
      -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)} :
      Set (Fin Tag.E6.rank → ℤ)) ⊆ e6SplitCodeRoots c := by
    intro δ hδ
    rcases hδ with rfl | rfl
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨i, hi, Or.inr (Or.inr (Or.inr rfl))⟩
  by_cases hfix : ExcRaw.tabFix1.getD i.val false = true
  · rw [e6SplitWeyl, if_pos hfix]
    exact rootSpan_mono hsub (rootSL2_mem_rootSpan_pair (isRoot_e6SplitRoot i) WSL)
  · rw [e6SplitWeyl, if_neg hfix]
    exact mul_mem (rootSpan_mono hsub
        (rootSL2_mem_rootSpan_pair (isRoot_e6SplitRoot i) WSL))
      (rootSpan_mono hsubσ
        (rootSL2_mem_rootSpan_pair (isRoot_permLattice_e6SplitRoot i) WSL))

private theorem e6Split_ggLin_ggConjAut_commutator {L : Type} [Field L] [IsAlgClosed L]
    {p : ℕ} {S : LangSetup .E6 L p} {T₀ : Subgroup (ModGL .E6 L)}
    (hS : E6SplitLangTwo S) (d : E6SplitDatum S T₀) (i j : ExcRaw.Root 1)
    (hκN : ⁅e6SplitWeyl L i, e6SplitWeyl L j⁆ ∈
      Subgroup.normalizer (T₀ : Set (ModGL .E6 L))) (hchar : CharP L 2) :
    ggLin (p := 3) d.coord (ggConjAut T₀ hκN) =
      ExcRaw.reflection 1 i * ExcRaw.reflection 1 j *
        ExcRaw.reflection 1 i * ExcRaw.reflection 1 j := by
  have hwiN : e6SplitWeyl L i ∈ Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
    E6SplitDatum.e6SplitWeyl_mem_normalizer d hS i
  have hwjN : e6SplitWeyl L j ∈ Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
    E6SplitDatum.e6SplitWeyl_mem_normalizer d hS j
  have hwiinv : (e6SplitWeyl L i)⁻¹ = e6SplitWeyl L i :=
    inv_eq_of_mul_eq_one_right (e6SplitWeyl_mul_self (hchar := hchar) i)
  have hwjinv : (e6SplitWeyl L j)⁻¹ = e6SplitWeyl L j :=
    inv_eq_of_mul_eq_one_right (e6SplitWeyl_mul_self (hchar := hchar) j)
  have hκeq : ⁅e6SplitWeyl L i, e6SplitWeyl L j⁆ =
      e6SplitWeyl L i * e6SplitWeyl L j * e6SplitWeyl L i * e6SplitWeyl L j := by
    rw [commutatorElement_def, hwiinv, hwjinv]
  let h2N : e6SplitWeyl L i * e6SplitWeyl L j ∈
      Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) := Subgroup.mul_mem _ hwiN hwjN
  let h3N : e6SplitWeyl L i * e6SplitWeyl L j * e6SplitWeyl L i ∈
      Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) := Subgroup.mul_mem _ h2N hwiN
  let h4N : e6SplitWeyl L i * e6SplitWeyl L j * e6SplitWeyl L i * e6SplitWeyl L j ∈
      Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) := Subgroup.mul_mem _ h3N hwjN
  have hAutEq : ggConjAut T₀ hκN = ggConjAut T₀ h4N :=
    ggNSPosPA_ggConjAut_congr hκN h4N hκeq
  have hprod : ggConjAut T₀ h4N =
      ggConjAut T₀ hwiN * ggConjAut T₀ hwjN *
        ggConjAut T₀ hwiN * ggConjAut T₀ hwjN := by
    have e3 : ggConjAut T₀ h4N = ggConjAut T₀ h3N * ggConjAut T₀ hwjN :=
      (ggNSPosPA_ggConjAut_mul h3N hwjN).symm
    have e2 : ggConjAut T₀ h3N = ggConjAut T₀ h2N * ggConjAut T₀ hwiN :=
      (ggNSPosPA_ggConjAut_mul h2N hwiN).symm
    have e1 : ggConjAut T₀ h2N = ggConjAut T₀ hwiN * ggConjAut T₀ hwjN :=
      (ggNSPosPA_ggConjAut_mul hwiN hwjN).symm
    rw [e3, e2, e1]
  rw [hAutEq, hprod]
  simp only [map_mul, E6SplitDatum.ggLin_ggConjAut_e6SplitWeyl d hS i,
    E6SplitDatum.ggLin_ggConjAut_e6SplitWeyl d hS j]

theorem e6SplitCoreCent_holds : E6SplitCoreCent := by
  intro L _ _ p S hS T₀ d c hc
  ext v
  rw [mem_ggLinImage]
  let t : ↥T₀ := Additive.toMul (d.coord.symm v)
  have hvcoord : d.coord (Additive.ofMul t) = v := by
    simp [t]
  obtain ⟨b, hb⟩ := E6SplitDatum.exists_rootDiagUnit d t
  have hbT : rootDiagUnit .E6 b ∈ T₀ := hb ▸ t.2
  constructor
  · intro hv
    simp only [ExcRaw.cent, Submodule.mem_iInf, LinearMap.mem_ker]
    intro i hi
    by_cases hlong : ExcRaw.tabFix1.getD i.val false = true
    · have hcne : c ≠ {i} := by
        intro hc_eq
        have hfilter : ({x ∈ ({i} : Finset (ExcRaw.Root 1)) |
            ExcRaw.tabFix1.getD x.val false = true} : Finset _) = {i} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hx, -⟩
            exact hx
          · intro hx
            subst hx
            exact ⟨rfl, hlong⟩
        have hlc : ExcRaw.longCount 1 ({i} : Finset (ExcRaw.Root 1)) = 1 := by
          rw [ExcRaw.longCount, hfilter]
          simp
        have hlabel : ExcRaw.label 1 ({i} : Finset (ExcRaw.Root 1)) = ⟨.A, 1, 1⟩ := by
          change ExcRaw.labelE6Rel ({i} : Finset (ExcRaw.Root 1)).card
              (ExcRaw.longCount 1 ({i} : Finset (ExcRaw.Root 1))) = ⟨.A, 1, 1⟩
          rw [hlc, Finset.card_singleton]
          rfl
        have hlab := hc.2
        rw [hc_eq, hlabel] at hlab
        exact (by simp [LargeEvenInLambda2] :
          ¬ LargeEvenInLambda2 (⟨.A, 1, 1⟩ : LargeEvenLabel)) hlab
      obtain ⟨U, hU⟩ := hc.1
      have hcomp : ExcRaw.IsComp 1 (ExcRaw.Vanish 1 U) c := hU
      have hmin := hcomp.2.2.2
      have hnot : ¬ ∀ x ∈ ({i} : Finset (ExcRaw.Root 1)),
          ∀ y ∈ c, ExcRaw.Adj 1 x y → y ∈ ({i} : Finset (ExcRaw.Root 1)) := by
        intro hT
        have hsub : ({i} : Finset (ExcRaw.Root 1)) ⊆ c := by
          intro x hx
          rw [Finset.mem_singleton] at hx
          subst hx
          exact hi
        have hne : ({i} : Finset (ExcRaw.Root 1)).Nonempty :=
          ⟨i, Finset.mem_singleton_self i⟩
        exact hcne (hmin {i} hsub hne hT).symm
      push Not at hnot
      obtain ⟨x, hx, y, hy, hadj, hyi⟩ := hnot
      rw [Finset.mem_singleton] at hx
      subst x
      have hji : y ≠ i := by
        intro hyi'
        exact hyi (Finset.mem_singleton.mpr hyi')
      have hij : i ≠ y := fun h => hji h.symm
      have hwiA : e6SplitWeyl L i ∈
          rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ :=
        ⟨e6SplitWeyl_mem_rootSpan hi, e6SplitWeyl_mem_Γ hS i⟩
      have hwyA : e6SplitWeyl L y ∈
          rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ :=
        ⟨e6SplitWeyl_mem_rootSpan hy, e6SplitWeyl_mem_Γ hS y⟩
      have hκR : ⁅e6SplitWeyl L i, e6SplitWeyl L y⁆ ∈ e6SplitComponent S c :=
        Subgroup.commutator_mem_commutator hwiA hwyA
      have hwiN : e6SplitWeyl L i ∈
          Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
        E6SplitDatum.e6SplitWeyl_mem_normalizer d hS i
      have hwyN : e6SplitWeyl L y ∈
          Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
        E6SplitDatum.e6SplitWeyl_mem_normalizer d hS y
      have hκN : ⁅e6SplitWeyl L i, e6SplitWeyl L y⁆ ∈
          Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
        Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator hwiN hwyN)
      have hcommκ : ⁅e6SplitWeyl L i, e6SplitWeyl L y⁆ * (t : ModGL .E6 L) =
          (t : ModGL .E6 L) * ⁅e6SplitWeyl L i, e6SplitWeyl L y⁆ :=
        Subgroup.mem_centralizer_iff.1 hv _ hκR
      have hfixAut : ggConjAut T₀ hκN t = t := by
        apply Subtype.ext
        rw [ggConjAut_apply]
        rw [hcommκ]
        group
      have hchar : CharP L 2 :=
        charP_two_of_langSetup_q_eq_two_pow S (by rw [hS.1, pow_one])
      have hfixV : (ExcRaw.reflection 1 i * ExcRaw.reflection 1 y)
          ((ExcRaw.reflection 1 i * ExcRaw.reflection 1 y) v) = v := by
        have h1 : ggLin (p := 3) d.coord (ggConjAut T₀ hκN)
            (d.coord (Additive.ofMul t)) = d.coord (Additive.ofMul t) := by
          rw [ggLin_apply_ofMul, hfixAut]
        rw [e6Split_ggLin_ggConjAut_commutator hS d i y hκN hchar] at h1
        rw [hvcoord] at h1
        rwa [mul_assoc, LinearEquiv.mul_apply] at h1
      exact ExcRaw.root_eq_zero_of_reflection_fix ExcRaw.adjIndep_one hij hadj hfixV
    · have hshort : ExcRaw.tabFix1.getD i.val false = false := by
        cases h : ExcRaw.tabFix1.getD i.val false <;> simp_all
      have hwi_mem : e6SplitWeyl L i ∈ e6SplitComponent S c :=
        e6SplitWeyl_mem_e6SplitComponent hS hi hshort
      have hwiN : e6SplitWeyl L i ∈
          Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
        E6SplitDatum.e6SplitWeyl_mem_normalizer d hS i
      have hcommwi : e6SplitWeyl L i * (t : ModGL .E6 L) =
          (t : ModGL .E6 L) * e6SplitWeyl L i :=
        Subgroup.mem_centralizer_iff.1 hv _ hwi_mem
      have hfixAut : ggConjAut T₀ hwiN t = t := by
        apply Subtype.ext
        rw [ggConjAut_apply]
        rw [hcommwi]
        group
      have h1 : ggLin (p := 3) d.coord (ggConjAut T₀ hwiN)
          (d.coord (Additive.ofMul t)) = d.coord (Additive.ofMul t) := by
        rw [ggLin_apply_ofMul, hfixAut]
      rw [E6SplitDatum.ggLin_ggConjAut_e6SplitWeyl d hS i, hvcoord] at h1
      have hzero : ExcRaw.root 1 i v • ExcRaw.coroot 1 i = 0 := by
        have h : v - ExcRaw.root 1 i v • ExcRaw.coroot 1 i = v := by
          rw [← ExcRaw.reflection_apply, h1]
        exact sub_eq_self.mp h
      exact (smul_eq_zero.mp hzero).resolve_right (ExcRaw.coroot_ne_zero 1 i)

  · intro hv
    have hcent_i : ∀ i ∈ c, ExcRaw.root 1 i v = 0 := by
      simpa only [ExcRaw.cent, Submodule.mem_iInf, LinearMap.mem_ker] using hv
    have hbfull : rootDiagUnit .E6 b ∈ fullThreeTorus S := d.le_fullThreeTorus hbT
    have hγ : ∀ i ∈ c, rootChar b (e6SplitRoot i) = 1 := by
      intro i hi
      rw [d.rootChar_eq t b hb i, hvcoord, hcent_i i hi]
      simp
    have hker : e6SplitCodeRoots c ⊆ rootCharKernel b := by
      rintro δ ⟨i, hi, hδ⟩
      have hneg : rootChar b (-e6SplitRoot i) = 1 := by
        rw [show -e6SplitRoot i = 0 - e6SplitRoot i by simp, rootChar_sub,
          rootChar_zero, one_mul, hγ i hi, inv_one]
      have hσ : rootChar b (permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 1 := by
        rw [rootChar_permLattice_of_mem_fullThreeTorus hS hbfull (e6SplitRoot i), hγ i hi]
      have hσneg : rootChar b
          (-permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i)) = 1 := by
        rw [show -permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) =
            0 - permLattice (τ := .E6) TwistTag.E6.perm (e6SplitRoot i) by simp,
          rootChar_sub, rootChar_zero, one_mul, hσ, inv_one]
      rcases hδ with rfl | rfl | rfl | rfl
      · exact ⟨isRoot_e6SplitRoot i, hγ i hi⟩
      · exact ⟨IsRoot.neg (isRoot_e6SplitRoot i), hneg⟩
      · exact ⟨isRoot_permLattice_e6SplitRoot i, hσ⟩
      · exact ⟨IsRoot.neg (isRoot_permLattice_e6SplitRoot i), hσneg⟩
    have hle := rootSpan_le_centralizer (K := L) b hker
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hxroot : x ∈ rootSpan .E6 L (e6SplitCodeRoots c) := by
      have hx' : x ∈ rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ :=
        (Subgroup.commutator_le_self
          (rootSpan .E6 L (e6SplitCodeRoots c) ⊓ S.Γ)) hx
      exact (Subgroup.mem_inf.1 hx').1
    have hxcent : x ∈ Subgroup.centralizer {rootDiagUnit .E6 b} := hle hxroot
    have hxd : rootDiagUnit .E6 b * x = x * rootDiagUnit .E6 b :=
      Subgroup.mem_centralizer_iff.1 hxcent (rootDiagUnit .E6 b) (Set.mem_singleton _)
    rw [hb]
    exact hxd.symm

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
