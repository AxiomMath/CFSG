module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoDefs
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenGeoDefs
import CFSG.ClassicalInvolution.Q3.Q3OFCovS7
import CFSG.LieType.Steinberg.CentralExt.POmegaOddMultiplier
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FourDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal CFSG.Open QuadraticMap
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt.SpinOddClosed
open scoped commutatorElement

private noncomputable def omSevenGCProj {K : Type} [Field K] (h2 : (2 : K) ≠ 0) :
    spinGroup (quadOdd 3 K) →* StatedProj (StatedOmega (StatedQuadOdd 3 K)) :=
  spinToStatedProj (quadOdd 3 K) (range_spinMatrix_quadOdd h2 (by norm_num))

private def omSevenGCLong : Fin 3 → ℤ := ofStdB 3 (Pi.single 0 1 + Pi.single 1 1)

private def omSevenGCShort : Fin 3 → ℤ := ofStdB 3 (Pi.single 2 1)

private theorem omSevenGC_isOrthPair_std {K : Type} [Field K] :
    IsOrthPair omSevenGCLong omSevenGCShort := by
  unfold omSevenGCLong omSevenGCShort
  refine ⟨0, 1, 2, true, true, true, by decide, by decide, by decide, ?_, ?_⟩
  · rw [toStdB_ofStdB]
    rfl
  · rw [toStdB_ofStdB]
    rfl

private theorem omSevenGC_exists_lifts_not_commute {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0)
    {L : Type} [Group L] (π : L →* StatedProj (StatedOmega (StatedQuadOdd 3 K)))
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center L)
    (hperf : Group.IsPerfect L) (hcard : Nat.card π.ker = 3) :
    ∃ l l' : L,
      π l = omSevenGCProj h2 (SpinOdd.x 3 K omSevenGCLong 1) ∧
      π l' = omSevenGCProj h2 (SpinOdd.x 3 K omSevenGCShort 1) ∧
      l * l' ≠ l' * l := by
  classical
  haveI hperfSpin : Group.IsPerfect (spinGroup (quadOdd 3 K)) :=
    isPerfect_spinGroup_quadOdd h2 (by norm_num)
  by_contra hcon
  push Not at hcon
  set E := pullback (omSevenGCProj h2) π with hE
  set E' : Subgroup ↥E := commutator ↥E with hE'
  set fst : ↥E →* spinGroup (quadOdd 3 K) := pullbackFst (omSevenGCProj h2) π with hfst
  set prj : ↥E →* L := (MonoidHom.snd (spinGroup (quadOdd 3 K)) L).comp E.subtype with hprj
  have hfs : Function.Surjective fst := pullbackFst_surjective hπ
  have hfc : fst.ker ≤ Subgroup.center ↥E := ker_pullbackFst_le_center hcen
  haveI : Group.IsPerfect ↥E' :=
    CFSG.ClassicalInvolution.Q3.Q3OF.isPerfect_commutator_of_central fst hfs hfc
  set π' : ↥E' →* spinGroup (quadOdd 3 K) := fst.comp E'.subtype with hπ'
  have hπ's : Function.Surjective π' := by
    rw [← MonoidHom.range_eq_top, hπ', MonoidHom.range_comp, Subgroup.range_subtype, hE',
      commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective fst hfs,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  have hπ'c : π'.ker ≤ Subgroup.center ↥E' := by
    intro y hy
    have h1 : (y : ↥E) ∈ Subgroup.center ↥E := hfc hy
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (Subgroup.mem_center_iff.mp h1 (z : ↥E))
  have hpair : IsOrthPair omSevenGCLong omSevenGCShort := omSevenGC_isOrthPair_std (K := K)
  have hcomm' : ∀ a b : ↥E', π' a = SpinOdd.x 3 K omSevenGCLong 1 →
      π' b = SpinOdd.x 3 K omSevenGCShort 1 → a * b = b * a := by
    intro a b ha hb
    have hLa : π (prj a) = omSevenGCProj h2
        (SpinOdd.x 3 K omSevenGCLong 1) := by
      have hm : omSevenGCProj h2 (fst (a : ↥E)) = π (prj a) := mem_pullback.1 (a : ↥E).2
      rw [← hm]
      have ha' : fst (a : ↥E) = SpinOdd.x 3 K omSevenGCLong 1 := ha
      rw [ha']
    have hLb : π (prj b) = omSevenGCProj h2
        (SpinOdd.x 3 K omSevenGCShort 1) := by
      have hm : omSevenGCProj h2 (fst (b : ↥E)) = π (prj b) := mem_pullback.1 (b : ↥E).2
      rw [← hm]
      have hb' : fst (b : ↥E) = SpinOdd.x 3 K omSevenGCShort 1 := hb
      rw [hb']
    have hLab : prj a * prj b = prj b * prj a := hcon (prj a) (prj b) hLa hLb
    have hfst : fst (a : ↥E) * fst (b : ↥E) = fst (b : ↥E) * fst (a : ↥E) := by
      rw [show fst (a : ↥E) = SpinOdd.x 3 K omSevenGCLong 1 from ha,
          show fst (b : ↥E) = SpinOdd.x 3 K omSevenGCShort 1 from hb]
      exact commute_x_of_isOrthPair (n := 3) (K := K) hpair 1 1
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))
    · show fst (a : ↥E) * fst (b : ↥E) = fst (b : ↥E) * fst (a : ↥E)
      exact hfst
    · show prj a * prj b = prj b * prj a
      exact hLab
  have hker : π'.ker = ⊥ :=
    spinSeven_ker_eq_bot_of_comm hK hπ's hπ'c hpair hcomm'
  have hπ'inj : Function.Injective π' := (MonoidHom.ker_eq_bot_iff π').mp hker
  set e : ↥E' ≃* spinGroup (quadOdd 3 K) :=
    MulEquiv.ofBijective π' ⟨hπ'inj, hπ's⟩ with he
  let σ : spinGroup (quadOdd 3 K) →* L :=
    (prj.comp E'.subtype).comp (e.symm : spinGroup (quadOdd 3 K) →* ↥E')
  have hσ : ∀ s, π (σ s) = omSevenGCProj h2 s := by
    intro s
    have h1 := mem_pullback.1 ((e.symm s : ↥E') : ↥E).2
    have h2 : ((e.symm s : ↥E') : ↥E).val.1 = s := by
      have h3 : π' (e.symm s) = s := e.apply_symm_apply s
      exact h3
    rw [h2] at h1
    exact h1.symm
  haveI hq2 : IsPGroup 2 (omSevenGCProj h2).ker :=
    IsPGroup.of_card (n := 1) (by
      change Nat.card (spinToStatedProj (quadOdd 3 K)
        (range_spinMatrix_quadOdd h2 (by norm_num))).ker = 2 ^ 1
      rw [card_ker_spinToStatedProj_quadOdd (n := 3) h2 (by norm_num)]
      norm_num)
  have hsurj : Function.Surjective σ := by
    have hdecomp : ∀ x : L, ∃ s, x * (σ s)⁻¹ ∈ Subgroup.center L :=
      fun x => by
        obtain ⟨s, hs⟩ := spinToStatedProj_surjective (quadOdd 3 K)
          (range_spinMatrix_quadOdd h2 (by norm_num)) (π x)
        have hs' : (omSevenGCProj h2) s = π x := hs
        refine ⟨s, hcen ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, hs', mul_inv_cancel]
    have hcommσ : commutator L ≤ σ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ := hdecomp x
      obtain ⟨t, ht⟩ := hdecomp y
      have e1 : ⁅x, y⁆ = ⁅σ s, σ t⁆ := by
        have h := commutatorElement_mul_mul_of_mem_center hs ht (σ s) (σ t)
        rwa [inv_mul_cancel_right, inv_mul_cancel_right] at h
      rw [e1, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro x
    exact hcommσ (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top x)
  have hbot : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨s, rfl⟩ := hsurj p
    have hs1 : (omSevenGCProj h2) s = 1 := by rw [← hσ s]; exact hp
    obtain ⟨k, hk⟩ := hq2 ⟨s, hs1⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hpk : (σ s) ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    have hodd : Odd (orderOf (σ s)) := by
      have hdvd : orderOf (σ s) ∣ 3 := by
        have := Subgroup.orderOf_dvd_natCard π.ker (show σ s ∈ π.ker from hp)
        rwa [hcard] at this
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    have hd := orderOf_dvd_of_pow_eq_one hpk
    have hcop : Nat.Coprime (orderOf (σ s)) (2 ^ k) :=
      (Nat.coprime_two_right.2 hodd).pow_right k
    have h1 : σ s = 1 := orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd)
    rw [h1]
    exact Subgroup.mem_bot.mpr rfl
  rw [hbot, Subgroup.card_bot] at hcard
  omega

private theorem omSevenGC_liftsConjugate_std {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (h2 : (2 : K) ≠ 0) :
    LiftsConjugate (omSevenGCProj h2 (SpinOdd.x 3 K omSevenGCShort 1)) := by
  classical
  intro L _ π hπ hcen hperf hcard x' hx' z hz
  obtain ⟨l, l', hl, hl', hne⟩ :=
    omSevenGC_exists_lifts_not_commute hK h2 π hπ hcen hperf hcard
  have hgl : ⁅l, l'⁆ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hl, hl']
    rw [commutatorElement_eq_one_iff_mul_comm]
    rw [← map_mul, ← map_mul,
      commute_x_of_isOrthPair (n := 3) (K := K) (omSevenGC_isOrthPair_std (K := K)) 1 1]
  have hg_ne : ⁅l, l'⁆ ≠ 1 := by
    intro h
    exact hne (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hgpow3 : ⁅l, l'⁆ ^ 3 = 1 := by
    have hdvd : orderOf ⁅l, l'⁆ ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard π.ker hgl
      rwa [hcard] at h
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hg3 : orderOf ⁅l, l'⁆ = 3 := orderOf_eq_prime hgpow3 hg_ne
  haveI : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hgpowers : Subgroup.zpowers ⁅l, l'⁆ = π.ker := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgl)
    rw [Nat.card_zpowers, hg3, hcard]
  have hzmem : z ∈ Subgroup.zpowers ⁅l, l'⁆ := by
    rw [hgpowers]
    exact hz
  have hfin : IsOfFinOrder ⁅l, l'⁆ := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hgpow3⟩
  have hzpow : z ∈ Submonoid.powers ⁅l, l'⁆ := hfin.mem_powers_iff_mem_zpowers.mpr hzmem
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff z ⁅l, l'⁆).mp hzpow
  have hcentral_g : ⁅l, l'⁆ ∈ Subgroup.center L := hcen hgl
  have hcomm_lg : Commute l ⁅l, l'⁆ := Subgroup.mem_center_iff.mp hcentral_g l
  have hpow : ⁅l, l'⁆ ^ j = ⁅l ^ j, l'⁆ := hcomm_lg.commutatorElement_pow_left j
  have hzc : ⁅l ^ j, l'⁆ = z := by rw [← hpow, hj]
  set w : L := (l')⁻¹ * x' with hwdef
  have hwker : w ∈ π.ker := by
    rw [hwdef, MonoidHom.mem_ker, map_mul, map_inv, hl', hx', inv_mul_cancel]
  have hwcent : w ∈ Subgroup.center L := hcen hwker
  have hxw : x' = l' * w := by rw [hwdef]; group
  have hstep : l ^ j * x' * (l ^ j)⁻¹ = ⁅l ^ j, l'⁆ * x' := by
    rw [hxw]
    have hwmove : ∀ a : L, w * a = a * w := fun a =>
      (Subgroup.mem_center_iff.mp hwcent a).symm
    calc
      l ^ j * (l' * w) * (l ^ j)⁻¹ = l ^ j * l' * (w * (l ^ j)⁻¹) := by group
      _ = l ^ j * l' * ((l ^ j)⁻¹ * w) := by rw [hwmove ((l ^ j)⁻¹)]
      _ = (l ^ j * l' * (l ^ j)⁻¹) * w := by group
      _ = (⁅l ^ j, l'⁆ * l') * w := by
            rw [show l ^ j * l' * (l ^ j)⁻¹ = ⁅l ^ j, l'⁆ * l' from by
              rw [commutatorElement_def]; group]
      _ = ⁅l ^ j, l'⁆ * (l' * w) := by group
  refine ⟨l ^ j, ?_⟩
  rw [hstep, hzc]
  exact (Subgroup.mem_center_iff.mp (hcen hz) x').symm

theorem exists_liftsConjugate_eichlerProj {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (h2 : (2 : K) ≠ 0) :
    ∃ u w : OmegaSevenIdx → K, OmegaSevenShortPair u w ∧ LiftsConjugate (eichlerProj h2 u w) := by
  classical
  set u : OmegaSevenIdx → K := Pi.single (SpinOdd.oddIdx 2 true) 1 with hu_def
  set w : OmegaSevenIdx → K := Pi.single SpinOdd.zIdx 1 with hw_def
  have huQ : quadOdd 3 K u = 0 := by simp [u, quadOdd_apply, SpinOdd.oddIdx, Pi.single_apply]
  have hu0 : u ≠ 0 := by simp [u, SpinOdd.oddIdx, Pi.single_apply]
  have hpol : polar (quadOdd 3 K) u w = 0 := by
    simp [u, w, polar_quadOdd, SpinOdd.oddIdx, SpinOdd.zIdx, Pi.single_apply]
  have hwQ : quadOdd 3 K w = 1 := by simp [w, quadOdd_apply, SpinOdd.zIdx, Pi.single_apply]
  have hδ : SpinOdd.x 3 K omSevenGCShort 1 =
      (oddFrame 3 K).shortRoot 2 true (.ofAdd 1) := by
    rw [SpinOdd.x_eq_short (i := 2) (s := true) (h := by
      rw [show omSevenGCShort = ofStdB 3 (Pi.single 2 1) from rfl, toStdB_ofStdB]
      rfl)]
    simp [boolSign]
  have hmatrix : toLinEquiv OmegaSevenIdx K
      (spinMatrix (quadOdd 3 K) (SpinOdd.x 3 K omSevenGCShort 1)) =
      eichler (quadOdd 3 K) u w := by
    rw [hδ]
    have h1 : toLinEquiv OmegaSevenIdx K
        (spinMatrix (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 true (.ofAdd 1))) =
        spinAction (quadOdd 3 K) ((oddFrame 3 K).shortRoot 2 true (.ofAdd 1)) := by
      apply LinearEquiv.ext
      intro v
      rw [toLinEquiv_apply, spinMatrix_mulVec]
    rw [h1, OddFrame.spinAction_shortRoot_eq_eichler]
    have hu : (oddFrame 3 K).vec 2 true = u := by
      simp [u, SpinOdd.oddIdx]
    have hw : (1 : K) • (oddFrame 3 K).z = w := by
      simp [w, SpinOdd.zIdx, oddZ]
    rw [hu, hw]
  have hgl : (eichlerOmega h2 u w : Matrix.GeneralLinearGroup OmegaSevenIdx K) =
      spinMatrix (quadOdd 3 K) (SpinOdd.x 3 K omSevenGCShort 1) := by
    apply (toLinEquiv OmegaSevenIdx K).injective
    have h1 : toLinEquiv OmegaSevenIdx K (eichlerOmega h2 u w) =
        eichler (quadOdd 3 K) u w := by
      have hval : ((eichlerOmega h2 u w : StatedOmega (StatedQuadOdd 3 K)) :
          Matrix.GeneralLinearGroup OmegaSevenIdx K) =
          (toLinEquiv OmegaSevenIdx K).symm (eichler (quadOdd 3 K) u w) := rfl
      rw [hval, MulEquiv.apply_symm_apply]
    rw [h1, hmatrix]
  have hsub : (eichlerOmega h2 u w : StatedOmega (StatedQuadOdd 3 K)) =
      ⟨spinMatrix (quadOdd 3 K) (SpinOdd.x 3 K omSevenGCShort 1),
        spinMatrix_mem_of_range_eq (quadOdd 3 K)
          (range_spinMatrix_quadOdd h2 (by norm_num)) _⟩ := Subtype.ext hgl
  have hx : eichlerProj h2 u w =
      omSevenGCProj h2 (SpinOdd.x 3 K omSevenGCShort 1) := by
    have h1 : eichlerProj h2 u w = QuotientGroup.mk (eichlerOmega h2 u w) := rfl
    have h2 : omSevenGCProj h2 (SpinOdd.x 3 K omSevenGCShort 1) =
        spinToStatedProj (quadOdd 3 K) (range_spinMatrix_quadOdd h2 (by norm_num))
          (SpinOdd.x 3 K omSevenGCShort 1) := rfl
    rw [h1, h2, spinToStatedProj_apply]
    exact congrArg QuotientGroup.mk hsub
  refine ⟨u, w, ⟨huQ, hu0, hpol, hwQ⟩, ?_⟩
  rw [hx]
  exact omSevenGC_liftsConjugate_std hK h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
