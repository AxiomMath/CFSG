module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIV.lemma_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIV.lemma_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.theorem_2_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.DegreeBounds

namespace CFSG
end CFSG
open CFSG

attribute [local instance] commutatorElement
open scoped IsMulCommutative

/-!
# Peterfalvi Appendix IV, Feit-Sibley Theorem

The statement and the eight numbered proof stages follow the authoritative
PFpart2 PNG rendering, printed pages 145-150.
-/

noncomputable section

attribute [local instance] Fintype.ofFinite

attribute [local instance] commutatorElement

namespace CFSG.BenderSuzuki
namespace PFAppendixIV

open Section1 Section5 Section6

universe u

private def correctionLinear
    {G : Type u} [Group G] [Finite G] (R : Subgroup G) :
    ClassFunction R →ₗ[ℂ] ClassFunction G where
  toFun := fun chi =>
    degree chi • (principalCharacter G - inducedCF R (principalCharacter R))
  map_add' := by
    intro chi psi
    ext g
    simp [degree, add_mul]
  map_smul' := by
    intro c chi
    ext g
    simp [degree, mul_assoc]

private def exceptionalLinear
    {G : Type u} [Group G] [Finite G] (R : Subgroup G) :
    ClassFunction R →ₗ[ℂ] ClassFunction G :=
  inducedCFLinear R + correctionLinear R

private theorem exceptionalLinear_apply
    {G : Type u} [Group G] [Finite G] (R : Subgroup G)
    (chi : ClassFunction R) :
    exceptionalLinear R chi =
      External.Suzuki.VI.frobeniusExceptionalCharacter R chi := by
  rw [External.Suzuki.VI.frobeniusExceptionalCharacter]
  rw [← inducedCFLinear_apply R
    (chi - degree chi • principalCharacter R)]
  rw [map_sub, map_smul]
  ext g
  simp [exceptionalLinear, correctionLinear, inducedCFLinear_apply]
  ring

private theorem map_evalCoeff
    {L : Type u} [Group L]
    {G : Type u} [Group G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ClassFunction L →ₗ[ℂ] ClassFunction G)
    (mu : ι → ClassFunction L) (v : CoeffVector ι) :
    T (evalCoeff mu v) = evalCoeff (fun i => T (mu i)) v := by
  classical
  ext g
  simp [evalCoeff, Finset.sum_apply]

private theorem scalarProduct_evalCoeff_eq_of_gram_eq
    {L : Type u} [Group L] [Finite L]
    {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι]
    (mu : ι → ClassFunction L) (nu : ι → ClassFunction G)
    (hgram : ∀ i j, scalarProduct G (nu i) (nu j) =
      scalarProduct L (mu i) (mu j))
    (v w : CoeffVector ι) :
    scalarProduct G (evalCoeff nu v) (evalCoeff nu w) =
      scalarProduct L (evalCoeff mu v) (evalCoeff mu w) := by
  have hleftG :
      (∑ i : ι, (v i : ℂ) • nu i) =
        (fun g : G => ∑ i : ι, ((v i : ℂ) • nu i) g) := by
    ext g
    simp
  have hrightG :
      (∑ i : ι, (w i : ℂ) • nu i) =
        (fun g : G => ∑ i : ι, ((w i : ℂ) • nu i) g) := by
    ext g
    simp
  have hleftL :
      (∑ i : ι, (v i : ℂ) • mu i) =
        (fun g : L => ∑ i : ι, ((v i : ℂ) • mu i) g) := by
    ext g
    simp
  have hrightL :
      (∑ i : ι, (w i : ℂ) • mu i) =
        (fun g : L => ∑ i : ι, ((w i : ℂ) • mu i) g) := by
    ext g
    simp
  calc
    scalarProduct G (evalCoeff nu v) (evalCoeff nu w) =
        ∑ i : ι, ∑ j : ι,
          (v i : ℂ) * (star (w j : ℂ) * scalarProduct G (nu i) (nu j)) := by
      simp only [evalCoeff]
      rw [hleftG, hrightG, scalarProduct_fintype_sum_left]
      simp_rw [scalarProduct_smul_left]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [scalarProduct_fintype_sum_right]
      simp_rw [scalarProduct_smul_right]
      rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ j : ι,
          (v i : ℂ) * (star (w j : ℂ) * scalarProduct L (mu i) (mu j)) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hgram i j]
    _ = scalarProduct L (evalCoeff mu v) (evalCoeff mu w) := by
      symm
      simp only [evalCoeff]
      rw [hleftL, hrightL, scalarProduct_fintype_sum_left]
      simp_rw [scalarProduct_smul_left]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [scalarProduct_fintype_sum_right]
      simp_rw [scalarProduct_smul_right]
      rw [Finset.mul_sum]

private theorem virtual_zsmul
    {G : Type u} [Group G] [Finite G]
    (n : ℤ) {chi : ClassFunction G}
    (hchi : Theory.Character.IsVirtualCharacter chi) :
    Theory.Character.IsVirtualCharacter ((n : ℂ) • chi) := by
  classical
  rcases hchi with ⟨r, m, k, rho, rfl⟩
  refine ⟨r, fun i => n * m i, k, rho, ?_⟩
  ext g
  calc
    ((n : ℂ) • Theory.Character.virtualCharacterOfRepresentations r m k rho) g
        = (n : ℂ) * Theory.Character.virtualCharacterOfRepresentations r m k rho g := by
      simp
    _ = (n : ℂ) * (∑ i : Fin r, ((m i : ℤ) : ℂ) * ((rho i).character g)) := rfl
    _ = ∑ i : Fin r, (((n : ℤ) * (m i : ℤ) : ℤ) : ℂ) * ((rho i).character g) := by
      simp [Finset.mul_sum, mul_assoc]
    _ = Theory.Character.virtualCharacterOfRepresentations r (fun i : Fin r => n * m i) k rho g := by
      simp [Theory.Character.virtualCharacterOfRepresentations]

private theorem virtual_finset_sum
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} (s : Finset ι) (Phi : ι → ClassFunction G)
    (hPhi : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Phi i)) :
    Theory.Character.IsVirtualCharacter (Finset.sum s Phi) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i => nomatch i), (fun i => nomatch i),
        (fun i => nomatch i), ?_⟩
      ext g
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert a s ha ih =>
      have ha' := hPhi a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (Finset.sum s Phi) := by
        apply ih
        intro i hi
        exact hPhi i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

private theorem virtual_evalCoeff
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : ι → ClassFunction G)
    (hmu : ∀ i, Theory.Character.IsVirtualCharacter (mu i))
    (v : CoeffVector ι) :
    Theory.Character.IsVirtualCharacter (evalCoeff mu v) := by
  classical
  rw [evalCoeff]
  apply virtual_finset_sum (Finset.univ : Finset ι)
    (fun i => ((v i : ℂ) • mu i))
  intro i _hi
  simpa using virtual_zsmul (v i) (hmu i)

private theorem coherent_of_TI_exceptional
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hRne : R ≠ ⊥)
    (hTI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g))
    (chars : Finset (ClassFunction R))
    (hirr : ∀ chi : ClassFunction R, chi ∈ chars →
      IsIrreducibleCharacterOnGroup chi)
    (hnonempty : integerSpanOnNonempty chars puncturedSet) :
    IsCoherentTriple puncturedSet chars (inducedCFLinear R) := by
  classical
  let T' := exceptionalLinear R
  have hTapply (chi : ClassFunction R) :
      T' chi = External.Suzuki.VI.frobeniusExceptionalCharacter R chi :=
    exceptionalLinear_apply R chi
  have hTirr (chi : ClassFunction R) (hchi : chi ∈ chars) :
      IsIrreducibleCharacterOnGroup (T' chi) := by
    rw [hTapply]
    exact External.Suzuki.VI.frobeniusExceptionalCharacter_irreducible_of_TI
      R hRne hTI chi (hirr chi hchi)
  have hTne (chi psi : ClassFunction R)
      (hchi : chi ∈ chars) (hpsi : psi ∈ chars) (hne : chi ≠ psi) :
      T' chi ≠ T' psi := by
    intro heq
    apply hne
    have hstarEq :
        External.Suzuki.VI.frobeniusExceptionalCharacter R chi =
          External.Suzuki.VI.frobeniusExceptionalCharacter R psi := by
      simpa [hTapply] using heq
    have hdegree : degree chi = degree psi := by
      calc
        degree chi = degree
            (External.Suzuki.VI.frobeniusExceptionalCharacter R chi) :=
          (External.Suzuki.VI.frobeniusExceptionalCharacter_degree R chi).symm
        _ = degree
            (External.Suzuki.VI.frobeniusExceptionalCharacter R psi) :=
          congrArg degree hstarEq
        _ = degree psi :=
          External.Suzuki.VI.frobeniusExceptionalCharacter_degree R psi
    ext r
    by_cases hr : (r : G) = 1
    · have hr1 : r = 1 := Subtype.ext hr
      subst r
      simpa [degree] using hdegree
    · calc
        chi r = External.Suzuki.VI.frobeniusExceptionalCharacter R chi (r : G) :=
          (External.Suzuki.VI.frobeniusExceptionalCharacter_apply_subgroup_of_TI
            R hRne hTI chi (hirr chi hchi) r hr).symm
        _ = External.Suzuki.VI.frobeniusExceptionalCharacter R psi (r : G) :=
          congrFun hstarEq (r : G)
        _ = psi r :=
          External.Suzuki.VI.frobeniusExceptionalCharacter_apply_subgroup_of_TI
            R hRne hTI psi (hirr psi hpsi) r hr
  have hgram : ∀ i j : chars,
      scalarProduct G (T' (i : ClassFunction R)) (T' (j : ClassFunction R)) =
        scalarProduct R (i : ClassFunction R) (j : ClassFunction R) := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [scalarProduct_irreducibleCharacter_self (hTirr i i.property),
        scalarProduct_irreducibleCharacter_self (hirr i i.property)]
    · have hsourceNe : (i : ClassFunction R) ≠ (j : ClassFunction R) := by
        intro h
        exact hij (Subtype.ext h)
      rw [scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hTirr i i.property) (hTirr j j.property)
          (hTne i j i.property j.property hsourceNe),
        scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hirr i i.property) (hirr j j.property) hsourceNe]
  refine ⟨?_, hnonempty, T', ?_, ?_, ?_⟩
  · intro chi hchi
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hirr chi hchi)
  · rintro phi psi ⟨v, rfl⟩ ⟨w, rfl⟩
    rw [map_evalCoeff, map_evalCoeff]
    exact scalarProduct_evalCoeff_eq_of_gram_eq
      (fun i : chars => (i : ClassFunction R))
      (fun i : chars => T' (i : ClassFunction R)) hgram v w
  · rintro phi ⟨v, rfl⟩
    rw [map_evalCoeff]
    apply virtual_evalCoeff
    intro i
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hTirr i i.property)
  · intro phi hphi
    have hdegree : degree phi = 0 :=
      (supportedOn_puncturedSet_iff_degree_eq_zero phi).mp hphi.2
    ext g
    simp [T', exceptionalLinear, correctionLinear, hdegree,
      inducedCFLinear_apply]

private theorem isZGroup_of_odd_subgroup_of_frobenius_complement
    {G : Type u} [Group G] [Finite G]
    {K R R0 : Subgroup G}
    (hfrob : IsFrobeniusGroupWithKernelComplement K R)
    (hR0le : R0 ≤ R) (hR0odd : Odd (Nat.card R0)) :
    IsZGroup R0 := by
  classical
  let : K.Normal := hfrob.normal
  let : MulDistribMulAction R K :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) R K
      (Subgroup.le_normalizer_of_normal (H := K))
  have hregularR : ActsRegularly R K := hfrob.regular_conj_action
  let R0R : Subgroup R := R0.subgroupOf R
  let : MulDistribMulAction R0R K :=
    MulDistribMulAction.compHom K R0R.subtype
  have hregularR0R : ActsRegularly R0R K :=
    hregularR.subgroup R0R
  have : Nontrivial K :=
    (Subgroup.nontrivial_iff_ne_bot K).2 hfrob.kernel_ne_bot
  have hR0Rodd : Odd (Nat.card R0R) := by
    change Odd (Nat.card (R0.subgroupOf R))
    rw [natCard_subgroupOf_eq R0 R hR0le]
    exact hR0odd
  have hZR0R : IsZGroup R0R := by
    rw [isZGroup_iff]
    intro p hp P
    exact isCyclic_of_odd_regular_pSubgroup
      (H := K) (R := R0R) (P := (P : Subgroup R0R))
        hp hR0Rodd hregularR0R P.isPGroup'
  let e : R0R ≃* R0 := Subgroup.subgroupOfEquivOfLe hR0le
  let : IsZGroup R0R := hZR0R
  exact IsZGroup.of_injective (f := e.symm.toMonoidHom) e.symm.injective

private theorem FeitSibleyData.isZGroup_Q1_of_D_eq_bot
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) (hD : d.D = ⊥) :
    IsZGroup d.Q1 := by
  classical
  have hQtop : d.Q = ⊤ := by
    simpa [hD] using d.H_eq_Q_sup_D
  have hQInG_eq_H : d.QInG = d.H := by
    rw [FeitSibleyData.QInG, hQtop]
    simpa [MonoidHom.range_eq_map] using
      (d.H.range_subtype : d.H.subtype.range = d.H)
  have hQ1ne : d.Q1 ≠ ⊥ := by
    intro hQ1
    apply d.Q1_not_two_group
    exact hQ1.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
  have hQne : d.Q ≠ ⊥ := by
    intro hQ
    apply hQ1ne
    apply le_bot_iff.mp
    simpa [hQ] using d.Q1_le_Q
  have hQInGne : d.QInG ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (H := d.Q) (f := d.H.subtype) d.H.subtype_injective).not.mpr hQne
  have hQInGproper : d.QInG ≠ ⊤ := by
    rw [hQInG_eq_H]
    exact d.H_ne_top
  have hTI : ∀ g : G, g ∉ d.QInG →
      Disjoint d.QInG (d.QInG.conjBy g) := by
    intro g hg
    have hginv : g⁻¹ ∉ d.H := by
      intro h
      apply hg
      rw [hQInG_eq_H]
      simpa using d.H.inv_mem h
    have htemp := d.Q_TI_in_G g⁻¹ hginv
    -- need to rewrite Subgroup.map to d.QInG
    have htemp' : Disjoint d.QInG (d.QInG.conjBy g) := by
      simpa [FeitSibleyData.QInG, PFchapter1section1.rightConjugate] using htemp
    exact htemp'
  obtain ⟨K, hfrob⟩ :=
    External.Suzuki.VI.suzuki_ch6_theorem_2_3
      d.QInG hQInGne hQInGproper hTI
  let Q1InG : Subgroup G := d.Q1.map d.H.subtype
  have hQ1InG_le : Q1InG ≤ d.QInG := by
    simpa [Q1InG, FeitSibleyData.QInG] using
      (Subgroup.map_mono (f := d.H.subtype) d.Q1_le_Q)
  have hQ1InGodd : Odd (Nat.card Q1InG) := by
    have hcard : Nat.card Q1InG = Nat.card d.Q1 := by
      exact Subgroup.card_map_of_injective
        (K := d.Q1) (f := d.H.subtype) d.H.subtype_injective
    rw [hcard]
    exact d.Q1_odd
  have hZQ1InG : IsZGroup Q1InG :=
    isZGroup_of_odd_subgroup_of_frobenius_complement
      hfrob hQ1InG_le hQ1InGodd
  let e : d.Q1 ≃* Q1InG :=
    Subgroup.equivMapOfInjective d.Q1 d.H.subtype d.H.subtype_injective
  let : IsZGroup Q1InG := hZQ1InG
  exact IsZGroup.of_injective (f := e.toMonoidHom) e.injective

private theorem FeitSibleyData.isNilpotent_Q1_of_D_ne_bot
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) (hD : d.D ≠ ⊥) :
    Group.IsNilpotent d.Q1 := by
  let : d.Q1.Normal := d.Q1_normal
  apply
    External.huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
      d.Q1 d.D
  · exact Subgroup.le_normalizer_of_normal (H := d.Q1)
  · obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
    exact ⟨x, x.property, by simpa using hx⟩
  · intro x hx hxne
    apply le_antisymm
    · intro q hq
      have hcomm : x * (q : d.H) = q * x :=
        (Subgroup.mem_centralizer_iff.mp hq.1 x) (by simp)
      have hfix : x * (q : d.H) * x⁻¹ = q := by
        rw [hcomm]
        simp
      have hqeq : (⟨q, hq.2⟩ : d.Q1) = 1 :=
        d.D_fixedPointFree_on_Q1 ⟨x, hx⟩ hxne ⟨q, hq.2⟩ hfix
      simpa using congrArg Subtype.val hqeq
    · exact bot_le
private theorem FeitSibleyData.internalDirectProduct_Q
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) :
    Section2.IsInternalDirectProduct d.Q d.S d.Q1 := by
  let : d.Q1.Normal := d.Q1_normal
  refine
    { left_le := d.S_le_Q
      right_le := d.Q1_le_Q
      commute := by
        intro h hh k hk
        simpa only using d.S_commutes_Q1 h k hh hk
      inf_eq_bot := d.S_disjoint_Q1.eq_bot
      mul_surjective := ?_ }
  intro q hq
  have hqSup : q ∈ d.S ⊔ d.Q1 := by
    rw [d.Q_eq_S_sup_Q1]
    exact hq
  rcases Subgroup.mem_sup_of_normal_right.mp hqSup with
    ⟨s, hs, q1, hq1, hprod⟩
  exact ⟨s, hs, q1, hq1, hprod.symm⟩
private theorem FeitSibleyData.S_normal
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) :
    d.S.Normal := by
  let : d.Q.Normal := d.Q_normal
  let S0 : Subgroup d.Q := d.S.subgroupOf d.Q
  have hdir := d.internalDirectProduct_Q
  have hS0normal : S0.Normal := by
    refine ⟨?_⟩
    intro n hn q
    rcases hdir.mul_surjective (q : d.H) q.property with
      ⟨s, hs, k, hk, hq⟩
    change (q : d.H) * (n : d.H) * (q : d.H)⁻¹ ∈ d.S
    have hcomm : (n : d.H) * k = k * (n : d.H) :=
      hdir.commute (n : d.H) hn k hk
    have hconjK : k * (n : d.H) * k⁻¹ = n := by
      rw [← hcomm]
      simp
    rw [hq, mul_inv_rev]
    rw [show (s * k) * (n : d.H) * (k⁻¹ * s⁻¹) =
        s * (k * (n : d.H) * k⁻¹) * s⁻¹ by group]
    rw [hconjK]
    exact d.S.mul_mem (d.S.mul_mem hs hn) (d.S.inv_mem hs)
  let : S0.Normal := hS0normal
  let hsemi : Section2.IsInternalSemidirectProduct d.Q d.S d.Q1 :=
    { left_le := hdir.left_le
      right_le := hdir.right_le
      right_normalizes_left := by
        intro k hk s hs
        have hcomm : s * k = k * s := hdir.commute s hs k hk
        simp [Section2.conjBy, ← hcomm, hs]
      inf_eq_bot := hdir.inf_eq_bot
      mul_surjective := hdir.mul_surjective }
  have hcardS0 : Nat.card S0 = Nat.card d.S := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe d.S_le_Q).toEquiv
  have hindexS0 : S0.index = Nat.card d.Q1 := by
    simpa [S0, Subgroup.relIndex] using
      Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  let pi : Set Nat.Primes := {p | p.val ∣ Nat.card d.S}
  have hHall : IsHallSubgroup pi S0 := by
    refine isHallSubgroup_of pi S0 ?_ ?_
    · intro p hp
      rw [hcardS0] at hp
      simpa [pi] using hp
    · intro p hp hpIndex
      have hpS : p.val ∣ Nat.card d.S := by
        simpa [pi] using hp
      have hpQ1 : p.val ∣ Nat.card d.Q1 := by
        simpa [hindexS0] using hpIndex
      have hcop : Nat.Coprime p.val p.val :=
        Nat.Coprime.of_dvd hpS hpQ1 d.card_S_coprime_card_Q1
      exact p.property.ne_one ((Nat.coprime_self p.val).mp hcop)
  have hchar : S0.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    exact hHall.eq_of_normal (hHall.map_mulAut e)
  let : S0.Characteristic := hchar
  have hmapNormal : (S0.map d.Q.subtype).Normal := inferInstance
  have hmap : S0.map d.Q.subtype = d.S := by
    ext x
    simp [S0, d.S_le_Q]
  rw [hmap] at hmapNormal
  exact hmapNormal

private theorem map_derivedSubgroup_internalDirectProduct_eq_sup
    {G : Type*} [Group G] {W W1 W2 : Subgroup G}
    (h : Section2.IsInternalDirectProduct W W1 W2) :
    Subgroup.map W.subtype (derivedSubgroup W) =
      Subgroup.map W1.subtype (derivedSubgroup W1) ⊔
        Subgroup.map W2.subtype (derivedSubgroup W2) := by
  let e : W1 × W2 ≃* W := Section3.internalDirectProductMulEquiv h
  have hder_e :
      Subgroup.map e.toMonoidHom (derivedSubgroup (W1 × W2)) =
        derivedSubgroup W := by
    change (derivedSeries (W1 × W2) 1).map e.toMonoidHom =
      derivedSeries W 1
    exact map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 1
  have hder_prod :
      derivedSubgroup (W1 × W2) =
        (derivedSubgroup W1).prod (derivedSubgroup W2) := by
    simpa [derivedSubgroup, derivedSeries_one] using
      (Subgroup.commutator_prod_prod
        (⊤ : Subgroup W1) (⊤ : Subgroup W1)
        (⊤ : Subgroup W2) (⊤ : Subgroup W2))
  let F : W1 × W2 →* G := W.subtype.comp e.toMonoidHom
  have haxis1 (x : W1) :
      F (MonoidHom.inl W1 W2 x) = (x : G) := by
    change ((e (MonoidHom.inl W1 W2 x) : W) : G) = (x : G)
    simpa [e] using congrArg Subtype.val
      (Section3.internalDirectProductMulEquiv_apply_inl h x)
  have haxis2 (x : W2) :
      F (MonoidHom.inr W1 W2 x) = (x : G) := by
    change ((e (MonoidHom.inr W1 W2 x) : W) : G) = (x : G)
    simpa [e] using congrArg Subtype.val
      (Section3.internalDirectProductMulEquiv_apply_inr h x)
  have hmap_prod :
      Subgroup.map F
          ((derivedSubgroup W1).prod (derivedSubgroup W2)) =
        Subgroup.map W1.subtype (derivedSubgroup W1) ⊔
          Subgroup.map W2.subtype (derivedSubgroup W2) := by
    apply le_antisymm
    · refine (Subgroup.map_le_iff_le_comap).2 ?_
      rw [Subgroup.prod_le_iff]
      constructor
      · refine (Subgroup.map_le_iff_le_comap).2 ?_
        intro x hx
        change F (MonoidHom.inl W1 W2 x) ∈
          Subgroup.map W1.subtype (derivedSubgroup W1) ⊔
            Subgroup.map W2.subtype (derivedSubgroup W2)
        rw [haxis1 x]
        have hm :
            (x : G) ∈ Subgroup.map W1.subtype (derivedSubgroup W1) :=
          Subgroup.mem_map_of_mem W1.subtype hx
        exact
          (show Subgroup.map W1.subtype (derivedSubgroup W1) ≤ _ from
            le_sup_left) hm
      · refine (Subgroup.map_le_iff_le_comap).2 ?_
        intro x hx
        change F (MonoidHom.inr W1 W2 x) ∈
          Subgroup.map W1.subtype (derivedSubgroup W1) ⊔
            Subgroup.map W2.subtype (derivedSubgroup W2)
        rw [haxis2 x]
        have hm :
            (x : G) ∈ Subgroup.map W2.subtype (derivedSubgroup W2) :=
          Subgroup.mem_map_of_mem W2.subtype hx
        exact
          (show Subgroup.map W2.subtype (derivedSubgroup W2) ≤ _ from
            le_sup_right) hm
    · apply sup_le
      · refine (Subgroup.map_le_iff_le_comap).2 ?_
        intro x hx
        change (x : G) ∈
          Subgroup.map F
            ((derivedSubgroup W1).prod (derivedSubgroup W2))
        exact Subgroup.mem_map.mpr
          ⟨MonoidHom.inl W1 W2 x, ⟨hx, Subgroup.one_mem _⟩, haxis1 x⟩
      · refine (Subgroup.map_le_iff_le_comap).2 ?_
        intro x hx
        change (x : G) ∈
          Subgroup.map F
            ((derivedSubgroup W1).prod (derivedSubgroup W2))
        exact Subgroup.mem_map.mpr
          ⟨MonoidHom.inr W1 W2 x, ⟨Subgroup.one_mem _, hx⟩, haxis2 x⟩
  calc
    Subgroup.map W.subtype (derivedSubgroup W) =
        Subgroup.map W.subtype
          (Subgroup.map e.toMonoidHom
            (derivedSubgroup (W1 × W2))) := by
      rw [hder_e]
    _ = Subgroup.map F (derivedSubgroup (W1 × W2)) := by
      rw [Subgroup.map_map]
    _ = Subgroup.map F
        ((derivedSubgroup W1).prod (derivedSubgroup W2)) := by
      rw [hder_prod]
    _ = _ := hmap_prod

private theorem FeitSibleyData.map_derivedSubgroup_Q_eq_sup
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) :
    Subgroup.map (d.Q.subtype : d.Q →* d.H) (derivedSubgroup d.Q) =
      Subgroup.map (d.S.subtype : d.S →* d.H) (derivedSubgroup d.S) ⊔
        Subgroup.map (d.Q1.subtype : d.Q1 →* d.H)
          (derivedSubgroup d.Q1) :=
  map_derivedSubgroup_internalDirectProduct_eq_sup
    d.internalDirectProduct_Q
private theorem FeitSibleyData.exists_exceptional_mem_derived_kernel
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hsolv : Group.IsSolvable d.Q1)
    (hprod : Section2.IsInternalDirectProduct d.Q d.S d.Q1) :
    ∃ chi : ClassFunction d.H,
      chi ∈ chars ∧
        subgroupInKernel' chi
          (Subgroup.map (d.Q.subtype : d.Q →* d.H) (derivedSubgroup d.Q)) := by
  let : Group.IsSolvable d.Q1 := hsolv
  have hQ1ne : d.Q1 ≠ ⊥ := by
    intro hQ1
    apply d.Q1_not_two_group
    exact hQ1.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
  let : Nontrivial d.Q1 :=
    (Subgroup.nontrivial_iff_ne_bot d.Q1).2 hQ1ne
  rcases Section6.exists_nontrivial_linear_character_of_solvable d.Q1 with
    ⟨eta, heta⟩
  let phi : ClassFunction d.Q :=
    Section3.linearCharacterProductOverInternalDirectProduct hprod 1 eta
  have hphiIrr : IsIrreducibleCharacterOnGroup phi :=
    Section3.linearCharacterProductOverInternalDirectProduct_irreducible
      hprod 1 eta
  have hphiNotQ1 :
      ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q) := by
    intro hker
    exact heta
      ((Section3.linearCharacterProductOverInternalDirectProduct_leftKernel_iff
        hprod 1 eta).mp hker)
  let : d.Q.Normal := d.Q_normal
  let A : Subgroup d.H :=
    Subgroup.map (d.Q.subtype : d.Q →* d.H) (derivedSubgroup d.Q)
  have hAleQ : A ≤ d.Q := by
    simpa [A] using Subgroup.map_subtype_le (derivedSubgroup d.Q)
  have : A.Normal := by
    dsimp [A]
    infer_instance
  have hAsub : A.subgroupOf d.Q = derivedSubgroup d.Q := by
    dsimp [A]
    exact subgroupOf_map_subtype_eq (derivedSubgroup d.Q)
  have hphiA : subgroupInKernel' phi (A.subgroupOf d.Q) := by
    intro a
    have ha : (a : d.Q) ∈ derivedSubgroup d.Q := by
      rw [← hAsub]
      exact a.property
    have hker :
        Section3.internalDirectProductLinearCharacter hprod 1 eta (a : d.Q) = 1 :=
      Abelianization.commutator_subset_ker
        (Section3.internalDirectProductLinearCharacter hprod 1 eta) ha
    have hkerC := congrArg (fun z : ℂˣ => (z : ℂ)) hker
    simpa [phi, Section3.linearCharacterProductOverInternalDirectProduct,
      Section3.linearCharacterProductOverInternalDirectProduct_degree
        hprod 1 eta] using hkerC
  rcases hphiIrr with ⟨n, rho, hrho, hphiEq⟩
  have hrhoA : subgroupInKernel' rho.character (A.subgroupOf d.Q) := by
    simpa [hphiEq] using hphiA
  have hindA : subgroupInKernel' (inducedCF d.Q rho.character) A :=
    (Section1.proposition_1_6_a d.Q A hAleQ rho).mp hrhoA
  have hindPhi : subgroupInKernel' (inducedCF d.Q phi) A := by
    simpa [hphiEq] using hindA
  refine ⟨inducedCF d.Q phi, ?_, ?_⟩
  · exact (lemma_2_a d chars hchars (inducedCF d.Q phi)).mpr
      ⟨phi,
        Section3.linearCharacterProductOverInternalDirectProduct_irreducible
          hprod 1 eta,
        hphiNotQ1, rfl⟩
  · simpa [A] using hindPhi
private theorem degree_eq_one_of_irreducible_subgroupInKernel_derived_appendixIV
    {G : Type u} [Group G] [Finite G]
    {theta : ClassFunction G}
    (hthetaIrr : IsIrreducibleCharacterOnGroup theta)
    (hker : subgroupInKernel' theta (derivedSubgroup G)) :
    degree theta = (1 : Complex) := by
  classical
  rcases hthetaIrr with ⟨n, rho, hrhoIrr, hthetaEq⟩
  have hthetaKerRho :
      subgroupInKernel' rho.character (derivedSubgroup G) := by
    simpa [hthetaEq] using hker
  have hkerRep :
      subgroupInRepresentationKernel rho (derivedSubgroup G) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel rho
      (derivedSubgroup G)).mp hthetaKerRho
  let rhoQ : Representation Complex (G ⧸ derivedSubgroup G) (Fin n → Complex) :=
    quotientRepresentationOfKernelSubgroup rho (derivedSubgroup G) hkerRep
  let q : G →* G ⧸ derivedSubgroup G :=
    QuotientGroup.mk' (derivedSubgroup G)
  have hcomp : rhoQ.comp q = rho := by
    apply MonoidHom.ext
    intro g
    exact quotientRepresentationOfKernelSubgroup_mk rho
      (derivedSubgroup G) hkerRep g
  have hrhoQIrr : Representation.IsIrreducible rhoQ := by
    apply Section6.representation_isIrreducible_of_comp_surjective rhoQ q
      (QuotientGroup.mk'_surjective (derivedSubgroup G))
    simpa [← hcomp] using hrhoIrr
  have : IsMulCommutative (G ⧸ derivedSubgroup G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (by
      intro x hx
      exact hx)
  have hn : n = 1 := by
    have : Representation.IsIrreducible rhoQ := hrhoQIrr
    simpa using
      (Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
        (ρ := rhoQ))
  rw [hthetaEq, degree_representation_character]
  simp [hn]
private theorem
    derivedSubgroup_le_representation_ker_of_finrank_one_appendixIV
    {G V : Type*} [Group G] [AddCommGroup V] [Module Complex V]
    [FiniteDimensional Complex V]
    (rho : Representation Complex G V)
    (hfin : Module.finrank Complex V = 1) :
    derivedSubgroup G ≤ rho.ker := by
  have hscalar (g : G) :
      ∃ a : Complex, ∀ v : V, rho g v = a • v := by
    obtain ⟨a, ha, _⟩ :=
      LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
        (R := Complex) (M := V) hfin (rho g)
    refine ⟨a, ?_⟩
    intro v
    simpa using congrArg (fun f : Module.End Complex V => f v) ha
  have hmulComm (g1 g2 : G) : rho g1 * rho g2 = rho g2 * rho g1 := by
    refine LinearMap.ext fun v : V => ?_
    obtain ⟨a1, ha1⟩ := hscalar g1
    obtain ⟨a2, ha2⟩ := hscalar g2
    calc
      (rho g1 * rho g2) v = rho g1 (rho g2 v) := rfl
      _ = rho g1 (a2 • v) := by rw [ha2]
      _ = a2 • rho g1 v := by rw [map_smul]
      _ = a2 • (a1 • v) := by rw [ha1]
      _ = (a2 * a1) • v := by rw [smul_smul]
      _ = (a1 * a2) • v := by rw [mul_comm]
      _ = a1 • (a2 • v) := by rw [smul_smul]
      _ = a1 • rho g2 v := by rw [ha2]
      _ = rho g2 (a1 • v) := by rw [map_smul]
      _ = rho g2 (rho g1 v) := by rw [ha1]
      _ = (rho g2 * rho g1) v := rfl
  have hcomm : commutator G ≤ rho.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro c ⟨g1, g2, rfl⟩
    change rho (g1 * g2 * g1⁻¹ * g2⁻¹) = 1
    have hcomm' : rho g2 * rho g1⁻¹ = rho g1⁻¹ * rho g2 := by
      calc
        rho g2 * rho g1⁻¹ = rho (g2 * g1⁻¹) :=
          (map_mul rho g2 g1⁻¹).symm
        _ = rho (g1⁻¹ * g2) := by
          have h := hmulComm g2 g1⁻¹
          simpa [map_mul] using h
        _ = rho g1⁻¹ * rho g2 := map_mul rho g1⁻¹ g2
    have hg1 : rho g1 * rho g1⁻¹ = 1 := by
      calc
        rho g1 * rho g1⁻¹ = rho (g1 * g1⁻¹) :=
          (map_mul rho g1 g1⁻¹).symm
        _ = 1 := by simp
    have hg2 : rho g2 * rho g2⁻¹ = 1 := by
      calc
        rho g2 * rho g2⁻¹ = rho (g2 * g2⁻¹) :=
          (map_mul rho g2 g2⁻¹).symm
        _ = 1 := by simp
    calc
      rho (g1 * g2 * g1⁻¹ * g2⁻¹) =
          rho g1 * (rho g2 * rho g1⁻¹) * rho g2⁻¹ := by
            simp [map_mul, mul_assoc]
      _ = rho g1 * (rho g1⁻¹ * rho g2) * rho g2⁻¹ := by
        rw [hcomm']
      _ = (rho g1 * rho g1⁻¹) * (rho g2 * rho g2⁻¹) := by
        simp [mul_assoc]
      _ = 1 := by simp [hg1, hg2]
  simpa [commutator, derivedSubgroup, derivedSeries_one] using hcomm

set_option maxHeartbeats 800000 in
private theorem FeitSibleyData.map_derivedSubgroup_Q_eq_S_of_Q1_commutative
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (hab : ∀ x y : d.Q1, x * y = y * x) :
    Subgroup.map (d.Q.subtype : d.Q →* d.H) (derivedSubgroup d.Q) =
      Subgroup.map (d.S.subtype : d.S →* d.H) (derivedSubgroup d.S) := by
  have hcomm : ⁅d.Q, d.Q⁆ = ⁅d.S, d.S⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      let hprod := d.internalDirectProduct_Q
      let e : d.S × d.Q1 ≃* d.Q :=
        Section3.internalDirectProductMulEquiv hprod
      let xQ : d.Q := ⟨x, hx⟩
      let yQ : d.Q := ⟨y, hy⟩
      let px : d.S × d.Q1 := e.symm xQ
      let py : d.S × d.Q1 := e.symm yQ
      have hright : ⁅px.2, py.2⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hab px.2 py.2)
      have hprodComm :
          ⁅px, py⁆ = MonoidHom.inl d.S d.Q1 ⁅px.1, py.1⁆ := by
        apply Prod.ext
        · simp [MonoidHom.inl_apply, commutatorElement_def]
        · have h_comm_snd : (⁅px, py⁆).2 = ⁅px.2, py.2⁆ := by
            calc
              (⁅px, py⁆).2 = (px * py * px⁻¹ * py⁻¹).2 := rfl
              _ = px.2 * py.2 * px.2⁻¹ * py.2⁻¹ := rfl
              _ = ⁅px.2, py.2⁆ := rfl
          calc
            (⁅px, py⁆).2 = ⁅px.2, py.2⁆ := h_comm_snd
            _ = 1 := hright
            _ = ((MonoidHom.inl d.S d.Q1 ⁅px.1, py.1⁆).2) := by
              dsimp [MonoidHom.inl]
      have heq := map_commutatorElement e.toMonoidHom px py
      rw [hprodComm] at heq
      change e (MonoidHom.inl d.S d.Q1 ⁅px.1, py.1⁆) =
        ⁅e px, e py⁆ at heq
      have hinl :
          e (MonoidHom.inl d.S d.Q1 ⁅px.1, py.1⁆) =
            ⟨((⁅px.1, py.1⁆ : d.S) : d.H),
              hprod.left_le (⁅px.1, py.1⁆ : d.S).property⟩ :=
        Section3.internalDirectProductMulEquiv_apply_inl hprod ⁅px.1, py.1⁆
      rw [hinl] at heq
      have heqH := congrArg Subtype.val heq
      have hxy :
          ⁅x, y⁆ = ⁅(px.1 : d.H), (py.1 : d.H)⁆ := by
        -- heq after hinl rewrite: ⟨(⁅px.1, py.1⁆ : d.H), ...⟩ = (⁅xQ, yQ⁆ : d.Q)
        -- heqH: (⁅px.1, py.1⁆ : d.H) = (⁅xQ, yQ⁆ : d.H)
        -- heqH.symm: (⁅xQ, yQ⁆ : d.H) = (⁅px.1, py.1⁆ : d.H)
        -- need: ⁅x, y⁆ = ⁅(px.1 : d.H), (py.1 : d.H)⁆
        have hxQ_val : (d.Q.subtype : d.Q →* d.H) xQ = x := rfl
        have hyQ_val : (d.Q.subtype : d.Q →* d.H) yQ = y := rfl
        have hm1 : (d.Q.subtype : d.Q →* d.H) (xQ * yQ * xQ⁻¹ * yQ⁻¹) = ⁅x, y⁆ := by
          calc
            (d.Q.subtype : d.Q →* d.H) (xQ * yQ * xQ⁻¹ * yQ⁻¹)
                = (d.Q.subtype : d.Q →* d.H) xQ * (d.Q.subtype : d.Q →* d.H) yQ * (d.Q.subtype : d.Q →* d.H) xQ⁻¹ * (d.Q.subtype : d.Q →* d.H) yQ⁻¹ := by
              simp [map_mul, map_inv, mul_assoc]
            _ = x * y * x⁻¹ * y⁻¹ := by
              simp [hxQ_val, hyQ_val, map_inv (d.Q.subtype : d.Q →* d.H)]
            _ = ⁅x, y⁆ := by
              simp [commutatorElement_def, mul_assoc]
        have hm2 : (d.S.subtype : d.S →* d.H) (px.1 * py.1 * px.1⁻¹ * py.1⁻¹) = ⁅(px.1 : d.H), (py.1 : d.H)⁆ := by
          calc
            (d.S.subtype : d.S →* d.H) (px.1 * py.1 * px.1⁻¹ * py.1⁻¹)
                = (d.S.subtype : d.S →* d.H) ((px.1 * py.1) * (px.1⁻¹ * py.1⁻¹)) := by simp [mul_assoc]
            _ = (d.S.subtype : d.S →* d.H) (px.1 * py.1) * (d.S.subtype : d.S →* d.H) (px.1⁻¹ * py.1⁻¹) := by
              rw [map_mul (d.S.subtype : d.S →* d.H) (px.1 * py.1) (px.1⁻¹ * py.1⁻¹)]
            _ = ((d.S.subtype : d.S →* d.H) px.1 * (d.S.subtype : d.S →* d.H) py.1) * ((d.S.subtype : d.S →* d.H) px.1⁻¹ * (d.S.subtype : d.S →* d.H) py.1⁻¹) := by
              simp [map_mul, map_inv, mul_assoc]
            _ = (d.S.subtype : d.S →* d.H) px.1 * (d.S.subtype : d.S →* d.H) py.1 * (d.S.subtype : d.S →* d.H) px.1⁻¹ * (d.S.subtype : d.S →* d.H) py.1⁻¹ := by simp [mul_assoc]
            _ = (px.1 : d.H) * (py.1 : d.H) * (px.1 : d.H)⁻¹ * (py.1 : d.H)⁻¹ := by simp
            _ = ⁅(px.1 : d.H), (py.1 : d.H)⁆ := by simp [commutatorElement_def, mul_assoc]
        have h_symm : (xQ * yQ * xQ⁻¹ * yQ⁻¹ : d.H) = (px.1 * py.1 * px.1⁻¹ * py.1⁻¹ : d.H) := by
          calc
            (xQ * yQ * xQ⁻¹ * yQ⁻¹ : d.H) = (xQ.1 * yQ.1 * xQ.1⁻¹ * yQ.1⁻¹ : d.H) := by
              simp [mul_assoc]
            _ = (px.1.1 * py.1.1 * px.1.1⁻¹ * py.1.1⁻¹ : d.H) := by
              -- Use heqH.symm: commutator in d.Q coerced to d.H equals commutator in d.S coerced to d.H
              -- Expand using the definition of commutator: xQ.1 * yQ.1 * xQ.1⁻¹ * yQ.1⁻¹ = (⁅xQ, yQ⁆ : d.H)
              -- and px.1.1 * py.1.1 * px.1.1⁻¹ * py.1.1⁻¹ = (⁅px.1, py.1⁆ : d.H)
              -- Since heqH.symm gives (⁅xQ, yQ⁆ : d.H) = (⁅px.1, py.1⁆ : d.H)
              -- we need to expand both sides
              calc
                (xQ.1 * yQ.1 * xQ.1⁻¹ * yQ.1⁻¹ : d.H) = ((xQ * yQ * xQ⁻¹ * yQ⁻¹ : d.Q) : d.H) := by
                  simp [mul_assoc]
                _ = ((e px * e py * (e px)⁻¹ * (e py)⁻¹ : d.Q) : d.H) := by
                  simp [px, py, MulEquiv.apply_symm_apply, mul_assoc]
                _ = (px.1 * py.1 * px.1⁻¹ * py.1⁻¹ : d.H) := by
                  simpa [commutatorElement_def, mul_assoc] using heqH.symm
                _ = ((px.1 * py.1 * px.1⁻¹ * py.1⁻¹ : d.S) : d.H) := rfl
                _ = (px.1.1 * py.1.1 * px.1.1⁻¹ * py.1.1⁻¹ : d.H) := by
                  simp [mul_assoc]
        calc
          ⁅x, y⁆ = (x * y) * (x⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
          _ = (d.Q.subtype : d.Q →* d.H) (xQ * yQ * xQ⁻¹ * yQ⁻¹) := by
            simp [hxQ_val, hyQ_val, map_mul, map_inv, mul_assoc]
          _ = (xQ * yQ * xQ⁻¹ * yQ⁻¹ : d.H) := rfl
          _ = (px.1 * py.1 * px.1⁻¹ * py.1⁻¹ : d.H) := h_symm
          _ = (d.S.subtype : d.S →* d.H) (px.1 * py.1 * px.1⁻¹ * py.1⁻¹) := by simp
          _ = ⁅(px.1 : d.H), (py.1 : d.H)⁆ := hm2
      rw [hxy]
      exact Subgroup.commutator_mem_commutator px.1.property py.1.property
    · exact Subgroup.commutator_mono d.S_le_Q d.S_le_Q
  calc
    Subgroup.map d.Q.subtype (derivedSubgroup d.Q) = ⁅d.Q, d.Q⁆ := by
      simpa [derivedSubgroup, commutator] using
        Subgroup.map_subtype_commutator d.Q
    _ = ⁅d.S, d.S⁆ := hcomm
    _ = Subgroup.map d.S.subtype (derivedSubgroup d.S) := by
      symm
      simpa [derivedSubgroup, commutator] using
        Subgroup.map_subtype_commutator d.S
private theorem FeitSibleyData.degree_eq_relIndex_of_exceptional_derived_kernel
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (eta : ClassFunction d.H) (hetaChars : eta ∈ chars)
    (hetaKernel :
      subgroupInKernel' eta
        (Subgroup.map (d.Q.subtype : d.Q →* d.H)
          (derivedSubgroup d.Q))) :
    degree eta =
      (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
  rcases (lemma_2_a d chars hchars eta).mp hetaChars with
    ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
  let : d.Q.Normal := d.Q_normal
  let A : Subgroup d.H :=
    Subgroup.map (d.Q.subtype : d.Q →* d.H)
      (derivedSubgroup d.Q)
  have hAle : A ≤ d.Q := by
    simpa [A] using
      Subgroup.map_subtype_le (derivedSubgroup d.Q)
  have : A.Normal := by
    dsimp [A]
    infer_instance
  have hAsub :
      A.subgroupOf d.Q = derivedSubgroup d.Q := by
    dsimp [A]
    exact subgroupOf_map_subtype_eq (derivedSubgroup d.Q)
  rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
  have hindKernelPhi :
      subgroupInKernel' (inducedCF d.Q phi) A := by
    rw [hind]
    simpa [A] using hetaKernel
  have hindKernel :
      subgroupInKernel' (inducedCF d.Q rho.character) A := by
    simpa [hphiEq] using hindKernelPhi
  have hrhoKernel :
      subgroupInKernel' rho.character (A.subgroupOf d.Q) :=
    (Section1.proposition_1_6_a d.Q A hAle rho).mpr hindKernel
  have hphiKernel :
      subgroupInKernel' phi (derivedSubgroup d.Q) := by
    simpa [hphiEq, hAsub] using hrhoKernel
  have hphiDegree : degree phi = (1 : Complex) :=
    degree_eq_one_of_irreducible_subgroupInKernel_derived_appendixIV
      ⟨n, rho, hrhoIrr, hphiEq⟩ hphiKernel
  rw [← hind, degree_inducedClassFunction d.Q phi, hphiDegree]
  simp [Subgroup.relIndex_top_right]
private theorem degree_re_sq_sum_mono_appendixIV
    {L : Type*} [Group L]
    {U V : Finset (ClassFunction L)}
    (hUV : U ⊆ V) :
    (∑ chi : U, (degree (chi : ClassFunction L)).re ^ 2) ≤
      ∑ chi : V, (degree (chi : ClassFunction L)).re ^ 2 := by
  classical
  rw [← Finset.sum_subtype (s := U)
    (p := fun chi : ClassFunction L => chi ∈ U)
    (f := fun chi : ClassFunction L => (degree chi).re ^ 2) (by simp)]
  rw [← Finset.sum_subtype (s := V)
    (p := fun chi : ClassFunction L => chi ∈ V)
    (f := fun chi : ClassFunction L => (degree chi).re ^ 2) (by simp)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hUV
    (by
      intro chi _hchiV _hchiU
      positivity)

private theorem exists_degree_obstruction_of_not_coherent_appendixIV
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (U V : Finset (ClassFunction H))
    (tau : ClassFunction H →ₗ[Complex] ClassFunction G)
    (hUV : U ⊆ V)
    (chi0 : ClassFunction H) (hchi0 : chi0 ∈ U)
    (hirr : ∀ chi : V,
      IsIrreducibleCharacterOnGroup (chi : ClassFunction H))
    (hisometry :
      isCFLinearIsometryOnSpanOn V puncturedSet tau)
    (htarget :
      ∀ phi : ClassFunction H,
        integerSpanOn V puncturedSet phi →
          Theory.Character.IsVirtualCharacter (tau phi) ∧
            supportedOn (tau phi) puncturedSet)
    (hdiv : ∀ psi : ClassFunction H, psi ∈ V →
      ∃ n : Nat, degree psi = (n : Complex) * degree chi0)
    (hcohU : IsCoherentTriple puncturedSet U tau)
    (hnotcohV : ¬ IsCoherentTriple puncturedSet V tau) :
    ∃ psi : ClassFunction H,
      psi ∈ V ∧ psi ∉ U ∧
        (∑ chi : U, (degree (chi : ClassFunction H)).re ^ 2) ≤
          2 * (degree psi).re * (degree chi0).re := by
  classical
  by_contra hno
  push Not at hno
  let D : Finset (ClassFunction H) := V \ U
  have hcoh :
      ∀ W : Finset (ClassFunction H), W ⊆ D →
        IsCoherentTriple puncturedSet (U ∪ W) tau := by
    intro W
    induction W using Finset.induction_on with
    | empty =>
        intro _h
        simpa using hcohU
    | @insert psi W hpsiW ih =>
        intro hins
        have hWD : W ⊆ D := by
          intro chi hchi
          exact hins (Finset.mem_insert_of_mem hchi)
        have hpsiD : psi ∈ D :=
          hins (Finset.mem_insert_self psi W)
        have hpsiV : psi ∈ V := (Finset.mem_sdiff.mp hpsiD).1
        have hpsiU : psi ∉ U := (Finset.mem_sdiff.mp hpsiD).2
        have hcohCurrent :
            IsCoherentTriple puncturedSet (U ∪ W) tau :=
          ih hWD
        have hpsiCurrent : psi ∉ U ∪ W := by
          simp [hpsiU, hpsiW]
        have hcurrentSub : U ∪ W ⊆ V := by
          exact Finset.union_subset hUV
            (fun chi hchi => (Finset.mem_sdiff.mp (hWD hchi)).1)
        have hconsSub :
            (U ∪ W).cons psi hpsiCurrent ⊆ V := by
          intro chi hchi
          rw [Finset.mem_cons] at hchi
          rcases hchi with rfl | hchi
          · exact hpsiV
          · exact hcurrentSub hchi
        have hirrCurrent :
            ∀ chi : ↥(U ∪ W),
              IsIrreducibleCharacterOnGroup
                (chi : ClassFunction H) := by
          intro chi
          exact hirr ⟨chi, hcurrentSub chi.property⟩
        have hirrPsi :
            IsIrreducibleCharacterOnGroup psi :=
          hirr ⟨psi, hpsiV⟩
        have hisoCons :
            isCFLinearIsometryOnSpanOn
              ((U ∪ W).cons psi hpsiCurrent) puncturedSet tau := by
          intro phi theta hphi htheta
          exact hisometry phi theta
            (integerSpanOn_mono hconsSub hphi)
            (integerSpanOn_mono hconsSub htheta)
        have htargetCons :
            ∀ phi : ClassFunction H,
              integerSpanOn ((U ∪ W).cons psi hpsiCurrent)
                  puncturedSet phi →
                Theory.Character.IsVirtualCharacter (tau phi) ∧
                  supportedOn (tau phi) puncturedSet := by
          intro phi hphi
          exact htarget phi (integerSpanOn_mono hconsSub hphi)
        have hsumBase :
            (∑ chi : U,
                (degree (chi : ClassFunction H)).re ^ 2) ≤
              ∑ chi : ↥(U ∪ W),
                (degree (chi : ClassFunction H)).re ^ 2 :=
          degree_re_sq_sum_mono_appendixIV
            (fun chi hchi => Finset.mem_union_left W hchi)
        have hgrowthBase :
            2 * (degree psi).re * (degree chi0).re <
              ∑ chi : U,
                (degree (chi : ClassFunction H)).re ^ 2 := by
          exact hno psi hpsiV hpsiU
        have hgrowth :
            2 * (degree psi).re * (degree chi0).re <
              ∑ chi : ↥(U ∪ W),
                (degree (chi : ClassFunction H)).re ^ 2 :=
          lt_of_lt_of_le hgrowthBase hsumBase
        have hnew :=
          lemma_1_a H (U ∪ W) psi chi0
            (Finset.mem_union_left W hchi0) hpsiCurrent tau
            hirrCurrent hirrPsi hisoCons htargetCons hcohCurrent
            (hdiv psi hpsiV) hgrowth
        simpa [Finset.cons_eq_insert, Finset.union_insert] using hnew
  have hDsub : D ⊆ D := fun _ h => h
  have hcohV := hcoh D hDsub
  have hUD : U ∪ D = V := by
    ext chi
    simp only [D, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (hchiU | ⟨hchiV, _hchiU⟩)
      · exact hUV hchiU
      · exact hchiV
    · intro hchiV
      by_cases hchiU : chi ∈ U
      · exact Or.inl hchiU
      · exact Or.inr ⟨hchiV, hchiU⟩
  exact hnotcohV (hUD ▸ hcohV)

private theorem irreducible_finrank_sq_le_index_prod_centerModulo_appendixIV
    {A C G V : Type*} [Group A] [Group C] [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : A × C ≃* G) (N : Subgroup C) [N.Normal]
    (rho : Representation ℂ G V) [rho.IsIrreducible]
    (hker : ∀ x : (commutator A).prod N, rho (e x) = 1) :
    Module.finrank ℂ V ^ 2 ≤
      (Subgroup.comap (QuotientGroup.mk' N)
        (Subgroup.center (C ⧸ N))).index := by
  classical
  let Z0 := Subgroup.comap (QuotientGroup.mk' N)
    (Subgroup.center (C ⧸ N))
  let K := Subgroup.map e.toMonoidHom ((commutator A).prod N)
  let T := Subgroup.map e.toMonoidHom ((⊤ : Subgroup A).prod Z0)
  have hKker : ∀ k : K, rho k = 1 := by
    intro k
    rcases k.property with ⟨x, hx, hxk⟩
    rw [← hxk]
    exact hker ⟨x, hx⟩
  have hcentral : Theory.Character.IsCentralModulo K T := by
    intro x hx y
    rcases hx with ⟨xz, hxz, hxeq⟩
    rw [← hxeq]
    let yz := e.symm y
    have hyeq : e yz = y := e.apply_symm_apply y
    rw [← hyeq]
    change ⁅e.toMonoidHom xz, e.toMonoidHom yz⁆ ∈ K
    rw [← map_commutatorElement e.toMonoidHom]
    apply Subgroup.mem_map.mpr
    refine ⟨⁅xz, yz⁆, ?_, rfl⟩
    change ⁅xz.1, yz.1⁆ ∈ commutator A ∧ ⁅xz.2, yz.2⁆ ∈ N
    constructor
    · exact Subgroup.commutator_mem_commutator (by simp) (by simp)
    · apply (QuotientGroup.eq_one_iff (N := N) ⁅xz.2, yz.2⁆).mp
      change (QuotientGroup.mk' N) ⁅xz.2, yz.2⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hxz.2 yz.2).symm
  have hbound :=
    Theory.Character.irreducible_finrank_sq_le_index_of_centralModulo_kernel
      rho K T hKker hcentral
  simpa [T, Z0, Subgroup.index_map_equiv, Subgroup.index_prod] using hbound
private theorem irreducible_finrank_sq_le_centerModulo_index_mul_center_index_appendixIV
    {A C G V : Type*} [Group A] [Group C] [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : A × C ≃* G) (N : Subgroup A) [N.Normal]
    (rho : Representation ℂ G V) [rho.IsIrreducible]
    (hker : ∀ x : N.prod (⊥ : Subgroup C), rho (e x) = 1) :
    Module.finrank ℂ V ^ 2 ≤
      (Subgroup.comap (QuotientGroup.mk' N)
        (Subgroup.center (A ⧸ N))).index *
      (Subgroup.center C).index := by
  classical
  let Z0 := Subgroup.comap (QuotientGroup.mk' N)
    (Subgroup.center (A ⧸ N))
  let K := Subgroup.map e.toMonoidHom (N.prod (⊥ : Subgroup C))
  let T := Subgroup.map e.toMonoidHom (Z0.prod (Subgroup.center C))
  have hKker : ∀ k : K, rho k = 1 := by
    intro k
    rcases k.property with ⟨x, hx, hxk⟩
    rw [← hxk]
    exact hker ⟨x, hx⟩
  have hcentral : Theory.Character.IsCentralModulo K T := by
    intro x hx y
    rcases hx with ⟨xz, hxz, hxeq⟩
    rw [← hxeq]
    let yz := e.symm y
    have hyeq : e yz = y := e.apply_symm_apply y
    rw [← hyeq]
    change ⁅e.toMonoidHom xz, e.toMonoidHom yz⁆ ∈ K
    rw [← map_commutatorElement e.toMonoidHom]
    apply Subgroup.mem_map.mpr
    refine ⟨⁅xz, yz⁆, ?_, rfl⟩
    change ⁅xz.1, yz.1⁆ ∈ N ∧
      ⁅xz.2, yz.2⁆ ∈ (⊥ : Subgroup C)
    constructor
    · apply (QuotientGroup.eq_one_iff (N := N) ⁅xz.1, yz.1⁆).mp
      change (QuotientGroup.mk' N) ⁅xz.1, yz.1⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hxz.1 yz.1).symm
    · change ⁅xz.2, yz.2⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hxz.2 yz.2).symm
  have hbound :=
    Theory.Character.irreducible_finrank_sq_le_index_of_centralModulo_kernel
      rho K T hKker hcentral
  simpa [T, Z0, Subgroup.index_map_equiv, Subgroup.index_prod] using hbound

private theorem
    irreducible_finrank_sq_le_centerModulo_index_mul_subgroup_index_appendixIV
    {A C G V : Type*} [Group A] [Group C] [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : A × C ≃* G) (N : Subgroup A) [N.Normal]
    (Z : Subgroup C) (hZcentral : Z ≤ Subgroup.center C)
    (rho : Representation ℂ G V) [rho.IsIrreducible]
    (hker : ∀ x : N.prod (⊥ : Subgroup C), rho (e x) = 1) :
    Module.finrank ℂ V ^ 2 ≤
      (Subgroup.comap (QuotientGroup.mk' N)
        (Subgroup.center (A ⧸ N))).index * Z.index := by
  classical
  let Z0 := Subgroup.comap (QuotientGroup.mk' N)
    (Subgroup.center (A ⧸ N))
  let K := Subgroup.map e.toMonoidHom (N.prod (⊥ : Subgroup C))
  let T := Subgroup.map e.toMonoidHom (Z0.prod Z)
  have hKker : ∀ k : K, rho k = 1 := by
    intro k
    rcases k.property with ⟨x, hx, hxk⟩
    rw [← hxk]
    exact hker ⟨x, hx⟩
  have hcentral : Theory.Character.IsCentralModulo K T := by
    intro x hx y
    rcases hx with ⟨xz, hxz, hxeq⟩
    rw [← hxeq]
    let yz := e.symm y
    have hyeq : e yz = y := e.apply_symm_apply y
    rw [← hyeq]
    change ⁅e.toMonoidHom xz, e.toMonoidHom yz⁆ ∈ K
    rw [← map_commutatorElement e.toMonoidHom]
    apply Subgroup.mem_map.mpr
    refine ⟨⁅xz, yz⁆, ?_, rfl⟩
    change ⁅xz.1, yz.1⁆ ∈ N ∧
      ⁅xz.2, yz.2⁆ ∈ (⊥ : Subgroup C)
    constructor
    · apply (QuotientGroup.eq_one_iff (N := N) ⁅xz.1, yz.1⁆).mp
      change (QuotientGroup.mk' N) ⁅xz.1, yz.1⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hxz.1 yz.1).symm
    · change ⁅xz.2, yz.2⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hZcentral hxz.2) yz.2).symm
  have hbound :=
    Theory.Character.irreducible_finrank_sq_le_index_of_centralModulo_kernel
      rho K T hKker hcentral
  simpa [T, Z0, Subgroup.index_map_equiv, Subgroup.index_prod] using hbound

private theorem subgroupInKernel'_mono_appendixIV
    {L : Type*} [Group L] {A B : Subgroup L}
    {chi : ClassFunction L} (hAB : A ≤ B)
    (hchi : subgroupInKernel' chi B) :
    subgroupInKernel' chi A := by
  intro a
  exact hchi ⟨a, hAB a.property⟩

private theorem subgroupInKernel'_sup_of_irreducible_appendixIV
    {L : Type*} [Group L] [Finite L]
    {A B : Subgroup L} {chi : ClassFunction L}
    (hirr : IsIrreducibleCharacterOnGroup chi)
    (hA : subgroupInKernel' chi A)
    (hB : subgroupInKernel' chi B) :
    subgroupInKernel' chi (A ⊔ B) := by
  rcases hirr with ⟨n, rho, hrho, hchi⟩
  have hAchar : subgroupInKernel' rho.character A :=
    subgroupInKernel'_of_eq hchi hA
  have hBchar : subgroupInKernel' rho.character B :=
    subgroupInKernel'_of_eq hchi hB
  have hArep : subgroupInRepresentationKernel rho A :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel rho A).mp hAchar
  have hBrep : subgroupInRepresentationKernel rho B :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel rho B).mp hBchar
  have hAle : A ≤ rho.ker := by
    intro a ha
    exact hArep ⟨a, ha⟩
  have hBle : B ≤ rho.ker := by
    intro b hb
    exact hBrep ⟨b, hb⟩
  have hsupRep : subgroupInRepresentationKernel rho (A ⊔ B) := by
    intro x
    exact (sup_le hAle hBle) x.property
  have hsupChar : subgroupInKernel' rho.character (A ⊔ B) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho (A ⊔ B)).mpr hsupRep
  exact subgroupInKernel'_of_eq hchi.symm hsupChar

private theorem exceptional_kernel_degree_sq_sum_appendixIV
    {L : Type*} [Group L] [Finite L]
    (R Z : Subgroup L) [R.Normal] [Z.Normal]
    (S : Finset (ClassFunction L))
    (hS : ∀ chi : ClassFunction L, chi ∈ S ↔
      IsIrreducibleCharacterOnGroup chi ∧
        subgroupInKernel' chi R ∧
        ¬ subgroupInKernel' chi Z) :
    (∑ chi : S, (degree (chi : ClassFunction L)).re ^ 2) +
        (Nat.card (L ⧸ (R ⊔ Z)) : Real) =
      (Nat.card (L ⧸ R) : Real) := by
  classical
  let : (R ⊔ Z).Normal := inferInstance
  obtain ⟨A, hA, degA, hdegA, hsumA⟩ :=
    Section6.theorem_6_6_complete_nonkernel_degree_data (L := L) (Z := R ⊔ Z)
  obtain ⟨B, hB, degB, hdegB, hsumB⟩ :=
    Section6.theorem_6_6_complete_nonkernel_degree_data (L := L) (Z := R)
  have hBsubA : B ⊆ A := by
    intro chi hchiB
    rcases (hB chi).mp hchiB with ⟨hirr, hnotR⟩
    apply (hA chi).mpr
    refine ⟨hirr, ?_⟩
    intro hsup
    exact hnotR
      (subgroupInKernel'_mono_appendixIV le_sup_left hsup)
  have hSeq : S = A \ B := by
    ext chi
    rw [hS chi]
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hirr, hR, hnotZ⟩
      constructor
      · apply (hA chi).mpr
        refine ⟨hirr, ?_⟩
        intro hsup
        exact hnotZ
          (subgroupInKernel'_mono_appendixIV le_sup_right hsup)
      · intro hchiB
        exact ((hB chi).mp hchiB).2 hR
    · rintro ⟨hchiA, hchiB⟩
      rcases (hA chi).mp hchiA with ⟨hirr, hnotSup⟩
      have hR : subgroupInKernel' chi R := by
        by_contra hnotR
        exact hchiB ((hB chi).mpr ⟨hirr, hnotR⟩)
      refine ⟨hirr, hR, ?_⟩
      intro hZ
      exact hnotSup
        (subgroupInKernel'_sup_of_irreducible_appendixIV hirr hR hZ)
  let f : ClassFunction L → Real :=
    fun chi => (degree chi).re ^ 2
  have hdegSumA :
      (∑ chi : A, f (chi : ClassFunction L)) =
        ∑ chi : A, (degA chi : Real) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro chi _hchi
    simp [f, hdegA]
  have hdegSumB :
      (∑ chi : B, f (chi : ClassFunction L)) =
        ∑ chi : B, (degB chi : Real) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro chi _hchi
    simp [f, hdegB]
  have hsumAreal :
      (∑ chi : A, f (chi : ClassFunction L)) +
          (Nat.card (L ⧸ (R ⊔ Z)) : Real) =
        (Nat.card L : Real) := by
    rw [hdegSumA]
    norm_cast
  have hsumBreal :
      (∑ chi : B, f (chi : ClassFunction L)) +
          (Nat.card (L ⧸ R) : Real) =
        (Nat.card L : Real) := by
    rw [hdegSumB]
    norm_cast
  have hdiff :
      (∑ chi : ↥(A \ B), f (chi : ClassFunction L)) +
          (∑ chi : B, f (chi : ClassFunction L)) =
        ∑ chi : A, f (chi : ClassFunction L) := by
    rw [← Finset.sum_subtype (s := A \ B)
      (p := fun chi : ClassFunction L => chi ∈ A \ B)
      (f := f) (by simp)]
    rw [← Finset.sum_subtype (s := B)
      (p := fun chi : ClassFunction L => chi ∈ B)
      (f := f) (by simp)]
    rw [← Finset.sum_subtype (s := A)
      (p := fun chi : ClassFunction L => chi ∈ A)
      (f := f) (by simp)]
    exact Finset.sum_sdiff hBsubA
  rw [hSeq]
  dsimp [f]
  dsimp [f] at hdiff hsumAreal hsumBreal
  linarith

private theorem actsRegularly_quotient_of_solvable_coprime_appendixIV
    {A M : Type*} [Group A] [Finite A] [Group M] [Finite M]
    [MulDistribMulAction A M]
    (hsolv : Group.IsSolvable M)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card M))
    (N : Subgroup M) [N.Normal] (hNinv : IsInvariant A M N)
    (hregular : ActsRegularly A M) :
    letI : MulDistribMulAction A (M ⧸ N) :=
      quotientMulDistribMulAction (A := A) (G := M) N hNinv
    ActsRegularly A (M ⧸ N) := by
  intro a ha
  let A' : Subgroup A := Subgroup.zpowers a
  have hNinvA' : IsInvariant A' M N := by
    refine ⟨?_⟩
    intro b x
    have h := IsInvariant.invariant (A := A) (G := M) (H := N) (b : A) x
    have hsmul : (b : A) • x = b • x := rfl
    simpa [hsmul] using h
  have hfixedA' : fixedPointSubgroup A' M = ⊥ := by
    simpa using hregular a ha
  let : MulDistribMulAction A' (M ⧸ N) :=
    quotientMulDistribMulAction (A := A') (G := M) N hNinvA'
  have hfixed :=
    fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
      (G := M) (A := A') hsolv ?_ (∅ : Set Nat.Primes) N hNinvA'
  · rw [hfixedA'] at hfixed
    simpa [A'] using hfixed
  · exact Nat.Coprime.of_dvd_left (Subgroup.card_subgroup_dvd_card A') hcop

private theorem natCard_add_one_le_of_actsRegularly_appendixIV
    {A M : Type*} [Group A] [Finite A] [Group M] [Finite M]
    [MulDistribMulAction A M]
    (hregular : ActsRegularly A M) (hM : Nontrivial M) :
    Nat.card A + 1 ≤ Nat.card M := by
  let : Nontrivial M := hM
  obtain ⟨x, hx⟩ := exists_ne (1 : M)
  let f : Option A → M
    | none => 1
    | some a => a • x
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some b =>
            exfalso
            have hb : b • x = 1 := hxy.symm
            have hxone : x = 1 := by
              have := congrArg (fun z : M => b⁻¹ • z) hb
              simpa [smul_smul] using this
            exact hx hxone
    | some a =>
        cases y with
        | none =>
            exfalso
            have ha : a • x = 1 := hxy
            have hxone : x = 1 := by
              have := congrArg (fun z : M => a⁻¹ • z) ha
              simpa [smul_smul] using this
            exact hx hxone
        | some b =>
            congr 1
            change a • x = b • x at hxy
            have hfix : (b⁻¹ * a) • x = x := by
              have := congrArg (fun z : M => b⁻¹ • z) hxy
              simpa [smul_smul] using this
            have hab : b⁻¹ * a = 1 := by
              by_contra hne
              have hxmem : x ∈
                  fixedPointSubgroup (Subgroup.zpowers (b⁻¹ * a)) M := by
                rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
                intro z
                exact smul_eq_self_of_mem_zpowers z.2 hfix
              have hbot := hregular (b⁻¹ * a) hne
              have : x = 1 := by
                rw [hbot] at hxmem
                exact Subgroup.mem_bot.mp hxmem
              exact hx this
            exact (inv_mul_eq_one.mp hab).symm
  simpa using Nat.card_le_card_of_injective f hf

private theorem relIndex_sub_one_le_two_mul_of_degree_obstruction_appendixIV
    {L : Type*} [Group L] [Finite L]
    (R T : Subgroup L) [R.Normal] [T.Normal]
    (hRT : R ≤ T) (s x d0 : Real)
    (hx : 0 ≤ x)
    (hsum : s + (Nat.card (L ⧸ T) : Real) =
      (Nat.card (L ⧸ R) : Real))
    (hbound : s ≤ 2 * x * d0)
    (hd0 : d0 ≤ (Nat.card (L ⧸ T) : Real)) :
    (R.relIndex T : Real) - 1 ≤ 2 * x := by
  have hcard :
      (Nat.card (L ⧸ R) : Real) =
        (R.relIndex T : Real) * (Nat.card (L ⧸ T) : Real) := by
    norm_cast
    simpa [Subgroup.index_eq_card] using
      (Subgroup.relIndex_mul_index (H := R) (K := T) hRT).symm
  have hTpos : 0 < (Nat.card (L ⧸ T) : Real) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (L ⧸ T))
  have hbound' :
      s ≤ 2 * x * (Nat.card (L ⧸ T) : Real) := by
    calc
      s ≤ 2 * x * d0 := hbound
      _ ≤ 2 * x * (Nat.card (L ⧸ T) : Real) := by
        exact mul_le_mul_of_nonneg_left hd0 (by positivity)
  nlinarith

private theorem centerModulo_preimage_normal_appendixIV
    {H : Type*} [Group H]
    (Q1 Q3 : Subgroup H) [Q1.Normal] [Q3.Normal] :
    let K : Subgroup Q1 := Q3.subgroupOf Q1
    let Z1 : Subgroup (Q1 ⧸ K) := Subgroup.center (Q1 ⧸ K)
    let Z : Subgroup H :=
      (Subgroup.comap (QuotientGroup.mk' K) Z1).map Q1.subtype
    Z.Normal := by
  let K : Subgroup Q1 := Q3.subgroupOf Q1
  let : K.Normal := (inferInstance : Q3.Normal).subgroupOf Q1
  let Z1 : Subgroup (Q1 ⧸ K) := Subgroup.center (Q1 ⧸ K)
  let Z : Subgroup H :=
    (Subgroup.comap (QuotientGroup.mk' K) Z1).map Q1.subtype
  dsimp only
  refine ⟨fun z hz x => ?_⟩
  rcases Subgroup.mem_map.mp hz with ⟨z1, hz1, rfl⟩
  let zx : Q1 := ⟨x * (z1 : H) * x⁻¹,
    (inferInstance : Q1.Normal).conj_mem z1 z1.property x⟩
  refine Subgroup.mem_map.mpr ⟨zx, ?_, rfl⟩
  change QuotientGroup.mk' K zx ∈ Subgroup.center (Q1 ⧸ K)
  rw [Subgroup.mem_center_iff]
  intro qbar
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective K qbar
  let qpre : Q1 := ⟨x⁻¹ * (q : H) * x,
    by simpa [mul_assoc] using
      (inferInstance : Q1.Normal).conj_mem q q.property x⁻¹⟩
  have hzcenter :
      QuotientGroup.mk' K z1 ∈ Subgroup.center (Q1 ⧸ K) := by
    simpa [Z1] using hz1
  have hpre_one : QuotientGroup.mk' K ⁅z1, qpre⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp hzcenter
        (QuotientGroup.mk' K qpre)).symm)
  have hpreK : ⁅z1, qpre⁆ ∈ K :=
    (QuotientGroup.eq_one_iff ⁅z1, qpre⁆).mp hpre_one
  have hpreQ3 : ⁅(z1 : H), (qpre : H)⁆ ∈ Q3 := hpreK
  have hconj : x * ⁅(z1 : H), (qpre : H)⁆ * x⁻¹ ∈ Q3 :=
    (inferInstance : Q3.Normal).conj_mem _ hpreQ3 x
  rw [conjugate_commutatorElement] at hconj
  have hcomm : ⁅(zx : Q1), q⁆ ∈ K := by
    change ⁅(zx : H), (q : H)⁆ ∈ Q3
    simpa [zx, qpre, mul_assoc] using hconj
  symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff ⁅zx, q⁆).mpr hcomm

private theorem chiefFactor_le_centerModulo_preimage_appendixIV
    {H : Type*} [Group H] [Finite H]
    (Q1 Q2 Q3 : Subgroup H)
    [Q1.Normal] [Q2.Normal] [Q3.Normal]
    [Group.IsNilpotent Q1]
    (hchief : IsChiefFactor Q3 Q2) (hQ2le : Q2 ≤ Q1) :
    let K : Subgroup Q1 := Q3.subgroupOf Q1
    let Z1 : Subgroup (Q1 ⧸ K) := Subgroup.center (Q1 ⧸ K)
    let Z : Subgroup H :=
      (Subgroup.comap (QuotientGroup.mk' K) Z1).map Q1.subtype
    Q2 ≤ Z := by
  let K : Subgroup Q1 := Q3.subgroupOf Q1
  let : K.Normal := (inferInstance : Q3.Normal).subgroupOf Q1
  let Z1 : Subgroup (Q1 ⧸ K) := Subgroup.center (Q1 ⧸ K)
  let Z : Subgroup H :=
    (Subgroup.comap (QuotientGroup.mk' K) Z1).map Q1.subtype
  let : Z.Normal := centerModulo_preimage_normal_appendixIV Q1 Q3
  let Q2sub : Subgroup Q1 := Q2.subgroupOf Q1
  let : Q2sub.Normal := (inferInstance : Q2.Normal).subgroupOf Q1
  let Q2bar : Subgroup (Q1 ⧸ K) :=
    Q2sub.map (QuotientGroup.mk' K)
  let : Q2bar.Normal := by
    dsimp [Q2bar]
    infer_instance
  obtain ⟨a, haQ2, haQ3⟩ := SetLike.exists_of_lt hchief.lt
  let a1 : Q1 := ⟨a, hQ2le haQ2⟩
  have ha1Q2sub : a1 ∈ Q2sub := haQ2
  have hma_mem : QuotientGroup.mk' K a1 ∈ Q2bar :=
    Subgroup.mem_map_of_mem (QuotientGroup.mk' K) ha1Q2sub
  have hma_ne : QuotientGroup.mk' K a1 ≠ 1 := by
    intro hma
    apply haQ3
    exact (QuotientGroup.eq_one_iff a1).mp hma
  have hQ2bar_ne : Q2bar ≠ ⊥ := by
    intro hbot
    have hbotmem : QuotientGroup.mk' K a1 ∈
        (⊥ : Subgroup (Q1 ⧸ K)) := by
      rw [← hbot]
      exact hma_mem
    exact hma_ne (by simpa using hbotmem)
  have hnontriv : Q2bar ⊓ Subgroup.center (Q1 ⧸ K) ≠ ⊥ :=
    Section6.nilpotent_normal_inf_center_ne_bot Q2bar hQ2bar_ne
  obtain ⟨ybar, hybar_ne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hnontriv
  rcases Subgroup.mem_map.mp ybar.property.1 with
    ⟨y, hyQ2sub, hyMap⟩
  have hyQ2 : (y : H) ∈ Q2 := hyQ2sub
  have hyCenter :
      QuotientGroup.mk' K y ∈ Subgroup.center (Q1 ⧸ K) := by
    rw [hyMap]
    exact ybar.property.2
  have hyZ : (y : H) ∈ Z :=
    Subgroup.mem_map.mpr ⟨y, hyCenter, rfl⟩
  have hyQ3 : (y : H) ∉ Q3 := by
    intro hy
    apply hybar_ne
    apply Subtype.ext
    rw [← hyMap]
    exact (QuotientGroup.eq_one_iff y).mpr hy
  have hQ3leZ : Q3 ≤ Z := by
    intro q hq
    let q1 : Q1 := ⟨q, hQ2le (hchief.lt.le hq)⟩
    refine Subgroup.mem_map.mpr ⟨q1, ?_, rfl⟩
    change QuotientGroup.mk' K q1 ∈ Subgroup.center (Q1 ⧸ K)
    have hq1 : QuotientGroup.mk' K q1 = 1 :=
      (QuotientGroup.eq_one_iff q1).mpr hq
    rw [hq1]
    exact Subgroup.one_mem _
  have hQ3leInf : Q3 ≤ Q2 ⊓ Z := le_inf hchief.lt.le hQ3leZ
  have hQ3ltInf : Q3 < Q2 ⊓ Z := by
    refine lt_of_le_of_ne hQ3leInf ?_
    intro heq
    have hyInf : (y : H) ∈ Q2 ⊓ Z := ⟨hyQ2, hyZ⟩
    rw [← heq] at hyInf
    exact hyQ3 hyInf
  have hInfEqQ2 : Q2 ⊓ Z = Q2 :=
    (hchief.is_maximal (Q2 ⊓ Z) (by infer_instance)
      hQ3leInf inf_le_left).resolve_left (ne_of_gt hQ3ltInf)
  calc
    Q2 = Q2 ⊓ Z := hInfEqQ2.symm
    _ ≤ Z := inf_le_right

private theorem exists_chiefFactor_below_appendixIV
    {L : Type*} [Group L] [Finite L]
    (Q2 : Subgroup L) [Q2.Normal] (hQ2 : Q2 ≠ ⊥) :
    ∃ Q3 : Subgroup L, IsChiefFactor Q3 Q2 := by
  obtain ⟨Q3, hQ3normal, hQ3lt, hmax⟩ :=
    exists_maximal_normal_lt Q2 hQ2
  refine ⟨Q3, {
    normal_K := hQ3normal
    normal_H := inferInstance
    lt := hQ3lt
    is_maximal := ?_ }⟩
  intro N hNnormal hQ3N hNQ2
  by_cases hNQ3 : N = Q3
  · exact Or.inl hNQ3
  · exact Or.inr (hmax N hNnormal
      (lt_of_le_of_ne hQ3N (Ne.symm hNQ3)) hNQ2)
private abbrev feitSibleyCoherent
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (U : Finset (ClassFunction d.H)) : Prop :=
  IsCoherentTriple puncturedSet U (Section1.inducedCFLinear d.H)

private abbrev feitSibleySker
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) (R : Subgroup d.H) :
    Finset (ClassFunction d.H) := by
  classical
  exact chars.filter (fun chi => subgroupInKernel' chi R)

private abbrev feitSibleySnonker
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) (R : Subgroup d.H) :
    Finset (ClassFunction d.H) := by
  classical
  exact chars.filter (fun chi => ¬ subgroupInKernel' chi R)

private abbrev feitSibleyExtensionOn
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (U : Finset (ClassFunction d.H))
    (T' : ClassFunction d.H →ₗ[Complex] ClassFunction G) : Prop :=
  isCFLinearIsometryOnSpan U T' ∧
    mapsIntegerSpanToVirtualCharacters U T' ∧
    agreesOnIntegerSpanOn U puncturedSet
      (Section1.inducedCFLinear d.H) T'

private abbrev feitSibleyCrossOrthogonal
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (X Y : Finset (ClassFunction d.H))
    (TX TY : ClassFunction d.H →ₗ[Complex] ClassFunction G) : Prop :=
  ∀ chi : X, ∀ eta : Y,
    scalarProduct G (TX (chi : ClassFunction d.H))
      (TY (eta : ClassFunction d.H)) = 0

private abbrev feitSibleySderivedH
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    Subgroup d.H :=
  Subgroup.map (d.S.subtype : d.S →* d.H) (derivedSubgroup d.S)

private abbrev feitSibleyQderivedH
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    Subgroup d.H :=
  Subgroup.map (d.Q.subtype : d.Q →* d.H) (derivedSubgroup d.Q)

private abbrev feitSibleyQ1derivedH
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    Subgroup d.H :=
  Subgroup.map (d.Q1.subtype : d.Q1 →* d.H) (derivedSubgroup d.Q1)

private abbrev feitSibleyCenterQ1H
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    Subgroup d.H :=
  Subgroup.map (d.Q1.subtype : d.Q1 →* d.H) (Subgroup.center d.Q1)

private abbrev feitSibleyZ
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    Subgroup d.H :=
  feitSibleyQ1derivedH d ⊓ feitSibleyCenterQ1H d

private abbrev feitSibleyX
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) : Finset (ClassFunction d.H) :=
  feitSibleySnonker d chars (feitSibleyZ d)

private abbrev feitSibleyY
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) : Finset (ClassFunction d.H) :=
  feitSibleySker d chars (feitSibleyQderivedH d)

private theorem
    FeitSibleyData.exceptional_derived_kernel_of_degree_eq_relIndex
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (chi : ClassFunction d.H) (hchiChars : chi ∈ chars)
    (hdegree :
      degree chi =
        (d.Q.relIndex (⊤ : Subgroup d.H) : Complex)) :
    subgroupInKernel' chi (feitSibleyQderivedH d) := by
  classical
  let : d.Q.Normal := d.Q_normal
  rcases (lemma_2_a d chars hchars chi).mp hchiChars with
    ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
  rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
  have hdegreeInd :
      degree chi = (d.Q.index : Complex) * (n : Complex) := by
    rw [← hind, degree_inducedClassFunction d.Q phi, hphiEq,
      degree_representation_character]
    simp
  have hrelIndex :
      d.Q.relIndex (⊤ : Subgroup d.H) = d.Q.index := by
    simp [Subgroup.relIndex_top_right]
  have hcast :
      (d.Q.index : Complex) * (n : Complex) =
        (d.Q.index : Complex) := by
    calc
      (d.Q.index : Complex) * (n : Complex) = degree chi :=
        hdegreeInd.symm
      _ = (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := hdegree
      _ = (d.Q.index : Complex) := by rw [hrelIndex]
  have hnat : d.Q.index * n = d.Q.index := by
    exact_mod_cast hcast
  have hindexPos : 0 < d.Q.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have hn : n = 1 :=
    Nat.eq_of_mul_eq_mul_left hindexPos (by simpa using hnat)
  have hderivedKer : derivedSubgroup d.Q ≤ rho.ker := by
    apply derivedSubgroup_le_representation_ker_of_finrank_one_appendixIV
      rho
    simp [hn]
  have hrepKernel :
      subgroupInRepresentationKernel rho (derivedSubgroup d.Q) := by
    intro x
    exact hderivedKer x.property
  have hcharKernel :
      subgroupInKernel' rho.character (derivedSubgroup d.Q) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho (derivedSubgroup d.Q)).mpr hrepKernel
  have hphiKernel :
      subgroupInKernel' phi (derivedSubgroup d.Q) := by
    simpa [hphiEq] using hcharKernel
  have hQderivedLe : feitSibleyQderivedH d ≤ d.Q := by
    simpa [feitSibleyQderivedH] using
      Subgroup.map_subtype_le (derivedSubgroup d.Q)
  have : (feitSibleyQderivedH d).Normal := by
    dsimp [feitSibleyQderivedH]
    infer_instance
  have hQderivedSub :
      (feitSibleyQderivedH d).subgroupOf d.Q =
        derivedSubgroup d.Q := by
    dsimp [feitSibleyQderivedH]
    exact subgroupOf_map_subtype_eq (derivedSubgroup d.Q)
  have hphiKernelSub :
      subgroupInKernel' phi
        ((feitSibleyQderivedH d).subgroupOf d.Q) := by
    simpa [hQderivedSub] using hphiKernel
  have hindKernelRho :
      subgroupInKernel' (inducedCF d.Q rho.character)
        (feitSibleyQderivedH d) :=
    (Section1.proposition_1_6_a d.Q (feitSibleyQderivedH d)
      hQderivedLe rho).mp (by simpa [hphiEq] using hphiKernelSub)
  have hindKernel :
      subgroupInKernel' (inducedCF d.Q phi)
        (feitSibleyQderivedH d) := by
    simpa [hphiEq] using hindKernelRho
  simpa [hind] using hindKernel

private noncomputable def feitSibleyCenterModuloPreimage
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (Q3 : Subgroup d.H) [Q3.Normal] : Subgroup d.Q1 := by
  let : d.Q1.Normal := d.Q1_normal
  let N : Subgroup d.Q1 := Q3.subgroupOf d.Q1
  let : N.Normal := (inferInstance : Q3.Normal).subgroupOf d.Q1
  exact
    Subgroup.comap (QuotientGroup.mk' N)
      (Subgroup.center (d.Q1 ⧸ N))

private noncomputable def feitSibleyCenterModuloPreimageH
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (Q3 : Subgroup d.H) [Q3.Normal] : Subgroup d.H :=
  (feitSibleyCenterModuloPreimage d Q3).map d.Q1.subtype

private def feitSibleyStep4Data
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) : Prop :=
  let Z := feitSibleyZ d
  let X := feitSibleyX d chars
  let Y := feitSibleyY d chars
  Z ≠ ⊥ ∧
    Z.Normal ∧
    Z ≤ feitSibleyCenterQ1H d ∧
    Disjoint X Y ∧
    feitSibleyCoherent d X ∧
    feitSibleyCoherent d Y ∧
    X.Nonempty ∧
    Y.Nonempty ∧
    (∀ eta : Y,
      degree (eta : ClassFunction d.H) =
        (Nat.card d.D : Complex)) ∧
    ∃ chi1 : X, ∃ a : Nat,
      1 < a ∧
      degree (chi1 : ClassFunction d.H) =
        (a : Complex) * (Nat.card d.D : Complex) ∧
      ∀ chi : X, ∃ ai : Nat,
        degree (chi : ClassFunction d.H) =
          (ai : Complex) * degree (chi1 : ClassFunction d.H)

private def feitSibleyStep5Data
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) : Prop :=
  ∀ (TX TY : ClassFunction d.H →ₗ[Complex] ClassFunction G),
    feitSibleyExtensionOn d (feitSibleyX d chars) TX →
    feitSibleyExtensionOn d (feitSibleyY d chars) TY →
    feitSibleyCrossOrthogonal d (feitSibleyX d chars)
      (feitSibleyY d chars) TX TY

private def feitSibleyStep6Data
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) : Prop :=
  ∀ (TX TY : ClassFunction d.H →ₗ[Complex] ClassFunction G)
    (chi1 : feitSibleyX d chars) (eta1 : feitSibleyY d chars)
    (a : Nat),
    (∀ chi : feitSibleyX d chars, ∃ ai : Nat,
      degree (chi : ClassFunction d.H) =
        (ai : Complex) * degree (chi1 : ClassFunction d.H)) →
    feitSibleyExtensionOn d (feitSibleyX d chars) TX →
    feitSibleyExtensionOn d (feitSibleyY d chars) TY →
    feitSibleyCrossOrthogonal d (feitSibleyX d chars)
      (feitSibleyY d chars) TX TY →
    1 < a →
    degree (chi1 : ClassFunction d.H) =
      (a : Complex) * degree (eta1 : ClassFunction d.H) →
    ∃ (v : ClassFunction G) (lambda : Int),
      Theory.Character.IsVirtualCharacter v ∧
      Section1.inducedCF d.H
          ((chi1 : ClassFunction d.H) -
            (a : Complex) • (eta1 : ClassFunction d.H)) =
        -(a : Complex) • TY (eta1 : ClassFunction d.H) +
          (lambda : Complex) •
            (∑ eta : feitSibleyY d chars,
              TY (eta : ClassFunction d.H)) + v ∧
      (∀ eta : feitSibleyY d chars,
        scalarProduct G v (TY (eta : ClassFunction d.H)) = 0) ∧
      ((a : Int) ∣ lambda → feitSibleyCoherent d chars)

private def feitSibleyStep7Data
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) : Prop :=
  ∀ psi : ClassFunction G,
    (∀ z1 z2 : feitSibleyZ d,
      (z1 : d.H) ≠ 1 → (z2 : d.H) ≠ 1 →
        psi (d.H.subtype z1) = psi (d.H.subtype z2)) →
    IsIrreducibleCharacterOnGroup psi →
    ∀ z : feitSibleyZ d, (z : d.H) ≠ 1 →
      IsIntegral Int
        ((psi (d.H.subtype z) - psi 1) /
          (Nat.card d.Q : Complex))

private theorem isPGroup_of_nilpotent_center_isPGroup_appendixIV
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : Nat} [Fact p.Prime]
    (hcenter : IsPGroup p (Subgroup.center G)) :
    IsPGroup p G := by
  by_contra hnot
  obtain ⟨q, hq, hqne, hqdiv⟩ :=
    External.hkt_exists_qprime_divisor_card_of_not_isPGroup p G hnot
  let : Fact q.Prime := ⟨hq⟩
  let P : Sylow q G := default
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hqdiv
  let : (P : Subgroup G).Normal :=
    Group.IsNilpotent.sylow_normal
      (inferInstance : Group.IsNilpotent G) q P
  have hinter : (P : Subgroup G) ⊓ Subgroup.center G ≠ ⊥ :=
    Section6.nilpotent_normal_inf_center_ne_bot (P : Subgroup G) hPne
  have hdisj : Disjoint (P : Subgroup G) (Subgroup.center G) :=
    IsPGroup.disjoint_of_ne q p hqne
      (P : Subgroup G) (Subgroup.center G) P.isPGroup' hcenter
  exact hinter hdisj.eq_bot
private theorem feitSibley_step1_strict_center_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (Q2 Q3 : Subgroup d.H) [Q2.Normal] [Q3.Normal]
    [Group.IsNilpotent d.Q1]
    (hp : ¬ ∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1)
    (hchief : IsChiefFactor Q3 Q2)
    (hQ2derived : Q2 ≤ feitSibleyQ1derivedH d) :
    Q2 < feitSibleyCenterModuloPreimageH d Q3 ∧
      feitSibleyCenterModuloPreimageH d Q3 < d.Q1 := by
  let : d.Q1.Normal := d.Q1_normal
  let N : Subgroup d.Q1 := Q3.subgroupOf d.Q1
  let : N.Normal := (inferInstance : Q3.Normal).subgroupOf d.Q1
  let Z0 : Subgroup d.Q1 := feitSibleyCenterModuloPreimage d Q3
  let Z3 : Subgroup d.H := feitSibleyCenterModuloPreimageH d Q3
  have hQ2leQ1 : Q2 ≤ d.Q1 := by
    calc
      Q2 ≤ feitSibleyQ1derivedH d := hQ2derived
      _ ≤ d.Q1 := by
        simpa [feitSibleyQ1derivedH] using
          Subgroup.map_subtype_le (derivedSubgroup d.Q1)
  have hQ2leZ3 : Q2 ≤ Z3 := by
    simpa [Z3, Z0, N, feitSibleyCenterModuloPreimageH,
      feitSibleyCenterModuloPreimage] using
      (chiefFactor_le_centerModulo_preimage_appendixIV
        d.Q1 Q2 Q3 hchief hQ2leQ1)
  have hZ3leQ1 : Z3 ≤ d.Q1 := by
    simpa [Z3, feitSibleyCenterModuloPreimageH] using
      Subgroup.map_subtype_le Z0
  constructor
  · refine lt_of_le_of_ne hQ2leZ3 ?_
    intro hQ2Z3
    have hQ3leQ1 : Q3 ≤ d.Q1 := hchief.lt.le.trans hQ2leQ1
    let piH : d.H →* d.H ⧸ Q3 := QuotientGroup.mk' Q3
    let f : d.Q1 ⧸ N →* d.H ⧸ Q3 :=
      QuotientGroup.map N Q3 d.Q1.subtype (by
        intro x hx
        exact hx)
    have hf_inj : Function.Injective f := by
      intro a b hab
      rcases QuotientGroup.mk'_surjective N a with ⟨x, rfl⟩
      rcases QuotientGroup.mk'_surjective N b with ⟨y, rfl⟩
      apply QuotientGroup.eq.mpr
      have hxyQ3 : (x : d.H)⁻¹ * (y : d.H) ∈ Q3 := by
        apply QuotientGroup.eq.mp
        calc
          (QuotientGroup.mk' Q3) (x : d.H) = f (QuotientGroup.mk' N x) := by
            symm
            exact QuotientGroup.map_mk' N Q3 d.Q1.subtype (by
              intro z hz
              exact hz) x
          _ = f (QuotientGroup.mk' N y) := hab
          _ = (QuotientGroup.mk' Q3) (y : d.H) := by
            exact QuotientGroup.map_mk' N Q3 d.Q1.subtype (by
              intro z hz
              exact hz) y
      exact hxyQ3
    let Uq : Subgroup (d.H ⧸ Q3) := Q2.map piH
    let : Uq.Normal := by
      dsimp [Uq, piH]
      exact (inferInstance : Q2.Normal).map (QuotientGroup.mk' Q3)
        (QuotientGroup.mk'_surjective Q3)
    have hcenterMap :
        (Subgroup.center (d.Q1 ⧸ N)).map f = Uq := by
      apply le_antisymm
      · intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨xbar, hxcenter, rfl⟩
        rcases QuotientGroup.mk'_surjective N xbar with ⟨x, rfl⟩
        have hxZ0 : x ∈ Z0 := by
          simpa [Z0, N, feitSibleyCenterModuloPreimage] using hxcenter
        have hxZ3 : (x : d.H) ∈ Z3 :=
          Subgroup.mem_map.mpr ⟨x, hxZ0, rfl⟩
        have hxQ2 : (x : d.H) ∈ Q2 := by
          rw [hQ2Z3]
          exact hxZ3
        refine Subgroup.mem_map.mpr ⟨(x : d.H), hxQ2, ?_⟩
        change f (QuotientGroup.mk' N x) = (QuotientGroup.mk' Q3) (x : d.H)
        exact QuotientGroup.map_mk' N Q3 d.Q1.subtype (by
          intro z hz
          exact hz) x
      · intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨x, hxQ2, rfl⟩
        let x1 : d.Q1 := ⟨x, hQ2leQ1 hxQ2⟩
        have hxZ3 : x ∈ Z3 := hQ2leZ3 hxQ2
        rcases Subgroup.mem_map.mp hxZ3 with ⟨z, hzZ0, hzx⟩
        have hzx1 : z = x1 := by
          apply Subtype.ext
          exact hzx
        have hx1Z0 : x1 ∈ Z0 := by simpa [hzx1] using hzZ0
        have hx1center :
            QuotientGroup.mk' N x1 ∈ Subgroup.center (d.Q1 ⧸ N) := by
          simpa [Z0, N, feitSibleyCenterModuloPreimage] using hx1Z0
        refine Subgroup.mem_map.mpr
          ⟨QuotientGroup.mk' N x1, hx1center, ?_⟩
        change f (QuotientGroup.mk' N x1) = (QuotientGroup.mk' Q3) (x : d.H)
        exact QuotientGroup.map_mk' N Q3 d.Q1.subtype (by
          intro z hz
          exact hz) x1
    let eCenter0 :
        Subgroup.center (d.Q1 ⧸ N) ≃*
          (Subgroup.center (d.Q1 ⧸ N)).map f :=
      Subgroup.equivMapOfInjective (Subgroup.center (d.Q1 ⧸ N)) f hf_inj
    let eCenter : Subgroup.center (d.Q1 ⧸ N) ≃* Uq :=
      eCenter0.trans (MulEquiv.subgroupCongr hcenterMap)
    have hUqSolv : Group.IsSolvable Uq :=
      Group.isSolvable_of_comm (fun a b => by
        have hcenter_comm : ∀ (x y : Subgroup.center (d.Q1 ⧸ N)), x * y = y * x := by
          intro x y
          ext
          simp [Subgroup.mem_center_iff.mp x.2 y.1]
        have h_comm : eCenter.symm a * eCenter.symm b = eCenter.symm b * eCenter.symm a :=
          hcenter_comm (eCenter.symm a) (eCenter.symm b)
        apply eCenter.symm.injective
        simpa only [map_mul] using h_comm)
    let : Group.IsSolvable Uq := hUqSolv
    let cf : ChiefFactor d.H := { V := Q3, U := Q2, isChief := hchief }
    let : IsMinimalNormal Uq := by
      simpa [cf, Uq, piH] using
        chiefFactor_quotient_isMinimalNormal (G := d.H) cf
    obtain ⟨p, hpprime, hUqElem⟩ :=
      minimalNormal_solvable_exists_isElementaryAbelian
        (G := d.H ⧸ Q3) Uq
    let : Fact p.Prime := ⟨hpprime⟩
    have hUqp : IsPGroup p Uq := by
      let : IsElementaryAbelian p Uq := hUqElem
      exact IsElementaryAbelian.isPGroup p Uq
    have hcenterP : IsPGroup p (Subgroup.center (d.Q1 ⧸ N)) :=
      hUqp.of_equiv eCenter.symm
    let : Group.IsNilpotent (d.Q1 ⧸ N) := by infer_instance
    have hquotP : IsPGroup p (d.Q1 ⧸ N) :=
      isPGroup_of_nilpotent_center_isPGroup_appendixIV hcenterP
    have hNleDerived : N ≤ derivedSubgroup d.Q1 := by
      intro x hx
      have hxQ2 : (x : d.H) ∈ Q2 := hchief.lt.le hx
      rcases Subgroup.mem_map.mp (hQ2derived hxQ2) with
        ⟨y, hyderived, hyx⟩
      have hyx' : y = x := by
        apply Subtype.ext
        exact hyx
      simpa [hyx'] using hyderived
    let C : Subgroup d.Q1 := commutator d.Q1
    let : C.Normal := by dsimp [C]; infer_instance
    let qAb : d.Q1 ⧸ N →* d.Q1 ⧸ C :=
      QuotientGroup.map N C (MonoidHom.id d.Q1) (by
        simpa [C] using hNleDerived)
    have hqAbSurj : Function.Surjective qAb := by
      intro xbar
      rcases QuotientGroup.mk'_surjective C xbar with ⟨x, rfl⟩
      refine ⟨QuotientGroup.mk' N x, ?_⟩
      simp [qAb]
    have hAbP : IsPGroup p (d.Q1 ⧸ C) :=
      hquotP.of_surjective qAb hqAbSurj
    have hQ1P : IsPGroup p d.Q1 := by
      apply Section6.isPGroup_of_nilpotent_quotient_commutator_isPGroup
        (inferInstance : Group.IsNilpotent d.Q1)
      have hAbP' : IsPGroup p (d.Q1 ⧸ commutator d.Q1) := by
        simpa [C] using hAbP
      simpa using hAbP'
    exact hp ⟨p, hpprime, hQ1P⟩
  · refine lt_of_le_of_ne hZ3leQ1 ?_
    intro hZ3eq
    change Z3 = d.Q1 at hZ3eq
    have hZ0top : Z0 = ⊤ := by
      apply eq_top_iff.mpr
      intro x hx
      have hxmap : (x : d.H) ∈ Z3 := by
        rw [hZ3eq]
        exact x.property
      rcases Subgroup.mem_map.mp hxmap with ⟨z, hzZ0, hzx⟩
      have hzx' : z = x := by
        apply Subtype.ext
        exact hzx
      simpa [hzx'] using hzZ0
    have hquotComm :
        Std.Commutative (· * · : (d.Q1 ⧸ N) → (d.Q1 ⧸ N) → d.Q1 ⧸ N) := by
      apply Std.Commutative.mk
      intro xbar ybar
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N xbar
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N ybar
      have hxZ0 : x ∈ Z0 := by rw [hZ0top]; exact Subgroup.mem_top x
      have hxCenter :
          QuotientGroup.mk' N x ∈ Subgroup.center (d.Q1 ⧸ N) := by
        simpa [Z0, N, feitSibleyCenterModuloPreimage] using hxZ0
      exact (Subgroup.mem_center_iff.mp hxCenter
        (QuotientGroup.mk' N y)).symm
    have hderivedN : derivedSubgroup d.Q1 ≤ N := by
      have hcomm' : IsMulCommutative (d.Q1 ⧸ N) := ⟨hquotComm⟩
      exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm'
    have hQ2leQ3 : Q2 ≤ Q3 := by
      intro q hq
      rcases Subgroup.mem_map.mp (hQ2derived hq) with ⟨x, hxder, hxq⟩
      have hxN : x ∈ N := hderivedN hxder
      change (x : d.H) ∈ Q3 at hxN
      change (x : d.H) = q at hxq
      rw [← hxq]
      exact hxN
    exact hchief.lt.2 hQ2leQ3

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
private theorem feitSibley_step1_regular_index_contradiction_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (Q2 Q3 : Subgroup d.H) [Q2.Normal] [Q3.Normal]
    (hD : d.D ≠ ⊥)
    (_ : Odd (Nat.card d.D))
    (hQ2lt :
      Q2 < feitSibleyCenterModuloPreimageH d Q3)
    (hZlt :
      feitSibleyCenterModuloPreimageH d Q3 < d.Q1)
    (psiDegreeRe : Real)
    (h11 :
      (Q2.relIndex d.Q1 : Real) - 1 ≤ 2 * psiDegreeRe)
    (h12 :
      psiDegreeRe ^ 2 ≤
        (d.Q.relIndex (⊤ : Subgroup d.H) : Real) ^ 2 *
          ((feitSibleyCenterModuloPreimage d Q3).index : Real)) :
    False := by
  classical
  let : d.Q1.Normal := d.Q1_normal
  let : d.Q.Normal := d.Q_normal
  let K3 : Subgroup d.Q1 := Q3.subgroupOf d.Q1
  let : K3.Normal := (inferInstance : Q3.Normal).subgroupOf d.Q1
  let Z0 : Subgroup d.Q1 := feitSibleyCenterModuloPreimage d Q3
  let Z3 : Subgroup d.H := Z0.map d.Q1.subtype
  let : Z3.Normal := by
    simpa [Z3, Z0, K3, feitSibleyCenterModuloPreimage] using
      (centerModulo_preimage_normal_appendixIV d.Q1 Q3)
  have hQ2lt' : Q2 < Z3 := by
    simpa [Z3, Z0, feitSibleyCenterModuloPreimageH] using hQ2lt
  have hZlt' : Z3 < d.Q1 := by
    simpa [Z3, Z0, feitSibleyCenterModuloPreimageH] using hZlt
  have hQ2leZ3 : Q2 ≤ Z3 := hQ2lt'.le
  have hZ3leQ1 : Z3 ≤ d.Q1 := hZlt'.le
  have hQ2leQ1 : Q2 ≤ d.Q1 := hQ2leZ3.trans hZ3leQ1
  let : Group.IsNilpotent d.Q1 := d.isNilpotent_Q1_of_D_ne_bot hD
  let : Group.IsSolvable d.Q1 := IsNilpotent.to_isSolvable

  let : MulDistribMulAction d.D Z3 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := d.H) d.D Z3
      (Subgroup.le_normalizer_of_normal (H := Z3))
  have hregularZ3 : ActsRegularly d.D Z3 := by
    intro a ha
    apply le_antisymm
    · intro z hz
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hz
      have hfixZ : a • z = z := hz ⟨a, Subgroup.mem_zpowers a⟩
      have hfixH :
          (a : d.H) * (z : d.H) * (a : d.H)⁻¹ = (z : d.H) := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val hfixZ
      have haH : (a : d.H) ≠ 1 := by
        intro ha1
        exact ha (Subtype.ext ha1)
      let zQ1 : d.Q1 := ⟨(z : d.H), hZ3leQ1 z.property⟩
      have hz1 : zQ1 = 1 :=
        d.D_fixedPointFree_on_Q1 a haH zQ1 (by simpa [zQ1] using hfixH)
      apply Subtype.ext
      simpa [zQ1] using congrArg Subtype.val hz1
    · exact bot_le
  have hsolvZ3 : Group.IsSolvable Z3 :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hZ3leQ1)
      (Subgroup.inclusion_injective hZ3leQ1)
  have hcopZ3 : Nat.Coprime (Nat.card d.D) (Nat.card Z3) := by
    apply Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le (hZ3leQ1.trans d.Q1_le_Q))
    exact d.card_Q_coprime_card_D.symm
  let N2 : Subgroup Z3 := Q2.subgroupOf Z3
  let : N2.Normal := (inferInstance : Q2.Normal).subgroupOf Z3
  have hN2inv : IsInvariant d.D Z3 N2 := by
    refine ⟨?_⟩
    intro a z
    constructor
    · intro hz
      change (z : d.H) ∈ Q2 at hz
      change ((a • z : Z3) : d.H) ∈ Q2
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        (inferInstance : Q2.Normal).conj_mem (z : d.H) hz (a : d.H)
    · intro hz
      change ((a • z : Z3) : d.H) ∈ Q2 at hz
      have hz' :
          (a : d.H) * (z : d.H) * (a : d.H)⁻¹ ∈ Q2 := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hz
      have :=
        (inferInstance : Q2.Normal).conj_mem
          ((a : d.H) * (z : d.H) * (a : d.H)⁻¹) hz' (a : d.H)⁻¹
      change (z : d.H) ∈ Q2
      simpa [mul_assoc] using this
  let : MulAction.QuotientAction d.D N2 :=
    quotientAction_of_isInvariant (A := d.D) (G := Z3) N2 hN2inv
  let : MulDistribMulAction d.D (Z3 ⧸ N2) :=
    quotientMulDistribMulAction (A := d.D) (G := Z3) N2 hN2inv
  have hregularN2 : ActsRegularly d.D (Z3 ⧸ N2) :=
    actsRegularly_quotient_of_solvable_coprime_appendixIV
      hsolvZ3 hcopZ3 N2 hN2inv hregularZ3
  have hnontrivN2 : Nontrivial (Z3 ⧸ N2) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hQ2lt'.2 (Subgroup.subgroupOf_eq_top.mp htop)
  have hboundB :
      Nat.card d.D + 1 ≤ Q2.relIndex Z3 := by
    simpa [N2, Subgroup.relIndex, Subgroup.index_eq_card] using
      (natCard_add_one_le_of_actsRegularly_appendixIV
        hregularN2 hnontrivN2)

  let : MulDistribMulAction d.D d.Q1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := d.H) d.D d.Q1
      (Subgroup.le_normalizer_of_normal (H := d.Q1))
  have hregularQ1 : ActsRegularly d.D d.Q1 := by
    intro a ha
    apply le_antisymm
    · intro q hq
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hq
      have hfixQ : a • q = q := hq ⟨a, Subgroup.mem_zpowers a⟩
      have hfixH :
          (a : d.H) * (q : d.H) * (a : d.H)⁻¹ = (q : d.H) := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
          congrArg Subtype.val hfixQ
      have haH : (a : d.H) ≠ 1 := by
        intro ha1
        exact ha (Subtype.ext ha1)
      have hq1 : q = 1 :=
        d.D_fixedPointFree_on_Q1 a haH q hfixH
      exact hq1
    · exact bot_le
  have hcopQ1 : Nat.Coprime (Nat.card d.D) (Nat.card d.Q1) := by
    apply Nat.Coprime.of_dvd_right
      (Subgroup.card_dvd_of_le d.Q1_le_Q)
    exact d.card_Q_coprime_card_D.symm
  let NZ : Subgroup d.Q1 := Z3.subgroupOf d.Q1
  let : NZ.Normal := (inferInstance : Z3.Normal).subgroupOf d.Q1
  have hNZinv : IsInvariant d.D d.Q1 NZ := by
    refine ⟨?_⟩
    intro a q
    constructor
    · intro hq
      change (q : d.H) ∈ Z3 at hq
      change ((a • q : d.Q1) : d.H) ∈ Z3
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        (inferInstance : Z3.Normal).conj_mem (q : d.H) hq (a : d.H)
    · intro hq
      change ((a • q : d.Q1) : d.H) ∈ Z3 at hq
      have hq' :
          (a : d.H) * (q : d.H) * (a : d.H)⁻¹ ∈ Z3 := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hq
      have :=
        (inferInstance : Z3.Normal).conj_mem
          ((a : d.H) * (q : d.H) * (a : d.H)⁻¹) hq' (a : d.H)⁻¹
      change (q : d.H) ∈ Z3
      simpa [mul_assoc] using this
  let : MulAction.QuotientAction d.D NZ :=
    quotientAction_of_isInvariant (A := d.D) (G := d.Q1) NZ hNZinv
  let : MulDistribMulAction d.D (d.Q1 ⧸ NZ) :=
    quotientMulDistribMulAction (A := d.D) (G := d.Q1) NZ hNZinv
  have hregularNZ : ActsRegularly d.D (d.Q1 ⧸ NZ) :=
    actsRegularly_quotient_of_solvable_coprime_appendixIV
      (inferInstance : Group.IsSolvable d.Q1) hcopQ1 NZ hNZinv hregularQ1
  have hnontrivNZ : Nontrivial (d.Q1 ⧸ NZ) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    exact hZlt'.2 (Subgroup.subgroupOf_eq_top.mp htop)
  have hNZeq : NZ = Z0 := by
    ext q
    constructor
    · intro hq
      change (q : d.H) ∈ Z3 at hq
      rcases Subgroup.mem_map.mp hq with ⟨z, hz, hzq⟩
      have hzq' : z = q := Subtype.ext hzq
      simpa [hzq'] using hz
    · intro hq
      change (q : d.H) ∈ Z3
      exact Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
  have hboundA :
      Nat.card d.D + 1 ≤ Z0.index := by
    have hbound :
        Nat.card d.D + 1 ≤ Z3.relIndex d.Q1 := by
      simpa [NZ, Subgroup.relIndex, Subgroup.index_eq_card] using
        (natCard_add_one_le_of_actsRegularly_appendixIV
          hregularNZ hnontrivNZ)
    simpa [Subgroup.relIndex, NZ, hNZeq] using hbound

  have hmulIndex :
      Q2.relIndex Z3 * Z0.index = Q2.relIndex d.Q1 := by
    have hmul :=
      Subgroup.relIndex_mul_relIndex Q2 Z3 d.Q1 hQ2leZ3 hZ3leQ1
    simpa [Subgroup.relIndex, NZ, hNZeq] using hmul
  have hQindex :
      d.Q.relIndex (⊤ : Subgroup d.H) = Nat.card d.D := by
    let hsemi : Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup d.H) d.Q d.D := by
      refine
        { left_le := le_top
          right_le := le_top
          right_normalizes_left := ?_
          inf_eq_bot := d.Q_disjoint_D.eq_bot
          mul_surjective := ?_ }
      · intro e he q hq
        exact d.Q_normal.conj_mem q hq e
      · intro x _hx
        have hx : x ∈ d.Q ⊔ d.D := by
          rw [d.H_eq_Q_sup_D]
          trivial
        rcases Subgroup.mem_sup_of_normal_left.mp hx with
          ⟨q, hq, e, he, hqe⟩
        exact ⟨q, hq, e, he, hqe.symm⟩
    simpa using
      Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi
  have hm : 1 < Nat.card d.D :=
    (Subgroup.one_lt_card_iff_ne_bot d.D).2 hD
  have hmR : (1 : Real) < Nat.card d.D := by exact_mod_cast hm
  have hAR : (Nat.card d.D : Real) + 1 ≤ Z0.index := by
    exact_mod_cast hboundA
  have hBR : (Nat.card d.D : Real) + 1 ≤ Q2.relIndex Z3 := by
    exact_mod_cast hboundB
  have hmulR :
      (Q2.relIndex Z3 : Real) * Z0.index =
        Q2.relIndex d.Q1 := by
    exact_mod_cast hmulIndex
  have hm0 : (0 : Real) ≤ Nat.card d.D := by positivity
  have ha0 : (0 : Real) ≤ Z0.index := by positivity
  have hb0 : (0 : Real) ≤ Q2.relIndex Z3 := by positivity
  have hba :
      ((Nat.card d.D : Real) + 1) * Z0.index ≤
        (Q2.relIndex Z3 : Real) * Z0.index :=
    mul_le_mul_of_nonneg_right hBR ha0
  have hbase0 :
      (0 : Real) ≤ ((Nat.card d.D : Real) + 1) * Z0.index - 1 := by
    nlinarith [mul_nonneg
      (show (0 : Real) ≤ (Nat.card d.D : Real) + 1 by positivity) ha0]
  have hc_nonneg :
      (0 : Real) ≤ (Q2.relIndex d.Q1 : Real) - 1 := by
    rw [← hmulR]
    linarith
  have hpsi_nonneg : (0 : Real) ≤ 2 * psiDegreeRe :=
    hc_nonneg.trans h11
  have hsq :
      ((Q2.relIndex d.Q1 : Real) - 1) ^ 2 ≤
        (2 * psiDegreeRe) ^ 2 :=
    (sq_le_sq₀ hc_nonneg hpsi_nonneg).2 h11
  have hsq' :
      ((Q2.relIndex d.Q1 : Real) - 1) ^ 2 ≤
        4 * (Nat.card d.D : Real) ^ 2 * (Z0.index : Real) := by
    rw [hQindex] at h12
    nlinarith
  have hbase_le :
      (((Nat.card d.D : Real) + 1) * Z0.index - 1) ^ 2 ≤
        ((Q2.relIndex Z3 : Real) * Z0.index - 1) ^ 2 := by
    apply (sq_le_sq₀ hbase0 (by
      linarith : (0 : Real) ≤
        (Q2.relIndex Z3 : Real) * Z0.index - 1)).2
    linarith
  have hupper :
      (((Nat.card d.D : Real) + 1) * Z0.index - 1) ^ 2 ≤
        4 * (Nat.card d.D : Real) ^ 2 * (Z0.index : Real) := by
    rw [← hmulR] at hsq'
    exact hbase_le.trans hsq'
  have haSum :
      2 * ((Nat.card d.D : Real) + 1) ≤
        (Z0.index : Real) + ((Nat.card d.D : Real) + 1) := by
    linarith
  have hmulLower :
      ((Nat.card d.D : Real) + 1) ^ 2 *
          (2 * ((Nat.card d.D : Real) + 1)) ≤
        ((Nat.card d.D : Real) + 1) ^ 2 *
          ((Z0.index : Real) + ((Nat.card d.D : Real) + 1)) :=
    mul_le_mul_of_nonneg_left haSum (sq_nonneg _)
  have hlowNonneg :
      (0 : Real) ≤
        ((Nat.card d.D : Real) + 1) ^ 2 *
            (2 * ((Nat.card d.D : Real) + 1)) -
          2 * ((Nat.card d.D : Real) + 1) -
          4 * (Nat.card d.D : Real) ^ 2 := by
    have heq :
        ((Nat.card d.D : Real) + 1) ^ 2 *
              (2 * ((Nat.card d.D : Real) + 1)) -
            2 * ((Nat.card d.D : Real) + 1) -
            4 * (Nat.card d.D : Real) ^ 2 =
          2 * (Nat.card d.D : Real) *
            ((Nat.card d.D : Real) ^ 2 + Nat.card d.D + 2) := by
      ring
    rw [heq]
    positivity
  have hB :
      (0 : Real) ≤
        ((Nat.card d.D : Real) + 1) ^ 2 *
            ((Z0.index : Real) + ((Nat.card d.D : Real) + 1)) -
          2 * ((Nat.card d.D : Real) + 1) -
          4 * (Nat.card d.D : Real) ^ 2 := by
    linarith
  have ht :
      (0 : Real) ≤ (Z0.index : Real) -
        ((Nat.card d.D : Real) + 1) := by
    linarith
  have hprod :
      (0 : Real) ≤
        ((Z0.index : Real) - ((Nat.card d.D : Real) + 1)) *
          (((Nat.card d.D : Real) + 1) ^ 2 *
              ((Z0.index : Real) + ((Nat.card d.D : Real) + 1)) -
            2 * ((Nat.card d.D : Real) + 1) -
            4 * (Nat.card d.D : Real) ^ 2) :=
    mul_nonneg ht hB
  have hstrict :
      4 * (Nat.card d.D : Real) ^ 2 * (Z0.index : Real) <
        (((Nat.card d.D : Real) + 1) * Z0.index - 1) ^ 2 := by
    have hid :
        (((Nat.card d.D : Real) + 1) * Z0.index - 1) ^ 2 -
              4 * (Nat.card d.D : Real) ^ 2 * (Z0.index : Real) =
          (Nat.card d.D : Real) ^ 4 +
            ((Z0.index : Real) - ((Nat.card d.D : Real) + 1)) *
              (((Nat.card d.D : Real) + 1) ^ 2 *
                  ((Z0.index : Real) +
                    ((Nat.card d.D : Real) + 1)) -
                2 * ((Nat.card d.D : Real) + 1) -
                4 * (Nat.card d.D : Real) ^ 2) := by
      ring
    rw [← sub_pos, hid]
    positivity
  exact (not_lt_of_ge hupper) hstrict

private theorem actor_dvd_group_card_sub_one_appendixIV
    {A E : Type*} [Group A] [Finite A] [Group E] [Finite E]
    [MulDistribMulAction A E]
    (hfree : forall a : A, a ≠ 1 -> forall e : E, a • e = e -> e = 1) :
    Nat.card A ∣ Nat.card E - 1 := by
  classical
  let alpha := {e : E // e ≠ 1}
  let : MulAction A alpha :=
    { smul := fun a e => ⟨a • (e : E), by
        intro h
        apply e.2
        have h' := congrArg (fun x : E => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro e
        apply Subtype.ext
        change (1 : A) • (e : E) = (e : E)
        simp
      mul_smul := by
        intro a b e
        apply Subtype.ext
        change (a * b) • (e : E) = a • (b • (e : E))
        rw [mul_smul] }
  have hstab : forall e : alpha, MulAction.stabilizer A e = ⊥ := by
    intro e
    rw [eq_bot_iff]
    intro a ha
    have hae : a • e = e := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha_not_bot
    have ha_ne : a ≠ 1 := by
      intro ha1
      apply ha_not_bot
      simp [ha1]
    have hfix : a • (e : E) = (e : E) := congrArg Subtype.val hae
    exact e.2 (hfree a ha_ne (e : E) hfix)
  have hcard_equiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcard_alpha : Nat.card alpha = Nat.card E - 1 := by
    let : Fintype E := Fintype.ofFinite E
    let : Fintype alpha := Fintype.ofFinite alpha
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {e : E // e ≠ 1} = Fintype.card E - 1
    simp
  rw [hcard_alpha, Nat.card_prod] at hcard_equiv
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A alpha)), by
    rw [mul_comm]
    exact hcard_equiv⟩

private theorem two_mul_add_one_le_of_odd_dvd_card_sub_one_appendixIV
    {a e : Nat} (haodd : Odd a) (heodd : Odd e)
    (he : 1 < e) (hdiv : a ∣ e - 1) :
    2 * a + 1 ≤ e := by
  rcases hdiv with ⟨k, hk⟩
  have heven_sub : Even (e - 1) := by
    apply (Nat.even_sub' (by omega)).2
    exact ⟨fun _ => odd_one, fun _ => heodd⟩
  have heven_mul : Even (a * k) := by
    rw [← hk]
    exact heven_sub
  have hk_even : Even k := by
    rw [← Nat.not_odd_iff_even]
    intro hkodd
    exact (Nat.not_even_iff_odd.mpr (haodd.mul hkodd)) heven_mul
  have hkpos : 0 < k := by
    by_contra hknpos
    have hkzero : k = 0 := by omega
    rw [hkzero, mul_zero] at hk
    omega
  rcases hk_even with ⟨m, hm⟩
  have hktwo : 2 ≤ k := by omega
  calc
    2 * a + 1 = a * 2 + 1 := by omega
    _ ≤ a * k + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left a hktwo) 1
    _ = (e - 1) + 1 := by rw [hk]
    _ = e := Nat.sub_add_cancel (by omega)

set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem feitSibley_step2_center_card_lower_bound_nilpotent_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    [Group.IsNilpotent d.Q1]
    (hDodd : Odd (Nat.card d.D)) :
    2 * Nat.card d.D + 1 ≤ Nat.card (Subgroup.center d.Q1) := by
  classical
  let : d.Q1.Normal := d.Q1_normal
  let : MulDistribMulAction d.D d.Q1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := d.H) d.D d.Q1
      (Subgroup.le_normalizer_of_normal (H := d.Q1))
  let : IsInvariant d.D d.Q1 (Subgroup.center d.Q1) := by
    infer_instance
  let : MulDistribMulAction d.D (Subgroup.center d.Q1) :=
    instMulDistribMulAction_subtype (G := d.Q1) (A := d.D)
  have hfreeCenter :
      ∀ a : d.D, a ≠ 1 →
        ∀ z : Subgroup.center d.Q1, a • z = z → z = 1 := by
    intro a ha z hfix
    have hfixQ1 : a • (z : d.Q1) = (z : d.Q1) :=
      congrArg Subtype.val hfix
    have hfixH :
        (a : d.H) * ((z : d.Q1) : d.H) * (a : d.H)⁻¹ =
          ((z : d.Q1) : d.H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfixQ1
    have haH : (a : d.H) ≠ 1 := by
      intro ha1
      exact ha (Subtype.ext ha1)
    have hz1 : (z : d.Q1) = 1 :=
      d.D_fixedPointFree_on_Q1 a haH (z : d.Q1) hfixH
    apply Subtype.ext
    exact hz1
  have hdiv :
      Nat.card d.D ∣ Nat.card (Subgroup.center d.Q1) - 1 :=
    actor_dvd_group_card_sub_one_appendixIV hfreeCenter
  have hcenterOdd : Odd (Nat.card (Subgroup.center d.Q1)) :=
    odd_of_card_dvd d.Q1_odd
      (Subgroup.card_subgroup_dvd_card (Subgroup.center d.Q1))
  have hQ1ne : d.Q1 ≠ ⊥ := by
    intro hQ1
    apply d.Q1_not_two_group
    rw [hQ1]
    exact IsPGroup.of_bot (p := 2) (G := d.H)
  let : Nontrivial d.Q1 :=
    (Subgroup.nontrivial_iff_ne_bot d.Q1).2 hQ1ne
  have hcenterne : Subgroup.center d.Q1 ≠ ⊥ := by
    have hinter :=
      Section6.nilpotent_normal_inf_center_ne_bot
        (⊤ : Subgroup d.Q1) (top_ne_bot : (⊤ : Subgroup d.Q1) ≠ ⊥)
    simpa using hinter
  have : Nontrivial (Subgroup.center d.Q1) :=
    (Subgroup.nontrivial_iff_ne_bot (Subgroup.center d.Q1)).2 hcenterne
  have hcenterCard : 1 < Nat.card (Subgroup.center d.Q1) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  exact two_mul_add_one_le_of_odd_dvd_card_sub_one_appendixIV
    hDodd hcenterOdd hcenterCard hdiv
private theorem feitSibley_step2_center_card_lower_bound_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (hD : d.D ≠ ⊥) (hDodd : Odd (Nat.card d.D)) :
    2 * Nat.card d.D + 1 ≤ Nat.card (Subgroup.center d.Q1) := by
  let : Group.IsNilpotent d.Q1 :=
    d.isNilpotent_Q1_of_D_ne_bot hD
  exact feitSibley_step2_center_card_lower_bound_nilpotent_core d hDodd

private theorem feitSibley_Q_relIndex_top_eq_card_D_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    d.Q.relIndex (⊤ : Subgroup d.H) = Nat.card d.D := by
  let : d.Q.Normal := d.Q_normal
  let hsemi : Section2.IsInternalSemidirectProduct
      (⊤ : Subgroup d.H) d.Q d.D := by
    refine
      { left_le := le_top
        right_le := le_top
        right_normalizes_left := ?_
        inf_eq_bot := d.Q_disjoint_D.eq_bot
        mul_surjective := ?_ }
    · intro e he q hq
      exact d.Q_normal.conj_mem q hq e
    · intro x _hx
      have hx : x ∈ d.Q ⊔ d.D := by
        rw [d.H_eq_Q_sup_D]
        trivial
      rcases Subgroup.mem_sup_of_normal_left.mp hx with
        ⟨q, hq, e, he, hqe⟩
      exact ⟨q, hq, e, he, hqe.symm⟩
  exact Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemi

private theorem feitSibley_step2_quotient_card_factor_core
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (R1 : Subgroup d.H) [R1.Normal]
    (hR1leS : R1 ≤ d.S) :
    Nat.card (d.H ⧸ R1) =
        Nat.card d.D * R1.relIndex d.S * Nat.card d.Q1 ∧
      Nat.card (d.H ⧸ (R1 ⊔ d.Q1)) =
        Nat.card d.D * R1.relIndex d.S := by
  classical
  let : d.Q1.Normal := d.Q1_normal
  let : d.Q.Normal := d.Q_normal
  let hsemiSQ : Section2.IsInternalSemidirectProduct d.Q d.S d.Q1 := by
    refine
      { left_le := d.S_le_Q
        right_le := d.Q1_le_Q
        right_normalizes_left := ?_
        inf_eq_bot := d.S_disjoint_Q1.eq_bot
        mul_surjective := ?_ }
    · intro q hq s hs
      rw [Section2.conjBy, ← d.S_commutes_Q1 s q hs hq]
      simpa using hs
    · intro x hx
      have hx' : x ∈ d.S ⊔ d.Q1 := by
        rw [d.Q_eq_S_sup_Q1]
        exact hx
      rcases Subgroup.mem_sup_of_normal_right.mp hx' with
        ⟨s, hs, q, hq, hsq⟩
      exact ⟨s, hs, q, hq, hsq.symm⟩
  have hSindexQ : d.S.relIndex d.Q = Nat.card d.Q1 :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemiSQ
  let hsemiQD : Section2.IsInternalSemidirectProduct
      (⊤ : Subgroup d.H) d.Q d.D := by
    refine
      { left_le := le_top
        right_le := le_top
        right_normalizes_left := ?_
        inf_eq_bot := d.Q_disjoint_D.eq_bot
        mul_surjective := ?_ }
    · intro e he q hq
      exact d.Q_normal.conj_mem q hq e
    · intro x _hx
      have hx : x ∈ d.Q ⊔ d.D := by
        rw [d.H_eq_Q_sup_D]
        trivial
      rcases Subgroup.mem_sup_of_normal_left.mp hx with
        ⟨q, hq, e, he, hqe⟩
      exact ⟨q, hq, e, he, hqe.symm⟩
  have hQindexH :
      d.Q.relIndex (⊤ : Subgroup d.H) = Nat.card d.D :=
    Section2.internalSemidirectProduct_left_relIndex_eq_card_right hsemiQD
  have hR1leQ : R1 ≤ d.Q := hR1leS.trans d.S_le_Q
  have hR1Q :
      R1.relIndex d.Q =
        R1.relIndex d.S * Nat.card d.Q1 := by
    have hmul :=
      Subgroup.relIndex_mul_relIndex R1 d.S d.Q hR1leS d.S_le_Q
    rw [hSindexQ] at hmul
    exact hmul.symm
  have hR1H :
      R1.relIndex (⊤ : Subgroup d.H) =
        Nat.card d.D * R1.relIndex d.S * Nat.card d.Q1 := by
    have hmul :=
      Subgroup.relIndex_mul_relIndex R1 d.Q (⊤ : Subgroup d.H)
        hR1leQ le_top
    calc
      R1.relIndex (⊤ : Subgroup d.H) =
          R1.relIndex d.Q * d.Q.relIndex (⊤ : Subgroup d.H) :=
        hmul.symm
      _ = (R1.relIndex d.S * Nat.card d.Q1) * Nat.card d.D := by
        rw [hR1Q, hQindexH]
      _ = Nat.card d.D * R1.relIndex d.S * Nat.card d.Q1 := by
        ac_rfl
  let U : Subgroup d.H := R1 ⊔ d.Q1
  let : U.Normal := by
    dsimp [U]
    infer_instance
  have hUleQ : U ≤ d.Q :=
    sup_le hR1leQ d.Q1_le_Q
  have hUS : U ⊓ d.S = R1 := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxU, hxS⟩
      rcases Subgroup.mem_sup_of_normal_right.mp hxU with
        ⟨r, hr, q, hq, hrqx⟩
      have hqS : q ∈ d.S := by
        have hqeq : q = r⁻¹ * x := by
          rw [← hrqx]
          simp
        rw [hqeq]
        exact d.S.mul_mem (d.S.inv_mem (hR1leS hr)) hxS
      have hqone : q = 1 := by
        apply Subgroup.mem_bot.mp
        exact d.S_disjoint_Q1.le_bot ⟨hqS, hq⟩
      rw [hqone, mul_one] at hrqx
      exact hrqx ▸ hr
    · intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨(show R1 ≤ U from le_sup_left) hx, hR1leS hx⟩
  have hU_sup_S : U ⊔ d.S = d.Q := by
    calc
      U ⊔ d.S = d.S ⊔ (R1 ⊔ d.Q1) := by
        rw [sup_comm]
      _ = (d.S ⊔ R1) ⊔ d.Q1 := by
        rw [sup_assoc]
      _ = d.S ⊔ d.Q1 := by
        rw [sup_eq_left.mpr hR1leS]
      _ = d.Q := d.Q_eq_S_sup_Q1
  have hUindexQ :
      U.relIndex d.Q = R1.relIndex d.S := by
    calc
      U.relIndex d.Q = U.relIndex (U ⊔ d.S) := by rw [hU_sup_S]
      _ = U.relIndex d.S :=
        Subgroup.relIndex_sup_left d.S U
      _ = (U ⊓ d.S).relIndex d.S :=
        (Subgroup.inf_relIndex_right U d.S).symm
      _ = R1.relIndex d.S := by rw [hUS]
  have hUH :
      U.relIndex (⊤ : Subgroup d.H) =
        Nat.card d.D * R1.relIndex d.S := by
    have hmul :=
      Subgroup.relIndex_mul_relIndex U d.Q (⊤ : Subgroup d.H)
        hUleQ le_top
    calc
      U.relIndex (⊤ : Subgroup d.H) =
          U.relIndex d.Q * d.Q.relIndex (⊤ : Subgroup d.H) :=
        hmul.symm
      _ = R1.relIndex d.S * Nat.card d.D := by
        rw [hUindexQ, hQindexH]
      _ = Nat.card d.D * R1.relIndex d.S := by
        ac_rfl
  constructor
  · simpa [Subgroup.relIndex_top_right, Subgroup.index_eq_card] using hR1H
  · simpa [U, Subgroup.relIndex_top_right, Subgroup.index_eq_card] using hUH

private theorem feitSibley_step2_degree_inequality_core
    (m s q z c n : Nat) (a : Real)
    (hm : 0 < m) (hs : 0 < s) (hz : 0 < z) (hc : 0 < c)
    (hsum : a + (s : Real) * m = (s : Real) * q * m)
    (hbound : a ≤ 2 * ((n : Real) * m) * m)
    (hnSq : n ^ 2 ≤ s * c)
    (hcz : c * z = q) :
    (s : Real) * (z : Real) * ((q : Real) - 2) <
      4 * (m : Real) ^ 2 := by
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have hsR : (0 : Real) < s := by exact_mod_cast hs
  have hzR : (0 : Real) < z := by exact_mod_cast hz
  have hcR : (0 : Real) < c := by exact_mod_cast hc
  have hnSqR : (n : Real) ^ 2 ≤ (s : Real) * c := by
    exact_mod_cast hnSq
  have hczR : (c : Real) * z = q := by exact_mod_cast hcz
  have hqR : (0 : Real) < q := by nlinarith
  have hlin :
      (s : Real) * ((q : Real) - 1) ≤
        2 * (n : Real) * m := by
    nlinarith
  have hqpos : 0 < q := by exact_mod_cast hqR
  have hqone : (1 : Real) ≤ q := by exact_mod_cast hqpos
  have hlinNonneg :
      (0 : Real) ≤ (s : Real) * ((q : Real) - 1) := by
    exact mul_nonneg hsR.le (sub_nonneg.mpr hqone)
  have hnNonneg : (0 : Real) ≤ 2 * (n : Real) * m := by positivity
  have hsq :
      ((s : Real) * ((q : Real) - 1)) ^ 2 ≤
        (2 * (n : Real) * m) ^ 2 :=
    (sq_le_sq₀ hlinNonneg hnNonneg).2 hlin
  have hnSqMul :
      (n : Real) ^ 2 * (m : Real) ^ 2 ≤
        ((s : Real) * c) * (m : Real) ^ 2 :=
    mul_le_mul_of_nonneg_right hnSqR (sq_nonneg (m : Real))
  have hsqBound :
      (s : Real) * ((q : Real) - 1) ^ 2 ≤
        4 * (c : Real) * (m : Real) ^ 2 := by
    nlinarith
  have hscaled0 := mul_le_mul_of_nonneg_left hsqBound hzR.le
  have hscaled :
      (s : Real) * (z : Real) * ((q : Real) - 1) ^ 2 ≤
        4 * (q : Real) * (m : Real) ^ 2 := by
    nlinarith
  have hstrictScaled :
      (q : Real) * ((s : Real) * (z : Real) * ((q : Real) - 2)) <
        (q : Real) * (4 * (m : Real) ^ 2) := by
    nlinarith [mul_pos hsR hzR]
  nlinarith

private theorem feitSibley_step2_arithmetic_core
    (m z s q : Nat)
    (hm : 1 ≤ m)
    (hz : 2 * m + 1 ≤ z)
    (hzq : z ≤ q)
    (hs : 2 ≤ s)
    (hineq :
      (s : Real) * (z : Real) * ((q : Real) - 2) <
        4 * (m : Real) ^ 2) :
    False := by
  have hmR : (1 : Real) ≤ m := by exact_mod_cast hm
  have hzR : 2 * (m : Real) + 1 ≤ (z : Real) := by exact_mod_cast hz
  have hzqR : (z : Real) ≤ (q : Real) := by exact_mod_cast hzq
  have hsR : (2 : Real) ≤ (s : Real) := by exact_mod_cast hs
  have hqm2 : (0 : Real) ≤ (q : Real) - 2 := by nlinarith
  have hz0 : (0 : Real) ≤ (z : Real) := by positivity
  have htwoz :
      (2 : Real) * (z : Real) * ((q : Real) - 2) ≤
        (s : Real) * (z : Real) * ((q : Real) - 2) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsR hz0) hqm2
  have hzlower :
      (2 : Real) * (2 * (m : Real) + 1) * ((q : Real) - 2) ≤
        (2 : Real) * (z : Real) * ((q : Real) - 2) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hzR (by positivity)) hqm2
  have hqm2lower :
      (2 : Real) * (2 * (m : Real) + 1) * (2 * (m : Real) - 1) ≤
        (2 : Real) * (2 * (m : Real) + 1) * ((q : Real) - 2) := by
    apply mul_le_mul_of_nonneg_left
    · nlinarith
    · positivity
  nlinarith [htwoz, hzlower, hqm2lower]

private theorem feitSibley_step2_arithmetic_contradiction_core
    (m z s q : Nat)
    (hm : Odd m)
    (hz : 2 * m + 1 ≤ z)
    (hzq : z ≤ q)
    (hs : 2 ≤ s)
    (hineq :
      (s : Real) * (z : Real) * ((q : Real) - 2) <
        4 * (m : Real) ^ 2) :
    False := by
  have hm1 : 1 ≤ m := by
    rcases hm with ⟨k, hk⟩
    omega
  exact feitSibley_step2_arithmetic_core m z s q hm1 hz hzq hs hineq

private theorem feitSibley_coherent_of_D_eq_bot_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D))
    (hD : d.D = ⊥) :
    feitSibleyCoherent d chars := by
  classical
  let : IsZGroup d.Q1 := d.isZGroup_Q1_of_D_eq_bot hD
  have hsolvQ1 : Group.IsSolvable d.Q1 := by infer_instance
  obtain ⟨chi, hchiChars, _hchiKernel⟩ :=
    d.exists_exceptional_mem_derived_kernel
      chars hchars hsolvQ1 d.internalDirectProduct_Q
  have hbarChars : conjugateCharacter chi ∈ chars := by
    let : d.Q.Normal := d.Q_normal
    rcases (lemma_2_a d chars hchars chi).mp hchiChars with
      ⟨phi, hphiIrr, hphiNotKernel, hind⟩
    apply (lemma_2_a d chars hchars (conjugateCharacter chi)).mpr
    refine ⟨conjugateCharacter phi,
      isIrreducibleCharacterOnGroup_conjugateCharacter hphiIrr, ?_, ?_⟩
    · intro hbarKernelQ1
      apply hphiNotKernel
      have hdouble :=
        Section6.subgroupInKernel'_conjugateCharacter
          (conjugateCharacter phi) hbarKernelQ1
      have hcc : conjugateCharacter (conjugateCharacter phi) = phi := by
        ext q
        simp [conjugateCharacter]
      simpa [hcc] using hdouble
    · calc
        inducedCF d.Q (conjugateCharacter phi) =
            conjugateCharacter (inducedCF d.Q phi) :=
          (conjugateCharacter_inducedCF d.Q phi).symm
        _ = conjugateCharacter chi := by rw [hind]
  have hbarNe : conjugateCharacter chi ≠ chi :=
    lemma_2_c d chars hchars hDodd chi hchiChars
  have hsourceNonempty : integerSpanOnNonempty chars puncturedSet :=
    integerSpanOnNonempty_of_conjugate_pair
      hchiChars hbarChars hbarNe.symm
      (isCharacter_of_isIrreducibleCharacterOnGroup
        ((hchars chi).mp hchiChars).1)
  have hQtop : d.Q = ⊤ := by
    simpa [hD] using d.H_eq_Q_sup_D
  have hQInG_eq_H : d.QInG = d.H := by
    rw [FeitSibleyData.QInG, hQtop]
    simpa [MonoidHom.range_eq_map] using
      (d.H.range_subtype : d.H.subtype.range = d.H)
  have hQ1ne : d.Q1 ≠ ⊥ := by
    intro hQ1
    apply d.Q1_not_two_group
    exact hQ1.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
  have hQne : d.Q ≠ ⊥ := by
    intro hQ
    apply hQ1ne
    apply le_bot_iff.mp
    simpa [hQ] using d.Q1_le_Q
  have hQInGne : d.QInG ≠ ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (H := d.Q) (f := d.H.subtype) d.H.subtype_injective).not.mpr hQne
  have hHne : d.H ≠ ⊥ := by
    simpa [hQInG_eq_H] using hQInGne
  have hTI : ∀ g : G, g ∉ d.H → Disjoint d.H (d.H.conjBy g) := by
    intro g hg
    have hginv : g⁻¹ ∉ d.H := by
      intro h
      apply hg
      simpa using d.H.inv_mem h
    rw [← hQInG_eq_H]
    simpa [FeitSibleyData.QInG,
      PFchapter1section1.rightConjugate] using
      d.Q_TI_in_G g⁻¹ hginv
  apply coherent_of_TI_exceptional d.H hHne hTI chars
  · intro chi hchi
    exact ((hchars chi).mp hchi).1
  · exact hsourceNonempty
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem feitSibley_step2_chief_factor_contradiction_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D))
    (hD : d.D ≠ ⊥)
    (R1 R2 : Subgroup d.H) [R1.Normal] [R2.Normal]
    (hR1le : R1 ≤ feitSibleySderivedH d)
    (hchief : IsChiefFactor R2 R1)
    (hcoherentR1 :
      feitSibleyCoherent d (feitSibleySker d chars R1))
    (hnotcoherentR2 :
      ¬ feitSibleyCoherent d (feitSibleySker d chars R2)) :
    False := by
  classical
  let : d.S.Normal := d.S_normal
  let : d.Q1.Normal := d.Q1_normal
  let : Group.IsNilpotent d.S := d.S_nilpotent
  let : Group.IsNilpotent d.Q1 := d.isNilpotent_Q1_of_D_ne_bot hD
  let : Group.IsSolvable d.Q1 := IsNilpotent.to_isSolvable
  have hSderivedLeS : feitSibleySderivedH d ≤ d.S := by
    simpa [feitSibleySderivedH] using
      Subgroup.map_subtype_le (derivedSubgroup d.S)
  have hR1leS : R1 ≤ d.S := hR1le.trans hSderivedLeS
  have hR2leS : R2 ≤ d.S := hchief.lt.le.trans hR1leS
  have hQderived :
      feitSibleyQderivedH d =
        feitSibleySderivedH d ⊔ feitSibleyQ1derivedH d := by
    simpa [feitSibleyQderivedH, feitSibleySderivedH,
      feitSibleyQ1derivedH] using d.map_derivedSubgroup_Q_eq_sup
  have hR1leQderived : R1 ≤ feitSibleyQderivedH d := by
    rw [hQderived]
    exact hR1le.trans le_sup_left
  let U : Finset (ClassFunction d.H) :=
    feitSibleySker d chars R1
  let V : Finset (ClassFunction d.H) :=
    feitSibleySker d chars R2
  have hUV : U ⊆ V := by
    intro chi hchi
    rcases Finset.mem_filter.mp hchi with ⟨hchiChars, hchiKernel⟩
    refine Finset.mem_filter.mpr ⟨hchiChars, ?_⟩
    intro x
    exact hchiKernel ⟨x, hchief.lt.le x.property⟩
  obtain ⟨chi0, hchi0Chars, hchi0KernelQderived⟩ :=
    d.exists_exceptional_mem_derived_kernel
      chars hchars (inferInstance : Group.IsSolvable d.Q1)
        d.internalDirectProduct_Q
  have hchi0U : chi0 ∈ U := by
    refine Finset.mem_filter.mpr ⟨hchi0Chars, ?_⟩
    intro x
    exact hchi0KernelQderived ⟨x, hR1leQderived x.property⟩
  have hchi0Degree :
      degree chi0 =
        (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) :=
    d.degree_eq_relIndex_of_exceptional_derived_kernel
      chars hchars chi0 hchi0Chars hchi0KernelQderived
  have hVsub : V ⊆ chars := by
    intro chi hchi
    exact (Finset.mem_filter.mp hchi).1
  have hirrV :
      ∀ chi : V,
        IsIrreducibleCharacterOnGroup (chi : ClassFunction d.H) := by
    intro chi
    exact ((hchars (chi : ClassFunction d.H)).mp
      (hVsub chi.property)).1
  rcases lemma_2_b d chars hchars with ⟨hisoChars, htargetChars⟩
  have hisoV :
      isCFLinearIsometryOnSpanOn V puncturedSet
        (Section1.inducedCFLinear d.H) := by
    intro phi theta hphi htheta
    exact hisoChars phi theta
      (Section5.integerSpanOn_mono hVsub hphi)
      (Section5.integerSpanOn_mono hVsub htheta)
  have htargetV :
      ∀ phi : ClassFunction d.H,
        integerSpanOn V puncturedSet phi →
          Theory.Character.IsVirtualCharacter
              (Section1.inducedCFLinear d.H phi) ∧
            supportedOn
              (Section1.inducedCFLinear d.H phi) puncturedSet := by
    intro phi hphi
    exact htargetChars phi
      (Section5.integerSpanOn_mono hVsub hphi)
  have hdivV :
      ∀ psi : ClassFunction d.H, psi ∈ V →
        ∃ n : Nat,
          degree psi = (n : Complex) * degree chi0 := by
    intro psi hpsiV
    have hpsiChars : psi ∈ chars := hVsub hpsiV
    rcases (lemma_2_a d chars hchars psi).mp hpsiChars with
      ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
    rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
    refine ⟨n, ?_⟩
    rw [← hind, degree_inducedClassFunction d.Q phi,
      hphiEq, degree_representation_character, hchi0Degree]
    simp [Subgroup.relIndex_top_right, mul_comm]
  obtain ⟨psi, hpsiV, _hpsiU, hdegreeBound⟩ :=
    exists_degree_obstruction_of_not_coherent_appendixIV
      d.H U V (Section1.inducedCFLinear d.H) hUV chi0 hchi0U
      hirrV hisoV htargetV hdivV
      (by simpa [U] using hcoherentR1)
      (by simpa [V] using hnotcoherentR2)
  have hUchar :
      ∀ chi : ClassFunction d.H, chi ∈ U ↔
        IsIrreducibleCharacterOnGroup chi ∧
          subgroupInKernel' chi R1 ∧
            ¬ subgroupInKernel' chi d.Q1 := by
    intro chi
    simp only [U, feitSibleySker, Finset.mem_filter]
    rw [hchars chi]
    tauto
  have hsumU :=
    exceptional_kernel_degree_sq_sum_appendixIV
      R1 d.Q1 U hUchar
  have hpsiKernel : subgroupInKernel' psi R2 :=
    (Finset.mem_filter.mp hpsiV).2
  have hpsiChars : psi ∈ chars := hVsub hpsiV
  rcases (lemma_2_a d chars hchars psi).mp hpsiChars with
    ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
  rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
  have hR2leQ : R2 ≤ d.Q := hR2leS.trans d.S_le_Q
  let : d.Q.Normal := d.Q_normal
  have hindKerPhi : subgroupInKernel' (inducedCF d.Q phi) R2 := by
    rw [hind]
    exact hpsiKernel
  have hindKerRho : subgroupInKernel' (inducedCF d.Q rho.character) R2 := by
    simpa [hphiEq] using hindKerPhi
  have hrhoKerCF :
      subgroupInKernel' rho.character (R2.subgroupOf d.Q) :=
    (Section1.proposition_1_6_a d.Q R2 hR2leQ rho).mpr hindKerRho
  have hrepker :
      subgroupInRepresentationKernel rho (R2.subgroupOf d.Q) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho _).mp hrhoKerCF
  let N : Subgroup d.S := R2.subgroupOf d.S
  let : N.Normal := (inferInstance : R2.Normal).subgroupOf d.S
  let e : d.S × d.Q1 ≃* d.Q :=
    Section3.internalDirectProductMulEquiv d.internalDirectProduct_Q
  have hker : ∀ x : N.prod (⊥ : Subgroup d.Q1), rho (e x) = 1 := by
    intro x
    have hx2 : x.1.2 = 1 := Subgroup.mem_bot.mp x.property.2
    have hinl :
        ((e (MonoidHom.inl d.S d.Q1 x.1.1) : d.Q) : d.H) =
          (x.1.1 : d.H) := by
      simpa [e] using congrArg Subtype.val
        (Section3.internalDirectProductMulEquiv_apply_inl
          d.internalDirectProduct_Q x.1.1)
    have hinr :
        ((e (MonoidHom.inr d.S d.Q1 x.1.2) : d.Q) : d.H) =
          (x.1.2 : d.H) := by
      simpa [e] using congrArg Subtype.val
        (Section3.internalDirectProductMulEquiv_apply_inr
          d.internalDirectProduct_Q x.1.2)
    have hxdecomp :
        (x.1 : d.S × d.Q1) =
          MonoidHom.inl d.S d.Q1 x.1.1 *
            MonoidHom.inr d.S d.Q1 x.1.2 := by
      ext <;> simp
    have heq : ((e x : d.Q) : d.H) = (x.1.1 : d.H) := by
      rw [show e x = e (MonoidHom.inl d.S d.Q1 x.1.1 *
        MonoidHom.inr d.S d.Q1 x.1.2) from congrArg e hxdecomp]
      rw [map_mul]
      change ((e (MonoidHom.inl d.S d.Q1 x.1.1) : d.Q) : d.H) *
          ((e (MonoidHom.inr d.S d.Q1 x.1.2) : d.Q) : d.H) = _
      rw [hinl, hinr, hx2]
      simp
    apply hrepker ⟨e x, ?_⟩
    change ((e x : d.Q) : d.H) ∈ R2
    rw [heq]
    exact x.property.1
  let : Representation.IsIrreducible rho := hrhoIrr
  have hnSq :
      n ^ 2 ≤
        (Subgroup.comap (QuotientGroup.mk' N)
          (Subgroup.center (d.S ⧸ N))).index *
        (Subgroup.center d.Q1).index := by
    simpa [N, e] using
      (irreducible_finrank_sq_le_centerModulo_index_mul_center_index_appendixIV
        e N rho hker)
  let ZS : Subgroup d.S :=
    Subgroup.comap (QuotientGroup.mk' N)
      (Subgroup.center (d.S ⧸ N))
  let R1S : Subgroup d.S := R1.subgroupOf d.S
  have hR1leZSmap : R1 ≤ ZS.map d.S.subtype := by
    simpa [ZS, N] using
      (chiefFactor_le_centerModulo_preimage_appendixIV
        d.S R1 R2 hchief hR1leS)
  have hR1SleZS : R1S ≤ ZS := by
    intro x hx
    have hxmap : (x : d.H) ∈ ZS.map d.S.subtype :=
      hR1leZSmap hx
    rcases Subgroup.mem_map.mp hxmap with ⟨z, hz, hzx⟩
    have hzx' : z = x := by
      apply Subtype.ext
      exact hzx
    simpa [hzx'] using hz
  have hZSindex : ZS.index ≤ R1S.index :=
    Subgroup.index_antitone hR1SleZS
  have hnSqBound :
      n ^ 2 ≤ R1S.index * (Subgroup.center d.Q1).index :=
    hnSq.trans (Nat.mul_le_mul_right (Subgroup.center d.Q1).index hZSindex)
  have hQindex :
      d.Q.relIndex (⊤ : Subgroup d.H) = Nat.card d.D :=
    feitSibley_Q_relIndex_top_eq_card_D_appendixIV d
  have hpsiDegree :
      degree psi =
        (n : Complex) *
          (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
    rw [← hind, degree_inducedClassFunction d.Q phi, hphiEq,
      degree_representation_character]
    simp [Subgroup.relIndex_top_right, mul_comm]
  have hpsiRe :
      (degree psi).re =
        (n : Real) * Nat.card d.D := by
    rw [hpsiDegree, hQindex]
    simp
  have hchi0Re :
      (degree chi0).re = (Nat.card d.D : Real) := by
    rw [hchi0Degree, hQindex]
    simp
  have hdegreeBound' :
      (∑ chi : U,
          (degree (chi : ClassFunction d.H)).re ^ 2) ≤
        2 * ((n : Real) * Nat.card d.D) * Nat.card d.D := by
    rw [hpsiRe, hchi0Re] at hdegreeBound
    exact hdegreeBound
  obtain ⟨hcardR1, hcardR1Q1⟩ :=
    feitSibley_step2_quotient_card_factor_core d R1 hR1leS
  have hsumFactor :
      (∑ chi : U,
          (degree (chi : ClassFunction d.H)).re ^ 2) +
          (R1S.index : Real) * Nat.card d.D =
        (R1S.index : Real) * Nat.card d.Q1 * Nat.card d.D := by
    rw [hcardR1, hcardR1Q1] at hsumU
    simpa [R1S, Subgroup.relIndex, mul_comm, mul_left_comm, mul_assoc] using hsumU
  have hm : 0 < Nat.card d.D := Nat.card_pos
  have hs : 0 < R1S.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have hz : 0 < Nat.card (Subgroup.center d.Q1) := Nat.card_pos
  have hc : 0 < (Subgroup.center d.Q1).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  have hcenterMul :
      (Subgroup.center d.Q1).index *
          Nat.card (Subgroup.center d.Q1) = Nat.card d.Q1 :=
    (Subgroup.center d.Q1).index_mul_card
  have hineq :
      (R1S.index : Real) *
          (Nat.card (Subgroup.center d.Q1) : Real) *
          ((Nat.card d.Q1 : Real) - 2) <
        4 * (Nat.card d.D : Real) ^ 2 :=
    feitSibley_step2_degree_inequality_core
      (Nat.card d.D) R1S.index (Nat.card d.Q1)
        (Nat.card (Subgroup.center d.Q1))
        (Subgroup.center d.Q1).index n
        (∑ chi : U,
          (degree (chi : ClassFunction d.H)).re ^ 2)
        hm hs hz hc hsumFactor hdegreeBound' hnSqBound hcenterMul
  have hR1ne : R1 ≠ ⊥ := by
    intro hR1
    subst R1
    exact (not_lt_of_ge bot_le) hchief.lt
  have hSne : d.S ≠ ⊥ := by
    intro hS
    apply hR1ne
    exact le_bot_iff.mp (by simpa [hS] using hR1leS)
  let : Nontrivial d.S :=
    (Subgroup.nontrivial_iff_ne_bot d.S).2 hSne
  have hR1SleDerived : R1S ≤ derivedSubgroup d.S := by
    intro x hx
    have hxmap := hR1le hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hyx' : y = x := by
      apply Subtype.ext
      exact hyx
    simpa [hyx'] using hy
  have hderivedLt : derivedSubgroup d.S < ⊤ := by
    change commutator d.S < ⊤
    let : Group.IsSolvable d.S := IsNilpotent.to_isSolvable
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial (G := d.S)
  have hR1Slt : R1S < ⊤ := hR1SleDerived.trans_lt hderivedLt
  have hsTwo : 2 ≤ R1S.index := by
    have hone := Subgroup.one_lt_index_of_ne_top hR1Slt.ne
    omega
  have hzLower :=
    feitSibley_step2_center_card_lower_bound_core d hD hDodd
  have hzq :
      Nat.card (Subgroup.center d.Q1) ≤ Nat.card d.Q1 :=
    Nat.card_le_card_of_injective
      (fun z : Subgroup.center d.Q1 => (z : d.Q1)) Subtype.val_injective
  exact feitSibley_step2_arithmetic_contradiction_core
    (Nat.card d.D) (Nat.card (Subgroup.center d.Q1))
      R1S.index (Nat.card d.Q1) hDodd hzLower hzq hsTwo hineq

private theorem feitSibley_step2_chief_descent_of_D_ne_bot_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D))
    (hD : d.D ≠ ⊥)
    (hcoherent :
      feitSibleyCoherent d
        (feitSibleySker d chars (feitSibleySderivedH d))) :
    feitSibleyCoherent d chars := by
  classical
  let : d.S.Normal := d.S_normal
  let P : Subgroup d.H → Prop := fun R =>
    R ≤ feitSibleySderivedH d ∧ R.Normal ∧
      feitSibleyCoherent d (feitSibleySker d chars R)
  have hPtop : P (feitSibleySderivedH d) := by
    refine ⟨le_rfl, ?_, hcoherent⟩
    dsimp [feitSibleySderivedH]
    infer_instance
  rcases Finite.exists_le_minimal (p := P) hPtop with
    ⟨R1, _hR1sel, hR1min⟩
  rcases hR1min.prop with ⟨hR1le, hR1normal, hcoherentR1⟩
  by_cases hR1bot : R1 = ⊥
  · subst R1
    have hSkerBot : feitSibleySker d chars ⊥ = chars := by
      apply Finset.filter_eq_self.mpr
      intro chi hchi a
      have ha : (a : d.H) = 1 := Subgroup.mem_bot.mp a.property
      rw [ha]
      rfl
    rw [hSkerBot] at hcoherentR1
    exact hcoherentR1
  · let : R1.Normal := hR1normal
    obtain ⟨R2, hchief⟩ :=
      exists_chiefFactor_below_appendixIV R1 hR1bot
    let : R2.Normal := hchief.normal_K
    have hR2le : R2 ≤ feitSibleySderivedH d :=
      hchief.lt.le.trans hR1le
    have hnotcoherentR2 :
        ¬ feitSibleyCoherent d (feitSibleySker d chars R2) := by
      intro hcoherentR2
      have hP2 : P R2 :=
        ⟨hR2le, inferInstance, hcoherentR2⟩
      have hR1leR2 :=
        hR1min.le_of_le hP2 hchief.lt.le
      exact hchief.lt.2 hR1leR2
    exact False.elim
      (feitSibley_step2_chief_factor_contradiction_core
        d chars hchars hDodd hD R1 R2 hR1le hchief
          hcoherentR1 hnotcoherentR2)

private theorem feitSibley_step2_chief_descent_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D))
    (hcoherent :
      feitSibleyCoherent d
        (feitSibleySker d chars (feitSibleySderivedH d))) :
    feitSibleyCoherent d chars := by
  by_cases hD : d.D = ⊥
  · exact feitSibley_coherent_of_D_eq_bot_core
      d chars hchars hDodd hD
  · exact feitSibley_step2_chief_descent_of_D_ne_bot_core
      d chars hchars hDodd hD hcoherent

private theorem scalar_of_commutator_left_kernel_appendixIV
    {A C V : Type*} [Group A] [Group C]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ (A × C) V)
    (hrho : Representation.IsIrreducible rho)
    (hker : ∀ x : (commutator A).prod (⊥ : Subgroup C), rho x = 1)
    (a : A) :
    ∃ c : ℂ,
      (rho (MonoidHom.inl A C a) : Module.End ℂ V) =
        c • (1 : Module.End ℂ V) := by
  classical
  let : Representation.IsIrreducible rho := hrho
  have hcommute : ∀ x : A × C,
      rho (MonoidHom.inl A C a) * rho x =
        rho x * rho (MonoidHom.inl A C a) := by
    intro x
    have hmem :
        ⁅x, MonoidHom.inl A C a⁆ ∈
          (commutator A).prod (⊥ : Subgroup C) := by
      change ⁅x.1, a⁆ ∈ commutator A ∧
        ⁅x.2, 1⁆ ∈ (⊥ : Subgroup C)
      constructor
      · exact Subgroup.commutator_mem_commutator (by simp) (by simp)
      · simp
    have hcommImage :
        rho ⁅x, MonoidHom.inl A C a⁆ = (1 : Module.End ℂ V) :=
      hker ⟨⁅x, MonoidHom.inl A C a⁆, hmem⟩
    have hmul :
        rho x * rho (MonoidHom.inl A C a) * rho x⁻¹ *
            rho (MonoidHom.inl A C a)⁻¹ =
          (1 : Module.End ℂ V) := by
      simpa [commutatorElement_def, map_mul] using hcommImage
    have hleftInv : rho x⁻¹ * rho x = 1 := by
      rw [← map_mul]
      simp
    have hrightInv :
        rho (MonoidHom.inl A C a)⁻¹ * rho (MonoidHom.inl A C a) = 1 := by
      rw [← map_inv, ← map_mul]
      have hx :
          MonoidHom.inl A C a⁻¹ * MonoidHom.inl A C a =
            (1 : A × C) := by
        ext <;> simp
      rw [hx, map_one]
    have hconjEq :
        rho x * rho (MonoidHom.inl A C a) * rho x⁻¹ =
          rho (MonoidHom.inl A C a) := by
      calc
        rho x * rho (MonoidHom.inl A C a) * rho x⁻¹ =
            (rho x * rho (MonoidHom.inl A C a) * rho x⁻¹) * 1 := by simp
        _ = (rho x * rho (MonoidHom.inl A C a) * rho x⁻¹) *
              (rho (MonoidHom.inl A C a)⁻¹ *
                rho (MonoidHom.inl A C a)) := by rw [hrightInv]
        _ = (rho x * rho (MonoidHom.inl A C a) * rho x⁻¹ *
              rho (MonoidHom.inl A C a)⁻¹) *
                rho (MonoidHom.inl A C a) := by simp [mul_assoc]
        _ = 1 * rho (MonoidHom.inl A C a) := by rw [hmul]
        _ = rho (MonoidHom.inl A C a) := by simp
    calc
      rho (MonoidHom.inl A C a) * rho x =
          (rho x * rho (MonoidHom.inl A C a) * rho x⁻¹) * rho x := by
            rw [hconjEq]
      _ = rho x * rho (MonoidHom.inl A C a) * (rho x⁻¹ * rho x) := by
        rw [mul_assoc]
      _ = rho x * rho (MonoidHom.inl A C a) := by
        rw [hleftInv, mul_one]
  let f : Representation.IntertwiningMap rho rho :=
    (rho (MonoidHom.inl A C a)).intertwiningMap_of_isIntertwiningMap
      rho rho (by
        intro x v
        exact congrArg (fun F : Module.End ℂ V => F v) (hcommute x))
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rho)).surjective f
  refine ⟨c, ?_⟩
  have hlin :
      ((algebraMap ℂ (Representation.IntertwiningMap rho rho) c :
          Representation.IntertwiningMap rho rho) : Module.End ℂ V) =
        (f : Module.End ℂ V) := by
    calc
      ((algebraMap ℂ (Representation.IntertwiningMap rho rho) c :
          Representation.IntertwiningMap rho rho) : Module.End ℂ V) =
          ((c • (1 : Representation.IntertwiningMap rho rho)) :
            Module.End ℂ V) := by
        exact congrArg (fun F : Representation.IntertwiningMap rho rho =>
          (F : Module.End ℂ V))
          (Representation.IntertwiningMap.algebraMap_apply rho c)
      _ = (f : Module.End ℂ V) := by
        exact congrArg (fun F : Representation.IntertwiningMap rho rho =>
          (F : Module.End ℂ V)) hc
  ext v
  have hEval := congrArg (fun F : Module.End ℂ V => F v) hlin.symm
  calc
    rho (MonoidHom.inl A C a) v = (f : Module.End ℂ V) v := by rfl
    _ = ((algebraMap ℂ (Representation.IntertwiningMap rho rho) c :
        Representation.IntertwiningMap rho rho) : Module.End ℂ V) v := hEval
    _ = c • v := by
      calc
        ((algebraMap ℂ (Representation.IntertwiningMap rho rho) c :
            Representation.IntertwiningMap rho rho) : Module.End ℂ V) v =
            ((c • (1 : Representation.IntertwiningMap rho rho)) :
              Module.End ℂ V) v := by
          exact congrArg (fun F : Representation.IntertwiningMap rho rho =>
            (F : Module.End ℂ V) v)
            (Representation.IntertwiningMap.algebraMap_apply rho c)
        _ = c • v := by simp

private theorem irreducible_restrict_right_of_commutator_left_kernel_appendixIV
    {A C V : Type*} [Group A] [Group C]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ (A × C) V)
    (hrho : Representation.IsIrreducible rho)
    (hker : ∀ x : (commutator A).prod (⊥ : Subgroup C), rho x = 1) :
    Representation.IsIrreducible (rho.comp (MonoidHom.inr A C)) := by
  let rhoC := rho.comp (MonoidHom.inr A C)
  let e : Subrepresentation rhoC ≃o Subrepresentation rho := {
    toFun W := {
      toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro x v hv
        obtain ⟨c, hc⟩ :=
          scalar_of_commutator_left_kernel_appendixIV rho hrho hker x.1
        have hvC : rho (MonoidHom.inr A C x.2) v ∈ W :=
          W.apply_mem_toSubmodule x.2 hv
        have hx : x = MonoidHom.inl A C x.1 * MonoidHom.inr A C x.2 := by
          ext <;> simp
        rw [hx, map_mul, hc]
        exact W.toSubmodule.smul_mem c hvC
    }
    invFun W := {
      toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro c v hv
        exact W.apply_mem_toSubmodule (MonoidHom.inr A C c) hv
    }
    left_inv W := by
      apply Subrepresentation.toSubmodule_injective
      rfl
    right_inv W := by
      apply Subrepresentation.toSubmodule_injective
      rfl
    map_rel_iff' := by
      intro W U
      rfl
  }
  let : Representation.IsIrreducible rho := hrho
  exact OrderIso.isSimpleOrder e

private theorem irreducible_restrict_right_of_left_centralModulo_kernel_appendixIV
    {A C G V : Type*} [Group A] [Group C] [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e : A × C ≃* G) (N : Subgroup A)
    (rho : Representation ℂ G V) [rho.IsIrreducible]
    (hker : ∀ x : N, rho (e (x, 1)) = 1)
    (hcentral : ∀ a : A, ∀ b : A, ⁅a, b⁆ ∈ N) :
    Representation.IsIrreducible
      (rho.comp (e.toMonoidHom.comp (MonoidHom.inr A C))) := by
  let rhoAC : Representation ℂ (A × C) V :=
    rho.comp e.toMonoidHom
  have hrhoAC : Representation.IsIrreducible rhoAC :=
    Section6.representation_isIrreducible_comp_surjective
      rho e.toMonoidHom e.surjective inferInstance
  have hcommAN : commutator A ≤ N := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ha b _hb
    exact hcentral a b
  have hkerAC :
      ∀ x : (commutator A).prod (⊥ : Subgroup C), rhoAC x = 1 := by
    intro x
    have hx2 : x.1.2 = 1 := Subgroup.mem_bot.mp x.property.2
    change rho (e x.1) = 1
    have hx : x.1 = (x.1.1, 1) := by
      ext <;> simp [hx2]
    rw [hx]
    exact hker ⟨x.1.1, hcommAN x.property.1⟩
  exact irreducible_restrict_right_of_commutator_left_kernel_appendixIV
    rhoAC hrhoAC hkerAC

private def feitSibleyStep3BaseDegreeData
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (_ : Finset (ClassFunction d.H)) (_ : Subgroup d.H)
    (X1 : Finset (ClassFunction d.H)) (p : Nat) : Prop :=
  ∃ deg : X1 → Nat,
    (∀ chi : X1,
      0 < deg chi ∧
        degree (chi : ClassFunction d.H) = (deg chi : Complex)) ∧
    (∀ chi : X1, ∃ k : Nat,
      deg chi = Nat.card d.D * p ^ k) ∧
    ∀ chi : X1,
      deg chi ^ 2 ∣
        Finset.sum (Finset.univ.filter (fun psi : X1 => deg psi < deg chi)) (fun psi => deg psi ^ 2)

private theorem sum_filter_subtype_le_sum_subtype_appendixIV
    {α : Type*} [DecidableEq α]
    (X S : Finset α) (hSX : S ⊆ X)
    (f : X → Nat) (P : X → Prop) [DecidablePred P]
    (hP : ∀ x : X, P x → x.1 ∈ S) :
    ∑ x ∈ (Finset.univ.filter P), f x ≤
      ∑ y : S, f ⟨y.1, hSX y.2⟩ := by
  let T := {x : X // P x}
  let emb : T ↪ S :=
    ⟨fun x => ⟨x.1.1, hP x.1 x.2⟩, by
      intro x y hxy
      have hval : x.1.1 = y.1.1 :=
        congrArg (fun z : S => z.1) hxy
      apply Subtype.ext
      exact Subtype.ext hval⟩
  have hleft :
      ∑ x ∈ (Finset.univ.filter P), f x = ∑ x : T, f x.1 := by
    exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f
  rw [hleft]
  calc
    ∑ x : T, f x.1 =
        ∑ y ∈ (Finset.univ.map emb), f ⟨y.1, hSX y.2⟩ := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ y : S, f ⟨y.1, hSX y.2⟩ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by intro y hy; simp at hy ⊢)
        (by intro y _hy _hnot; exact Nat.zero_le _)

private theorem coherent_of_prime_power_degree_prefix_dvd_appendixIV
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (X : Finset (ClassFunction L))
    (tau : ClassFunction L →ₗ[Complex] ClassFunction G)
    (hXne : X.Nonempty)
    (hclosed : ∀ chi : ClassFunction L, chi ∈ X →
      conjugateCharacter chi ∈ X)
    (hnonself : ∀ chi : ClassFunction L, chi ∈ X →
      conjugateCharacter chi ≠ chi)
    (hirr : ∀ chi : X,
      IsIrreducibleCharacterOnGroup (chi : ClassFunction L))
    (hiso : isCFLinearIsometryOnSpanOn X puncturedSet tau)
    (htarget : ∀ phi : ClassFunction L,
      integerSpanOn X puncturedSet phi →
        Theory.Character.IsVirtualCharacter (tau phi) ∧
          supportedOn (tau phi) puncturedSet)
    (p m : Nat) (hp : p.Prime) (hpgt : 2 < p) (hm : 0 < m)
    (deg : X → Nat)
    (hdeg : ∀ chi : X,
      0 < deg chi ∧ degree (chi : ClassFunction L) = (deg chi : Complex))
    (hpower : ∀ chi : X, ∃ k : Nat, deg chi = m * p ^ k)
    (hprefix : ∀ chi : X,
      deg chi ^ 2 ∣
        Finset.sum (Finset.univ.filter (fun psi : X => deg psi < deg chi)) (fun psi => deg psi ^ 2)) :
    IsCoherentTriple puncturedSet X tau := by
  classical
  have huniv : (Finset.univ : Finset X).Nonempty := by
    rcases hXne with ⟨chi, hchi⟩
    exact ⟨⟨chi, hchi⟩, by simp⟩
  rcases Finset.exists_min_image (Finset.univ : Finset X) deg huniv with
    ⟨chi0, _hchi0univ, hchi0min⟩
  let d0 : Nat := deg chi0
  let degOf : ClassFunction L → Nat := fun chi =>
    if hchi : chi ∈ X then deg ⟨chi, hchi⟩ else 0
  have hdegOf : ∀ (chi : ClassFunction L) (hchi : chi ∈ X),
      degOf chi = deg ⟨chi, hchi⟩ := by
    intro chi hchi
    simp [degOf, hchi]
  let S0 : Finset (ClassFunction L) :=
    X.filter fun chi => degOf chi = d0
  have hS0X : S0 ⊆ X := by
    intro chi hchi
    exact (Finset.mem_filter.mp hchi).1
  have hchi0S0 : (chi0 : ClassFunction L) ∈ S0 := by
    change (chi0 : ClassFunction L) ∈
      X.filter (fun chi => degOf chi = d0)
    rw [Finset.mem_filter]
    exact ⟨chi0.2, by simp [degOf, d0, chi0.2]⟩
  have hbarX : conjugateCharacter (chi0 : ClassFunction L) ∈ X :=
    hclosed (chi0 : ClassFunction L) chi0.2
  let chibar : X :=
    ⟨conjugateCharacter (chi0 : ClassFunction L), hbarX⟩
  have hbarDeg : deg chibar = deg chi0 := by
    have hcast : (deg chibar : Complex) = (deg chi0 : Complex) := by
      rw [← (hdeg chibar).2, ← (hdeg chi0).2]
      exact Section5.degree_conjugateCharacter_eq_of_isCharacter
        (Section1.isCharacter_of_isIrreducibleCharacterOnGroup (hirr chi0))
    exact_mod_cast hcast
  have hbarS0 : conjugateCharacter (chi0 : ClassFunction L) ∈ S0 := by
    change conjugateCharacter (chi0 : ClassFunction L) ∈
      X.filter (fun chi => degOf chi = d0)
    rw [Finset.mem_filter]
    refine ⟨hbarX, ?_⟩
    rw [hdegOf _ hbarX, hbarDeg]
  have hS0card : 2 ≤ S0.card := by
    have hone : 1 < S0.card := Finset.one_lt_card.mpr
      ⟨(chi0 : ClassFunction L), hchi0S0,
        conjugateCharacter (chi0 : ClassFunction L), hbarS0,
        (hnonself (chi0 : ClassFunction L) chi0.2).symm⟩
    omega
  have hS0irr : ∀ chi : S0,
      IsIrreducibleCharacterOnGroup (chi : ClassFunction L) := by
    intro chi
    exact hirr ⟨chi, hS0X chi.2⟩
  have hS0iso : isCFLinearIsometryOnSpanOn S0 puncturedSet tau := by
    intro phi theta hphi htheta
    exact hiso phi theta
      (integerSpanOn_mono hS0X hphi)
      (integerSpanOn_mono hS0X htheta)
  have hS0target : ∀ phi : ClassFunction L,
      integerSpanOn S0 puncturedSet phi →
        Theory.Character.IsVirtualCharacter (tau phi) ∧
          supportedOn (tau phi) puncturedSet := by
    intro phi hphi
    exact htarget phi (integerSpanOn_mono hS0X hphi)
  have hS0degree : ∀ chi psi : S0,
      degree (chi : ClassFunction L) = degree (psi : ClassFunction L) := by
    intro chi psi
    have hchiDeg : deg ⟨chi, hS0X chi.2⟩ = d0 := by
      rw [← hdegOf chi (hS0X chi.2)]
      exact (Finset.mem_filter.mp chi.2).2
    have hpsiDeg : deg ⟨psi, hS0X psi.2⟩ = d0 := by
      rw [← hdegOf psi (hS0X psi.2)]
      exact (Finset.mem_filter.mp psi.2).2
    rw [(hdeg ⟨chi, hS0X chi.2⟩).2,
      (hdeg ⟨psi, hS0X psi.2⟩).2, hchiDeg, hpsiDeg]
  have hS0coherent : IsCoherentTriple puncturedSet S0 tau :=
    lemma_1_b L S0 tau hS0card hS0irr hS0iso hS0target hS0degree
  let Q : Nat → Prop := fun n =>
    ∀ S : Finset (ClassFunction L),
      (X \ S).card = n →
      S0 ⊆ S →
      S ⊆ X →
      IsCoherentTriple puncturedSet S tau →
      IsCoherentTriple puncturedSet X tau
  have hQ : ∀ n, Q n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hcard hS0S hSX hScoherent
        by_cases hSXeq : S = X
        · simpa [hSXeq] using hScoherent
        · have hdiffne : (X \ S).Nonempty := by
            rw [Finset.sdiff_nonempty]
            intro hXS
            exact hSXeq (Finset.Subset.antisymm hSX hXS)
          rcases Finset.exists_min_image (X \ S) degOf hdiffne with
            ⟨psi, hpsiDiff, hpsimin⟩
          have hpsiX : psi ∈ X := (Finset.mem_sdiff.mp hpsiDiff).1
          have hpsiS : psi ∉ S := (Finset.mem_sdiff.mp hpsiDiff).2
          let psiX : X := ⟨psi, hpsiX⟩
          have hdegPsi : degOf psi = deg psiX := hdegOf psi hpsiX
          have hd0le : d0 ≤ deg psiX := by
            simpa [d0] using hchi0min psiX (by simp)
          have hd0ne : d0 ≠ deg psiX := by
            intro heq
            apply hpsiS
            apply hS0S
            change psi ∈ X.filter (fun chi => degOf chi = d0)
            rw [Finset.mem_filter]
            exact ⟨hpsiX, by rw [hdegPsi, ← heq]⟩
          have hd0lt : d0 < deg psiX := lt_of_le_of_ne hd0le hd0ne
          have hlowerS : ∀ x : X, deg x < deg psiX → x.1 ∈ S := by
            intro x hx
            by_contra hxS
            have hxDiff : x.1 ∈ X \ S :=
              Finset.mem_sdiff.mpr ⟨x.2, hxS⟩
            have hmin := hpsimin x.1 hxDiff
            have hmin' : deg psiX ≤ deg x := by
              simpa [psiX, hdegOf psi hpsiX, hdegOf x.1 x.2] using hmin
            exact (not_lt_of_ge hmin' hx).elim
          rcases hpower chi0 with ⟨k0, hk0⟩
          rcases hpower psiX with ⟨k, hk⟩
          have hpowlt : p ^ k0 < p ^ k := by
            apply (Nat.mul_lt_mul_left hm).mp
            simpa [d0, hk0, hk] using hd0lt
          have hklt : k0 < k :=
            (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpowlt
          have hdegDvd : d0 ∣ deg psiX := by
            change deg chi0 ∣ deg psiX
            rw [hk0, hk]
            exact Nat.mul_dvd_mul_left m
              (Nat.pow_dvd_pow p (Nat.le_of_lt hklt))
          have hdiv : ∃ q : Nat,
              degree psi = (q : Complex) *
                degree (chi0 : ClassFunction L) := by
            obtain ⟨q, hq⟩ := hdegDvd
            refine ⟨q, ?_⟩
            rw [(hdeg psiX).2, (hdeg chi0).2]
            norm_cast
            simpa [mul_comm] using hq
          have hpd0 : p * d0 ≤ deg psiX := by
            have hsucc : k0 + 1 ≤ k := Nat.succ_le_iff.mpr hklt
            have hpowle : p ^ (k0 + 1) ≤ p ^ k :=
              Nat.pow_le_pow_right hp.one_lt.le hsucc
            change p * deg chi0 ≤ deg psiX
            rw [hk0, hk]
            calc
              p * (m * p ^ k0) = m * p ^ (k0 + 1) := by
                rw [pow_succ]
                ac_rfl
              _ ≤ m * p ^ k := Nat.mul_le_mul_left m hpowle
          have hgap :
              2 * (deg psiX : Real) * (d0 : Real) <
                (deg psiX : Real) ^ 2 := by
            have hpR : (2 : Real) < p := by exact_mod_cast hpgt
            have hd0R : (0 : Real) < d0 := by
              exact_mod_cast (hdeg chi0).1
            have hpsiR : (0 : Real) < deg psiX := by
              exact_mod_cast (hdeg psiX).1
            have hpd0R : (p : Real) * d0 ≤ deg psiX := by
              exact_mod_cast hpd0
            have htwod0 : (2 : Real) * d0 < deg psiX := by
              nlinarith
            have hmul := mul_lt_mul_of_pos_left htwod0 hpsiR
            nlinarith
          let lower : Finset X :=
            Finset.univ.filter fun x : X => deg x < deg psiX
          have hchi0lower : chi0 ∈ lower := by
            simp [lower, d0, hd0lt]
          have hlowerPos : 0 < ∑ x ∈ lower, deg x ^ 2 := by
            have hterm : 0 < deg chi0 ^ 2 := pow_pos (hdeg chi0).1 _
            have hle : deg chi0 ^ 2 ≤ ∑ x ∈ lower, deg x ^ 2 := by
              exact Finset.single_le_sum
                (fun x _hx => Nat.zero_le (deg x ^ 2)) hchi0lower
            omega
          have hsqPrefix : deg psiX ^ 2 ≤ ∑ x ∈ lower, deg x ^ 2 := by
            exact Nat.le_of_dvd hlowerPos (by
              simpa [lower] using hprefix psiX)
          have hlowerLe :
              ∑ x ∈ lower, deg x ^ 2 ≤
                ∑ y : S, deg ⟨y.1, hSX y.2⟩ ^ 2 := by
            simpa [lower] using
              (sum_filter_subtype_le_sum_subtype_appendixIV X S hSX
                (fun x : X => deg x ^ 2)
                (fun x : X => deg x < deg psiX) hlowerS)
          have hsqS :
              deg psiX ^ 2 ≤
                ∑ y : S, deg ⟨y.1, hSX y.2⟩ ^ 2 :=
            hsqPrefix.trans hlowerLe
          have hsqSReal :
              (deg psiX : Real) ^ 2 ≤
                ∑ y : S, (deg ⟨y.1, hSX y.2⟩ : Real) ^ 2 := by
            exact_mod_cast hsqS
          have hgrowth :
              2 * (degree psi).re *
                  (degree (chi0 : ClassFunction L)).re <
                ∑ chi : S, (degree (chi : ClassFunction L)).re ^ 2 := by
            have hpsiRe : (degree psi).re = (deg psiX : Real) := by
              rw [(hdeg psiX).2]
              simp
            have hchi0Re :
                (degree (chi0 : ClassFunction L)).re = (d0 : Real) := by
              rw [(hdeg chi0).2]
              simp [d0]
            have hsumEq :
                (∑ chi : S,
                    (degree (chi : ClassFunction L)).re ^ 2) =
                  ∑ chi : S,
                    (deg ⟨chi.1, hSX chi.2⟩ : Real) ^ 2 := by
              apply Finset.sum_congr rfl
              intro chi _hchi
              rw [(hdeg ⟨chi.1, hSX chi.2⟩).2]
              simp
            rw [hpsiRe, hchi0Re, hsumEq]
            exact hgap.trans_le hsqSReal
          have hnewX : S.cons psi hpsiS ⊆ X := by
            intro chi hchi
            rw [Finset.mem_cons] at hchi
            rcases hchi with rfl | hchi
            · exact hpsiX
            · exact hSX hchi
          have hnewCoherent :
              IsCoherentTriple puncturedSet (S.cons psi hpsiS) tau := by
            apply lemma_1_a L S psi (chi0 : ClassFunction L)
                (hS0S hchi0S0) hpsiS tau
            · intro chi
              exact hirr ⟨chi, hSX chi.2⟩
            · exact hirr psiX
            · intro phi theta hphi htheta
              exact hiso phi theta
                (integerSpanOn_mono hnewX hphi)
                (integerSpanOn_mono hnewX htheta)
            · intro phi hphi
              exact htarget phi (integerSpanOn_mono hnewX hphi)
            · exact hScoherent
            · exact hdiv
            · exact hgrowth
          let Snew : Finset (ClassFunction L) := S.cons psi hpsiS
          have hSnewEq : Snew = insert psi S := by
            simp [Snew]
          have hdiffStrict : X \ Snew ⊂ X \ S := by
            refine (Finset.ssubset_iff_of_subset ?_).2 ?_
            · intro chi hchi
              rw [Finset.mem_sdiff] at hchi ⊢
              exact ⟨hchi.1, fun hchiS => hchi.2 (by
                rw [hSnewEq]
                exact Finset.mem_insert_of_mem hchiS)⟩
            · refine ⟨psi, hpsiDiff, ?_⟩
              rw [Finset.mem_sdiff]
              intro hbad
              exact hbad.2 (by
                rw [hSnewEq]
                exact Finset.mem_insert_self _ _)
          have hmeasure : (X \ Snew).card < (X \ S).card :=
            Finset.card_lt_card hdiffStrict
          exact ih (X \ Snew).card (by simpa [hcard] using hmeasure)
            Snew rfl
            (fun chi hchi => by
              rw [hSnewEq]
              exact Finset.mem_insert_of_mem (hS0S hchi))
            hnewX (by simpa [Snew] using hnewCoherent)
  exact hQ (X \ S0).card S0 rfl (fun _ hchi => hchi) hS0X hS0coherent

private theorem feitSibley_step3_degree_shape_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (R : Subgroup d.H) (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d)
    (chi : ClassFunction d.H)
    (hchiChars : chi ∈ chars)
    (hchiKernel : subgroupInKernel' chi (feitSibleySderivedH d)) :
    ∃ k n : Nat,
      0 < n ∧ degree chi = (n : Complex) ∧
        n = Nat.card d.D * p ^ k ∧
          p ^ (2 * k) ∣ R.relIndex d.Q1 := by
  classical
  let : d.Q.Normal := d.Q_normal
  let : d.S.Normal := d.S_normal
  rcases (lemma_2_a d chars hchars chi).mp hchiChars with
    ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
  rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
  have hnpos : 0 < n := by
    rcases Section6.theorem_6_6_positive_degree_nat_of_irreducible
        (show IsIrreducibleCharacterOnGroup phi from
          ⟨n, rho, hrhoIrr, hphiEq⟩) with
      ⟨n0, hn0, hdeg0⟩
    have hcast : (n : Complex) = (n0 : Complex) := by
      rw [hphiEq, degree_representation_character] at hdeg0
      simpa using hdeg0
    have hn : n = n0 := by exact_mod_cast hcast
    simpa [hn] using hn0
  have hSderivedLeQ : feitSibleySderivedH d ≤ d.Q := by
    exact (show feitSibleySderivedH d ≤ d.S from by
      simpa [feitSibleySderivedH] using
        Subgroup.map_subtype_le (derivedSubgroup d.S)).trans d.S_le_Q
  have : (feitSibleySderivedH d).Normal := by
    dsimp [feitSibleySderivedH]
    infer_instance
  have hindKernelPhi :
      subgroupInKernel' (inducedCF d.Q phi) (feitSibleySderivedH d) := by
    rw [hind]
    exact hchiKernel
  have hindKernelRho :
      subgroupInKernel' (inducedCF d.Q rho.character)
        (feitSibleySderivedH d) := by
    simpa [hphiEq] using hindKernelPhi
  have hrhoKernelCF :
      subgroupInKernel' rho.character
        ((feitSibleySderivedH d).subgroupOf d.Q) :=
    (Section1.proposition_1_6_a d.Q (feitSibleySderivedH d)
      hSderivedLeQ rho).mpr hindKernelRho
  have hrhoKernel :
      subgroupInRepresentationKernel rho
        ((feitSibleySderivedH d).subgroupOf d.Q) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho _).mp hrhoKernelCF
  let e : d.S × d.Q1 ≃* d.Q :=
    Section3.internalDirectProductMulEquiv d.internalDirectProduct_Q
  have hkerLeft :
      ∀ x : derivedSubgroup d.S, rho (e (x, 1)) = 1 := by
    intro x
    exact hrhoKernel ⟨e (x, 1), by
      change ((e (x, 1) : d.Q) : d.H) ∈ feitSibleySderivedH d
      have hinl : ((e (x, 1) : d.Q) : d.H) = (x : d.H) := by
        simpa [e] using congrArg Subtype.val
          (Section3.internalDirectProductMulEquiv_apply_inl
            d.internalDirectProduct_Q x)
      rw [hinl]
      exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  let : Representation.IsIrreducible rho := hrhoIrr
  have hirrQ1 :
      Representation.IsIrreducible
        (rho.comp (e.toMonoidHom.comp (MonoidHom.inr d.S d.Q1))) :=
    irreducible_restrict_right_of_left_centralModulo_kernel_appendixIV
      e (derivedSubgroup d.S) rho hkerLeft (by
        intro a b
        exact Subgroup.commutator_mem_commutator (by simp) (by simp))
  let rhoQ1 : Representation Complex d.Q1 (Fin n → Complex) :=
    rho.comp (e.toMonoidHom.comp (MonoidHom.inr d.S d.Q1))
  let : Representation.IsIrreducible rhoQ1 := hirrQ1
  have hnDvd : n ∣ Fintype.card d.Q1 := by
    simpa [rhoQ1] using
      Theory.Character.irreducible_dimension_dvd_group_order rhoQ1
  let : Fact p.Prime := ⟨hpprime⟩
  rcases hpQ1.exists_card_eq with ⟨mQ1, hQ1card⟩
  have hQ1cardF : Fintype.card d.Q1 = p ^ mQ1 := by
    simpa [Nat.card_eq_fintype_card] using hQ1card
  have hnDvdPow : n ∣ p ^ mQ1 := by
    simpa [hQ1cardF] using hnDvd
  rcases (Nat.dvd_prime_pow hpprime).1 hnDvdPow with
    ⟨k, _hk, hn⟩
  have hRleQ1 : R ≤ d.Q1 :=
    hRle.trans (by
      simpa [feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  let RQ1 : Subgroup d.Q1 := R.subgroupOf d.Q1
  let : RQ1.Normal := hRnormal.subgroupOf d.Q1
  have hcentral :
      Theory.Character.IsCentralModulo (⊥ : Subgroup d.Q1) RQ1 := by
    intro z hz q
    change ⁅z, q⁆ = 1
    have hzCenter : (z : d.Q1) ∈ Subgroup.center d.Q1 := by
      have hzAmbient : ((z : d.Q1) : d.H) ∈ feitSibleyCenterQ1H d :=
        hRle hz
      simpa [RQ1, feitSibleyCenterQ1H,
        subgroupOf_map_subtype_eq] using hzAmbient
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp hzCenter q).symm
  have hbotker : ∀ b : (⊥ : Subgroup d.Q1),
      rhoQ1 b = (1 : Module.End Complex (Fin n → Complex)) := by
    intro b
    have hb : (b : d.Q1) = 1 := Subgroup.mem_bot.mp b.property
    simp [hb]
  have hnSqLe : n ^ 2 ≤ R.relIndex d.Q1 := by
    have hbound :=
      Theory.Character.irreducible_finrank_sq_le_index_of_centralModulo_kernel
        rhoQ1 (⊥ : Subgroup d.Q1) RQ1 hbotker hcentral
    simpa [rhoQ1, RQ1, Subgroup.relIndex] using hbound
  have hquotP : IsPGroup p (d.Q1 ⧸ RQ1) := hpQ1.to_quotient RQ1
  rcases hquotP.exists_card_eq with ⟨mR, hRcard⟩
  have hRindex : R.relIndex d.Q1 = p ^ mR := by
    rw [← hRcard, ← Subgroup.index_eq_card RQ1]
    rfl
  have hpowLe : p ^ (2 * k) ≤ p ^ mR := by
    rw [← hRindex]
    calc
      p ^ (2 * k) = (p ^ k) ^ 2 := by
        rw [← pow_mul]
        rw [Nat.mul_comm]
      _ = n ^ 2 := by rw [← hn]
      _ ≤ R.relIndex d.Q1 := hnSqLe
  have hkLe : 2 * k ≤ mR :=
    (Nat.pow_le_pow_iff_right hpprime.one_lt).mp hpowLe
  have hpowDvd : p ^ (2 * k) ∣ R.relIndex d.Q1 := by
    rw [hRindex]
    exact Nat.pow_dvd_pow p hkLe
  refine ⟨k, Nat.card d.D * n,
    Nat.mul_pos (Nat.card_pos (α := d.D)) hnpos, ?_, ?_, hpowDvd⟩
  · have hindex : d.Q.index = Nat.card d.D := by
      simpa [Subgroup.relIndex_top_right] using
        feitSibley_Q_relIndex_top_eq_card_D_appendixIV d
    rw [← hind, degree_inducedClassFunction d.Q phi, hphiEq,
      degree_representation_character]
    simp [hindex, Nat.cast_mul]
  · rw [hn]

set_option maxHeartbeats 1600000 in
private theorem feitSibley_step3_prefix_sq_dvd_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (R : Subgroup d.H) (_ : R ≠ ⊥)
    (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d)
    (X1 : Finset (ClassFunction d.H))
    (hX1mem : ∀ chi : ClassFunction d.H, chi ∈ X1 ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d))
    (deg : X1 → Nat)
    (hdeg : ∀ chi,
      0 < deg chi ∧
        degree (chi : ClassFunction d.H) = (deg chi : Complex))
    (hpower : ∀ chi, ∃ k : Nat,
      deg chi = Nat.card d.D * p ^ k) :
    ∀ chi,
      deg chi ^ 2 ∣
        Finset.sum
          (Finset.univ.filter (fun psi => deg psi < deg chi))
          (fun psi => deg psi ^ 2) := by
  classical
  let : Fact p.Prime := ⟨hpprime⟩
  let : R.Normal := hRnormal
  let : d.S.Normal := d.S_normal
  have hRleQ1 : R ≤ d.Q1 :=
    hRle.trans (by
      simpa [feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  have hSderivedLeS : feitSibleySderivedH d ≤ d.S := by
    simpa [feitSibleySderivedH] using
      Subgroup.map_subtype_le (derivedSubgroup d.S)
  have : (feitSibleySderivedH d).Normal := by
    dsimp [feitSibleySderivedH]
    infer_instance
  have hXchar : ∀ chi : ClassFunction d.H, chi ∈ X1 ↔
      IsIrreducibleCharacterOnGroup chi ∧
        subgroupInKernel' chi (feitSibleySderivedH d) ∧
          ¬ subgroupInKernel' chi R := by
    intro chi
    rw [hX1mem]
    constructor
    · rintro ⟨⟨hchiChars, hnotR⟩, _hchiChars', hkerS⟩
      exact ⟨(hchars chi).mp hchiChars |>.1, hkerS, hnotR⟩
    · rintro ⟨hirr, hkerS, hnotR⟩
      have hnotQ1 : ¬ subgroupInKernel' chi d.Q1 := by
        intro hkerQ1
        exact hnotR (subgroupInKernel'_mono_appendixIV hRleQ1 hkerQ1)
      have hchiChars : chi ∈ chars := (hchars chi).mpr ⟨hirr, hnotQ1⟩
      exact ⟨⟨hchiChars, hnotR⟩, hchiChars, hkerS⟩
  have hsumReal :=
    exceptional_kernel_degree_sq_sum_appendixIV
      (feitSibleySderivedH d) R X1 hXchar
  have hsumReal' :
      (∑ chi : X1, (deg chi : Real) ^ 2) +
          (Nat.card (d.H ⧸ (feitSibleySderivedH d ⊔ R)) : Real) =
        (Nat.card (d.H ⧸ feitSibleySderivedH d) : Real) := by
    calc
      (∑ chi : X1, (deg chi : Real) ^ 2) +
          (Nat.card (d.H ⧸ (feitSibleySderivedH d ⊔ R)) : Real) =
          (∑ chi : X1,
            (degree (chi : ClassFunction d.H)).re ^ 2) +
              (Nat.card (d.H ⧸ (feitSibleySderivedH d ⊔ R)) : Real) := by
        congr 1
        apply Finset.sum_congr rfl
        intro chi _hchi
        rw [(hdeg chi).2]
        simp
      _ = _ := hsumReal
  have hsumNat :
      (∑ chi : X1, deg chi ^ 2) +
          Nat.card (d.H ⧸ (feitSibleySderivedH d ⊔ R)) =
        Nat.card (d.H ⧸ feitSibleySderivedH d) := by
    exact_mod_cast hsumReal'
  have hInf :
      (feitSibleySderivedH d ⊔ R) ⊓ d.Q1 = R := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxSup, hxQ1⟩
      rcases Subgroup.mem_sup_of_normal_right.mp hxSup with
        ⟨s, hs, r, hr, hsr⟩
      have hsQ1 : s ∈ d.Q1 := by
        have hseq : s = x * r⁻¹ := by
          rw [← hsr]
          simp
        rw [hseq]
        exact d.Q1.mul_mem hxQ1 (d.Q1.inv_mem (hRleQ1 hr))
      have hsOne : s = 1 := by
        apply Subgroup.mem_bot.mp
        exact d.S_disjoint_Q1.le_bot ⟨hSderivedLeS hs, hsQ1⟩
      rw [hsOne, one_mul] at hsr
      exact hsr ▸ hr
    · intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨(show R ≤ feitSibleySderivedH d ⊔ R from le_sup_right) hx,
          hRleQ1 hx⟩
  have hrel :
      (feitSibleySderivedH d ⊔ R).relIndex
          (feitSibleySderivedH d ⊔ d.Q1) =
        R.relIndex d.Q1 := by
    calc
      (feitSibleySderivedH d ⊔ R).relIndex
          (feitSibleySderivedH d ⊔ d.Q1) =
          (feitSibleySderivedH d ⊔ R).relIndex
            ((feitSibleySderivedH d ⊔ R) ⊔ d.Q1) := by
              rw [sup_assoc, sup_eq_right.2 hRleQ1]
      _ = (feitSibleySderivedH d ⊔ R).relIndex d.Q1 :=
        Subgroup.relIndex_sup_left d.Q1 (feitSibleySderivedH d ⊔ R)
      _ = ((feitSibleySderivedH d ⊔ R) ⊓ d.Q1).relIndex d.Q1 :=
        (Subgroup.inf_relIndex_right
          (feitSibleySderivedH d ⊔ R) d.Q1).symm
      _ = R.relIndex d.Q1 := by rw [hInf]
  have hrelDvdSupIndex :
      R.relIndex d.Q1 ∣ (feitSibleySderivedH d ⊔ R).index := by
    have hdvd := Subgroup.relIndex_dvd_index_of_le
      (show feitSibleySderivedH d ⊔ R ≤
          feitSibleySderivedH d ⊔ d.Q1 from
        sup_le_sup le_rfl hRleQ1)
    rwa [hrel] at hdvd
  have hsupIndexDvdBase :
      (feitSibleySderivedH d ⊔ R).index ∣
        (feitSibleySderivedH d).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hcop : Nat.Coprime (Nat.card d.D) p := by
    have hQ1ne : d.Q1 ≠ ⊥ := by
      intro hQ1
      apply d.Q1_not_two_group
      exact hQ1.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
    have hpQ1card : p ∣ Nat.card d.Q1 := by
      rcases hpQ1.card_eq_or_dvd with hcard | hdvd
      · have hbot : d.Q1 = ⊥ := by
          rw [← Subgroup.card_le_one_iff_eq_bot, hcard]
        exact (hQ1ne hbot).elim
      · exact hdvd
    have hpQcard : p ∣ Nat.card d.Q :=
      hpQ1card.trans (Subgroup.card_dvd_of_le d.Q1_le_Q)
    exact Nat.Coprime.of_dvd_right hpQcard d.card_Q_coprime_card_D.symm
  intro chi
  have hchiFacts := (hXchar (chi : ClassFunction d.H)).mp chi.2
  have hchiNotQ1 :
      ¬ subgroupInKernel' (chi : ClassFunction d.H) d.Q1 := by
    intro hkerQ1
    exact hchiFacts.2.2
      (subgroupInKernel'_mono_appendixIV hRleQ1 hkerQ1)
  have hchiChars : (chi : ClassFunction d.H) ∈ chars :=
    (hchars (chi : ClassFunction d.H)).mpr ⟨hchiFacts.1, hchiNotQ1⟩
  rcases feitSibley_step3_degree_shape_core
      d chars hchars p hpprime hpQ1 R hRnormal hRle
      (chi : ClassFunction d.H) hchiChars hchiFacts.2.1 with
    ⟨k, nchi, _hnpos, hchiDegree, hnchi, hpRel⟩
  have hdegChi : deg chi = Nat.card d.D * p ^ k := by
    have hcast : (deg chi : Complex) = (nchi : Complex) := by
      rw [← (hdeg chi).2, hchiDegree]
    have hnat : deg chi = nchi := by exact_mod_cast hcast
    exact hnat.trans hnchi
  have hpSupIndex :
      p ^ (2 * k) ∣ (feitSibleySderivedH d ⊔ R).index :=
    hpRel.trans hrelDvdSupIndex
  have hpBaseIndex :
      p ^ (2 * k) ∣ (feitSibleySderivedH d).index :=
    hpSupIndex.trans hsupIndexDvdBase
  have hpSupCard :
      p ^ (2 * k) ∣
        Nat.card (d.H ⧸ (feitSibleySderivedH d ⊔ R)) := by
    simpa [Subgroup.index_eq_card] using hpSupIndex
  have hpBaseCard :
      p ^ (2 * k) ∣
        Nat.card (d.H ⧸ feitSibleySderivedH d) := by
    simpa [Subgroup.index_eq_card] using hpBaseIndex
  have hpTotal : p ^ (2 * k) ∣ ∑ psi : X1, deg psi ^ 2 := by
    apply (Nat.dvd_add_iff_left hpSupCard).2
    rw [hsumNat]
    exact hpBaseCard
  let lower : Finset X1 :=
    Finset.univ.filter fun psi : X1 => deg psi < deg chi
  let tail : Finset X1 :=
    Finset.univ.filter fun psi : X1 => ¬ deg psi < deg chi
  have hpTail : p ^ (2 * k) ∣ ∑ psi ∈ tail, deg psi ^ 2 := by
    apply Finset.dvd_sum
    intro psi hpsiTail
    have hge : deg chi ≤ deg psi := by
      have := (Finset.mem_filter.mp hpsiTail).2
      omega
    rcases hpower psi with ⟨b, hpsiDegree⟩
    have hpowLe : p ^ k ≤ p ^ b := by
      apply Nat.le_of_mul_le_mul_left
        (by simpa [hdegChi, hpsiDegree] using hge)
      simpa [Nat.card_eq_fintype_card] using
        (Nat.card_pos (α := d.D))
    have hkle : k ≤ b :=
      (Nat.pow_le_pow_iff_right hpprime.one_lt).mp hpowLe
    have hpDvd : p ^ (2 * k) ∣ p ^ (2 * b) :=
      Nat.pow_dvd_pow p (Nat.mul_le_mul_left 2 hkle)
    rw [hpsiDegree]
    convert dvd_mul_of_dvd_right hpDvd (Nat.card d.D ^ 2) using 1
    ring
  have hpartition :
      (∑ psi ∈ lower, deg psi ^ 2) +
          (∑ psi ∈ tail, deg psi ^ 2) =
        ∑ psi : X1, deg psi ^ 2 := by
    simpa [lower, tail] using
      Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun psi : X1 => deg psi < deg chi) (fun psi => deg psi ^ 2)
  have hpLower : p ^ (2 * k) ∣ ∑ psi ∈ lower, deg psi ^ 2 := by
    apply (Nat.dvd_add_iff_left hpTail).2
    rw [hpartition]
    exact hpTotal
  have hdLower : (Nat.card d.D) ^ 2 ∣
      ∑ psi ∈ lower, deg psi ^ 2 := by
    apply Finset.dvd_sum
    intro psi _hpsi
    rcases hpower psi with ⟨b, hpsiDegree⟩
    rw [hpsiDegree]
    use (p ^ b) ^ 2
    ring
  have hcopPow : Nat.Coprime ((Nat.card d.D) ^ 2) (p ^ (2 * k)) :=
    (hcop.pow_left 2).pow_right (2 * k)
  have hmul : (Nat.card d.D) ^ 2 * p ^ (2 * k) ∣
      ∑ psi ∈ lower, deg psi ^ 2 :=
    hcopPow.mul_dvd_of_dvd_of_dvd hdLower hpLower
  simpa [lower, hdegChi] using (show
    (Nat.card d.D * p ^ k) ^ 2 ∣
      ∑ psi ∈ lower, deg psi ^ 2 by
        (convert hmul using 1; ring))

set_option maxHeartbeats 1600000 in
private theorem feitSibley_step3_base_degree_data_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (R : Subgroup d.H) (hRne : R ≠ ⊥)
    (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d)
    {X1 : Finset (ClassFunction d.H)}
    (hX1mem : ∀ chi : ClassFunction d.H, chi ∈ X1 ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d)) :
    feitSibleyStep3BaseDegreeData d chars R X1 p := by
  classical
  let degOf : ClassFunction d.H → Nat := fun chi =>
    if hchi : chi ∈ chars then
      Classical.choose
        (Section6.theorem_6_6_positive_degree_nat_of_irreducible
          ((hchars chi).mp hchi).1)
    else 0
  have hdegOf (chi : ClassFunction d.H) (hchi : chi ∈ chars) :
      0 < degOf chi ∧ degree chi = (degOf chi : Complex) := by
    simpa only [degOf, dif_pos hchi] using
      (Classical.choose_spec
        (Section6.theorem_6_6_positive_degree_nat_of_irreducible
          ((hchars chi).mp hchi).1))
  have hpowerOf (chi : ClassFunction d.H) (hchi : chi ∈ chars)
      (hchiKernel : subgroupInKernel' chi (feitSibleySderivedH d)) :
      ∃ k : Nat, degOf chi = Nat.card d.D * p ^ k := by
    rcases feitSibley_step3_degree_shape_core
        d chars hchars p hpprime hpQ1 R hRnormal hRle chi hchi hchiKernel with
      ⟨k, n, _hnpos, hdegree, hn, _hrel⟩
    have hcast : (degOf chi : Complex) = (n : Complex) := by
      rw [← (hdegOf chi hchi).2, hdegree]
    have hnat : degOf chi = n := by exact_mod_cast hcast
    exact ⟨k, hnat.trans hn⟩
  unfold feitSibleyStep3BaseDegreeData
  refine ⟨fun chi => degOf (chi : ClassFunction d.H), ?_, ?_, ?_⟩
  · intro chi
    have hchiData :
        ((chi : ClassFunction d.H) ∈ chars ∧
            ¬ subgroupInKernel' (chi : ClassFunction d.H) R) ∧
          (chi : ClassFunction d.H) ∈ chars ∧
            subgroupInKernel' (chi : ClassFunction d.H)
              (feitSibleySderivedH d) := by
      exact (hX1mem (chi : ClassFunction d.H)).mp chi.2
    exact hdegOf (chi : ClassFunction d.H) hchiData.1.1
  · intro chi
    have hchiData :
        ((chi : ClassFunction d.H) ∈ chars ∧
            ¬ subgroupInKernel' (chi : ClassFunction d.H) R) ∧
          (chi : ClassFunction d.H) ∈ chars ∧
            subgroupInKernel' (chi : ClassFunction d.H)
              (feitSibleySderivedH d) := by
      exact (hX1mem (chi : ClassFunction d.H)).mp chi.2
    exact hpowerOf (chi : ClassFunction d.H) hchiData.1.1 hchiData.2.2
  · apply feitSibley_step3_prefix_sq_dvd_core
      d chars hchars p hpprime hpQ1 R hRne hRnormal hRle
    · exact hX1mem
    · intro chi
      have hchiData :
          ((chi : ClassFunction d.H) ∈ chars ∧
              ¬ subgroupInKernel' (chi : ClassFunction d.H) R) ∧
            (chi : ClassFunction d.H) ∈ chars ∧
              subgroupInKernel' (chi : ClassFunction d.H)
                (feitSibleySderivedH d) := by
        exact (hX1mem (chi : ClassFunction d.H)).mp chi.2
      exact hdegOf (chi : ClassFunction d.H) hchiData.1.1
    · intro chi
      have hchiData :
          ((chi : ClassFunction d.H) ∈ chars ∧
              ¬ subgroupInKernel' (chi : ClassFunction d.H) R) ∧
            (chi : ClassFunction d.H) ∈ chars ∧
              subgroupInKernel' (chi : ClassFunction d.H)
                (feitSibleySderivedH d) := by
        exact (hX1mem (chi : ClassFunction d.H)).mp chi.2
      exact hpowerOf (chi : ClassFunction d.H) hchiData.1.1 hchiData.2.2

set_option maxHeartbeats 1600000 in
private theorem feitSibley_step3_base_family_coherence_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D))
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (_ : ¬ ∀ x y : d.Q1, x * y = y * x)
    (R : Subgroup d.H) (hRne : R ≠ ⊥)
    (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d)
    {X1 : Finset (ClassFunction d.H)}
    (hX1mem : ∀ chi : ClassFunction d.H, chi ∈ X1 ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d)) :
    feitSibleyCoherent d X1 := by
  classical
  let : R.Normal := hRnormal
  let : d.S.Normal := d.S_normal
  have : (feitSibleySderivedH d).Normal := by
    dsimp [feitSibleySderivedH]
    infer_instance
  have hRleQ1 : R ≤ d.Q1 :=
    hRle.trans (by
      simpa [feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  have hSderivedLeS : feitSibleySderivedH d ≤ d.S := by
    simpa [feitSibleySderivedH] using
      Subgroup.map_subtype_le (derivedSubgroup d.S)
  have hXchar : ∀ chi : ClassFunction d.H, chi ∈ X1 ↔
      IsIrreducibleCharacterOnGroup chi ∧
        subgroupInKernel' chi (feitSibleySderivedH d) ∧
          ¬ subgroupInKernel' chi R := by
    intro chi
    rw [hX1mem]
    constructor
    · rintro ⟨⟨hchiChars, hnotR⟩, _hchiChars', hkerS⟩
      exact ⟨((hchars chi).mp hchiChars).1, hkerS, hnotR⟩
    · rintro ⟨hirr, hkerS, hnotR⟩
      have hnotQ1 : ¬ subgroupInKernel' chi d.Q1 := by
        intro hkerQ1
        exact hnotR (subgroupInKernel'_mono_appendixIV hRleQ1 hkerQ1)
      have hchiChars : chi ∈ chars := (hchars chi).mpr ⟨hirr, hnotQ1⟩
      exact ⟨⟨hchiChars, hnotR⟩, hchiChars, hkerS⟩
  have hXne : X1.Nonempty := by
    have hRnotle : ¬ R ≤ feitSibleySderivedH d := by
      intro hle
      apply hRne
      apply le_antisymm
      · intro r hr
        exact d.S_disjoint_Q1.le_bot ⟨hSderivedLeS (hle hr), hRleQ1 hr⟩
      · exact bot_le
    have hstrict : feitSibleySderivedH d < feitSibleySderivedH d ⊔ R :=
      lt_of_le_of_ne le_sup_left (fun heq =>
        hRnotle (by rw [heq]; exact le_sup_right))
    have hcardlt :
        Nat.card (d.H ⧸ (feitSibleySderivedH d ⊔ R)) <
          Nat.card (d.H ⧸ feitSibleySderivedH d) := by
      rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
      exact Subgroup.index_strictAnti hstrict
    have hsum := exceptional_kernel_degree_sq_sum_appendixIV
      (feitSibleySderivedH d) R X1 hXchar
    by_contra hne
    have hXempty : X1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hXempty] at hsum
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hsum
    have hcardEq :
        Nat.card (d.H ⧸ (feitSibleySderivedH d ⊔ R)) =
          Nat.card (d.H ⧸ feitSibleySderivedH d) := by
      exact_mod_cast hsum
    exact (Nat.ne_of_lt hcardlt) hcardEq
  have hclosed : ∀ chi : ClassFunction d.H, chi ∈ X1 →
      conjugateCharacter chi ∈ X1 := by
    intro chi hchi
    have hchiData := (hX1mem chi).mp hchi
    have hconjNotKernel (A : Subgroup d.H)
        (hnot : ¬ subgroupInKernel' chi A) :
        ¬ subgroupInKernel' (conjugateCharacter chi) A := by
      intro hbarKernel
      apply hnot
      have hdouble :=
        Section6.subgroupInKernel'_conjugateCharacter
          (conjugateCharacter chi) hbarKernel
      have hcc : conjugateCharacter (conjugateCharacter chi) = chi := by
        ext x
        simp [conjugateCharacter]
      simpa [hcc] using hdouble
    have hbarChars : conjugateCharacter chi ∈ chars := by
      apply (hchars (conjugateCharacter chi)).mpr
      exact ⟨isIrreducibleCharacterOnGroup_conjugateCharacter
          ((hchars chi).mp hchiData.1.1).1,
        hconjNotKernel d.Q1 ((hchars chi).mp hchiData.1.1).2⟩
    apply (hX1mem (conjugateCharacter chi)).mpr
    exact ⟨⟨hbarChars, hconjNotKernel R hchiData.1.2⟩,
      hbarChars,
      Section6.subgroupInKernel'_conjugateCharacter chi hchiData.2.2⟩
  have hnonself : ∀ chi : ClassFunction d.H, chi ∈ X1 →
      conjugateCharacter chi ≠ chi := by
    intro chi hchi
    exact lemma_2_c d chars hchars hDodd chi ((hX1mem chi).mp hchi).1.1
  have hXsub : X1 ⊆ chars := by
    intro chi hchi
    exact ((hX1mem chi).mp hchi).1.1
  have hirr : ∀ chi : X1,
      IsIrreducibleCharacterOnGroup (chi : ClassFunction d.H) := by
    intro chi
    exact ((hchars (chi : ClassFunction d.H)).mp (hXsub chi.2)).1
  rcases lemma_2_b d chars hchars with ⟨hisoChars, htargetChars⟩
  have hiso : isCFLinearIsometryOnSpanOn X1 puncturedSet
      (Section1.inducedCFLinear d.H) := by
    intro phi theta hphi htheta
    exact hisoChars phi theta
      (integerSpanOn_mono hXsub hphi) (integerSpanOn_mono hXsub htheta)
  have htarget : ∀ phi : ClassFunction d.H,
      integerSpanOn X1 puncturedSet phi →
        Theory.Character.IsVirtualCharacter
            (Section1.inducedCFLinear d.H phi) ∧
          supportedOn (Section1.inducedCFLinear d.H phi) puncturedSet := by
    intro phi hphi
    exact htargetChars phi (integerSpanOn_mono hXsub hphi)
  have hpne : p ≠ 2 := by
    intro hp
    subst p
    exact d.Q1_not_two_group hpQ1
  have hpgt : 2 < p := lt_of_le_of_ne hpprime.two_le hpne.symm
  rcases feitSibley_step3_base_degree_data_core
      d chars hchars p hpprime hpQ1 R hRne hRnormal hRle hX1mem with
    ⟨deg, hdeg, hpower, hprefix⟩
  exact coherent_of_prime_power_degree_prefix_dvd_appendixIV
    d.H X1 (Section1.inducedCFLinear d.H) hXne hclosed hnonself
      hirr hiso htarget p (Nat.card d.D) hpprime hpgt
      (Nat.card_pos (α := d.D)) deg hdeg hpower hprefix

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem feitSibley_step3_exists_base_companion_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (R : Subgroup d.H) (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d)
    {Xbase : Finset (ClassFunction d.H)}
    (hXbaseMem : ∀ chi : ClassFunction d.H, chi ∈ Xbase ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d))
    (psi : ClassFunction d.H) (hpsiChars : psi ∈ chars)
    (hpsiNotR : ¬ subgroupInKernel' psi R) :
    ∃ chi : ClassFunction d.H, chi ∈ Xbase ∧
      ∃ n : Nat, degree psi = (n : Complex) * degree chi := by
  classical
  let : d.Q.Normal := d.Q_normal
  let : d.S.Normal := d.S_normal
  let : R.Normal := hRnormal
  let : (d.Q1.subgroupOf d.Q).Normal := d.Q1_normal_in_Q
  have hRleQ1 : R ≤ d.Q1 :=
    hRle.trans (by
      simpa [feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  have hRleQ : R ≤ d.Q := hRleQ1.trans d.Q1_le_Q
  rcases (lemma_2_a d chars hchars psi).mp hpsiChars with
    ⟨phi, hphiIrr, _hphiNotQ1, hind⟩
  rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
  have hphiNotR :
      ¬ subgroupInKernel' phi (R.subgroupOf d.Q) := by
    intro hphiR
    have hrhoR :
        subgroupInKernel' rho.character (R.subgroupOf d.Q) := by
      simpa [hphiEq] using hphiR
    have hindR :
        subgroupInKernel' (inducedCF d.Q rho.character) R :=
      (Section1.proposition_1_6_a d.Q R hRleQ rho).mp hrhoR
    apply hpsiNotR
    rw [← hind]
    simpa [hphiEq] using hindR
  let NQ : Subgroup d.Q := d.Q1.subgroupOf d.Q
  let rhoN : Representation Complex NQ (Fin n → Complex) :=
    rho.comp NQ.subtype
  let : Nontrivial (Fin n → Complex) :=
    Subrepresentation.irreducible_module_nontrivial rho
  obtain ⟨W, hWirr⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional rhoN
  let : FiniteDimensional Complex W.toSubmodule :=
    FiniteDimensional.of_injective W.toSubmodule.subtype Subtype.val_injective
  rcases BenderSuzuki.PFAppendixIV.lemma_2_Q1_restriction_homogeneous
      d rho hrhoIrr W hWirr with
    ⟨m, hm, hhom⟩
  let RN : Subgroup NQ := (R.subgroupOf d.Q).subgroupOf NQ
  have hWNotR :
      ¬ subgroupInKernel' W.toRepresentation.character RN := by
    intro hWKernel
    apply hphiNotR
    intro r
    let rN : NQ := ⟨(r : d.Q), hRleQ1 r.property⟩
    let rRN : RN := ⟨rN, r.property⟩
    have hrhoN : rhoN.character rN = degree rhoN.character := by
      calc
        rhoN.character rN =
            (m : Complex) * W.toRepresentation.character rN :=
          congrFun hhom rN
        _ = (m : Complex) * degree W.toRepresentation.character := by
          rw [hWKernel rRN]
        _ = rhoN.character 1 := by
          simpa [degree] using (congrFun hhom (1 : NQ)).symm
        _ = degree rhoN.character := rfl
    simpa [rhoN, hphiEq, rN, Representation.character, degree] using hrhoN
  let e : d.S × d.Q1 ≃* d.Q :=
    Section3.internalDirectProductMulEquiv d.internalDirectProduct_Q
  let kEquiv : NQ ≃* d.Q1 :=
    Subgroup.subgroupOfEquivOfLe d.Q1_le_Q
  let projQ1 : d.Q →* d.Q1 :=
    (MonoidHom.snd d.S d.Q1).comp e.symm.toMonoidHom
  let pi : d.Q →* NQ :=
    kEquiv.symm.toMonoidHom.comp projQ1
  have hpiSurj : Function.Surjective pi := by
    intro k
    let q : d.Q := e (MonoidHom.inr d.S d.Q1 (kEquiv k))
    refine ⟨q, ?_⟩
    apply kEquiv.injective
    simp [pi, projQ1, q, e, kEquiv]
  have hpiN (k : NQ) : pi k = k := by
    apply kEquiv.injective
    have hk :
        (e.symm k : d.S × d.Q1) =
          MonoidHom.inr d.S d.Q1 (kEquiv k) := by
      have hk_eq_val : (k : d.Q) = (⟨(kEquiv k).val,
          d.internalDirectProduct_Q.right_le (kEquiv k).property⟩ : d.Q) := by
        apply Subtype.ext
        apply Subtype.ext
        dsimp [kEquiv, Subgroup.subgroupOfEquivOfLe]
      calc
        e.symm k = e.symm (⟨(kEquiv k).val,
          d.internalDirectProduct_Q.right_le (kEquiv k).property⟩ : d.Q) := by rw [hk_eq_val]
        _ = MonoidHom.inr d.S d.Q1 (kEquiv k) := by
          rw [Section3.internalDirectProductMulEquiv_symm_apply_inr
            d.internalDirectProduct_Q (kEquiv k : d.Q1)]
    simp [pi, projQ1, hk, kEquiv]
  have hpiS (s : d.S) :
      pi ⟨(s : d.H), d.S_le_Q s.property⟩ = 1 := by
    apply kEquiv.injective
    have hs :
        e.symm (⟨(s : d.H), d.S_le_Q s.property⟩ : d.Q) =
          MonoidHom.inl d.S d.Q1 s := by
      exact Section3.internalDirectProductMulEquiv_symm_apply_inl
        d.internalDirectProduct_Q s
    simp [pi, projQ1, hs, kEquiv]
  let rhoComp : Representation Complex d.Q W.toSubmodule :=
    W.toRepresentation.comp pi
  have hrhoCompIrr : Representation.IsIrreducible rhoComp :=
    Section6.representation_isIrreducible_comp_surjective
      W.toRepresentation pi hpiSurj hWirr
  let phiComp : ClassFunction d.Q := rhoComp.character
  have hphiCompIrr : IsIrreducibleCharacterOnGroup phiComp := by
    refine ⟨Module.finrank Complex W.toSubmodule,
      Section1.standardizeRepresentation rhoComp, ?_, ?_⟩
    · exact Section1.standardizeRepresentation_irreducible rhoComp hrhoCompIrr
    · ext q
      symm
      exact Section1.standardizeRepresentation_character rhoComp q
  have hphiCompNotR :
      ¬ subgroupInKernel' phiComp (R.subgroupOf d.Q) := by
    intro hcompKernel
    apply hWNotR
    intro r
    let rQ : R.subgroupOf d.Q := ⟨(r : NQ), r.property⟩
    have hr := hcompKernel rQ
    have hrComp :
        rhoComp.character (rQ : d.Q) =
          (Module.finrank Complex W.toSubmodule : Complex) := by
      simpa [phiComp, degree] using hr
    have hpiR : pi (rQ : d.Q) = (r : NQ) := by
      simpa [rQ] using hpiN (r : NQ)
    have hr' :
        W.toRepresentation.character r =
          (Module.finrank Complex W.toSubmodule : Complex) := by
      calc
        W.toRepresentation.character r =
            W.toRepresentation.character (pi (rQ : d.Q)) := by rw [hpiR]
        _ = rhoComp.character (rQ : d.Q) := rfl
        _ = (Module.finrank Complex W.toSubmodule : Complex) := hrComp
    calc
      W.toRepresentation.character r =
          (Module.finrank Complex W.toSubmodule : Complex) := hr'
      _ = degree W.toRepresentation.character := by simp [degree]
  have hRNleNQ : R.subgroupOf d.Q ≤ NQ := by
    intro r hr
    exact hRleQ1 hr
  have hphiCompNotNQ : ¬ subgroupInKernel' phiComp NQ := by
    intro hcompNQ
    exact hphiCompNotR
      (subgroupInKernel'_mono_appendixIV hRNleNQ hcompNQ)
  have hSderivedLeS : feitSibleySderivedH d ≤ d.S := by
    simpa [feitSibleySderivedH] using
      Subgroup.map_subtype_le (derivedSubgroup d.S)
  have hSderivedLeQ : feitSibleySderivedH d ≤ d.Q :=
    hSderivedLeS.trans d.S_le_Q
  have : (feitSibleySderivedH d).Normal := by
    dsimp [feitSibleySderivedH]
    infer_instance
  have hphiCompKernelS :
      subgroupInKernel' phiComp
        ((feitSibleySderivedH d).subgroupOf d.Q) := by
    apply (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rhoComp _).mpr
    intro s
    let sS : d.S := ⟨(s : d.Q), hSderivedLeS s.property⟩
    change W.toRepresentation (pi (s : d.Q)) = 1
    rw [show pi (s : d.Q) = 1 by
      simpa [sS] using hpiS sS]
    exact map_one W.toRepresentation
  let chi : ClassFunction d.H := inducedCF d.Q phiComp
  have hchiChars : chi ∈ chars :=
    (lemma_2_a d chars hchars chi).mpr
      ⟨phiComp, hphiCompIrr, hphiCompNotNQ, rfl⟩
  have hchiNotR : ¬ subgroupInKernel' chi R := by
    intro hchiR
    apply hphiCompNotR
    exact (Section1.proposition_1_6_a d.Q R hRleQ rhoComp).mpr hchiR
  have hchiKernelS :
      subgroupInKernel' chi (feitSibleySderivedH d) :=
    (Section1.proposition_1_6_a d.Q (feitSibleySderivedH d)
      hSderivedLeQ rhoComp).mp hphiCompKernelS
  have hchiXbase : chi ∈ Xbase :=
    (hXbaseMem chi).mpr
      ⟨⟨hchiChars, hchiNotR⟩, hchiChars, hchiKernelS⟩
  have hdimC :
      (n : Complex) =
        (m : Complex) *
          (Module.finrank Complex W.toSubmodule : Complex) := by
    simpa [rhoN] using congrFun hhom (1 : NQ)
  have hpsiDegree :
      degree psi = (d.Q.index : Complex) * (n : Complex) := by
    rw [← hind, degree_inducedClassFunction d.Q phi, hphiEq,
      degree_representation_character]
    simp
  have hchiDegree :
      degree chi =
        (d.Q.index : Complex) *
          (Module.finrank Complex W.toSubmodule : Complex) := by
    change degree (inducedCF d.Q phiComp) = _
    rw [degree_inducedClassFunction d.Q phiComp]
    change (d.Q.index : Complex) * degree rhoComp.character = _
    rw [degree_representation_character]
  refine ⟨chi, hchiXbase, m, ?_⟩
  rw [hpsiDegree, hchiDegree]
  rw [hdimC]
  ring

private theorem feitSibley_step3_chief_factor_numeric_core
    (m s t z a b sigma : Real)
    (hm : 0 < m) (hs : 0 < s) (ht : 0 < t) (hz : 1 ≤ z)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsigma : sigma = m * s * t * (z - 1))
    (hobstruction : sigma ≤ 2 * a * b)
    (haSq : a ^ 2 ≤ m ^ 2 * t)
    (hbSq : b ^ 2 ≤ m ^ 2 * s * t) :
    s * (z - 1) ^ 2 ≤ 4 * m ^ 2 := by
  have hz0 : 0 ≤ z - 1 := by linarith
  have hsigma0 : 0 ≤ sigma := by
    rw [hsigma]
    positivity
  have hab0 : 0 ≤ 2 * a * b := by positivity
  have hsigmaSq : sigma ^ 2 ≤ (2 * a * b) ^ 2 :=
    (sq_le_sq₀ hsigma0 hab0).2 hobstruction
  have habSq : a ^ 2 * b ^ 2 ≤
      (m ^ 2 * t) * (m ^ 2 * s * t) :=
    mul_le_mul haSq hbSq (sq_nonneg b) (by positivity)
  rw [hsigma] at hsigmaSq
  have hsqChain :
      (m * s * t * (z - 1)) ^ 2 ≤
        4 * (m ^ 2 * t) * (m ^ 2 * s * t) := by
    nlinarith
  have hfactor : 0 < m ^ 2 * s * t ^ 2 := by positivity
  have hmulBound :
      (m ^ 2 * s * t ^ 2) * (s * (z - 1) ^ 2) ≤
        (m ^ 2 * s * t ^ 2) * (4 * m ^ 2) := by
    calc
      _ = (m * s * t * (z - 1)) ^ 2 := by ring
      _ ≤ 4 * (m ^ 2 * t) * (m ^ 2 * s * t) := hsqChain
      _ = _ := by ring
  exact le_of_mul_le_mul_left hmulBound hfactor

private theorem feitSibley_step3_arithmetic_contradiction_core
    (m s z : Nat) (hm : 0 < m)
    (hs : 2 ≤ s) (hz : 2 * m + 1 ≤ z)
    (hbound : (s : Real) * ((z : Real) - 1) ^ 2 ≤
      4 * (m : Real) ^ 2) :
    False := by
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  have hsR : (2 : Real) ≤ s := by exact_mod_cast hs
  have hzR' : (2 * m : Real) + 1 ≤ z := by exact_mod_cast hz
  have hzR : (2 : Real) * m ≤ (z : Real) - 1 := by
    linarith
  have hz0 : (0 : Real) ≤ (z : Real) - 1 := by
    nlinarith
  have hsq : ((2 : Real) * m) ^ 2 ≤ ((z : Real) - 1) ^ 2 :=
    (sq_le_sq₀ (by positivity) hz0).2 hzR
  have hs0 : (0 : Real) ≤ s := le_trans (by norm_num) hsR
  have hmul :
      (2 : Real) * ((2 : Real) * m) ^ 2 ≤
        (s : Real) * ((z : Real) - 1) ^ 2 :=
    mul_le_mul hsR hsq (sq_nonneg _) hs0
  nlinarith
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem feitSibley_step3_chief_factor_contradiction_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D)) (hD : d.D ≠ ⊥)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (_ : ¬ ∀ x y : d.Q1, x * y = y * x)
    (R : Subgroup d.H) (hRne : R ≠ ⊥)
    (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d)
    (R1 R2 : Subgroup d.H) [R1.Normal] [R2.Normal]
    (hR1le : R1 ≤ feitSibleySderivedH d)
    (hchief : IsChiefFactor R2 R1)
    {U V : Finset (ClassFunction d.H)}
    (hUmem : ∀ chi : ClassFunction d.H, chi ∈ U ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧ subgroupInKernel' chi R1)
    (hVmem : ∀ chi : ClassFunction d.H, chi ∈ V ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧ subgroupInKernel' chi R2)
    (hcoherentR1 : feitSibleyCoherent d U)
    (hnotcoherentR2 : ¬ feitSibleyCoherent d V) :
    False := by
  classical
  have hD_ne_bot : d.D ≠ ⊥ := hD
  let : d.S.Normal := d.S_normal
  let : d.Q1.Normal := d.Q1_normal
  let : d.Q.Normal := d.Q_normal
  let : R.Normal := hRnormal
  let : Group.IsNilpotent d.S := d.S_nilpotent
  let : Group.IsNilpotent d.Q1 := d.isNilpotent_Q1_of_D_ne_bot hD_ne_bot
  let : Group.IsSolvable d.Q1 := IsNilpotent.to_isSolvable
  have hSderivedLeS : feitSibleySderivedH d ≤ d.S := by
    simpa [feitSibleySderivedH] using
      Subgroup.map_subtype_le (derivedSubgroup d.S)
  have hR1leS : R1 ≤ d.S := hR1le.trans hSderivedLeS
  have hR2leS : R2 ≤ d.S := hchief.lt.le.trans hR1leS
  have hRleQ1 : R ≤ d.Q1 :=
    hRle.trans (by
      simpa [feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  let RQ1 : Subgroup d.Q1 := R.subgroupOf d.Q1
  let : RQ1.Normal := hRnormal.subgroupOf d.Q1
  have hRQ1central : RQ1 ≤ Subgroup.center d.Q1 := by
    intro r hr
    have hrAmbient : ((r : d.Q1) : d.H) ∈ feitSibleyCenterQ1H d :=
      hRle hr
    simpa [RQ1, feitSibleyCenterQ1H,
      subgroupOf_map_subtype_eq] using hrAmbient
  let Xbase : Finset (ClassFunction d.H) :=
    feitSibleySnonker d chars R ∩
      feitSibleySker d chars (feitSibleySderivedH d)
  have hXbaseMem : ∀ chi : ClassFunction d.H, chi ∈ Xbase ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d) := by
    intro chi
    simp only [Xbase, feitSibleySnonker, feitSibleySker,
      Finset.mem_inter, Finset.mem_filter]
  have hUV : U ⊆ V := by
    intro chi hchi
    rcases (hUmem chi).mp hchi with ⟨hchiNonker, hchiChars, hchiKer⟩
    exact (hVmem chi).mpr
      ⟨hchiNonker, hchiChars,
        subgroupInKernel'_mono_appendixIV hchief.lt.le hchiKer⟩
  have hUne : U.Nonempty := by
    rcases hcoherentR1.2.1 with ⟨phi, hphi, hphiNe⟩
    by_contra hne
    have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hUempty] at hphi
    rcases hphi.1 with ⟨v, rfl⟩
    apply hphiNe
    ext g
    simp [Section1.evalCoeff]
  have hXbaseNe : Xbase.Nonempty := by
    rcases hUne with ⟨psi0, hpsi0U⟩
    have hpsi0Data := (hUmem psi0).mp hpsi0U
    rcases feitSibley_step3_exists_base_companion_core
        d chars hchars R hRnormal hRle hXbaseMem psi0
          hpsi0Data.1.1 hpsi0Data.1.2 with
      ⟨chi, hchiXbase, _n, _hdegree⟩
    exact ⟨chi, hchiXbase⟩
  rcases feitSibley_step3_base_degree_data_core
      d chars hchars p hpprime hpQ1 R hRne hRnormal hRle hXbaseMem with
    ⟨deg, hdeg, hpower, _hprefix⟩
  let : Nonempty Xbase := hXbaseNe.to_subtype
  have hUniv : (Finset.univ : Finset Xbase).Nonempty :=
    Finset.univ_nonempty
  obtain ⟨chi0, _hchi0Univ, hchi0min⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Xbase) deg hUniv
  have hchi0Data := (hXbaseMem (chi0 : ClassFunction d.H)).mp chi0.property
  have hchi0U : (chi0 : ClassFunction d.H) ∈ U := by
    apply (hUmem (chi0 : ClassFunction d.H)).mpr
    exact ⟨hchi0Data.1, hchi0Data.2.1,
      subgroupInKernel'_mono_appendixIV hR1le hchi0Data.2.2⟩
  have hVsub : V ⊆ chars := by
    intro chi hchi
    exact ((hVmem chi).mp hchi).2.1
  have hirrV :
      ∀ chi : V,
        IsIrreducibleCharacterOnGroup (chi : ClassFunction d.H) := by
    intro chi
    exact ((hchars (chi : ClassFunction d.H)).mp
      (hVsub chi.property)).1
  rcases lemma_2_b d chars hchars with ⟨hisoChars, htargetChars⟩
  have hisoV :
      isCFLinearIsometryOnSpanOn V puncturedSet
        (Section1.inducedCFLinear d.H) := by
    intro phi theta hphi htheta
    exact hisoChars phi theta
      (Section5.integerSpanOn_mono hVsub hphi)
      (Section5.integerSpanOn_mono hVsub htheta)
  have htargetV :
      ∀ phi : ClassFunction d.H,
        integerSpanOn V puncturedSet phi →
          Theory.Character.IsVirtualCharacter
              (Section1.inducedCFLinear d.H phi) ∧
            supportedOn
              (Section1.inducedCFLinear d.H phi) puncturedSet := by
    intro phi hphi
    exact htargetChars phi
      (Section5.integerSpanOn_mono hVsub hphi)
  have hdivV :
      ∀ psi : ClassFunction d.H, psi ∈ V →
        ∃ n : Nat,
          degree psi = (n : Complex) *
            degree (chi0 : ClassFunction d.H) := by
    intro psi hpsiV
    have hpsiData := (hVmem psi).mp hpsiV
    rcases feitSibley_step3_exists_base_companion_core
        d chars hchars R hRnormal hRle hXbaseMem psi
          hpsiData.1.1 hpsiData.1.2 with
      ⟨chi, hchiXbase, n, hpsiDegree⟩
    let chiX : Xbase := ⟨chi, hchiXbase⟩
    rcases hpower chi0 with ⟨k0, hk0⟩
    rcases hpower chiX with ⟨k, hk⟩
    have hdegLe : deg chi0 ≤ deg chiX :=
      hchi0min chiX (Finset.mem_univ _)
    have hpowLe : p ^ k0 ≤ p ^ k := by
      apply Nat.le_of_mul_le_mul_left
        (by simpa [hk0, hk] using hdegLe)
      simpa [Nat.card_eq_fintype_card] using (Nat.card_pos (α := d.D))
    have hkle : k0 ≤ k :=
      (Nat.pow_le_pow_iff_right hpprime.one_lt).mp hpowLe
    rcases Nat.exists_eq_add_of_le hkle with ⟨c, hkc⟩
    have hchiMultiple :
        degree chi =
          ((p ^ c : Nat) : Complex) *
            degree (chi0 : ClassFunction d.H) := by
      rw [(hdeg chiX).2, (hdeg chi0).2, hk, hk0, hkc, Nat.pow_add]
      push_cast
      ring
    refine ⟨n * p ^ c, ?_⟩
    rw [hpsiDegree, hchiMultiple]
    push_cast
    ring
  obtain ⟨psi, hpsiV, _hpsiU, hdegreeBound⟩ :=
    exists_degree_obstruction_of_not_coherent_appendixIV
      d.H U V (Section1.inducedCFLinear d.H) hUV
      (chi0 : ClassFunction d.H) hchi0U hirrV hisoV htargetV hdivV
      hcoherentR1 hnotcoherentR2
  have hUchar :
      ∀ chi : ClassFunction d.H, chi ∈ U ↔
        IsIrreducibleCharacterOnGroup chi ∧
          subgroupInKernel' chi R1 ∧
            ¬ subgroupInKernel' chi R := by
    intro chi
    constructor
    · intro hchi
      have hchiData := (hUmem chi).mp hchi
      exact ⟨((hchars chi).mp hchiData.1.1).1,
        hchiData.2.2, hchiData.1.2⟩
    · rintro ⟨hirr, hkerR1, hnotR⟩
      have hnotQ1 : ¬ subgroupInKernel' chi d.Q1 := by
        intro hkerQ1
        exact hnotR (subgroupInKernel'_mono_appendixIV hRleQ1 hkerQ1)
      have hchiChars : chi ∈ chars :=
        (hchars chi).mpr ⟨hirr, hnotQ1⟩
      exact (hUmem chi).mpr
        ⟨⟨hchiChars, hnotR⟩, hchiChars, hkerR1⟩
  have hsumU :=
    exceptional_kernel_degree_sq_sum_appendixIV
      R1 R U hUchar
  have hpsiData := (hVmem psi).mp hpsiV
  have hpsiKernel : subgroupInKernel' psi R2 := hpsiData.2.2
  have hpsiChars : psi ∈ chars := hpsiData.1.1
  rcases (lemma_2_a d chars hchars psi).mp hpsiChars with
    ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
  rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
  have hR2leQ : R2 ≤ d.Q := hR2leS.trans d.S_le_Q
  have hindKerPhi : subgroupInKernel' (inducedCF d.Q phi) R2 := by
    rw [hind]
    exact hpsiKernel
  have hindKerRho : subgroupInKernel' (inducedCF d.Q rho.character) R2 := by
    simpa [hphiEq] using hindKerPhi
  have hrhoKerCF :
      subgroupInKernel' rho.character (R2.subgroupOf d.Q) :=
    (Section1.proposition_1_6_a d.Q R2 hR2leQ rho).mpr hindKerRho
  have hrepker :
      subgroupInRepresentationKernel rho (R2.subgroupOf d.Q) :=
    (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho _).mp hrhoKerCF
  let N : Subgroup d.S := R2.subgroupOf d.S
  let : N.Normal := (inferInstance : R2.Normal).subgroupOf d.S
  let e : d.S × d.Q1 ≃* d.Q :=
    Section3.internalDirectProductMulEquiv d.internalDirectProduct_Q
  have hker : ∀ x : N.prod (⊥ : Subgroup d.Q1), rho (e x) = 1 := by
    intro x
    have hx2 : x.1.2 = 1 := Subgroup.mem_bot.mp x.property.2
    have hinl :
        ((e (MonoidHom.inl d.S d.Q1 x.1.1) : d.Q) : d.H) =
          (x.1.1 : d.H) := by
      simpa [e] using congrArg Subtype.val
        (Section3.internalDirectProductMulEquiv_apply_inl
          d.internalDirectProduct_Q x.1.1)
    have hinr :
        ((e (MonoidHom.inr d.S d.Q1 x.1.2) : d.Q) : d.H) =
          (x.1.2 : d.H) := by
      simpa [e] using congrArg Subtype.val
        (Section3.internalDirectProductMulEquiv_apply_inr
          d.internalDirectProduct_Q x.1.2)
    have hxdecomp :
        (x.1 : d.S × d.Q1) =
          MonoidHom.inl d.S d.Q1 x.1.1 *
            MonoidHom.inr d.S d.Q1 x.1.2 := by
      ext <;> simp
    have heq : ((e x : d.Q) : d.H) = (x.1.1 : d.H) := by
      rw [show e x = e (MonoidHom.inl d.S d.Q1 x.1.1 *
        MonoidHom.inr d.S d.Q1 x.1.2) from congrArg e hxdecomp]
      rw [map_mul]
      change ((e (MonoidHom.inl d.S d.Q1 x.1.1) : d.Q) : d.H) *
          ((e (MonoidHom.inr d.S d.Q1 x.1.2) : d.Q) : d.H) = _
      rw [hinl, hinr, hx2]
      simp
    apply hrepker ⟨e x, ?_⟩
    change ((e x : d.Q) : d.H) ∈ R2
    rw [heq]
    exact x.property.1
  let : Representation.IsIrreducible rho := hrhoIrr
  have hnSq :
      n ^ 2 ≤
        (Subgroup.comap (QuotientGroup.mk' N)
          (Subgroup.center (d.S ⧸ N))).index * RQ1.index := by
    simpa [N, e, RQ1] using
      (irreducible_finrank_sq_le_centerModulo_index_mul_subgroup_index_appendixIV
        e N RQ1 hRQ1central rho hker)
  let ZS : Subgroup d.S :=
    Subgroup.comap (QuotientGroup.mk' N)
      (Subgroup.center (d.S ⧸ N))
  let R1S : Subgroup d.S := R1.subgroupOf d.S
  have hR1leZSmap : R1 ≤ ZS.map d.S.subtype := by
    simpa [ZS, N] using
      (chiefFactor_le_centerModulo_preimage_appendixIV
        d.S R1 R2 hchief hR1leS)
  have hR1SleZS : R1S ≤ ZS := by
    intro x hx
    have hxmap : (x : d.H) ∈ ZS.map d.S.subtype :=
      hR1leZSmap hx
    rcases Subgroup.mem_map.mp hxmap with ⟨z, hz, hzx⟩
    have hzx' : z = x := by
      apply Subtype.ext
      exact hzx
    simpa [hzx'] using hz
  have hZSindex : ZS.index ≤ R1S.index :=
    Subgroup.index_antitone hR1SleZS
  have hnSqBound : n ^ 2 ≤ R1S.index * RQ1.index :=
    hnSq.trans (Nat.mul_le_mul_right RQ1.index hZSindex)
  have hpsiDegree :
      degree psi =
        (n : Complex) *
          (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
    rw [← hind, degree_inducedClassFunction d.Q phi, hphiEq,
      degree_representation_character]
    simp [Subgroup.relIndex_top_right, mul_comm]
  have hQindex :
      d.Q.relIndex (⊤ : Subgroup d.H) = Nat.card d.D :=
    feitSibley_Q_relIndex_top_eq_card_D_appendixIV d
  have hpsiRe :
      (degree psi).re = (n : Real) * Nat.card d.D := by
    rw [hpsiDegree, hQindex]
    simp
  rcases feitSibley_step3_degree_shape_core
      d chars hchars p hpprime hpQ1 R hRnormal hRle
        (chi0 : ClassFunction d.H) hchi0Data.1.1 hchi0Data.2.2 with
    ⟨k0, n0, hn0pos, hchi0Degree, hn0, hn0Dvd⟩
  have hchi0Re :
      (degree (chi0 : ClassFunction d.H)).re = (n0 : Real) := by
    rw [hchi0Degree]
    simp
  let T : Subgroup d.H := R1 ⊔ R
  let W : Subgroup d.H := R1 ⊔ d.Q1
  have hTleW : T ≤ W :=
    sup_le_sup le_rfl hRleQ1
  have hTinfQ1 : T ⊓ d.Q1 = R := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxT, hxQ1⟩
      rcases Subgroup.mem_sup_of_normal_right.mp hxT with
        ⟨s, hs, r, hr, hsr⟩
      have hsQ1 : s ∈ d.Q1 := by
        have hseq : s = x * r⁻¹ := by
          rw [← hsr]
          simp
        rw [hseq]
        exact d.Q1.mul_mem hxQ1 (d.Q1.inv_mem (hRleQ1 hr))
      have hsOne : s = 1 := by
        apply Subgroup.mem_bot.mp
        exact d.S_disjoint_Q1.le_bot ⟨hR1leS hs, hsQ1⟩
      rw [hsOne, one_mul] at hsr
      exact hsr ▸ hr
    · intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨(show R ≤ T from le_sup_right) hx, hRleQ1 hx⟩
  have hTsupQ1 : T ⊔ d.Q1 = W := by
    dsimp [T, W]
    rw [sup_assoc, sup_eq_right.2 hRleQ1]
  have hTrelW : T.relIndex W = R.relIndex d.Q1 := by
    calc
      T.relIndex W = T.relIndex (T ⊔ d.Q1) := by rw [hTsupQ1]
      _ = T.relIndex d.Q1 :=
        Subgroup.relIndex_sup_left d.Q1 T
      _ = (T ⊓ d.Q1).relIndex d.Q1 :=
        (Subgroup.inf_relIndex_right T d.Q1).symm
      _ = R.relIndex d.Q1 := by rw [hTinfQ1]
  obtain ⟨hcardR1, hcardW⟩ :=
    feitSibley_step2_quotient_card_factor_core d R1 hR1leS
  have hWtop :
      W.relIndex (⊤ : Subgroup d.H) =
        Nat.card d.D * R1.relIndex d.S := by
    simpa [W, Subgroup.relIndex_top_right, Subgroup.index_eq_card] using
      hcardW
  have hTtop :
      T.relIndex (⊤ : Subgroup d.H) =
        Nat.card d.D * R1.relIndex d.S * R.relIndex d.Q1 := by
    have hmul :=
      Subgroup.relIndex_mul_relIndex T W (⊤ : Subgroup d.H)
        hTleW le_top
    calc
      T.relIndex (⊤ : Subgroup d.H) =
          T.relIndex W * W.relIndex (⊤ : Subgroup d.H) := hmul.symm
      _ = R.relIndex d.Q1 *
          (Nat.card d.D * R1.relIndex d.S) := by
        rw [hTrelW, hWtop]
      _ = Nat.card d.D * R1.relIndex d.S *
          R.relIndex d.Q1 := by ac_rfl
  have hcardT :
      Nat.card (d.H ⧸ T) =
        Nat.card d.D * R1.relIndex d.S * R.relIndex d.Q1 := by
    simpa [Subgroup.relIndex_top_right, Subgroup.index_eq_card] using hTtop
  have hRQ1card : Nat.card RQ1 = Nat.card R :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hRleQ1).toEquiv
  have hQ1factor :
      R.relIndex d.Q1 * Nat.card R = Nat.card d.Q1 := by
    have hindexMul := RQ1.index_mul_card
    rw [hRQ1card] at hindexMul
    simpa [RQ1, Subgroup.relIndex] using hindexMul
  have hsumFactor :
      (∑ chi : U,
          (degree (chi : ClassFunction d.H)).re ^ 2) =
        (Nat.card d.D : Real) * (R1S.index : Real) *
          (RQ1.index : Real) * ((Nat.card R : Real) - 1) := by
    rw [show R1 ⊔ R = T from rfl] at hsumU
    rw [hcardR1, hcardT] at hsumU
    have hR1rel : R1.relIndex d.S = R1S.index := rfl
    have hRrel : R.relIndex d.Q1 = RQ1.index := rfl
    have hfactorR :
        (Nat.card d.Q1 : Real) =
          (RQ1.index : Real) * Nat.card R := by
      exact_mod_cast hQ1factor.symm
    push_cast at hsumU
    rw [hR1rel, hRrel, hfactorR] at hsumU
    nlinarith
  have hn0SqDvd :
      n0 ^ 2 ∣ Nat.card d.D ^ 2 * R.relIndex d.Q1 := by
    convert Nat.mul_dvd_mul_left (Nat.card d.D ^ 2) hn0Dvd using 1
    rw [hn0]
    ring
  have hn0SqBoundNat :
      n0 ^ 2 ≤ Nat.card d.D ^ 2 * RQ1.index := by
    apply Nat.le_of_dvd
    · exact Nat.mul_pos (pow_pos Nat.card_pos 2)
        (by rw [Subgroup.index_eq_card]; exact Nat.card_pos)
    · simpa [RQ1, Subgroup.relIndex] using hn0SqDvd
  have hchi0Sq :
      (degree (chi0 : ClassFunction d.H)).re ^ 2 ≤
        (Nat.card d.D : Real) ^ 2 * (RQ1.index : Real) := by
    rw [hchi0Re]
    exact_mod_cast hn0SqBoundNat
  have hpsiSqNat :
      (n * Nat.card d.D) ^ 2 ≤
        Nat.card d.D ^ 2 * R1S.index * RQ1.index := by
    calc
      (n * Nat.card d.D) ^ 2 =
          Nat.card d.D ^ 2 * n ^ 2 := by ring
      _ ≤ Nat.card d.D ^ 2 * (R1S.index * RQ1.index) :=
        Nat.mul_le_mul_left (Nat.card d.D ^ 2) hnSqBound
      _ = Nat.card d.D ^ 2 * R1S.index * RQ1.index := by ring
  have hpsiSq :
      (degree psi).re ^ 2 ≤
        (Nat.card d.D : Real) ^ 2 *
          (R1S.index : Real) * (RQ1.index : Real) := by
    rw [hpsiRe]
    exact_mod_cast hpsiSqNat
  have hnumeric :
      (R1S.index : Real) * ((Nat.card R : Real) - 1) ^ 2 ≤
        4 * (Nat.card d.D : Real) ^ 2 := by
    apply feitSibley_step3_chief_factor_numeric_core
      (Nat.card d.D : Real) (R1S.index : Real)
      (RQ1.index : Real) (Nat.card R : Real)
      (degree (chi0 : ClassFunction d.H)).re (degree psi).re
      (∑ chi : U, (degree (chi : ClassFunction d.H)).re ^ 2)
    · exact_mod_cast (Nat.card_pos (α := d.D))
    · exact_mod_cast (show 0 < R1S.index by
        rw [Subgroup.index_eq_card]
        exact Nat.card_pos)
    · exact_mod_cast (show 0 < RQ1.index by
        rw [Subgroup.index_eq_card]
        exact Nat.card_pos)
    · exact_mod_cast (show 1 ≤ Nat.card R by
        exact Nat.card_pos)
    · rw [hchi0Re]
      positivity
    · rw [hpsiRe]
      positivity
    · exact hsumFactor
    · nlinarith [hdegreeBound]
    · exact hchi0Sq
    · exact hpsiSq
  have hR1ne : R1 ≠ ⊥ := by
    intro hR1
    subst R1
    exact (not_lt_of_ge bot_le) hchief.lt
  have hSne : d.S ≠ ⊥ := by
    intro hS
    apply hR1ne
    exact le_bot_iff.mp (by simpa [hS] using hR1leS)
  let : Nontrivial d.S :=
    (Subgroup.nontrivial_iff_ne_bot d.S).2 hSne
  have hR1SleDerived : R1S ≤ derivedSubgroup d.S := by
    intro x hx
    have hxmap := hR1le hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hyx' : y = x := by
      apply Subtype.ext
      exact hyx
    simpa [hyx'] using hy
  have hderivedLt : derivedSubgroup d.S < ⊤ := by
    change commutator d.S < ⊤
    let : Group.IsSolvable d.S := IsNilpotent.to_isSolvable
    exact Group.IsSolvable.commutator_lt_top_of_nontrivial (G := d.S)
  have hR1Slt : R1S < ⊤ :=
    hR1SleDerived.trans_lt hderivedLt
  have hsTwo : 2 ≤ R1S.index := by
    have hone := Subgroup.one_lt_index_of_ne_top hR1Slt.ne
    omega
  let : MulDistribMulAction d.D R :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := d.H) d.D R
      (Subgroup.le_normalizer_of_normal (H := R))
  have hfreeR :
      ∀ a : d.D, a ≠ 1 →
        ∀ z : R, a • z = z → z = 1 := by
    intro a ha z hfix
    have hfixH :
        (a : d.H) * (z : d.H) * (a : d.H)⁻¹ = (z : d.H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have haH : (a : d.H) ≠ 1 := by
      intro ha1
      exact ha (Subtype.ext ha1)
    let hzQ1 : d.Q1 := ⟨(z : d.H), hRleQ1 z.property⟩
    have hfixQ1 :
        (a : d.H) * (hzQ1 : d.H) * (a : d.H)⁻¹ = (hzQ1 : d.H) := by
      simpa [hzQ1] using hfixH
    have hz1 : hzQ1 = 1 :=
      d.D_fixedPointFree_on_Q1 a haH hzQ1 hfixQ1
    apply Subtype.ext
    change (z : d.H) = (1 : d.H)
    calc
      (z : d.H) = (hzQ1 : d.H) := rfl
      _ = ((1 : d.Q1) : d.H) :=
        congrArg (fun x : d.Q1 => ((x : d.H))) hz1
      _ = 1 := rfl
  have hdivR :
      Nat.card d.D ∣ Nat.card R - 1 :=
    actor_dvd_group_card_sub_one_appendixIV hfreeR
  have hRcardDvd : Nat.card R ∣ Nat.card d.Q1 := by
    have hdvd := Subgroup.card_subgroup_dvd_card RQ1
    rw [hRQ1card] at hdvd
    exact hdvd
  have hRodd : Odd (Nat.card R) :=
    odd_of_card_dvd d.Q1_odd hRcardDvd
  let : Nontrivial R :=
    (Subgroup.nontrivial_iff_ne_bot R).2 hRne
  have hRcard : 1 < Nat.card R :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hzLower : 2 * Nat.card d.D + 1 ≤ Nat.card R :=
    two_mul_add_one_le_of_odd_dvd_card_sub_one_appendixIV
      hDodd hRodd hRcard hdivR
  exact feitSibley_step3_arithmetic_contradiction_core
    (Nat.card d.D) R1S.index (Nat.card R)
      Nat.card_pos hsTwo hzLower hnumeric

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem feitSibley_step3_chief_descent_of_D_ne_bot_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D)) (hD : d.D ≠ ⊥)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (hab : ¬ ∀ x y : d.Q1, x * y = y * x)
    (R : Subgroup d.H) (hRne : R ≠ ⊥)
    (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d)
    {Xbase : Finset (ClassFunction d.H)}
    (hXbaseMem : ∀ chi : ClassFunction d.H, chi ∈ Xbase ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d))
    (hbase : feitSibleyCoherent d Xbase) :
    feitSibleyCoherent d (feitSibleySnonker d chars R) := by
  classical
  let : d.S.Normal := d.S_normal
  let X := feitSibleySnonker d chars R
  let P : Subgroup d.H → Prop := fun R0 =>
    R0 ≤ feitSibleySderivedH d ∧ R0.Normal ∧
      feitSibleyCoherent d (X ∩ feitSibleySker d chars R0)
  have hPtop : P (feitSibleySderivedH d) := by
    refine ⟨le_rfl, ?_, ?_⟩
    · dsimp [feitSibleySderivedH]
      infer_instance
    · have hEq :
          X ∩ feitSibleySker d chars (feitSibleySderivedH d) = Xbase := by
        ext chi
        rw [hXbaseMem]
        simp only [X, feitSibleySnonker, feitSibleySker,
          Finset.mem_inter, Finset.mem_filter]
      rw [hEq]
      exact hbase
  rcases Finite.exists_le_minimal (p := P) hPtop with
    ⟨R1, _hR1sel, hR1min⟩
  rcases hR1min.prop with ⟨hR1le, hR1normal, hcoherentR1⟩
  by_cases hR1bot : R1 = ⊥
  · subst R1
    have hSkerBot : feitSibleySker d chars ⊥ = chars := by
      apply Finset.filter_eq_self.mpr
      intro chi hchi a
      have ha : (a : d.H) = 1 := Subgroup.mem_bot.mp a.property
      rw [ha]
      rfl
    have hXsub : X ⊆ chars := by
      intro chi hchi
      exact (Finset.mem_filter.mp hchi).1
    have hXinter : X ∩ feitSibleySker d chars ⊥ = X := by
      rw [hSkerBot]
      exact Finset.inter_eq_left.mpr hXsub
    rw [hXinter] at hcoherentR1
    simpa [X] using hcoherentR1
  · let : R1.Normal := hR1normal
    obtain ⟨R2, hchief⟩ :=
      exists_chiefFactor_below_appendixIV R1 hR1bot
    let : R2.Normal := hchief.normal_K
    have hR2le : R2 ≤ feitSibleySderivedH d :=
      hchief.lt.le.trans hR1le
    have hnotcoherentR2 :
        ¬ feitSibleyCoherent d
          (X ∩ feitSibleySker d chars R2) := by
      intro hcoherentR2
      have hP2 : P R2 := ⟨hR2le, inferInstance, hcoherentR2⟩
      have hR1leR2 := hR1min.le_of_le hP2 hchief.lt.le
      exact hchief.lt.2 hR1leR2
    exact False.elim
      (feitSibley_step3_chief_factor_contradiction_core
        d chars hchars hDodd hD p hpprime hpQ1 hab R hRne hRnormal hRle
          R1 R2 hR1le hchief
          (U := X ∩ feitSibleySker d chars R1)
          (V := X ∩ feitSibleySker d chars R2)
          (by
            intro chi
            simp only [X, feitSibleySnonker, feitSibleySker,
              Finset.mem_inter, Finset.mem_filter])
          (by
            intro chi
            simp only [X, feitSibleySnonker, feitSibleySker,
              Finset.mem_inter, Finset.mem_filter])
          hcoherentR1 hnotcoherentR2)

private theorem feitSibley_step3_coherent_of_D_eq_bot_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D)) (hD : d.D = ⊥)
    (R : Subgroup d.H) (hRne : R ≠ ⊥)
    (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d) :
    feitSibleyCoherent d (feitSibleySnonker d chars R) := by
  classical
  let : R.Normal := hRnormal
  have hRleQ1 : R ≤ d.Q1 :=
    hRle.trans (by
      simpa [feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  obtain ⟨A, hA, degA, _hdegA, hsumA⟩ :=
    Section6.theorem_6_6_complete_nonkernel_degree_data
      (L := d.H) (Z := R)
  have hindexlt : Nat.card (d.H ⧸ R) < Nat.card d.H := by
    calc
      Nat.card (d.H ⧸ R) = R.index := (Subgroup.index_eq_card R).symm
      _ < (⊥ : Subgroup d.H).index :=
        Subgroup.index_strictAnti (bot_lt_iff_ne_bot.mpr hRne)
      _ = Nat.card d.H := Subgroup.index_bot
  have hAne : A.Nonempty := by
    by_contra hne
    have hsumZero : ∑ X : A, degA X ^ (2 : Nat) = 0 := by
      apply Finset.sum_eq_zero
      intro X _hX
      exact (hne ⟨X.1, X.2⟩).elim
    rw [hsumZero, zero_add] at hsumA
    exact (Nat.ne_of_lt hindexlt) hsumA
  rcases hAne with ⟨chi, hchiA⟩
  have hchiIrr : IsIrreducibleCharacterOnGroup chi := (hA chi).mp hchiA |>.1
  have hchiNotR : ¬ subgroupInKernel' chi R := (hA chi).mp hchiA |>.2
  have hchiNotQ1 : ¬ subgroupInKernel' chi d.Q1 := by
    intro hkerQ1
    exact hchiNotR (subgroupInKernel'_mono_appendixIV hRleQ1 hkerQ1)
  have hchiChars : chi ∈ chars := (hchars chi).mpr ⟨hchiIrr, hchiNotQ1⟩
  have hchiX : chi ∈ feitSibleySnonker d chars R :=
    Finset.mem_filter.mpr ⟨hchiChars, hchiNotR⟩
  have hconjNotKernel (B : Subgroup d.H)
      (hnot : ¬ subgroupInKernel' chi B) :
      ¬ subgroupInKernel' (conjugateCharacter chi) B := by
    intro hbarKernel
    apply hnot
    have hdouble := Section6.subgroupInKernel'_conjugateCharacter
      (conjugateCharacter chi) hbarKernel
    have hcc : conjugateCharacter (conjugateCharacter chi) = chi := by
      ext x
      simp [conjugateCharacter]
    simpa [hcc] using hdouble
  have hbarChars : conjugateCharacter chi ∈ chars := by
    apply (hchars (conjugateCharacter chi)).mpr
    exact ⟨isIrreducibleCharacterOnGroup_conjugateCharacter hchiIrr,
      hconjNotKernel d.Q1 hchiNotQ1⟩
  have hbarX : conjugateCharacter chi ∈ feitSibleySnonker d chars R :=
    Finset.mem_filter.mpr ⟨hbarChars, hconjNotKernel R hchiNotR⟩
  have hbarNe : conjugateCharacter chi ≠ chi :=
    lemma_2_c d chars hchars hDodd chi hchiChars
  have hsourceNonempty :
      integerSpanOnNonempty (feitSibleySnonker d chars R) puncturedSet :=
    integerSpanOnNonempty_of_conjugate_pair
      hchiX hbarX hbarNe.symm
        (isCharacter_of_isIrreducibleCharacterOnGroup hchiIrr)
  have hXsub : feitSibleySnonker d chars R ⊆ chars := by
    intro psi hpsi
    exact (Finset.mem_filter.mp hpsi).1
  exact IsCoherentTriple_mono hXsub hsourceNonempty
    (feitSibley_coherent_of_D_eq_bot_core d chars hchars hDodd hD)

private theorem feitSibley_step3_nonkernel_coherence_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D))
    (hp : ∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1)
    (hab : ¬ ∀ x y : d.Q1, x * y = y * x)
    (R : Subgroup d.H) (hRne : R ≠ ⊥)
    (hRnormal : R.Normal)
    (hRle : R ≤ feitSibleyCenterQ1H d) :
    feitSibleyCoherent d (feitSibleySnonker d chars R) := by
  classical
  rcases hp with ⟨p, hpprime, hpQ1⟩
  by_cases hD : d.D = ⊥
  · exact feitSibley_step3_coherent_of_D_eq_bot_core
      d chars hchars hDodd hD R hRne hRnormal hRle
  · let Xbase :=
      feitSibleySnonker d chars R ∩
        feitSibleySker d chars (feitSibleySderivedH d)
    have hXbaseMem : ∀ chi : ClassFunction d.H, chi ∈ Xbase ↔
        (chi ∈ chars ∧ ¬ subgroupInKernel' chi R) ∧
          chi ∈ chars ∧
            subgroupInKernel' chi (feitSibleySderivedH d) := by
      intro chi
      simp only [Xbase, feitSibleySnonker, feitSibleySker,
        Finset.mem_inter, Finset.mem_filter]
    have hbase : feitSibleyCoherent d Xbase :=
      feitSibley_step3_base_family_coherence_core
        d chars hchars hDodd p hpprime hpQ1 hab R hRne hRnormal hRle
          hXbaseMem
    exact feitSibley_step3_chief_descent_of_D_ne_bot_core
      d chars hchars hDodd hD p hpprime hpQ1 hab R hRne hRnormal hRle
        hXbaseMem hbase
private theorem feitSibley_step4_Z_properties
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (hp : ∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1)
    (hab : ¬ ∀ x y : d.Q1, x * y = y * x) :
    feitSibleyZ d ≠ ⊥ ∧
      (feitSibleyZ d).Normal ∧
      feitSibleyZ d ≤ feitSibleyCenterQ1H d := by
  rcases hp with ⟨p, hpprime, hpQ1⟩
  let : Fact p.Prime := ⟨hpprime⟩
  let : Fact (IsPGroup p d.Q1) := ⟨hpQ1⟩
  let : d.Q1.Normal := d.Q1_normal
  have hderivedNe : derivedSubgroup d.Q1 ≠ ⊥ := by
    intro hderived
    apply hab
    have hcenter : Subgroup.center d.Q1 = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top (G := d.Q1)).mp hderived
    intro x y
    have hx : x ∈ Subgroup.center d.Q1 := by
      rw [hcenter]
      trivial
    exact (Subgroup.mem_center_iff.mp hx y).symm
  let : Nontrivial (derivedSubgroup d.Q1) :=
    (Subgroup.nontrivial_iff_ne_bot (derivedSubgroup d.Q1)).2 hderivedNe
  obtain ⟨x, hxne, hxcenter⟩ :=
    exists_nontrivial_center_mem_normal
      (G := d.Q1) (p := p) (derivedSubgroup d.Q1)
  have hxDerivedH : ((x : d.Q1) : d.H) ∈ feitSibleyQ1derivedH d := by
    exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩
  have hxCenterH : ((x : d.Q1) : d.H) ∈ feitSibleyCenterQ1H d := by
    exact Subgroup.mem_map.mpr ⟨(x : d.Q1), hxcenter, rfl⟩
  have hxZ : ((x : d.Q1) : d.H) ∈ feitSibleyZ d := ⟨hxDerivedH, hxCenterH⟩
  refine ⟨?_, ?_, inf_le_right⟩
  · intro hZ
    have hxH : ((x : d.Q1) : d.H) = 1 :=
      Subgroup.mem_bot.mp (hZ ▸ hxZ)
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    exact hxH
  · dsimp [feitSibleyZ, feitSibleyQ1derivedH,
      feitSibleyCenterQ1H]
    infer_instance

private theorem feitSibley_step4_XY_coherence_nonempty
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (_ : IsFeitSibleyExceptionalFamily d chars)
    (_ : feitSibleyZ d ≠ ⊥)
    (hcoherentX : feitSibleyCoherent d (feitSibleyX d chars))
    (hcoherentY : feitSibleyCoherent d (feitSibleyY d chars))
    (hYcard : 2 ≤ (feitSibleyY d chars).card) :
    Disjoint (feitSibleyX d chars) (feitSibleyY d chars) ∧
      feitSibleyCoherent d (feitSibleyX d chars) ∧
      feitSibleyCoherent d (feitSibleyY d chars) ∧
      (feitSibleyX d chars).Nonempty ∧
      (feitSibleyY d chars).Nonempty := by
  classical
  have hQderived :
      feitSibleyQderivedH d =
        feitSibleySderivedH d ⊔ feitSibleyQ1derivedH d := by
    simpa [feitSibleyQderivedH, feitSibleySderivedH,
      feitSibleyQ1derivedH] using d.map_derivedSubgroup_Q_eq_sup
  have hZleQderived : feitSibleyZ d ≤ feitSibleyQderivedH d := by
    rw [hQderived]
    exact inf_le_left.trans le_sup_right
  have hdisjoint : Disjoint (feitSibleyX d chars) (feitSibleyY d chars) := by
    rw [Finset.disjoint_left]
    intro chi hchiX hchiY
    have hnotZ : ¬ subgroupInKernel' chi (feitSibleyZ d) :=
      (Finset.mem_filter.mp hchiX).2
    have hkerQ : subgroupInKernel' chi (feitSibleyQderivedH d) :=
      (Finset.mem_filter.mp hchiY).2
    exact hnotZ (subgroupInKernel'_mono_appendixIV hZleQderived hkerQ)
  have hXne : (feitSibleyX d chars).Nonempty := by
    rcases hcoherentX.2.1 with ⟨phi, hphi, hphiNe⟩
    by_contra hne
    have hempty : feitSibleyX d chars = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty] at hphi
    rcases hphi.1 with ⟨v, rfl⟩
    apply hphiNe
    ext g
    simp [Section1.evalCoeff]
  have hYne : (feitSibleyY d chars).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  exact ⟨hdisjoint, hcoherentX, hcoherentY, hXne, hYne⟩

private theorem feitSibley_step4_degree_data
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (_ : Odd (Nat.card d.D))
    (hp : ∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1)
    (hZne : feitSibleyZ d ≠ ⊥)
    (hXne : (feitSibleyX d chars).Nonempty)
    (_ : (feitSibleyY d chars).Nonempty) :
    (∀ eta : feitSibleyY d chars,
      degree (eta : ClassFunction d.H) =
        (Nat.card d.D : Complex)) ∧
    ∃ chi1 : feitSibleyX d chars, ∃ a : Nat,
      1 < a ∧
      degree (chi1 : ClassFunction d.H) =
        (a : Complex) * (Nat.card d.D : Complex) ∧
      ∀ chi : feitSibleyX d chars, ∃ ai : Nat,
        degree (chi : ClassFunction d.H) =
          (ai : Complex) * degree (chi1 : ClassFunction d.H) := by
  classical
  rcases hp with ⟨p, hpprime, hpQ1⟩
  let : Fact p.Prime := ⟨hpprime⟩
  let : d.Q1.Normal := d.Q1_normal
  have hZnormal : (feitSibleyZ d).Normal := by
    dsimp [feitSibleyZ, feitSibleyQ1derivedH, feitSibleyCenterQ1H]
    infer_instance
  have hZleCenter :
      feitSibleyZ d ≤ feitSibleyCenterQ1H d :=
    inf_le_right
  have hQindex :
      d.Q.relIndex (⊤ : Subgroup d.H) = Nat.card d.D :=
    feitSibley_Q_relIndex_top_eq_card_D_appendixIV d
  have hYdegree :
      ∀ eta : feitSibleyY d chars,
        degree (eta : ClassFunction d.H) =
          (Nat.card d.D : Complex) := by
    intro eta
    have hetaData :=
      Finset.mem_filter.mp eta.property
    rw [d.degree_eq_relIndex_of_exceptional_derived_kernel
      chars hchars (eta : ClassFunction d.H) hetaData.1 hetaData.2]
    rw [hQindex]
  let Xbase : Finset (ClassFunction d.H) :=
    feitSibleyX d chars ∩
      feitSibleySker d chars (feitSibleySderivedH d)
  have hXbaseMem : ∀ chi : ClassFunction d.H, chi ∈ Xbase ↔
      (chi ∈ chars ∧
          ¬ subgroupInKernel' chi (feitSibleyZ d)) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d) := by
    intro chi
    simp only [Xbase, feitSibleyX, feitSibleySnonker,
      feitSibleySker, Finset.mem_inter, Finset.mem_filter]
  have hXbaseNe : Xbase.Nonempty := by
    rcases hXne with ⟨psi, hpsiX⟩
    have hpsiData := Finset.mem_filter.mp hpsiX
    rcases feitSibley_step3_exists_base_companion_core
        d chars hchars (feitSibleyZ d) hZnormal hZleCenter
          hXbaseMem psi hpsiData.1 hpsiData.2 with
      ⟨chi, hchiXbase, _n, _hdegree⟩
    exact ⟨chi, hchiXbase⟩
  rcases feitSibley_step3_base_degree_data_core
      d chars hchars p hpprime hpQ1 (feitSibleyZ d)
        hZne hZnormal hZleCenter hXbaseMem with
    ⟨deg, hdeg, hpower, _hprefix⟩
  let : Nonempty Xbase := hXbaseNe.to_subtype
  obtain ⟨chi0, _hchi0Univ, hchi0min⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Xbase) deg
      Finset.univ_nonempty
  let chi1 : feitSibleyX d chars :=
    ⟨(chi0 : ClassFunction d.H),
      (Finset.mem_inter.mp chi0.property).1⟩
  rcases hpower chi0 with ⟨k0, hk0⟩
  have hchi1Degree :
      degree (chi1 : ClassFunction d.H) =
        ((p ^ k0 : Nat) : Complex) *
          (Nat.card d.D : Complex) := by
    rw [(hdeg chi0).2, hk0]
    push_cast
    ring
  have hdivX :
      ∀ chi : feitSibleyX d chars, ∃ ai : Nat,
        degree (chi : ClassFunction d.H) =
          (ai : Complex) * degree (chi1 : ClassFunction d.H) := by
    intro chi
    have hchiData := Finset.mem_filter.mp chi.property
    rcases feitSibley_step3_exists_base_companion_core
        d chars hchars (feitSibleyZ d) hZnormal hZleCenter
          hXbaseMem (chi : ClassFunction d.H)
            hchiData.1 hchiData.2 with
      ⟨theta, hthetaXbase, n, hchiDegree⟩
    let thetaX : Xbase := ⟨theta, hthetaXbase⟩
    rcases hpower thetaX with ⟨k, hk⟩
    have hdegLe : deg chi0 ≤ deg thetaX :=
      hchi0min thetaX (Finset.mem_univ _)
    have hpowLe : p ^ k0 ≤ p ^ k := by
      apply Nat.le_of_mul_le_mul_left
        (by simpa [hk0, hk] using hdegLe)
      simpa [Nat.card_eq_fintype_card] using
        (Nat.card_pos (α := d.D))
    have hkle : k0 ≤ k :=
      (Nat.pow_le_pow_iff_right hpprime.one_lt).mp hpowLe
    rcases Nat.exists_eq_add_of_le hkle with ⟨c, hkc⟩
    have hthetaMultiple :
        degree theta =
          ((p ^ c : Nat) : Complex) *
            degree (chi1 : ClassFunction d.H) := by
      rw [(hdeg thetaX).2, (hdeg chi0).2, hk, hk0,
        hkc, Nat.pow_add]
      push_cast
      ring
    refine ⟨n * p ^ c, ?_⟩
    rw [hchiDegree, hthetaMultiple]
    push_cast
    ring
  have ha : 1 < p ^ k0 := by
    by_contra hnot
    have hapos : 0 < p ^ k0 := pow_pos hpprime.pos k0
    have haone : p ^ k0 = 1 := by omega
    have hchi1RelIndex :
        degree (chi1 : ClassFunction d.H) =
          (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
      calc
        degree (chi1 : ClassFunction d.H) =
            (Nat.card d.D : Complex) := by
          simpa [haone] using hchi1Degree
        _ = (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
          rw [hQindex]
    have hchi1Chars :
        (chi1 : ClassFunction d.H) ∈ chars :=
      (Finset.mem_filter.mp chi1.property).1
    have hchi1Kernel :
        subgroupInKernel' (chi1 : ClassFunction d.H)
          (feitSibleyQderivedH d) :=
      d.exceptional_derived_kernel_of_degree_eq_relIndex
        chars hchars (chi1 : ClassFunction d.H)
          hchi1Chars hchi1RelIndex
    have hQderived :
        feitSibleyQderivedH d =
          feitSibleySderivedH d ⊔ feitSibleyQ1derivedH d := by
      simpa [feitSibleyQderivedH, feitSibleySderivedH,
        feitSibleyQ1derivedH] using d.map_derivedSubgroup_Q_eq_sup
    have hZleQderived :
        feitSibleyZ d ≤ feitSibleyQderivedH d := by
      rw [hQderived]
      exact inf_le_left.trans le_sup_right
    exact (Finset.mem_filter.mp chi1.property).2
      (subgroupInKernel'_mono_appendixIV hZleQderived hchi1Kernel)
  exact ⟨hYdegree, chi1, p ^ k0, ha, hchi1Degree, hdivX⟩

private theorem feitSibley_step5_cross_orthogonality_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D))
    (hstep4 : feitSibleyStep4Data d chars) :
    feitSibleyStep5Data d chars := by
  classical
  rcases hstep4 with
    ⟨_hZne, _hZnormal, _hZle, hXY, _hcohX, _hcohY,
      _hXne, _hYne, _hYdegree, _hdegreeData⟩
  unfold feitSibleyStep5Data
  intro TX TY hTX hTY
  unfold feitSibleyCrossOrthogonal
  intro chi eta
  have hXsub : feitSibleyX d chars ⊆ chars := by
    intro theta htheta
    exact (Finset.mem_filter.mp htheta).1
  have hYsub : feitSibleyY d chars ⊆ chars := by
    intro theta htheta
    exact (Finset.mem_filter.mp htheta).1
  have hconjNotKernel (theta : ClassFunction d.H)
      (A : Subgroup d.H)
      (hnot : ¬ subgroupInKernel' theta A) :
      ¬ subgroupInKernel' (conjugateCharacter theta) A := by
    intro hbarKernel
    apply hnot
    have hdouble :=
      Section6.subgroupInKernel'_conjugateCharacter
        (conjugateCharacter theta) hbarKernel
    have hcc :
        conjugateCharacter (conjugateCharacter theta) = theta := by
      ext x
      simp [conjugateCharacter]
    simpa [hcc] using hdouble
  have hbarChars (theta : ClassFunction d.H) (htheta : theta ∈ chars) :
      conjugateCharacter theta ∈ chars := by
    let : d.Q.Normal := d.Q_normal
    rcases (lemma_2_a d chars hchars theta).mp htheta with
      ⟨phi, hphiIrr, hphiNotKernel, hind⟩
    apply (lemma_2_a d chars hchars (conjugateCharacter theta)).mpr
    refine ⟨conjugateCharacter phi,
      isIrreducibleCharacterOnGroup_conjugateCharacter hphiIrr, ?_, ?_⟩
    · intro hbarKernel
      apply hphiNotKernel
      have hdouble :=
        Section6.subgroupInKernel'_conjugateCharacter
          (conjugateCharacter phi) hbarKernel
      have hcc : conjugateCharacter (conjugateCharacter phi) = phi := by
        ext q
        simp [conjugateCharacter]
      simpa [hcc] using hdouble
    · calc
        inducedCF d.Q (conjugateCharacter phi) =
            conjugateCharacter (inducedCF d.Q phi) :=
          (conjugateCharacter_inducedCF d.Q phi).symm
        _ = conjugateCharacter theta := by rw [hind]
  have hchiChars : (chi : ClassFunction d.H) ∈ chars :=
    hXsub chi.property
  have hetaChars : (eta : ClassFunction d.H) ∈ chars :=
    hYsub eta.property
  have hbarChiX :
      conjugateCharacter (chi : ClassFunction d.H) ∈
        feitSibleyX d chars := by
    apply Finset.mem_filter.mpr
    exact ⟨hbarChars (chi : ClassFunction d.H) hchiChars,
      hconjNotKernel (chi : ClassFunction d.H) (feitSibleyZ d)
        (Finset.mem_filter.mp chi.property).2⟩
  have hbarEtaY :
      conjugateCharacter (eta : ClassFunction d.H) ∈
        feitSibleyY d chars := by
    apply Finset.mem_filter.mpr
    exact ⟨hbarChars (eta : ClassFunction d.H) hetaChars,
      Section6.subgroupInKernel'_conjugateCharacter
        (eta : ClassFunction d.H)
        (Finset.mem_filter.mp eta.property).2⟩
  let chibar : feitSibleyX d chars :=
    ⟨conjugateCharacter (chi : ClassFunction d.H), hbarChiX⟩
  let etabar : feitSibleyY d chars :=
    ⟨conjugateCharacter (eta : ClassFunction d.H), hbarEtaY⟩
  have hchiBarNe :
      (chibar : ClassFunction d.H) ≠ (chi : ClassFunction d.H) := by
    simpa [chibar] using
      lemma_2_c d chars hchars hDodd
        (chi : ClassFunction d.H) hchiChars
  have hetaBarNe :
      (etabar : ClassFunction d.H) ≠ (eta : ClassFunction d.H) := by
    simpa [etabar] using
      lemma_2_c d chars hchars hDodd
        (eta : ClassFunction d.H) hetaChars
  have hirrX (theta : feitSibleyX d chars) :
      IsIrreducibleCharacterOnGroup (theta : ClassFunction d.H) :=
    ((hchars (theta : ClassFunction d.H)).mp (hXsub theta.property)).1
  have hirrY (theta : feitSibleyY d chars) :
      IsIrreducibleCharacterOnGroup (theta : ClassFunction d.H) :=
    ((hchars (theta : ClassFunction d.H)).mp (hYsub theta.property)).1
  have hsignedX (theta : feitSibleyX d chars) :
      Section3.IsSignedIrreducibleCharacter
        (TX (theta : ClassFunction d.H)) := by
    apply Section5.signed_irreducible_of_virtual_norm_one_pf59
    · exact hTX.2.1 (theta : ClassFunction d.H)
        (integerSpan_of_mem _ theta.property)
    · calc
        scalarProduct G (TX (theta : ClassFunction d.H))
            (TX (theta : ClassFunction d.H)) =
            scalarProduct d.H (theta : ClassFunction d.H)
              (theta : ClassFunction d.H) :=
          Section5.isCFLinearIsometryOnSpan_apply_of_mem
            hTX.1 theta.property theta.property
        _ = 1 :=
          Section1.scalarProduct_irreducibleCharacter_self (hirrX theta)
  have hsignedY (theta : feitSibleyY d chars) :
      Section3.IsSignedIrreducibleCharacter
        (TY (theta : ClassFunction d.H)) := by
    apply Section5.signed_irreducible_of_virtual_norm_one_pf59
    · exact hTY.2.1 (theta : ClassFunction d.H)
        (integerSpan_of_mem _ theta.property)
    · calc
        scalarProduct G (TY (theta : ClassFunction d.H))
            (TY (theta : ClassFunction d.H)) =
            scalarProduct d.H (theta : ClassFunction d.H)
              (theta : ClassFunction d.H) :=
          Section5.isCFLinearIsometryOnSpan_apply_of_mem
            hTY.1 theta.property theta.property
        _ = 1 :=
          Section1.scalarProduct_irreducibleCharacter_self (hirrY theta)
  have horthX :
      scalarProduct G (TX (chi : ClassFunction d.H))
        (TX (chibar : ClassFunction d.H)) = 0 := by
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
      hTX.1 chi.property chibar.property]
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hirrX chi) (hirrX chibar) hchiBarNe.symm
  have horthY :
      scalarProduct G (TY (eta : ClassFunction d.H))
        (TY (etabar : ClassFunction d.H)) = 0 := by
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
      hTY.1 eta.property etabar.property]
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hirrY eta) (hirrY etabar) hetaBarNe.symm
  have hdegChiBar :
      degree (chibar : ClassFunction d.H) =
        degree (chi : ClassFunction d.H) := by
    simpa [chibar] using
      Section5.degree_conjugateCharacter_eq_of_isCharacter
        (isCharacter_of_isIrreducibleCharacterOnGroup (hirrX chi))
  have hdegEtaBar :
      degree (etabar : ClassFunction d.H) =
        degree (eta : ClassFunction d.H) := by
    simpa [etabar] using
      Section5.degree_conjugateCharacter_eq_of_isCharacter
        (isCharacter_of_isIrreducibleCharacterOnGroup (hirrY eta))
  let diffX : ClassFunction d.H :=
    (chi : ClassFunction d.H) - (chibar : ClassFunction d.H)
  let diffY : ClassFunction d.H :=
    (eta : ClassFunction d.H) - (etabar : ClassFunction d.H)
  have hdegDiffX : degree diffX = 0 := by
    change (chi : ClassFunction d.H) 1 - (chibar : ClassFunction d.H) 1 = 0
    have h := hdegChiBar
    change (chibar : ClassFunction d.H) 1 = (chi : ClassFunction d.H) 1 at h
    rw [h]
    ring
  have hdegDiffY : degree diffY = 0 := by
    change (eta : ClassFunction d.H) 1 - (etabar : ClassFunction d.H) 1 = 0
    have h := hdegEtaBar
    change (etabar : ClassFunction d.H) 1 = (eta : ClassFunction d.H) 1 at h
    rw [h]
    ring
  have hspanX :
      integerSpanOn (feitSibleyX d chars) puncturedSet diffX := by
    refine ⟨?_, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero diffX).2
      hdegDiffX⟩
    exact integerSpan_sub
      (integerSpan_of_mem _ chi.property)
      (integerSpan_of_mem _ chibar.property)
  have hspanY :
      integerSpanOn (feitSibleyY d chars) puncturedSet diffY := by
    refine ⟨?_, (Section5.supportedOn_puncturedSet_iff_degree_eq_zero diffY).2
      hdegDiffY⟩
    exact integerSpan_sub
      (integerSpan_of_mem _ eta.property)
      (integerSpan_of_mem _ etabar.property)
  have hTXdiff :
      TX diffX = Section1.inducedCFLinear d.H diffX :=
    hTX.2.2 diffX hspanX
  have hTYdiff :
      TY diffY = Section1.inducedCFLinear d.H diffY :=
    hTY.2.2 diffY hspanY
  have hsourceCross (x : feitSibleyX d chars)
      (y : feitSibleyY d chars) :
      scalarProduct d.H (x : ClassFunction d.H)
        (y : ClassFunction d.H) = 0 := by
    have hne :
        (x : ClassFunction d.H) ≠ (y : ClassFunction d.H) := by
      intro heq
      have hxY : (x : ClassFunction d.H) ∈ feitSibleyY d chars := by
        rw [heq]
        exact y.property
      exact (Finset.disjoint_left.mp hXY x.property) hxY
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hirrX x) (hirrY y) hne
  have scalarProduct_sub_left
      (a b c : ClassFunction d.H) :
      scalarProduct d.H (a - b) c =
        scalarProduct d.H a c - scalarProduct d.H b c := by
    calc
      scalarProduct d.H (a - b) c =
          scalarProduct d.H (a + (-1 : Complex) • b) c := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
      _ = scalarProduct d.H a c +
          scalarProduct d.H ((-1 : Complex) • b) c := by
            rw [Section1.scalarProduct_add_left]
      _ = scalarProduct d.H a c - scalarProduct d.H b c := by
            rw [Section1.scalarProduct_smul_left]
            simp [sub_eq_add_neg]
  have scalarProduct_sub_right
      (a b c : ClassFunction d.H) :
      scalarProduct d.H a (b - c) =
        scalarProduct d.H a b - scalarProduct d.H a c := by
    simp [Section1.scalarProduct, mul_sub, Finset.sum_sub_distrib]
  have hsourceDiff :
      scalarProduct d.H diffX diffY = 0 := by
    rw [show diffX =
      (chi : ClassFunction d.H) - (chibar : ClassFunction d.H) from rfl]
    rw [show diffY =
      (eta : ClassFunction d.H) - (etabar : ClassFunction d.H) from rfl]
    rw [scalarProduct_sub_left, scalarProduct_sub_right,
      scalarProduct_sub_right]
    rw [hsourceCross chi eta, hsourceCross chi etabar,
      hsourceCross chibar eta, hsourceCross chibar etabar]
    ring
  rcases lemma_2_b d chars hchars with ⟨hisoChars, _htargetChars⟩
  have hindDiff :
      scalarProduct G (Section1.inducedCFLinear d.H diffX)
        (Section1.inducedCFLinear d.H diffY) = 0 := by
    rw [hisoChars diffX diffY
      (Section5.integerSpanOn_mono hXsub hspanX)
      (Section5.integerSpanOn_mono hYsub hspanY)]
    exact hsourceDiff
  have hmixed :
      scalarProduct G
        (TX (chi : ClassFunction d.H) -
          TX (chibar : ClassFunction d.H))
        (TY (eta : ClassFunction d.H) -
          TY (etabar : ClassFunction d.H)) = 0 := by
    rw [← map_sub, ← map_sub]
    change scalarProduct G (TX diffX) (TY diffY) = 0
    rw [hTXdiff, hTYdiff]
    exact hindDiff
  have hdegTXdiff :
      degree
        (TX (chi : ClassFunction d.H) -
          TX (chibar : ClassFunction d.H)) = 0 := by
    rw [← map_sub]
    change degree (TX diffX) = 0
    rw [hTXdiff]
    change degree (inducedCF d.H diffX) = 0
    rw [degree_inducedClassFunction d.H diffX, hdegDiffX]
    simp
  have hdegTYdiff :
      degree
        (TY (eta : ClassFunction d.H) -
          TY (etabar : ClassFunction d.H)) = 0 := by
    rw [← map_sub]
    change degree (TY diffY) = 0
    rw [hTYdiff]
    change degree (inducedCF d.H diffY) = 0
    rw [degree_inducedClassFunction d.H diffY, hdegDiffY]
    simp
  have hpair := Section4.proposition_4_1
    (α := TX (chi : ClassFunction d.H))
    (β := TX (chibar : ClassFunction d.H))
    (γ := TY (eta : ClassFunction d.H))
    (δ := TY (etabar : ClassFunction d.H))
    (u := (1 : Real)) (v := (1 : Real))
    (hsignedX chi) (hsignedX chibar)
    (hsignedY eta) (hsignedY etabar)
    (by norm_num) (by norm_num) horthX horthY
    (by simpa using hmixed) hdegTXdiff
    (by simpa using hdegTYdiff)
  exact hpair.2.1

private theorem appendixIV_unionImage_agreesOnIntegerSpanOn_of_split
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {W1 : Subgroup L}
    {U : Finset (ClassFunction L)}
    {Tnew T : ClassFunction L →ₗ[Complex] ClassFunction G}
    {eta1 : ClassFunction L} {Ycf : ClassFunction G}
    {img : U → ClassFunction G}
    (hsplit : ∀ eta : U,
      T ((eta : ClassFunction L) -
          (degree (eta : ClassFunction L) /
            (Nat.card W1 : Complex)) • eta1) =
        img eta -
          (degree (eta : ClassFunction L) /
            (Nat.card W1 : Complex)) • Ycf)
    (hTnew : ∀ eta : U,
      Tnew (eta : ClassFunction L) = img eta) :
    agreesOnIntegerSpanOn U puncturedSet T Tnew := by
  classical
  intro chi hchi
  rcases hchi with ⟨⟨coeff, hcoeff⟩, hchiOn⟩
  let mu : U → ClassFunction L := fun eta => (eta : ClassFunction L)
  let ratio : U → Complex := fun eta =>
    degree (eta : ClassFunction L) / (Nat.card W1 : Complex)
  let gen : U → ClassFunction L := fun eta =>
    (eta : ClassFunction L) - ratio eta • eta1
  let s : Complex := ∑ eta : U, (coeff eta : Complex) * ratio eta
  have hcardNe : (Nat.card W1 : Complex) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := W1)).ne'
  have hdegreeChi : degree chi = 0 :=
    (supportedOn_puncturedSet_iff_degree_eq_zero chi).1 hchiOn
  have hdegreeEval :
      degree chi =
        ∑ eta : U,
          (coeff eta : Complex) * degree (eta : ClassFunction L) := by
    change chi 1 =
      ∑ eta : U, (coeff eta : Complex) * (eta : ClassFunction L) 1
    rw [hcoeff, evalCoeff]
    simp
  have hfactor :
      (∑ eta : U,
          (coeff eta : Complex) * degree (eta : ClassFunction L)) =
        s * (Nat.card W1 : Complex) := by
    calc
      (∑ eta : U,
          (coeff eta : Complex) * degree (eta : ClassFunction L)) =
          ∑ eta : U,
            (coeff eta : Complex) * ratio eta *
              (Nat.card W1 : Complex) := by
            refine Finset.sum_congr rfl ?_
            intro eta _heta
            dsimp [ratio]
            field_simp [hcardNe]
      _ = s * (Nat.card W1 : Complex) := by
            simp [s, Finset.sum_mul, mul_assoc]
  have hs : s = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_right hcardNe
    rw [← hfactor, ← hdegreeEval, hdegreeChi]
  have hsourceEval : evalCoeff gen coeff = chi - s • eta1 := by
    rw [hcoeff]
    ext g
    simp [evalCoeff, gen, ratio, s, Pi.smul_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib,
      mul_comm, mul_left_comm, sub_eq_add_neg]
    rw [Finset.mul_sum]
  have htargetEval :
      evalCoeff (fun eta : U => T (gen eta)) coeff =
        evalCoeff img coeff - s • Ycf := by
    have hsplitEval :
        evalCoeff (fun eta : U => T (gen eta)) coeff =
          evalCoeff
            (fun eta : U => img eta - ratio eta • Ycf) coeff := by
      congr 1
      funext eta
      exact hsplit eta
    rw [hsplitEval]
    ext g
    simp [evalCoeff, ratio, s, Pi.smul_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib,
      mul_comm, mul_left_comm, sub_eq_add_neg]
    rw [Finset.mul_sum]
  have himgEval : evalCoeff img coeff = T chi := by
    have heq : evalCoeff img coeff - s • Ycf = T (chi - s • eta1) := by
      calc
        evalCoeff img coeff - s • Ycf =
            evalCoeff (fun eta : U => T (gen eta)) coeff :=
          htargetEval.symm
        _ = T (evalCoeff gen coeff) :=
          (map_evalCoeff T gen coeff).symm
        _ = T (chi - s • eta1) := by rw [hsourceEval]
    rw [hs, zero_smul, sub_zero] at heq
    simpa using heq
  calc
    Tnew chi = Tnew (evalCoeff mu coeff) := by rw [hcoeff]
    _ = evalCoeff (fun eta : U => Tnew (eta : ClassFunction L)) coeff :=
      map_evalCoeff Tnew mu coeff
    _ = evalCoeff img coeff := by
      congr 1
      funext eta
      exact hTnew eta
    _ = T chi := himgEval

private theorem appendixIV_step6_norm_cases
    (a m : Nat) (x r : Int) (ha : 1 < a) (hm : 2 ≤ m)
    (hr : 0 ≤ r)
    (hnorm : (1 : Int) + (a : Int) ^ 2 =
      r + (a : Int) ^ 2 *
        ((x - 1) ^ 2 + ((m : Int) - 1) * x ^ 2)) :
    (x = 0 ∨ (x = 1 ∧ m = 2)) ∧ r = 1 := by
  have ha2 : (2 : Int) ≤ (a : Int) ^ 2 := by
    have haI : (2 : Int) ≤ a := by exact_mod_cast ha
    nlinarith
  have hmI : (1 : Int) ≤ (m : Int) - 1 := by omega
  let q : Int :=
    (x - 1) ^ 2 + ((m : Int) - 1) * x ^ 2
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hqle : q ≤ 1 := by
    nlinarith
  have hxsq : x ^ 2 ≤ 1 := by
    dsimp [q] at hqle
    nlinarith [sq_nonneg (x - 1)]
  have hxmsq : (x - 1) ^ 2 ≤ 1 := by
    dsimp [q] at hqle
    nlinarith [sq_nonneg x]
  have hxlo : 0 ≤ x := by nlinarith [sq_nonneg (x - 1)]
  have hxhi : x ≤ 1 := by nlinarith [sq_nonneg x]
  have hx : x = 0 ∨ x = 1 := by omega
  rcases hx with rfl | rfl
  · constructor
    · exact Or.inl rfl
    · norm_num [q] at hnorm ⊢
      nlinarith
  · have hmEq : m = 2 := by
      dsimp [q] at hqle
      norm_num at hqle
      omega
    constructor
    · exact Or.inr ⟨rfl, hmEq⟩
    · subst hmEq
      norm_num [q] at hnorm ⊢
      nlinarith

set_option maxHeartbeats 1600000 in
private theorem feitSibley_step6_union_coherence_of_normalized_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (X Y U : Finset (ClassFunction d.H))
    (hXmem : ∀ theta : ClassFunction d.H,
      theta ∈ X ↔ theta ∈ feitSibleyX d chars)
    (hYmem : ∀ theta : ClassFunction d.H,
      theta ∈ Y ↔ theta ∈ feitSibleyY d chars)
    (hUmem : ∀ theta : ClassFunction d.H,
      theta ∈ U ↔ theta ∈ X ∨ theta ∈ Y)
    (TX : ClassFunction d.H →ₗ[Complex] ClassFunction G)
    (EY : Y → ClassFunction G)
    (chi1 : X) (eta1 : Y) (a : Nat)
    (hXY : Disjoint X Y)
    (hXnonemptyOn : integerSpanOnNonempty X puncturedSet)
    (hYdegree : ∀ eta : Y,
      degree (eta : ClassFunction d.H) = (Nat.card d.D : Complex))
    (hdegree : degree (chi1 : ClassFunction d.H) =
      (a : Complex) * degree (eta1 : ClassFunction d.H))
    (hdivX : ∀ chi : X, ∃ ai : Nat,
      degree (chi : ClassFunction d.H) =
        (ai : Complex) * degree (chi1 : ClassFunction d.H))
    (hTX : feitSibleyExtensionOn d X TX)
    (hEYvirt : ∀ eta : Y,
      Theory.Character.IsVirtualCharacter (EY eta))
    (hEYself : ∀ eta : Y, scalarProduct G (EY eta) (EY eta) = 1)
    (hEYoff : ∀ eta zeta : Y, eta ≠ zeta →
      scalarProduct G (EY eta) (EY zeta) = 0)
    (hcross : ∀ chi : X, ∀ eta : Y,
        scalarProduct G (TX (chi : ClassFunction d.H)) (EY eta) = 0)
    (v : ClassFunction G) (hvvirt : Theory.Character.IsVirtualCharacter v)
    (hvSelf : scalarProduct G v v = 1)
    (hvorth : ∀ eta : Y,
      scalarProduct G v (EY eta) = 0)
    (hbridge :
      Section1.inducedCF d.H
          ((chi1 : ClassFunction d.H) -
            (a : Complex) • (eta1 : ClassFunction d.H)) =
        v - (a : Complex) • EY eta1)
    (hEYdiff : ∀ eta : Y,
      Section1.inducedCF d.H
          ((eta : ClassFunction d.H) - (eta1 : ClassFunction d.H)) =
        EY eta - EY eta1) :
    IsCoherentTriple puncturedSet
      U (Section1.inducedCFLinear d.H) := by
  classical
  have hXsub : X ⊆ chars := by
    intro chi hchi
    exact (Finset.mem_filter.mp ((hXmem chi).mp hchi)).1
  have hYsub : Y ⊆ chars := by
    intro eta heta
    exact (Finset.mem_filter.mp ((hYmem eta).mp heta)).1
  have hUsub : U ⊆ chars := by
    intro theta htheta
    rcases (hUmem theta).mp htheta with hthetaX | hthetaY
    · exact hXsub hthetaX
    · exact hYsub hthetaY
  have hirrU (theta : U) :
      IsIrreducibleCharacterOnGroup (theta : ClassFunction d.H) :=
    ((hchars (theta : ClassFunction d.H)).mp (hUsub theta.property)).1
  have hirrX (chi : X) :
      IsIrreducibleCharacterOnGroup (chi : ClassFunction d.H) :=
    ((hchars (chi : ClassFunction d.H)).mp (hXsub chi.property)).1
  have hirrY (eta : Y) :
      IsIrreducibleCharacterOnGroup (eta : ClassFunction d.H) :=
    ((hchars (eta : ClassFunction d.H)).mp (hYsub eta.property)).1
  let ai : X → Nat := fun chi => Classical.choose (hdivX chi)
  have hai (chi : X) :
      degree (chi : ClassFunction d.H) =
        (ai chi : Complex) * degree (chi1 : ClassFunction d.H) :=
    Classical.choose_spec (hdivX chi)
  have hdegreeChi1Ne : degree (chi1 : ClassFunction d.H) ≠ 0 :=
    Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup
      (chi1 : ClassFunction d.H) (hirrX chi1)
  have hai1 : ai chi1 = 1 := by
    have hzero : ((ai chi1 : Complex) - 1) *
        degree (chi1 : ClassFunction d.H) = 0 := by
      rw [sub_mul, ← hai chi1]
      ring
    have hcast : (ai chi1 : Complex) = 1 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hdegreeChi1Ne)
    exact_mod_cast hcast
  have hTXgram (chi psi : X) :
      scalarProduct G (TX (chi : ClassFunction d.H))
          (TX (psi : ClassFunction d.H)) =
        if chi = psi then 1 else 0 := by
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
      hTX.1 chi.property psi.property]
    split_ifs with heq
    · subst psi
      exact Section1.scalarProduct_irreducibleCharacter_self (hirrX chi)
    · exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hirrX chi) (hirrX psi) (by
          intro hval
          exact heq (Subtype.ext hval))
  have hTXvirt (chi : X) :
      Theory.Character.IsVirtualCharacter
        (TX (chi : ClassFunction d.H)) :=
    hTX.2.1 (chi : ClassFunction d.H)
      (integerSpan_of_mem X chi.property)
  have hsourceCross (chi : X) (eta : Y) :
      scalarProduct d.H (chi : ClassFunction d.H)
        (eta : ClassFunction d.H) = 0 := by
    have hne : (chi : ClassFunction d.H) ≠
        (eta : ClassFunction d.H) := by
      intro heq
      exact (Finset.disjoint_left.mp hXY chi.property)
        (heq ▸ eta.property)
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hirrX chi) (hirrY eta) hne
  have hXdiff (chi : X) :
      Section1.inducedCF d.H
          ((chi : ClassFunction d.H) -
            (ai chi : Complex) • (chi1 : ClassFunction d.H)) =
        TX (chi : ClassFunction d.H) -
          (ai chi : Complex) • TX (chi1 : ClassFunction d.H) := by
    let diff : ClassFunction d.H :=
      (chi : ClassFunction d.H) -
        (ai chi : Complex) • (chi1 : ClassFunction d.H)
    have hdiffDegree : degree diff = 0 := by
      change degree (chi : ClassFunction d.H) -
        (ai chi : Complex) * degree (chi1 : ClassFunction d.H) = 0
      rw [hai chi]
      ring
    have hdiffOn : integerSpanOn X puncturedSet diff := by
      refine ⟨integerSpan_sub
        (integerSpan_of_mem X chi.property) ?_,
          (supportedOn_puncturedSet_iff_degree_eq_zero diff).2 hdiffDegree⟩
      simpa using integerSpan_zsmul (ai chi : Int)
        (integerSpan_of_mem X chi1.property)
    have hagree := hTX.2.2 diff hdiffOn
    rw [map_sub, map_smul] at hagree
    simpa [diff, Section1.inducedCFLinear_apply] using hagree.symm
  let sourceBridge : ClassFunction d.H :=
    (chi1 : ClassFunction d.H) -
      (a : Complex) • (eta1 : ClassFunction d.H)
  have hsourceBridgeDegree : degree sourceBridge = 0 := by
    change degree (chi1 : ClassFunction d.H) -
      (a : Complex) * degree (eta1 : ClassFunction d.H) = 0
    rw [hdegree]
    ring
  have hsourceBridgeOn : integerSpanOn chars puncturedSet sourceBridge := by
    refine ⟨integerSpan_sub
      (integerSpan_of_mem chars (hXsub chi1.property)) ?_,
        (supportedOn_puncturedSet_iff_degree_eq_zero sourceBridge).2
          hsourceBridgeDegree⟩
    simpa using integerSpan_zsmul (a : Int)
      (integerSpan_of_mem chars (hYsub eta1.property))
  have hbridgeLinear :
      Section1.inducedCFLinear d.H sourceBridge =
        v - (a : Complex) • EY eta1 := by
    simpa [sourceBridge, Section1.inducedCFLinear_apply] using hbridge
  rcases lemma_2_b d chars hchars with ⟨hIndIso, _hIndTarget⟩
  let u : ClassFunction G := v - TX (chi1 : ClassFunction d.H)
  let c : Complex :=
    scalarProduct G (TX (chi1 : ClassFunction d.H)) v - 1
  have hTXu (chi : X) :
      scalarProduct G (TX (chi : ClassFunction d.H)) u =
        (ai chi : Complex) * c := by
    let diff : ClassFunction d.H :=
      (chi : ClassFunction d.H) -
        (ai chi : Complex) • (chi1 : ClassFunction d.H)
    have hdiffDegree : degree diff = 0 := by
      change degree (chi : ClassFunction d.H) -
        (ai chi : Complex) * degree (chi1 : ClassFunction d.H) = 0
      rw [hai chi]
      ring
    have hdiffOn : integerSpanOn chars puncturedSet diff := by
      refine ⟨integerSpan_sub
        (integerSpan_of_mem chars (hXsub chi.property)) ?_,
          (supportedOn_puncturedSet_iff_degree_eq_zero diff).2 hdiffDegree⟩
      simpa using integerSpan_zsmul (ai chi : Int)
        (integerSpan_of_mem chars (hXsub chi1.property))
    have hpair :
        scalarProduct G
            (TX (chi : ClassFunction d.H) -
              (ai chi : Complex) • TX (chi1 : ClassFunction d.H))
            (v - (a : Complex) • EY eta1) =
          scalarProduct d.H diff sourceBridge := by
      calc
        _ = scalarProduct G
            (Section1.inducedCFLinear d.H diff)
            (Section1.inducedCFLinear d.H sourceBridge) := by
          rw [← hXdiff chi, ← hbridge]
          rfl
        _ = scalarProduct d.H diff sourceBridge :=
          hIndIso diff sourceBridge hdiffOn hsourceBridgeOn
    have hrel :
        scalarProduct G (TX (chi : ClassFunction d.H)) v -
            (ai chi : Complex) *
              scalarProduct G (TX (chi1 : ClassFunction d.H)) v =
          (if chi = chi1 then 1 else 0) - (ai chi : Complex) := by
      rw [show diff = (chi : ClassFunction d.H) -
        (ai chi : Complex) • (chi1 : ClassFunction d.H) from rfl] at hpair
      rw [show sourceBridge = (chi1 : ClassFunction d.H) -
        (a : Complex) • (eta1 : ClassFunction d.H) from rfl] at hpair
      simp only [Section5.scalarProduct_sub_left,
        Section5.scalarProduct_sub_right,
        Section1.scalarProduct_smul_left,
        Section1.scalarProduct_smul_right] at hpair
      rw [hcross chi eta1, hcross chi1 eta1,
        hsourceCross chi eta1, hsourceCross chi1 eta1,
        Section1.scalarProduct_irreducibleCharacter_self (hirrX chi1)] at hpair
      have hsourceXX :
          scalarProduct d.H (chi : ClassFunction d.H)
              (chi1 : ClassFunction d.H) =
            if chi = chi1 then 1 else 0 := by
        split_ifs with heq
        · subst chi
          exact Section1.scalarProduct_irreducibleCharacter_self (hirrX chi1)
        · exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
            (hirrX chi) (hirrX chi1) (by
              intro hval
              exact heq (Subtype.ext hval))
      rw [hsourceXX] at hpair
      simpa using hpair
    rw [show u = v - TX (chi1 : ClassFunction d.H) from rfl,
      Section5.scalarProduct_sub_right, hTXgram chi chi1]
    dsimp [c]
    split_ifs with heq
    · subst chi
      rw [hai1] at hrel ⊢
      norm_num at hrel ⊢
    · rw [if_neg heq] at hrel
      linear_combination hrel
  have huTX (chi : X) :
      scalarProduct G u (TX (chi : ClassFunction d.H)) =
        (ai chi : Complex) * star c := by
    have hstar := Section1.scalarProduct_star_swap
      (G := G) u (TX (chi : ClassFunction d.H))
    rw [hTXu chi] at hstar
    simpa [map_mul, mul_comm] using hstar.symm
  have huu : scalarProduct G u u = -(c + star c) := by
    rw [show u = v - TX (chi1 : ClassFunction d.H) from rfl]
    simp only [Section5.scalarProduct_sub_left,
      Section5.scalarProduct_sub_right]
    have hTX1v :
        scalarProduct G (TX (chi1 : ClassFunction d.H)) v = c + 1 := by
      simp [c]
    have hvTX1 :
        scalarProduct G v (TX (chi1 : ClassFunction d.H)) = star c + 1 := by
      have hstar := Section1.scalarProduct_star_swap
        (G := G) v (TX (chi1 : ClassFunction d.H))
      rw [hTX1v] at hstar
      simpa using hstar.symm
    rw [hvSelf, hTXgram chi1 chi1, hTX1v, hvTX1]
    simp
    ring
  let imgX : X → ClassFunction G := fun chi =>
    TX (chi : ClassFunction d.H) + (ai chi : Complex) • u
  have himgXchi1 : imgX chi1 = v := by
    rw [show imgX chi1 = TX (chi1 : ClassFunction d.H) +
      (ai chi1 : Complex) • u from rfl, hai1]
    simp [u]
  have himgXvirt (chi : X) :
      Theory.Character.IsVirtualCharacter (imgX chi) := by
    apply Section3.isVirtualCharacter_add (hTXvirt chi)
    simpa using virtual_zsmul (ai chi : Int)
      (Section3.isVirtualCharacter_sub hvvirt (hTXvirt chi1))
  have himgXgram (chi psi : X) :
      scalarProduct G (imgX chi) (imgX psi) =
        if chi = psi then 1 else 0 := by
    rw [show imgX chi = TX (chi : ClassFunction d.H) +
      (ai chi : Complex) • u from rfl]
    rw [show imgX psi = TX (psi : ClassFunction d.H) +
      (ai psi : Complex) • u from rfl]
    simp only [Section1.scalarProduct_add_left,
      Section5.scalarProduct_add_right,
      Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_right]
    rw [hTXgram chi psi, hTXu chi, huTX psi, huu]
    simp
    ring
  have himgXcross (chi : X) (eta : Y) :
      scalarProduct G (imgX chi) (EY eta) = 0 := by
    rw [show imgX chi = TX (chi : ClassFunction d.H) +
      (ai chi : Complex) • u from rfl]
    rw [Section1.scalarProduct_add_left,
      Section1.scalarProduct_smul_left, hcross chi eta]
    have huEY : scalarProduct G u (EY eta) = 0 := by
      rw [show u = v - TX (chi1 : ClassFunction d.H) from rfl,
        Section5.scalarProduct_sub_left, hvorth eta, hcross chi1 eta]
      ring
    rw [huEY]
    ring
  let img : U → ClassFunction G := fun theta =>
    if htheta : (theta : ClassFunction d.H) ∈ X then
      imgX ⟨theta, htheta⟩
    else
      EY ⟨theta, ((hUmem theta).mp theta.property).resolve_left htheta⟩
  have himgX (chi : X) :
      img ⟨chi, (hUmem chi).mpr (Or.inl chi.property)⟩ = imgX chi := by
    simp [img, chi.property]
  have himgY (eta : Y) :
      img ⟨eta, (hUmem eta).mpr (Or.inr eta.property)⟩ = EY eta := by
    have hetaX : (eta : ClassFunction d.H) ∉ X := by
      intro heta
      exact (Finset.disjoint_left.mp hXY heta) eta.property
    simp [img, hetaX]
  have himgVirt (theta : U) :
      Theory.Character.IsVirtualCharacter (img theta) := by
    by_cases htheta : (theta : ClassFunction d.H) ∈ X
    · simpa [img, htheta] using himgXvirt ⟨theta, htheta⟩
    · let eta : Y :=
        ⟨theta, ((hUmem theta).mp theta.property).resolve_left htheta⟩
      simpa [img, htheta, eta] using hEYvirt eta
  have himgGram (theta zeta : U) :
      scalarProduct G (img theta) (img zeta) =
        scalarProduct d.H (theta : ClassFunction d.H)
          (zeta : ClassFunction d.H) := by
    by_cases htheta : (theta : ClassFunction d.H) ∈ X
    · let chi : X := ⟨theta, htheta⟩
      rw [show img theta = imgX chi by simp [img, htheta, chi]]
      by_cases hzeta : (zeta : ClassFunction d.H) ∈ X
      · let psi : X := ⟨zeta, hzeta⟩
        rw [show img zeta = imgX psi by simp [img, hzeta, psi]]
        rw [himgXgram chi psi]
        split_ifs with heq
        · have hval0 := congrArg
            (fun q : X => (q : ClassFunction d.H)) heq
          have hval : (theta : ClassFunction d.H) =
              (zeta : ClassFunction d.H) := hval0
          rw [← hval]
          exact (Section1.scalarProduct_irreducibleCharacter_self
            (hirrX chi)).symm
        · simpa [chi, psi] using
            (Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
              (hirrX chi) (hirrX psi) (by
                intro hval
                exact heq (Subtype.ext hval))).symm
      · let eta : Y :=
          ⟨zeta, ((hUmem zeta).mp zeta.property).resolve_left hzeta⟩
        rw [show img zeta = EY eta by simp [img, hzeta, eta]]
        rw [himgXcross chi eta]
        simpa [chi, eta] using (hsourceCross chi eta).symm
    · let eta : Y :=
        ⟨theta, ((hUmem theta).mp theta.property).resolve_left htheta⟩
      rw [show img theta = EY eta by simp [img, htheta, eta]]
      by_cases hzeta : (zeta : ClassFunction d.H) ∈ X
      · let chi : X := ⟨zeta, hzeta⟩
        rw [show img zeta = imgX chi by simp [img, hzeta, chi]]
        have htarget := Section1.scalarProduct_star_swap
          (G := G) (EY eta) (imgX chi)
        rw [himgXcross chi eta] at htarget
        have hsource := Section1.scalarProduct_star_swap
          (G := d.H) (eta : ClassFunction d.H)
            (chi : ClassFunction d.H)
        rw [hsourceCross chi eta] at hsource
        simpa using htarget.symm.trans hsource
      · let zetaY : Y :=
          ⟨zeta, ((hUmem zeta).mp zeta.property).resolve_left hzeta⟩
        rw [show img zeta = EY zetaY by simp [img, hzeta, zetaY]]
        by_cases heq : eta = zetaY
        · rw [heq, hEYself]
          have hval0 := congrArg
            (fun q : Y => (q : ClassFunction d.H)) heq
          have hval : (theta : ClassFunction d.H) =
              (zeta : ClassFunction d.H) := hval0
          rw [← hval]
          exact (Section1.scalarProduct_irreducibleCharacter_self
            (hirrY eta)).symm
        · rw [hEYoff eta zetaY heq]
          simpa [eta, zetaY] using
            (Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
              (hirrY eta) (hirrY zetaY) (by
                intro hval
                exact heq (Subtype.ext hval))).symm
  have hpairwise : Section5.hypothesis_5_2_c_statement U := by
    intro theta zeta htheta hzeta hne
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hirrU ⟨theta, htheta⟩) (hirrU ⟨zeta, hzeta⟩) hne
  have hselfNe (theta : U) :
      scalarProduct d.H (theta : ClassFunction d.H)
        (theta : ClassFunction d.H) ≠ 0 := by
    rw [Section1.scalarProduct_irreducibleCharacter_self (hirrU theta)]
    norm_num
  have hsplit (theta : U) :
      Section1.inducedCFLinear d.H
          ((theta : ClassFunction d.H) -
            (degree (theta : ClassFunction d.H) /
              (Nat.card d.D : Complex)) • (eta1 : ClassFunction d.H)) =
        img theta -
          (degree (theta : ClassFunction d.H) /
            (Nat.card d.D : Complex)) • EY eta1 := by
    have hcardNe : (Nat.card d.D : Complex) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := d.D)).ne'
    by_cases htheta : (theta : ClassFunction d.H) ∈ X
    · let chi : X := ⟨theta, htheta⟩
      have hratio :
          degree (theta : ClassFunction d.H) /
              (Nat.card d.D : Complex) =
            ((ai chi * a : Nat) : Complex) := by
        rw [hai chi, hdegree, hYdegree eta1]
        field_simp [hcardNe]
        push_cast
        ring
      have hdecomp :
          (theta : ClassFunction d.H) -
              ((ai chi * a : Nat) : Complex) •
                (eta1 : ClassFunction d.H) =
            ((chi : ClassFunction d.H) -
                (ai chi : Complex) • (chi1 : ClassFunction d.H)) +
              (ai chi : Complex) • sourceBridge := by
        ext g
        simp [sourceBridge]
        ring
      rw [hratio, hdecomp, map_add, map_smul, hbridgeLinear,
        inducedCFLinear_apply, hXdiff chi]
      rw [show img theta = imgX chi by simp [img, htheta, chi]]
      rw [show imgX chi = TX (chi : ClassFunction d.H) +
        (ai chi : Complex) • u from rfl]
      rw [show u = v - TX (chi1 : ClassFunction d.H) from rfl]
      ext g
      simp
      ring
    · let eta : Y :=
        ⟨theta, ((hUmem theta).mp theta.property).resolve_left htheta⟩
      have hratio :
          degree (theta : ClassFunction d.H) /
              (Nat.card d.D : Complex) = 1 := by
        rw [hYdegree eta]
        exact div_self hcardNe
      rw [hratio, one_smul, inducedCFLinear_apply]
      rw [show img theta = EY eta by simp [img, htheta, eta]]
      simpa using hEYdiff eta
  obtain ⟨Tnew, hnewIso, hnewVirt, hnewAgree⟩ :=
    Section5.exists_extension_fields_of_image_family_pf57
      U (Section1.inducedCFLinear d.H) img hpairwise hselfNe
        himgVirt himgGram (by
          intro Tnew hTnew
          exact appendixIV_unionImage_agreesOnIntegerSpanOn_of_split
            (W1 := d.D) (eta1 := (eta1 : ClassFunction d.H))
            (Ycf := EY eta1) hsplit hTnew)
  have hsourceVirt : sourceVirtualCharacters U := by
    intro theta htheta
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup
      (hirrU ⟨theta, htheta⟩)
  have hnonempty : integerSpanOnNonempty U puncturedSet := by
    rcases hXnonemptyOn with ⟨phi, hphi, hphiNe⟩
    exact ⟨phi, integerSpanOn_mono
      (fun theta htheta => (hUmem theta).mpr (Or.inl htheta)) hphi, hphiNe⟩
  exact ⟨hsourceVirt, hnonempty, Tnew, hnewIso, hnewVirt, hnewAgree⟩

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem feitSibley_step6_extend_union_coherence_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (hZne : feitSibleyZ d ≠ ⊥)
    (hZnormal : (feitSibleyZ d).Normal)
    (hZle : feitSibleyZ d ≤ feitSibleyCenterQ1H d)
    (X Y U : Finset (ClassFunction d.H))
    (hXmem : ∀ theta : ClassFunction d.H,
      theta ∈ X ↔ theta ∈ feitSibleyX d chars)
    (hYmem : ∀ theta : ClassFunction d.H,
      theta ∈ Y ↔ theta ∈ feitSibleyY d chars)
    (hUmem : ∀ theta : ClassFunction d.H,
      theta ∈ U ↔ theta ∈ X ∨ theta ∈ Y)
    (hXne : X.Nonempty)
    (hYne : Y.Nonempty)
    (hYnonemptyOn : integerSpanOnNonempty Y puncturedSet)
    (hYdegree : ∀ eta : Y,
      degree (eta : ClassFunction d.H) = (Nat.card d.D : Complex))
    (hcoherentUnion : feitSibleyCoherent d U)
    (hstep2 :
      feitSibleyCoherent d
          (feitSibleySker d chars (feitSibleySderivedH d)) →
        feitSibleyCoherent d chars) :
    feitSibleyCoherent d chars := by
  classical
  let V := feitSibleySker d chars (feitSibleySderivedH d)
  let X1 := X ∩ V
  let U1 := X1 ∪ Y
  let : Fact p.Prime := ⟨hpprime⟩
  let : (feitSibleyZ d).Normal := hZnormal
  let : d.S.Normal := d.S_normal
  have : (feitSibleySderivedH d).Normal := by
    dsimp [feitSibleySderivedH]
    infer_instance
  have hQderived :
      feitSibleyQderivedH d =
        feitSibleySderivedH d ⊔ feitSibleyQ1derivedH d := by
    simpa [feitSibleyQderivedH, feitSibleySderivedH,
      feitSibleyQ1derivedH] using d.map_derivedSubgroup_Q_eq_sup
  have hSderivedLeQderived :
      feitSibleySderivedH d ≤ feitSibleyQderivedH d := by
    rw [hQderived]
    exact le_sup_left
  have hYV : Y ⊆ V := by
    intro eta heta
    rcases Finset.mem_filter.mp ((hYmem eta).mp heta) with
      ⟨hetaChars, hetaKernel⟩
    exact Finset.mem_filter.mpr
      ⟨hetaChars,
        subgroupInKernel'_mono_appendixIV hSderivedLeQderived hetaKernel⟩
  have hU1V : U1 ⊆ V := by
    intro theta htheta
    rcases Finset.mem_union.mp htheta with hthetaX1 | hthetaY
    · exact (Finset.mem_inter.mp hthetaX1).2
    · exact hYV hthetaY
  have hU1U : U1 ⊆ U := by
    intro theta htheta
    rcases Finset.mem_union.mp htheta with hthetaX1 | hthetaY
    · exact (hUmem theta).mpr (Or.inl (Finset.mem_inter.mp hthetaX1).1)
    · exact (hUmem theta).mpr (Or.inr hthetaY)
  have hYU1 : Y ⊆ U1 := fun eta heta => Finset.mem_union_right X1 heta
  have hU1nonempty : integerSpanOnNonempty U1 puncturedSet := by
    rcases hYnonemptyOn with ⟨phi, hphi, hphiNe⟩
    exact ⟨phi, integerSpanOn_mono hYU1 hphi, hphiNe⟩
  have hcoherentU1 : feitSibleyCoherent d U1 :=
    IsCoherentTriple_mono hU1U hU1nonempty hcoherentUnion
  apply hstep2
  by_contra hnotcoherentV
  have hVsub : V ⊆ chars := by
    intro psi hpsi
    exact (Finset.mem_filter.mp hpsi).1
  have hirrV : ∀ psi : V,
      IsIrreducibleCharacterOnGroup (psi : ClassFunction d.H) := by
    intro psi
    exact ((hchars (psi : ClassFunction d.H)).mp (hVsub psi.property)).1
  rcases lemma_2_b d chars hchars with ⟨hisoChars, htargetChars⟩
  have hisoV : isCFLinearIsometryOnSpanOn V puncturedSet
      (Section1.inducedCFLinear d.H) := by
    intro phi theta hphi htheta
    exact hisoChars phi theta
      (integerSpanOn_mono hVsub hphi) (integerSpanOn_mono hVsub htheta)
  have htargetV : ∀ phi : ClassFunction d.H,
      integerSpanOn V puncturedSet phi →
        Theory.Character.IsVirtualCharacter
            (Section1.inducedCFLinear d.H phi) ∧
          supportedOn (Section1.inducedCFLinear d.H phi) puncturedSet := by
    intro phi hphi
    exact htargetChars phi (integerSpanOn_mono hVsub hphi)
  obtain ⟨eta0, heta0Mem⟩ := hYne
  let eta0Y : Y := ⟨eta0, heta0Mem⟩
  have heta0U1 : eta0 ∈ U1 := hYU1 heta0Mem
  have hdivV : ∀ psi : ClassFunction d.H, psi ∈ V →
      ∃ n : Nat, degree psi = (n : Complex) * degree eta0 := by
    intro psi hpsiV
    have hpsiChars : psi ∈ chars := hVsub hpsiV
    have hpsiKernel :
        subgroupInKernel' psi (feitSibleySderivedH d) :=
      (Finset.mem_filter.mp hpsiV).2
    rcases feitSibley_step3_degree_shape_core
        d chars hchars p hpprime hpQ1 (feitSibleyZ d)
          hZnormal hZle psi hpsiChars hpsiKernel with
      ⟨k, n, _hnpos, hpsiDegree, hn, _hpRel⟩
    refine ⟨p ^ k, ?_⟩
    rw [hpsiDegree, hn, hYdegree eta0Y]
    push_cast
    ring
  obtain ⟨psi, hpsiV, hpsiU1, hdegreeBound⟩ :=
    exists_degree_obstruction_of_not_coherent_appendixIV
      d.H U1 V (Section1.inducedCFLinear d.H) hU1V eta0 heta0U1
        hirrV hisoV htargetV hdivV hcoherentU1
        (by simpa [V] using hnotcoherentV)
  have hpsiChars : psi ∈ chars := hVsub hpsiV
  have hpsiKernelS :
      subgroupInKernel' psi (feitSibleySderivedH d) :=
    (Finset.mem_filter.mp hpsiV).2
  have hpsiNotX1 : psi ∉ X1 := by
    intro hpsiX1
    exact hpsiU1 (Finset.mem_union_left Y hpsiX1)
  have hpsiNotX : psi ∉ X := by
    intro hpsiX
    exact hpsiNotX1 (Finset.mem_inter.mpr ⟨hpsiX, hpsiV⟩)
  have hpsiKernelZ : subgroupInKernel' psi (feitSibleyZ d) := by
    by_contra hnotZ
    exact hpsiNotX ((hXmem psi).mpr
      (Finset.mem_filter.mpr ⟨hpsiChars, hnotZ⟩))
  have hpsiNotY : psi ∉ Y := by
    intro hpsiY
    exact hpsiU1 (Finset.mem_union_right X1 hpsiY)
  have hpsiNotKernelQderived :
      ¬ subgroupInKernel' psi (feitSibleyQderivedH d) := by
    intro hpsiKernel
    exact hpsiNotY ((hYmem psi).mpr
      (Finset.mem_filter.mpr ⟨hpsiChars, hpsiKernel⟩))
  rcases feitSibley_step3_degree_shape_core
      d chars hchars p hpprime hpQ1 (feitSibleyZ d)
        hZnormal hZle psi hpsiChars hpsiKernelS with
    ⟨k, n, hnpos, hpsiDegree, hn, hpRel⟩
  have hkpos : 0 < k := by
    by_contra hk
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk
    have hdegreeRelIndex :
        degree psi =
          (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
      rw [hpsiDegree, hn, hkzero]
      rw [feitSibley_Q_relIndex_top_eq_card_D_appendixIV d]
      simp
    exact hpsiNotKernelQderived
      (d.exceptional_derived_kernel_of_degree_eq_relIndex
        chars hchars psi hpsiChars hdegreeRelIndex)
  have hpne : p ≠ 2 := by
    intro hp
    subst p
    exact d.Q1_not_two_group hpQ1
  have hpgt : 2 < p := lt_of_le_of_ne hpprime.two_le hpne.symm
  have hX1mem : ∀ chi : ClassFunction d.H, chi ∈ X1 ↔
      (chi ∈ chars ∧ ¬ subgroupInKernel' chi (feitSibleyZ d)) ∧
        chi ∈ chars ∧
          subgroupInKernel' chi (feitSibleySderivedH d) := by
    intro chi
    rw [Finset.mem_inter, hXmem]
    simp only [V, feitSibleyX, feitSibleySnonker,
      feitSibleySker, Finset.mem_filter]
  have hX1ne : X1.Nonempty := by
    obtain ⟨chi, hchiX⟩ := hXne
    have hchiData := Finset.mem_filter.mp ((hXmem chi).mp hchiX)
    rcases feitSibley_step3_exists_base_companion_core
        d chars hchars (feitSibleyZ d) hZnormal hZle hX1mem
          chi hchiData.1 hchiData.2 with
      ⟨theta, hthetaX1, _m, _hthetaDegree⟩
    exact ⟨theta, hthetaX1⟩
  rcases feitSibley_step3_base_degree_data_core
      d chars hchars p hpprime hpQ1 (feitSibleyZ d)
        hZne hZnormal hZle hX1mem with
    ⟨deg, hdeg, hpower, _hprefix⟩
  have hZleQ1 : feitSibleyZ d ≤ d.Q1 :=
    hZle.trans (by
      simpa [feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  have hSderivedLeS : feitSibleySderivedH d ≤ d.S := by
    simpa [feitSibleySderivedH] using
      Subgroup.map_subtype_le (derivedSubgroup d.S)
  have hXchar : ∀ chi : ClassFunction d.H, chi ∈ X1 ↔
      IsIrreducibleCharacterOnGroup chi ∧
        subgroupInKernel' chi (feitSibleySderivedH d) ∧
          ¬ subgroupInKernel' chi (feitSibleyZ d) := by
    intro chi
    rw [hX1mem]
    constructor
    · rintro ⟨⟨hchiChars, hnotZ⟩, _hchiChars', hkerS⟩
      exact ⟨((hchars chi).mp hchiChars).1, hkerS, hnotZ⟩
    · rintro ⟨hirr, hkerS, hnotZ⟩
      have hnotQ1 : ¬ subgroupInKernel' chi d.Q1 := by
        intro hkerQ1
        exact hnotZ (subgroupInKernel'_mono_appendixIV hZleQ1 hkerQ1)
      have hchiChars : chi ∈ chars := (hchars chi).mpr ⟨hirr, hnotQ1⟩
      exact ⟨⟨hchiChars, hnotZ⟩, hchiChars, hkerS⟩
  have hsumReal := exceptional_kernel_degree_sq_sum_appendixIV
    (feitSibleySderivedH d) (feitSibleyZ d) X1 hXchar
  have hsumReal' :
      (∑ chi : X1, (deg chi : Real) ^ 2) +
          (Nat.card (d.H ⧸
            (feitSibleySderivedH d ⊔ feitSibleyZ d)) : Real) =
        (Nat.card (d.H ⧸ feitSibleySderivedH d) : Real) := by
    calc
      (∑ chi : X1, (deg chi : Real) ^ 2) +
          (Nat.card (d.H ⧸
            (feitSibleySderivedH d ⊔ feitSibleyZ d)) : Real) =
          (∑ chi : X1,
            (degree (chi : ClassFunction d.H)).re ^ 2) +
              (Nat.card (d.H ⧸
                (feitSibleySderivedH d ⊔ feitSibleyZ d)) : Real) := by
        congr 1
        apply Finset.sum_congr rfl
        intro chi _hchi
        rw [(hdeg chi).2]
        simp
      _ = _ := hsumReal
  have hsumNat :
      (∑ chi : X1, deg chi ^ 2) +
          Nat.card (d.H ⧸
            (feitSibleySderivedH d ⊔ feitSibleyZ d)) =
        Nat.card (d.H ⧸ feitSibleySderivedH d) := by
    exact_mod_cast hsumReal'
  have hInf :
      (feitSibleySderivedH d ⊔ feitSibleyZ d) ⊓ d.Q1 =
        feitSibleyZ d := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_inf.mp hx with ⟨hxSup, hxQ1⟩
      rcases Subgroup.mem_sup_of_normal_right.mp hxSup with
        ⟨s, hs, z, hz, hsz⟩
      have hsQ1 : s ∈ d.Q1 := by
        have hseq : s = x * z⁻¹ := by
          rw [← hsz]
          simp
        rw [hseq]
        exact d.Q1.mul_mem hxQ1 (d.Q1.inv_mem (hZleQ1 hz))
      have hsOne : s = 1 := by
        apply Subgroup.mem_bot.mp
        exact d.S_disjoint_Q1.le_bot ⟨hSderivedLeS hs, hsQ1⟩
      rw [hsOne, one_mul] at hsz
      exact hsz ▸ hz
    · intro x hx
      exact Subgroup.mem_inf.mpr
        ⟨(show feitSibleyZ d ≤
            feitSibleySderivedH d ⊔ feitSibleyZ d from le_sup_right) hx,
          hZleQ1 hx⟩
  have hrel :
      (feitSibleySderivedH d ⊔ feitSibleyZ d).relIndex
          (feitSibleySderivedH d ⊔ d.Q1) =
        (feitSibleyZ d).relIndex d.Q1 := by
    calc
      (feitSibleySderivedH d ⊔ feitSibleyZ d).relIndex
          (feitSibleySderivedH d ⊔ d.Q1) =
          (feitSibleySderivedH d ⊔ feitSibleyZ d).relIndex
            ((feitSibleySderivedH d ⊔ feitSibleyZ d) ⊔ d.Q1) := by
              rw [sup_assoc, sup_eq_right.2 hZleQ1]
      _ = (feitSibleySderivedH d ⊔ feitSibleyZ d).relIndex d.Q1 :=
        Subgroup.relIndex_sup_left d.Q1
          (feitSibleySderivedH d ⊔ feitSibleyZ d)
      _ = ((feitSibleySderivedH d ⊔ feitSibleyZ d) ⊓ d.Q1).relIndex
          d.Q1 :=
        (Subgroup.inf_relIndex_right
          (feitSibleySderivedH d ⊔ feitSibleyZ d) d.Q1).symm
      _ = (feitSibleyZ d).relIndex d.Q1 := by rw [hInf]
  have hrelDvdSupIndex :
      (feitSibleyZ d).relIndex d.Q1 ∣
        (feitSibleySderivedH d ⊔ feitSibleyZ d).index := by
    have hdvd := Subgroup.relIndex_dvd_index_of_le
      (show feitSibleySderivedH d ⊔ feitSibleyZ d ≤
          feitSibleySderivedH d ⊔ d.Q1 from
        sup_le_sup le_rfl hZleQ1)
    rwa [hrel] at hdvd
  have hsupIndexDvdBase :
      (feitSibleySderivedH d ⊔ feitSibleyZ d).index ∣
        (feitSibleySderivedH d).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hcop : Nat.Coprime (Nat.card d.D) p := by
    have hQ1ne : d.Q1 ≠ ⊥ := by
      intro hQ1
      apply d.Q1_not_two_group
      exact hQ1.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
    have hpQ1card : p ∣ Nat.card d.Q1 := by
      rcases hpQ1.card_eq_or_dvd with hcard | hdvd
      · have hbot : d.Q1 = ⊥ := by
          rw [← Subgroup.card_le_one_iff_eq_bot, hcard]
        exact (hQ1ne hbot).elim
      · exact hdvd
    have hpQcard : p ∣ Nat.card d.Q :=
      hpQ1card.trans (Subgroup.card_dvd_of_le d.Q1_le_Q)
    exact Nat.Coprime.of_dvd_right hpQcard d.card_Q_coprime_card_D.symm
  have hpSupIndex :
      p ^ (2 * k) ∣
        (feitSibleySderivedH d ⊔ feitSibleyZ d).index :=
    hpRel.trans hrelDvdSupIndex
  have hpBaseIndex :
      p ^ (2 * k) ∣ (feitSibleySderivedH d).index :=
    hpSupIndex.trans hsupIndexDvdBase
  have hpSupCard :
      p ^ (2 * k) ∣
        Nat.card (d.H ⧸
          (feitSibleySderivedH d ⊔ feitSibleyZ d)) := by
    simpa [Subgroup.index_eq_card] using hpSupIndex
  have hpBaseCard :
      p ^ (2 * k) ∣ Nat.card (d.H ⧸ feitSibleySderivedH d) := by
    simpa [Subgroup.index_eq_card] using hpBaseIndex
  have hpTotal : p ^ (2 * k) ∣ ∑ chi : X1, deg chi ^ 2 := by
    apply (Nat.dvd_add_iff_left hpSupCard).2
    rw [hsumNat]
    exact hpBaseCard
  have hDTotal : (Nat.card d.D) ^ 2 ∣ ∑ chi : X1, deg chi ^ 2 := by
    apply Finset.dvd_sum
    intro chi _hchi
    rcases hpower chi with ⟨b, hchiDegree⟩
    rw [hchiDegree]
    use (p ^ b) ^ 2
    ring
  have hcopPow :
      Nat.Coprime ((Nat.card d.D) ^ 2) (p ^ (2 * k)) :=
    (hcop.pow_left 2).pow_right (2 * k)
  have hmul : (Nat.card d.D) ^ 2 * p ^ (2 * k) ∣
      ∑ chi : X1, deg chi ^ 2 :=
    hcopPow.mul_dvd_of_dvd_of_dvd hDTotal hpTotal
  have hnSqDvd : n ^ 2 ∣ ∑ chi : X1, deg chi ^ 2 := by
    rw [hn]
    (convert hmul using 1; ring)
  have hsumPos : 0 < ∑ chi : X1, deg chi ^ 2 := by
    obtain ⟨chi, hchiX1⟩ := hX1ne
    let chiX1 : X1 := ⟨chi, hchiX1⟩
    have hterm : 0 < deg chiX1 ^ 2 := pow_pos (hdeg chiX1).1 _
    have hle : deg chiX1 ^ 2 ≤ ∑ theta : X1, deg theta ^ 2 := by
      exact Finset.single_le_sum
        (fun theta _htheta => Nat.zero_le (deg theta ^ 2))
        (show chiX1 ∈ (Finset.univ : Finset X1) by simp)
    omega
  have hnSqLeNat : n ^ 2 ≤ ∑ chi : X1, deg chi ^ 2 :=
    Nat.le_of_dvd hsumPos hnSqDvd
  have hnSqLeReal : (n : Real) ^ 2 ≤
      ∑ chi : X1, (deg chi : Real) ^ 2 := by
    exact_mod_cast hnSqLeNat
  have hsumX1 :
      (∑ chi : X1, (degree (chi : ClassFunction d.H)).re ^ 2) =
        ∑ chi : X1, (deg chi : Real) ^ 2 := by
    apply Finset.sum_congr rfl
    intro chi _hchi
    rw [(hdeg chi).2]
    simp
  have hpsiRe : (degree psi).re = (n : Real) := by
    rw [hpsiDegree]
    simp
  have heta0Re : (degree eta0).re = (Nat.card d.D : Real) := by
    rw [hYdegree eta0Y]
    simp
  have hpPow : p < p ^ k ∨ p = p ^ k := by
    exact lt_or_eq_of_le
      (by
        simpa using
          (Nat.pow_le_pow_right hpprime.one_lt.le
            (show 1 ≤ k from hkpos)))
  have htwoLtPow : 2 < p ^ k := by
    rcases hpPow with hpPow | hpPow
    · exact hpgt.trans hpPow
    · simpa [← hpPow] using hpgt
  have htwiceDlt : 2 * Nat.card d.D < n := by
    rw [hn]
    simpa [Nat.mul_comm] using
      (Nat.mul_lt_mul_left (Nat.card_pos (α := d.D))).2 htwoLtPow
  have hgap :
      2 * (degree psi).re * (degree eta0).re <
        (degree psi).re ^ 2 := by
    rw [hpsiRe, heta0Re]
    have htwiceDltReal :
        (2 : Real) * (Nat.card d.D : Real) < (n : Real) := by
      exact_mod_cast htwiceDlt
    have hnposReal : (0 : Real) < (n : Real) := by exact_mod_cast hnpos
    nlinarith
  have hpsiSqLeX1 :
      (degree psi).re ^ 2 ≤
        ∑ chi : X1, (degree (chi : ClassFunction d.H)).re ^ 2 := by
    rw [hpsiRe, hsumX1]
    exact hnSqLeReal
  have hX1U1 : X1 ⊆ U1 :=
    fun chi hchi => Finset.mem_union_left Y hchi
  have hX1LeU1 := degree_re_sq_sum_mono_appendixIV hX1U1
  have hcontra :
      2 * (degree psi).re * (degree eta0).re <
        ∑ chi : U1, (degree (chi : ClassFunction d.H)).re ^ 2 :=
    hgap.trans_le (hpsiSqLeX1.trans hX1LeU1)
  exact (not_lt_of_ge hdegreeBound) hcontra

set_option maxHeartbeats 1600000 in
private theorem feitSibley_step6_lambda_decomposition_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (hYcard : 2 ≤ (feitSibleyY d chars).card)
    (hstep4 : feitSibleyStep4Data d chars)
    (hstep2 :
      feitSibleyCoherent d
          (feitSibleySker d chars (feitSibleySderivedH d)) →
        feitSibleyCoherent d chars) :
    feitSibleyStep6Data d chars := by
  classical
  rcases hstep4 with
    ⟨hZne, hZnormal, hZle, hXY, hcoherentX, hcoherentY,
      hXne, hYne, hYdegree, hdegreeData⟩
  unfold feitSibleyStep6Data
  intro TX TY chi1 eta1 a hdivX hTX hTY hcross ha hdegree
  let X := feitSibleyX d chars
  let Y := feitSibleyY d chars
  have hXsub : X ⊆ chars := by
    intro chi hchi
    exact (Finset.mem_filter.mp hchi).1
  have hYsub : Y ⊆ chars := by
    intro eta heta
    exact (Finset.mem_filter.mp heta).1
  have hirrX (chi : X) :
      IsIrreducibleCharacterOnGroup (chi : ClassFunction d.H) :=
    ((hchars (chi : ClassFunction d.H)).mp (hXsub chi.property)).1
  have hirrY (eta : Y) :
      IsIrreducibleCharacterOnGroup (eta : ClassFunction d.H) :=
    ((hchars (eta : ClassFunction d.H)).mp (hYsub eta.property)).1
  have hsourceCross (chi : X) (eta : Y) :
      scalarProduct d.H (chi : ClassFunction d.H)
        (eta : ClassFunction d.H) = 0 := by
    have hne : (chi : ClassFunction d.H) ≠
        (eta : ClassFunction d.H) := by
      intro heq
      exact (Finset.disjoint_left.mp hXY chi.property)
        (heq ▸ eta.property)
    exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
      (hirrX chi) (hirrY eta) hne
  have hsignedY (eta : Y) :
      Section3.IsSignedIrreducibleCharacter
        (TY (eta : ClassFunction d.H)) := by
    apply Section5.signed_irreducible_of_virtual_norm_one_pf59
    · exact hTY.2.1 (eta : ClassFunction d.H)
        (integerSpan_of_mem _ eta.property)
    · calc
        scalarProduct G (TY (eta : ClassFunction d.H))
            (TY (eta : ClassFunction d.H)) =
            scalarProduct d.H (eta : ClassFunction d.H)
              (eta : ClassFunction d.H) :=
          Section5.isCFLinearIsometryOnSpan_apply_of_mem
            hTY.1 eta.property eta.property
        _ = 1 :=
          Section1.scalarProduct_irreducibleCharacter_self (hirrY eta)
  have hTYvirt (eta : Y) :
      Theory.Character.IsVirtualCharacter
        (TY (eta : ClassFunction d.H)) :=
    Section3.isVirtualCharacter_of_signedIrreducible_pf35 (hsignedY eta)
  let source : ClassFunction d.H :=
    (chi1 : ClassFunction d.H) -
      (a : Complex) • (eta1 : ClassFunction d.H)
  let w : ClassFunction G := Section1.inducedCF d.H source
  have hsourceDegree : degree source = 0 := by
    change degree (chi1 : ClassFunction d.H) -
      (a : Complex) * degree (eta1 : ClassFunction d.H) = 0
    rw [hdegree]
    ring
  have hsourceSpan : integerSpan chars source := by
    apply integerSpan_sub
    · exact integerSpan_of_mem chars (hXsub chi1.property)
    · simpa using integerSpan_zsmul (a : Int)
        (integerSpan_of_mem chars (hYsub eta1.property))
  have hsourceOn : integerSpanOn chars puncturedSet source :=
    ⟨hsourceSpan,
      (supportedOn_puncturedSet_iff_degree_eq_zero source).2 hsourceDegree⟩
  rcases lemma_2_b d chars hchars with ⟨hIndIso, hIndTarget⟩
  have hwvirt : Theory.Character.IsVirtualCharacter w := by
    exact (hIndTarget source hsourceOn).1
  have hTYgram (eta zeta : Y) :
      scalarProduct G (TY (eta : ClassFunction d.H))
          (TY (zeta : ClassFunction d.H)) =
        if eta = zeta then 1 else 0 := by
    rw [Section5.isCFLinearIsometryOnSpan_apply_of_mem
      hTY.1 eta.property zeta.property]
    split_ifs with heq
    · subst zeta
      exact Section1.scalarProduct_irreducibleCharacter_self (hirrY eta)
    · exact Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
        (hirrY eta) (hirrY zeta) (by
          intro hval
          exact heq (Subtype.ext hval))
  have hcoeffDiff (eta : Y) (hne : eta ≠ eta1) :
      scalarProduct G w (TY (eta : ClassFunction d.H)) -
          scalarProduct G w (TY (eta1 : ClassFunction d.H)) =
        (a : Complex) := by
    let diff : ClassFunction d.H :=
      (eta : ClassFunction d.H) - (eta1 : ClassFunction d.H)
    have hdiffDegree : degree diff = 0 := by
      change degree (eta : ClassFunction d.H) -
        degree (eta1 : ClassFunction d.H) = 0
      rw [hYdegree eta, hYdegree eta1]
      ring
    have hdiffSpanY : integerSpan Y diff :=
      integerSpan_sub
        (integerSpan_of_mem Y eta.property)
        (integerSpan_of_mem Y eta1.property)
    have hdiffOnY : integerSpanOn Y puncturedSet diff :=
      ⟨hdiffSpanY,
        (supportedOn_puncturedSet_iff_degree_eq_zero diff).2 hdiffDegree⟩
    have hTYdiff : TY diff = Section1.inducedCFLinear d.H diff :=
      hTY.2.2 diff hdiffOnY
    have hdiffOnChars : integerSpanOn chars puncturedSet diff :=
      integerSpanOn_mono hYsub hdiffOnY
    calc
      scalarProduct G w (TY (eta : ClassFunction d.H)) -
          scalarProduct G w (TY (eta1 : ClassFunction d.H)) =
          scalarProduct G w
            (TY (eta : ClassFunction d.H) -
              TY (eta1 : ClassFunction d.H)) := by
            rw [Section5.scalarProduct_sub_right]
      _ = scalarProduct G w (TY diff) := by rw [map_sub]
      _ = scalarProduct G
          (Section1.inducedCFLinear d.H source)
          (Section1.inducedCFLinear d.H diff) := by
            rw [hTYdiff]
            rfl
      _ = scalarProduct d.H source diff :=
        hIndIso source diff hsourceOn hdiffOnChars
      _ = (a : Complex) := by
        rw [show source = (chi1 : ClassFunction d.H) -
          (a : Complex) • (eta1 : ClassFunction d.H) from rfl]
        rw [show diff = (eta : ClassFunction d.H) -
          (eta1 : ClassFunction d.H) from rfl]
        rw [Section5.scalarProduct_sub_left,
          Section5.scalarProduct_sub_right,
          Section5.scalarProduct_sub_right,
          Section1.scalarProduct_smul_left]
        rw [hsourceCross chi1 eta, hsourceCross chi1 eta1,
          Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne
            (hirrY eta1) (hirrY eta) (by
              intro hval
              exact hne (Subtype.ext hval.symm)),
          Section1.scalarProduct_smul_left,
          Section1.scalarProduct_irreducibleCharacter_self (hirrY eta1)]
        simp
  obtain ⟨k, hk⟩ :=
    Section3.scalarProduct_isVirtualCharacter_eq_int hwvirt (hTYvirt eta1)
  let lambda : Int := k + a
  let component : ClassFunction G :=
    -(a : Complex) • TY (eta1 : ClassFunction d.H) +
      (lambda : Complex) •
        (∑ eta : Y, TY (eta : ClassFunction d.H))
  let v : ClassFunction G := w - component
  have hwCoeff (eta : Y) :
      scalarProduct G w (TY (eta : ClassFunction d.H)) =
        if eta = eta1 then (lambda - a : Int) else lambda := by
    split_ifs with heq
    · subst eta
      simpa [lambda] using hk
    · have hdiff := hcoeffDiff eta heq
      rw [hk] at hdiff
      have : scalarProduct G w (TY (eta : ClassFunction d.H)) =
          (lambda : Complex) := by
        calc
          scalarProduct G w (TY (eta : ClassFunction d.H)) =
              (a : Complex) + (k : Complex) :=
            sub_eq_iff_eq_add.mp hdiff
          _ = ((k + (a : Int) : Int) : Complex) := by
            push_cast
            ring
      simpa using this
  have hTYsum (eta : Y) :
      scalarProduct G (∑ zeta : Y, TY (zeta : ClassFunction d.H))
        (TY (eta : ClassFunction d.H)) = 1 := by
    have hsumEq :
        (∑ zeta : Y, TY (zeta : ClassFunction d.H)) =
          (fun g : G => ∑ zeta : Y,
            (TY (zeta : ClassFunction d.H)) g) := by
      ext g
      simp
    rw [hsumEq, Section1.scalarProduct_fintype_sum_left]
    rw [Finset.sum_eq_single eta]
    · simp [hTYgram eta eta]
    · intro zeta _hzeta hne
      simp [hTYgram zeta eta, hne]
    · simp
  have hvorth (eta : Y) :
      scalarProduct G v (TY (eta : ClassFunction d.H)) = 0 := by
    rw [show v = w - component from rfl]
    rw [Section5.scalarProduct_sub_left]
    rw [show component =
      -(a : Complex) • TY (eta1 : ClassFunction d.H) +
        (lambda : Complex) •
          (∑ zeta : Y, TY (zeta : ClassFunction d.H)) from rfl]
    rw [Section1.scalarProduct_add_left,
      Section1.scalarProduct_smul_left,
      Section1.scalarProduct_smul_left, hTYsum]
    by_cases heta : eta = eta1
    · subst eta
      rw [hwCoeff eta1]
      rw [hTYgram eta1 eta1]
      simp
      ring
    · rw [hwCoeff eta]
      have heta' : eta1 ≠ eta := Ne.symm heta
      rw [hTYgram eta1 eta]
      simp [heta, heta']
  have hsumVirt :
      Theory.Character.IsVirtualCharacter
        (∑ eta : Y, TY (eta : ClassFunction d.H)) := by
    apply virtual_finset_sum (Finset.univ : Finset Y)
      (fun eta => TY (eta : ClassFunction d.H))
    intro eta _heta
    exact hTYvirt eta
  have hcomponentVirt : Theory.Character.IsVirtualCharacter component := by
    apply Section3.isVirtualCharacter_add
    · simpa using virtual_zsmul (-(a : Int)) (hTYvirt eta1)
    · simpa using virtual_zsmul lambda hsumVirt
  have hvvirt : Theory.Character.IsVirtualCharacter v :=
    Section3.isVirtualCharacter_sub hwvirt hcomponentVirt
  have hwDecomp : w = component + v := by
    simp [v]
  refine ⟨v, lambda, hvvirt, ?_, hvorth, ?_⟩
  · exact hwDecomp
  · intro hlambda
    rcases hlambda with ⟨x, hlambda⟩
    obtain ⟨r, hr⟩ :=
      Section3.scalarProduct_isVirtualCharacter_eq_int hvvirt hvvirt
    have hrnonneg : (0 : Int) ≤ r := by
      have hnonneg := Section5.cfNormSq_nonneg v
      have hrReal : (0 : Real) ≤ (r : Real) := by
        simpa [Section5.cfNormSq, hr] using hnonneg
      exact_mod_cast hrReal
    let sumY : ClassFunction G :=
      ∑ eta : Y, TY (eta : ClassFunction d.H)
    have hsumYSelf : scalarProduct G sumY sumY = (Y.card : Complex) := by
      have hsumEq : sumY =
          (fun g : G => ∑ eta : Y,
            (TY (eta : ClassFunction d.H)) g) := by
        ext g
        simp [sumY]
      calc
        scalarProduct G sumY sumY =
            ∑ eta : Y,
              scalarProduct G sumY (TY (eta : ClassFunction d.H)) := by
          simpa only [← hsumEq] using
            (Section1.scalarProduct_fintype_sum_right sumY
              (fun eta : Y => TY (eta : ClassFunction d.H)))
        _ = ∑ _eta : Y, (1 : Complex) := by
          apply Finset.sum_congr rfl
          intro eta _heta
          simpa [sumY] using hTYsum eta
        _ = (Y.card : Complex) := by simp
    have hSumEta :
        scalarProduct G sumY (TY (eta1 : ClassFunction d.H)) = 1 := by
      simpa [sumY] using hTYsum eta1
    have hEtaSum :
        scalarProduct G (TY (eta1 : ClassFunction d.H)) sumY = 1 := by
      have hstar := Section1.scalarProduct_star_swap
        (G := G) (TY (eta1 : ClassFunction d.H)) sumY
      rw [hSumEta] at hstar
      simpa using hstar.symm
    have hcomponentSelf :
        scalarProduct G component component =
          (a : Complex) ^ 2 -
            2 * (a : Complex) * (lambda : Complex) +
              (Y.card : Complex) * (lambda : Complex) ^ 2 := by
      rw [show component =
        -(a : Complex) • TY (eta1 : ClassFunction d.H) +
          (lambda : Complex) • sumY from rfl]
      simp only [Section1.scalarProduct_add_left,
        Section5.scalarProduct_add_right,
        Section1.scalarProduct_smul_left,
        Section1.scalarProduct_smul_right]
      rw [hTYgram eta1 eta1, hSumEta, hEtaSum, hsumYSelf]
      simp
      ring
    have hvComponent : scalarProduct G v component = 0 := by
      rw [show component =
        -(a : Complex) • TY (eta1 : ClassFunction d.H) +
          (lambda : Complex) • sumY from rfl]
      rw [Section5.scalarProduct_add_right,
        Section1.scalarProduct_smul_right,
        Section1.scalarProduct_smul_right, hvorth eta1]
      have hvSum : scalarProduct G v sumY = 0 := by
        have hsumEq : sumY =
            (fun g : G => ∑ eta : Y,
              (TY (eta : ClassFunction d.H)) g) := by
          ext g
          simp [sumY]
        rw [hsumEq, Section1.scalarProduct_fintype_sum_right]
        simp [hvorth]
      rw [hvSum]
      simp
    have hComponentV : scalarProduct G component v = 0 := by
      have hstar := Section1.scalarProduct_star_swap
        (G := G) component v
      rw [hvComponent] at hstar
      simpa using hstar.symm
    have hsourceCrossRev :
        scalarProduct d.H (eta1 : ClassFunction d.H)
          (chi1 : ClassFunction d.H) = 0 := by
      have hstar := Section1.scalarProduct_star_swap
        (G := d.H) (eta1 : ClassFunction d.H)
          (chi1 : ClassFunction d.H)
      rw [hsourceCross chi1 eta1] at hstar
      simpa using hstar.symm
    have hwSelf :
        scalarProduct G w w = 1 + (a : Complex) ^ 2 := by
      calc
        scalarProduct G w w = scalarProduct d.H source source :=
          hIndIso source source hsourceOn hsourceOn
        _ = 1 + (a : Complex) ^ 2 := by
          rw [show source = (chi1 : ClassFunction d.H) -
            (a : Complex) • (eta1 : ClassFunction d.H) from rfl]
          simp only [Section5.scalarProduct_sub_left,
            Section5.scalarProduct_sub_right,
            Section1.scalarProduct_smul_left,
            Section1.scalarProduct_smul_right]
          rw [hsourceCross chi1 eta1, hsourceCrossRev,
            Section1.scalarProduct_irreducibleCharacter_self (hirrX chi1),
            Section1.scalarProduct_irreducibleCharacter_self (hirrY eta1)]
          simp
          ring
    have hwSelfSplit :
        scalarProduct G w w =
          scalarProduct G component component + scalarProduct G v v := by
      rw [hwDecomp]
      simp only [Section1.scalarProduct_add_left,
        Section5.scalarProduct_add_right]
      rw [hvComponent, hComponentV]
      ring
    have hcomponentFormula :
        scalarProduct G component component =
          (((a : Int) ^ 2 *
            ((x - 1) ^ 2 + ((Y.card : Int) - 1) * x ^ 2) : Int) :
              Complex) := by
      rw [hcomponentSelf, hlambda]
      push_cast
      ring
    have hnormComplex :
        (((1 : Int) + (a : Int) ^ 2 : Int) : Complex) =
          ((r + (a : Int) ^ 2 *
            ((x - 1) ^ 2 + ((Y.card : Int) - 1) * x ^ 2) : Int) :
              Complex) := by
      calc
        (((1 : Int) + (a : Int) ^ 2 : Int) : Complex) =
            1 + (a : Complex) ^ 2 := by
          push_cast
          ring
        _ = scalarProduct G w w := hwSelf.symm
        _ = scalarProduct G component component + scalarProduct G v v :=
          hwSelfSplit
        _ = ((r + (a : Int) ^ 2 *
            ((x - 1) ^ 2 + ((Y.card : Int) - 1) * x ^ 2) : Int) :
              Complex) := by
          rw [hcomponentFormula, hr]
          push_cast
          ring
    have hnormInt :
        (1 : Int) + (a : Int) ^ 2 =
          r + (a : Int) ^ 2 *
            ((x - 1) ^ 2 + ((Y.card : Int) - 1) * x ^ 2) := by
      exact_mod_cast hnormComplex
    have hcases := appendixIV_step6_norm_cases
      a Y.card x r ha hYcard hrnonneg hnormInt
    have hvSelf : scalarProduct G v v = 1 := by
      rw [hr, hcases.2]
      simp
    let U : Finset (ClassFunction d.H) := X ∪ Y
    have hUmem (theta : ClassFunction d.H) :
        theta ∈ U ↔ theta ∈ X ∨ theta ∈ Y := by
      simp [U]
    have hTYdiffEq (eta : Y) :
        Section1.inducedCF d.H
            ((eta : ClassFunction d.H) - (eta1 : ClassFunction d.H)) =
          TY (eta : ClassFunction d.H) -
            TY (eta1 : ClassFunction d.H) := by
      let diff : ClassFunction d.H :=
        (eta : ClassFunction d.H) - (eta1 : ClassFunction d.H)
      have hdiffDegree : degree diff = 0 := by
        change degree (eta : ClassFunction d.H) -
          degree (eta1 : ClassFunction d.H) = 0
        rw [hYdegree eta, hYdegree eta1]
        ring
      have hdiffOn : integerSpanOn Y puncturedSet diff := by
        exact ⟨integerSpan_sub
          (integerSpan_of_mem Y eta.property)
          (integerSpan_of_mem Y eta1.property),
            (supportedOn_puncturedSet_iff_degree_eq_zero diff).2 hdiffDegree⟩
      have hagree := hTY.2.2 diff hdiffOn
      rw [map_sub] at hagree
      simpa [diff, Section1.inducedCFLinear_apply] using hagree.symm
    have hXmemLocal (theta : ClassFunction d.H) :
        theta ∈ X ↔ theta ∈ feitSibleyX d chars := by
      simp [X, feitSibleyX, feitSibleySnonker]
    have hYmemLocal (theta : ClassFunction d.H) :
        theta ∈ Y ↔ theta ∈ feitSibleyY d chars := by
      simp [Y, feitSibleyY, feitSibleySker]
    let chi1X : X :=
      ⟨chi1, (hXmemLocal chi1).mpr chi1.property⟩
    let eta1Y : Y :=
      ⟨eta1, (hYmemLocal eta1).mpr eta1.property⟩
    have hXYlocal : Disjoint X Y := by
      apply Finset.disjoint_left.mpr
      intro theta hthetaX hthetaY
      exact (Finset.disjoint_left.mp hXY
        ((hXmemLocal theta).mp hthetaX))
          ((hYmemLocal theta).mp hthetaY)
    have hXnonemptyOn : integerSpanOnNonempty X puncturedSet := by
      rcases hcoherentX.2.1 with ⟨phi, hphi, hphiNe⟩
      exact ⟨phi, integerSpanOn_mono
        (fun theta htheta => (hXmemLocal theta).mpr htheta) hphi, hphiNe⟩
    have hYdegreeLocal (eta : Y) :
        degree (eta : ClassFunction d.H) = (Nat.card d.D : Complex) := by
      exact hYdegree ⟨eta, (hYmemLocal eta).mp eta.property⟩
    have hdegreeLocal :
        degree (chi1X : ClassFunction d.H) =
          (a : Complex) * degree (eta1Y : ClassFunction d.H) := by
      simpa [chi1X, eta1Y] using hdegree
    have hdivXLocal (chi : X) : ∃ ai : Nat,
        degree (chi : ClassFunction d.H) =
          (ai : Complex) * degree (chi1X : ClassFunction d.H) := by
      simpa [chi1X] using
        hdivX ⟨chi, (hXmemLocal chi).mp chi.property⟩
    have hTXLocal : feitSibleyExtensionOn d X TX := by
      have hXto : X ⊆ feitSibleyX d chars :=
        fun theta htheta => (hXmemLocal theta).mp htheta
      exact ⟨isCFLinearIsometryOnSpan_mono hXto hTX.1,
        mapsIntegerSpanToVirtualCharacters_mono hXto hTX.2.1,
        agreesOnIntegerSpanOn_mono hXto hTX.2.2⟩
    have hcrossLocal (chi : X) (eta : Y) :
        scalarProduct G (TX (chi : ClassFunction d.H))
          (TY (eta : ClassFunction d.H)) = 0 := by
      exact hcross
        ⟨chi, (hXmemLocal chi).mp chi.property⟩
        ⟨eta, (hYmemLocal eta).mp eta.property⟩
    have hTYselfLocal (eta : Y) :
        scalarProduct G (TY (eta : ClassFunction d.H))
          (TY (eta : ClassFunction d.H)) = 1 := by
      simpa using hTYgram eta eta
    have hTYoffLocal (eta zeta : Y) (hne : eta ≠ zeta) :
        scalarProduct G (TY (eta : ClassFunction d.H))
          (TY (zeta : ClassFunction d.H)) = 0 := by
      rw [hTYgram eta zeta]
      simp [hne]
    have hcoherentUnion :
        IsCoherentTriple puncturedSet U (Section1.inducedCFLinear d.H) := by
      rcases hcases.1 with hx | ⟨hx, hYcardEq⟩
      · have hlambdaZero : lambda = 0 := by
          rw [hx, mul_zero] at hlambda
          exact hlambda
        have hbridgeZero :
            Section1.inducedCF d.H
                ((chi1 : ClassFunction d.H) -
                  (a : Complex) • (eta1 : ClassFunction d.H)) =
              v - (a : Complex) • TY (eta1 : ClassFunction d.H) := by
          change w = v - (a : Complex) • TY (eta1 : ClassFunction d.H)
          rw [hwDecomp]
          rw [show component =
            -(a : Complex) • TY (eta1 : ClassFunction d.H) +
              (lambda : Complex) • sumY from rfl, hlambdaZero]
          simp
          abel
        exact feitSibley_step6_union_coherence_of_normalized_core
          d chars hchars X Y U hXmemLocal hYmemLocal hUmem TX
          (fun eta : Y => TY (eta : ClassFunction d.H))
          chi1X eta1Y a hXYlocal hXnonemptyOn hYdegreeLocal hdegreeLocal
          hdivXLocal hTXLocal hTYvirt hTYselfLocal hTYoffLocal hcrossLocal
          v hvvirt hvSelf hvorth (by simpa [chi1X, eta1Y] using hbridgeZero)
          (by simpa [eta1Y] using hTYdiffEq)
      · have hlambdaOne : lambda = (a : Int) := by
          rw [hx, mul_one] at hlambda
          exact hlambda
        let EY : Y → ClassFunction G := fun eta =>
          TY (eta : ClassFunction d.H) - sumY
        have hsumEta (eta : Y) :
            scalarProduct G sumY (TY (eta : ClassFunction d.H)) = 1 := by
          simpa [sumY] using hTYsum eta
        have hetaSum (eta : Y) :
            scalarProduct G (TY (eta : ClassFunction d.H)) sumY = 1 := by
          have hstar := Section1.scalarProduct_star_swap
            (G := G) (TY (eta : ClassFunction d.H)) sumY
          rw [hsumEta eta] at hstar
          simpa using hstar.symm
        have hEYvirt (eta : Y) :
            Theory.Character.IsVirtualCharacter (EY eta) := by
          exact Section3.isVirtualCharacter_sub (hTYvirt eta) hsumVirt
        have hEYgram (eta zeta : Y) :
            scalarProduct G (EY eta) (EY zeta) =
              if eta = zeta then 1 else 0 := by
          rw [show EY eta = TY (eta : ClassFunction d.H) - sumY from rfl]
          rw [show EY zeta = TY (zeta : ClassFunction d.H) - sumY from rfl]
          simp only [Section5.scalarProduct_sub_left,
            Section5.scalarProduct_sub_right]
          rw [hTYgram eta zeta, hsumEta zeta, hetaSum eta,
            hsumYSelf, hYcardEq]
          simp
          ring
        have hEYself (eta : Y) : scalarProduct G (EY eta) (EY eta) = 1 := by
          simpa using hEYgram eta eta
        have hEYoff (eta zeta : Y) (hne : eta ≠ zeta) :
            scalarProduct G (EY eta) (EY zeta) = 0 := by
          rw [hEYgram eta zeta]
          simp [hne]
        have hTXsum (chi : X) :
            scalarProduct G (TX (chi : ClassFunction d.H)) sumY = 0 := by
          have hsumEq : sumY =
              (fun g : G => ∑ eta : Y,
                (TY (eta : ClassFunction d.H)) g) := by
            ext g
            simp [sumY]
          calc
            scalarProduct G (TX (chi : ClassFunction d.H)) sumY =
                ∑ eta : Y, scalarProduct G
                  (TX (chi : ClassFunction d.H))
                  (TY (eta : ClassFunction d.H)) := by
              simpa only [← hsumEq] using
                (Section1.scalarProduct_fintype_sum_right
                  (TX (chi : ClassFunction d.H))
                  (fun eta : Y => TY (eta : ClassFunction d.H)))
            _ = 0 := by simp [hcrossLocal]
        have hEYcross (chi : X) (eta : Y) :
            scalarProduct G (TX (chi : ClassFunction d.H)) (EY eta) = 0 := by
          rw [show EY eta = TY (eta : ClassFunction d.H) - sumY from rfl,
            Section5.scalarProduct_sub_right, hcrossLocal chi eta, hTXsum chi]
          ring
        have hvSum : scalarProduct G v sumY = 0 := by
          have hsumEq : sumY =
              (fun g : G => ∑ eta : Y,
                (TY (eta : ClassFunction d.H)) g) := by
            ext g
            simp [sumY]
          calc
            scalarProduct G v sumY =
                ∑ eta : Y,
                  scalarProduct G v (TY (eta : ClassFunction d.H)) := by
              simpa only [← hsumEq] using
                (Section1.scalarProduct_fintype_sum_right v
                  (fun eta : Y => TY (eta : ClassFunction d.H)))
            _ = 0 := by simp [hvorth]
        have hvEY (eta : Y) :
            scalarProduct G v (EY eta) = 0 := by
          rw [show EY eta = TY (eta : ClassFunction d.H) - sumY from rfl,
            Section5.scalarProduct_sub_right, hvorth eta, hvSum]
          ring
        have hEYdiff (eta : Y) :
            Section1.inducedCF d.H
                ((eta : ClassFunction d.H) - (eta1Y : ClassFunction d.H)) =
              EY eta - EY eta1Y := by
          rw [hTYdiffEq eta]
          simp [EY, eta1Y]
        have hbridgeOne :
            Section1.inducedCF d.H
                ((chi1 : ClassFunction d.H) -
                  (a : Complex) • (eta1 : ClassFunction d.H)) =
              v - (a : Complex) • EY eta1Y := by
          change w = v - (a : Complex) • EY eta1Y
          rw [hwDecomp]
          rw [show component =
            -(a : Complex) • TY (eta1 : ClassFunction d.H) +
              (lambda : Complex) • sumY from rfl, hlambdaOne]
          ext g
          simp [EY, eta1Y]
          ring
        exact feitSibley_step6_union_coherence_of_normalized_core
          d chars hchars X Y U hXmemLocal hYmemLocal hUmem TX EY
          chi1X eta1Y a hXYlocal hXnonemptyOn hYdegreeLocal hdegreeLocal
          hdivXLocal hTXLocal hEYvirt hEYself hEYoff hEYcross
          v hvvirt hvSelf hvEY (by simpa [chi1X, eta1Y] using hbridgeOne)
          (by simpa [eta1Y] using hEYdiff)
    have hXneLocal : X.Nonempty := by
      obtain ⟨chi, hchi⟩ := hXne
      exact ⟨chi, (hXmemLocal chi).mpr hchi⟩
    have hYneLocal : Y.Nonempty := by
      obtain ⟨eta, heta⟩ := hYne
      exact ⟨eta, (hYmemLocal eta).mpr heta⟩
    have hYnonemptyOn : integerSpanOnNonempty Y puncturedSet := by
      rcases hcoherentY.2.1 with ⟨phi, hphi, hphiNe⟩
      exact ⟨phi, integerSpanOn_mono
        (fun theta htheta => (hYmemLocal theta).mpr htheta) hphi, hphiNe⟩
    exact feitSibley_step6_extend_union_coherence_core
      d chars hchars p hpprime hpQ1 hZne hZnormal hZle
        X Y U hXmemLocal hYmemLocal hUmem hXneLocal hYneLocal
          hYnonemptyOn hYdegreeLocal hcoherentUnion hstep2

private theorem sylow_map_subtype_of_normalizer_le_appendixIV
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {P0 : Subgroup L}
    {p : Nat} [Fact p.Prime]
    (P : Sylow p L) (hP : (P : Subgroup L) = P0)
    (hnorm :
      Subgroup.normalizer (((P0.map L.subtype : Subgroup G) : Set G)) ≤ L) :
    ∃ Pamb : Sylow p G,
      (Pamb : Subgroup G) = P0.map L.subtype := by
  classical
  let Pmap : Subgroup G := P0.map L.subtype
  have hPcard : Nat.card P0 = p ^ (Nat.card L).factorization p := by
    simpa [← hP] using P.card_eq_multiplicity
  have hPmapCard : Nat.card Pmap = p ^ (Nat.card L).factorization p := by
    calc
      Nat.card Pmap = Nat.card P0 := by
        simpa [Pmap] using
          (Subgroup.card_map_of_injective (K := P0) (f := L.subtype)
            L.subtype_injective)
      _ = p ^ (Nat.card L).factorization p := hPcard
  have hPmapP : IsPGroup p Pmap := by
    have hPp : IsPGroup p ((P : Subgroup L).map L.subtype) :=
      P.isPGroup'.map L.subtype
    rw [hP] at hPp
    simpa [Pmap] using hPp
  have hnotidx : ¬ p ∣ Pmap.index := by
    intro hpidx
    let n : Nat := (Nat.card L).factorization p
    have hpowdvdG : p ^ (n + 1) ∣ Nat.card G := by
      rw [← Subgroup.index_mul_card Pmap, hPmapCard]
      change p ^ ((Nat.card L).factorization p + 1) ∣
        Pmap.index * p ^ (Nat.card L).factorization p
      rcases hpidx with ⟨k, hk⟩
      rw [hk]
      use k
      rw [Nat.pow_succ]
      ac_rfl
    have hpowdvdNorm :
        p ^ (n + 1) ∣
          Nat.card (Subgroup.normalizer ((Pmap : Set G))) := by
      exact Sylow.prime_pow_dvd_card_normalizer hpowdvdG hPmapCard
    have hnormCardDvd :
        Nat.card (Subgroup.normalizer ((Pmap : Set G))) ∣ Nat.card L :=
      Subgroup.card_dvd_of_le (by simpa [Pmap] using hnorm)
    have hpowdvdL : p ^ ((Nat.card L).factorization p + 1) ∣
        Nat.card L := by
      simpa [n] using hpowdvdNorm.trans hnormCardDvd
    exact Nat.pow_succ_factorization_not_dvd
      (Nat.card_pos (α := L)).ne' (Fact.out : Nat.Prime p) hpowdvdL
  let Pamb : Sylow p G := IsPGroup.toSylow hPmapP hnotidx
  exact ⟨Pamb, by
    simp [Pamb, Pmap]⟩

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem FeitSibleyData.QInG_card_coprime_index_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    Nat.Coprime (Nat.card d.QInG) d.QInG.index := by
  classical
  have hQcard : Nat.card d.QInG = Nat.card d.Q := by
    simpa [FeitSibleyData.QInG] using
      (Subgroup.card_map_of_injective (K := d.Q) (f := d.H.subtype)
        d.H.subtype_injective)
  have hQindexH : d.Q.index = Nat.card d.D := by
    simpa [Subgroup.relIndex_top_right] using
      feitSibley_Q_relIndex_top_eq_card_D_appendixIV d
  have hHcard : Nat.card d.H = Nat.card d.D * Nat.card d.Q := by
    have hcard := Subgroup.index_mul_card d.Q
    rw [hQindexH] at hcard
    exact hcard.symm
  refine Nat.coprime_of_dvd ?_
  intro p hpprime hpQcard hpQindex
  let : Fact p.Prime := ⟨hpprime⟩
  have hpQcard' : p ∣ Nat.card d.Q := by
    rw [← hQcard]
    exact hpQcard
  let P : Sylow p d.Q := default
  let PH0 : Subgroup d.H := (P : Subgroup d.Q).map d.Q.subtype
  have hPH0card :
      Nat.card PH0 = p ^ (Nat.card d.Q).factorization p := by
    calc
      Nat.card PH0 = Nat.card (P : Subgroup d.Q) := by
        simpa [PH0] using
          (Subgroup.card_map_of_injective (K := (P : Subgroup d.Q))
            (f := d.Q.subtype) d.Q.subtype_injective)
      _ = p ^ (Nat.card d.Q).factorization p := P.card_eq_multiplicity
  have hPH0P : IsPGroup p PH0 := by
    exact P.isPGroup'.map d.Q.subtype
  have hpDcop : Nat.Coprime p (Nat.card d.D) :=
    Nat.Coprime.of_dvd_left hpQcard' d.card_Q_coprime_card_D
  have hPH0notidx : ¬ p ∣ PH0.index := by
    intro hpidx
    let n : Nat := (Nat.card d.Q).factorization p
    have hpowdvdH : p ^ (n + 1) ∣ Nat.card d.H := by
      rw [← Subgroup.index_mul_card PH0, hPH0card]
      change p ^ ((Nat.card d.Q).factorization p + 1) ∣
        PH0.index * p ^ (Nat.card d.Q).factorization p
      rcases hpidx with ⟨k, hk⟩
      rw [hk]
      use k
      rw [Nat.pow_succ]
      ac_rfl
    have hpowdvdQD : p ^ (n + 1) ∣ Nat.card d.Q * Nat.card d.D := by
      rw [hHcard] at hpowdvdH
      simpa [Nat.mul_comm] using hpowdvdH
    have hpowDcop : Nat.Coprime (p ^ (n + 1)) (Nat.card d.D) :=
      hpDcop.pow_left (n + 1)
    have hpowdvdQ : p ^ ((Nat.card d.Q).factorization p + 1) ∣
        Nat.card d.Q := by
      simpa [n] using hpowDcop.dvd_of_dvd_mul_right hpowdvdQD
    exact Nat.pow_succ_factorization_not_dvd
      (Nat.card_pos (α := d.Q)).ne' hpprime hpowdvdQ
  let PH : Sylow p d.H := IsPGroup.toSylow hPH0P hPH0notidx
  have hPH : (PH : Subgroup d.H) = PH0 := by
    exact IsPGroup.toSylow_coe hPH0P hPH0notidx
  let PG : Subgroup G := PH0.map d.H.subtype
  have hPH0leQ : PH0 ≤ d.Q := by
    intro x hx
    rcases hx with ⟨y, hyP, rfl⟩
    exact y.property
  have hpHcard : p ∣ Nat.card d.H := by
    exact hpQcard'.trans (Subgroup.card_subgroup_dvd_card d.Q)
  have hPHne : (PH : Subgroup d.H) ≠ ⊥ := PH.ne_bot_of_dvd_card hpHcard
  have hPH0ne : PH0 ≠ ⊥ := by simpa [hPH] using hPHne
  have hPGleQ : PG ≤ d.QInG := by
    intro x hx
    rcases hx with ⟨y, hyPH0, rfl⟩
    exact ⟨y, hPH0leQ hyPH0, rfl⟩
  have hnorm : Subgroup.normalizer ((PG : Set G)) ≤ d.H := by
    intro g hg
    by_contra hgH
    have hgInv : g⁻¹ ∉ d.H := by
      intro hgInv
      exact hgH (by simpa using d.H.inv_mem hgInv)
    have hnotle : ¬ PG ≤ (⊥ : Subgroup G) := by
      intro hle
      apply hPH0ne
      have hmapbot : PG = ⊥ := le_bot_iff.mp hle
      have hpre : Subgroup.comap d.H.subtype PG = PH0 := by
        simpa [PG] using
          (Subgroup.comap_map_eq_self_of_injective d.H.subtype_injective PH0)
      rw [← hpre, hmapbot]
      ext x
      simp
    rcases SetLike.not_le_iff_exists.mp hnotle with ⟨x, hxPG, hxBot⟩
    have hxne : x ≠ 1 := by simpa using hxBot
    have hconjPG : g * x * g⁻¹ ∈ PG :=
      (Subgroup.mem_normalizer_iff.mp hg x).1 hxPG
    have hconjQ : g * x * g⁻¹ ∈ d.QInG := hPGleQ hconjPG
    have hconjRight :
        g * x * g⁻¹ ∈
          PFchapter1section1.rightConjugate d.QInG g⁻¹ := by
      change g * x * g⁻¹ ∈ d.QInG.conjBy (g⁻¹)⁻¹
      exact Subgroup.mem_map.mpr ⟨x, hPGleQ hxPG, by simp⟩
    have hconjBot : g * x * g⁻¹ ∈ (⊥ : Subgroup G) :=
      (d.Q_TI_in_G g⁻¹ hgInv).le_bot ⟨hconjQ, hconjRight⟩
    have hconjOne : g * x * g⁻¹ = 1 := by simpa using hconjBot
    apply hxne
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [hconjOne]; simp
  obtain ⟨Pamb, hPamb⟩ :=
    sylow_map_subtype_of_normalizer_le_appendixIV PH hPH hnorm
  have hindexDvd : d.QInG.index ∣ PG.index :=
    Subgroup.index_dvd_of_le hPGleQ
  have hpPGindex : p ∣ PG.index := hpQindex.trans hindexDvd
  have hpPambIndex : p ∣ (Pamb : Subgroup G).index := by
    simpa [hPamb] using hpPGindex
  exact Pamb.not_dvd_index hpPambIndex

private theorem FeitSibleyData.pElement_mem_Q_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (p : Nat) (hpprime : p.Prime) (hpQcard : p ∣ Nat.card d.Q)
    (x : d.H) (hxOrder : ∃ k : Nat, orderOf x = p ^ k) :
    (x : d.H) ∈ d.Q := by
  classical
  let : Fact p.Prime := ⟨hpprime⟩
  let : d.Q.Normal := d.Q_normal
  let P : Subgroup d.H := Subgroup.zpowers x
  have hP : IsPGroup p P := by
    rw [IsPGroup.iff_orderOf]
    intro y
    obtain ⟨k, hxOrder⟩ := hxOrder
    have hyDvd : orderOf (y : d.H) ∣ p ^ k := by
      rw [← hxOrder]
      exact orderOf_dvd_of_mem_zpowers y.property
    obtain ⟨m, _hmle, hm⟩ := (Nat.dvd_prime_pow hpprime).mp hyDvd
    refine ⟨m, ?_⟩
    rw [← Subgroup.orderOf_coe y]
    exact hm
  let pi : d.H →* d.H ⧸ d.Q := QuotientGroup.mk' d.Q
  let Pbar : Subgroup (d.H ⧸ d.Q) := P.map pi
  have hPbar : IsPGroup p Pbar := hP.map pi
  have hpDcop : Nat.Coprime p (Nat.card d.D) :=
    Nat.Coprime.of_dvd_left hpQcard d.card_Q_coprime_card_D
  have hpD : ¬ p ∣ Nat.card d.D :=
    hpprime.coprime_iff_not_dvd.mp hpDcop
  have hQindex : d.Q.index = Nat.card d.D := by
    simpa [Subgroup.relIndex_top_right] using
      feitSibley_Q_relIndex_top_eq_card_D_appendixIV d
  have hquotCard : Nat.card (d.H ⧸ d.Q) = Nat.card d.D := by
    rw [← Subgroup.index_eq_card, hQindex]
  have hpQuot : ¬ p ∣ Nat.card (d.H ⧸ d.Q) := by
    rw [hquotCard]
    exact hpD
  have hpPbar : ¬ p ∣ Nat.card Pbar := by
    intro hp
    exact hpQuot (hp.trans (Subgroup.card_subgroup_dvd_card Pbar))
  have hPbarCard : Nat.card Pbar = 1 :=
    (hPbar.card_eq_or_dvd).resolve_right hpPbar
  have hPbarBot : Pbar = ⊥ :=
    (Subgroup.card_le_one_iff_eq_bot Pbar).mp (by omega)
  have hxP : (x : d.H) ∈ P := Subgroup.mem_zpowers x
  have hpi : pi x ∈ Pbar := Subgroup.mem_map.mpr ⟨x, hxP, rfl⟩
  rw [hPbarBot] at hpi
  have hker : x ∈ pi.ker := by
    simpa [MonoidHom.mem_ker] using hpi
  simpa [pi, QuotientGroup.ker_mk'] using hker

private theorem FeitSibleyData.QInG_elementCentralizer_le_H_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    {q : G} (hq : q ∈ d.QInG) (hqne : q ≠ 1) :
    Section2.elementCentralizer q ≤ d.H := by
  intro c hc
  by_contra hcH
  have hcomm : c * q = q * c := by
    unfold Section2.elementCentralizer at hc
    rw [Subgroup.mem_centralizer_iff] at hc
    exact (hc q (by simp)).symm
  have hqRight :
      q ∈ PFchapter1section1.rightConjugate d.QInG c := by
    change q ∈ d.QInG.conjBy c⁻¹
    apply Subgroup.mem_map.mpr
    refine ⟨q, hq, ?_⟩
    change c⁻¹ * q * (c⁻¹)⁻¹ = q
    rw [inv_inv]
    calc
      c⁻¹ * q * c = c⁻¹ * (q * c) := by simp [mul_assoc]
      _ = c⁻¹ * (c * q) := by rw [hcomm]
      _ = q := by simp []
  have hqBot : q ∈ (⊥ : Subgroup G) :=
    (d.Q_TI_in_G c hcH).le_bot ⟨hq, hqRight⟩
  exact hqne (by simpa using hqBot)

private theorem FeitSibleyData.mem_map_Z_of_mem_H_mem_class_meets_map_Z_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (hpQcard : p ∣ Nat.card d.Q)
    (Z : Subgroup d.H) (hZnormal : Z.Normal) (hZleQ1 : Z ≤ d.Q1)
    (c : ConjClasses G) {u : G} (huH : u ∈ d.H) (huc : u ∈ c.carrier)
    (hc : Section6.conjugacyClassMeetsPuncturedSubgroup
      c (Z.map d.H.subtype)) :
    u ∈ Z.map d.H.subtype := by
  classical
  let : Fact p.Prime := ⟨hpprime⟩
  rcases hc with ⟨z, hzc, hzZG, hzne⟩
  rcases Subgroup.mem_map.mp hzZG with ⟨zH, hzZ, hzval⟩
  let uH : d.H := ⟨u, huH⟩
  have hmkZ : ConjClasses.mk z = c :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 hzc
  have hmkU : ConjClasses.mk u = c :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 huc
  have hconj : IsConj z u :=
    (ConjClasses.mk_eq_mk_iff_isConj).1 (hmkZ.trans hmkU.symm)
  rcases isConj_iff.mp hconj with ⟨g, hg⟩
  have hzQ1 : zH ∈ d.Q1 := hZleQ1 hzZ
  let zQ1 : d.Q1 := ⟨zH, hzQ1⟩
  obtain ⟨k, hzk⟩ := (IsPGroup.iff_orderOf.mp hpQ1) zQ1
  have hzOrderG : orderOf z = p ^ k := by
    rw [← hzval]
    calc
      orderOf ((zH : d.H) : G) = orderOf zH := Subgroup.orderOf_coe zH
      _ = orderOf zQ1 := by
        exact Subgroup.orderOf_coe zQ1
      _ = p ^ k := hzk
  have huOrderG : orderOf u = p ^ k := by
    have horder := orderOf_injective (MulAut.conj g).toMonoidHom
      (MulEquiv.injective (MulAut.conj g)) z
    change orderOf (g * z * g⁻¹) = orderOf z at horder
    rw [hg] at horder
    exact horder.trans hzOrderG
  have huOrderH : orderOf uH = p ^ k := by
    rw [← Subgroup.orderOf_coe uH]
    exact huOrderG
  have huQ : uH ∈ d.Q :=
    d.pElement_mem_Q_appendixIV p hpprime hpQcard uH ⟨k, huOrderH⟩
  have huQG : u ∈ d.QInG :=
    Subgroup.mem_map.mpr ⟨uH, huQ, rfl⟩
  have hzQG : z ∈ d.QInG := by
    apply Subgroup.mem_map.mpr
    refine ⟨zH, d.Q1_le_Q hzQ1, ?_⟩
    exact hzval
  have huNe : u ≠ 1 := by
    intro hu
    apply hzne
    calc
      z = g⁻¹ * u * g := by rw [← hg]; group
      _ = 1 := by rw [hu]; simp
  have hgH : g ∈ d.H := by
    by_contra hgH
    have hgInv : g⁻¹ ∉ d.H := by
      intro hgInv
      exact hgH (by simpa using d.H.inv_mem hgInv)
    have huRight :
        u ∈ PFchapter1section1.rightConjugate d.QInG g⁻¹ := by
      change u ∈ d.QInG.conjBy (g⁻¹)⁻¹
      apply Subgroup.mem_map.mpr
      refine ⟨z, hzQG, ?_⟩
      simpa using hg
    have huBot : u ∈ (⊥ : Subgroup G) :=
      (d.Q_TI_in_G g⁻¹ hgInv).le_bot ⟨huQG, huRight⟩
    exact huNe (by simpa using huBot)
  let gH : d.H := ⟨g, hgH⟩
  have hconjZ : gH * zH * gH⁻¹ ∈ Z :=
    hZnormal.conj_mem zH hzZ gH
  apply Subgroup.mem_map.mpr
  refine ⟨gH * zH * gH⁻¹, hconjZ, ?_⟩
  change g * (zH : G) * g⁻¹ = u
  have hzval' : (zH : G) = z := hzval
  rw [hzval']
  exact hg

private theorem FeitSibleyData.Q_commutes_Z_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (Z : Subgroup d.H)
    (hZleQ1 : Z ≤ d.Q1)
    (hZleCenter :
      Z ≤ Subgroup.map d.Q1.subtype (Subgroup.center d.Q1))
    (q : d.Q) (z : Z) :
    (q : d.H) * (z : d.H) = (z : d.H) * (q : d.H) := by
  obtain ⟨q1, hq1⟩ := d.exists_Q1_inner_conjugator q
  let zQ1 : d.Q1 := ⟨z, hZleQ1 z.property⟩
  have hzCenterH := hZleCenter z.property
  rcases Subgroup.mem_map.mp hzCenterH with ⟨zc, hzc, hzval⟩
  have hzcEq : zc = zQ1 := by
    apply Subtype.ext
    exact hzval
  have hzCenter : zQ1 ∈ Subgroup.center d.Q1 := hzcEq ▸ hzc
  have hq1Comm : (q1 : d.H) * (zQ1 : d.H) =
      (zQ1 : d.H) * (q1 : d.H) := by
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzCenter q1)
  have hq1Conj :
      (q1 : d.H) * (zQ1 : d.H) * (q1 : d.H)⁻¹ = (zQ1 : d.H) := by
    rw [hq1Comm]
    simp
  have hqConj :
      (q : d.H) * (zQ1 : d.H) * (q : d.H)⁻¹ = (zQ1 : d.H) := by
    rw [hq1 zQ1, hq1Conj]
  have hmul := congrArg (fun x : d.H => x * (q : d.H)) hqConj
  simpa [zQ1, mul_assoc] using hmul

private theorem FeitSibleyData.not_isConj_inv_of_mem_map_Z_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (hDodd : Odd (Nat.card d.D))
    (Z : Subgroup d.H)
    (hZleQ1 : Z ≤ d.Q1)
    (hZleCenter :
      Z ≤ Subgroup.map d.Q1.subtype (Subgroup.center d.Q1))
    (z : Z.map d.H.subtype) (hz : (z : G) ≠ 1) :
    ¬ IsConj (z : G) ((z : G)⁻¹) := by
  classical
  intro hconj
  rcases Subgroup.mem_map.mp z.property with ⟨zH, hzZ, hzval⟩
  have hzval' : (zH : G) = (z : G) := hzval
  have hzQ1 : zH ∈ d.Q1 := hZleQ1 hzZ
  let zQ1 : d.Q1 := ⟨zH, hzQ1⟩
  have hzQ1ne : zQ1 ≠ 1 := by
    intro hzOne
    apply hz
    rw [← hzval']
    simpa [zQ1] using congrArg Subtype.val hzOne
  have hzQG : (z : G) ∈ d.QInG := by
    apply Subgroup.mem_map.mpr
    refine ⟨zH, d.Q1_le_Q hzQ1, ?_⟩
    exact hzval
  have hzinvQG : ((z : G)⁻¹) ∈ d.QInG := d.QInG.inv_mem hzQG
  rcases isConj_iff.mp hconj with ⟨g, hg⟩
  have hgH : g ∈ d.H := by
    by_contra hgH
    have hgInv : g⁻¹ ∉ d.H := by
      intro hgInv
      exact hgH (by simpa using d.H.inv_mem hgInv)
    have hzinvRight :
        (z : G)⁻¹ ∈
          PFchapter1section1.rightConjugate d.QInG g⁻¹ := by
      change (z : G)⁻¹ ∈ d.QInG.conjBy (g⁻¹)⁻¹
      apply Subgroup.mem_map.mpr
      refine ⟨(z : G), hzQG, ?_⟩
      simpa using hg
    have hzinvBot : (z : G)⁻¹ ∈ (⊥ : Subgroup G) :=
      (d.Q_TI_in_G g⁻¹ hgInv).le_bot ⟨hzinvQG, hzinvRight⟩
    have hzinvOne : (z : G)⁻¹ = 1 := by simpa using hzinvBot
    exact hz (inv_eq_one.mp hzinvOne)
  let gH : d.H := ⟨g, hgH⟩
  have hgConjH : gH * zH * gH⁻¹ = zH⁻¹ := by
    apply Subtype.ext
    change g * (zH : G) * g⁻¹ = (zH : G)⁻¹
    simpa only [hzval'] using hg
  obtain ⟨q, e, hqe⟩ := d.exists_Q_mul_D gH
  let zZ : Z := ⟨zH, hzZ⟩
  have hqComm : (q : d.H) * (zH : d.H) =
      (zH : d.H) * (q : d.H) := by
    simpa [zZ] using d.Q_commutes_Z_appendixIV Z hZleQ1 hZleCenter q zZ
  have hqConjInv :
      (q : d.H) * zH⁻¹ * (q : d.H)⁻¹ = zH⁻¹ := by
    have hcommInv : (q : d.H) * zH⁻¹ = zH⁻¹ * (q : d.H) :=
      (show Commute (q : d.H) zH from hqComm).inv_right
    rw [hcommInv]
    simp
  have heConj :
      (e : d.H) * zH * (e : d.H)⁻¹ = zH⁻¹ := by
    have hqeq :
        (q : d.H) * ((e : d.H) * zH * (e : d.H)⁻¹) * (q : d.H)⁻¹ =
          (q : d.H) * zH⁻¹ * (q : d.H)⁻¹ := by
      rw [hqConjInv]
      rw [← hgConjH]
      rw [← hqe]
      group
    have hcancel := congrArg
      (fun x : d.H => (q : d.H)⁻¹ * x * (q : d.H)) hqeq
    simpa [mul_assoc] using hcancel
  let e2 : d.D := e * e
  have he2Fix : (e2 : d.H) * (zQ1 : d.H) * (e2 : d.H)⁻¹ =
      (zQ1 : d.H) := by
    change ((e : d.H) * (e : d.H)) * zH *
        ((e : d.H) * (e : d.H))⁻¹ = zH
    calc
      ((e : d.H) * (e : d.H)) * zH *
          ((e : d.H) * (e : d.H))⁻¹ =
          (e : d.H) * ((e : d.H) * zH * (e : d.H)⁻¹) *
            (e : d.H)⁻¹ := by group
      _ = (e : d.H) * zH⁻¹ * (e : d.H)⁻¹ := by rw [heConj]
      _ = ((e : d.H) * zH * (e : d.H)⁻¹)⁻¹ := by group
      _ = (zH⁻¹)⁻¹ := by rw [heConj]
      _ = zH := by simp
  have he2OneH : (e2 : d.H) = 1 := by
    by_contra he2ne
    exact hzQ1ne (d.D_fixedPointFree_on_Q1 e2 he2ne zQ1 he2Fix)
  have he2One : e * e = 1 := by
    apply Subtype.ext
    exact he2OneH
  have heEqInv : e = e⁻¹ := eq_inv_of_mul_eq_one_left he2One
  have heOne : e = 1 :=
    Section1.eq_one_of_conj_eq_inv_of_odd_card
      (G := d.D) hDodd (g := e) (x := 1) (by simpa using heEqInv)
  have hqeqg : (q : d.H) = gH := by
    simpa [heOne] using hqe
  have hqConj : (q : d.H) * zH * (q : d.H)⁻¹ = zH := by
    rw [hqComm]
    simp
  have hzEqInvH : zH = zH⁻¹ := by
    calc
      zH = (q : d.H) * zH * (q : d.H)⁻¹ := hqConj.symm
      _ = gH * zH * gH⁻¹ := by rw [hqeqg]
      _ = zH⁻¹ := hgConjH
  have hzEqInvQ1 : zQ1 = zQ1⁻¹ := by
    apply Subtype.ext
    exact hzEqInvH
  have hzOne : zQ1 = 1 :=
    Section1.eq_one_of_conj_eq_inv_of_odd_card
      (G := d.Q1) d.Q1_odd (g := zQ1) (x := 1) (by simpa using hzEqInvQ1)
  exact hzQ1ne hzOne

private theorem FeitSibleyData.elementCentralizer_eq_QInG_of_mem_map_Z_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (Z : Subgroup d.H)
    (hZleQ1 : Z ≤ d.Q1)
    (hZleCenter :
      Z ≤ Subgroup.map d.Q1.subtype (Subgroup.center d.Q1))
    (z : Z.map d.H.subtype) (hz : (z : G) ≠ 1) :
    Section2.elementCentralizer (z : G) = d.QInG := by
  classical
  rcases Subgroup.mem_map.mp z.property with ⟨zH, hzZ, hzval⟩
  have hzval' : (zH : G) = (z : G) := hzval
  have hzQ1 : zH ∈ d.Q1 := hZleQ1 hzZ
  let zQ1 : d.Q1 := ⟨zH, hzQ1⟩
  have hzQ1ne : zQ1 ≠ 1 := by
    intro hzOne
    apply hz
    rw [← hzval']
    simpa [zQ1] using congrArg Subtype.val hzOne
  have hzQG : (z : G) ∈ d.QInG := by
    apply Subgroup.mem_map.mpr
    refine ⟨zH, d.Q1_le_Q hzQ1, ?_⟩
    exact hzval
  apply le_antisymm
  · intro c hc
    have hcH : c ∈ d.H :=
      d.QInG_elementCentralizer_le_H_appendixIV hzQG hz hc
    let cH : d.H := ⟨c, hcH⟩
    obtain ⟨q, e, hqe⟩ := d.exists_Q_mul_D cH
    let zZ : Z := ⟨zH, hzZ⟩
    have hqComm : (q : d.H) * zH = zH * (q : d.H) := by
      simpa [zZ] using d.Q_commutes_Z_appendixIV Z hZleQ1 hZleCenter q zZ
    have hcCommG : c * (z : G) = (z : G) * c := by
      unfold Section2.elementCentralizer at hc
      rw [Subgroup.mem_centralizer_iff] at hc
      exact (hc (z : G) (by simp)).symm
    have hcCommH : cH * zH = zH * cH := by
      apply Subtype.ext
      change c * (zH : G) = (zH : G) * c
      simpa only [hzval'] using hcCommG
    have hqeComm :
        ((q : d.H) * (e : d.H)) * zH =
          zH * ((q : d.H) * (e : d.H)) := by
      rw [hqe]
      exact hcCommH
    have heComm : (e : d.H) * zH = zH * (e : d.H) := by
      calc
        (e : d.H) * zH =
            (q : d.H)⁻¹ * (((q : d.H) * (e : d.H)) * zH) := by group
        _ = (q : d.H)⁻¹ *
            (zH * ((q : d.H) * (e : d.H))) := by rw [hqeComm]
        _ = (q : d.H)⁻¹ * ((zH * (q : d.H)) * (e : d.H)) := by group
        _ = (q : d.H)⁻¹ * (((q : d.H) * zH) * (e : d.H)) := by
          rw [hqComm]
        _ = zH * (e : d.H) := by group
    have heFix :
        (e : d.H) * (zQ1 : d.H) * (e : d.H)⁻¹ = (zQ1 : d.H) := by
      change (e : d.H) * zH * (e : d.H)⁻¹ = zH
      rw [heComm]
      simp
    have heOneH : (e : d.H) = 1 := by
      by_contra heNe
      exact hzQ1ne (d.D_fixedPointFree_on_Q1 e heNe zQ1 heFix)
    have heOne : e = 1 := by
      apply Subtype.ext
      exact heOneH
    have hqeqc : (q : d.H) = cH := by
      simpa [heOne] using hqe
    apply Subgroup.mem_map.mpr
    refine ⟨q, q.property, ?_⟩
    exact congrArg Subtype.val hqeqc
  · intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨qH, hqQ, hqval⟩
    let qQ : d.Q := ⟨qH, hqQ⟩
    let zZ : Z := ⟨zH, hzZ⟩
    have hqCommH : (qQ : d.H) * zH = zH * (qQ : d.H) := by
      simpa [qQ, zZ] using
        d.Q_commutes_Z_appendixIV Z hZleQ1 hZleCenter qQ zZ
    unfold Section2.elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp at hy
    subst y
    have hqval' : (qH : G) = q := hqval
    have hcommG := congrArg (fun x : d.H => (x : G)) hqCommH
    change (qH : G) * (zH : G) = (zH : G) * (qH : G) at hcommG
    rw [hqval', hzval'] at hcommG
    exact hcommG.symm

private def appendixIV_step7_elementCentralizerEquivStabilizer
    {G : Type u} [Group G] (z : G) :
    Section2.elementCentralizer z ≃ MulAction.stabilizer (ConjAct G) z := by
  refine
    { toFun := fun c => ⟨ConjAct.toConjAct (c : G), ?_⟩
      invFun := fun c => ⟨ConjAct.ofConjAct (c : ConjAct G), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [MulAction.mem_stabilizer_iff]
    have hcprop := c.2
    unfold Section2.elementCentralizer at hcprop
    rw [Subgroup.mem_centralizer_iff] at hcprop
    have hc : (c : G) * z = z * (c : G) := (hcprop z (by simp)).symm
    simp [ConjAct.smul_def, mul_assoc, hc]
  · have hcprop := c.2
    rw [MulAction.mem_stabilizer_iff] at hcprop
    unfold Section2.elementCentralizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simp at hy
    subst y
    rw [ConjAct.smul_def] at hcprop
    let g : G := ConjAct.ofConjAct (c : ConjAct G)
    have h := congrArg (fun t : G => t * g) hcprop
    simpa [g, mul_assoc] using h.symm
  · intro c
    rfl
  · intro c
    ext
    rfl

private theorem FeitSibleyData.card_conjClass_eq_QInG_index_of_mem_map_Z_appendixIV
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (Z : Subgroup d.H)
    (hZleQ1 : Z ≤ d.Q1)
    (hZleCenter :
      Z ≤ Subgroup.map d.Q1.subtype (Subgroup.center d.Q1))
    (z : Z.map d.H.subtype) (hz : (z : G) ≠ 1) :
    Nat.card (ConjClasses.mk (z : G)).carrier = d.QInG.index := by
  classical
  have hcard := ConjClasses.card_carrier (G := G) (z : G)
  rw [← Nat.card_eq_fintype_card] at hcard
  rw [← Nat.card_eq_fintype_card] at hcard
  rw [← Nat.card_eq_fintype_card] at hcard
  have hstab : Nat.card (MulAction.stabilizer (ConjAct G) (z : G)) =
      Nat.card (Section2.elementCentralizer (z : G)) :=
    Nat.card_congr
      (appendixIV_step7_elementCentralizerEquivStabilizer (z : G)).symm
  rw [hstab,
    d.elementCentralizer_eq_QInG_of_mem_map_Z_appendixIV
      Z hZleQ1 hZleCenter z hz] at hcard
  rw [hcard, ← d.QInG.index_mul_card]
  simp

private theorem step7_congr_zero_of_dvd
    {n m : Nat} (hdiv : n ∣ m) :
    algebraicIntegerCongruentModNat n (m : Complex) 0 := by
  rcases hdiv with ⟨k, rfl⟩
  unfold algebraicIntegerCongruentModNat
  constructor
  · exact_mod_cast
      (isIntegral_algebraMap (R := Int) (A := Complex) (x := ((n * k : Nat) : Int)))
  constructor
  · exact_mod_cast
      (isIntegral_algebraMap (R := Int) (A := Complex) (x := (0 : Int)))
  · by_cases hn : n = 0
    · subst n
      simp
      exact_mod_cast
        (isIntegral_algebraMap (R := Int) (A := Complex) (x := (0 : Int)))
    · have hnC : (n : Complex) ≠ 0 := by exact_mod_cast hn
      convert (isIntegral_algebraMap (R := Int) (A := Complex) (x := (k : Int))) using 1
      field_simp [hnC]
      norm_num [Nat.cast_mul]

private theorem step7_congr_refl
    {n : Nat} {alpha : Complex} (halpha : IsIntegral Int alpha) :
    algebraicIntegerCongruentModNat n alpha alpha := by
  unfold algebraicIntegerCongruentModNat
  exact ⟨halpha, halpha, by simpa using (isIntegral_zero : IsIntegral Int (0 : Complex))⟩

private theorem step7_congr_mul_right
    {n : Nat} {alpha beta gamma : Complex}
    (h : algebraicIntegerCongruentModNat n alpha beta)
    (hgamma : IsIntegral Int gamma) :
    algebraicIntegerCongruentModNat n (alpha * gamma) (beta * gamma) := by
  rcases h with ⟨halpha, hbeta, hq⟩
  unfold algebraicIntegerCongruentModNat
  refine ⟨halpha.mul hgamma, hbeta.mul hgamma, ?_⟩
  have hqgamma : IsIntegral Int (((alpha - beta) / (n : Complex)) * gamma) :=
    hq.mul hgamma
  convert hqgamma using 1
  ring


private theorem step7_congr_sum
    {n : Nat} {ι : Type*} (s : Finset ι) (alpha beta : ι → Complex)
    (h : ∀ i ∈ s, algebraicIntegerCongruentModNat n (alpha i) (beta i)) :
    algebraicIntegerCongruentModNat n (s.sum alpha) (s.sum beta) := by
  classical
  unfold algebraicIntegerCongruentModNat
  constructor
  · exact IsIntegral.sum (s := s) (fun i => alpha i) (fun i hi => (h i hi).1)
  constructor
  · exact IsIntegral.sum (s := s) (fun i => beta i) (fun i hi => (h i hi).2.1)
  · have hq : IsIntegral Int
        (s.sum fun i => (alpha i - beta i) / (n : Complex)) :=
      IsIntegral.sum (s := s) (fun i => (alpha i - beta i) / (n : Complex))
        (fun i hi => (h i hi).2.2)
    convert hq using 1
    rw [← Finset.sum_sub_distrib, Finset.sum_div]

private theorem step7_congr_trans
    {n : Nat} {alpha beta gamma : Complex}
    (h1 : algebraicIntegerCongruentModNat n alpha beta)
    (h2 : algebraicIntegerCongruentModNat n beta gamma) :
    algebraicIntegerCongruentModNat n alpha gamma := by
  rcases h1 with ⟨halpha, _hbeta, hq1⟩
  rcases h2 with ⟨_hbeta', hgamma, hq2⟩
  unfold algebraicIntegerCongruentModNat
  refine ⟨halpha, hgamma, ?_⟩
  have hq : IsIntegral Int
      (((alpha - beta) / (n : Complex)) + ((beta - gamma) / (n : Complex))) :=
    hq1.add hq2
  convert hq using 1
  ring

private theorem step7_congr_symm
    {n : Nat} {alpha beta : Complex}
    (h : algebraicIntegerCongruentModNat n alpha beta) :
    algebraicIntegerCongruentModNat n beta alpha := by
  rcases h with ⟨halpha, hbeta, hq⟩
  unfold algebraicIntegerCongruentModNat
  refine ⟨hbeta, halpha, ?_⟩
  convert hq.neg using 1
  ring

private theorem step7_congr_cancel_nat_mul_left
    {n C : Nat} (hn : n ≠ 0) (hcop : Nat.Coprime C n)
    {alpha beta : Complex} (halpha : IsIntegral Int alpha)
    (hbeta : IsIntegral Int beta)
    (h : algebraicIntegerCongruentModNat n
      ((C : Complex) * alpha) ((C : Complex) * beta)) :
    algebraicIntegerCongruentModNat n alpha beta := by
  rcases h with ⟨_hCalpha, _hCbeta, hq⟩
  rcases hcop.isCoprime with ⟨u, v, huv⟩
  have hbez : (u : Complex) * (C : Complex) + (v : Complex) * (n : Complex) = 1 := by
    exact_mod_cast huv
  unfold algebraicIntegerCongruentModNat
  refine ⟨halpha, hbeta, ?_⟩
  have huInt : IsIntegral Int (u : Complex) := by
    exact_mod_cast (isIntegral_algebraMap (R := Int) (A := Complex) (x := u))
  have hvInt : IsIntegral Int (v : Complex) := by
    exact_mod_cast (isIntegral_algebraMap (R := Int) (A := Complex) (x := v))
  have hlin : IsIntegral Int
      ((u : Complex) * (((C : Complex) * alpha - (C : Complex) * beta) /
          (n : Complex)) + (v : Complex) * (alpha - beta)) :=
    (huInt.mul hq).add (hvInt.mul (halpha.sub hbeta))
  have hrewrite : (alpha - beta) / (n : Complex) =
      (u : Complex) * (((C : Complex) * alpha - (C : Complex) * beta) /
          (n : Complex)) + (v : Complex) * (alpha - beta) := by
    have hnC : (n : Complex) ≠ 0 := by exact_mod_cast hn
    field_simp [hnC]
    nth_rewrite 1 [← one_mul (alpha - beta)]
    rw [← hbez]
    ring
  rw [hrewrite]
  exact hlin

private theorem step7_congr_cancel_add_right
    {n : Nat} {alpha beta gamma : Complex}
    (halpha : IsIntegral Int alpha) (hbeta : IsIntegral Int beta)
    (h : algebraicIntegerCongruentModNat n
      (alpha + gamma) (beta + gamma)) :
    algebraicIntegerCongruentModNat n alpha beta := by
  rcases h with ⟨_halphagamma, _hbetagamma, hq⟩
  unfold algebraicIntegerCongruentModNat
  refine ⟨halpha, hbeta, ?_⟩
  convert hq using 1
  ring

private theorem step7_natCast_isIntegral (m : Nat) :
    IsIntegral Int (m : Complex) := by
  exact_mod_cast (isIntegral_algebraMap (R := Int) (A := Complex) (x := (m : Int)))

private theorem step7_value_isIntegral_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {psi : ClassFunction G}
    (hpsi : IsIrreducibleCharacterOnGroup psi) (g : G) :
    IsIntegral Int (psi g) := by
  rcases hpsi with ⟨_n, rho, _hrho, hpsiEq⟩
  rw [hpsiEq]
  exact Theory.Character.representation_character_isIntegral (ρ := rho) g

private theorem step7_character_one_ne_zero_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {psi : ClassFunction G}
    (hpsi : IsIrreducibleCharacterOnGroup psi) : psi 1 ≠ 0 := by
  have hdegree : degree psi ≠ 0 :=
    Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup psi hpsi
  simpa [degree] using hdegree

private theorem step7_card_actor_dvd_of_fixedPointFree
    {A Omega : Type*} [Group A] [Finite A] [Finite Omega] [MulAction A Omega]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : Omega, a • x = x → False) :
    Nat.card A ∣ Nat.card Omega := by
  classical
  have hstab : ∀ x : Omega, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra haNotBot
    have haNe : a ≠ 1 := by
      intro ha1
      apply haNotBot
      simp [ha1]
    exact hfree a haNe x hax
  have hcardEquiv := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod] at hcardEquiv
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A Omega)), by
    rw [mul_comm]
    exact hcardEquiv⟩

private theorem step7_conj_mem_conjClass
    {G : Type u} [Group G] {c : ConjClasses G} {x : G}
    (hx : x ∈ c.carrier) (g : G) :
    g * x * g⁻¹ ∈ c.carrier := by
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hx ⊢
  rw [← hx]
  rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  refine ⟨g⁻¹, ?_⟩
  simp [mul_assoc]

private theorem step7_conj_product_eq
    {G : Type u} [Group G] (g u v : G) :
    (g * u * g⁻¹) * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by
  simp [mul_assoc]

private def step7_classProductPairEquiv
    {G : Type u} [Group G] [Finite G]
    (i j s : ConjClasses G) :
    {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧
      uv.1 * uv.2 ∈ s.carrier} ≃
      Sigma (fun x : s.carrier =>
        {pair : i.carrier × j.carrier // pair.1.1 * pair.2.1 = (x : G)}) := by
  classical
  refine
    { toFun := fun uv =>
        ⟨⟨uv.1.1 * uv.1.2, uv.2.2.2⟩,
          ⟨(⟨uv.1.1, uv.2.1⟩, ⟨uv.1.2, uv.2.2.1⟩), rfl⟩⟩
      invFun := fun x =>
        ⟨((x.2.1.1 : G), (x.2.1.2 : G)), ⟨x.2.1.1.2, x.2.1.2.2, by
          have hprod : (x.2.1.1 : G) * (x.2.1.2 : G) = (x.1 : G) := x.2.2
          rw [hprod]
          exact x.1.2⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro uv
    rcases uv with ⟨⟨u, v⟩, hu, hv, huv⟩
    rfl
  · intro x
    rcases x with ⟨x, y⟩
    rcases x with ⟨xv, hxv⟩
    rcases y with ⟨uv, huv⟩
    rcases uv with ⟨u, v⟩
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    simp at huv
    subst xv
    rfl

private theorem step7_classProductPair_card
    {G : Type u} [Group G] [Finite G]
    {a : ConjClasses G → ConjClasses G → ConjClasses G → Nat}
    (hdata : classProductCoefficientData a)
    (i j s : ConjClasses G) :
    Nat.card {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧
      uv.1 * uv.2 ∈ s.carrier} = a i j s * Nat.card s.carrier := by
  classical
  calc
    Nat.card {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧
        uv.1 * uv.2 ∈ s.carrier} =
        Nat.card (Sigma (fun x : s.carrier =>
          {pair : i.carrier × j.carrier //
            pair.1.1 * pair.2.1 = (x : G)})) := by
      exact Nat.card_congr (step7_classProductPairEquiv i j s)
    _ = ∑ x : s.carrier,
        Nat.card {pair : i.carrier × j.carrier //
          pair.1.1 * pair.2.1 = (x : G)} := by
      rw [Nat.card_sigma]
    _ = ∑ _x : s.carrier, a i j s := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact (hdata i j s x x.2).symm
    _ = a i j s * Nat.card s.carrier := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [@Nat.card_eq_fintype_card s.carrier (inferInstanceAs (Fintype s.carrier))]
      simp [mul_comm]

private def step7_classProductFiberConjEquiv
    {G : Type u} [Group G]
    {i j : ConjClasses G} {x y : G} (hxy : IsConj x y) :
    {pair : i.carrier × j.carrier // pair.1.1 * pair.2.1 = x} ≃
      {pair : i.carrier × j.carrier // pair.1.1 * pair.2.1 = y} := by
  let g : G := Classical.choose (isConj_iff.mp hxy)
  have hg : g * x * g⁻¹ = y := Classical.choose_spec (isConj_iff.mp hxy)
  refine
    { toFun := fun pair =>
        ⟨(⟨g * pair.1.1.1 * g⁻¹, step7_conj_mem_conjClass pair.1.1.2 g⟩,
          ⟨g * pair.1.2.1 * g⁻¹, step7_conj_mem_conjClass pair.1.2.2 g⟩), ?_⟩
      invFun := fun pair =>
        ⟨(⟨g⁻¹ * pair.1.1.1 * (g⁻¹)⁻¹,
            step7_conj_mem_conjClass pair.1.1.2 g⁻¹⟩,
          ⟨g⁻¹ * pair.1.2.1 * (g⁻¹)⁻¹,
            step7_conj_mem_conjClass pair.1.2.2 g⁻¹⟩), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [step7_conj_product_eq, pair.2, hg]
  · have hg' : g⁻¹ * y * (g⁻¹)⁻¹ = x := by
      rw [← hg]
      simp [mul_assoc]
    rw [step7_conj_product_eq, pair.2, hg']
  · intro pair
    apply Subtype.ext
    rcases pair with ⟨pair, _hpair⟩
    rcases pair with ⟨a, b⟩
    rcases a with ⟨a, _ha⟩
    rcases b with ⟨b, _hb⟩
    simp [mul_assoc]
  · intro pair
    apply Subtype.ext
    rcases pair with ⟨pair, _hpair⟩
    rcases pair with ⟨a, b⟩
    rcases a with ⟨a, _ha⟩
    rcases b with ⟨b, _hb⟩
    simp [mul_assoc]

private noncomputable def step7_coeff
    {G : Type u} [Group G]
    (i j s : ConjClasses G) : Nat :=
  Nat.card {pair : i.carrier × j.carrier //
    pair.1.1 * pair.2.1 = Classical.choose (ConjClasses.exists_rep s)}

private theorem step7_coeff_data
    {G : Type u} [Group G] :
    classProductCoefficientData (step7_coeff (G := G)) := by
  intro i j s x hx
  unfold step7_coeff
  let r : G := Classical.choose (ConjClasses.exists_rep s)
  have hrmk : ConjClasses.mk r = s :=
    Classical.choose_spec (ConjClasses.exists_rep s)
  have hxmk : ConjClasses.mk x = s :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 hx
  have hconj : IsConj r x :=
    (ConjClasses.mk_eq_mk_iff_isConj).1 (hrmk.trans hxmk.symm)
  exact Nat.card_congr (step7_classProductFiberConjEquiv hconj)

private theorem step7_off_Z_coefficient_congr_zero
    {G : Type u} [Group G] [Finite G]
    (Q Z : Subgroup G)
    (a : ConjClasses G → ConjClasses G → ConjClasses G → Nat)
    (hdata : classProductCoefficientData a)
    (hfixedMem : ∀ q : Q, (q : G) ≠ 1 →
      ∀ c : ConjClasses G, conjugacyClassMeetsPuncturedSubgroup c Z →
      ∀ u : G, u ∈ c.carrier →
        (q : G) * u * (q : G)⁻¹ = u → u ∈ Z)
    (i j s : ConjClasses G)
    (hi : conjugacyClassMeetsPuncturedSubgroup i Z)
    (hj : conjugacyClassMeetsPuncturedSubgroup j Z)
    (hs : conjugacyClassDisjointFromSubgroup s Z) :
    algebraicIntegerCongruentModNat (Nat.card Q)
      ((a i j s * Nat.card s.carrier : Nat) : Complex) 0 := by
  classical
  let Omega := {uv : G × G // uv.1 ∈ i.carrier ∧ uv.2 ∈ j.carrier ∧
    uv.1 * uv.2 ∈ s.carrier}
  let : MulAction Q Omega :=
    { smul := fun q w =>
        ⟨((q : G) * w.1.1 * (q : G)⁻¹,
          (q : G) * w.1.2 * (q : G)⁻¹), by
          rcases w.2 with ⟨hu, hv, hprod⟩
          exact ⟨step7_conj_mem_conjClass hu (q : G),
            step7_conj_mem_conjClass hv (q : G), by
              rw [step7_conj_product_eq]
              exact step7_conj_mem_conjClass hprod (q : G)⟩⟩
      one_smul := by
        intro w
        apply Subtype.ext
        rcases w with ⟨uv, _huv⟩
        rcases uv with ⟨u, v⟩
        change ((1 : G) * u * (1 : G)⁻¹,
          (1 : G) * v * (1 : G)⁻¹) = (u, v)
        simp
      mul_smul := by
        intro q r w
        apply Subtype.ext
        rcases w with ⟨uv, _huv⟩
        rcases uv with ⟨u, v⟩
        change ((((q : G) * (r : G)) * u * (((q : G) * (r : G))⁻¹)),
            ((q : G) * (r : G)) * v * (((q : G) * (r : G))⁻¹)) =
          ((q : G) * ((r : G) * u * (r : G)⁻¹) * (q : G)⁻¹,
            (q : G) * ((r : G) * v * (r : G)⁻¹) * (q : G)⁻¹)
        simp [mul_assoc] }
  have hfree : ∀ q : Q, q ≠ 1 → ∀ w : Omega, q • w = w → False := by
    intro q hqne w hfix
    rcases w with ⟨⟨u, v⟩, hu, hv, hprod⟩
    change (⟨((q : G) * u * (q : G)⁻¹,
      (q : G) * v * (q : G)⁻¹), _⟩ : Omega) =
        ⟨(u, v), ⟨hu, hv, hprod⟩⟩ at hfix
    have hqneG : (q : G) ≠ 1 := by
      intro hq1
      apply hqne
      ext
      exact hq1
    have hpair :
        (((q : G) * u * (q : G)⁻¹,
          (q : G) * v * (q : G)⁻¹) : G × G) = (u, v) :=
      congrArg Subtype.val hfix
    have huFixed : (q : G) * u * (q : G)⁻¹ = u :=
      congrArg Prod.fst hpair
    have hvFixed : (q : G) * v * (q : G)⁻¹ = v :=
      congrArg Prod.snd hpair
    have huZ : u ∈ Z := hfixedMem q hqneG i hi u hu huFixed
    have hvZ : v ∈ Z := hfixedMem q hqneG j hj v hv hvFixed
    exact hs (u * v) hprod (Z.mul_mem huZ hvZ)
  have hdiv : Nat.card Q ∣ Nat.card Omega :=
    step7_card_actor_dvd_of_fixedPointFree
      (A := Q) (Omega := Omega) hfree
  have hcard : Nat.card Omega = a i j s * Nat.card s.carrier :=
    step7_classProductPair_card hdata i j s
  exact step7_congr_zero_of_dvd (by
    rw [← hcard]
    exact hdiv)

private theorem step7_conjClass_one_eq_one
    {G : Type u} [Group G] {x : (ConjClasses.mk (1 : G)).carrier} :
    (x : G) = 1 := by
  have hxmk : ConjClasses.mk (x : G) = ConjClasses.mk (1 : G) :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 x.2
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hxmk
  rcases isConj_iff.mp hxmk with ⟨g, hg⟩
  have h := congrArg (fun t : G => g⁻¹ * t * g) hg
  simpa [mul_assoc] using h

private theorem step7_card_conjClass_one
    {G : Type u} [Group G] [Finite G] :
    Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  classical
  let c : ConjClasses G := ConjClasses.mk (1 : G)
  have : Unique c.carrier :=
    { default := ⟨1, (ConjClasses.mem_carrier_iff_mk_eq).2 rfl⟩
      uniq := by
        intro x
        apply Subtype.ext
        exact step7_conjClass_one_eq_one (x := x) }
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_unique

private theorem step7_classSumScalar_eq_alpha
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module Complex V] [FiniteDimensional Complex V]
    (rho : Representation Complex G V) [Representation.IsIrreducible rho]
    {Z : Subgroup G} {psi : ClassFunction G} {alpha : Complex}
    (hpsiEq : psi = rho.character)
    (halpha : theorem_6_7_alphaData Z psi alpha)
    {s : ConjClasses G} (hs : conjugacyClassMeetsPuncturedSubgroup s Z) :
    Theory.Character.classSumScalar (ρ := rho) s = alpha := by
  rcases halpha s hs with ⟨z, hzs, _hzZ, _hzne, halpha⟩
  have hscalar := Theory.Character.classSumScalar_eq_card_mul_character_div
    (ρ := rho) s hzs
  rw [hpsiEq] at halpha
  exact hscalar.trans halpha.symm

private theorem step7_classSumScalar_one
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module Complex V] [FiniteDimensional Complex V]
    (rho : Representation Complex G V) [Representation.IsIrreducible rho] :
    Theory.Character.classSumScalar (ρ := rho) (ConjClasses.mk (1 : G)) = 1 := by
  have hmem : (1 : G) ∈ (ConjClasses.mk (1 : G)).carrier :=
    (ConjClasses.mem_carrier_iff_mk_eq).2 rfl
  have hscalar := Theory.Character.classSumScalar_eq_card_mul_character_div
    (ρ := rho) (ConjClasses.mk (1 : G)) hmem
  have : Nontrivial V := Theory.Character.irreducible_nontrivial (ρ := rho)
  have hdimPos : 0 < Module.finrank Complex V :=
    (Module.finrank_pos_iff (R := Complex) (M := V)).2 inferInstance
  have hcharNe : rho.character 1 ≠ 0 := by
    have hdimNe : ((Module.finrank Complex V : Complex) ≠ 0) := by
      exact_mod_cast Nat.ne_of_gt hdimPos
    simpa [Representation.character] using hdimNe
  rw [hscalar, step7_card_conjClass_one]
  field_simp [hcharNe]
  norm_num

private theorem step7_not_meets_conjClass_one
    {G : Type u} [Group G] (Z : Subgroup G) :
    ¬ conjugacyClassMeetsPuncturedSubgroup (ConjClasses.mk (1 : G)) Z := by
  rintro ⟨z, hzclass, _hzZ, hzne⟩
  exact hzne (step7_conjClass_one_eq_one (x := ⟨z, hzclass⟩))

private theorem step7_conjClass_disjoint_of_not_one_not_meets
    {G : Type u} [Group G] (Z : Subgroup G) {s : ConjClasses G}
    (hsone : s ≠ ConjClasses.mk (1 : G))
    (hsnot : ¬ conjugacyClassMeetsPuncturedSubgroup s Z) :
    conjugacyClassDisjointFromSubgroup s Z := by
  intro z hzclass hzZ
  by_cases hz1 : z = 1
  · have hmk : ConjClasses.mk z = s :=
      (ConjClasses.mem_carrier_iff_mk_eq).1 hzclass
    apply hsone
    rw [← hmk, hz1]
  · exact hsnot ⟨z, hzclass, hzZ, hz1⟩

private theorem step7_disjoint_classSumScalar_term_congr_zero
    {G : Type u} {V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module Complex V] [FiniteDimensional Complex V]
    (Q Z : Subgroup G)
    (psi : ClassFunction G)
    (rho : Representation Complex G V) [Representation.IsIrreducible rho]
    (a : ConjClasses G → ConjClasses G → ConjClasses G → Nat)
    (hfixedMem : ∀ q : Q, (q : G) ≠ 1 →
      ∀ c : ConjClasses G, conjugacyClassMeetsPuncturedSubgroup c Z →
      ∀ u : G, u ∈ c.carrier →
        (q : G) * u * (q : G)⁻¹ = u → u ∈ Z)
    (hpsi : IsIrreducibleCharacterOnGroup psi)
    (hpsiEq : psi = rho.character)
    (hdata : classProductCoefficientData a)
    {i j s : ConjClasses G}
    (hi : conjugacyClassMeetsPuncturedSubgroup i Z)
    (hj : conjugacyClassMeetsPuncturedSubgroup j Z)
    (hs : conjugacyClassDisjointFromSubgroup s Z) :
    algebraicIntegerCongruentModNat (Nat.card Q)
      (psi 1 * ((a i j s : Complex) *
        Theory.Character.classSumScalar (ρ := rho) s)) 0 := by
  classical
  obtain ⟨x, hxmk⟩ := ConjClasses.exists_rep s
  have hxs : x ∈ s.carrier := (ConjClasses.mem_carrier_iff_mk_eq).2 hxmk
  have hscalar := Theory.Character.classSumScalar_eq_card_mul_character_div
    (ρ := rho) s hxs
  have : Nontrivial V := Theory.Character.irreducible_nontrivial (ρ := rho)
  have hdimPos : 0 < Module.finrank Complex V :=
    (Module.finrank_pos_iff (R := Complex) (M := V)).2 inferInstance
  have hcharNe : rho.character 1 ≠ 0 := by
    have hdimNe : ((Module.finrank Complex V : Complex) ≠ 0) := by
      exact_mod_cast Nat.ne_of_gt hdimPos
    simpa [Representation.character] using hdimNe
  have hterm :
      psi 1 * ((a i j s : Complex) *
          Theory.Character.classSumScalar (ρ := rho) s) =
        ((a i j s * Nat.card s.carrier : Nat) : Complex) * psi x := by
    rw [hpsiEq, hscalar]
    field_simp [hcharNe]
    norm_num [Nat.cast_mul]
    ring
  have hcoeff : algebraicIntegerCongruentModNat (Nat.card Q)
      ((a i j s * Nat.card s.carrier : Nat) : Complex) 0 :=
    step7_off_Z_coefficient_congr_zero
      Q Z a hdata hfixedMem i j s hi hj hs
  have hxint : IsIntegral Int (psi x) :=
    step7_value_isIntegral_of_irreducible hpsi x
  have hmul := step7_congr_mul_right hcoeff hxint
  simpa [hterm] using hmul

private theorem step7_class_sum_square_congr
    {G : Type u} [Group G] [Finite G]
    (Q Z : Subgroup G)
    (psi : ClassFunction G)
    (a : ConjClasses G → ConjClasses G → ConjClasses G → Nat)
    (alpha : Complex)
    (hfixedMem : ∀ q : Q, (q : G) ≠ 1 →
      ∀ c : ConjClasses G, conjugacyClassMeetsPuncturedSubgroup c Z →
      ∀ u : G, u ∈ c.carrier →
        (q : G) * u * (q : G)⁻¹ = u → u ∈ Z)
    (hpsi : IsIrreducibleCharacterOnGroup psi)
    (hdata : classProductCoefficientData a)
    (halpha : theorem_6_7_alphaData Z psi alpha)
    (i j : ConjClasses G)
    (hi : conjugacyClassMeetsPuncturedSubgroup i Z)
    (hj : conjugacyClassMeetsPuncturedSubgroup j Z) :
    algebraicIntegerCongruentModNat (Nat.card Q)
      (psi 1 * alpha ^ 2)
      (psi 1 * ((a i j (ConjClasses.mk (1 : G)) : Complex) +
        (theorem_6_7_aij Z a i j : Complex) * alpha)) := by
  classical
  rcases hpsi with ⟨n, rho, hrho, hpsiEq⟩
  have : Representation.IsIrreducible rho := hrho
  let C : Finset (ConjClasses G) :=
    @Finset.univ (ConjClasses G) (Fintype.ofFinite (ConjClasses G))
  let c0 : ConjClasses G := ConjClasses.mk (1 : G)
  let f : ConjClasses G → Complex := fun s =>
    psi 1 * ((a i j s : Complex) * Theory.Character.classSumScalar (ρ := rho) s)
  let g : ConjClasses G → Complex := fun s =>
    (if s = c0 then psi 1 * (a i j c0 : Complex) else 0) +
      if conjugacyClassMeetsPuncturedSubgroup s Z then
        psi 1 * ((a i j s : Complex) * alpha)
      else 0
  have hci : Theory.Character.classSumScalar (ρ := rho) i = alpha :=
    step7_classSumScalar_eq_alpha rho hpsiEq halpha hi
  have hcj : Theory.Character.classSumScalar (ρ := rho) j = alpha :=
    step7_classSumScalar_eq_alpha rho hpsiEq halpha hj
  have hscalarMul := Theory.Character.classSumScalar_mul_eq_sum_of_coefficients
    (ρ := rho) a hdata i j
  have hscalarEq : alpha ^ 2 = C.sum fun s =>
      (a i j s : Complex) * Theory.Character.classSumScalar (ρ := rho) s := by
    dsimp [C]
    simpa [hci, hcj, pow_two] using hscalarMul
  have hleftEq : psi 1 * alpha ^ 2 = C.sum f := by
    rw [hscalarEq]
    dsimp [f]
    rw [Finset.mul_sum]
  have hpsi1Int : IsIntegral Int (psi 1) :=
    step7_value_isIntegral_of_irreducible ⟨n, rho, hrho, hpsiEq⟩ 1
  have hfInt (s : ConjClasses G) : IsIntegral Int (f s) := by
    dsimp [f]
    exact hpsi1Int.mul
      ((step7_natCast_isIntegral (a i j s)).mul
        (Theory.Character.classSumScalar_isIntegral (ρ := rho) s))
  have hpoint : ∀ s ∈ C, algebraicIntegerCongruentModNat (Nat.card Q)
      (f s) (g s) := by
    intro s _hsC
    by_cases hsone : s = c0
    · subst s
      have hnotMeets : ¬ conjugacyClassMeetsPuncturedSubgroup c0 Z := by
        simpa [c0] using step7_not_meets_conjClass_one (Z := Z)
      simpa [f, g, c0, hnotMeets, step7_classSumScalar_one rho,
        mul_assoc] using step7_congr_refl (n := Nat.card Q) (hfInt c0)
    · by_cases hsmeet : conjugacyClassMeetsPuncturedSubgroup s Z
      · have hsalpha : Theory.Character.classSumScalar (ρ := rho) s = alpha :=
          step7_classSumScalar_eq_alpha rho hpsiEq halpha hsmeet
        simpa [f, g, c0, hsone, hsmeet, hsalpha, mul_assoc] using
          step7_congr_refl (n := Nat.card Q) (hfInt s)
      · have hsdisj : conjugacyClassDisjointFromSubgroup s Z :=
          step7_conjClass_disjoint_of_not_one_not_meets Z hsone hsmeet
        simpa [f, g, c0, hsone, hsmeet] using
          step7_disjoint_classSumScalar_term_congr_zero
            Q Z psi rho a hfixedMem ⟨n, rho, hrho, hpsiEq⟩ hpsiEq hdata
              hi hj hsdisj
  have hsumCongr := step7_congr_sum C f g hpoint
  have hsumG : C.sum g =
      psi 1 * ((a i j c0 : Complex) +
        (theorem_6_7_aij Z a i j : Complex) * alpha) := by
    dsimp [g, C, c0, theorem_6_7_aij]
    rw [Finset.sum_add_distrib]
    simp [mul_add, mul_assoc, mul_comm, Nat.cast_sum]
    rw [← Finset.sum_filter]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp
    · intro x _hx
      ring
  rw [← hleftEq] at hsumCongr
  rw [hsumG] at hsumCongr
  simpa [c0, mul_add, mul_assoc, mul_left_comm, mul_comm] using hsumCongr

private theorem step7_alphaData_of_constant_card
    {G : Type u} [Group G] [Finite G]
    (Z : Subgroup G) (psi : ClassFunction G) (C : Nat)
    (hcard : ∀ z : Z, (z : G) ≠ 1 →
      Nat.card (ConjClasses.mk (z : G)).carrier = C)
    (hconst : constantOnNonidentitySubgroup Z psi)
    (z0 : Z) (hz0ne : z0 ≠ 1) :
    theorem_6_7_alphaData Z psi ((C : Complex) * psi z0 / psi 1) := by
  intro s hs
  rcases hs with ⟨y, hys, hyZ, hyne⟩
  refine ⟨y, hys, hyZ, hyne, ?_⟩
  have hysMk : ConjClasses.mk y = s :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 hys
  let yZ : Z := ⟨y, hyZ⟩
  have hyZne : yZ ≠ 1 := by
    intro hyOne
    exact hyne (congrArg Subtype.val hyOne)
  have hyCard : Nat.card s.carrier = C := by
    rw [← hysMk]
    exact hcard yZ hyne
  have hpsi : psi y = psi z0 := hconst yZ z0 hyZne hz0ne
  rw [hyCard, hpsi]

private theorem step7_inv_mem_conjClass_inv
    {G : Type u} [Group G] {z u : G}
    (hu : u ∈ (ConjClasses.mk z).carrier) :
    u⁻¹ ∈ (ConjClasses.mk z⁻¹).carrier := by
  have hmk : ConjClasses.mk u = ConjClasses.mk z :=
    (ConjClasses.mem_carrier_iff_mk_eq).1 hu
  rw [ConjClasses.mem_carrier_iff_mk_eq]
  rw [ConjClasses.mk_eq_mk_iff_isConj] at hmk ⊢
  rcases isConj_iff.mp hmk with ⟨g, hg⟩
  refine isConj_iff.mpr ⟨g, ?_⟩
  rw [← hg]
  simp [mul_assoc]

private theorem step7_a_self_self_one_eq_zero
    {G : Type u} [Group G] [Finite G]
    {a : ConjClasses G → ConjClasses G → ConjClasses G → Nat}
    (hdata : classProductCoefficientData a)
    {z : G} (hnot : ¬ IsConj z z⁻¹) :
    a (ConjClasses.mk z) (ConjClasses.mk z) (ConjClasses.mk (1 : G)) = 0 := by
  have hcoeff := hdata (ConjClasses.mk z) (ConjClasses.mk z)
    (ConjClasses.mk (1 : G)) (1 : G)
      ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
  rw [hcoeff]
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  exact ⟨fun p => by
    let u : G := p.1.1.1
    let v : G := p.1.2.1
    have hu : u ∈ (ConjClasses.mk z).carrier := p.1.1.2
    have hv : v ∈ (ConjClasses.mk z).carrier := p.1.2.2
    have huv : u * v = 1 := p.2
    apply hnot
    have hvEq : v = u⁻¹ := by
      have h := congrArg (fun t : G => u⁻¹ * t) huv
      simpa [mul_assoc] using h
    have huInvZ : u⁻¹ ∈ (ConjClasses.mk z⁻¹).carrier :=
      step7_inv_mem_conjClass_inv hu
    have huInvZ' : u⁻¹ ∈ (ConjClasses.mk z).carrier := by
      simpa [hvEq] using hv
    have hmk1 : ConjClasses.mk (u⁻¹) = ConjClasses.mk z :=
      (ConjClasses.mem_carrier_iff_mk_eq).1 huInvZ'
    have hmk2 : ConjClasses.mk (u⁻¹) = ConjClasses.mk z⁻¹ :=
      (ConjClasses.mem_carrier_iff_mk_eq).1 huInvZ
    exact (ConjClasses.mk_eq_mk_iff_isConj).1 (hmk1.symm.trans hmk2)⟩

private theorem step7_a_self_inv_one_eq_card
    {G : Type u} [Group G] [Finite G]
    {a : ConjClasses G → ConjClasses G → ConjClasses G → Nat}
    (hdata : classProductCoefficientData a) (z : G) :
    a (ConjClasses.mk z) (ConjClasses.mk z⁻¹) (ConjClasses.mk (1 : G)) =
      Nat.card (ConjClasses.mk z).carrier := by
  have hcoeff := hdata (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
    (ConjClasses.mk (1 : G)) (1 : G)
      ((ConjClasses.mem_carrier_iff_mk_eq).2 rfl)
  rw [hcoeff]
  let e : (ConjClasses.mk z).carrier ≃
      {p : (ConjClasses.mk z).carrier × (ConjClasses.mk z⁻¹).carrier //
        p.1.1 * p.2.1 = (1 : G)} :=
    { toFun := fun u =>
        ⟨(u, ⟨(u : G)⁻¹, step7_inv_mem_conjClass_inv u.2⟩), by simp⟩
      invFun := fun p => ⟨p.1.1.1, p.1.1.2⟩
      left_inv := by
        intro u
        apply Subtype.ext
        rfl
      right_inv := by
        intro p
        apply Subtype.ext
        let u : G := p.1.1.1
        let v : G := p.1.2.1
        have hp : u * v = 1 := p.2
        have hvEq : v = u⁻¹ := by
          have h := congrArg (fun t : G => u⁻¹ * t) hp
          simpa [mul_assoc] using h
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          exact hvEq.symm }
  exact (Nat.card_congr e).symm

private theorem step7_class_algebra_congruence
    {G : Type u} [Group G] [Finite G]
    (Q Z : Subgroup G)
    (hfixedMem : ∀ q : Q, (q : G) ≠ 1 →
      ∀ c : ConjClasses G, conjugacyClassMeetsPuncturedSubgroup c Z →
      ∀ u : G, u ∈ c.carrier →
        (q : G) * u * (q : G)⁻¹ = u → u ∈ Z)
    (C : Nat)
    (hcard : ∀ z : Z, (z : G) ≠ 1 →
      Nat.card (ConjClasses.mk (z : G)).carrier = C)
    (hcop : Nat.Coprime C (Nat.card Q))
    (psi : ClassFunction G)
    (hconst : constantOnNonidentitySubgroup Z psi)
    (hpsi : IsIrreducibleCharacterOnGroup psi)
    (z : Z) (hz : z ≠ 1)
    (hnot : ¬ IsConj (z : G) ((z : G)⁻¹)) :
    algebraicIntegerCongruentModNat (Nat.card Q) (psi z) (psi 1) := by
  classical
  let a : ConjClasses G → ConjClasses G → ConjClasses G → Nat :=
    step7_coeff (G := G)
  let i : ConjClasses G := ConjClasses.mk (z : G)
  let j : ConjClasses G := ConjClasses.mk ((z : G)⁻¹)
  let c0 : ConjClasses G := ConjClasses.mk (1 : G)
  let A11 : Nat := theorem_6_7_aij Z a i i
  let A12 : Nat := theorem_6_7_aij Z a i j
  let alpha : Complex := (C : Complex) * psi z / psi 1
  have hdata : classProductCoefficientData a := step7_coeff_data (G := G)
  have hzGNe : (z : G) ≠ 1 := by
    intro hzOne
    exact hz (Subtype.ext hzOne)
  have hzinvNe : ((z : G)⁻¹) ≠ 1 := by
    intro hzinv
    exact hz (Subtype.ext (inv_eq_one.mp hzinv))
  have hi : conjugacyClassMeetsPuncturedSubgroup i Z := by
    refine ⟨(z : G), ?_, z.2, hzGNe⟩
    exact (ConjClasses.mem_carrier_iff_mk_eq).2 rfl
  have hj : conjugacyClassMeetsPuncturedSubgroup j Z := by
    refine ⟨((z : G)⁻¹), ?_, Z.inv_mem z.2, hzinvNe⟩
    exact (ConjClasses.mem_carrier_iff_mk_eq).2 rfl
  have halpha : theorem_6_7_alphaData Z psi alpha := by
    simpa [alpha] using
      step7_alphaData_of_constant_card Z psi C hcard hconst z hz
  have hpsi1Ne : psi 1 ≠ 0 :=
    step7_character_one_ne_zero_of_irreducible hpsi
  have ha110 : a i i c0 = 0 := by
    simpa [i, c0] using
      step7_a_self_self_one_eq_zero (hdata := hdata) hnot
  have ha120 : a i j c0 = C := by
    simpa [i, j, c0] using
      (step7_a_self_inv_one_eq_card (hdata := hdata) (z := (z : G))).trans
        (hcard z hzGNe)
  have hii := step7_class_sum_square_congr Q Z psi a alpha hfixedMem
    hpsi hdata halpha i i hi hi
  have hij := step7_class_sum_square_congr Q Z psi a alpha hfixedMem
    hpsi hdata halpha i j hi hj
  have hpsiLeft : algebraicIntegerCongruentModNat (Nat.card Q)
      (psi 1 * ((A11 : Complex) * alpha)) (psi 1 * alpha ^ 2) := by
    simpa [A11, c0, ha110] using step7_congr_symm hii
  have hpsiRight : algebraicIntegerCongruentModNat (Nat.card Q)
      (psi 1 * alpha ^ 2)
      (psi 1 * ((C : Complex) + (A12 : Complex) * alpha)) := by
    simpa [A12, c0, ha120] using hij
  have hpsiCmp0 : algebraicIntegerCongruentModNat (Nat.card Q)
      (psi 1 * ((A11 : Complex) * alpha))
      (psi 1 * ((C : Complex) + (A12 : Complex) * alpha)) :=
    step7_congr_trans hpsiLeft hpsiRight
  have hpsiLeftEq :
      psi 1 * ((A11 : Complex) * alpha) =
        (C : Complex) * ((A11 : Complex) * psi z) := by
    dsimp [alpha]
    field_simp [hpsi1Ne]
  have hpsiRightEq :
      psi 1 * ((C : Complex) + (A12 : Complex) * alpha) =
        (C : Complex) * (psi 1 + (A12 : Complex) * psi z) := by
    dsimp [alpha]
    field_simp [hpsi1Ne]
  rw [hpsiLeftEq, hpsiRightEq] at hpsiCmp0
  have hnQ : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hzInt : IsIntegral Int (psi z) :=
    step7_value_isIntegral_of_irreducible hpsi (z : G)
  have h1Int : IsIntegral Int (psi 1) :=
    step7_value_isIntegral_of_irreducible hpsi (1 : G)
  have hA11Int : IsIntegral Int (A11 : Complex) :=
    step7_natCast_isIntegral A11
  have hA12Int : IsIntegral Int (A12 : Complex) :=
    step7_natCast_isIntegral A12
  have hpsiLeftInt : IsIntegral Int ((A11 : Complex) * psi z) :=
    hA11Int.mul hzInt
  have hpsiRightInt : IsIntegral Int (psi 1 + (A12 : Complex) * psi z) :=
    h1Int.add (hA12Int.mul hzInt)
  have hpsiCmp : algebraicIntegerCongruentModNat (Nat.card Q)
      ((A11 : Complex) * psi z) (psi 1 + (A12 : Complex) * psi z) :=
    step7_congr_cancel_nat_mul_left hnQ hcop hpsiLeftInt hpsiRightInt hpsiCmp0
  let principal : ClassFunction G := principalCharacter G
  have hprincipalConst : constantOnNonidentitySubgroup Z principal := by
    intro z1 z2 _hz1 _hz2
    simp [principal]
  have hprincipal : IsIrreducibleCharacterOnGroup principal := by
    simpa [principal] using
      (Section3.principalCharacter_isIrreducibleCharacterOnGroup (G := G))
  let alpha0 : Complex := (C : Complex)
  have halpha0 : theorem_6_7_alphaData Z principal alpha0 := by
    simpa [alpha0, principal, principalCharacter] using
      step7_alphaData_of_constant_card Z principal C hcard hprincipalConst z hz
  have hpii := step7_class_sum_square_congr Q Z principal a alpha0 hfixedMem
    hprincipal hdata halpha0 i i hi hi
  have hpij := step7_class_sum_square_congr Q Z principal a alpha0 hfixedMem
    hprincipal hdata halpha0 i j hi hj
  have hpLeft : algebraicIntegerCongruentModNat (Nat.card Q)
      ((C : Complex) * (A11 : Complex)) ((C : Complex) ^ 2) := by
    simpa [principal, alpha0, A11, c0, ha110, principalCharacter,
      pow_two, mul_assoc, mul_left_comm, mul_comm] using step7_congr_symm hpii
  have hpRight : algebraicIntegerCongruentModNat (Nat.card Q)
      ((C : Complex) ^ 2) ((C : Complex) * ((1 : Complex) + (A12 : Complex))) := by
    simpa [principal, alpha0, A12, c0, ha120, principalCharacter,
      pow_two, mul_add, mul_assoc, mul_left_comm, mul_comm] using hpij
  have hpCmp0 : algebraicIntegerCongruentModNat (Nat.card Q)
      ((C : Complex) * (A11 : Complex))
      ((C : Complex) * ((1 : Complex) + (A12 : Complex))) :=
    step7_congr_trans hpLeft hpRight
  have hcoefRightInt : IsIntegral Int ((1 : Complex) + (A12 : Complex)) := by
    simpa [Nat.cast_add] using step7_natCast_isIntegral (1 + A12)
  have hcoefCmp : algebraicIntegerCongruentModNat (Nat.card Q)
      (A11 : Complex) ((1 : Complex) + (A12 : Complex)) :=
    step7_congr_cancel_nat_mul_left hnQ hcop hA11Int hcoefRightInt hpCmp0
  have hcoefMul : algebraicIntegerCongruentModNat (Nat.card Q)
      ((A11 : Complex) * psi z) (((1 : Complex) + (A12 : Complex)) * psi z) :=
    step7_congr_mul_right hcoefCmp hzInt
  have hmain0 : algebraicIntegerCongruentModNat (Nat.card Q)
      (((1 : Complex) + (A12 : Complex)) * psi z)
      (psi 1 + (A12 : Complex) * psi z) :=
    step7_congr_trans (step7_congr_symm hcoefMul) hpsiCmp
  have hleftCommon :
      ((1 : Complex) + (A12 : Complex)) * psi z =
        psi z + (A12 : Complex) * psi z := by
    ring
  rw [hleftCommon] at hmain0
  exact step7_congr_cancel_add_right hzInt h1Int hmain0


private theorem feitSibley_step7_class_algebra_congruence_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (p : Nat) (hpprime : p.Prime) (hpQ1 : IsPGroup p d.Q1)
    (hDodd : Odd (Nat.card d.D))
    (hstep4 : feitSibleyStep4Data d chars) :
    feitSibleyStep7Data d := by
  classical
  let : Fact p.Prime := ⟨hpprime⟩
  rcases hstep4 with
    ⟨hZne, hZnormal, hZleCenter, _hXY, _hcoherentX, _hcoherentY,
      _hXne, _hYne, _hYdegree, _hdegreeData⟩
  let Z : Subgroup d.H := feitSibleyZ d
  let ZG : Subgroup G := Z.map d.H.subtype
  have hZleQ1 : Z ≤ d.Q1 :=
    hZleCenter.trans (by
      simpa [Z, feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  have hQ1ne : d.Q1 ≠ ⊥ := by
    intro hQ1
    apply hZne
    exact bot_unique (by simpa [Z, hQ1] using hZleQ1)
  have hpQ1card : p ∣ Nat.card d.Q1 := by
    rcases hpQ1.card_eq_or_dvd with hcard | hdvd
    · have hbot : d.Q1 = ⊥ := by
        rw [← Subgroup.card_le_one_iff_eq_bot, hcard]
      exact (hQ1ne hbot).elim
    · exact hdvd
  have hpQcard : p ∣ Nat.card d.Q :=
    hpQ1card.trans (Subgroup.card_dvd_of_le d.Q1_le_Q)
  have hfixedMem : ∀ q : d.QInG, (q : G) ≠ 1 →
      ∀ c : ConjClasses G, conjugacyClassMeetsPuncturedSubgroup c ZG →
      ∀ u : G, u ∈ c.carrier →
        (q : G) * u * (q : G)⁻¹ = u → u ∈ ZG := by
    intro q hqne c hc u huc hfix
    have huCentralizer : u ∈ Section2.elementCentralizer (q : G) := by
      unfold Section2.elementCentralizer
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      have hmul := congrArg (fun x : G => x * (q : G)) hfix
      simpa [mul_assoc] using hmul
    have huH : u ∈ d.H :=
      d.QInG_elementCentralizer_le_H_appendixIV q.property hqne huCentralizer
    exact d.mem_map_Z_of_mem_H_mem_class_meets_map_Z_appendixIV
      p hpprime hpQ1 hpQcard Z hZnormal hZleQ1 c huH huc hc
  have hcard : ∀ z : ZG, (z : G) ≠ 1 →
      Nat.card (ConjClasses.mk (z : G)).carrier = d.QInG.index := by
    intro z hz
    exact d.card_conjClass_eq_QInG_index_of_mem_map_Z_appendixIV
      Z hZleQ1 hZleCenter z hz
  have hcop : Nat.Coprime d.QInG.index (Nat.card d.QInG) :=
    d.QInG_card_coprime_index_appendixIV.symm
  have hQcard : Nat.card d.QInG = Nat.card d.Q := by
    simpa [FeitSibleyData.QInG] using
      (Subgroup.card_map_of_injective (K := d.Q) (f := d.H.subtype)
        d.H.subtype_injective)
  unfold feitSibleyStep7Data
  intro psi hconst hpsi z hz
  let zG : ZG :=
    ⟨d.H.subtype z, Subgroup.mem_map.mpr ⟨z, z.property, rfl⟩⟩
  have hzG : zG ≠ 1 := by
    intro hzOne
    have hzOneG : (zG : G) = 1 := congrArg Subtype.val hzOne
    apply hz
    apply Subtype.ext
    simpa [zG] using hzOneG
  have hconstG : constantOnNonidentitySubgroup ZG psi := by
    intro z1 z2 hz1 hz2
    rcases Subgroup.mem_map.mp z1.property with ⟨z1H, hz1Z, hz1val⟩
    rcases Subgroup.mem_map.mp z2.property with ⟨z2H, hz2Z, hz2val⟩
    let z1Z : Z := ⟨z1H, hz1Z⟩
    let z2Z : Z := ⟨z2H, hz2Z⟩
    have hz1Zne : (z1Z : d.H) ≠ 1 := by
      intro h
      apply hz1
      apply Subtype.ext
      change (z1 : G) = 1
      rw [← hz1val]
      exact congrArg Subtype.val h
    have hz2Zne : (z2Z : d.H) ≠ 1 := by
      intro h
      apply hz2
      apply Subtype.ext
      change (z2 : G) = 1
      rw [← hz2val]
      exact congrArg Subtype.val h
    have h := hconst z1Z z2Z hz1Zne hz2Zne
    change psi ((z1H : d.H) : G) = psi ((z2H : d.H) : G) at h
    calc
      psi (z1 : G) = psi ((z1H : d.H) : G) := congrArg psi hz1val.symm
      _ = psi ((z2H : d.H) : G) := h
      _ = psi (z2 : G) := congrArg psi hz2val
  have hzGAmbient : (zG : G) ≠ 1 := by
    intro hzOne
    exact hzG (Subtype.ext hzOne)
  have hnot : ¬ IsConj (zG : G) ((zG : G)⁻¹) :=
    d.not_isConj_inv_of_mem_map_Z_appendixIV
      hDodd Z hZleQ1 hZleCenter zG hzGAmbient
  have hcongr := step7_class_algebra_congruence
    d.QInG ZG hfixedMem d.QInG.index hcard hcop
      psi hconstG hpsi zG hzG hnot
  rw [hQcard] at hcongr
  simpa [zG] using hcongr.2.2

private theorem step8_subgroupRestriction_isVirtualCharacter
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {phi : ClassFunction G}
    (hphi : Theory.Character.IsVirtualCharacter phi) :
    Theory.Character.IsVirtualCharacter (subgroupRestriction H phi) := by
  classical
  rcases hphi with ⟨r, m, n, rho, hphiEq⟩
  refine ⟨r, m, n, fun i => (rho i).comp H.subtype, ?_⟩
  ext h
  rw [hphiEq]
  simp [Theory.Character.virtualCharacterOfRepresentations,
    subgroupRestriction, Representation.character]

private theorem step8_source_scalarProduct_star_eq_self_of_virtual
    {G : Type u} [Group G] [Finite G]
    {L : Subgroup G} {chi : ClassFunction L}
    (hchi : IsIrreducibleCharacterOnGroup chi)
    {psi : ClassFunction G}
    (hpsi : Theory.Character.IsVirtualCharacter psi) :
    star (scalarProduct L chi (subgroupRestriction L psi)) =
      scalarProduct L chi (subgroupRestriction L psi) := by
  have hchiVirt : Theory.Character.IsVirtualCharacter chi :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hchi
  have hresVirt :
      Theory.Character.IsVirtualCharacter (subgroupRestriction L psi) :=
    step8_subgroupRestriction_isVirtualCharacter L hpsi
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hchiVirt hresVirt with
    ⟨n, hn⟩
  rw [hn]
  simp

private theorem step8_isClassFunction_of_irreducible
    {G : Type u} [Group G] [Finite G]
    {chi : ClassFunction G}
    (hchi : IsIrreducibleCharacterOnGroup chi) :
    IsClassFunction chi := by
  rcases hchi with ⟨n, rho, _hirr, rfl⟩
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := rho) g x

private theorem step8_isClassFunction_of_signed
    {G : Type u} [Group G] [Finite G]
    {chi : ClassFunction G}
    (hchi : Section3.IsSignedIrreducibleCharacter chi) :
    IsClassFunction chi := by
  rcases hchi with ⟨epsilon, _hepsilon, mu, hmu, rfl⟩
  exact isClassFunction_smul epsilon mu
    (step8_isClassFunction_of_irreducible hmu)

private theorem step8_isClassFunction_subgroupRestriction
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) {chi : ClassFunction G}
    (hchi : IsClassFunction chi) :
    IsClassFunction (subgroupRestriction H chi) := by
  intro x g
  change chi (((x * g * x⁻¹ : H) : G)) = chi (g : G)
  simpa using hchi (x : G) (g : G)

private theorem step8_isClassFunction_weightedFamilySum
    {G : Type u} [Group G]
    {iota : Type*} [Finite iota]
    (w : iota → Complex) (phi : iota → ClassFunction G)
    (hphi : ∀ i : iota, IsClassFunction (phi i)) :
    IsClassFunction (weightedFamilySum w phi) := by
  classical
  intro x g
  rw [weightedFamilySum]
  exact Finset.sum_congr rfl fun i _hi => by
    simp [hphi i x g]

private theorem step8_X_weighted_degree_sum_scalarProduct
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (ClassFunction L)}
    (hXchar : ∀ chi : ClassFunction L, chi ∈ X ↔
      IsIrreducibleCharacterOnGroup chi ∧ ¬ subgroupInKernel' chi Z)
    (dX : X → Nat) (chi : X) :
    scalarProduct L
      (weightedFamilySum (fun xi : X => (dX xi : Complex))
        (fun xi : X => (xi : ClassFunction L)))
      (chi : ClassFunction L) = (dX chi : Complex) := by
  classical
  have horth : ∀ i j : X,
      scalarProduct L (i : ClassFunction L) (j : ClassFunction L) =
        if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact scalarProduct_irreducibleCharacter_self
        ((hXchar (i : ClassFunction L)).1 i.2).1
    · rw [if_neg hij]
      exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
        ((hXchar (i : ClassFunction L)).1 i.2).1
        ((hXchar (j : ClassFunction L)).1 j.2).1
        (by intro h; exact hij (Subtype.ext h))
  exact scalarProduct_weightedFamilySum_left_orthonormal
    (fun xi : X => (dX xi : Complex))
    (fun xi : X => (xi : ClassFunction L)) horth chi

private theorem step8_source_residual_subgroupInKernel
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (ClassFunction L)}
    (hXchar : ∀ chi : ClassFunction L, chi ∈ X ↔
      IsIrreducibleCharacterOnGroup chi ∧ ¬ subgroupInKernel' chi Z)
    (dX : X → Nat)
    {psi : ClassFunction L} (hpsiClass : IsClassFunction psi)
    (chi0 : X) {c : Complex} (hcstar : star c = c)
    (hdeg0Ne : (dX chi0 : Complex) ≠ 0)
    (hcoeff : ∀ chi : X,
      scalarProduct L (chi : ClassFunction L) psi =
        ((dX chi : Complex) / (dX chi0 : Complex)) * c) :
    subgroupInKernel'
      (psi - (c / (dX chi0 : Complex)) •
        weightedFamilySum (fun chi : X => (dX chi : Complex))
          (fun chi : X => (chi : ClassFunction L))) Z := by
  classical
  let W : ClassFunction L :=
    weightedFamilySum (fun chi : X => (dX chi : Complex))
      (fun chi : X => (chi : ClassFunction L))
  have hWClass : IsClassFunction W := by
    exact step8_isClassFunction_weightedFamilySum
      (fun chi : X => (dX chi : Complex))
      (fun chi : X => (chi : ClassFunction L))
      (fun chi => step8_isClassFunction_of_irreducible
        ((hXchar (chi : ClassFunction L)).1 chi.2).1)
  have hphiClass : IsClassFunction (psi - (c / (dX chi0 : Complex)) • W) := by
    intro x g
    change psi (x * g * x⁻¹) -
        (c / (dX chi0 : Complex)) * W (x * g * x⁻¹) =
      psi g - (c / (dX chi0 : Complex)) * W g
    rw [hpsiClass x g, hWClass x g]
  have horth : ∀ chi : X,
      scalarProduct L (psi - (c / (dX chi0 : Complex)) • W)
        (chi : ClassFunction L) = 0 := by
    intro chi
    have hpsiChi : scalarProduct L psi (chi : ClassFunction L) =
        ((dX chi : Complex) / (dX chi0 : Complex)) * c := by
      calc
        scalarProduct L psi (chi : ClassFunction L) =
            star (scalarProduct L (chi : ClassFunction L) psi) := by
          exact (scalarProduct_star_swap (G := L)
            (phi := psi) (psi := (chi : ClassFunction L))).symm
        _ = star (((dX chi : Complex) / (dX chi0 : Complex)) * c) := by
          rw [hcoeff chi]
        _ = ((dX chi : Complex) / (dX chi0 : Complex)) * c := by
          simp [hcstar]
    have hWChi : scalarProduct L W (chi : ClassFunction L) =
        (dX chi : Complex) :=
      step8_X_weighted_degree_sum_scalarProduct hXchar dX chi
    rw [Section5.scalarProduct_sub_left, scalarProduct_smul_left,
      hpsiChi, hWChi]
    field_simp [hdeg0Ne]
    ring
  simpa [W] using
    theorem_6_6_orthogonal_Xset_complement_subgroupInKernel
      hXchar hphiClass horth

private theorem step8_sub_values_of_residual_kernel_weighted_X
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (ClassFunction L)}
    (hXchar : ∀ chi : ClassFunction L, chi ∈ X ↔
      IsIrreducibleCharacterOnGroup chi ∧ ¬ subgroupInKernel' chi Z)
    (dX : X → Nat)
    (hdegX : ∀ chi : X, degree (chi : ClassFunction L) = (dX chi : Complex))
    {psi : ClassFunction L} {A : Complex}
    (hker : subgroupInKernel'
      (psi - A • weightedFamilySum (fun chi : X => (dX chi : Complex))
        (fun chi : X => (chi : ClassFunction L))) Z)
    (z : Z) (hz : z ≠ 1) :
    psi 1 - psi (z : L) = A * (Nat.card L : Complex) := by
  classical
  let W : ClassFunction L :=
    weightedFamilySum (fun chi : X => (dX chi : Complex))
      (fun chi : X => (chi : ClassFunction L))
  have hker' : subgroupInKernel' (psi - A • W) Z := by
    simpa [W] using hker
  have hkerz : (psi - A • W) (z : L) = (psi - A • W) (1 : L) :=
    (hker' z).trans (hker' (1 : Z)).symm
  have hW1 : W (1 : L) =
      (Nat.card L : Complex) - (Nat.card (L ⧸ Z) : Complex) := by
    dsimp [W]
    rw [weightedFamilySum]
    have huniv : (@Finset.univ X (Fintype.ofFinite X)) =
        (@Finset.univ X (Finset.Subtype.fintype X)) := by
      ext chi
      simp
    rw [huniv]
    exact theorem_6_6_Xset_weighted_degree_sum_eq_card_sub_quotient_at_one
      hXchar dX hdegX
  have hWz : W (z : L) = - (Nat.card (L ⧸ Z) : Complex) := by
    dsimp [W]
    rw [weightedFamilySum]
    have huniv : (@Finset.univ X (Fintype.ofFinite X)) =
        (@Finset.univ X (Finset.Subtype.fintype X)) := by
      ext chi
      simp
    rw [huniv]
    exact theorem_6_6_Xset_weighted_degree_sum_eq_neg_quotient_card_of_mem_Z_ne_one
      hXchar dX hdegX z hz
  have hsub : psi 1 - psi (z : L) = A * (W 1 - W (z : L)) := by
    have hpsi1 : psi 1 = psi (z : L) - A * W (z : L) + A * W 1 := by
      have h := hkerz
      change psi (z : L) - A * W (z : L) = psi 1 - A * W 1 at h
      calc
        psi 1 = (psi 1 - A * W 1) + A * W 1 := by ring
        _ = (psi (z : L) - A * W (z : L)) + A * W 1 := by rw [← h]
        _ = psi (z : L) - A * W (z : L) + A * W 1 := by ring
    rw [hpsi1]
    ring
  have hWdiff : W 1 - W (z : L) = (Nat.card L : Complex) := by
    rw [hW1, hWz]
    ring
  rw [hsub, hWdiff]

private theorem step8_constantOnNonidentitySubgroup_of_residual_kernel
    {L : Type u} [Group L] [Finite L]
    {Z : Subgroup L} [Z.Normal]
    {X : Finset (ClassFunction L)}
    (hXchar : ∀ chi : ClassFunction L, chi ∈ X ↔
      IsIrreducibleCharacterOnGroup chi ∧ ¬ subgroupInKernel' chi Z)
    (dX : X → Nat)
    (hdegX : ∀ chi : X, degree (chi : ClassFunction L) = (dX chi : Complex))
    {psi : ClassFunction L} {A : Complex}
    (hker : subgroupInKernel'
      (psi - A • weightedFamilySum (fun chi : X => (dX chi : Complex))
        (fun chi : X => (chi : ClassFunction L))) Z) :
    constantOnNonidentitySubgroup Z psi := by
  intro z1 z2 hz1 hz2
  have h1 := step8_sub_values_of_residual_kernel_weighted_X
    hXchar dX hdegX hker z1 hz1
  have h2 := step8_sub_values_of_residual_kernel_weighted_X
    hXchar dX hdegX hker z2 hz2
  calc
    psi (z1 : L) = psi 1 - (psi 1 - psi (z1 : L)) := by ring
    _ = psi 1 - A * (Nat.card L : Complex) := by rw [h1]
    _ = psi 1 - (psi 1 - psi (z2 : L)) := by rw [h2]
    _ = psi (z2 : L) := by ring

private theorem step8_restriction_divisibility
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G)
    (X Y : Finset (ClassFunction L))
    (Z : Subgroup L) [Z.Normal]
    (qcard dcard : Nat)
    (hZne : Z ≠ ⊥)
    (hHcard : Nat.card L = dcard * qcard)
    (hXchar : ∀ chi : ClassFunction L, chi ∈ X ↔
      IsIrreducibleCharacterOnGroup chi ∧ ¬ subgroupInKernel' chi Z)
    (hYirr : ∀ eta : Y,
      IsIrreducibleCharacterOnGroup (eta : ClassFunction L))
    (TX TY : ClassFunction L →ₗ[Complex] ClassFunction G)
    (hTX : isCFLinearIsometryOnSpan X TX ∧
      mapsIntegerSpanToVirtualCharacters X TX ∧
      agreesOnIntegerSpanOn X puncturedSet (inducedCFLinear L) TX)
    (hTY : isCFLinearIsometryOnSpan Y TY ∧
      mapsIntegerSpanToVirtualCharacters Y TY ∧
      agreesOnIntegerSpanOn Y puncturedSet (inducedCFLinear L) TY)
    (hcross : ∀ chi : X, ∀ eta : Y,
      scalarProduct G (TX (chi : ClassFunction L))
        (TY (eta : ClassFunction L)) = 0)
    (chi1 : X) (eta1 : Y) (a : Nat)
    (ha : 1 < a)
    (hdcard : dcard ≠ 0)
    (hdegreeEta : degree (eta1 : ClassFunction L) = (dcard : Complex))
    (hdegreeBase : degree (chi1 : ClassFunction L) =
      (a : Complex) * degree (eta1 : ClassFunction L))
    (hdivX : ∀ chi : X, ∃ ai : Nat,
      degree (chi : ClassFunction L) =
        (ai : Complex) * degree (chi1 : ClassFunction L))
    (v : ClassFunction G) (lambda : Int)
    (_ : Theory.Character.IsVirtualCharacter v)
    (hdecomp : inducedCF L
        ((chi1 : ClassFunction L) -
          (a : Complex) • (eta1 : ClassFunction L)) =
      -(a : Complex) • TY (eta1 : ClassFunction L) +
        (lambda : Complex) •
          (∑ eta : Y, TY (eta : ClassFunction L)) + v)
    (hvorth : ∀ eta : Y,
      scalarProduct G v (TY (eta : ClassFunction L)) = 0)
    (hstep7 : ∀ psi : ClassFunction G,
      (∀ z1 z2 : Z, (z1 : L) ≠ 1 → (z2 : L) ≠ 1 →
        psi (L.subtype z1) = psi (L.subtype z2)) →
      IsIrreducibleCharacterOnGroup psi →
      ∀ z : Z, (z : L) ≠ 1 →
        IsIntegral Int
          ((psi (L.subtype z) - psi 1) / (qcard : Complex))) :
    (a : Int) ∣ lambda := by
  classical
  let e : ClassFunction G := TY (eta1 : ClassFunction L)
  let res : ClassFunction L := subgroupRestriction L e
  have heVirt : Theory.Character.IsVirtualCharacter e := by
    exact hTY.2.1 (eta1 : ClassFunction L)
      (integerSpan_of_mem Y eta1.property)
  have heSelf : scalarProduct G e e = 1 := by
    calc
      scalarProduct G e e =
          scalarProduct L (eta1 : ClassFunction L) (eta1 : ClassFunction L) :=
        isCFLinearIsometryOnSpan_apply_of_mem
          hTY.1 eta1.property eta1.property
      _ = 1 := scalarProduct_irreducibleCharacter_self (hYirr eta1)
  have heSigned : Section3.IsSignedIrreducibleCharacter e :=
    Section5.signed_irreducible_of_virtual_norm_one_pf59 heVirt heSelf
  have heClass : IsClassFunction e :=
    step8_isClassFunction_of_signed heSigned
  have hresVirt : Theory.Character.IsVirtualCharacter res :=
    step8_subgroupRestriction_isVirtualCharacter L heVirt
  have hresClass : IsClassFunction res :=
    step8_isClassFunction_subgroupRestriction L heClass
  have hetaVirt : Theory.Character.IsVirtualCharacter
      (eta1 : ClassFunction L) :=
    Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hYirr eta1)
  obtain ⟨m, hm⟩ :=
    Section3.scalarProduct_isVirtualCharacter_eq_int hresVirt hetaVirt
  let mu : Int := m - 1
  let ai : X → Nat := fun chi =>
    if chi = chi1 then 1 else Classical.choose (hdivX chi)
  have haiDegree (chi : X) :
      degree (chi : ClassFunction L) =
        (ai chi : Complex) * degree (chi1 : ClassFunction L) := by
    by_cases hchi : chi = chi1
    · subst chi
      simp [ai]
    · simpa [ai, hchi] using Classical.choose_spec (hdivX chi)
  let dX : X → Nat := fun chi => ai chi * a * dcard
  have hdegX (chi : X) :
      degree (chi : ClassFunction L) = (dX chi : Complex) := by
    rw [haiDegree chi, hdegreeBase, hdegreeEta]
    simp [dX, Nat.cast_mul]
    ring
  have haiOne : ai chi1 = 1 := by simp [ai]
  have hdXchi1 : dX chi1 = a * dcard := by simp [dX, haiOne]
  have haNe : a ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one ha)
  have haC : (a : Complex) ≠ 0 := by exact_mod_cast haNe
  have hdC : (dcard : Complex) ≠ 0 := by exact_mod_cast hdcard
  have hdXchi1Ne : (dX chi1 : Complex) ≠ 0 := by
    simpa [hdXchi1, Nat.cast_mul] using mul_ne_zero haC hdC
  have hcrossRev (chi : X) :
      scalarProduct G e (TX (chi : ClassFunction L)) = 0 := by
    have hstar := scalarProduct_star_swap
      (G := G) e (TX (chi : ClassFunction L))
    rw [hcross chi eta1] at hstar
    simpa using hstar.symm
  have hcoeffRight (chi : X) :
      scalarProduct L res (chi : ClassFunction L) =
        (ai chi : Complex) * scalarProduct L res (chi1 : ClassFunction L) := by
    let diff : ClassFunction L :=
      (chi : ClassFunction L) -
        (ai chi : Complex) • (chi1 : ClassFunction L)
    have hdiffDegree : degree diff = 0 := by
      change degree (chi : ClassFunction L) -
          (ai chi : Complex) * degree (chi1 : ClassFunction L) = 0
      rw [haiDegree chi]
      ring
    have hdiffSpan : integerSpan X diff :=
      integerSpan_sub
        (integerSpan_of_mem X chi.property)
        (by simpa using (integerSpan_zsmul (ai chi : Int)
          (integerSpan_of_mem X chi1.property)))
    have hdiffOn : integerSpanOn X puncturedSet diff :=
      ⟨hdiffSpan, (supportedOn_puncturedSet_iff_degree_eq_zero diff).2 hdiffDegree⟩
    have hTXdiff : TX diff = inducedCFLinear L diff :=
      hTX.2.2 diff hdiffOn
    have hglobal : scalarProduct G e (inducedCF L diff) = 0 := by
      change scalarProduct G e (inducedCFLinear L diff) = 0
      rw [← hTXdiff]
      change scalarProduct G e
        (TX ((chi : ClassFunction L) -
          (ai chi : Complex) • (chi1 : ClassFunction L))) = 0
      rw [map_sub, map_smul, Section5.scalarProduct_sub_right,
        scalarProduct_smul_right, hcrossRev chi, hcrossRev chi1]
      simp
    rw [inducedClassFunction_frobenius_right L diff e heClass] at hglobal
    change scalarProduct L res
      ((chi : ClassFunction L) -
        (ai chi : Complex) • (chi1 : ClassFunction L)) = 0 at hglobal
    rw [Section5.scalarProduct_sub_right, scalarProduct_smul_right] at hglobal
    simpa using sub_eq_zero.mp hglobal
  have hTYsum (eta : Y) :
      scalarProduct G (∑ zeta : Y, TY (zeta : ClassFunction L))
        (TY (eta : ClassFunction L)) = 1 := by
    have hTYgram (zeta : Y) :
        scalarProduct G (TY (zeta : ClassFunction L))
          (TY (eta : ClassFunction L)) = if zeta = eta then 1 else 0 := by
      rw [isCFLinearIsometryOnSpan_apply_of_mem
        hTY.1 zeta.property eta.property]
      split_ifs with hEq
      · subst zeta
        exact scalarProduct_irreducibleCharacter_self (hYirr eta)
      · exact scalarProduct_irreducibleCharacter_eq_zero_of_ne
          (hYirr zeta) (hYirr eta)
          (by intro h; exact hEq (Subtype.ext h))
    have hsumEq : (∑ zeta : Y, TY (zeta : ClassFunction L)) =
        (fun g : G => ∑ zeta : Y, (TY (zeta : ClassFunction L)) g) := by
      ext g
      simp
    rw [hsumEq, scalarProduct_fintype_sum_left]
    rw [Finset.sum_eq_single eta]
    · simp [hTYgram eta]
    · intro zeta _hzeta hne
      simp [hTYgram zeta, hne]
    · simp
  let source : ClassFunction L :=
    (chi1 : ClassFunction L) -
      (a : Complex) • (eta1 : ClassFunction L)
  let w : ClassFunction G := inducedCF L source
  have hwCoeff : scalarProduct G w e = ((lambda - a : Int) : Complex) := by
    rw [show w = inducedCF L source from rfl]
    rw [show source = (chi1 : ClassFunction L) -
      (a : Complex) • (eta1 : ClassFunction L) from rfl]
    rw [hdecomp, scalarProduct_add_left, scalarProduct_add_left,
      scalarProduct_smul_left, scalarProduct_smul_left,
      heSelf, hTYsum eta1, hvorth eta1]
    push_cast
    ring
  have hswap (theta : ClassFunction L)
      (htheta : IsIrreducibleCharacterOnGroup theta) :
      scalarProduct L theta res = scalarProduct L res theta := by
    calc
      scalarProduct L theta res = star (scalarProduct L theta res) :=
        (step8_source_scalarProduct_star_eq_self_of_virtual htheta heVirt).symm
      _ = scalarProduct L res theta := scalarProduct_star_swap res theta
  have hsourceCoeff :
      scalarProduct L (chi1 : ClassFunction L) res -
          (a : Complex) * scalarProduct L (eta1 : ClassFunction L) res =
        ((lambda - a : Int) : Complex) := by
    calc
      scalarProduct L (chi1 : ClassFunction L) res -
          (a : Complex) * scalarProduct L (eta1 : ClassFunction L) res =
          scalarProduct L source res := by
        rw [show source = (chi1 : ClassFunction L) -
          (a : Complex) • (eta1 : ClassFunction L) from rfl]
        rw [Section5.scalarProduct_sub_left, scalarProduct_smul_left]
      _ = scalarProduct G w e := by
        exact (scalarProduct_inducedCF_left L source e heClass).symm
      _ = ((lambda - a : Int) : Complex) := hwCoeff
  let cInt : Int := lambda + (a : Int) * mu
  have hbaseCoeff : scalarProduct L res (chi1 : ClassFunction L) =
      (cInt : Complex) := by
    have hsourceCoeff' := hsourceCoeff
    rw [hswap (eta1 : ClassFunction L) (hYirr eta1), hm] at hsourceCoeff'
    calc
      scalarProduct L res (chi1 : ClassFunction L) =
          scalarProduct L (chi1 : ClassFunction L) res :=
        (hswap (chi1 : ClassFunction L)
          ((hXchar (chi1 : ClassFunction L)).1 chi1.property).1).symm
      _ = ((lambda - a : Int) : Complex) +
          (a : Complex) * (m : Complex) := sub_eq_iff_eq_add.mp hsourceCoeff'
      _ = (cInt : Complex) := by
        simp [cInt, mu]
        ring
  have hcoeffLeft (chi : X) :
      scalarProduct L (chi : ClassFunction L) res =
        ((dX chi : Complex) / (dX chi1 : Complex)) * (cInt : Complex) := by
    calc
      scalarProduct L (chi : ClassFunction L) res =
          star (scalarProduct L res (chi : ClassFunction L)) := by
        exact (scalarProduct_star_swap (G := L)
          (phi := (chi : ClassFunction L)) (psi := res)).symm
      _ = star ((ai chi : Complex) *
          scalarProduct L res (chi1 : ClassFunction L)) := by
        rw [hcoeffRight chi]
      _ = (ai chi : Complex) * (cInt : Complex) := by
        rw [hbaseCoeff]
        simp
      _ = ((dX chi : Complex) / (dX chi1 : Complex)) *
          (cInt : Complex) := by
        rw [show (dX chi : Complex) =
          (ai chi : Complex) * ((a : Complex) * (dcard : Complex)) by
            simp [dX, Nat.cast_mul]; ring]
        rw [show (dX chi1 : Complex) =
          (a : Complex) * (dcard : Complex) by
            rw [hdXchi1]
            push_cast
            ring]
        field_simp [haC, hdC]
  have hcstar : star (cInt : Complex) = (cInt : Complex) := by simp
  have hker := step8_source_residual_subgroupInKernel
    hXchar dX hresClass chi1 hcstar hdXchi1Ne hcoeffLeft
  have hresConst : constantOnNonidentitySubgroup Z res :=
    step8_constantOnNonidentitySubgroup_of_residual_kernel
      hXchar dX hdegX hker
  have heConst : ∀ z1 z2 : Z, (z1 : L) ≠ 1 → (z2 : L) ≠ 1 →
      e (L.subtype z1) = e (L.subtype z2) := by
    intro z1 z2 hz1 hz2
    have hz1' : z1 ≠ 1 := by
      intro h
      exact hz1 (congrArg Subtype.val h)
    have hz2' : z2 ≠ 1 := by
      intro h
      exact hz2 (congrArg Subtype.val h)
    simpa [res, subgroupRestriction] using hresConst z1 z2 hz1' hz2'
  rcases heSigned with ⟨epsilon, hepsilon, theta, htheta, he⟩
  have hthetaConst : ∀ z1 z2 : Z,
      (z1 : L) ≠ 1 → (z2 : L) ≠ 1 →
        theta (L.subtype z1) = theta (L.subtype z2) := by
    intro z1 z2 hz1 hz2
    have h := heConst z1 z2 hz1 hz2
    rcases hepsilon with rfl | rfl
    · simpa [he] using h
    · simpa [he] using h
  have heIntegral (z : Z) (hz : (z : L) ≠ 1) :
      IsIntegral Int ((e (L.subtype z) - e 1) / (qcard : Complex)) := by
    have hthetaIntegral := hstep7 theta hthetaConst htheta z hz
    rcases hepsilon with rfl | rfl
    · simpa [he] using hthetaIntegral
    · have hneg := hthetaIntegral.neg
      (convert hneg using 1; simp [he]; ring)
  have hsub (z : Z) (hz : z ≠ 1) :
      res 1 - res (z : L) =
        ((cInt : Complex) / (dX chi1 : Complex)) * (Nat.card L : Complex) :=
    step8_sub_values_of_residual_kernel_weighted_X
      hXchar dX hdegX hker z hz
  have hqcard : qcard ≠ 0 := by
    intro hq
    have hzero : Nat.card L = 0 := by rw [hHcard, hq, Nat.mul_zero]
    exact Nat.card_pos.ne' hzero
  have hqC : (qcard : Complex) ≠ 0 := by exact_mod_cast hqcard
  let : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
  obtain ⟨z, hz⟩ := exists_ne (1 : Z)
  have hzL : (z : L) ≠ 1 := by
    intro hzOne
    exact hz (Subtype.ext hzOne)
  have hsubSimple : e 1 - e (L.subtype z) =
      (qcard : Complex) * ((cInt : Complex) / (a : Complex)) := by
    calc
      e 1 - e (L.subtype z) = res 1 - res (z : L) := by
        rfl
      _ = ((cInt : Complex) / (dX chi1 : Complex)) *
          (Nat.card L : Complex) := hsub z hz
      _ = (qcard : Complex) * ((cInt : Complex) / (a : Complex)) := by
        rw [hdXchi1, hHcard]
        push_cast
        field_simp [haC, hdC]
  have hquotEq :
      (e (L.subtype z) - e 1) / (qcard : Complex) =
        - (((lambda : Int) : Complex) / (a : Complex) + (mu : Complex)) := by
    calc
      (e (L.subtype z) - e 1) / (qcard : Complex) =
          - ((e 1 - e (L.subtype z)) / (qcard : Complex)) := by ring
      _ = - ((cInt : Complex) / (a : Complex)) := by
        rw [hsubSimple]
        field_simp [hqC]
      _ = - (((lambda : Int) : Complex) / (a : Complex) +
          (mu : Complex)) := by
        simp [cInt]
        field_simp [haC]
        ring
  have hsumIntegral : IsIntegral Int
      (((lambda : Int) : Complex) / (a : Complex) + (mu : Complex)) := by
    have h := heIntegral z hzL
    rw [hquotEq] at h
    simpa using h.neg
  have hmuIntegral : IsIntegral Int (mu : Complex) := by
    exact_mod_cast
      (isIntegral_algebraMap (R := Int) (A := Complex) (x := mu))
  have hlambdaIntegral : IsIntegral Int
      (((lambda : Int) : Complex) / ((a : Int) : Complex)) := by
    simpa using hsumIntegral.sub hmuIntegral
  exact Theory.Character.integer_division_of_integral_quotient
    (by exact_mod_cast haNe) hlambdaIntegral


private theorem feitSibley_step8_restriction_divisibility_core
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (_ : Odd (Nat.card d.D))
    (hstep4 : feitSibleyStep4Data d chars)
    (hstep5 : feitSibleyStep5Data d chars)
    (hstep6 : feitSibleyStep6Data d chars)
    (hstep7 : feitSibleyStep7Data d) :
    feitSibleyCoherent d chars := by
  classical
  let Z : Subgroup d.H := feitSibleyZ d
  let X : Finset (ClassFunction d.H) := feitSibleyX d chars
  let Y : Finset (ClassFunction d.H) := feitSibleyY d chars
  rcases hstep4 with
    ⟨hZne, hZnormal, hZleCenter, _hXY, hcoherentX, hcoherentY,
      _hXne, hYne, hYdegree, chi1, a, ha, hchi1Degree, hdivX⟩
  let : Z.Normal := hZnormal
  have hZleQ1 : Z ≤ d.Q1 :=
    hZleCenter.trans (by
      simpa [Z, feitSibleyCenterQ1H] using
        Subgroup.map_subtype_le (Subgroup.center d.Q1))
  have hXchar : ∀ chi : ClassFunction d.H, chi ∈ X ↔
      IsIrreducibleCharacterOnGroup chi ∧ ¬ subgroupInKernel' chi Z := by
    intro chi
    simp only [X, feitSibleyX, feitSibleySnonker, Finset.mem_filter]
    constructor
    · rintro ⟨hchiChars, hchiNotZ⟩
      exact ⟨((hchars chi).mp hchiChars).1, hchiNotZ⟩
    · rintro ⟨hchiIrr, hchiNotZ⟩
      have hchiNotQ1 : ¬ subgroupInKernel' chi d.Q1 := by
        intro hchiQ1
        exact hchiNotZ
          (subgroupInKernel'_mono_appendixIV hZleQ1 hchiQ1)
      exact ⟨(hchars chi).mpr ⟨hchiIrr, hchiNotQ1⟩, hchiNotZ⟩
  have hYsub : Y ⊆ chars := by
    intro eta heta
    exact (Finset.mem_filter.mp heta).1
  have hYirr : ∀ eta : Y,
      IsIrreducibleCharacterOnGroup (eta : ClassFunction d.H) := by
    intro eta
    exact ((hchars (eta : ClassFunction d.H)).mp (hYsub eta.property)).1
  rcases hcoherentX.2.2 with ⟨TX, hTX⟩
  rcases hcoherentY.2.2 with ⟨TY, hTY⟩
  have hcross : feitSibleyCrossOrthogonal d X Y TX TY := by
    exact hstep5 TX TY hTX hTY
  rcases hYne with ⟨eta1Value, heta1Value⟩
  let eta1 : Y := ⟨eta1Value, heta1Value⟩
  have hdegreeBase : degree (chi1 : ClassFunction d.H) =
      (a : Complex) * degree (eta1 : ClassFunction d.H) := by
    rw [hYdegree eta1]
    exact hchi1Degree
  rcases hstep6 TX TY chi1 eta1 a hdivX hTX hTY hcross ha hdegreeBase with
    ⟨v, lambda, hvvirt, hdecomp, hvorth, hfinish⟩
  apply hfinish
  have hQindex : d.Q.index = Nat.card d.D := by
    simpa [Subgroup.relIndex_top_right] using
      feitSibley_Q_relIndex_top_eq_card_D_appendixIV d
  have hHcard : Nat.card d.H = Nat.card d.D * Nat.card d.Q := by
    have hcard := Subgroup.index_mul_card d.Q
    rw [hQindex] at hcard
    exact hcard.symm
  have hstep7' : ∀ psi : ClassFunction G,
      (∀ z1 z2 : Z, (z1 : d.H) ≠ 1 → (z2 : d.H) ≠ 1 →
        psi (d.H.subtype z1) = psi (d.H.subtype z2)) →
      IsIrreducibleCharacterOnGroup psi →
      ∀ z : Z, (z : d.H) ≠ 1 →
        IsIntegral Int
          ((psi (d.H.subtype z) - psi 1) /
            (Nat.card d.Q : Complex)) := by
    unfold feitSibleyStep7Data at hstep7
    exact hstep7
  exact step8_restriction_divisibility
    d.H X Y Z (Nat.card d.Q) (Nat.card d.D)
      hZne hHcard hXchar hYirr TX TY hTX hTY hcross
      chi1 eta1 a ha Nat.card_pos.ne' (hYdegree eta1)
      hdegreeBase hdivX v lambda hvvirt hdecomp hvorth hstep7'
set_option maxHeartbeats 800000 in
/-- Peterfalvi Appendix IV, Feit-Sibley Theorem.  If `d = |D|` is odd, the
exceptional irreducible characters of `H` that are nontrivial on `Q1` are
coherent for induction from `H` to `G`. -/
public theorem feitSibley_theorem
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D)) :
    IsCoherentTriple puncturedSet chars
      (Section1.inducedCFLinear d.H) := by
  classical
  let coherent := feitSibleyCoherent d
  let Sker := feitSibleySker d chars
  let Snonker := feitSibleySnonker d chars
  let extensionOn := feitSibleyExtensionOn d
  let crossOrthogonal := feitSibleyCrossOrthogonal d

  let SderivedH := feitSibleySderivedH d
  let QderivedH := feitSibleyQderivedH d
  let Q1derivedH := feitSibleyQ1derivedH d
  let centerQ1H := feitSibleyCenterQ1H d
  let Z := feitSibleyZ d
  let X := feitSibleyX d chars
  let Y := feitSibleyY d chars

  have hYcard : 2 ≤ Y.card := by
    have hsolvQ1 : Group.IsSolvable d.Q1 := by
      by_cases hD : d.D = ⊥
      · let : IsZGroup d.Q1 := d.isZGroup_Q1_of_D_eq_bot hD
        infer_instance
      · let : Group.IsNilpotent d.Q1 :=
          d.isNilpotent_Q1_of_D_ne_bot hD
        exact IsNilpotent.to_isSolvable
    obtain ⟨chi, hchiChars, hchiKernel⟩ :=
      d.exists_exceptional_mem_derived_kernel chars hchars hsolvQ1
        d.internalDirectProduct_Q
    have hchiY : chi ∈ Y := by
      exact Finset.mem_filter.mpr ⟨hchiChars, hchiKernel⟩
    have hbarChars : conjugateCharacter chi ∈ chars := by
      let : d.Q.Normal := d.Q_normal
      rcases (lemma_2_a d chars hchars chi).mp hchiChars with
        ⟨phi, hphiIrr, hphiNotKernel, hind⟩
      apply (lemma_2_a d chars hchars (conjugateCharacter chi)).mpr
      refine ⟨conjugateCharacter phi,
        isIrreducibleCharacterOnGroup_conjugateCharacter hphiIrr, ?_, ?_⟩
      · intro hbarKernelQ1
        apply hphiNotKernel
        have hdouble :=
          Section6.subgroupInKernel'_conjugateCharacter
            (conjugateCharacter phi) hbarKernelQ1
        have hcc : conjugateCharacter (conjugateCharacter phi) = phi := by
          ext q
          simp [conjugateCharacter]
        simpa [hcc] using hdouble
      · calc
          inducedCF d.Q (conjugateCharacter phi) =
              conjugateCharacter (inducedCF d.Q phi) :=
            (conjugateCharacter_inducedCF d.Q phi).symm
          _ = conjugateCharacter chi := by rw [hind]
    have hbarKernel :
        subgroupInKernel' (conjugateCharacter chi) QderivedH :=
      Section6.subgroupInKernel'_conjugateCharacter chi hchiKernel
    have hbarY : conjugateCharacter chi ∈ Y := by
      exact Finset.mem_filter.mpr ⟨hbarChars, hbarKernel⟩
    have hbarNe : conjugateCharacter chi ≠ chi :=
      lemma_2_c d chars hchars hDodd chi hchiChars
    let pair : Finset (ClassFunction d.H) := {chi, conjugateCharacter chi}
    have hpairSubset : pair ⊆ Y := by
      intro psi hpsi
      simp [pair] at hpsi
      rcases hpsi with rfl | rfl
      · exact hchiY
      · exact hbarY
    have hpairCard : pair.card = 2 := by
      simp [pair, hbarNe.symm]
    calc
      2 = pair.card := hpairCard.symm
      _ ≤ Y.card := Finset.card_le_card hpairSubset

  have hbase_Qderived : coherent Y := by
    have hYsub : Y ⊆ chars := by
      intro chi hchi
      exact (Finset.mem_filter.mp hchi).1
    rcases lemma_2_b d chars hchars with ⟨hisoChars, htargetChars⟩
    apply lemma_1_b d.H Y (Section1.inducedCFLinear d.H) hYcard
    · intro chi
      exact ((hchars (chi : ClassFunction d.H)).mp
        (hYsub chi.property)).1
    · intro phi psi hphi hpsi
      exact hisoChars phi psi
        (Section5.integerSpanOn_mono hYsub hphi)
        (Section5.integerSpanOn_mono hYsub hpsi)
    · intro theta htheta
      exact htargetChars theta
        (Section5.integerSpanOn_mono hYsub htheta)
    · intro chi psi
      have hdegree (eta : Y) :
          degree (eta : ClassFunction d.H) =
            (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
        have hetaKernel :
            subgroupInKernel' (eta : ClassFunction d.H) QderivedH :=
          (Finset.mem_filter.mp eta.property).2
        have hetaChars : (eta : ClassFunction d.H) ∈ chars :=
          hYsub eta.property
        rcases
            (lemma_2_a d chars hchars
              (eta : ClassFunction d.H)).mp hetaChars with
          ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
        let : d.Q.Normal := d.Q_normal
        have hQderivedLe : QderivedH ≤ d.Q := by
          simpa [QderivedH, feitSibleyQderivedH] using
            Subgroup.map_subtype_le (derivedSubgroup d.Q)
        have : QderivedH.Normal := by
          dsimp [QderivedH]
          infer_instance
        have hQderivedSub :
            QderivedH.subgroupOf d.Q = derivedSubgroup d.Q := by
          dsimp [QderivedH]
          exact subgroupOf_map_subtype_eq (derivedSubgroup d.Q)
        rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
        have hindKernelPhi :
            subgroupInKernel' (inducedCF d.Q phi) QderivedH := by
          rw [hind]
          exact hetaKernel
        have hindKernel :
            subgroupInKernel' (inducedCF d.Q rho.character) QderivedH := by
          simpa [hphiEq] using hindKernelPhi
        have hrhoKernel :
            subgroupInKernel' rho.character
              (QderivedH.subgroupOf d.Q) :=
          (Section1.proposition_1_6_a d.Q QderivedH hQderivedLe rho).mpr
            hindKernel
        have hphiKernel :
            subgroupInKernel' phi (derivedSubgroup d.Q) := by
          simpa [hphiEq, hQderivedSub] using hrhoKernel
        have hphiDegree : degree phi = (1 : Complex) :=
          degree_eq_one_of_irreducible_subgroupInKernel_derived_appendixIV
            ⟨n, rho, hrhoIrr, hphiEq⟩ hphiKernel
        rw [← hind, degree_inducedClassFunction d.Q phi, hphiDegree]
        simp [Subgroup.relIndex_top_right]
      exact (hdegree chi).trans (hdegree psi).symm

  have hbase_abelian :
      (∀ x y : d.Q1, x * y = y * x) →
        coherent (Sker SderivedH) := by
    intro hab
    have hderived : QderivedH = SderivedH := by
      simpa [QderivedH, SderivedH, feitSibleyQderivedH, feitSibleySderivedH] using
        d.map_derivedSubgroup_Q_eq_S_of_Q1_commutative hab
    simpa [Y, feitSibleyY, Sker, feitSibleySker, QderivedH, SderivedH, hderived] using hbase_Qderived


  have hsourceNonempty : integerSpanOnNonempty chars puncturedSet := by
    have hYpos : 0 < Y.card := by omega
    obtain ⟨chi, hchiY⟩ := Finset.card_pos.mp hYpos
    have hchiChars : chi ∈ chars := (Finset.mem_filter.mp hchiY).1
    have hbarChars : conjugateCharacter chi ∈ chars := by
      let : d.Q.Normal := d.Q_normal
      rcases (lemma_2_a d chars hchars chi).mp hchiChars with
        ⟨phi, hphiIrr, hphiNotKernel, hind⟩
      apply (lemma_2_a d chars hchars (conjugateCharacter chi)).mpr
      refine ⟨conjugateCharacter phi,
        isIrreducibleCharacterOnGroup_conjugateCharacter hphiIrr, ?_, ?_⟩
      · intro hbarKernelQ1
        apply hphiNotKernel
        have hdouble :=
          Section6.subgroupInKernel'_conjugateCharacter
            (conjugateCharacter phi) hbarKernelQ1
        have hcc : conjugateCharacter (conjugateCharacter phi) = phi := by
          ext q
          simp [conjugateCharacter]
        simpa [hcc] using hdouble
      · calc
          inducedCF d.Q (conjugateCharacter phi) =
              conjugateCharacter (inducedCF d.Q phi) :=
            (conjugateCharacter_inducedCF d.Q phi).symm
          _ = conjugateCharacter chi := by rw [hind]
    have hbarNe : conjugateCharacter chi ≠ chi :=
      lemma_2_c d chars hchars hDodd chi hchiChars
    exact integerSpanOnNonempty_of_conjugate_pair
      hchiChars hbarChars hbarNe.symm
      (isCharacter_of_isIrreducibleCharacterOnGroup
        ((hchars chi).mp hchiChars).1)

  have hcoherent_D_bot : d.D = ⊥ → coherent chars := by
    intro hD
    have hQtop : d.Q = ⊤ := by
      simpa [hD] using d.H_eq_Q_sup_D
    have hQInG_eq_H : d.QInG = d.H := by
      rw [FeitSibleyData.QInG, hQtop]
      simpa [MonoidHom.range_eq_map] using
        (d.H.range_subtype : d.H.subtype.range = d.H)
    have hQ1ne : d.Q1 ≠ ⊥ := by
      intro hQ1
      apply d.Q1_not_two_group
      exact hQ1.symm ▸ IsPGroup.of_bot (p := 2) (G := d.H)
    have hQne : d.Q ≠ ⊥ := by
      intro hQ
      apply hQ1ne
      apply le_bot_iff.mp
      simpa [hQ] using d.Q1_le_Q
    have hQInGne : d.QInG ≠ ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := d.Q) (f := d.H.subtype) d.H.subtype_injective).not.mpr hQne
    have hHne : d.H ≠ ⊥ := by
      simpa [hQInG_eq_H] using hQInGne
    have hTI : ∀ g : G, g ∉ d.H → Disjoint d.H (d.H.conjBy g) := by
      intro g hg
      have hginv : g⁻¹ ∉ d.H := by
        intro h
        apply hg
        simpa using d.H.inv_mem h
      rw [← hQInG_eq_H]
      simpa [FeitSibleyData.QInG,
        PFchapter1section1.rightConjugate] using
        d.Q_TI_in_G g⁻¹ hginv
    apply coherent_of_TI_exceptional d.H hHne hTI chars
    · intro chi hchi
      exact ((hchars chi).mp hchi).1
    · exact hsourceNonempty
  have step1 :
      d.D ≠ ⊥ →
      (¬ (∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1)) →
        coherent (Sker SderivedH) := by
    intro hD hp
    let : Group.IsNilpotent d.Q1 := d.isNilpotent_Q1_of_D_ne_bot hD
    let : d.S.Normal := d.S_normal
    by_cases hab : ∀ x y : d.Q1, x * y = y * x
    · exact hbase_abelian hab
    · let : d.Q1.Normal := d.Q1_normal
      have hQderived :
          QderivedH = SderivedH ⊔ Q1derivedH := by
        simpa [QderivedH, SderivedH, Q1derivedH, feitSibleyQderivedH, feitSibleySderivedH, feitSibleyQ1derivedH] using
          d.map_derivedSubgroup_Q_eq_sup
      let P : Subgroup d.H → Prop := fun Q2 =>
        Q2 ≤ Q1derivedH ∧ Q2.Normal ∧
          coherent (Sker (SderivedH ⊔ Q2))
      have hPtop : P Q1derivedH := by
        refine ⟨le_rfl, ?_, ?_⟩
        · dsimp [Q1derivedH]
          infer_instance
        · simpa [Y, feitSibleyY, Sker, feitSibleySker, QderivedH, SderivedH, Q1derivedH, hQderived] using hbase_Qderived
      rcases Finite.exists_le_minimal (p := P) hPtop with
        ⟨Q2, _hQ2sel, hQ2min⟩
      rcases hQ2min.prop with ⟨hQ2le, hQ2normal, hcohQ2⟩
      by_cases hQ2bot : Q2 = ⊥
      · subst Q2
        simpa using hcohQ2
      · let : Q2.Normal := hQ2normal
        obtain ⟨Q3, hchief⟩ :=
          exists_chiefFactor_below_appendixIV Q2 hQ2bot
        let : Q3.Normal := hchief.normal_K
        have hQ3le : Q3 ≤ Q1derivedH :=
          hchief.lt.le.trans hQ2le
        have hnotcohQ3 :
            ¬ coherent (Sker (SderivedH ⊔ Q3)) := by
          intro hcohQ3
          have hP3 : P Q3 :=
            ⟨hQ3le, inferInstance, hcohQ3⟩
          have hQ2leQ3 :=
            hQ2min.le_of_le hP3 hchief.lt.le
          exact hchief.lt.2 hQ2leQ3
        let U : Finset (ClassFunction d.H) :=
          Sker (SderivedH ⊔ Q2)
        let V : Finset (ClassFunction d.H) :=
          Sker (SderivedH ⊔ Q3)
        have hsup_le :
            SderivedH ⊔ Q3 ≤ SderivedH ⊔ Q2 :=
          sup_le_sup le_rfl hchief.lt.le
        have hUV : U ⊆ V := by
          intro chi hchi
          rcases Finset.mem_filter.mp hchi with ⟨hchiChars, hchiKernel⟩
          refine Finset.mem_filter.mpr ⟨hchiChars, ?_⟩
          intro x
          exact hchiKernel ⟨x, hsup_le x.property⟩
        have hsolvQ1 : Group.IsSolvable d.Q1 :=
          IsNilpotent.to_isSolvable
        obtain ⟨chi0, hchi0Chars, hchi0KernelQderived⟩ :=
          d.exists_exceptional_mem_derived_kernel
            chars hchars hsolvQ1 d.internalDirectProduct_Q
        have hQ2sup_le : SderivedH ⊔ Q2 ≤ QderivedH := by
          rw [hQderived]
          exact sup_le_sup le_rfl hQ2le
        have hchi0U : chi0 ∈ U := by
          refine Finset.mem_filter.mpr ⟨hchi0Chars, ?_⟩
          intro x
          exact hchi0KernelQderived ⟨x, hQ2sup_le x.property⟩
        have hchi0Degree :
            degree chi0 =
              (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) :=
          d.degree_eq_relIndex_of_exceptional_derived_kernel
            chars hchars chi0 hchi0Chars hchi0KernelQderived
        have hVsub : V ⊆ chars := by
          intro chi hchi
          exact (Finset.mem_filter.mp hchi).1
        have hirrV :
            ∀ chi : V,
              IsIrreducibleCharacterOnGroup
                (chi : ClassFunction d.H) := by
          intro chi
          exact ((hchars (chi : ClassFunction d.H)).mp
            (hVsub chi.property)).1
        rcases lemma_2_b d chars hchars with ⟨hisoChars, htargetChars⟩
        have hisoV :
            isCFLinearIsometryOnSpanOn V puncturedSet
              (Section1.inducedCFLinear d.H) := by
          intro phi theta hphi htheta
          exact hisoChars phi theta
            (Section5.integerSpanOn_mono hVsub hphi)
            (Section5.integerSpanOn_mono hVsub htheta)
        have htargetV :
            ∀ phi : ClassFunction d.H,
              integerSpanOn V puncturedSet phi →
                Theory.Character.IsVirtualCharacter
                    (Section1.inducedCFLinear d.H phi) ∧
                  supportedOn
                    (Section1.inducedCFLinear d.H phi) puncturedSet := by
          intro phi hphi
          exact htargetChars phi
            (Section5.integerSpanOn_mono hVsub hphi)
        have hdivV :
            ∀ psi : ClassFunction d.H, psi ∈ V →
              ∃ n : Nat,
                degree psi = (n : Complex) * degree chi0 := by
          intro psi hpsiV
          have hpsiChars : psi ∈ chars := hVsub hpsiV
          rcases (lemma_2_a d chars hchars psi).mp hpsiChars with
            ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
          rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
          refine ⟨n, ?_⟩
          rw [← hind, degree_inducedClassFunction d.Q phi,
            hphiEq, degree_representation_character, hchi0Degree]
          simp [Subgroup.relIndex_top_right, mul_comm]
        obtain ⟨psi, hpsiV, hpsiU, hdegreeBound⟩ :=
          exists_degree_obstruction_of_not_coherent_appendixIV
            d.H U V (Section1.inducedCFLinear d.H) hUV chi0 hchi0U
            hirrV hisoV htargetV hdivV
            (by simpa [U] using hcohQ2)
            (by simpa [V] using hnotcohQ3)
        let R : Subgroup d.H := SderivedH ⊔ Q2
        have : R.Normal := by
          dsimp [R, SderivedH]
          infer_instance
        have hUchar :
            ∀ chi : ClassFunction d.H, chi ∈ U ↔
              IsIrreducibleCharacterOnGroup chi ∧
                subgroupInKernel' chi R ∧
                  ¬ subgroupInKernel' chi d.Q1 := by
          intro chi
          simp only [U, Sker, Finset.mem_filter, R]
          rw [hchars chi]
          tauto
        have hsumU :=
          exceptional_kernel_degree_sq_sum_appendixIV
            R d.Q1 U hUchar
        have hpsiKernel :
            subgroupInKernel' psi (SderivedH ⊔ Q3) :=
          (Finset.mem_filter.mp hpsiV).2
        have hpsiChars : psi ∈ chars := hVsub hpsiV
        rcases (lemma_2_a d chars hchars psi).mp hpsiChars with
          ⟨phi, hphiIrr, _hphiNotKernel, hind⟩
        rcases hphiIrr with ⟨n, rho, hrhoIrr, hphiEq⟩
        have hQderivedLe : QderivedH ≤ d.Q := by
          simpa [QderivedH, feitSibleyQderivedH] using
            Subgroup.map_subtype_le (derivedSubgroup d.Q)
        have hR3leQ : SderivedH ⊔ Q3 ≤ d.Q := by
          calc
            SderivedH ⊔ Q3 ≤ SderivedH ⊔ Q1derivedH :=
              sup_le_sup le_rfl hQ3le
            _ = QderivedH := hQderived.symm
            _ ≤ d.Q := hQderivedLe
        have : SderivedH.Normal := by
          dsimp [SderivedH]
          infer_instance
        have : (SderivedH ⊔ Q3).Normal := inferInstance
        let : d.Q.Normal := d.Q_normal
        have hindKerPhi :
            subgroupInKernel' (inducedCF d.Q phi)
              (SderivedH ⊔ Q3) := by
          rw [hind]
          exact hpsiKernel
        have hindKerRho :
            subgroupInKernel' (inducedCF d.Q rho.character)
              (SderivedH ⊔ Q3) := by
          simpa [hphiEq] using hindKerPhi
        have hrhoKerCF :
            subgroupInKernel' rho.character
              ((SderivedH ⊔ Q3).subgroupOf d.Q) :=
          (Section1.proposition_1_6_a d.Q (SderivedH ⊔ Q3) hR3leQ rho).mpr
            hindKerRho
        have hrepker :
            subgroupInRepresentationKernel rho
              ((SderivedH ⊔ Q3).subgroupOf d.Q) :=
          (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
            rho _).mp hrhoKerCF
        let N : Subgroup d.Q1 := Q3.subgroupOf d.Q1
        let : N.Normal := (inferInstance : Q3.Normal).subgroupOf d.Q1
        let e : d.S × d.Q1 ≃* d.Q :=
          Section3.internalDirectProductMulEquiv d.internalDirectProduct_Q
        have hker :
            ∀ x : (commutator d.S).prod N, rho (e x) = 1 := by
          intro x
          have hs : ((x.1.1 : d.S) : d.H) ∈
              Subgroup.map d.S.subtype (derivedSubgroup d.S) := by
            apply Subgroup.mem_map.mpr
            exact ⟨x.1.1, x.property.1, rfl⟩
          have hq : (x.1.2 : d.H) ∈ Q3 := x.property.2
          have hinl :
              ((e (MonoidHom.inl d.S d.Q1 x.1.1) : d.Q) : d.H) =
                (x.1.1 : d.H) := by
            simpa [e] using congrArg Subtype.val
              (Section3.internalDirectProductMulEquiv_apply_inl
                d.internalDirectProduct_Q x.1.1)
          have hinr :
              ((e (MonoidHom.inr d.S d.Q1 x.1.2) : d.Q) : d.H) =
                (x.1.2 : d.H) := by
            simpa [e] using congrArg Subtype.val
              (Section3.internalDirectProductMulEquiv_apply_inr
                d.internalDirectProduct_Q x.1.2)
          have hxdecomp :
              (x.1 : d.S × d.Q1) =
                MonoidHom.inl d.S d.Q1 x.1.1 *
                  MonoidHom.inr d.S d.Q1 x.1.2 := by
            ext <;> simp
          have hemap :
              e x =
                e (MonoidHom.inl d.S d.Q1 x.1.1 *
                  MonoidHom.inr d.S d.Q1 x.1.2) :=
            congrArg e hxdecomp
          have heq : ((e x : d.Q) : d.H) =
              (x.1.1 : d.H) * (x.1.2 : d.H) := by
            rw [hemap, map_mul]
            exact congrArg₂ (fun a b : d.H => a * b) hinl hinr
          apply hrepker ⟨e x, ?_⟩
          change ((e x : d.Q) : d.H) ∈ SderivedH ⊔ Q3
          rw [heq]
          exact (SderivedH ⊔ Q3).mul_mem
            ((show SderivedH ≤ SderivedH ⊔ Q3 from le_sup_left) hs)
            ((show Q3 ≤ SderivedH ⊔ Q3 from le_sup_right) hq)
        let : Representation.IsIrreducible rho := hrhoIrr
        have hnSq :
            n ^ 2 ≤
              (Subgroup.comap (QuotientGroup.mk' N)
                (Subgroup.center (d.Q1 ⧸ N))).index := by
          simpa [N, e, derivedSubgroup, derivedSeries_one] using
            (irreducible_finrank_sq_le_index_prod_centerModulo_appendixIV
              e N rho hker)
        have hpsiDegree :
            degree psi =
              (n : Complex) *
                (d.Q.relIndex (⊤ : Subgroup d.H) : Complex) := by
          rw [← hind, degree_inducedClassFunction d.Q phi, hphiEq,
            degree_representation_character]
          simp [Subgroup.relIndex_top_right, mul_comm]
        have hSderivedLeS : SderivedH ≤ d.S := by
          simpa [SderivedH, feitSibleySderivedH] using
            Subgroup.map_subtype_le (derivedSubgroup d.S)
        have hQ1derivedLeQ1 : Q1derivedH ≤ d.Q1 := by
          simpa [Q1derivedH, feitSibleyQ1derivedH] using
            Subgroup.map_subtype_le (derivedSubgroup d.Q1)
        have hQ2leQ1 : Q2 ≤ d.Q1 :=
          hQ2le.trans hQ1derivedLeQ1
        have hRinfQ1 : R ⊓ d.Q1 = Q2 := by
          apply le_antisymm
          · intro x hx
            rcases Subgroup.mem_inf.mp hx with ⟨hxR, hxQ1⟩
            rcases (Subgroup.mem_sup_of_normal_right.mp hxR) with
              ⟨s, hs, q, hq, hsq⟩
            have hsQ1 : s ∈ d.Q1 := by
              have hseq : s = x * q⁻¹ := by
                rw [← hsq]
                simp
              rw [hseq]
              exact d.Q1.mul_mem hxQ1 (d.Q1.inv_mem (hQ2leQ1 hq))
            have hsOne : s = 1 := by
              apply Subgroup.mem_bot.mp
              exact d.S_disjoint_Q1.le_bot
                ⟨hSderivedLeS hs, hsQ1⟩
            rw [hsOne, one_mul] at hsq
            exact hsq ▸ hq
          · intro x hx
            exact Subgroup.mem_inf.mpr
              ⟨(show Q2 ≤ R from le_sup_right) hx, hQ2leQ1 hx⟩
        have hrelIndex :
            R.relIndex (R ⊔ d.Q1) = Q2.relIndex d.Q1 := by
          calc
            R.relIndex (R ⊔ d.Q1) = R.relIndex d.Q1 :=
              Subgroup.relIndex_sup_left d.Q1 R
            _ = (R ⊓ d.Q1).relIndex d.Q1 :=
              (Subgroup.inf_relIndex_right R d.Q1).symm
            _ = Q2.relIndex d.Q1 := by rw [hRinfQ1]
        have hTleQ : R ⊔ d.Q1 ≤ d.Q := by
          rw [show R = SderivedH ⊔ Q2 from rfl]
          exact sup_le
            (sup_le (hSderivedLeS.trans d.S_le_Q)
              (hQ2leQ1.trans d.Q1_le_Q))
            d.Q1_le_Q
        have hd0Nat :
            d.Q.relIndex (⊤ : Subgroup d.H) ≤
              Nat.card (d.H ⧸ (R ⊔ d.Q1)) := by
          rw [Subgroup.relIndex_top_right, ← Subgroup.index_eq_card]
          exact Subgroup.index_antitone hTleQ
        have hchi0Re :
            (degree chi0).re =
              (d.Q.relIndex (⊤ : Subgroup d.H) : Real) := by
          rw [hchi0Degree]
          simp
        have hd0 :
            (degree chi0).re ≤
              (Nat.card (d.H ⧸ (R ⊔ d.Q1)) : Real) := by
          rw [hchi0Re]
          exact_mod_cast hd0Nat
        have hpsiReNonneg : 0 ≤ (degree psi).re := by
          rw [hpsiDegree]
          simp
          positivity
        have h11raw :=
          relIndex_sub_one_le_two_mul_of_degree_obstruction_appendixIV
            R (R ⊔ d.Q1) le_sup_left
            (∑ chi : U,
              (degree (chi : ClassFunction d.H)).re ^ 2)
            (degree psi).re (degree chi0).re
            hpsiReNonneg hsumU hdegreeBound hd0
        have h11 :
            (Q2.relIndex d.Q1 : Real) - 1 ≤
              2 * (degree psi).re := by
          simpa [hrelIndex] using h11raw
        let Z0 : Subgroup d.Q1 :=
          Subgroup.comap (QuotientGroup.mk' N)
            (Subgroup.center (d.Q1 ⧸ N))
        have hnSqZ0 : n ^ 2 ≤ Z0.index := by
          simpa [Z0] using hnSq
        have hnSqReal : (n : Real) ^ 2 ≤ (Z0.index : Real) := by
          exact_mod_cast hnSqZ0
        have hpsiRe :
            (degree psi).re =
              (n : Real) *
                (d.Q.relIndex (⊤ : Subgroup d.H) : Real) := by
          rw [hpsiDegree]
          simp
        have h12 :
            (degree psi).re ^ 2 ≤
              (d.Q.relIndex (⊤ : Subgroup d.H) : Real) ^ 2 *
                (Z0.index : Real) := by
          rw [hpsiRe]
          calc
            ((n : Real) *
                (d.Q.relIndex (⊤ : Subgroup d.H) : Real)) ^ 2 =
                (d.Q.relIndex (⊤ : Subgroup d.H) : Real) ^ 2 *
                  (n : Real) ^ 2 := by ring
            _ ≤
                (d.Q.relIndex (⊤ : Subgroup d.H) : Real) ^ 2 *
                  (Z0.index : Real) :=
              mul_le_mul_of_nonneg_left hnSqReal (sq_nonneg _)
        let Z3 : Subgroup d.H := Z0.map d.Q1.subtype
        let : Z3.Normal := by
          simpa [Z3, Z0, N] using
            (centerModulo_preimage_normal_appendixIV d.Q1 Q3)
        have hQ2leZ3 : Q2 ≤ Z3 := by
          simpa [Z3, Z0, N] using
            (chiefFactor_le_centerModulo_preimage_appendixIV
              d.Q1 Q2 Q3 hchief hQ2leQ1)
        have hZ3leQ1 : Z3 ≤ d.Q1 := by
          simpa [Z3] using Subgroup.map_subtype_le Z0
        have hstrict : Q2 < Z3 ∧ Z3 < d.Q1 := by
          simpa [Z3, Z0, N, feitSibleyCenterModuloPreimageH,
            feitSibleyCenterModuloPreimage] using
            (feitSibley_step1_strict_center_core
              d Q2 Q3 hp hchief hQ2le)
        have hcontra : False := by
          apply feitSibley_step1_regular_index_contradiction_core
            d Q2 Q3 hD hDodd hstrict.1 hstrict.2
            (degree psi).re h11
          simpa [Z0, N, feitSibleyCenterModuloPreimage] using h12
        exact hcontra.elim

  have step2 :
      coherent (Sker SderivedH) → coherent chars := by
    intro hcoherent
    exact feitSibley_step2_chief_descent_core
      d chars hchars hDodd hcoherent

  have step3 :
      (∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1) →
      (¬ (∀ x y : d.Q1, x * y = y * x)) →
      ∀ R : Subgroup d.H,
        R ≠ ⊥ →
        R.Normal →
        R ≤ centerQ1H →
        coherent (Snonker R) := by
    intro hp hab R hRne hRnormal hRle
    exact feitSibley_step3_nonkernel_coherence_core
      d chars hchars hDodd hp hab R hRne hRnormal hRle

  have step4 :
      (∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1) →
      (¬ (∀ x y : d.Q1, x * y = y * x)) →
      feitSibleyStep4Data d chars := by
    intro hp hab
    have hZprops :
        Z ≠ ⊥ ∧ Z.Normal ∧ Z ≤ centerQ1H :=
      feitSibley_step4_Z_properties d hp hab
    have hcoherentX : coherent X :=
      step3 hp hab Z hZprops.1 hZprops.2.1 hZprops.2.2
    have hfamily :
        Disjoint X Y ∧ coherent X ∧ coherent Y ∧
          X.Nonempty ∧ Y.Nonempty :=
      feitSibley_step4_XY_coherence_nonempty
        d chars hchars hZprops.1 hcoherentX hbase_Qderived hYcard
    have hdegrees :
        (∀ eta : Y,
          degree (eta : ClassFunction d.H) =
            (Nat.card d.D : Complex)) ∧
        ∃ chi1 : X, ∃ a : Nat,
          1 < a ∧
          degree (chi1 : ClassFunction d.H) =
            (a : Complex) * (Nat.card d.D : Complex) ∧
          ∀ chi : X, ∃ ai : Nat,
            degree (chi : ClassFunction d.H) =
              (ai : Complex) *
                degree (chi1 : ClassFunction d.H) :=
      feitSibley_step4_degree_data d chars hchars hDodd hp
        hZprops.1 hfamily.2.2.2.1 hfamily.2.2.2.2
    exact
      ⟨hZprops.1, hZprops.2.1, hZprops.2.2,
        hfamily.1, hfamily.2.1, hfamily.2.2.1,
        hfamily.2.2.2.1, hfamily.2.2.2.2,
        hdegrees.1, hdegrees.2⟩

  have step5 :
      (∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1) →
      (¬ (∀ x y : d.Q1, x * y = y * x)) →
      feitSibleyStep5Data d chars := by
    intro hp hab
    exact feitSibley_step5_cross_orthogonality_core
      d chars hchars hDodd (step4 hp hab)

  have step6 :
      (∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1) →
      (¬ (∀ x y : d.Q1, x * y = y * x)) →
      feitSibleyStep6Data d chars := by
    rintro ⟨p, hpprime, hpQ1⟩ hab
    exact feitSibley_step6_lambda_decomposition_core
      d chars hchars p hpprime hpQ1 hYcard
        (step4 ⟨p, hpprime, hpQ1⟩ hab) step2

  have step7 :
      (∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1) →
      (¬ (∀ x y : d.Q1, x * y = y * x)) →
      feitSibleyStep7Data d := by
    rintro ⟨p, hpprime, hpQ1⟩ hab
    exact feitSibley_step7_class_algebra_congruence_core
      d chars p hpprime hpQ1 hDodd
        (step4 ⟨p, hpprime, hpQ1⟩ hab)

  have step8 :
      (∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1) →
      (¬ (∀ x y : d.Q1, x * y = y * x)) →
      coherent chars := by
    intro hp hab
    exact feitSibley_step8_restriction_divisibility_core
      d chars hchars hDodd (step4 hp hab)
        (step5 hp hab) (step6 hp hab) (step7 hp hab)
  change coherent chars
  by_cases hD : d.D = ⊥
  · exact hcoherent_D_bot hD
  · by_cases hp : ∃ p : Nat, Nat.Prime p ∧ IsPGroup p d.Q1
    · by_cases hab : ∀ x y : d.Q1, x * y = y * x
      · exact step2 (hbase_abelian hab)
      · exact step8 hp hab
    · exact step2 (step1 hD hp)

end PFAppendixIV
end CFSG.BenderSuzuki
