module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOddCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitOddCoreAlgebra
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitQuaternionRank
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEEndQuat
public import CFSG.ClassicalInvolution.Asc77.IsSylow2InIsSylowOf
public import CFSG.GroupTheory.InvertingElements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FunGeneral
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.Blueprint CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open scoped Pointwise commutatorElement


theorem exists_q8_of_mem_funSet
    {X : Type} [Group X] [Finite X] {q : ℕ}
    (hΩ : HypOmegaGen {J : Subgroup X | IsFundamentalOver q J})
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred q) X (P : Subgroup X))
    {z : X} (hz : IsUniqueInvolution K z) :
    ∃ Q : Subgroup X, Q ≤ (P : Subgroup X) ⊓ K ∧
      Nonempty (Q ≃* QuaternionGroup 2) ∧ IsUniqueInvolution Q z := by
  have hPK : IsSylow2In ((P : Subgroup X) ⊓ K) K := IsSylow2In.of_isSylowOf hK.2
  obtain ⟨k, hk, ⟨ePK⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hΩ
    (mem_RSet_of_isSylow2In hK.1 hPK)
  have hePK : ↥((P : Subgroup X) ⊓ K) ≃* QuaternionGroup (2 ^ ((k + 2) - 2)) := by
    rw [Nat.add_sub_cancel]
    exact ePK
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ :=
    CFSG.CGT.PushingUpLit.SolKNA.R4.ThmE.EndGame.exists_subgroup_q8 (r := k + 2) (by omega) hePK
  have hQcard : Nat.card Q = 8 := by
    rw [Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num)
  have hzQ : z ∈ Q := CFSG.ClassicalInvolution.Asc77.AscL62.mem_of_uniqueInvolution_of_pGroup
    hz (hQ.trans inf_le_right) hQ2 (by rw [hQcard]; norm_num)
  exact ⟨Q, hQ, ⟨eQ⟩,
    CFSG.ClassicalInvolution.Asc77.AscL62.isUniqueInvolution_of_le hz
      (hQ.trans inf_le_right) hzQ⟩

theorem oddCore_commutator_le_centralizingLayer
    {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hdesc : ∃ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f ∧
      p ^ e = p ^ f ∧ LieModel (X ⧸ center X) t n p f)
    (hL2 : ¬ IsL2Over17 (X ⧸ center X) (p ^ e))
    (hΩ : HypOmegaGen {J : Subgroup X | IsFundamentalOver (p ^ e) J})
    (P : Sylow 2 X) (B : Subgroup X)
    (hBab : IsMulCommutative B) (hBo : Odd (Nat.card B))
    (hrank : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → CFSG.Open.pRank r B ≤ 2)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    {K : Subgroup X} (hK : K ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X))
    {z : X} (hz : IsUniqueInvolution K z) :
    let H := B ⊔ (P : Subgroup X)
    let O := (classicalInvolutionOddCore H).map H.subtype
    let E := ⁅O, zpowers z⁆
    let Γ := {x : X | ∃ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      J ≠ K ∧ x ∈ J}
    let A := centralizingLayer {J : Subgroup X | IsFundamentalOver (p ^ e) J} Γ
    K ≤ A ∧ E ≤ A ∧ E ≤ centralizer Γ := by
  intro H O E Γ A
  have hPK : IsSylow2In ((P : Subgroup X) ⊓ K) K := IsSylow2In.of_isSylowOf hK.2
  have hzP : z ∈ (P : Subgroup X) := (Sec6Gen.mem_of_isSylow2In hz hPK).1
  have hzH : z ∈ H := (le_sup_right : (P : Subgroup X) ≤ H) hzP
  obtain ⟨hEO, hinv, hEE⟩ := oddCore_commutator_involution hBab hBo P.isPGroup' rfl hperm hzH hz.sq
  have hOB : O ≤ B := oddCore_map_le_of_permuting hBo P.isPGroup' rfl hperm
  have hEB : E ≤ B := hEO.trans hOB
  have hEodd : Odd (Nat.card E) := Odd.of_dvd_nat hBo (Subgroup.card_dvd_of_le hEB)
  have hEab : IsMulCommutative E :=
    ⟨⟨fun a b => Subtype.ext (congrArg (fun b : B => (b : X))
      (hBab.is_comm.comm ⟨a, hEB a.2⟩ ⟨b, hEB b.2⟩))⟩⟩
  have hErank : ∀ r : ℕ, r.Prime → r ∣ Nat.card E → CFSG.Open.pRank r E ≤ 2 := fun r hr hdvd =>
    (CFSG.SectionRank.pRank_mono hr.one_lt hEB).trans
      (hrank r hr (hdvd.trans (Subgroup.card_dvd_of_le hEB)))
  obtain ⟨Q, hQPK, ⟨eQ⟩, hzQ⟩ := exists_q8_of_mem_funSet hΩ P hK hz
  have hQH : Q ≤ H := (hQPK.trans inf_le_left).trans le_sup_right
  have hQK : Q ≤ K := hQPK.trans inf_le_right
  have hQN : Q ≤ normalizer (E : Set X) := fun q hq =>
    mem_normalizer_oddCore_commutator_of_mem_of_centralizes (hQH hq)
      (hz.commute_of_mem (hQK hq)).symm
  have hcentralJ : ∀ J ∈ F14.FunSet (fundPred (p ^ e)) X (P : Subgroup X),
      J ≠ K → E ≤ centralizer (J : Set X) := by
    intro J hJ hJK
    have hc : ∀ k ∈ K, ∀ j ∈ J, k * j = j * k := by
      have h := funSet_commute_of_lieModel (Fact.out : p.Prime) hp2 hdesc hL2 P hK hJ hJK.symm
      exact fun k hk j hj => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hk) j hj).symm
    obtain ⟨zJ, hzJ⟩ := (hΩ.omega1 J hJ.1).1
    obtain ⟨R, hRPJ, ⟨eR⟩, hzR⟩ := exists_q8_of_mem_funSet hΩ P hJ hzJ
    have hRN : R ≤ normalizer (E : Set X) := fun r hr =>
      mem_normalizer_oddCore_commutator_of_mem_of_centralizes
        ((le_sup_right : (P : Subgroup X) ≤ H) ((hRPJ hr).1))
        (hc z hz.mem r (hRPJ hr).2).symm
    have hfix := quaternion_commuting_center_fixes_rank_two E Q R hEab hEodd hErank
      eQ eR hzQ hzR (fun q hq r hr => hc q (hQK hq) r (hRPJ hr).2) hQN hRN hinv
    intro a ha
    have haodd : Odd (orderOf a) := Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E ha)
    have hza : a * zJ = zJ * a := by
      have h := hfix a ha
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have haN := mem_normalizer_of_fundamental_involution_of_odd hp2 hL2 hJ.1 hzJ haodd hza
    exact CFSG.GroupTheory.mem_centralizer_of_inverted haodd (hinv a ha)
      (fun j hj => hc z hz.mem j hj) haN
  have hKG : K ≤ centralizer Γ := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨J, hJ, hJK, hx⟩
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (funSet_commute_of_lieModel (Fact.out : p.Prime) hp2 hdesc hL2 P hK hJ hJK.symm) hk) x hx)
  have hKA : K ≤ A := le_centralizingLayer ⟨hK.1, hKG⟩
  have hEG : E ≤ centralizer Γ := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    rintro x ⟨J, hJ, hJK, hx⟩
    exact Subgroup.mem_centralizer_iff.mp (hcentralJ J hJ hJK ha) x hx
  have hEA : E ≤ A := DeltaClosure.le_centralizingLayer_of_commutator_eq
    hΩ.conjInvariant hEG (hKA hz.mem) hEE
  exact ⟨hKA, hEA, hEG⟩

theorem injective_center_quotient_of_q8_inverts
    {A : Type} [Group A] [Finite A] (E Q : Subgroup A)
    (hEodd : Odd (Nat.card E)) (hEne : E ≠ ⊥)
    (eQ : Q ≃* QuaternionGroup 2) (zQ : Q) (hzQ : eQ zQ = QuaternionGroup.a 2)
    (hinv : ∀ x ∈ E, (zQ : A) * x * (zQ : A)⁻¹ = x⁻¹) :
    Function.Injective ((QuotientGroup.mk' (center A)).domRestrict E) ∧
      Function.Injective ((QuotientGroup.mk' (center A)).domRestrict Q) := by
  let π : A →* A ⧸ center A := QuotientGroup.mk' (center A)
  have hEinj : Function.Injective (π.domRestrict E) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxZ : (x : A) ∈ center A := (QuotientGroup.eq_one_iff _).mp hx
    have hc : (zQ : A) * (x : A) = (x : A) * (zQ : A) :=
      Subgroup.mem_center_iff.mp hxZ (zQ : A)
    have hfix : (zQ : A) * (x : A) * (zQ : A)⁻¹ = x := by rw [hc]; group
    have hxinv : (x : A) = (x : A)⁻¹ := hfix.symm.trans (hinv x x.2)
    exact Subtype.ext (CFSG.Wreathed.ComponentCoverConfinement.eq_one_of_eq_inv_of_odd
      (Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E x.2)) hxinv)
  have hzinj : π (zQ : A) ≠ 1 := by
    intro hz
    have hzZ : (zQ : A) ∈ center A := (QuotientGroup.eq_one_iff _).mp hz
    apply hEne
    rw [eq_bot_iff]
    intro x hx
    have hc : (zQ : A) * x = x * (zQ : A) :=
      (Subgroup.mem_center_iff.mp hzZ x).symm
    have hfix : (zQ : A) * x * (zQ : A)⁻¹ = x := by rw [hc]; group
    exact Subgroup.mem_bot.mpr (CFSG.Wreathed.ComponentCoverConfinement.eq_one_of_eq_inv_of_odd
      (Odd.of_dvd_nat hEodd (Subgroup.orderOf_dvd_natCard E hx)) (hfix.symm.trans (hinv x hx)))
  have hQinj : Function.Injective (π.domRestrict Q) := by
    let f : QuaternionGroup 2 →* A ⧸ center A := (π.domRestrict Q).comp eQ.symm.toMonoidHom
    have hf : Function.Injective f := by
      by_contra h
      have hkill := CFSG.ClassicalInvolution.q8_center_mem_ker f h
      apply hzinj
      have hz : eQ.symm (QuaternionGroup.a 2) = zQ := eQ.injective (by simp [hzQ])
      simpa [f, hz] using hkill
    intro x y hxy
    have h := hf (by
      change π (eQ.symm (eQ x)) = π (eQ.symm (eQ y))
      simpa using hxy)
    exact eQ.injective h
  exact ⟨hEinj, hQinj⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
