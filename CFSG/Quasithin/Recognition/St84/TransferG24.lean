module

public import CFSG.Quasithin.Recognition.St84.TransferG24Data
public import CFSG.GroupTheory.AlternatingFive.NaturalModule
public import CFSG.GroupTheory.AlternatingFive.TwoCoreQuotient
public import CFSG.Quasithin.Background.SpecialPGroupCenter
public import CFSG.GroupTheory.KleinFourCocycle
public import CFSG.Quasithin.Recognition.St84.TransferA5A5
public import CFSG.Quasithin.Recognition.St84.TreeBase
public import CFSG.Quasithin.Recognition.St84.G24Tools
public import CFSG.Quasithin.Recognition.St84.G24Data
public import CFSG.Quasithin.Recognition.Stroth.Y9Transport
public import CFSG.Quasithin.Recognition.F112J2Act
import CFSG.Quasithin.Background.C35InspSp4A
import CFSG.Quasithin.Recognition.GoldschmidtF112RPerfect
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.GroupTheory.PrimeCorefreeQuasisimple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannDelOrigData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelH0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathGate6
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.C1PackBasic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModPack28Proof
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Steps
public import CFSG.Quasithin.EmptyFaithful.SzF53BasE
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecB
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.H13.GoldschmidtC137Data
public import CFSG.Quasithin.H13.GoldschmidtC137U33Hyp
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Over
public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Self
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven
public import CFSG.Quasithin.Recognition.St84.AppTreeSAP1
public import CFSG.Quasithin.Recognition.St84.PushUp
public import CFSG.Quasithin.Recognition.St84.RelCentMap
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecD555
public import CFSG.Quasithin.Vol2.Ch11SecD556
public import CFSG.Quasithin.Vol2.Ch11SecD556I
public import CFSG.Quasithin.Vol2.Ch11SecD557A
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem f112sa_not_commutator_mem_of_g24
    {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (hD : G24TransferData L1 L2 S) {k : H}
    (hkK : k ∈ f112saK L1 L2 S) (hkL : k ∈ oTwoPrime (f112saP2' L1 L2 S))
    (hk3 : orderOf k = 3) :
    ¬ ∀ t ∈ S ⊓ f112saK L1 L2 S, ⁅k, t⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S) := by
  intro hk
  have hQβT : pCoreOf 2 (f112saP2' L1 L2 S) ≤ S ⊓ f112saK L1 L2 S :=
    F7.isSylowTwoOf_pCoreOf_le (f112sa_T_sylow_P2' hF)
  have hSNQ : S ≤ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
        ((le_sup_right : S ≤ bigB L1 L2 S) hs)))
  have hkNα : k ∈ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ ((f112saK_le_P1' L1 L2 S) hkK)
  have hkNβ : k ∈ Subgroup.normalizer (pCoreOf 2 (f112saP2' L1 L2 S) : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ ((oTwoPrime_le _) hkL)
  have hkN : k ∈ Subgroup.normalizer
      ((pCoreOf 2 (f112saP1' L1 L2 S) ⊓ pCoreOf 2 (f112saP2' L1 L2 S) : Subgroup H) : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hkNα n,
      Subgroup.mem_normalizer_iff.mp hkNβ n]
  have hdec := CFSG.Quasithin.St84.exists_mul_mem_centralizer_of_acts_trivially
    (Q := pCoreOf 2 (f112saP2' L1 L2 S))
    (Z := pCoreOf 2 (f112saP1' L1 L2 S) ⊓ pCoreOf 2 (f112saP2' L1 L2 S))
    inf_le_right (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hk3 hkNβ hkN
    (fun q hq z hz => Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hSNQ (Subgroup.mem_inf.mp (hQβT hq)).1) z).mp
        (Subgroup.mem_inf.mp hz).1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hq (Subgroup.mem_inf.mp hz).2)
          (Subgroup.inv_mem _ hq)⟩)
    (fun x hx => Subgroup.mem_inf.mpr ⟨hk x (hQβT hx),
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hkNβ x).mp hx) (Subgroup.inv_mem _ hx)⟩)
  have hle : pCoreOf 2 (f112saP2' L1 L2 S) ≤ pCoreOf 2 (f112saP1' L1 L2 S) := by
    intro x hx
    obtain ⟨z, hz, a, ha, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp hz).1 (hD.cent_right k hkL hk3 ha)
  have h := hD.card_inf
  rw [inf_eq_right.mpr hle, hD.card_right] at h
  norm_num at h

private theorem f112sa_X2_le_of_g24 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S)
    {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    ∀ x ∈ f112saX2 L1 L2 S, ⁅c, x⁆ ∈ S ⊓ f112saK L1 L2 S := by
  set T := S ⊓ f112saK L1 L2 S with hTdef
  set K := f112saK L1 L2 S with hKdef
  set Qα := pCoreOf 2 (f112saP1' L1 L2 S) with hQαdef
  set Lα := oTwoPrime (f112saP1' L1 L2 S) with hLαdef
  have hTK : pCoreOf 2 K = T := f112_pCoreOf_K_eq hF h1 h2
  have hTn : K ≤ Subgroup.normalizer (T : Set H) := by
    rw [← hTK]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hTLα : T ≤ Lα := (f112sa_T_sylow_oTwoPrime_P1' hF).1
  have hcB : c ∈ bigB L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S) hcS
  have hcNE : c ∈ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) hcB)
  have hcNQ : c ∈ Subgroup.normalizer (Qα : Set H) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hcNE
  have hcNL : c ∈ Subgroup.normalizer (Lα : Set H) := mem_normalizer_oTwoPrime hcNE
  let R : Subgroup H := relCent ⊤ Qα Lα
  have hcR : c ∈ R := ⟨Subgroup.mem_top c, hcNQ, hcL⟩
  intro x hx
  have hxK : x ∈ K := Subgroup.mem_sup_right hx
  set y := ⁅c, x⁆ with hy
  have hyX : y ∈ f112saX2 L1 L2 S := by
    have hconj : c * x * c⁻¹ ∈ f112saX2 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (f112sa_bigB_le_normalizer_X2 hF hcB) x).mp hx
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hx)
  have hyK : y ∈ K := Subgroup.mem_sup_right hyX
  have hyL : y ∈ oTwoPrime (f112saP2' L1 L2 S) :=
    f112sa_oTwoRes_le_oTwoPrime_P2' hF h2 (f112sa_X2_le_oTwoRes L1 L2 S hyX)
  have hxE : x ∈ f112saP1' L1 L2 S := Subgroup.mem_sup_right hx
  have hyR : y ∈ R := by
    have hxcx : x * c⁻¹ * x⁻¹ ∈ R := by
      have h := conj_mem_relCent (E := ⊤) (Z := Qα) (A := Lα) (g := x) (x := c⁻¹)
        (Subgroup.mem_normalizer_iff.mpr (by simp))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hxE)
        (le_normalizer_oTwoPrime _ hxE) (R.inv_mem hcR)
      simpa [mul_assoc] using h
    have e : y = c * (x * c⁻¹ * x⁻¹) := by
      rw [hy, commutatorElement_def]
      group
    rw [e]
    exact R.mul_mem hcR hxcx
  by_cases h3 : 3 ∣ orderOf y
  · exfalso
    have hk3 : orderOf (y ^ (orderOf y / 3)) = 3 :=
      orderOf_pow_orderOf_div (orderOf_pos_iff.mpr (isOfFinOrder_of_finite y)).ne' h3
    exact f112sa_not_commutator_mem_of_g24 hF hD (K.pow_mem hyK _)
      (Subgroup.pow_mem _ hyL _) hk3
      (fun t ht => (R.pow_mem hyR _).2.2 t (hTLα ht))
  · have hdvdK : orderOf y ∣ 2 ^ 12 * 3 ^ 2 := by
      rw [← hD.card_K]
      exact Subgroup.orderOf_dvd_natCard K hyK
    have hcop : Nat.Coprime (orderOf y) (3 ^ 2) :=
      Nat.Coprime.pow_right 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
    have hdvd2 : orderOf y ∣ 2 ^ 12 := hcop.dvd_of_dvd_mul_right hdvdK
    have hyp : IsPGroup 2 (Subgroup.zpowers y) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hzle : Subgroup.zpowers y ≤ T :=
      CFSG.Quasithin.Stroth.le_of_isSylowTwoOf_normal (f112sa_T_sylow_K hF)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (f112sa_T_sylow_K hF).1).mpr hTn)
        (Subgroup.zpowers_le.mpr hyK) hyp
    exact hzle (Subgroup.mem_zpowers y)

private theorem f112sa_commutator_mem_T_of_g24
    {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S)
    {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    ∀ x ∈ f112saK L1 L2 S, ⁅c, x⁆ ∈ S ⊓ f112saK L1 L2 S := by
  set T := S ⊓ f112saK L1 L2 S with hTdef
  set K := f112saK L1 L2 S with hKdef
  set Qα := pCoreOf 2 (f112saP1' L1 L2 S) with hQαdef
  set Lα := oTwoPrime (f112saP1' L1 L2 S) with hLαdef
  have hTK : pCoreOf 2 K = T := f112_pCoreOf_K_eq hF h1 h2
  have hTn : K ≤ Subgroup.normalizer (T : Set H) := by
    rw [← hTK]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQαT : Qα ≤ T := F7.isSylowTwoOf_pCoreOf_le (f112sa_T_sylow_P1' hF)
  have hTLα : T ≤ Lα := (f112sa_T_sylow_oTwoPrime_P1' hF).1
  have hcB : c ∈ bigB L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S) hcS
  have hcNE : c ∈ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S) hcB)
  have hcNQ : c ∈ Subgroup.normalizer (Qα : Set H) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hcNE
  have hcNL : c ∈ Subgroup.normalizer (Lα : Set H) := mem_normalizer_oTwoPrime hcNE
  let R : Subgroup H := relCent ⊤ Qα Lα
  have hcR : c ∈ R := ⟨Subgroup.mem_top c, hcNQ, hcL⟩
  let M : Subgroup H :=
    { carrier := {x | x ∈ K ∧ ⁅c, x⁆ ∈ T}
      one_mem' := ⟨K.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxK, hx⟩ ⟨hyK, hy⟩
        refine ⟨K.mul_mem hxK hyK, ?_⟩
        rw [commutatorElement_mul_right_eq_mul_conj]
        have e : ⁅c, x⁆ * x * ⁅c, y⁆ * x⁻¹ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) := by group
        rw [e]
        exact T.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hTn hxK) _).mp hy)
      inv_mem' := by
        rintro x ⟨hxK, hx⟩
        refine ⟨K.inv_mem hxK, ?_⟩
        have e : ⁅c, x⁻¹⁆ = x⁻¹ * ⁅c, x⁆⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hTn (K.inv_mem hxK)) _).mp (T.inv_mem hx) }
  have hX1M : f112saX1 L1 L2 S ≤ M := by
    intro x hx
    refine ⟨Subgroup.mem_sup_left hx, hQαT (hcL x ?_)⟩
    exact f112sa_oTwoRes_le_oTwoPrime_P1' hF h1 (f112sa_X1_le_oTwoRes L1 L2 S hx)
  have hX2M : f112saX2 L1 L2 S ≤ M := by
    intro x hx
    exact ⟨Subgroup.mem_sup_right hx, f112sa_X2_le_of_g24 hF h1 h2 hD hcS hcL x hx⟩
  intro x hx
  have hKM : K ≤ M := sup_le hX1M hX2M
  exact (hKM hx).2

private theorem f112saW_eq_bot_of_g24 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S) :
    f112saW L1 L2 S = ⊥ := by
  obtain ⟨k2, hk2X', -, hk23, -⟩ :=
    f112_exists_orderThree_X1 (L1 := L2) (L2 := L1) hF.symm h2
  have hk2X : k2 ∈ f112saX2 L1 L2 S := by
    simpa [f112saX1, f112saX2, bigB_comm] using hk2X'
  have hk2K : k2 ∈ f112saK L1 L2 S := Subgroup.mem_sup_right hk2X
  have hk2L : k2 ∈ oTwoPrime (f112saP2' L1 L2 S) :=
    f112sa_oTwoRes_le_oTwoPrime_P2' hF h2 (f112sa_X2_le_oTwoRes L1 L2 S hk2X)
  refine eq_bot_iff.mpr fun w hw => ?_
  obtain ⟨hwZ, hwK⟩ := Subgroup.mem_inf.mp hw
  have hwZb : w ∈ centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) := f112sa_centerOf_T_le_P2' hF hwZ
  have hkw : k2 * w = w * k2 := Subgroup.mem_centralizer_iff.mp hwK k2 hk2K
  have hcomm : ⁅w, k2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hkw.symm
  exact hD.natZ_right k2 hk2L hk23 w hwZb (by rw [hcomm]; exact Subgroup.one_mem _)

private theorem f112sa_conj_mem_S_of_g24 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S)
    {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    ∀ e ∈ f112saP1' L1 L2 S, e * c * e⁻¹ ∈ S := by
  set T := S ⊓ f112saK L1 L2 S with hTdef
  set Eα := f112saP1' L1 L2 S with hEαdef
  set Qα := pCoreOf 2 Eα with hQαdef
  set Lα := oTwoPrime Eα with hLαdef
  set Qβ := pCoreOf 2 (f112saP2' L1 L2 S) with hQβdef
  have hT : Qα ⊔ Qβ = T := f112_pCoreOf_sup_eq hF h1 h2
  have hQαT : Qα ≤ T := le_sup_left.trans hT.le
  have hTS : T ≤ S := inf_le_left
  have hENQ : Eα ≤ Subgroup.normalizer (Qα : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hcK := f112sa_commutator_mem_T_of_g24 hF h1 h2 hD hcS hcL
  have hKNL : f112saK L1 L2 S ≤ Subgroup.normalizer (Lα : Set H) := fun k hk =>
    mem_normalizer_oTwoPrime (Subgroup.le_normalizer ((f112saK_le_P1' L1 L2 S) hk))
  have hEsup : Eα ≤ Lα ⊔ f112saK L1 L2 S := by
    show oTwoRes L1 ⊔ f112saX2 L1 L2 S ≤ _
    exact sup_le ((f112sa_oTwoRes_le_oTwoPrime_P1' hF h1).trans le_sup_left)
      ((le_sup_right : f112saX2 L1 L2 S ≤ f112saK L1 L2 S).trans le_sup_right)
  intro e he
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKNL).mp (hEsup (Eα.inv_mem he))
  have heq : e = b⁻¹ * a⁻¹ := by rw [← mul_inv_rev, ← hab, inv_inv]
  have hq : ⁅c, a⁻¹⁆ ∈ Qα := hcL a⁻¹ (Lα.inv_mem ha)
  have ht : ⁅c, b⁻¹⁆ ∈ T := hcK b⁻¹ ((f112saK L1 L2 S).inv_mem hb)
  have hbQ : b⁻¹ * ⁅c, a⁻¹⁆⁻¹ * b ∈ Qα := by
    have hbN : b⁻¹ ∈ Subgroup.normalizer (Qα : Set H) :=
      hENQ ((f112saK_le_P1' L1 L2 S) ((f112saK L1 L2 S).inv_mem hb))
    simpa using (Subgroup.mem_normalizer_iff.mp hbN _).mp (Qα.inv_mem hq)
  have hkey : e * c * e⁻¹ = (b⁻¹ * ⁅c, a⁻¹⁆⁻¹ * b) * ⁅c, b⁻¹⁆⁻¹ * c := by
    rw [heq]
    simp only [commutatorElement_def]
    group
  rw [hkey]
  exact S.mul_mem (S.mul_mem (hTS (hQαT hbQ)) (S.inv_mem (hTS ht))) hcS

private theorem f112sa_special_center_facts_of_g24 {L1 L2 S : Subgroup H}
    (hD : G24TransferData L1 L2 S) :
    (∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S), ∀ y ∈ pCoreOf 2 (f112saP1' L1 L2 S),
        ⁅x, y⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) ∧
      (∀ x ∈ pCoreOf 2 (f112saP1' L1 L2 S),
        x ^ 2 ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) ∧
      (∀ x ∈ pCoreOf 2 (f112saP2' L1 L2 S),
        x ^ 2 ∈ centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    simpa only [commutatorElement_def] using
      CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_left.1
        (Subgroup.commutator_mem_commutator hx hy)
  · exact fun x hx => CFSG.Quasithin.IsSpecialPGroup.pow_mem_centerOf hD.special_left.1 hx
  · exact fun x hx => CFSG.Quasithin.IsSpecialPGroup.pow_mem_centerOf hD.special_right hx

private theorem f112sa_exists_mul_commutator_mem_centerOf_of_g24
    {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S)
    {c : H} (hcS : c ∈ S)
    (hcQZ : ∀ q ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      ⁅c, q⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)))
    (hcL : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    ∃ y ∈ pCoreOf 2 (f112saP1' L1 L2 S),
      ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S),
        ⁅c * y, l⁆ ∈ centerOf (pCoreOf 2 (f112saP1' L1 L2 S)) := by
  set T := S ⊓ f112saK L1 L2 S with hTdef
  set Eα := f112saP1' L1 L2 S with hEαdef
  set Qα := pCoreOf 2 Eα with hQαdef
  set Lα := oTwoPrime Eα with hLαdef
  set Zα := centerOf Qα with hZαdef
  set Qβ := pCoreOf 2 (f112saP2' L1 L2 S) with hQβdef
  set Zβ := centerOf Qβ with hZβdef
  have hT : Qα ⊔ Qβ = T := f112_pCoreOf_sup_eq hF h1 h2
  have hQαT : Qα ≤ T := le_sup_left.trans hT.le
  have hQβT : Qβ ≤ T := le_sup_right.trans hT.le
  have hTS : T ≤ S := inf_le_left
  have hSN : S ≤ Subgroup.normalizer (Eα : Set H) := fun s hs =>
    f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hSNQ : S ≤ Subgroup.normalizer (Qα : Set H) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSN hs)
  have hSNZ : S ≤ Subgroup.normalizer (Zα : Set H) :=
    hSNQ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qα)
  have hENQ : Eα ≤ Subgroup.normalizer (Qα : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hENZ : Eα ≤ Subgroup.normalizer (Zα : Set H) :=
    hENQ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qα)
  have hQαE : Qα ≤ Eα := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hZαQα : Zα ≤ Qα := inf_le_left
  have hLE : Lα ≤ Eα := oTwoPrime_le _
  have hTL : T ≤ Lα := f112sa_T_le_oTwoPrime_P1' hF
  have hQαcard : Nat.card ↥Qα = 2 ^ 10 := hD.card_pCoreOf_left
  have hZαcard : Nat.card ↥Zα = 2 ^ 2 := hD.card_centerOf_left
  obtain ⟨hQcomm, hQsq, hQβsq⟩ := f112sa_special_center_facts_of_g24 hD
  have hQNZ : Qα ≤ Subgroup.normalizer (Zα : Set H) := hQαE.trans hENZ
  have hrel : relCent Qα Zα T = Zβ := hD.relCent_S
  have hZβQα : Zβ ≤ Qα := by
    rw [← hrel]
    exact relCent_le _ _ _
  have hTsq : ∀ t ∈ T, t ^ 2 ∈ Qα := by
    intro t ht
    rw [← hT] at ht
    have hQβN : Qβ ≤ Subgroup.normalizer (Qα : Set H) := (hQβT.trans hTS).trans hSNQ
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQβN).mp ht
    have hbab : b * a * b⁻¹ ∈ Qα := (Subgroup.mem_normalizer_iff.mp (hQβN hb) a).mp ha
    have e : (a * b) ^ 2 = a * (b * a * b⁻¹) * b ^ 2 := by simp only [pow_two]; group
    rw [e]
    exact Qα.mul_mem (Qα.mul_mem ha hbab) (hZβQα (hQβsq b hb))
  have hTQ : Qα.relIndex T = 4 := by
    have h := Subgroup.relIndex_mul_card (H := Qα) (K := T)
    rw [inf_eq_left.mpr hQαT, hQαcard, hD.card_T] at h
    norm_num at h
    omega
  have hZR : Zα ≤ Zβ := by
    rw [← hrel]
    intro z hz
    refine (mem_relCent hQNZ).mpr ⟨hZαQα hz, fun t ht => ?_⟩
    have h1 : t * z⁻¹ * t⁻¹ ∈ Zα :=
      (Subgroup.mem_normalizer_iff.mp (hSNZ (hTS ht)) z⁻¹).mp (Zα.inv_mem hz)
    have e : ⁅z, t⁆ = z * (t * z⁻¹ * t⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Zα.mul_mem hz h1
  have hR : ∀ q ∈ Qα, (∀ t ∈ T, ⁅q, t⁆ ∈ Zα) → q ∈ Zβ := by
    intro q hq hqt
    rw [← hrel]
    exact (mem_relCent hQNZ).mpr ⟨hq, hqt⟩
  have hfix : Zα.relIndex Zβ ^ 4 ≤ Zα.relIndex Qα := by
    have h1 := Subgroup.relIndex_mul_card (H := Zα) (K := Zβ)
    rw [inf_eq_left.mpr hZR, hZαcard, hD.card_center_right] at h1
    have h2 := Subgroup.relIndex_mul_card (H := Zα) (K := Qα)
    rw [inf_eq_left.mpr hZαQα, hZαcard, hQαcard] at h2
    have e1 : Zα.relIndex Zβ = 4 := by norm_num at h1; omega
    have e2 : Zα.relIndex Qα = 256 := by norm_num at h2; omega
    rw [e1, e2]
    norm_num
  have hTodd : Odd (T.relIndex Lα) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (f112sa_T_sylow_oTwoPrime_P1' hF).2.2)
  exact CFSG.GroupTheory.exists_mul_commutator_mem_of_kleinFour_odd_index_mod
    (Z := Zα) (Q := Qα) (T := T) (L := Lα) (R := Zβ) hZαQα hQαT hTL (hLE.trans hENZ)
    (hLE.trans hENQ) hQsq hQcomm hTsq hTQ hZR hZβQα hR hfix hTodd (hSNZ hcS) hcQZ hcL

private theorem f112sa_mem_T_of_g24_left {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S)
    {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ oTwoPrime (f112saP1' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S)) :
    c ∈ S ⊓ f112saK L1 L2 S := by
  classical
  set T := S ⊓ f112saK L1 L2 S with hTdef
  set Eα := f112saP1' L1 L2 S with hEαdef
  set Qα := pCoreOf 2 Eα with hQαdef
  set Lα := oTwoPrime Eα with hLαdef
  set Zα := centerOf Qα with hZαdef
  set Qβ := pCoreOf 2 (f112saP2' L1 L2 S) with hQβdef
  set Zβ := centerOf Qβ with hZβdef
  have hT : Qα ⊔ Qβ = T := f112_pCoreOf_sup_eq hF h1 h2
  have hQαT : Qα ≤ T := le_sup_left.trans hT.le
  have hQβT : Qβ ≤ T := le_sup_right.trans hT.le
  have hTS : T ≤ S := inf_le_left
  have hS2 : IsPGroup 2 ↥S := hF.1.h1.pgroup
  have hSN : S ≤ Subgroup.normalizer (Eα : Set H) := fun s hs =>
    f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hSNQ : S ≤ Subgroup.normalizer (Qα : Set H) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSN hs)
  have hSNZ : S ≤ Subgroup.normalizer (Zα : Set H) :=
    hSNQ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qα)
  have hENQ : Eα ≤ Subgroup.normalizer (Qα : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hENZ : Eα ≤ Subgroup.normalizer (Zα : Set H) :=
    hENQ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qα)
  have hQαE : Qα ≤ Eα := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hZαQα : Zα ≤ Qα := inf_le_left
  have hLE : Lα ≤ Eα := oTwoPrime_le _
  have hTL : T ≤ Lα := f112sa_T_le_oTwoPrime_P1' hF
  have hQαcard : Nat.card ↥Qα = 2 ^ 10 := hD.card_pCoreOf_left
  have hZαcard : Nat.card ↥Zα = 2 ^ 2 := hD.card_centerOf_left
  have hconj := f112sa_conj_mem_S_of_g24 hF h1 h2 hD hcS hcL
  have hcQZ : ∀ q ∈ Qα, ⁅c, q⁆ ∈ Zα :=
    CFSG.GroupTheory.commutatorElement_mem_of_irreducible_of_conj_mem (E := Eα) (S := S)
      hZαQα (hQαT.trans hTS) hS2 hSNZ hSNQ hENQ hENZ hD.irr_left hconj
  obtain ⟨y, hyQ, hy⟩ :=
    f112sa_exists_mul_commutator_mem_centerOf_of_g24 hF h1 h2 hD hcS hcQZ hcL
  have hind : ⁅pCoreOf 2 Lα, Lα⁆ = pCoreOf 2 Lα := by
    rw [pCoreOf_oTwoPrime]
    exact hD.indec_left
  have hperf : ⁅Lα, Lα⁆ = Lα :=
    perfect_of_VA5 (f112_isL2Quot_oTwoPrime_P1' hF h1 h2)
      (hind.ge.trans (Subgroup.commutator_mono
        (CFSG.LieType.BorelTits.pCoreOf_le 2 Lα) le_rfl))
  have hcy : c * y ∈ Subgroup.centralizer (Lα : Set H) :=
    C35Pf.mem_centralizer_of_comm_mem le_rfl hperf (fun m hm => hD.center_left.le (hy m hm))
  have hyS : y ∈ S := hTS (hQαT hyQ)
  have hcyC : c * y ∈ Subgroup.centralizer (T : Set H) := Subgroup.centralizer_le hTL hcy
  have hcyT : c * y ∈ T :=
    f112sa_S_inf_centralizer_le_T_of_W_eq_bot hF (f112saW_eq_bot_of_g24 hF h2 hD)
      (Subgroup.mem_inf.mpr ⟨S.mul_mem hcS hyS, hcyC⟩)
  have e : c = c * y * y⁻¹ := by group
  rw [e]
  exact T.mul_mem hcyT (T.inv_mem (hQαT hyQ))

private theorem f112sa_relCent_W_data_of_g24
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24TransferData L1 L2 S) {c : H} (hcS : c ∈ S) :
    centerOf (pCoreOf 2 (f112saP2' L1 L2 S)) ≤
        relCent (pCoreOf 2 (f112saP2' L1 L2 S))
          (centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) (oTwoPrime (f112saP2' L1 L2 S)) ∧
      NatSec (oTwoPrime (f112saP2' L1 L2 S))
        (relCent (pCoreOf 2 (f112saP2' L1 L2 S))
          (centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) (oTwoPrime (f112saP2' L1 L2 S)))
        (pCoreOf 2 (f112saP2' L1 L2 S)) ∧
      (relCent (pCoreOf 2 (f112saP2' L1 L2 S))
        (centerOf (pCoreOf 2 (f112saP2' L1 L2 S)))
        (oTwoPrime (f112saP2' L1 L2 S))).relIndex
        (pCoreOf 2 (f112saP2' L1 L2 S)) = 16 ∧
      oTwoPrime (f112saP2' L1 L2 S) ≤ Subgroup.normalizer
        (relCent (pCoreOf 2 (f112saP2' L1 L2 S))
          (centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) (oTwoPrime (f112saP2' L1 L2 S)) : Set H) ∧
      c ∈ Subgroup.normalizer
        (relCent (pCoreOf 2 (f112saP2' L1 L2 S))
          (centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) (oTwoPrime (f112saP2' L1 L2 S)) : Set H) := by
  set Eβ := f112saP2' L1 L2 S with hEβdef
  set Qβ := pCoreOf 2 Eβ with hQβdef
  set Lβ := oTwoPrime Eβ with hLβdef
  set Zβ := centerOf Qβ with hZβdef
  have hSNβ : S ≤ Subgroup.normalizer (Eβ : Set H) := fun s hs =>
    f112sa_P2_le_normalizer_P2' hF ((le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hSNQβ : S ≤ Subgroup.normalizer (Qβ : Set H) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSNβ hs)
  have hSNZβ : S ≤ Subgroup.normalizer (Zβ : Set H) :=
    hSNQβ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qβ)
  have hENQβ : Eβ ≤ Subgroup.normalizer (Qβ : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hENZβ : Eβ ≤ Subgroup.normalizer (Zβ : Set H) :=
    hENQβ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qβ)
  have hLβE : Lβ ≤ Eβ := oTwoPrime_le _
  have hQβNZβ : Qβ ≤ Subgroup.normalizer (Zβ : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hENZβ)
  obtain ⟨k2, hk2X', -, hk23, -⟩ :=
    f112_exists_orderThree_X1 (L1 := L2) (L2 := L1) hF.symm h2
  have hk2X : k2 ∈ f112saX2 L1 L2 S := by
    simpa [f112saX1, f112saX2, bigB_comm] using hk2X'
  have hk2L : k2 ∈ Lβ :=
    f112sa_oTwoRes_le_oTwoPrime_P2' hF h2 (f112sa_X2_le_oTwoRes L1 L2 S hk2X)
  obtain ⟨W0, hZW0, hW0Q, hW0card, hW0comm, hW0nat⟩ := hD.mid_right
  have hWeq : relCent Qβ Zβ Lβ = W0 := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxQ, -, hxL⟩ := hx
      exact hW0nat k2 hk2L hk23 x hxQ (hZW0 (hxL k2 hk2L))
    · refine (mem_relCent hQβNZβ).mpr ⟨hW0Q hx, fun a ha => ?_⟩
      exact hW0comm (Subgroup.commutator_mem_commutator hx ha)
  have hWQ : relCent Qβ Zβ Lβ ≤ Qβ := relCent_le _ _ _
  have hZW : Zβ ≤ relCent Qβ Zβ Lβ := by rw [hWeq]; exact hZW0
  have hWnat : NatSec Lβ (relCent Qβ Zβ Lβ) Qβ := by rw [hWeq]; exact hW0nat
  have hWcard : Nat.card ↥(relCent Qβ Zβ Lβ) = 2 ^ 6 := by rw [hWeq]; exact hW0card
  have hindex : (relCent Qβ Zβ Lβ).relIndex Qβ = 16 := by
    have h := Subgroup.relIndex_mul_card (H := relCent Qβ Zβ Lβ) (K := Qβ)
    rw [inf_eq_left.mpr hWQ, hWcard, hD.card_right] at h
    norm_num at h
    omega
  have hLNW : Lβ ≤ Subgroup.normalizer (relCent Qβ Zβ Lβ : Set H) := fun l hl =>
    mem_normalizer_relCent (hENQβ (hLβE hl)) (hENZβ (hLβE hl)) (Subgroup.le_normalizer hl)
  have hcNW : c ∈ Subgroup.normalizer (relCent Qβ Zβ Lβ : Set H) :=
    mem_normalizer_relCent (hSNQβ hcS) (hSNZβ hcS) (mem_normalizer_oTwoPrime (hSNβ hcS))
  exact ⟨hZW, hWnat, hindex, hLNW, hcNW⟩

private theorem f112sa_relCent_le_pCoreOf_right_of_g24
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h2 : VA5 L2)
    (hD : G24TransferData L1 L2 S) :
    relCent (pCoreOf 2 (f112saP2' L1 L2 S))
      (centerOf (pCoreOf 2 (f112saP2' L1 L2 S)))
      (oTwoPrime (f112saP2' L1 L2 S)) ≤ pCoreOf 2 (f112saP1' L1 L2 S) := by
  set Eβ := f112saP2' L1 L2 S with hEβdef
  set Qβ := pCoreOf 2 Eβ with hQβdef
  set Lβ := oTwoPrime Eβ with hLβdef
  set Zβ := centerOf Qβ with hZβdef
  have hENQβ : Eβ ≤ Subgroup.normalizer (Qβ : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hENZβ : Eβ ≤ Subgroup.normalizer (Zβ : Set H) :=
    hENQβ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qβ)
  have hLβE : Lβ ≤ Eβ := oTwoPrime_le _
  have hQβNZβ : Qβ ≤ Subgroup.normalizer (Zβ : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hENZβ)
  obtain ⟨k2, hk2X', -, hk23, -⟩ :=
    f112_exists_orderThree_X1 (L1 := L2) (L2 := L1) hF.symm h2
  have hk2X : k2 ∈ f112saX2 L1 L2 S := by
    simpa [f112saX1, f112saX2, bigB_comm] using hk2X'
  have hk2L : k2 ∈ Lβ :=
    f112sa_oTwoRes_le_oTwoPrime_P2' hF h2 (f112sa_X2_le_oTwoRes L1 L2 S hk2X)
  obtain ⟨W0, hZW0, hW0Q, hW0card, hW0comm, hW0nat⟩ := hD.mid_right
  have hWeq : relCent Qβ Zβ Lβ = W0 := by
    refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨hxQ, -, hxL⟩ := hx
      exact hW0nat k2 hk2L hk23 x hxQ (hZW0 (hxL k2 hk2L))
    · refine (mem_relCent hQβNZβ).mpr ⟨hW0Q hx, fun a ha => ?_⟩
      exact hW0comm (Subgroup.commutator_mem_commutator hx ha)
  have hWQ : relCent Qβ Zβ Lβ ≤ Qβ := relCent_le _ _ _
  have hZW : Zβ ≤ relCent Qβ Zβ Lβ := by rw [hWeq]; exact hZW0
  have hrel : relCent (pCoreOf 2 (f112saP1' L1 L2 S))
      (centerOf (pCoreOf 2 (f112saP1' L1 L2 S))) (S ⊓ f112saK L1 L2 S) = Zβ := hD.relCent_S
  have hZβQα : Zβ ≤ pCoreOf 2 (f112saP1' L1 L2 S) := by
    rw [← hrel]
    exact relCent_le _ _ _
  have hk2NW : k2 ∈ Subgroup.normalizer (relCent Qβ Zβ Lβ : Set H) :=
    mem_normalizer_relCent (hENQβ (hLβE hk2L)) (hENZβ (hLβE hk2L))
      (Subgroup.le_normalizer hk2L)
  intro x hx
  obtain ⟨z, hz, a, ha, rfl⟩ := CFSG.Quasithin.St84.exists_mul_mem_centralizer_of_acts_trivially
    (Q := relCent Qβ Zβ Lβ) (Z := Zβ) hZW
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Eβ).to_le hWQ) hk23
    hk2NW (hENZβ (hLβE hk2L))
    (fun q hq z hz => (Subgroup.mem_normalizer_iff.mp (hQβNZβ (hWQ hq)) z).mp hz)
    (fun y hy => by
      have h := Zβ.inv_mem (hy.2.2 k2 hk2L)
      rwa [commutatorElement_inv, commutatorElement_def] at h) x hx
  exact (pCoreOf 2 (f112saP1' L1 L2 S)).mul_mem (hZβQα hz)
    (hD.cent_right k2 hk2L hk23 (Subgroup.mem_inf.mpr ⟨hWQ (Subgroup.mem_inf.mp ha).1,
      (Subgroup.mem_inf.mp ha).2⟩))

private theorem f112sa_commutator_mem_pCoreOf_right_of_g24
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : G24TransferData L1 L2 S) {c : H} (hcS : c ∈ S)
    (hcQW : ∀ q ∈ pCoreOf 2 (f112saP2' L1 L2 S),
      ⁅c, q⁆ ∈ relCent (pCoreOf 2 (f112saP2' L1 L2 S))
        (centerOf (pCoreOf 2 (f112saP2' L1 L2 S))) (oTwoPrime (f112saP2' L1 L2 S)))
    (hWQα : relCent (pCoreOf 2 (f112saP2' L1 L2 S))
      (centerOf (pCoreOf 2 (f112saP2' L1 L2 S)))
      (oTwoPrime (f112saP2' L1 L2 S)) ≤ pCoreOf 2 (f112saP1' L1 L2 S)) :
    ∀ t ∈ S ⊓ f112saK L1 L2 S, ⁅c, t⁆ ∈ pCoreOf 2 (f112saP1' L1 L2 S) := by
  set T := S ⊓ f112saK L1 L2 S with hTdef
  set Eα := f112saP1' L1 L2 S with hEαdef
  set Qα := pCoreOf 2 Eα with hQαdef
  set Qβ := pCoreOf 2 (f112saP2' L1 L2 S) with hQβdef
  have hT : Qα ⊔ Qβ = T := f112_pCoreOf_sup_eq hF h1 h2
  have hQβT : Qβ ≤ T := le_sup_right.trans hT.le
  have hTS : T ≤ S := inf_le_left
  have hSNα : S ≤ Subgroup.normalizer (Eα : Set H) := fun s hs =>
    f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hSNQα : S ≤ Subgroup.normalizer (Qα : Set H) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSNα hs)
  have hQβNα : Qβ ≤ Subgroup.normalizer (Qα : Set H) := (hQβT.trans hTS).trans hSNQα
  intro t ht
  rw [← hT] at ht
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQβNα).mp ht
  have hca : ⁅c, a⁆ ∈ Qα := by
    rw [commutatorElement_def]
    exact Qα.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSNQα hcS) a).mp ha) (Qα.inv_mem ha)
  have hcb : a * ⁅c, b⁆ * a⁻¹ ∈ Qα :=
    Qα.mul_mem (Qα.mul_mem ha (hWQα (hcQW b hb))) (Qα.inv_mem ha)
  rw [commutatorElement_mul_right_eq_mul_conj]
  have e : ⁅c, a⁆ * a * ⁅c, b⁆ * a⁻¹ = ⁅c, a⁆ * (a * ⁅c, b⁆ * a⁻¹) := by group
  rw [e]
  exact Qα.mul_mem hca hcb

private theorem f112sa_mem_T_of_g24_right {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S)
    {c : H} (hcS : c ∈ S)
    (hcL : ∀ l ∈ oTwoPrime (f112saP2' L1 L2 S), ⁅c, l⁆ ∈ pCoreOf 2 (f112saP2' L1 L2 S)) :
    c ∈ S ⊓ f112saK L1 L2 S := by
  classical
  set T := S ⊓ f112saK L1 L2 S with hTdef
  set Eα := f112saP1' L1 L2 S with hEαdef
  set Eβ := f112saP2' L1 L2 S with hEβdef
  set Qα := pCoreOf 2 Eα with hQαdef
  set Lα := oTwoPrime Eα with hLαdef
  set Qβ := pCoreOf 2 Eβ with hQβdef
  set Lβ := oTwoPrime Eβ with hLβdef
  set Zβ := centerOf Qβ with hZβdef
  have hT : Qα ⊔ Qβ = T := f112_pCoreOf_sup_eq hF h1 h2
  have hQαT : Qα ≤ T := le_sup_left.trans hT.le
  have hQβT : Qβ ≤ T := le_sup_right.trans hT.le
  have hTS : T ≤ S := inf_le_left
  have hcB : c ∈ bigB L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S) hcS
  have hSNα : S ≤ Subgroup.normalizer (Eα : Set H) := fun s hs =>
    f112sa_P1_le_normalizer_P1' hF ((le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hSNβ : S ≤ Subgroup.normalizer (Eβ : Set H) := fun s hs =>
    f112sa_P2_le_normalizer_P2' hF ((le_sup_right : bigB L1 L2 S ≤ f112P2 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) hs))
  have hSNQα : S ≤ Subgroup.normalizer (Qα : Set H) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSNα hs)
  have hSNQβ : S ≤ Subgroup.normalizer (Qβ : Set H) := fun s hs =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hSNβ hs)
  have hSNZβ : S ≤ Subgroup.normalizer (Zβ : Set H) :=
    hSNQβ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qβ)
  have hENQβ : Eβ ≤ Subgroup.normalizer (Qβ : Set H) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hENZβ : Eβ ≤ Subgroup.normalizer (Zβ : Set H) :=
    hENQβ.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf Qβ)
  have hLβE : Lβ ≤ Eβ := oTwoPrime_le _
  have hQβL : Qβ ≤ Lβ := le_oTwoPrime_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
  have hQβNZβ : Qβ ≤ Subgroup.normalizer (Zβ : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hENZβ)
  have hQβcomm : ∀ x ∈ Qβ, ∀ y ∈ Qβ, ⁅x, y⁆ ∈ Zβ := by
    intro x hx y hy
    simpa only [commutatorElement_def] using
      CFSG.Quasithin.IsSpecialPGroup.commutator_le_centerOf hD.special_right
        (Subgroup.commutator_mem_commutator hx hy)
  have hrel : relCent Qα (centerOf Qα) T = Zβ := hD.relCent_S
  have hZβQα : Zβ ≤ Qα := by
    rw [← hrel]
    exact relCent_le _ _ _
  obtain ⟨hZW, hWnat, hindex, hLNW, hcNW⟩ :=
    f112sa_relCent_W_data_of_g24 hF h2 hD hcS
  have hWQ : relCent Qβ Zβ Lβ ≤ Qβ := relCent_le _ _ _
  have hc2 : ∃ m, c ^ 2 ^ m = 1 := by
    obtain ⟨m, hm⟩ := hF.1.h1.pgroup ⟨c, hcS⟩
    exact ⟨m, by simpa using congrArg (fun x : ↥S => (x : H)) hm⟩
  obtain ⟨e2a⟩ := f112_isL2Quot_oTwoPrime_P2' hF h1 h2
  obtain ⟨e2b⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  have hcQW : ∀ q ∈ Qβ, ⁅c, q⁆ ∈ relCent Qβ Zβ Lβ :=
    CFSG.GroupTheory.AlternatingFive.commutatorElement_mem_of_fixFree_of_twoPow (e2a.trans e2b)
      hQβL (hLβE.trans hENQβ) hWQ hLNW
      (fun x hx y hy => hZW (hQβcomm x hx y hy)) hindex hWnat hc2 (hSNQβ hcS) hcNW hcL
  have hWQα := f112sa_relCent_le_pCoreOf_right_of_g24 hF h2 hD
  have hcT := f112sa_commutator_mem_pCoreOf_right_of_g24 hF h1 h2 hD hcS hcQW hWQα
  obtain ⟨e1a⟩ := f112_isL2Quot_oTwoPrime_P1' hF h1 h2
  obtain ⟨e1b⟩ := CFSG.Quasithin.F112J2.nonempty_psl_four_equiv_alt5
  obtain ⟨q, hqT, hq⟩ :=
    CFSG.GroupTheory.AlternatingFive.exists_conjModPCore_eq_one_of_fixes_sylow
      (e1a.trans e1b) (mem_normalizer_oTwoPrime (hSNα hcS)) (f112sa_T_sylow_oTwoPrime_P1' hF)
      (by rw [pCoreOf_oTwoPrime]; exact hcT)
  rw [pCoreOf_oTwoPrime] at hq
  have hcq : c * q⁻¹ ∈ T :=
    f112sa_mem_T_of_g24_left hF h1 h2 hD (S.mul_mem hcS (S.inv_mem (hTS hqT))) hq
  have e : c = c * q⁻¹ * q := by group
  rw [e]
  exact T.mul_mem hcq hqT

theorem f112sa_le_K_of_g24 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24TransferData L1 L2 S) :
    S ≤ f112saK L1 L2 S :=
  f112sa_le_K_of_core_steps hF h1 h2
    (f112_isL2Quot_oTwoPrime_P1' hF h1 h2) (f112_isL2Quot_oTwoPrime_P2' hF h1 h2)
    (fun c hcS hcQ => (Subgroup.mem_inf.mp (f112sa_mem_T_of_g24_left hF h1 h2 hD hcS hcQ)).2)
    (fun c hcS hcQ => (Subgroup.mem_inf.mp (f112sa_mem_T_of_g24_right hF h1 h2 hD hcS hcQ)).2)

theorem f112_g24LocalData_of_g24TransferData
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : G24TransferData L1 L2 S) :
    G24LocalData L1 L2 S := by
  have hS := f112sa_le_K_of_g24 hF h1 h2 hD
  obtain ⟨hSL1, hL1, -⟩ := f112sa_S_le_L1_and_eq_oTwoPrime_of_S_le_K hF h1 hS
    (f112_isL2Quot_oTwoPrime_P1' hF h1 h2) hD.indec_left
  obtain ⟨hSL2, hL2, -⟩ := f112sa_S_le_L2_and_eq_oTwoPrime_of_S_le_K hF h2 hS
    (f112_isL2Quot_oTwoPrime_P2' hF h1 h2) hD.comm_right
  have hB : bigB L1 L2 S = f112saK L1 L2 S := by
    rw [f112sa_bigB_eq_S_sup_K hF]
    exact sup_eq_right.mpr hS
  have hP1 : L1 ⊔ bigB L1 L2 S = f112saP1' L1 L2 S := f112saP1_eq_of_S_le_K hF hS
  have hQ1 : dsQ L1 L2 S = pCoreOf 2 (f112saP1' L1 L2 S) := by
    show pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = _
    rw [hP1]
  have hQ2 : dsQ L2 L1 S = pCoreOf 2 (f112saP2' L1 L2 S) := by
    show pCoreOf 2 (L2 ⊔ bigB L2 L1 S) = _
    rw [bigB_comm]
    exact congrArg (pCoreOf 2) (f112saP2_eq_of_S_le_K hF hS)
  refine ⟨hSL1, hSL2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]; exact hD.card_K
  · rw [hQ1]; exact hD.special_left
  · have h := hD.center_left
    rw [← hL1, ← hQ1] at h
    exact h
  · intro Y hY1 hY2 hY3
    rw [hQ1] at hY1 hY2 ⊢
    rw [hP1] at hY3
    exact hD.irr_left Y hY1 hY2 hY3
  · have h := hD.orth_left
    rw [← hL1, ← hQ1] at h
    exact h
  · rw [hQ2]; exact hD.card_right
  · rw [hQ2]; exact hD.special_right
  · rw [hQ2]; exact hD.card_center_right
  · have h := hD.natZ_right
    rw [← hL2, ← hQ2] at h
    exact h
  · have h := hD.mid_right
    rw [← hL2, ← hQ2] at h
    exact h
  · have h := hD.comm_right
    rw [← hL2, ← hQ2] at h
    exact h
  · rw [hQ1, hQ2]; exact hD.card_inf

end CFSG.Quasithin.F112R.St84
