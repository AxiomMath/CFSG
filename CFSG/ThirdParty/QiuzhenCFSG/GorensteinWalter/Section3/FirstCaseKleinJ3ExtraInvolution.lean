module


public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSemidirectInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCardThreeTransferNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinJ3NormalizerEven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNoCentralizingInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseOrderInfra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePInfPg
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! If the centralizer of the `J₃` subgroup were even, the transferred
normalizer would contain an extra involution commuting with the `J₃`
involution. -/

public theorem firstCase_klein_J3_extra_commuting_involution_of_centralizer_even
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hyJ : y ∈ firstCaseJ c 3)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXcard : Nat.card X = 3)
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hXinf : X ⊓ (twoCoreOf c.Hhat ⊔ c.U) = ⊥)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G)))) :
    ∃ e : G, e ∈ c.Hhat ∧ IsInvolution e ∧ Commute e y := by
  classical
  have hy : IsInvolution y := by simpa [firstCaseJ] using hyJ |>.1
  have hyH : y ∉ c.Hhat := by simpa [firstCaseJ] using hyJ |>.2.1
  have hXodd : Nat.Coprime 2 (Nat.card X) := by rw [hXcard]; norm_num
  have hUcard : Nat.card c.U = 3 :=
    firstCase_klein_U_card_three_pre_b3 hmin c hfirst hklein
  have hN_even : Even (Nat.card
      (Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)) :=
    firstCase_klein_J3_normalizer_even hmin c hfirst hklein hyJ
      hXne hXle hXcard hXinv hXinf
  obtain ⟨g, hgnot, hXgU, hnormEq⟩ :=
    firstCase_klein_card_three_transfer_normalizer hmin c hfirst hklein
      hyJ hXne hXle hXcard hXinv hC_even hUcard
  let A : Subgroup G := Subgroup.normalizer (X : Set G)
  let E : Subgroup G := A ⊓ c.Hhat
  let Vg : Subgroup G := conjugateSubgroup (twoCoreOf c.Hhat) g⁻¹
  have hEleA : E ≤ A := inf_le_left
  have hEeven : Even (Nat.card E) := by
    simpa [E, A] using hN_even
  have hXcentU : X ≤ Subgroup.centralizer (c.U : Set G) :=
    firstCase_klein_card_three_subgroup_centralizes_U hmin c hXcard hXle hUcard
  have hUcentX : c.U ≤ Subgroup.centralizer (X : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hXcentU hx) u hu).symm
  have hUleH : c.U ≤ c.Hhat := by
    rw [(theorem_2_6 hmin c).1]
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat)
  have hUleE : c.U ≤ E := by
    exact fun u hu => ⟨Subgroup.centralizer_le_normalizer (X : Set G)
      (hUcentX hu), hUleH hu⟩
  have hXleE : X ≤ E := fun x hx => ⟨Subgroup.le_normalizer hx, hXle hx⟩
  have hUXdisj : Disjoint c.U X := by
    apply (disjoint_iff_inf_le).2
    intro z hz
    have hbot : z ∈ X ⊓ (twoCoreOf c.Hhat ⊔ c.U) :=
      ⟨hz.2, (le_sup_right : c.U ≤ twoCoreOf c.Hhat ⊔ c.U) hz.1⟩
    rw [hXinf] at hbot
    exact hbot
  have hUnormX : c.U ≤ Subgroup.normalizer (X : Set G) :=
    hUcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hUXcard : Nat.card (c.U ⊔ X : Subgroup G) = 9 := by
    rw [sup_comm]
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) X c.U
      hUnormX hUXdisj.symm, hXcard, hUcard]
  have hUXleE : c.U ⊔ X ≤ E := sup_le hUleE hXleE
  have h9dvdE : 9 ∣ Nat.card E := by
    simpa [hUXcard] using Subgroup.card_dvd_of_le hUXleE
  have h18dvdE : 18 ∣ Nat.card E := by
    have h2dvdE : 2 ∣ Nat.card E := hEeven.two_dvd
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by norm_num : Nat.Coprime 2 9) h2dvdE h9dvdE
    norm_num at this ⊢
    exact this
  have hEcardLower : 18 ≤ Nat.card E := Nat.le_of_dvd Nat.card_pos h18dvdE
  have hmapU : conjugateSubgroup c.U g⁻¹ = X := by
    have hm := congrArg (fun K : Subgroup G => conjugateSubgroup K g⁻¹) hXgU
    have hcancel : conjugateSubgroup (conjugateSubgroup X g) g⁻¹ = X := by
      simpa using (conj_inv_then_conj_eq X g⁻¹)
    rw [hcancel] at hm
    exact hm.symm
  have hVgcentX : Vg ≤ Subgroup.centralizer (X : Set G) := by
    have hVcentU : twoCoreOf c.Hhat ≤ Subgroup.centralizer (c.U : Set G) := by
      simpa [(theorem_2_6 hmin c).1] using
        twoCoreOf_centralizes_oddCoreOf c.Hhat
    change (twoCoreOf c.Hhat).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer (X : Set G)
    rw [← hmapU]
    exact centralizer_map_le_of_conj c.U (twoCoreOf c.Hhat) g hVcentU
  have hVgKlein : IsKleinFour Vg := by
    change IsKleinFour
      ((twoCoreOf c.Hhat).map (MulAut.conj g⁻¹).toMonoidHom)
    exact isKleinFour_map_mulEquiv (twoCoreOf c.Hhat)
      (firstCase_klein_V_klein c hklein) (MulAut.conj g⁻¹)
  have hVgcard : Nat.card Vg = 4 := hVgKlein.card_four
  have hVgleA : Vg ≤ A := by
    change Vg ≤ Subgroup.normalizer (X : Set G)
    rw [hnormEq]
    exact Subgroup.map_mono (Subgroup.map_subtype_le (pCore 2 c.Hhat))
  have hVnormH : IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
    refine ⟨Subgroup.map_subtype_le (pCore 2 c.Hhat), ?_⟩
    intro h hh v hv
    rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
    exact Subgroup.mem_map.mpr ⟨
      (⟨h, hh⟩ : c.Hhat) * v0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
      (pCore_normal (p := 2) (G := c.Hhat)).conj_mem v0 hv0
        (⟨h, hh⟩ : c.Hhat), by simp⟩
  have hVgnormA : IsNormalIn Vg A := by
    refine ⟨hVgleA, ?_⟩
    intro a ha v hv
    change a ∈ Subgroup.normalizer (X : Set G) at ha
    rw [hnormEq] at ha
    rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, rfl⟩
    rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
    refine Subgroup.mem_map.mpr ⟨a0 * v0 * a0⁻¹,
      hVnormH.2 a0 ha0 v0 hv0, ?_⟩
    · simpa [MulAut.conj_apply] using
        (show g⁻¹ * (a0 * v0 * a0⁻¹) * g =
          (g⁻¹ * a0 * g) * (g⁻¹ * v0 * g) *
            (g⁻¹ * a0 * g)⁻¹ by group)
  have hVgEdisj : Disjoint Vg E := by
    apply (disjoint_iff_inf_le).2
    intro z hz
    by_cases hz1 : z = 1
    · exact Subgroup.mem_bot.mpr hz1
    have hzI : IsInvolution z := by
      refine ⟨hz1, ?_⟩
      simpa [pow_two] using congrArg Subtype.val
        (hVgKlein.mul_self ⟨z, hz.1⟩)
    have hzH : z ∈ c.Hhat := (inf_le_right : E ≤ c.Hhat) hz.2
    have hzcent : ∀ q : G, q ∈ X → z * q * z⁻¹ = q := by
      intro q hq
      have hc := (Subgroup.mem_centralizer_iff.mp (hVgcentX hz.1)) q hq
      calc
        z * q * z⁻¹ = q * z * z⁻¹ := by rw [hc]
        _ = q := by simp
    exact False.elim (firstCase_klein_no_centralizing_involution_of_inverted_card_three
      hmin c hfirst hklein hy hyH hXne hXle hXodd hXinv hXcard hzH hzI hzcent)
  have hE_le_normVg : E ≤ Subgroup.normalizer (Vg : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he v hv
    exact hVgnormA.2 e (hEleA he) v hv
  have hsupcard : Nat.card (Vg ⊔ E : Subgroup G) = 4 * Nat.card E := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) Vg E
      hE_le_normVg hVgEdisj, hVgcard]
  have hHcard : Nat.card c.H = 24 := by
    rw [firstCase_H_card_eq_eight_mul_U hmin c hfirst hklein, hUcard]
  have hHhatcard : Nat.card c.Hhat = 72 := by
    rw [firstCase_Hhat_card_eq_three_mul_H hmin c hfirst hklein, hHcard]
  have hAcard : Nat.card A = 72 := by
    change Nat.card (Subgroup.normalizer (X : Set G)) = 72
    rw [hnormEq]
    calc
      Nat.card (conjugateSubgroup c.Hhat g⁻¹) = Nat.card c.Hhat := by
        exact Nat.card_congr
          (Subgroup.equivMapOfInjective c.Hhat (MulAut.conj g⁻¹).toMonoidHom
            (MulAut.conj g⁻¹).injective).toEquiv.symm
      _ = 72 := hHhatcard
  have hsupLeA : Vg ⊔ E ≤ A := sup_le hVgleA hEleA
  have hEcardUpper : Nat.card E ≤ 18 := by
    have hdvd : 4 * Nat.card E ∣ 72 := by
      have := Subgroup.card_dvd_of_le hsupLeA
      simpa [hsupcard, hAcard] using this
    have hle : 4 * Nat.card E ≤ 72 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hEcard : Nat.card E = 18 := by omega
  have hsupEq : Vg ⊔ E = A := by
    apply Subgroup.eq_of_le_of_card_ge hsupLeA
    rw [hsupcard, hEcard, hAcard]
  have hyA : y ∈ A := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [(hXinv z hz).2]
      exact X.inv_mem hz
    · intro hz
      have hz' := hXinv (y * z * y⁻¹) hz
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      have hback : y * (y * z * y⁻¹) * y⁻¹ = z := by
        rw [hyinv]
        calc
          y * (y * z * y) * y = (y * y) * z * (y * y) := by group
          _ = z := by rw [hy2]; simp
      rw [← hback, hz'.2]
      exact X.inv_mem hz
  have hyVg : y ∉ Vg := by
    intro hyVg
    have hcent : X ≤ Subgroup.centralizer ({y} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hVgcentX hyVg) x hx
    have hbot := oddOrder_subgroup_eq_bot_of_inverted_and_centralized
      X y (Nat.coprime_two_left.mp hXodd) hcent
      (fun x hx => (hXinv x hx).2)
    exact hXne hbot
  obtain ⟨e, heE, heI, hey⟩ :=
    exists_complement_involution_commuting_of_kleinFour_sup
      A Vg E hVgnormA hEleA hVgKlein hVgEdisj hsupEq hyA hy hyVg
  exact ⟨e, (inf_le_right : E ≤ c.Hhat) heE, heI, hey⟩

end CFSG.GorensteinWalter
