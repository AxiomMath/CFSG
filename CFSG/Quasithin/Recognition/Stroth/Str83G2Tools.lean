module

public import CFSG.Quasithin.Recognition.Stroth.Str86Frame
public import CFSG.Quasithin.Recognition.Stroth.Str83OrdersParts
public import CFSG.GH74.Uniqueness.Bender.OddComplement
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_inverting_involution_of_cartan_linear
    {K : Type} [Group K] [Finite K] {n : ℕ} (hB : BenderType K n 1 1) (Q : Sylow 2 K)
    {D : Subgroup K} (hD : D ≤ borel (Q : Subgroup K)) (hDodd : Odd (Nat.card D))
    (hQD : (Q : Subgroup K) ⊔ D = borel (Q : Subgroup K)) :
    ∃ t : K, t * t = 1 ∧ t ∉ borel (Q : Subgroup K) ∧
      (∀ d ∈ D, t * d * t⁻¹ = d⁻¹) ∧
      (Q : Subgroup K) ⊔ conjugate (Q : Subgroup K) t = ⊤ := by
  obtain ⟨t, ht2, htB, hcart⟩ := exists_involution_cartan_eq hB Q hD hDodd hQD
  obtain ⟨_, hc⟩ := hB.exists_benderCore Q
  have hc' : BenderCore (2 ^ n) 1 1 (Q : Subgroup K) t := hc.of_involution ht2 htB
  haveI : IsSimpleGroup K := hB.isSimple
  refine ⟨t, ht2, htB, ?_, hc'.sup_conjugate_eq_top⟩
  intro d hd
  have hd' : d ∈ cartan (Q : Subgroup K) t := by rw [hcart]; exact hd
  have hdcomm : d ∈ ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ := by
    rw [← hc'.cartan_eq_commutator rfl]
    exact hd'
  have h := (hc'.mem_commutator_cartan_iff.mp hdcomm).2
  rwa [inv_eq_of_mul_eq_one_right ht2]

theorem exists_mem_normalizer_of_mem_normalizer_sup
    {G : Type} [Group G] [Finite G] {Q D H : Subgroup G} [Q.Normal]
    (hH : H = Q ⊔ D) (hQ : IsPGroup 2 Q)
    (hDodd : Odd (Nat.card D)) (hinf : Q ⊓ D = ⊥)
    {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    ∃ n ∈ Subgroup.normalizer (D : Set G), n⁻¹ * g ∈ Q := by
  classical
  have hQHle : Q ≤ H := by rw [hH]; exact le_sup_left
  have hDHle : D ≤ H := by rw [hH]; exact le_sup_right
  let QH : Subgroup ↥H := Q.subgroupOf H
  let DH : Subgroup ↥H := D.subgroupOf H
  haveI : QH.Normal := Subgroup.Normal.subgroupOf (inferInstance : Q.Normal) H
  have hQHp : IsPGroup 2 QH :=
    hQ.of_injective (Subgroup.subgroupOfEquivOfLe hQHle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQHle).injective
  have hQH_DH : QH ⊔ DH = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQHle hDHle, hH, Subgroup.subgroupOf_self]
  have hQH_inf : QH ⊓ DH = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ Q ⊓ D := ⟨hx.1, hx.2⟩
    rw [hinf, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  set A : Subgroup G := conjugate D g with hA
  have hA_le_H : A ≤ H := by
    intro x hx
    rw [hA, mem_conjugate_iff] at hx
    exact (Subgroup.mem_normalizer_iff.mp hg x).mpr (hDHle hx)
  let AH : Subgroup ↥H := A.subgroupOf H
  have hAHodd : Odd (Nat.card AH) := by
    have hcard : Nat.card AH = Nat.card D := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_H).toEquiv]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective
    rw [hcard]
    exact hDodd
  obtain ⟨qH, hqQH, hq⟩ := exists_conj_mem_of_odd_card (G := ↥H)
    (N := QH) (D := DH) (D₃ := DH) (A := AH) hQHp hQH_inf hQH_DH le_rfl
    (fun d hd _ => hd) hAHodd
  let q : G := (qH : ↥H)
  have hqQ : q ∈ Q := hqQH
  have hqA : conjugate A q⁻¹ ≤ D := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have hxH : q⁻¹ * x * q ∈ H := hA_le_H hx
    have hxAH : (⟨q⁻¹ * x * q, hxH⟩ : ↥H) ∈ AH := hx
    have hthis : ((qH * ⟨q⁻¹ * x * q, hxH⟩ * qH⁻¹ : ↥H) : G) ∈ D := hq _ hxAH
    simpa [q, mul_assoc] using hthis
  have hqAeq : conjugate A q⁻¹ = D := by
    refine Subgroup.eq_of_le_of_card_ge hqA ?_
    have hcard1 : Nat.card ↥(conjugate A q⁻¹) = Nat.card A :=
      Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj (q⁻¹)⁻¹) A).symm.toEquiv
    have hcard2 : Nat.card A = Nat.card D := by
      rw [hA]
      exact Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g⁻¹) D).symm.toEquiv
    rw [hcard1, hcard2]
  have hconj : conjugate A q⁻¹ = D := hqAeq
  have hnconj : conjugate D (g * q⁻¹) = D := by
    rw [← conjugate_conjugate, ← hA, hconj]
  let n : G := g * q⁻¹
  have hnN : n ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hx' : x ∈ conjugate D n := by rw [hnconj]; exact hx
      exact (mem_conjugate_iff D n x).mp hx'
    · intro hx
      have hx' : x ∈ conjugate D n := (mem_conjugate_iff D n x).mpr hx
      rwa [hnconj] at hx'
  refine ⟨n, hnN, ?_⟩
  have hnq : n⁻¹ * g = q := by
    rw [show n = g * q⁻¹ from rfl, mul_inv_rev, inv_inv]
    group
  rw [hnq]
  exact hqQ

theorem q1_sup_q2_eq_s_of_caseII
    {L1 L2 S : Subgroup G} {a : ℕ} (hF : F112HypW L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hJ1 : thompsonJ S ≤ Q1 L1 L2 S) (hJ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S) :
    Q1 L1 L2 S ⊔ Q2 L1 L2 S = S := by
  have hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) :=
    str83_bigB_le_normalizer hF.1 ha hSz hL2
  have h := str86_pCoreOf_sup_pCoreOf (n := 2 * a + 1) hF hSB
    (Or.inl ⟨a, ha, hSz⟩) (by omega) hL2
  simpa [Q1, Q2, P1, P2] using h

end CFSG.Quasithin.Stroth

end
