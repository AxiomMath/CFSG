module

import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofCent
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.Assembly.ComponentTypeDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148V

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField)
open scoped commutatorElement

theorem exists_twist_of_fpf {X : Type} [Group X] [Finite X] {J K E A : Subgroup X} {σ z : X}
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set X)) (hz : z ∈ E)
    (hEC : E ≤ Subgroup.centralizer ({σ} : Set X)) (hEc : IsMulCommutative ↥E) (hAJ : A ≤ J)
    (hA3 : ¬ 3 ∣ Nat.card A) (hAN : Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (A : Set X))
    (hfpf : ∀ a ∈ A, a * z = z * a → a = 1)
    (hne : ∃ u ∈ A, u ≠ 1 ∧ u * (σ * z) = (σ * z) * u) :
    ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
      Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
      ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K := by
  have hzσ : z * σ = σ * z := Subgroup.mem_centralizer_singleton_iff.mp (hEC hz)
  have hσz : σ ∈ Subgroup.centralizer ({σ * z} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc, hzσ]
  have hEz : E ≤ Subgroup.centralizer ({σ * z} : Set X) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : e * σ = σ * e := Subgroup.mem_centralizer_singleton_iff.mp (hEC he)
    have h2 : e * z = z * e := congrArg Subtype.val (hEc.is_comm.comm ⟨e, he⟩ ⟨z, hz⟩)
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  have hHC : Subgroup.zpowers σ ⊔ E ≤ Subgroup.centralizer ({σ * z} : Set X) :=
    sup_le (Subgroup.zpowers_le.mpr hσz) hEz
  set V : Subgroup X := A ⊓ Subgroup.centralizer ({σ * z} : Set X) with hV
  refine ⟨V, inf_le_inf_right _ hAJ, fun h3 => hA3 (h3.trans (Subgroup.card_dvd_of_le
    inf_le_left)), fun g hg => ?_, fun hle => ?_⟩
  · apply Subgroup.mem_normalizer_fintype
    intro v hv
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hv ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hAN hg) v).mp hv.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHC hg) hv.2) (Subgroup.inv_mem _ (hHC hg))
  · obtain ⟨u, huA, hu1, huC⟩ := hne
    have huV : u ∈ V := ⟨huA, Subgroup.mem_centralizer_singleton_iff.mpr huC⟩
    have hw : ⁅u, z⁆ ∈ K := hle (Subgroup.commutator_mem_commutator huV (Subgroup.mem_sup_right hz))
    have hwσ : ⁅u, z⁆ * σ = σ * ⁅u, z⁆ := Subgroup.mem_centralizer_singleton_iff.mp (hKC hw)
    have hzC : z ∈ Subgroup.centralizer ({σ * z} : Set X) := hEz hz
    have hwσz : ⁅u, z⁆ * (σ * z) = (σ * z) * ⁅u, z⁆ := by
      rw [← Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huV.2 hzC)
        (Subgroup.inv_mem _ huV.2)) (Subgroup.inv_mem _ hzC)
    have hwz : ⁅u, z⁆ * z = z * ⁅u, z⁆ := by
      have e1 : ⁅u, z⁆ * σ⁻¹ = σ⁻¹ * ⁅u, z⁆ := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, hwσ, inv_mul_cancel_left]
      calc ⁅u, z⁆ * z = ⁅u, z⁆ * σ⁻¹ * (σ * z) := by group
        _ = σ⁻¹ * (⁅u, z⁆ * (σ * z)) := by rw [e1]; group
        _ = z * ⁅u, z⁆ := by rw [hwσz]; group
    have hwA : ⁅u, z⁆ ∈ A := by
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      refine A.mul_mem huA ?_
      have := (Subgroup.mem_normalizer_iff.mp (hAN (Subgroup.mem_sup_right hz)) u⁻¹).mp
        (A.inv_mem huA)
      rwa [← mul_assoc]
    have h1 := hfpf _ hwA hwz
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact hu1 (hfpf u huA h1)

section Certificates


theorem exists_fieldAut_model_unitary {Γ : Type} [Group Γ] [Finite Γ]
    {X K : Subgroup Γ} {σ : Γ} {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥X 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 2) (hind : KFacts.InducesStdKind X σ .field) (hσ3 : σ ^ 3 = 1)
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set Γ)) (hK : Sec4.IsoLThreePi ↥K 2 n) :
    ∃ (hU : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))))
      (χ : ↥X ≃* unitaryPSU hU 3) (τ : GaloisField 2 (2 * (3 * n)) ≃+* GaloisField 2 (2 * (3 * n))),
      orderOf τ = 3 ∧ ∀ x : ↥X, χ (X.normalizerMonoidHom ⟨σ, hσN⟩ x) = psuField hU τ (χ x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨hq', -⟩ | ⟨-, ⟨e⟩⟩
  · omega
  set F := GaloisField 2 (2 * (3 * n)) with hFdef
  have hcardF : Nat.card F = 2 ^ (2 * (3 * n)) := GaloisField.card 2 _ (by omega)
  have hU : UnitaryFieldData 2 (3 * n) F := ⟨Nat.prime_two, by omega, hcardF⟩
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
  set χ₀ : ↥X ≃* unitaryPSU hU 3 := e.trans φ.symm with hχ₀
  set α := X.normalizerMonoidHom ⟨σ, hσN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    rw [hα, ← map_pow]
    have : (⟨σ, hσN⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hσ3)
    rw [this, map_one]
  have hout := not_isInnerAut_of_inducesStdKind_field148 hind hσN
  have hαk : ∀ k : ↥X, (k : Γ) ∈ K → α k = k := by
    intro k hk
    apply Subtype.ext
    show σ * (k : Γ) * σ⁻¹ = k
    rw [(Subgroup.mem_centralizer_singleton_iff.mp (hKC hk)).symm, mul_inv_cancel_right]
  have h2K : 2 ∣ Nat.card K := Item148Res5.two_dvd_card_of_isoLThreePi hn hK
  obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' 2 h2K
  set t : ↥X := ⟨k₀, hKX k₀.2⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    have : (k₀ : Γ) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← hk₀, pow_orderOf_eq_one, Subgroup.coe_one]
    exact this
  have ht1 : t ≠ 1 := by
    intro h1
    have h2 : ((t : ↥X) : Γ) = 1 := congrArg Subtype.val h1
    have hk1 : k₀ = 1 := Subtype.ext h2
    rw [hk1, orderOf_one] at hk₀
    norm_num at hk₀
  have hαt : α t = t := hαk t k₀.2
  set β := MulAut.congr χ₀ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := fun hb =>
    hout ((KFacts.isInnerAut_congr χ₀ α).mp hb)
  have hβt : β (χ₀ t) = χ₀ t := by
    change χ₀ (α (χ₀.symm (χ₀ t))) = χ₀ t
    rw [MulEquiv.symm_apply_apply, hαt]
  have hχt2 : (χ₀ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hχt1 : χ₀ t ≠ 1 := fun h1 => ht1 (χ₀.injective (h1.trans (map_one χ₀).symm))
  have hD : β ∉ (psuConj hU).range := by
    rintro ⟨A, hA⟩
    apply hβout
    rw [← hA]
    exact Item148Res5.isInnerAut_of_psuConj_fix_involution hU
      ((Item148Res5.nine_dvd_of_two_pow_three_mul n).2 hq) (by rw [hA]; exact hβ3) hχt2 hχt1
      (by rw [hA]; exact hβt)
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  obtain ⟨τ, hτ, H, hβH⟩ :=
    CFSG.RankThree.PartTwo.KFacts.unitary_order_three_field_descent hq2 β hβ3 hD
  refine ⟨hU, χ₀.trans ((psuConj hU H)⁻¹ : MulAut (unitaryPSU hU 3)), τ, hτ, fun x => ?_⟩
  have h1 : β (χ₀ x) = χ₀ (α x) := by
    change χ₀ (α (χ₀.symm (χ₀ x))) = _
    rw [MulEquiv.symm_apply_apply]
  change (psuConj hU H)⁻¹ (χ₀ (α x)) = psuField hU τ ((psuConj hU H)⁻¹ (χ₀ x))
  rw [← h1, hβH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]

@[expose] def KF148FieldTopTwistROddU : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (J K E : Subgroup X) (σ : X) (n : ℕ), 1 ≤ n →
    Sec4.IsoLThreePi ↥J 2 (3 * n) → KFacts.InducesStdKind J σ .field → σ ^ 3 = 1 →
    K ≤ J → K ≤ Subgroup.centralizer ({σ} : Set X) → IsSimpleGroup ↥K →
    Sec4.IsoLThreePi ↥K 2 n → E ≤ J → E ≤ Subgroup.centralizer ({σ} : Set X) →
    IsMulCommutative ↥E → (∀ x ∈ E, x ^ 3 = 1) →
    ∀ z ∈ E, z ≠ 1 → ¬ 2 ∣ Nat.card ↥(J ⊓ Subgroup.centralizer ({z} : Set X)) →
    2 ^ (3 * n) % 3 = 2 →
    ∀ R : Subgroup X, R ≤ K ⊓ Subgroup.centralizer ({z} : Set X) →
      ¬ 3 ∣ Nat.card R → Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (R : Set X) →
      R = ⁅R, Subgroup.zpowers σ ⊔ E⁆ → R ≠ ⊥ →
      ∃ V : Subgroup X, V ≤ J ⊓ Subgroup.centralizer ({σ * z} : Set X) ∧ ¬ 3 ∣ Nat.card V ∧
        Subgroup.zpowers σ ⊔ E ≤ Subgroup.normalizer (V : Set X) ∧
        ¬ ⁅V, Subgroup.zpowers σ ⊔ E⁆ ≤ K

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148V
