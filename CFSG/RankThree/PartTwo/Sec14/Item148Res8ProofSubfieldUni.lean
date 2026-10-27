module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofUni
import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSubfieldLin
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofCent
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofField
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField)
open CFSG.HardMathSupport.Solomon.Coordinator (l3bUT l3bFix commutator_fix_le_l3bUT)

section Transfer


theorem subfieldOver_of_unitary {Γ : Type} [Group Γ] [Finite Γ]
    {X K H : Subgroup Γ} {σ : Γ} {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥X 2 (3 * n))
    (hq : 2 ^ (3 * n) % 3 = 2) (hind : KFacts.InducesStdKind X σ .field) (hσ3 : σ ^ 3 = 1)
    (hσN : σ ∈ Subgroup.normalizer (X : Set Γ)) (hKX : K ≤ X)
    (hKC : K ≤ Subgroup.centralizer ({σ} : Set Γ)) (hKs : IsSimpleGroup ↥K)
    (hK : Sec4.IsoLThreePi ↥K 2 n) (hKH : K ≤ H) (hHX : H ≤ X) :
    H = X ∨ (H ≤ Subgroup.normalizer (K : Set Γ) ∧ Nat.card H ∣ 3 * Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcube : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by rw [← pow_mul, mul_comm]
  have hmod : 2 ^ (3 * n) % 3 = 2 ^ n % 3 := by
    rw [hcube]
    exact Item148Rank.pow_three_mod_three148 _
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ho
    · exfalso
      rw [show 3 * (m + m) = 6 * m by ring, pow_mul, Nat.pow_mod] at hq
      norm_num at hq
    · exact ho
  have h2K : 2 ∣ Nat.card K := Item148Res5.two_dvd_card_of_isoLThreePi hn hK
  have h3K : 3 ∣ Nat.card K := Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi hn hK
  have hKnc : ¬ IsMulCommutative ↥K := not_isMulCommutative_of_six_dvd h2K h3K
  have hKp : Group.IsPerfect ↥K := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hKnc
  rcases hX with ⟨hq', -⟩ | ⟨-, ⟨e⟩⟩
  · omega
  rcases hK with ⟨hqK, -⟩ | ⟨-, ⟨eK⟩⟩
  · omega
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hn1 : n = 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    subst hn1
    have := Sec13.isSolvable_projSU_two
    have hsolv : Group.IsSolvable ↥K :=
      Group.isSolvable_of_surjective (f := eK.symm.toMonoidHom) eK.symm.surjective
    have : Nontrivial ↥K := hKs.toNontrivial
    exact Group.IsPerfect.not_isSolvable ↥K hsolv
  set F := GaloisField 2 (2 * (3 * n)) with hFdef
  have hU : UnitaryFieldData 2 (3 * n) F :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  obtain ⟨φ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_unitaryPSU_mulEquiv_projSU hU
  set τ : ↥X ≃* unitaryPSU hU 3 := e.trans φ.symm with hτ
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
  set β := MulAut.congr τ α with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hα3, map_one]
  have hβout : ¬ KFacts.IsInnerAut β := fun hb =>
    hout ((KFacts.isInnerAut_congr τ α).mp hb)
  have hβt : β (τ t) = τ t := by
    change τ (α (τ.symm (τ t))) = τ t
    rw [MulEquiv.symm_apply_apply, hαt]
  have hτt2 : (τ t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hτt1 : τ t ≠ 1 := fun h1 => ht1 (τ.injective (h1.trans (map_one τ).symm))
  have hD : β ∉ (psuConj hU).range := by
    rintro ⟨A, hA⟩
    apply hβout
    rw [← hA]
    exact Item148Res5.isInnerAut_of_psuConj_fix_involution hU
      ((Item148Res5.nine_dvd_of_two_pow_three_mul n).2 hq) (by rw [hA]; exact hβ3) hτt2 hτt1
      (by rw [hA]; exact hβt)
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  obtain ⟨σ', hσ', H₀, hβH⟩ :=
    CFSG.RankThree.PartTwo.KFacts.unitary_order_three_field_descent hq2 β hβ3 hD
  set γ := psuConj hU H₀ with hγ
  set ψ : ↥X ≃* unitaryPSU hU 3 := τ.trans (γ⁻¹ : MulAut (unitaryPSU hU 3)) with hψ
  have hψα : ∀ x : ↥X, ψ (α x) = psuField hU σ' (ψ x) := by
    intro x
    have h1 : β (τ x) = τ (α x) := by
      change τ (α (τ.symm (τ x))) = τ (α x)
      rw [MulEquiv.symm_apply_apply]
    have h2 : psuField hU σ' = γ⁻¹ * β * γ := by rw [hβH]; group
    change γ⁻¹ (τ (α x)) = psuField hU σ' (γ⁻¹ (τ x))
    rw [h2, ← h1]
    change γ⁻¹ (β (τ x)) = γ⁻¹ (β (γ (γ⁻¹ (τ x))))
    rw [MulAut.apply_inv_self]
  obtain ⟨f₀, hf₀, -, hcard₀⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_card_fixedField_of_orderOf_eq_three hU hσ'
  have hf₀n : f₀ = n := by omega
  rw [hf₀n] at hcard₀
  have h₀ : UnitaryFieldData 2 n (fixedField σ') := ⟨Nat.prime_two, hn, hcard₀⟩
  set P₀ := l3bUT hU rfl h₀ with hP₀
  set K' := (K.subgroupOf X).map ψ.toMonoidHom with hK'
  set H' := (H.subgroupOf X).map ψ.toMonoidHom with hH'
  have hcardK' : Nat.card K' = Nat.card K := by
    rw [hK', Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv]
  have hcardH' : Nat.card H' = Nat.card H := by
    rw [hH', Subgroup.card_map_of_injective ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv]
  have hK'fix : K' ≤ l3bFix (psuField hU σ') := by
    rintro _ ⟨k, hk, rfl⟩
    change psuField hU σ' (ψ k) = ψ k
    rw [← hψα, hαk k (Subgroup.mem_subgroupOf.mp hk)]
  have hK'p : Group.IsPerfect K' := by
    have e1 : ↥K ≃* K' := (Subgroup.subgroupOfEquivOfLe hKX).symm.trans
      ((K.subgroupOf X).equivMapOfInjective ψ.toMonoidHom ψ.injective)
    exact Group.IsPerfect.ofSurjective (f := e1.toMonoidHom) e1.surjective
  have hK'le : K' ≤ P₀ := by
    have hc : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp hK'p
    rw [← hc]
    exact (Subgroup.commutator_mono hK'fix hK'fix).trans (commutator_fix_le_l3bUT hU rfl h₀)
  have hcardP : Nat.card P₀ = Nat.card K := by
    have h1 := card_unitarySU_eq_three_mul hU hodd h₀
    rw [CFSG.RankThree.PartTwo.KFacts.card_unitarySU_three h₀] at h1
    have h2 := CFSG.RankThree.PartTwo.KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
    have hg : Nat.gcd 3 (2 ^ n + 1) = 3 :=
      Nat.gcd_eq_left (by have := two_pow_mod_three_of_odd hodd; omega)
    rw [hg, ← mul_assoc] at h2
    have h3 : 3 * Nat.card P₀ = Nat.card (CFSG.Assembly.RankThreeEven.projSU 3 2 n) * 3 := by
      rw [← h1, h2]
    rw [Nat.card_congr eK.toEquiv]
    omega
  have hK'eq : K' = P₀ := by
    refine (Subgroup.eq_of_le_of_card_ge hK'le ?_)
    rw [hcardP, hcardK']
  have hKH' : P₀ ≤ H' := by
    rw [← hK'eq, hK', hH']
    exact Subgroup.map_mono (fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hKH (Subgroup.mem_subgroupOf.mp hx)))
  have hmemK' : ∀ x : ↥X, ψ x ∈ K' ↔ (x : Γ) ∈ K := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := ψ.injective hyx
      rw [← this]
      exact Subgroup.mem_subgroupOf.mp hy
    · intro hx
      exact ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  rcases overgroup_l3bUT hU hn3 hodd hσ' h₀ H' hKH' with htop | ⟨hnorm, hdvd⟩
  · left
    apply le_antisymm hHX
    intro x hx
    have : ψ ⟨x, hx⟩ ∈ H' := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    have hyx' : y = ⟨x, hx⟩ := ψ.injective hyx
    rw [hyx'] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  · right
    refine ⟨?_, ?_⟩
    · intro h hh
      have hhX := hHX hh
      have hψh : ψ ⟨h, hhX⟩ ∈ Subgroup.normalizer (P₀ : Set (unitaryPSU hU 3)) :=
        hnorm ⟨⟨h, hhX⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · intro hk
        have hkX := hKX hk
        have hconj : h * k * h⁻¹ ∈ X := X.mul_mem (X.mul_mem hhX hkX) (X.inv_mem hhX)
        have h1 : ψ ⟨k, hkX⟩ ∈ P₀ := by
          rw [← hK'eq]; exact (hmemK' _).mpr hk
        have h2 := (Subgroup.mem_normalizer_iff.mp hψh (ψ ⟨k, hkX⟩)).mp h1
        have e : ψ ⟨h, hhX⟩ * ψ ⟨k, hkX⟩ * (ψ ⟨h, hhX⟩)⁻¹ = ψ ⟨h * k * h⁻¹, hconj⟩ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
        rw [e, ← hK'eq] at h2
        exact (hmemK' _).mp h2
      · intro hk
        have hconjX : h * k * h⁻¹ ∈ X := hKX hk
        have hkX : k ∈ X := by
          have : k = h⁻¹ * (h * k * h⁻¹) * h := by group
          rw [this]
          exact X.mul_mem (X.mul_mem (X.inv_mem hhX) hconjX) hhX
        have h1 : ψ ⟨h * k * h⁻¹, hconjX⟩ ∈ P₀ := by
          rw [← hK'eq]; exact (hmemK' _).mpr hk
        have e : ψ ⟨h, hhX⟩ * ψ ⟨k, hkX⟩ * (ψ ⟨h, hhX⟩)⁻¹ = ψ ⟨h * k * h⁻¹, hconjX⟩ := by
          rw [← map_mul, ← map_inv, ← map_mul]
          rfl
        rw [← e] at h1
        have h2 := (Subgroup.mem_normalizer_iff.mp hψh (ψ ⟨k, hkX⟩)).mpr h1
        rw [← hK'eq] at h2
        exact (hmemK' _).mp h2
    · rw [← hcardH', ← hcardK', hK'eq]
      exact hdvd

end Transfer

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
