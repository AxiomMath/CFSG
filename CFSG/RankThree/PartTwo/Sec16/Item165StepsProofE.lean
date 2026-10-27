module

public import CFSG.RankThree.PartTwo.Sec16.Item165Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

@[expose] def Q0R165 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → IsL3TwoPow L →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), CFSG.Open.pCoreOf 2 Y₀ ≤ S

@[expose] def CentU165 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      (∃ n : ℕ, 1 ≤ n ∧ 2 ^ n % 3 = 2 ∧
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
          CFSG.Assembly.RankThreeEven.projSU 3 2 n)) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), ⁅Y₀, S⁆ ≤ CFSG.Open.pCoreOf 2 Y₀

@[expose] def Tor165L : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      (∃ n : ℕ, 1 ≤ n ∧ 2 ^ n % 3 = 1 ∧
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≠ ⊥ →
        ¬ Y₀ ≤ Subgroup.normalizer (S : Set G) → CFSG.Open.pCoreOf 2 Y₀ ≤ S →
          ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ P : Subgroup G, P ≤ Y₀ ∧
            CFSG.Open.pCoreOf 2 Y₀ ≤ P ∧ S ≤ Subgroup.normalizer (P : Set G) ∧
            (∃ k : ℕ, 1 ≤ k ∧ Nat.card P = p ^ k * Nat.card (CFSG.Open.pCoreOf 2 Y₀)) ∧
            ∀ e ∈ P, e ∉ CFSG.Open.pCoreOf 2 Y₀ →
              Y₀ ≤ (Y₀ ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.zpowers e

namespace Steps165

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_commutator_le {Y S O : Subgroup G} (hYS : ⁅Y, S⁆ ≤ O) (hOS : O ≤ S) :
    Y ≤ Subgroup.normalizer (S : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have h1 : y * s * y⁻¹ * s⁻¹ ∈ S := hOS (hYS (Subgroup.commutator_mem_commutator hy hs))
    have h2 : y * s * y⁻¹ = (y * s * y⁻¹ * s⁻¹) * s := by group
    rw [h2]
    exact S.mul_mem h1 hs
  · intro hs
    have hs' : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ ∈ S := by
      have h1 : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ * (y * s * y⁻¹)⁻¹ ∈ S :=
        hOS (hYS (Subgroup.commutator_mem_commutator (Y.inv_mem hy) hs))
      have h2 : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ =
          (y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ * (y * s * y⁻¹)⁻¹) * (y * s * y⁻¹) := by group
      rw [h2]
      exact S.mul_mem h1 hs
    have : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s := by group
    rwa [this] at hs'

theorem exists_sylow_sup_eq {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P O : Subgroup G}
    (hOP : O ≤ P) (hPO : P ≤ Subgroup.normalizer (O : Set G)) (hO2 : IsPGroup 2 O)
    (hcard : Nat.card P = p ^ k * Nat.card O) :
    ∃ E : Subgroup G, E ≤ P ∧ IsPGroup p E ∧ Nat.card E = p ^ k ∧ Disjoint E O ∧
      E ⊔ O = P := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥P) := inferInstance
  set E := (Q : Subgroup ↥P).map P.subtype with hE
  have hEP : E ≤ P := Subgroup.map_subtype_le _
  have hEp : IsPGroup p E := Q.isPGroup'.map _
  have hEQ : Nat.card E = Nat.card (Q : Subgroup ↥P) :=
    Subgroup.card_map_of_injective P.subtype_injective
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hO2
  have hidx : ¬ p ∣ (Q : Subgroup ↥P).index := Q.not_dvd_index
  have hQ := Subgroup.card_mul_index (Q : Subgroup ↥P)
  have hcop1 : Nat.Coprime (p ^ k) (Q : Subgroup ↥P).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hidx)
  have hcop2 : Nat.Coprime (p ^ j) (2 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : p ^ k ∣ p ^ j := by
    refine hcop1.dvd_of_dvd_mul_right ?_
    rw [← hj, hQ, hcard]
    exact dvd_mul_right _ _
  have h2 : p ^ j ∣ p ^ k := by
    refine hcop2.dvd_of_dvd_mul_right ?_
    rw [← hm, ← hcard, ← hQ, hj]
    exact dvd_mul_right _ _
  have hjk : j = k := le_antisymm ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2)
    ((Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1)
  have hEk : Nat.card E = p ^ k := by rw [hEQ, hj, hjk]
  have hdisj : Disjoint E O := IsPGroup.disjoint_of_ne p 2 hp2 E O hEp hO2
  refine ⟨E, hEP, hEp, hEk, hdisj, ?_⟩
  have hprod := Sec6.card_sup_mul_card_inf (hEP.trans hPO)
  rw [hdisj.eq_bot, Subgroup.card_bot, mul_one, hEk, ← hcard] at hprod
  exact Subgroup.eq_of_le_of_card_ge (sup_le hEP hOP) hprod.ge

omit [Finite G] in
theorem coe_sup_eq_mul_of_tor {E O P S : Subgroup G} (hEOP : E ⊔ O = P)
    (hEO : E ≤ Subgroup.normalizer (O : Set G)) (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hOS : O ≤ S) : ((E ⊔ S : Subgroup G) : Set G) = (E : Set G) * (S : Set G) := by
  have hES : E ⊔ S = P ⊔ S := by
    rw [← hEOP]
    exact le_antisymm (sup_le_sup_right le_sup_left _)
      (sup_le (sup_le le_sup_left (hOS.trans le_sup_right)) le_sup_right)
  refine le_antisymm ?_ ?_
  swap
  · rintro _ ⟨e, he, s, hs, rfl⟩
    exact Subgroup.mul_mem_sup he hs
  rw [hES, Subgroup.coe_mul_of_right_le_normalizer_left P S hSP]
  rintro _ ⟨x, hx, s, hs, rfl⟩
  rw [← hEOP] at hx
  have hx' : x ∈ ((E ⊔ O : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E O hEO] at hx'
  obtain ⟨e, he, o, ho, rfl⟩ := hx'
  exact ⟨e, he, o * s, S.mul_mem (hOS ho) hs, (mul_assoc e o s).symm⟩

theorem isCharacteristicP_of_tor {Y₀ P S : Subgroup G}
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) (hPY : P ≤ Y₀)
    (hOP : CFSG.Open.pCoreOf 2 Y₀ ≤ P) (hSP : S ≤ Subgroup.normalizer (P : Set G))
    (hS2 : IsPGroup 2 S) : IsCharacteristicP 2 ↥(P ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : IsCharacteristicP 2 ↥Y₀ :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥Y₀ 2).mpr hF
  have hJ : CFSG.pCore 2 ↥Y₀ ≤ P.subgroupOf Y₀ := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hOP ⟨x, hx, rfl⟩)
  have hPc : IsCharacteristicP 2 ↥P := Sec14.isCharacteristicP_of_mulEquiv'
    (Subgroup.subgroupOfEquivOfLe hPY) (Sec14.isCharacteristicP_of_pCore_le _ hY hJ)
  exact Proof165.isCharacteristicP_sup hSP hS2 hPc

theorem exists_e165_of_tor {Y₀ S P : Subgroup G} {p k : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀) (hS2 : IsPGroup 2 S)
    (hOS : CFSG.Open.pCoreOf 2 Y₀ ≤ S) (hPY : P ≤ Y₀) (hOP : CFSG.Open.pCoreOf 2 Y₀ ≤ P)
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hk : 1 ≤ k)
    (hcard : Nat.card P = p ^ k * Nat.card (CFSG.Open.pCoreOf 2 Y₀))
    (hgen : ∀ e ∈ P, e ∉ CFSG.Open.pCoreOf 2 Y₀ →
      Y₀ ≤ (Y₀ ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.zpowers e) :
    ∃ E : Subgroup G, E ≤ Y₀ ∧ IsPGroup p E ∧ E ≠ ⊥ ∧
      ((E ⊔ S : Subgroup G) : Set G) = (E : Set G) * (S : Set G) ∧
      IsCharacteristicP 2 ↥(E ⊔ S) ∧
      ∀ e ∈ E, e ≠ 1 →
        Y₀ ⊔ S ≤ ((Y₀ ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 Y₀ with hO
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y₀
  have hPO : P ≤ Subgroup.normalizer (O : Set G) :=
    hPY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)
  obtain ⟨E, hEP, hEp, hEk, hdisj, hEOP⟩ :=
    exists_sylow_sup_eq hp (by omega) hOP hPO hO2 hcard
  have hE1 : E ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hEk
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  refine ⟨E, hEP.trans hPY, hEp, hE1, coe_sup_eq_mul_of_tor hEOP (hEP.trans hPO) hSP hOS, ?_, ?_⟩
  · have hES : E ⊔ S = P ⊔ S := by
      rw [← hEOP]
      exact le_antisymm (sup_le_sup_right le_sup_left _)
        (sup_le (sup_le le_sup_left (hOS.trans le_sup_right)) le_sup_right)
    rw [hES]
    exact isCharacteristicP_of_tor hF hPY hOP hSP hS2
  · intro e he he1
    have heO : e ∉ O := fun heO => he1 (Subgroup.disjoint_def.mp hdisj he heO)
    have hY := hgen e (hEP he) heO
    refine sup_le (hY.trans (sup_le_sup_right (inf_le_inf_right _ le_sup_left) _)) ?_
    exact le_sup_of_le_left (le_inf le_sup_right Subgroup.le_normalizer)

end Steps165

theorem step165E_of (hQ0 : Q0R165) (h153 : Item153MainR) (hU : CentU165) (hL : Tor165L) :
    Step165E := by
  intro G _ _ A c L Y₀ h hL3 S hS hS1 hYS
  have hOS := hQ0 G A c L Y₀ h hL3 S hS
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  obtain ⟨n, hn, hiso⟩ := hL3
  rcases hiso with ⟨hq, hφ⟩ | ⟨hq, hφ⟩
  · obtain ⟨p, hp, hp3, P, hPY, hOP, hSP, ⟨k, hk, hcard⟩, hgen⟩ :=
      hL G A c L Y₀ h ⟨n, hn, hq, hφ⟩ S hS hS1 hYS hOS
    have hF : generalizedFitting ↥Y₀ = CFSG.pCore 2 ↥Y₀ :=
      (h153 G A c L h.toSec15R Y₀ h.mem_y0Star).2.2
    exact ⟨p, hp, hp3, Steps165.exists_e165_of_tor hp hp3 hF hS2 hOS hPY hOP hSP hk hcard hgen⟩
  · exact absurd (Steps165.le_normalizer_of_commutator_le
      (hU G A c L Y₀ h ⟨n, hn, hq, hφ⟩ S hS) hOS) hYS

end CFSG.RankThree.PartTwo.Sec16
