module

public import CFSG.RankThree.PartTwo.Sec18.Item189Steps
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO3Act
import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec20.Step208MSPairProof
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)


namespace Item189O3Proof

variable {G : Type} [Group G] [Finite G]

theorem mem_of_pow_eq_one_of_odd {Z T : Subgroup G} (hTZ : T ≤ Subgroup.normalizer (Z : Set G))
    (hT : IsPGroup 2 T) {x : G} (hx : x ∈ Z ⊔ T) {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1) :
    x ∈ Z := by
  have hXZ : Z ⊔ T ≤ Subgroup.normalizer (Z : Set G) := sup_le Subgroup.le_normalizer hTZ
  have hZK : Subgroup.zpowers x ≤ Subgroup.normalizer (Z : Set G) :=
    (Subgroup.zpowers_le.mpr hx).trans hXZ
  have h1 : Z.relIndex (Subgroup.zpowers x ⊔ Z) ∣ n := by
    rw [Sec20.relIndex_sup_eq_of_le_normalizer hZK]
    exact (Subgroup.relIndex_dvd_card _ _).trans
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hxn)
  have h2 : Z.relIndex (Subgroup.zpowers x ⊔ Z) ∣ Z.relIndex (Z ⊔ T) := by
    have hle : Subgroup.zpowers x ⊔ Z ≤ Z ⊔ T := sup_le (Subgroup.zpowers_le.mpr hx) le_sup_left
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex Z _ _ le_sup_right hle)
  have h3 : Z.relIndex (Z ⊔ T) ∣ Nat.card T := by
    rw [sup_comm, Sec20.relIndex_sup_eq_of_le_normalizer hTZ]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [hk] at h3
  have hcop : Nat.Coprime n (2 ^ k) := Nat.Coprime.pow_right k hn.coprime_two_right
  have h4 : Z.relIndex (Subgroup.zpowers x ⊔ Z) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) (h2.trans h3)
  rw [Subgroup.relIndex_eq_one] at h4
  exact h4 (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

omit [Finite G] in
theorem normalizer_le_normalizer_inSubgroup_pPrimeCore (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (inSubgroup (CFSG.pPrimeCore p) X : Set G) := by
  have : (CFSG.pPrimeCore p X).Characteristic :=
    Subgroup.characteristic_iff_map_eq.mpr fun φ => CFSG.pPrimeCore_map_iso p φ
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

theorem mem_thetaQuotCentralizer_of_pow_eq_one {L B X : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hq3 : q ≠ 3) (hLp : ⁅L, L⁆ = L)
    (eL : L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 2)) (hBL : B ≤ L) (hB9 : Nat.card B = 9)
    (hB3 : IsPGroup 3 B) (hX3 : ¬ 3 ∣ Nat.card X) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) {y : G} (hy : y ∈ X) {k : ℕ}
    (hyk : y ^ q ^ k = 1) : y ∈ Sec4.thetaQuotCentralizer L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbotN : B ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  have hbotq : IsPGroup q (⊥ : Subgroup G) := fun g => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨T, hT, -, hBT⟩ := exists_isSylowOf_le_of_coprime189 hB3 hBX hX3 bot_le hbotq hbotN
  have hTC : T ≤ Sec4.thetaQuotCentralizer L :=
    le_thetaQuotCentralizer_of_isPGroup hq2 hq3 hLp eL hBL hB9 hB3 hT.isPGroup
      (hT.le.trans hXN) hBT
  have hzq : IsPGroup q (Subgroup.zpowers y) := by
    rw [IsPGroup.iff_card]
    have h1 : Nat.card (Subgroup.zpowers y) ∣ q ^ k := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hyk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp h1
    exact ⟨j, hj⟩
  obtain ⟨T', hT', hyT'⟩ := Sec20.exists_isSylowOf_le hzq (Subgroup.zpowers_le.mpr hy)
  obtain ⟨g, hg, hgT⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hT hT'
  have h1 : g⁻¹ * y * g ∈ T := (hgT y).mp (hyT' (Subgroup.mem_zpowers y))
  have h2 := Sec12.conj_mem_thetaQuotCentralizer (hXN hg) (hTC h1)
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rwa [e] at h2

end Item189O3Proof

section Certs

open Item189O3Proof


theorem inSubgroup_pPrimeCore_normalClosureIn_eq_pCoreOf (h1812 : Item181_2) (h184 : Item184_1)
    (h187 : Item187) {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}
    (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) :
    inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
      CFSG.Open.pCoreOf 2 (normalClosureIn M c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp := hyp201One_of189 h h7
  set L := inSubgroup perfectResidual H with hLdef
  set K := normalClosureIn M c with hKdef
  set X := inSubgroup (CFSG.pPrimeCore 3) K with hXdef
  set O := CFSG.Open.pCoreOf 2 L with hOdef
  have hAM : A ≤ M := sec18Std_le h.toSec18Std
  have hKM : K ≤ M := normalClosureIn_le_of_sec18H189 h
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := Sec20.le_normalizer_normalClosureIn M c
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := le_normalizer_inSubgroup_pPrimeCore 3 K
  have hMX : M ≤ Subgroup.normalizer (X : Set G) :=
    hMK.trans (normalizer_le_normalizer_inSubgroup_pPrimeCore 3 K)
  have hXK : X ≤ K := Subgroup.map_subtype_le _
  have hX3 : ¬ 3 ∣ Nat.card X := by
    rw [hXdef, inSubgroup, Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := by
    refine h187 G A M H c h h7 X ?_
    rw [mem_invariantPiSubgroups_piCompl_iff Nat.prime_three]
    exact ⟨le_top, hX3, sup_le (hAM.trans hMX) ((s189_le M H).trans hMX)⟩
  obtain ⟨⟨eL⟩, -⟩ := h184 G A M h.toSec18Std H h.mem_scriptH
  have hLp : ⁅L, L⁆ = L := commutator_inSubgroup_perfectResidual H
  have hB9 : Nat.card (A ⊓ L : Subgroup G) = 9 := card_inf_of_sec18H h1812 h184 h
  have hB3 : IsPGroup 3 (A ⊓ L : Subgroup G) :=
    (isE27_of_mem_partTwoE h.mem_partTwoE).isPGroup.to_le inf_le_left
  have hBX : A ⊓ L ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans (hAM.trans hMX)
  have hθO : inSubgroup (aschbacherSolvableCore 3) L = O := inSubgroup_theta_eq_pCoreOf hLp eL
  have hOM : O ≤ M := Sec20.pCoreOf_le_of_hyp201One hyp
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hodd : ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ Nat.card X := by
    intro q hq hq2 hqd
    haveI : Fact q.Prime := ⟨hq⟩
    have hq3 : q ≠ 3 := fun h3 => hX3 (h3 ▸ hqd)
    obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := X) q hqd
    have hy₀X : (x₀ : G) ∈ X := x₀.2
    have hy₀q : (x₀ : G) ^ q = 1 := by
      rw [← Subgroup.coe_pow, ← hx₀, pow_orderOf_eq_one]
      rfl
    have hy₀1 : (x₀ : G) ≠ 1 := by
      intro h1
      have : x₀ = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hx₀
      exact hq.one_lt.ne hx₀
    set S0 : Set G := {y | y ∈ X ∧ ∃ k : ℕ, y ^ q ^ k = 1} with hS0
    set Z : Subgroup G := Subgroup.closure S0 with hZ
    have hZX : Z ≤ X := (Subgroup.closure_le X).mpr fun y hy => hy.1
    have hZC : Z ≤ Sec4.thetaQuotCentralizer L := by
      rw [hZ, Subgroup.closure_le]
      rintro y ⟨hyX, k, hyk⟩
      exact mem_thetaQuotCentralizer_of_pow_eq_one hq2 hq3 hLp eL inf_le_right hB9 hB3 hX3 hBX
        hXN hyX hyk
    have hMZ : M ≤ Subgroup.normalizer (Z : Set G) := by
      intro m hm
      refine Sec20.mem_normalizer_of_map_conj_le ?_
      rw [hZ, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨hyX, k, hyk⟩, rfl⟩
      refine Subgroup.subset_closure ⟨?_, k, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hMX hm) y).mp hyX
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [conj_pow, hyk, mul_one, mul_inv_cancel]
    have hZM : Z ≤ M := hZX.trans (hXK.trans hKM)
    have hy₀Z : (x₀ : G) ∈ Z := Subgroup.subset_closure ⟨hy₀X, 1, by simpa using hy₀q⟩
    have hOZ : O ≤ Subgroup.normalizer (Z : Set G) := hOM.trans hMZ
    have hLZ : L ≤ Subgroup.normalizer (Z : Set G) := by
      intro l hl
      refine Sec20.mem_normalizer_of_map_conj_le ?_
      rw [hZ, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨hyX, k, hyk⟩, rfl⟩
      show l * y * l⁻¹ ∈ Z
      have hyZ : y ∈ Z := Subgroup.subset_closure ⟨hyX, k, hyk⟩
      have hu : l * y * l⁻¹ * y⁻¹ ∈ O := by
        have h1 := (Sec6.mem_thetaQuotCentralizer_iff.mp (hZC hyZ)).2 l⁻¹ (L.inv_mem hl)
        rw [hθO] at h1
        have e : (l⁻¹)⁻¹ * (y * l⁻¹ * y⁻¹) = l * y * l⁻¹ * y⁻¹ := by group
        rwa [e] at h1
      have hgZO : l * y * l⁻¹ ∈ Z ⊔ O := by
        have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left hyZ)
      refine mem_of_pow_eq_one_of_odd hOZ hO2 hgZO (n := q ^ k) ((hq.odd_of_ne_two hq2).pow) ?_
      rw [conj_pow, hyk, mul_one, mul_inv_cancel]
    exact Sec20.not_le_of_hyp201One hyp
      (hLZ.trans (normalizer_le_of_normal189 h.charTwoType h.mem_scriptM.1 hZM hMZ hy₀Z hy₀1))
  have hX2 : IsPGroup 2 X := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.card X).primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
    intro d hd hdvd
    by_contra hne
    exact hodd d hd hne hdvd
  refine le_antisymm
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXK hKX hX2) ?_
  have hO2K : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.Open.pCoreOf 2 K)) := by
    obtain ⟨k, hk⟩ := hO2K.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  exact le_inSubgroup_pPrimeCore_of hcop (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)

theorem step189O3_of (h1812 : Item181_2) (h184 : Item184_1) (h187 : Item187) :
    Step189O3 := fun _ _ _ _ _ _ _ hset _ =>
  inSubgroup_pPrimeCore_normalClosureIn_eq_pCoreOf h1812 h184 h187 hset.toSec18H hset.hyp187

end Certs

end CFSG.RankThree.PartTwo.Sec18
