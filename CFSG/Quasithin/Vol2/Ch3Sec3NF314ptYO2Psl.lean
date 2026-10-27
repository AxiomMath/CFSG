module

public import CFSG.Quasithin.Vol2.Ch3Sec3L2qFacts

public section

open CFSG.Quasithin CFSG.GorensteinWalter

namespace CFSG.Quasithin.H13.NF314pt

theorem yo2_mem_sylow_of_normalizes {X : Type} [Group X] [Finite X] {W : Subgroup X}
    (hW2 : IsPGroup 2 W) (hWi : ¬ 2 ∣ W.index) {k : X}
    (hk : k ∈ Subgroup.normalizer (W : Set X)) (hk2 : ∃ m : ℕ, k ^ 2 ^ m = 1) : k ∈ W := by
  obtain ⟨m, hm⟩ := hk2
  set N := Subgroup.normalizer (W : Set X)
  have hWN : W ≤ N := Subgroup.le_normalizer
  have hdvd : (W.subgroupOf N).index ∣ W.index := Dvd.intro _ (Subgroup.relIndex_mul_index hWN)
  have hnd : ¬ 2 ∣ (W.subgroupOf N).index := fun h2 => hWi (h2.trans hdvd)
  have hcop : Nat.Coprime (2 ^ m) (W.subgroupOf N).index :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
  haveI : (W.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mpr le_rfl
  have hy : ((⟨k, hk⟩ : N) : N ⧸ W.subgroupOf N) ^ 2 ^ m = 1 := by
    rw [← QuotientGroup.mk_pow]
    have h1 : (⟨k, hk⟩ : N) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
    rw [h1, QuotientGroup.mk_one]
  have hord1 : orderOf ((⟨k, hk⟩ : N) : N ⧸ W.subgroupOf N) ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one hy
  have hord2 : orderOf ((⟨k, hk⟩ : N) : N ⧸ W.subgroupOf N) ∣ (W.subgroupOf N).index :=
    orderOf_dvd_natCard _
  have h1 : orderOf ((⟨k, hk⟩ : N) : N ⧸ W.subgroupOf N) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem yo2_psl2_two_sub {Q : Type} [Group Q] [Finite Q]
    {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q)
    (h3 : q % 8 = 3 ∨ q % 8 = 5) {A : Subgroup Q} (eA : ↥A ≃* PSL2 F)
    {R : Subgroup Q} (hRA : R ≤ A) (hR : IsPGroup 2 R) :
    Nat.card R ∣ 4 ∧ (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧
      (Nat.card R = 4 → ¬ 2 ∣ (R.subgroupOf A).index) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' : IsPGroup 2 ↥(R.subgroupOf A) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRA).symm
  have hcard : Nat.card ↥(R.subgroupOf A) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRA).toEquiv
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hR'
  have hP4 : Nat.card (P : Subgroup ↥A) = 4 :=
    CFSG.Quasithin.H13.L2q.card_sylow_four eA hF hq hq5 h3 P.isPGroup' P.not_dvd_index
  have hdvd : Nat.card R ∣ 4 := by
    have h := Subgroup.card_dvd_of_le hP
    rw [hP4, hcard] at h
    exact h
  refine ⟨hdvd, ?_, fun h4 => ?_⟩
  ·
    have hcomm : IsMulCommutative ↥R := by
      have h4' : Nat.card R ∣ 2 ^ 2 := hdvd
      obtain ⟨m, hm, hRm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4'
      interval_cases m
      · rw [pow_zero] at hRm
        obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.mp hRm
        exact ⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩
      · rw [pow_one] at hRm
        haveI : IsCyclic ↥R := isCyclic_of_prime_card hRm
        infer_instance
      · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hRm
    intro a ha b hb
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  ·
    have hRP : R.subgroupOf A = (P : Subgroup ↥A) :=
      Subgroup.eq_of_le_of_card_ge hP (by omega)
    rw [hRP]
    exact P.not_dvd_index

theorem yo2_center_trivial {Q : Type} [Group Q] {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) {A : Subgroup Q} (eA : ↥A ≃* PSL2 F)
    {k : Q} (hkA : k ∈ A) (hk : ∀ a ∈ A, k * a = a * k) : k = 1 := by
  have hz : eA ⟨k, hkA⟩ ∈ Subgroup.center (PSL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := eA.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hk a.1 a.2).symm
  rw [CFSG.Quasithin.H13.L2q.center_eq_bot hF hq hq5, Subgroup.mem_bot] at hz
  have h1 : (⟨k, hkA⟩ : ↥A) = 1 := eA.injective (hz.trans (map_one eA).symm)
  exact congrArg Subtype.val h1

theorem yo2_cyclic_three {Q : Type} [Group Q] {F : Type} [Field F]
    [Finite F] {q : ℕ} (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) {A : Subgroup Q}
    (eA : ↥A ≃* PSL2 F) (B : Subgroup Q) (hBA : B ≤ A) (hB : IsPGroup 3 B) : IsCyclic B := by
  have h3 : IsPGroup 3 ↥(B.subgroupOf A) := hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBA).symm
  have hc : IsCyclic ↥(B.subgroupOf A) :=
    CFSG.Quasithin.H13.L2q.isCyclic_three eA hF hq hq5 (B.subgroupOf A) h3
  exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hBA)).mp hc

end CFSG.Quasithin.H13.NF314pt

end
