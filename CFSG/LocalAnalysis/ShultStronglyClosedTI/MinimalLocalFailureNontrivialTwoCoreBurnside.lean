module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore

theorem factorization_two_pow_mul_of_odd {a n : ℕ} (hn : Odd n) :
    (2 ^ a * n).factorization 2 = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hn.pos.ne',
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hn.not_two_dvd_nat, add_zero]

theorem factorization_two_pow_mul_of_ne {a n p : ℕ} (hn : n ≠ 0) (hp2 : p ≠ 2) :
    (2 ^ a * n).factorization p = n.factorization p := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hn, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_of_ne hp2, zero_add]

variable {F : Type*} [Group F] [Finite F]

theorem exists_normal_complement_of_odd_hall {W : Subgroup F} {a : ℕ}
    (hcard : Nat.card F = 2 ^ a * Nat.card W)
    (hN : ∀ W₀ : Subgroup F, W₀ ≤ W → W₀ ≠ ⊥ →
      Subgroup.normalizer (W₀ : Set F) ≤ Subgroup.centralizer (W₀ : Set F))
    (S : Sylow 2 F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ N : Subgroup F, N.Normal ∧ ¬ p ∣ Nat.card N ∧ (S : Subgroup F) ≤ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨PW⟩ : Nonempty (Sylow p W) := inferInstance
  set P : Subgroup F := (PW : Subgroup W).map W.subtype with hPdef
  have hPcard : Nat.card P = p ^ (Nat.card F).factorization p := by
    rw [hPdef, Subgroup.card_map_of_injective W.subtype_injective, Sylow.card_eq_multiplicity,
      hcard, factorization_two_pow_mul_of_ne Nat.card_pos.ne' hp2]
  set P' : Sylow p F := Sylow.ofCard P hPcard with hP'def
  have hPN : Subgroup.normalizer ((P' : Subgroup F) : Set F) ≤
      Subgroup.centralizer ((P' : Subgroup F) : Set F) := by
    change Subgroup.normalizer (P : Set F) ≤ Subgroup.centralizer (P : Set F)
    by_cases hP : P = ⊥
    · intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hP, SetLike.mem_coe, Subgroup.mem_bot] at hx
      rw [hx, one_mul, mul_one]
    · exact hN P (Subgroup.map_subtype_le _) hP
  obtain ⟨N, hNn, hNp, hNidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement P' hPN
  refine ⟨N, hNn, hNp, ?_⟩
  have hq : IsPGroup p (F ⧸ N) := by
    apply IsPGroup.of_card (n := (Nat.card F).factorization p)
    rw [← Subgroup.index_eq_card, hNidx]
    exact hPcard
  apply CFSG.GroupTheory.le_of_normal_coprime_of_isPGroup_quotient N S hq
  rw [Sylow.card_eq_multiplicity]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

theorem card_pCore_two_eq_of_odd_hall {W : Subgroup F} (hWodd : Odd (Nat.card W)) {a : ℕ}
    (hcard : Nat.card F = 2 ^ a * Nat.card W)
    (hN : ∀ W₀ : Subgroup F, W₀ ≤ W → W₀ ≠ ⊥ →
      Subgroup.normalizer (W₀ : Set F) ≤ Subgroup.centralizer (W₀ : Set F)) :
    Nat.card (CFSG.pCore 2 F) = 2 ^ a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 F) := inferInstance
  have hScard : Nat.card (S : Subgroup F) = 2 ^ a := by
    rw [Sylow.card_eq_multiplicity, hcard, factorization_two_pow_mul_of_odd hWodd]
  choose N hNn hNp hSN using fun (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) =>
    exists_normal_complement_of_odd_hall hcard hN S hp hp2
  set T : Subgroup F := ⨅ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2), N p hp hp2 with hTdef
  have hTn : T.Normal := Subgroup.normal_iInf_normal fun p =>
    Subgroup.normal_iInf_normal fun hp => Subgroup.normal_iInf_normal fun hp2 => hNn p hp hp2
  have hST : (S : Subgroup F) ≤ T :=
    le_iInf fun p => le_iInf fun hp => le_iInf fun hp2 => hSN p hp hp2
  have hT2 : IsPGroup 2 T := by
    apply IsPGroup.of_card (n := (Nat.card T).primeFactorsList.length)
    apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
    intro d hd hdT
    by_contra hd2
    have hTN : T ≤ N d hd hd2 := iInf_le_of_le d (iInf_le_of_le hd (iInf_le _ hd2))
    exact hNp d hd hd2 (hdT.trans (Subgroup.card_dvd_of_le hTN))
  have hTcore : T ≤ CFSG.pCore 2 F := le_sSup ⟨hTn, hT2⟩
  have heq : CFSG.pCore 2 F = S := S.is_maximal' CFSG.pCore_isPGroup (hST.trans hTcore)
  rw [heq, hScard]

end CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore
