module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaFork
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

theorem ggNEE_torusAct_simple_single (τ : Tag) {p : ℕ} [NeZero p] (i j : Fin τ.rank) :
    TableBExc.torusAct τ p (simple τ i) (Pi.single j 1 : Fin τ.rank → ZMod p) =
      Pi.single j 1 - ((τ.cartan i j : ℤ) : ZMod p) • Pi.single i 1 := by
  rw [ggExcPlus_torusAct_simple_eq, Finset.sum_eq_single j]
  · simp
  · intro b _ hbj; rw [Pi.single_eq_of_ne hbj, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem ggNEE_torusAct_simple_single_self (τ : Tag) {p : ℕ} [NeZero p] (j : Fin τ.rank) :
    TableBExc.torusAct τ p (simple τ j) (Pi.single j 1 : Fin τ.rank → ZMod p) =
      - Pi.single j 1 := by
  rw [ggNEE_torusAct_simple_single, Tag.cartan_self]
  simp only [Int.cast_ofNat, two_smul]
  abel

theorem ggNEE_torusAct_simple_neg_single (τ : Tag) {p : ℕ} [NeZero p] (i j : Fin τ.rank) :
    TableBExc.torusAct τ p (simple τ i) (- Pi.single j 1 : Fin τ.rank → ZMod p) =
      - Pi.single j 1 + ((τ.cartan i j : ℤ) : ZMod p) • Pi.single i 1 := by
  rw [ggExcPlus_torusAct_simple_eq]
  have hsum : (∑ j', ((τ.cartan i j' : ℤ) : ZMod p) *
      (- Pi.single j 1 : Fin τ.rank → ZMod p) j') = - ((τ.cartan i j : ℤ) : ZMod p) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj; simp [Pi.single_eq_of_ne hbj]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hsum, neg_smul, sub_neg_eq_add]

theorem ggNEE_torusAct_simple_mul_single_adj (τ : Tag) {p : ℕ} [NeZero p]
    {i j : Fin τ.rank} (h : τ.cartan i j = -1) :
    TableBExc.torusAct τ p (simple τ i * simple τ j) (Pi.single j 1 : Fin τ.rank → ZMod p) =
      - Pi.single j 1 - Pi.single i 1 := by
  rw [TableBExc.torusAct_mul, ggNEE_torusAct_simple_single_self,
    ggNEE_torusAct_simple_neg_single, h]
  rw [show ((-1 : ℤ) : ZMod p) = (-1 : ZMod p) by simp, neg_one_smul, sub_eq_add_neg]

theorem ggNEE_torusAct_simple_mul_single_orth (τ : Tag) {p : ℕ} [NeZero p]
    {i j : Fin τ.rank} (h : τ.cartan j i = 0) :
    TableBExc.torusAct τ p (simple τ i * simple τ j) (Pi.single i 1 : Fin τ.rank → ZMod p) =
      - Pi.single i 1 := by
  rw [TableBExc.torusAct_mul, ggNEE_torusAct_simple_single, h]
  rw [show ((0 : ℤ) : ZMod p) = 0 by simp, zero_smul, sub_zero,
    ggNEE_torusAct_simple_single_self]

theorem ggNEE_torusAct_simple_mul_single_adj_ne (τ : Tag) {p : ℕ} [Fact p.Prime]
    {i j : Fin τ.rank} (hij : i ≠ j) (h : τ.cartan i j = -1) :
    TableBExc.torusAct τ p (simple τ i * simple τ j) (Pi.single j 1 : Fin τ.rank → ZMod p) ≠
      Pi.single j 1 := by
  rw [ggNEE_torusAct_simple_mul_single_adj τ h]
  intro hcon
  have hc := congrFun hcon i
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
    neg_zero, zero_sub] at hc
  exact one_ne_zero (neg_eq_zero.mp hc)

theorem ggNEE_torusAct_simple_mul_single_orth_ne (τ : Tag) {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {i j : Fin τ.rank} (h : τ.cartan j i = 0) :
    TableBExc.torusAct τ p (simple τ i * simple τ j) (Pi.single i 1 : Fin τ.rank → ZMod p) ≠
      Pi.single i 1 := by
  rw [ggNEE_torusAct_simple_mul_single_orth τ h]
  intro hcon
  have hc := congrFun hcon i
  simp only [Pi.neg_apply, Pi.single_eq_same] at hc
  have h2 : (2 : ZMod p) = 0 := by
    have hh := congrArg (fun t : ZMod p => t + 1) hc
    rw [neg_add_cancel, one_add_one_eq_two] at hh
    exact hh.symm
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast hzero
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  exact h2ne h2

theorem ggNEE_coxeterMatrix_eq_three_of_cartan {τ : Tag} {i j : Fin τ.rank} (hij : i ≠ j)
    (hi : τ.cartan i j = -1) (hj : τ.cartan j i = -1) :
    (coxeterMatrix (isFiniteType_cartan τ)) i j = 3 := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    hij, hi, hj]
  norm_num

theorem ggNEE_coxeterMatrix_eq_two_of_cartan {τ : Tag} {i j : Fin τ.rank} (hij : i ≠ j)
    (hi : τ.cartan i j = 0) (hj : τ.cartan j i = 0) :
    (coxeterMatrix (isFiniteType_cartan τ)) i j = 2 := by
  simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
    hij, hi, hj]
  norm_num

theorem ggNEE_conjAut_pair_pow_apply {τ : Tag} {p : ℕ} [NeZero p] {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A ≃* Multiplicative (Fin τ.rank → ZMod p)}
    {ρ : Fin τ.rank → MulAut A}
    (hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a))) :
    ∀ (n : ℕ) (i j : Fin τ.rank) (a : A),
      Multiplicative.toAdd (Φ (((ρ i * ρ j) ^ n) a)) =
        TableBExc.torusAct τ p ((simple τ i * simple τ j) ^ n)
          (Multiplicative.toAdd (Φ a)) := by
  intro n
  induction n with
  | zero => intro i j a; simp only [pow_zero, MulAut.one_apply, TableBExc.torusAct_one]
  | succ n ih =>
    intro i j a
    have hL : ((ρ i * ρ j) ^ (n + 1)) a = ((ρ i * ρ j) ^ n) ((ρ i * ρ j) a) := by
      rw [pow_succ, MulAut.mul_apply]
    have h2 : Multiplicative.toAdd (Φ ((ρ i * ρ j) a)) =
        TableBExc.torusAct τ p (simple τ i * simple τ j) (Multiplicative.toAdd (Φ a)) := by
      rw [MulAut.mul_apply, hρ, hρ, TableBExc.torusAct_mul]
    rw [hL, ih, h2, ← TableBExc.torusAct_mul, ← pow_succ]

theorem ggNEE_pair_pow_eq_one {τ : Tag} {p : ℕ} [NeZero p] {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A ≃* Multiplicative (Fin τ.rank → ZMod p)}
    {ρ : Fin τ.rank → MulAut A}
    (hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)))
    {i j : Fin τ.rank} {n : ℕ} (h : (simple τ i * simple τ j) ^ n = 1) :
    (ρ i * ρ j) ^ n = 1 := by
  refine MulEquiv.ext fun a => ?_
  apply Φ.injective
  apply Multiplicative.toAdd.injective
  rw [ggNEE_conjAut_pair_pow_apply hρ n i j a, h, TableBExc.torusAct_one, MulAut.one_apply]

theorem ggNEE_pair_ne_one_of_torusAct_ne {τ : Tag} {p : ℕ} [NeZero p] {L' : Type} [Group L']
    {A : Subgroup (MulAut L')} {Φ : A ≃* Multiplicative (Fin τ.rank → ZMod p)}
    {ρ : Fin τ.rank → MulAut A}
    (hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)))
    {i j : Fin τ.rank} {x : Fin τ.rank → ZMod p}
    (hx : TableBExc.torusAct τ p (simple τ i * simple τ j) x ≠ x) :
    ρ i * ρ j ≠ 1 := by
  intro h1
  apply hx
  obtain ⟨a, ha⟩ := Φ.surjective (Multiplicative.ofAdd x)
  have ha' : Multiplicative.toAdd (Φ a) = x := congrArg Multiplicative.toAdd ha
  have hkey := ggNEE_conjAut_pair_pow_apply hρ 1 i j a
  rw [pow_one, h1, MulAut.one_apply, ha'] at hkey
  exact hkey.symm

theorem ggNEE_torusFork_of_weyl {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    (hsc : GGTorusSelfCent p A) (Φ : A ≃* Multiplicative (Fin τ.rank → ZMod p))
    (w : Fin τ.rank → L') (hw : ∀ i, GGTorusWeylElt p A (w i))
    (hact : ∀ i (a b : A), (b : MulAut L') = MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ →
      Multiplicative.toAdd (Φ b) =
        TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a))) :
    GGTorusFork p A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hN : ∀ i, MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torusWeylElt hsc (hw i)
  let ρ : Fin τ.rank → MulAut ↥A := fun i => ggConjAut A (hN i)
  have hρ : ∀ i (a : A), Multiplicative.toAdd (Φ (ρ i a)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) :=
    fun i a => hact i a (ρ i a) (ggConjAut_apply A (hN i) a)
  have hρsq : ∀ i, ρ i ^ 2 = 1 := fun i => by
    refine MulEquiv.ext fun a => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [pow_two, MulAut.mul_apply, hρ, hρ, torusAct_simple_involutive, MulAut.one_apply]
  have hρfix : ∀ i, Nat.card {a : A // ρ i a = a} * p = Nat.card A := fun i => by
    have hcardA : Nat.card A = p ^ τ.rank := by
      rw [Nat.card_congr Φ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have hcardFix : Nat.card {a : A // ρ i a = a} = Nat.card
        {x : Fin τ.rank → ZMod p // TableBExc.torusAct τ p (simple τ i) x = x} := by
      refine Nat.card_congr (Equiv.subtypeEquiv (Φ.toEquiv.trans Multiplicative.toAdd) ?_)
      intro a
      change ρ i a = a ↔ TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ a)) =
        Multiplicative.toAdd (Φ a)
      rw [← hρ]
      constructor
      · intro hh; rw [hh]
      · intro hh; exact Φ.injective (Multiplicative.toAdd.injective hh)
    rw [hcardFix, card_fix_torusAct_simple τ hp2 i, hcardA]
  have hρmem : ∀ i, ρ i ∈ ggTorusReflSet p A := fun i =>
    ⟨w i, hN i, hw i, rfl, hρsq i, hρfix i⟩
  have fork_of_star : ∀ (c l1 l2 l3 : Fin τ.rank),
      (coxeterMatrix (isFiniteType_cartan τ)) c l1 = 3 →
      (coxeterMatrix (isFiniteType_cartan τ)) c l2 = 3 →
      (coxeterMatrix (isFiniteType_cartan τ)) c l3 = 3 →
      (coxeterMatrix (isFiniteType_cartan τ)) l1 l2 = 2 →
      (coxeterMatrix (isFiniteType_cartan τ)) l1 l3 = 2 →
      (coxeterMatrix (isFiniteType_cartan τ)) l2 l3 = 2 →
      τ.cartan c l1 = -1 → τ.cartan c l2 = -1 → τ.cartan c l3 = -1 →
      τ.cartan l2 l1 = 0 → τ.cartan l3 l1 = 0 → τ.cartan l3 l2 = 0 →
      c ≠ l1 → c ≠ l2 → c ≠ l3 → l1 ≠ l2 → l1 ≠ l3 → l2 ≠ l3 →
      GGTorusFork p A := by
    intro c l1 l2 l3 hM1 hM2 hM3 hM12 hM13 hM23 hc1 hc2 hc3 h12 h13 h23
      hcl1 hcl2 hcl3 hl12 hl13 hl23
    have hpow1 : (simple τ c * simple τ l1) ^ 3 = 1 := by
      have h := (coxeterSystem τ).simple_mul_simple_pow c l1
      rwa [hM1] at h
    have hpow2 : (simple τ c * simple τ l2) ^ 3 = 1 := by
      have h := (coxeterSystem τ).simple_mul_simple_pow c l2
      rwa [hM2] at h
    have hpow3 : (simple τ c * simple τ l3) ^ 3 = 1 := by
      have h := (coxeterSystem τ).simple_mul_simple_pow c l3
      rwa [hM3] at h
    have hpow12 : (simple τ l1 * simple τ l2) ^ 2 = 1 := by
      have h := (coxeterSystem τ).simple_mul_simple_pow l1 l2
      rwa [hM12] at h
    have hpow13 : (simple τ l1 * simple τ l3) ^ 2 = 1 := by
      have h := (coxeterSystem τ).simple_mul_simple_pow l1 l3
      rwa [hM13] at h
    have hpow23 : (simple τ l2 * simple τ l3) ^ 2 = 1 := by
      have h := (coxeterSystem τ).simple_mul_simple_pow l2 l3
      rwa [hM23] at h
    refine ⟨ρ c, hρmem c, ρ l1, hρmem l1, ρ l2, hρmem l2, ρ l3, hρmem l3,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ hpow1)
        (ggNEE_pair_ne_one_of_torusAct_ne hρ (ggNEE_torusAct_simple_mul_single_adj_ne τ hcl1 hc1))
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ hpow2)
        (ggNEE_pair_ne_one_of_torusAct_ne hρ (ggNEE_torusAct_simple_mul_single_adj_ne τ hcl2 hc2))
    · exact orderOf_eq_prime (p := 3) (ggNEE_pair_pow_eq_one hρ hpow3)
        (ggNEE_pair_ne_one_of_torusAct_ne hρ (ggNEE_torusAct_simple_mul_single_adj_ne τ hcl3 hc3))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ hpow12)
        (ggNEE_pair_ne_one_of_torusAct_ne hρ (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 h12))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ hpow13)
        (ggNEE_pair_ne_one_of_torusAct_ne hρ (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 h13))
    · exact orderOf_eq_prime (p := 2) (ggNEE_pair_pow_eq_one hρ hpow23)
        (ggNEE_pair_ne_one_of_torusAct_ne hρ (ggNEE_torusAct_simple_mul_single_orth_ne τ hp2 h23))
  rcases hτ with rfl | rfl | rfl
  ·
    refine fork_of_star ⟨3, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    all_goals decide
  ·
    refine fork_of_star ⟨3, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    all_goals decide
  ·
    refine fork_of_star ⟨3, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_three_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    · exact ggNEE_coxeterMatrix_eq_two_of_cartan (by decide) (by decide) (by decide)
    all_goals decide

theorem ggNEE_torusFork_of_weylModel {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L'] [Finite L'] {A : Subgroup (MulAut L')}
    (hsc : GGTorusSelfCent p A) (h : GGExcPlusWeylModel τ p A) : GGTorusFork p A := by
  obtain ⟨Φ, w, hw, hact, -⟩ := h
  exact ggNEE_torusFork_of_weyl (Or.inr hτ) hp hp2 hsc Φ w hw hact

end CFSG.StandardType

end
