module

public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearGroup
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open (pCoreOf quasithinGenFitting quasithinG2)
open CFSG.Quasithin CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank

theorem padicValNat_two_pow_mul_odd {a u : ℕ} (hu : Odd u) : padicValNat 2 (2 ^ a * u) = a := by
  have hu0 : u ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hu).elim
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by positivity) hu0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h))]
  rfl

theorem odd_two_pow_sub_one_of_pos {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h1 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  rw [Nat.odd_iff]
  omega

theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  by_contra h0
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [h, show n = 0 by omega, pow_zero] at h1
  exact lt_irrefl _ h1

theorem false_of_b56List {X : Type} [Group X] [Finite X] (h : B56QuasisimpleList X) {m : ℕ}
    (hm : Odd m) (hm' : m ≠ 16383) (hc : Nat.card X = 2 ^ 7 * m) : False := by
  have hv : padicValNat 2 (Nat.card X) = 7 := by rw [hc]; exact padicValNat_two_pow_mul_odd hm
  have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
  rcases h with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | hA6 | hA7 | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | hL4 | hL5
  ·
    have hn := one_le_of_card_field hK
    have hX : Nat.card X = 2 ^ n * (2 ^ (n * 2) - 1) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hK, ← pow_mul]
    have h7 : n = 7 := by
      rw [hX, padicValNat_two_pow_mul_odd (odd_two_pow_sub_one_of_pos (by omega))] at hv
      exact hv
    subst h7
    rw [hc] at hX
    norm_num at hX
    omega
  ·
    have hn := one_le_of_card_field hK
    have hX : Nat.card X = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hK, ← pow_mul, ← pow_mul]
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    have hn := one_le_of_card_field hK
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX : Nat.card X = 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hI,
        Finset.prod_pair (by norm_num), ← pow_mul, ← pow_mul, ← pow_mul]
      norm_num
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    have hn := one_le_of_card_field hK
    have hX : Nat.card X = 2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) := by
      rw [Nat.card_congr e.toEquiv, card_quasithinG2_1527d hK, hK, ← pow_mul, ← pow_mul]
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    obtain ⟨e⟩ := hA6
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num)] at hc
    norm_num [Nat.factorial] at hc
    omega
  ·
    obtain ⟨e⟩ := hA7
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 7 (by norm_num)] at hc
    norm_num [Nat.factorial] at hc
    omega
  ·
    obtain ⟨-, hZ, ⟨e⟩⟩ := hhat
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup1527d 6 (by norm_num), hZ, hc] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    have hdvd : Nat.card X ∣ 12096 := by
      rw [Nat.card_congr e.toEquiv]
      have h1 := Subgroup.card_subgroup_dvd_card
        ((⁅quasithinG2 K, quasithinG2 K⁆).subgroupOf (quasithinG2 K))
      have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K :=
        Subgroup.commutator_le.mpr fun a ha b hb => by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
        card_quasithinG2_1527d (n := 1) (by rw [hK, pow_one]), hK] at h1
      exact h1
    rw [hc] at hdvd
    have h128 : 2 ^ 7 ∣ 12096 := (Dvd.intro m rfl).trans hdvd
    norm_num at h128
  ·
    obtain ⟨e⟩ := hL4
    rw [Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d] at hc
    omega
  ·
    obtain ⟨e⟩ := hL5
    rw [Nat.card_congr e.toEquiv, card_statedSL_five_zmod1527d] at hc
    omega

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_ff_card (h56 : AsB56) (hV : ∀ v : V, v * v = 1)
    {Γ L : Subgroup (MulAut V)} (hQ : G64.IsQuotientOfSQTKCat ↥Γ) (hLΓ : L ≤ Γ)
    (hn : (L.subgroupOf Γ).Normal) (hC : Γ ⊓ Subgroup.centralizer (L : Set (MulAut V)) = ⊥)
    (hq : CFSG.IsQuasisimple ↥L) {m : ℕ} (hm : Odd m) (hm' : m ≠ 16383)
    (hc : Nat.card ↥L = 2 ^ 7 * m) (hoff : ∃ A : Subgroup (MulAut V), IsFFStarOffender Γ A) :
    False := by
  have hZ := FFL.center_eq_bot hLΓ hC
  obtain ⟨hLG, hB53⟩ := FFL.b53Hyp_ffJ hQ hq hZ hC hLΓ hn hoff
  have hL1 : L ≠ ⊥ := by
    intro h
    have : Nontrivial ↥L := FFL.nontrivial_of_isQuasisimple hq
    rw [h] at this
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
  have hG1 : ffJ Γ ≠ ⊥ := fun h => hL1 (le_bot_iff.mp (h ▸ hLG))
  have hΓL := FFL.le_normalizer_of_normal hLΓ hn
  have hdich : ∀ H ≤ ffJ Γ, ffJ Γ ≤ Subgroup.normalizer (H : Set (MulAut V)) → L ≤ H ∨ H = ⊥ :=
    fun H hH hGH => FFL.le_or_eq_bot hq hZ hC (hH.trans (FFL.ffJ_le Γ)) (hLG.trans hGH)
      ((hH.trans (FFL.ffJ_le Γ)).trans hΓL)
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => by rw [sq]; exact hV v
  have hm0 : 1 ≤ m := by rcases hm with ⟨k, rfl⟩; omega
  have hcard6 : 6 < Nat.card ↥L := by rw [hc]; omega
  rcases h56 V hV2 (ffJ Γ) hG1 hB53 with ⟨hqF, -, hlist⟩ | h2 | h3 | h4 | h5
  ·
    have hFL : quasithinGenFitting (ffJ Γ) = L := by
      have hF := quasithinGenFitting_le (ffJ Γ)
      have hGF : ffJ Γ ≤ Subgroup.normalizer (quasithinGenFitting (ffJ Γ) : Set (MulAut V)) :=
        Subgroup.le_normalizer.trans (normalizer_le_normalizer_quasithinGenFitting _)
      rcases hdich _ hF hGF with hLF | hb
      · exact FFL.eq_of_isQuasisimple hq hqF hLF ((hF.trans (FFL.ffJ_le Γ)).trans hΓL)
      · exfalso
        have := FFL.nontrivial_of_isQuasisimple hqF
        rw [hb] at this
        exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
    rw [hFL] at hlist
    exact false_of_b56List hlist hm hm' hc
  · exact FFL.false_of_case2 hLG hcard6 h2
  · exact FFL.false_of_case3 hL1 hdich h3
  · exact FFL.false_of_case4 hcard6 hdich h4
  · exact FFL.false_of_case5 hL1 hdich h5

theorem padicValNat_m22 {N : ℕ} (hc : N = 443520 ∨ N = 1330560) : padicValNat 2 N = 7 := by
  rcases hc with rfl | rfl
  · exact padicValNat_two_pow_mul_odd (a := 7) (u := 3465) (by decide)
  · exact padicValNat_two_pow_mul_odd (a := 7) (u := 10395) (by decide)

theorem false_of_d310Two_card {W : Type} [CommGroup W] [Finite W] {T L : Subgroup (MulAut W)}
    {U : Subgroup W} (h : D310Two T L U) (hc : Nat.card L = 443520 ∨ Nat.card L = 1330560) :
    False := by
  have hv := padicValNat_m22 hc
  have hbig : 443520 ≤ Nat.card L := by rcases hc with h | h <;> omega
  obtain ⟨hcases, -, -⟩ := h
  rcases hcases with ⟨n, K, _, _, hK, π, hπ⟩ | ⟨n, K, _, _, hK, π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨α, π, hπ⟩
  ·
    have hn := one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX0 : Nat.card L = Nat.card ↥(StatedSL 3 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [hX0, card_statedSL_three1527d, hK, ← pow_mul, ← pow_mul]
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    have hn := one_le_of_card_field hK
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX0 : Nat.card L = Nat.card ↥(StatedSp 2 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    have hX : Nat.card L = 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [hX0, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK, hI,
        Finset.prod_pair (by norm_num), ← pow_mul, ← pow_mul, ← pow_mul]
      norm_num
    rw [hX, padicValNat_two_pow_mul_odd ((odd_two_pow_sub_one_of_pos (by omega)).mul
      (odd_two_pow_sub_one_of_pos (by omega)))] at hv
    omega
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 6))) π hπ.1
    rw [card_alternatingGroup1527d 6 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    omega
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(StatedSL 4 K)) π hπ.1
    rw [card_statedSL1527d (d := 4) (by norm_num), hK] at h1
    norm_num [Finset.prod_Icc_succ_top] at h1
    omega
  ·
    have hinj := G64.RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) hπ
    have hX : Nat.card L = Nat.card ↥(StatedSL 5 K) :=
      (Nat.card_congr (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).toEquiv).symm
    rw [hX, card_statedSL1527d (d := 5) (by norm_num), hK] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
  ·
    have h1 := Nat.card_le_card_of_surjective (α := ↥(alternatingGroup (Fin 7))) π hπ.1
    have h2 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
      rw [card_alternatingGroup1527d 7 (by norm_num)]
      norm_num [Nat.factorial]
    omega

end CFSG.Quasithin.H13.L32A.C
