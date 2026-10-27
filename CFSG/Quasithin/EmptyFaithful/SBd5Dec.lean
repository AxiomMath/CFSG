module

public import CFSG.Quasithin.EmptyFaithful.R3c2Hat
public import CFSG.Quasithin.EmptyFaithful.S153H30

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace SBd5

section Excl

variable {G : Type} [Group G]

omit [Group G] in
theorem card_alt_eq' {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

omit [Group G] in
theorem card_alt_small' {n : ℕ} (hn : n < 2) : Nat.card (alternatingGroup (Fin n)) = 1 := by
  have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr (by omega)
  have : Subsingleton (alternatingGroup (Fin n)) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_of_subsingleton 1

omit [Group G] in
theorem card_alt_ne_168 {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8) :
    Nat.card (alternatingGroup (Fin n)) ≠ 168 := by
  rw [card_alt_eq' (by omega)]
  interval_cases n <;> decide

theorem card_quot_of_surj_ker' {K : Subgroup G} {H : Type} [Group H] {α : ↥K →* H}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = Nat.card H :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv

theorem card_autOn_dvd_card' (K V : Subgroup G) : Nat.card ↥(autOn K V) ∣ Nat.card ↥K := by
  refine (Subgroup.card_map_dvd (H := K.subgroupOf (Subgroup.normalizer (V : Set G)))
    (conjAct V)).trans ?_
  let f : ↥(K.subgroupOf (Subgroup.normalizer (V : Set G))) →* ↥K :=
    { toFun := fun x => ⟨(x : ↥(Subgroup.normalizer (V : Set G))).1, x.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  exact Subgroup.card_dvd_of_injective f (fun a b hab => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : ↥K => (y : G)) hab)

variable [Finite G]

theorem card_statedSL_three_two :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

omit [Finite G] in
theorem card_quot_of_isLnTwoQuot {K : Subgroup G} (hq : IsLnTwoQuot K 3) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168 := by
  obtain ⟨e⟩ := hq
  rw [Nat.card_congr e.toEquiv, card_statedSL_three_two]

theorem not_five_dvd_of_isLnTwoQuot {K : Subgroup G} (hq : IsLnTwoQuot K 3) :
    ¬ 5 ∣ Nat.card ↥K := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  rw [card_quot_of_isLnTwoQuot hq] at h1
  have hpc : IsPGroup 2 ↥(CFSG.pCore 2 ↥K) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨a, ha⟩ := hpc.exists_card_eq
  rw [ha] at h1
  intro h5
  rw [h1] at h5
  have hp : Nat.Prime 5 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp h5 with h | h
  · omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
    omega

theorem c27_caseG {H R M K V : Subgroup G} (hq : IsLnTwoQuot K 3) (hC : C27Concl H R M K V) :
    IsMSPair (K ⊔ R) R := by
  have h168 := card_quot_of_isLnTwoQuot hq
  have h5 := not_five_dvd_of_isLnTwoQuot hq
  rcases hC.2.2 with ha | hb | hc | hd | he | hf | hg | hh
  · exfalso
    obtain ⟨-, hL | ⟨m, hm, hA⟩⟩ := ha.1
    · obtain ⟨n, hn, F, _, _, hF, α, hα, hker, -⟩ := hL
      have hq' := card_quot_of_surj_ker' hα hker
      rw [h168] at hq'
      have hFc : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
      have hSL := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 2)
        (by norm_num)
      rw [← hq', hFc, show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton] at hSL
      norm_num at hSL
      have hdvd : 2 ^ n ∣ 168 := ⟨(2 ^ n) ^ 2 - 1, hSL⟩
      have hn3 : n ≤ 3 := by
        by_contra hcon
        push Not at hcon
        have := pow_dvd_pow 2 hcon
        have h16 : (2 : ℕ) ^ 4 ∣ 168 := this.trans hdvd
        omega
      interval_cases n <;> omega
    · obtain ⟨α, hα, hker, -⟩ := hA
      have hq' := card_quot_of_surj_ker' hα hker
      rw [h168] at hq'
      by_cases hm2 : 2 ≤ m
      · rw [card_alt_eq' hm2] at hq'
        by_cases hm7 : 7 ≤ m
        · have := Nat.factorial_le hm7
          have h5040 : (7 : ℕ).factorial = 5040 := by decide
          omega
        · push Not at hm7
          interval_cases m <;> revert hq' <;> decide
      · push Not at hm2
        rw [card_alt_small' hm2] at hq'
        omega
  · exfalso
    obtain ⟨n, α, h5', h8, -, ⟨hα, hker, -⟩, -⟩ := hb.1
    have hq' := card_quot_of_surj_ker' hα hker
    rw [h168] at hq'
    exact card_alt_ne_168 h5' h8 hq'.symm
  · exfalso
    have h1080 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1080 := R3c2.card_of_isHat_alt6 hc.1.2.1
    omega
  · exfalso
    obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := hd.1
    have hq' := card_quot_of_surj_ker' hα hker
    rw [h168, card_alt_eq' (by norm_num)] at hq'
    revert hq'; decide
  · exfalso
    rcases he.1 with ⟨-, α, hα, hker, -⟩ | ⟨-, F, _, _, hF, α, hα, hker, -⟩
    · have hq' := card_quot_of_surj_ker' hα hker
      rw [h168, card_alt_eq' (by norm_num)] at hq'
      revert hq'; decide
    · have hq' := card_quot_of_surj_ker' hα hker
      rw [h168, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
        Nat.card_eq_fintype_card (α := F), hF] at hq'
      revert hq'
      rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
      norm_num
  · exfalso
    have h6048 := S153H.card_psu_three_three hf.1.2.1
    omega
  · exact hg.2.2
  · exfalso
    obtain ⟨hSL, -⟩ := hh
    have h5' : ∀ m : ℕ, Nat.card ↥(autOn K V) = m → 5 ∣ m → False := fun m hm h =>
      h5 ((hm ▸ h : 5 ∣ Nat.card ↥(autOn K V)).trans (card_autOn_dvd_card' K V))
    rcases hSL with h4 | h5''
    · obtain ⟨e⟩ := h4
      have h1 : Nat.card ↥(autOn K V) =
          Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 4 (ZMod 2)).toEquiv]
      have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 2) (n := 4)
        (by norm_num)
      rw [Nat.card_zmod] at h2
      exact h5' _ (h1.trans h2) (by decide)
    · obtain ⟨e⟩ := h5''
      have h1 : Nat.card ↥(autOn K V) =
          Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr (specialLinearGroupEquivStatedSL 5 (ZMod 2)).toEquiv]
      have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := ZMod 2) (n := 5)
        (by norm_num)
      rw [Nat.card_zmod] at h2
      exact h5' _ (h1.trans h2) (by decide)

end Excl

section Apply

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_cComp_sup' {K S H : Subgroup G} (hK : K ∈ cComp H)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) : K ∈ cComp (K ⊔ S) := by
  obtain ⟨hne, hperf, hsub, hmin⟩ := hK
  refine ⟨hne, hperf, ?_, fun K' hK'K hK'ne hK'perf hK'sub => ?_⟩
  · exact IsSubnormal.step le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer
      (_root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hSK)) (IsSubnormal.refl _)
  · exact hmin K' hK'K hK'ne hK'perf
      (A3.subnormal_trans (A3.subnormal_of_le_of_le hK'sub hK'K.le le_sup_left) hsub)

end Apply

end SBd5

end CFSG.Quasithin
