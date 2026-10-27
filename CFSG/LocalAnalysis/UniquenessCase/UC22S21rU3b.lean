module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Standing22
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ta
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rN
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Quasithin (IsSylowIn)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21ru3b_exists_cov {Y T : Subgroup G} (hTY : T ≤ Y) (hsol : Group.IsSolvable ↥Y)
    (hT2 : IsPGroup 2 ↥T) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpY : p ∣ Nat.card Y) :
    ∃ X : Subgroup G, T ⋖ X ∧ X ≤ Y ∧ ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p := by
  classical
  let π : Set Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨p, hp⟩}
  have hpπ : (⟨p, hp⟩ : Nat.Primes) ∈ π := Or.inr rfl
  set U : Subgroup ↥Y := T.subgroupOf Y with hU
  have hU2 : IsPGroup 2 ↥U := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTY).symm
  have hUπ : CFSG.IsPiSubgroup π U := by
    intro q hq
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    rw [hn] at hq
    exact Or.inl (Subtype.ext
      ((Nat.prime_dvd_prime_iff_eq q.2 Nat.prime_two).1 (q.2.dvd_of_dvd_pow hq)))
  obtain ⟨H, hH, hUH⟩ := CFSG.SolvableHall.solvable_hall_containment hsol π U hUπ
  set Y' : Subgroup G := H.map Y.subtype with hY'
  have hcardY' : Nat.card Y' = Nat.card H := Subgroup.card_map_of_injective Y.subtype_injective
  have hpH : p ∣ Nat.card H := by
    have h1 : p ∣ Nat.card H * H.index := by
      rw [Subgroup.card_mul_index]
      exact hpY
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · exact h
    · exact absurd hpπ (hH.p_in_pi_of_p_dvd_index ⟨p, hp⟩ h)
  have hTY' : T ≤ Y' := fun t ht => ⟨⟨t, hTY ht⟩, hUH ht, rfl⟩
  have hY'Y : Y' ≤ Y := Subgroup.map_subtype_le H
  have hlt : T < Y' := by
    refine lt_of_le_of_ne hTY' fun heq => ?_
    obtain ⟨n, hn⟩ := hT2.exists_card_eq
    have h1 : p ∣ Nat.card T := by rw [heq, hcardY']; exact hpH
    rw [hn] at h1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  haveI : WellFoundedLT (Subgroup G) := Finite.to_wellFoundedLT
  obtain ⟨X, hcov, hXY'⟩ := exists_covBy_le_of_lt hlt
  refine ⟨X, hcov, hXY'.trans hY'Y, fun q hq hqX => ?_⟩
  have hqY' : q ∣ Nat.card H := hcardY' ▸ hqX.trans (Subgroup.card_dvd_of_le hXY')
  rcases hH.p_in_pi_of_p_dvd_card ⟨q, hq⟩ hqY' with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem uc22s21ru3b_dvd_card {X T : Subgroup G} (hTX : IsSylowIn 2 T X) (hcov : T ⋖ X) {p : ℕ}
    (hpi : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p) : p ∣ Nat.card X := by
  have hne : T.relIndex X ≠ 1 := fun h =>
    hcov.lt.not_ge (Subgroup.relIndex_eq_one.1 h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne
  have hq2 : q ≠ 2 := fun h => hTX.not_dvd_relIndex (h ▸ hqd)
  rcases hpi q hq (hqd.trans (Subgroup.relIndex_dvd_card T X)) with h | h
  · exact absurd h hq2
  · exact h ▸ hqd.trans (Subgroup.relIndex_dvd_card T X)

theorem uc22s21ru3b_false_of_le (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {p : ℕ} (hp : p ∈ D.sig)
    (hsp : IsStronglyPEmbedded p D.M) {X H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hTX : D.T ≤ X) (hXM : X ≤ D.M) (hsol : Group.IsSolvable ↥X)
    (hpi : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p) (hpX : p ∣ Nat.card X)
    (hXH : X ≤ H) : False := by
  classical
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI := hsol
  by_cases hnc : ∃ Q : Subgroup G, Q ≤ X ∧ IsPGroup p ↥Q ∧ ¬ IsCyclic ↥Q
  · obtain ⟨Q, hQX, hQp, hQnc⟩ := hnc
    exact uc22s21rn_not_le_of_uniqueMax D hH (st.r6_1 p hp Q (hQX.trans hXM) hQp hQnc)
      (hQX.trans hXH)
  push Not at hnc
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hpX
  have hAorder : orderOf (a : G) = p := by rw [Subgroup.orderOf_coe]; exact ha
  have hAcard : Nat.card (Subgroup.zpowers (a : G)) = p := by rw [Nat.card_zpowers, hAorder]
  have hAX : Subgroup.zpowers (a : G) ≤ X := Subgroup.zpowers_le.2 a.2
  have hAp : IsPGroup p ↥(Subgroup.zpowers (a : G)) :=
    IsPGroup.of_card (n := 1) (by rw [hAcard, pow_one])
  have hA1 : Subgroup.zpowers (a : G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hAcard
    exact hpp.ne_one hAcard.symm
  have hAU : Subgroup.zpowers (a : G) ∈ uniqueSet D.M :=
    uc22p22r_mem_uniqueSet_of_sp D hpp hsp (hAX.trans hXM) hAp hA1
  have hZX : Subgroup.zpowers (a : G) ⊔ D.T ≤ X := sup_le hAX hTX
  have hsolZ : IsSolvable ↥(Subgroup.zpowers (a : G) ⊔ D.T) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hZX)
  have hZpi : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(Subgroup.zpowers (a : G) ⊔ D.T) → q = 2 ∨ q = p :=
    fun q hq hqZ => hpi q hq (hqZ.trans (Subgroup.card_dvd_of_le hZX))
  obtain ⟨P₀⟩ : Nonempty (Sylow p ↥(Subgroup.zpowers (a : G) ⊔ D.T)) := inferInstance
  have hAoddZ : (P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)).map
      (Subgroup.zpowers (a : G) ⊔ D.T).subtype ≤ Subgroup.zpowers (a : G) ⊔ D.T :=
    Subgroup.map_subtype_le _
  have hAoddp : IsPGroup p ↥((P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)).map
      (Subgroup.zpowers (a : G) ⊔ D.T).subtype) := P₀.isPGroup'.map _
  have hhall : IsHallOddIn ((P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)).map
      (Subgroup.zpowers (a : G) ⊔ D.T).subtype) (Subgroup.zpowers (a : G) ⊔ D.T) := by
    refine ⟨hAoddZ, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := hAoddp.exists_card_eq
      rw [hn]
      exact (hpp.odd_of_ne_two hp2).pow
    · have hsub : ((P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)).map
          (Subgroup.zpowers (a : G) ⊔ D.T).subtype).subgroupOf (Subgroup.zpowers (a : G) ⊔ D.T) =
          (P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)) :=
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
      rw [hsub]
      have hne0 : (P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)).index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite
      refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hne0 fun {d} hd hdd => ?_⟩
      rcases hZpi d hd (hdd.trans (Subgroup.index_dvd_card _)) with h | h
      · exact h
      · exact absurd (h ▸ hdd) P₀.not_dvd_index
  have hcomm : IsMulCommutative ↥((P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)).map
      (Subgroup.zpowers (a : G) ⊔ D.T).subtype) := by
    haveI : IsCyclic ↥((P₀ : Subgroup ↥(Subgroup.zpowers (a : G) ⊔ D.T)).map
      (Subgroup.zpowers (a : G) ⊔ D.T).subtype) := hnc _ (hAoddZ.trans hZX) hAoddp
    infer_instance
  have hrank : ∀ q ∈ piSet (Subgroup.zpowers (a : G) ⊔ D.T), q ≠ 2 →
      CFSG.Open.pRank q (Subgroup.zpowers (a : G) ⊔ D.T) ≤ 2 := by
    rintro q ⟨hq, hqZ⟩ hq2
    have hqp : q = p := (hZpi q hq hqZ).resolve_left hq2
    subst hqp
    refine CFSG.SectionRank.pRank_le hq.one_lt fun E hEZ hE => ?_
    have hcyc : IsCyclic ↥E := hnc E (hEZ.trans hZX) hE.isPGroup
    have hexp : ∀ g : ↥E, g ^ q = 1 := fun g => Subtype.ext (by simpa using hE.2 g.1 g.2)
    have hdvd : Nat.card ↥E ∣ q := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
    exact (Nat.le_of_dvd hq.pos hdvd).trans (Nat.le_self_pow (by norm_num) q)
  have hM := (h211 h1930 c (Subgroup.zpowers (a : G)) (by rw [hAcard]; exact hpp)
    (by rw [hAcard]; exact hp2) hsolZ ⟨_, hhall, hcomm⟩ hrank hAU).1
  exact uc22s21rn_not_le_of_uniqueMax D hH hM (hZX.trans hXH)

theorem uc22s21ru3b_not_dvd_card (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G}
    (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {p : ℕ} (hp : p ∈ D.sig) (hsp : IsStronglyPEmbedded p D.M) {Y : Subgroup G}
    (hTY : D.T ≤ Y) (hYM : Y ≤ D.M) (hsol : Group.IsSolvable ↥Y) : ¬ p ∣ Nat.card Y := by
  intro hpY
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  obtain ⟨X, hcov, hXY, hpi⟩ := uc22s21ru3b_exists_cov hTY hsol D.sylowM.isPGroup hpp hp2 hpY
  have hTX : D.T ≤ X := hcov.lt.le
  have hXM : X ≤ D.M := hXY.trans hYM
  haveI := hsol
  have hsolX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXY)
  have hTXs : IsSylowIn 2 D.T X := uc22p22ta_isSylowIn D hTX
  have hpX : p ∣ Nat.card X := uc22s21ru3b_dvd_card hTXs hcov hpi
  rcases uc22s21ru3a_le_or_le hTXs hcov hsolX hH₁.1 hH₂.1 (hfX X hXM hTX) with h | h
  · exact uc22s21ru3b_false_of_le D Ch st h211 h1930 c hp hsp hH₁ hTX hXM hsolX hpi hpX h
  · exact uc22s21ru3b_false_of_le D Ch st h211 h1930 c hp hsp hH₂ hTX hXM hsolX hpi hpX h

end CFSG.LocalAnalysis.UniquenessCase.UC22
