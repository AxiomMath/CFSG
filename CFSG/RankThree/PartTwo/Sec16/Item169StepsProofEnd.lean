module

public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1519
public import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem step169End38NeFive :
    ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → ∀ (d : G) (p : ℕ) (X U : Subgroup G),
      p.Prime → 3 < p → p ≠ 5 → Nat.card X = p → X ≤ thetaCen ({d} : Set G) →
        U ≤ thetaCen ({d} : Set G) → IsPGroup 2 U → U ≠ ⊥ → U = ⁅U, X⁆ →
          CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥ → False := by
  intro G _ _ hG d p X U hp hp3 hp5 hXp hXθ hUθ hU2 hU1 hUX hO2
  set Θ := thetaCen ({d} : Set G) with hΘ
  obtain ⟨hcs, -, hc3, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer ({d} : Set G))) Nat.prime_three
  have hs : Group.IsSolvable ↥Θ := by
    let e := (aschbacherSolvableCore 3 ↥(Subgroup.centralizer ({d} : Set G))).equivMapOfInjective
      _ (Subgroup.subtype_injective _)
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have h3 : ¬ 3 ∣ Nat.card Θ := by
    change ¬ 3 ∣ Nat.card ((aschbacherSolvableCore 3
      ↥(Subgroup.centralizer ({d} : Set G))).map (Subgroup.centralizer ({d} : Set G)).subtype)
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hc3
  obtain ⟨r, hr, hr3, hrU⟩ := exists_prime_not_le_centralizer_pCore hs h3
    (pCore_two_thetaCen_eq_bot hO2) hUθ hU2 hU1
  have : Fact r.Prime := ⟨hr⟩
  set Q := (CFSG.pCore r ↥Θ).map Θ.subtype with hQ
  have hQr : IsPGroup r Q := (CFSG.pCore_isPGroup (p := r) (G := ↥Θ)).map _
  have hΘQ : Θ ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hUX.symm.le
  exact false_of_commutator_action hG.localRank_lt hp hp3 hp5 hr hr3 hXp hU2 hUX.symm hXU hQr
    (hUθ.trans hΘQ) (hXθ.trans hΘQ) hrU

@[expose] noncomputable def Para1619At : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) →
      (∀ Y ∈ scriptY3 A (lB A), Group.IsSolvable ↥Y) →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSU 3 2 3) →
      ∀ p : ℕ, p.Prime → 3 < p → (2 : ZMod p) ^ n = Sec15.sign1519 n p →
        ∃ (b : G) (P : Subgroup G), Data1619 A c L b n p P

@[expose] noncomputable def Para1619Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) →
      (∀ Y ∈ scriptY3 A (lB A), Group.IsSolvable ↥Y) →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSU 3 2 3) →
        ∃ (b : G) (p : ℕ) (P : Subgroup G), Data1619 A c L b n p P ∧ (p = 5 → n = 4)

theorem para1619_of_five (h : Para1619Five) : Para1619 := by
  intro G _ _ A c L hc n hn h34 hsolv hU38
  obtain ⟨b, p, P, hD, -⟩ := h G A c L hc n hn h34 hsolv hU38
  exact ⟨b, p, P, hD⟩

namespace Proof169End

open CFSG.Timmesfeld

theorem ne_three_of_isZ3LThreeTwo {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {n : ℕ} (hn : IsZ3LThreeTwo A c L n)
    (hU38 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSU 3 2 3)) : n ≠ 3 := by
  rintro rfl
  rcases hn.2.1 with ⟨h3, -⟩ | ⟨-, ⟨φ⟩⟩
  · norm_num at h3
  · exact hU38.false φ

theorem exists_prime_ne_five {n : ℕ} (hn : 5 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ≠ 5 ∧ (2 : ZMod p) ^ n = Sec15.sign1519 n p := by
  rcases Nat.even_or_odd n with hev | hodd
  · by_cases h6 : n = 6
    · subst h6
      refine ⟨7, by norm_num, by norm_num, by norm_num, ?_⟩
      rw [Sec15.sign1519_of_even (by decide)]
      decide
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := n) (by omega) h6
    have hpp := hp.1
    refine ⟨p, hpp, Proof1514.three_lt_of_isPrimitivePrimeDivisor hp (by omega), ?_, ?_⟩
    · rintro rfl
      have hn4 : 4 < n := by obtain ⟨k, hk⟩ := hev; omega
      exact hp.2.2 4 (by norm_num) hn4 (by norm_num)
    · rw [Sec15.sign1519_of_even hev]
      exact (Bang.dvd_two_pow_sub_one_iff _).mp hp.2.1
  · obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
    have hpp := hp.1
    have : Fact p.Prime := ⟨hpp⟩
    have hk : (2 : ZMod p) ^ (2 * n) = 1 := (Bang.dvd_two_pow_sub_one_iff _).mp hp.2.1
    have hm1 : (2 : ZMod p) ^ n ≠ 1 := fun h =>
      hp.2.2 n (by omega) (by omega) ((Bang.dvd_two_pow_sub_one_iff n).mpr h)
    have hneg : (2 : ZMod p) ^ n = -1 := by
      have hsq : (2 : ZMod p) ^ n * (2 : ZMod p) ^ n = 1 := by
        rw [← pow_add, ← two_mul, hk]
      exact (mul_self_eq_one_iff.mp hsq).resolve_left hm1
    refine ⟨p, hpp, Proof1514.three_lt_of_isPrimitivePrimeDivisor hp (by omega), ?_, ?_⟩
    · rintro rfl
      exact hp.2.2 4 (by norm_num) (by omega) (by norm_num)
    · rw [Sec15.sign1519_of_odd hodd]
      exact hneg

theorem two_pow_four_five : (2 : ZMod 5) ^ 4 = Sec15.sign1519 4 5 := by
  rw [Sec15.sign1519_of_even (by decide)]
  decide

end Proof169End

open Proof169End in
theorem para1619Five_of_at (h : Para1619At) : Para1619Five := by
  intro G _ _ A c L hc n hn h34 hsolv hU38
  have h2 := two_lt_of_isZ3LThreeTwo hc.toSec13Data hn h34
  have h3 := ne_three_of_isZ3LThreeTwo hn hU38
  by_cases h4 : n = 4
  · subst h4
    obtain ⟨b, P, hD⟩ := h G A c L hc 4 hn h34 hsolv hU38 5 (by norm_num) (by norm_num)
      two_pow_four_five
    exact ⟨b, 5, P, hD, fun _ => rfl⟩
  · obtain ⟨p, hp, hp3, hp5, hpn⟩ := exists_prime_ne_five (n := n) (by omega)
    obtain ⟨b, P, hD⟩ := h G A c L hc n hn h34 hsolv hU38 p hp hp3 hpn
    exact ⟨b, p, P, hD, fun h5 => absurd h5 hp5⟩

@[expose] noncomputable def Step169EndFiveL316 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → ∀ (b : G) (P : Subgroup G), Data1619 A c L b 4 5 P →
      ∀ (m : ℕ) (V X : Subgroup G), Data1623 L b m 5 P V X →
      ∀ d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers b, d ∉ Subgroup.zpowers c →
      ∀ U : Subgroup G, U ≤ Subgroup.centralizer ({d} : Set G) → IsPGroup 2 U → U ≠ ⊥ →
        U = ⁅U, X⁆ → X ≤ thetaCen ({d} : Set G) → U ≤ thetaCen ({d} : Set G) →
          CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({d} : Set G)) = ⊥ → False

variable {G : Type} [Group G] [Finite G]

end CFSG.RankThree.PartTwo.Sec16
