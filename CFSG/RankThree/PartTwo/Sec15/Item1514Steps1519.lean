module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsTools
public import CFSG.Timmesfeld.Orders.Bang
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1514

theorem two_pow_mod_three_of_even {m : ℕ} (hm : Even m) : 2 ^ m % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {m : ℕ} (hm : Odd m) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end Proof1514

open Proof1514

theorem sign1519_of_even {m : ℕ} (hm : Even m) (r : ℕ) : sign1519 m r = 1 := by
  simp [sign1519, two_pow_mod_three_of_even hm]

theorem sign1519_of_odd {m : ℕ} (hm : Odd m) (r : ℕ) : sign1519 m r = -1 := by
  simp [sign1519, two_pow_mod_three_of_odd hm]

namespace Proof1514

open CFSG.Timmesfeld in
theorem three_lt_of_isPrimitivePrimeDivisor {p k : ℕ} (hp : IsPrimitivePrimeDivisor p k)
    (hk : 3 ≤ k) : 3 < p := by
  have h2 : p ≠ 2 := hp.ne_two (by omega)
  have h3 : p ≠ 3 := by
    rintro rfl
    exact hp.2.2 2 (by norm_num) (by omega) (by norm_num)
  have := hp.1.two_le
  omega

end Proof1514

open CFSG.Timmesfeld in
theorem exists_isChoice1519 {m : ℕ} (hm : 4 ≤ m) : ∃ p, IsChoice1519 m p ∧ 3 < p := by
  by_cases hm4 : m % 4 = 2
  ·
    obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := m / 2) (by omega) (by omega)
    have hpp := hp.1
    have hk : (2 : ZMod p) ^ (m / 2) = 1 := (Bang.dvd_two_pow_sub_one_iff _).mp hp.2.1
    have hev : Even m := ⟨m / 2, by omega⟩
    refine ⟨p, ⟨hpp, ?_, Or.inl ⟨m / 2, by omega, hm4, hk, fun i hi hik h2i => ?_⟩⟩,
      three_lt_of_isPrimitivePrimeDivisor hp (by omega)⟩
    · rw [sign1519_of_even hev, show m = m / 2 * 2 by omega, pow_mul, hk, one_pow]
    · have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hi (by omega)
      exact hp.2.2 i hi0 hik ((Bang.dvd_two_pow_sub_one_iff i).mpr h2i)
  · rcases Nat.even_or_odd m with hev | hodd
    ·
      obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := m) (by omega) (by omega)
      have hpp := hp.1
      have hk : (2 : ZMod p) ^ m = 1 := (Bang.dvd_two_pow_sub_one_iff _).mp hp.2.1
      refine ⟨p, ⟨hpp, by rw [sign1519_of_even hev]; exact hk,
        Or.inr ⟨hm4, fun i hi him h2i => ?_⟩⟩, three_lt_of_isPrimitivePrimeDivisor hp (by omega)⟩
      rw [sign1519_of_even hev] at h2i
      have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hi (by omega)
      exact hp.2.2 i hi0 him ((Bang.dvd_two_pow_sub_one_iff i).mpr h2i)
    ·
      obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 2 * m) (by omega) (by omega)
      have hpp := hp.1
      have : Fact p.Prime := ⟨hpp⟩
      have hk : (2 : ZMod p) ^ (2 * m) = 1 := (Bang.dvd_two_pow_sub_one_iff _).mp hp.2.1
      have hm1 : (2 : ZMod p) ^ m ≠ 1 := fun h =>
        hp.2.2 m (by omega) (by omega) ((Bang.dvd_two_pow_sub_one_iff m).mpr h)
      have hneg : (2 : ZMod p) ^ m = -1 := by
        have hsq : (2 : ZMod p) ^ m * (2 : ZMod p) ^ m = 1 := by
          rw [← pow_add, ← two_mul, hk]
        exact (mul_self_eq_one_iff.mp hsq).resolve_left hm1
      refine ⟨p, ⟨hpp, by rw [sign1519_of_odd hodd]; exact hneg,
        Or.inr ⟨hm4, fun i hi him h2i => ?_⟩⟩, three_lt_of_isPrimitivePrimeDivisor hp (by omega)⟩
      rw [sign1519_of_odd hodd] at h2i
      have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hi (by omega)
      have h2 : (2 : ZMod p) ^ (2 * i) = 1 := by
        rw [two_mul, pow_add, h2i]
        norm_num
      exact hp.2.2 (2 * i) (by omega) (by omega) ((Bang.dvd_two_pow_sub_one_iff _).mpr h2)

@[expose] noncomputable def Step1519Small : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ m : ℕ, Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m → m ≠ 2 ∧ m ≠ 3

@[expose] noncomputable def Step1519P : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ m p : ℕ, Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m →
        IsChoice1519 m p → 3 < p →
        ∃ P : Subgroup G, CFSG.Assembly.IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
          P ∈ scriptQPi A (lB A) L (piOf p)

@[expose] noncomputable def Step1519Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y →
      ∀ m p : ℕ, Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 m →
        IsChoice1519 m p → 3 < p →
        ∀ Y₀ ∈ scriptY0 A (lB A),
          ∀ R ∈ scriptQPi A (lB A) (Subgroup.normalizer (Y₀ : Set G)) (piOf p),
            (R : Set G) ⊆ Late.sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
              (CFSG.Open.pCoreOf 2 Y₀)

variable {G : Type} [Group G] [Finite G]

namespace Proof1514

theorem ne_one_of_isoLThreePi_two {K : Subgroup G} {a : G} (hK : K ∈ thetaComponentsAt 3 a)
    {m : ℕ} (hiso : Sec4.IsoLThreePi (K ⧸ aschbacherSolvableCore 3 K) 2 m) : m ≠ 1 := by
  rintro rfl
  rcases hiso with ⟨h1, -⟩ | ⟨-, ⟨φ⟩⟩
  · norm_num at h1
  · have hq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
      Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
    have := isSolvable_projSU_two
    have hsol : Group.IsSolvable (K ⧸ aschbacherSolvableCore 3 K) :=
      Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    have : Nontrivial (K ⧸ aschbacherSolvableCore 3 K) := by
      obtain ⟨x, y, hxy⟩ := hq.2.2
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      apply hxy
      have : Subsingleton ((K ⧸ aschbacherSolvableCore 3 K) ⧸
          Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) :=
        QuotientGroup.mk_surjective.subsingleton
      exact Subsingleton.elim _ _
    have := hq.1
    exact Group.IsPerfect.not_isSolvable _ hsol

end Proof1514

theorem rank3II_15_19_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (h1518 : Step1518 A (lB A) c L) (hsmall : Step1519Small) (hP : Step1519P)
    (hcent : Step1519Cent) : Step1519 A (lB A) c L := by
  intro Y hctx
  obtain ⟨p₀, e, hp₀, he, hiso, -⟩ := hctx.concl1515
  have hp2 : p₀ = 2 := h1518 Y hctx p₀ e he hiso
  subst hp2
  have he1 : e ≠ 1 := ne_one_of_isoLThreePi_two h.mem_thetaComponentsAt hiso
  obtain ⟨he2, he3⟩ := hsmall G A c L h Y hctx e hiso
  obtain ⟨p, hp, hp3⟩ := exists_isChoice1519 (m := e) (by omega)
  obtain ⟨P, hPab, hPcard, hPQ⟩ := hP G A c L h Y hctx e p hiso hp hp3
  exact ⟨p, P, hp.1, hp3, ⟨e, he, hiso, hp⟩, hPab, hPcard, hPQ,
    hcent G A c L h Y hctx e p hiso hp hp3⟩

end CFSG.RankThree.PartTwo.Sec15
