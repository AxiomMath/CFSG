module

public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.G11.SzG11S.B5c

open CFSG.SectionRank CFSG.Open

theorem exists_odd_prime_noncentral {K : Type*} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ ∃ a b : K, a * b ≠ b * a ∧ ∀ y : K, a ^ r * y = y * a ^ r := by
  obtain ⟨-, hsimple, a₀, b₀, hab₀⟩ := hK
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hsimple
  have hodd : ∃ r : ℕ, r.Prime ∧ r ∣ Nat.card (K ⧸ Subgroup.center K) ∧ Odd r := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (Nat.card (K ⧸ Subgroup.center K)) with
      ⟨k, hk⟩ | h
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 (K ⧸ Subgroup.center K) := IsPGroup.of_card hk
      have := hp.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center (K ⧸ Subgroup.center K)) with h | h
      · exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance h
      · apply hab₀
        have ha : a₀ ∈ Subgroup.center (K ⧸ Subgroup.center K) := h ▸ Subgroup.mem_top a₀
        exact ((Subgroup.mem_center_iff.mp ha) b₀).symm
    · exact h
  obtain ⟨r, hr, hdvd, hodd⟩ := hodd
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  have hpow : a ^ r ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hx]
    exact pow_orderOf_eq_one _
  have hnc : a ∉ Subgroup.center K := by
    intro h
    have : (a : K ⧸ Subgroup.center K) = 1 := (QuotientGroup.eq_one_iff a).2 h
    rw [this, orderOf_one] at hx
    exact hr.one_lt.ne hx
  rw [Subgroup.mem_center_iff] at hnc
  push Not at hnc
  obtain ⟨b, hb⟩ := hnc
  refine ⟨r, hr, ?_, a, b, fun h => hb h.symm, fun y => ?_⟩
  · rintro rfl
    exact absurd hodd (by decide)
  · exact ((Subgroup.mem_center_iff.mp hpow) y).symm

theorem three_le_pRank_center_quotient {Λ : Type*} [Group Λ] [Finite Λ] {r : ℕ} [hr : Fact r.Prime]
    (a t : Fin 3 → Λ) (hacen : ∀ i, a i ^ r ∈ Subgroup.center Λ)
    (hacomm : ∀ i j, Commute (a i) (a j))
    (htcomm : ∀ i j, i ≠ j → Commute (t i) (a j))
    (hta : ∀ i, ¬ Commute (t i) (a i)) :
    3 ≤ CFSG.Open.pRank r (⊤ : Subgroup (Λ ⧸ Subgroup.center Λ)) := by
  have hp1 : 1 < r := hr.out.one_lt
  set Z := Subgroup.center Λ with hZ
  let b : Fin 3 → Λ ⧸ Z := fun i => (a i : Λ ⧸ Z)
  have hbpow : ∀ i, b i ^ r = 1 := fun i => by
    show (a i : Λ ⧸ Z) ^ r = 1
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (hacen i)
  have hbcomm : ∀ i j, Commute (b i) (b j) := fun i j =>
    (hacomm i j).map (QuotientGroup.mk' Z)
  have hbmk : ∀ (i : Fin 3) (n : ℕ), b i ^ n = ((a i ^ n : Λ) : Λ ⧸ Z) := fun i n =>
    (QuotientGroup.mk_pow Z (a i) n).symm
  have hindep : ∀ (i : Fin 3) (x : Λ), Commute (t i) x → b i = (x : Λ ⧸ Z) → False := by
    intro i x hx hxe
    have hz : (a i)⁻¹ * x ∈ Z := QuotientGroup.eq.1 hxe
    have hzc : Commute (t i) ((a i)⁻¹ * x) := Subgroup.mem_center_iff.1 hz (t i)
    apply hta i
    have : a i = x * ((a i)⁻¹ * x)⁻¹ := by group
    rw [this]
    exact hx.mul_right hzc.inv_right
  have hc0 : ∀ u v : Unit, u * v = v * u := fun _ _ => rfl
  have hp0 : ∀ u : Unit, u ^ r = 1 := fun _ => rfl
  have hB0 : Nat.card Unit = r ^ 0 := by simp
  let F0 : Unit →* Λ ⧸ Z := 1
  have hF0 : Function.Injective F0 := fun u v _ => rfl
  have hF0one : ∀ u, F0 u = 1 := fun _ => rfl
  have h0ne : b 0 ∉ F0.range := by
    rintro ⟨u, hu⟩
    refine hindep 0 1 (Commute.one_right _) ?_
    rw [← hu, hF0one]; rfl
  obtain ⟨F1, hF1, hc1, hp1', hB1, hr1⟩ := exists_extend hc0 hp0 hB0 F0 hF0 (y := b 0)
    (hbpow 0) h0ne (fun u => by rw [hF0one]; exact Commute.one_left _)
  have hF1form : ∀ u, ∃ n : ℕ, F1 u = b 0 ^ n := fun u => by
    obtain ⟨u0, n, hn⟩ := hr1 u
    exact ⟨n, by rw [hn, hF0one, one_mul]⟩
  have h1ne : b 1 ∉ F1.range := by
    rintro ⟨u, hu⟩
    obtain ⟨n, hn⟩ := hF1form u
    refine hindep 1 (a 0 ^ n) ((htcomm 1 0 (by decide)).pow_right n) ?_
    rw [← hbmk, ← hn, hu]
  obtain ⟨F2, hF2, hc2, hp2, hB2, hr2⟩ := exists_extend hc1 hp1' hB1 F1 hF1 (y := b 1)
    (hbpow 1) h1ne (fun u => by
      obtain ⟨n, hn⟩ := hF1form u
      rw [hn]; exact (hbcomm 0 1).pow_left n)
  have hF2form : ∀ u, ∃ m n : ℕ, F2 u = b 0 ^ m * b 1 ^ n := fun u => by
    obtain ⟨u1, n, hn⟩ := hr2 u
    obtain ⟨m, hm⟩ := hF1form u1
    exact ⟨m, n, by rw [hn, hm]⟩
  have h2ne : b 2 ∉ F2.range := by
    rintro ⟨u, hu⟩
    obtain ⟨m, n, hmn⟩ := hF2form u
    refine hindep 2 (a 0 ^ m * a 1 ^ n)
      (((htcomm 2 0 (by decide)).pow_right m).mul_right ((htcomm 2 1 (by decide)).pow_right n)) ?_
    rw [QuotientGroup.mk_mul, ← hbmk, ← hbmk, ← hmn, hu]
  obtain ⟨F3, hF3, hc3, hp3, hB3, -⟩ := exists_extend hc2 hp2 hB2 F2 hF2 (y := b 2)
    (hbpow 2) h2ne (fun u => by
      obtain ⟨m, n, hmn⟩ := hF2form u
      rw [hmn]; exact ((hbcomm 0 2).pow_left m).mul_left ((hbcomm 1 2).pow_left n))
  have := le_pRank_of_injective hp1 hc3 hp3 hB3 F3 hF3 (le_top : F3.range ≤ ⊤)
  omega

end CFSG.Quasithin.G11.SzG11S.B5c
