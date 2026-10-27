module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.SQTKSimpleListTauCeti
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Open CFSG.SectionRank

@[expose] def RankLeTwo (Y : Type) [Group Y] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E ≤ p ^ 2

theorem stronglyQuasithin_of_rankLeTwo {X : Type} [Group X] [Finite X] (h : RankLeTwo X) :
    SQTKTauCeti.StronglyQuasithin X :=
  fun p hp hp2 => pRank_le hp.one_lt fun E _ hE => h p hp hp2 E hE

theorem isPGroup_of_isElemAbelian {Y : Type} [Group Y] {p : ℕ} {E : Subgroup Y}
    (hE : IsElemAbelian p E) : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem card_le_of_cube_free {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hnd : ¬ p ^ 3 ∣ Nat.card Y) {E : Subgroup Y} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
  have hdvd : p ^ n ∣ Nat.card Y := hn ▸ Subgroup.card_subgroup_dvd_card E
  have hn2 : n ≤ 2 := by
    by_contra h
    exact hnd ((pow_dvd_pow p (by omega)).trans hdvd)
  rw [hn]
  exact Nat.pow_le_pow_right hp.pos hn2

theorem not_pow_three_dvd {m p : ℕ} (hm : m = 168 ∨ m = 360 ∨ m = 1080 ∨ m = 6048)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 3 ∣ m := by
  intro hd
  by_cases hq : p < 19
  · interval_cases p <;> first
      | (exfalso; revert hp; norm_num; done)
      | omega
  · have h19 : 19 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have hle := Nat.le_of_dvd (by rcases hm with rfl | rfl | rfl | rfl <;> norm_num) hd
    rcases hm with rfl | rfl | rfl | rfl <;> omega

theorem rankLeTwo_of_three {Y : Type} [Group Y] [Finite Y]
    (hm : Nat.card Y = 168 ∨ Nat.card Y = 360 ∨ Nat.card Y = 1080 ∨ Nat.card Y = 6048)
    (h3 : ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2) : RankLeTwo Y := by
  intro p hp hp2 E hE
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 E hE
  · exact card_le_of_cube_free hp (not_pow_three_dvd hm hp hp2 hp3) hE

theorem rankLeTwo_of_card_168_or_360 {Y : Type} [Group Y] [Finite Y]
    (hm : Nat.card Y = 168 ∨ Nat.card Y = 360) : RankLeTwo Y :=
  rankLeTwo_of_three (by tauto) fun _ hE =>
    card_le_of_cube_free Nat.prime_three (by rcases hm with h | h <;> rw [h] <;> norm_num) hE

theorem rankLeTwo_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : RankLeTwo Y') : RankLeTwo Y := by
  intro p hp hp2 E hE
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := isElemAbelian_map hE e.toMonoidHom
  have := h p hp hp2 _ hE'
  rwa [Subgroup.card_map_of_injective e.injective] at this

theorem rankLeTwo_of_hom {X L : Type} [Group X] [Finite X] [Group L] (j : L →* X)
    (hj : Function.Injective j) [j.range.Normal] (hq : IsPGroup 2 (X ⧸ j.range))
    (O : Subgroup L) [O.Normal] (hO : IsPGroup 2 O) (hY : RankLeTwo (L ⧸ O)) :
    RankLeTwo X := by
  intro p hp hp2 E hE
  have key : ∀ {M : Type} [Group M] (x : M), x ^ p = 1 → (∃ b : ℕ, x ^ 2 ^ b = 1) → x = 1 := by
    intro M _ x hxp ⟨b, hxb⟩
    have hcop : Nat.Coprime p (2 ^ b) :=
      Nat.Coprime.pow_right b ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
    have := (pow_gcd_eq_one (a := x)).2 ⟨hxp, hxb⟩
    rwa [hcop, pow_one] at this
  have hEL : E ≤ j.range := by
    intro e he
    rw [← QuotientGroup.eq_one_iff (N := j.range)]
    obtain ⟨b, hb⟩ := hq (QuotientGroup.mk e)
    refine key _ ?_ ⟨b, hb⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (by rw [hE.2 e he]; exact j.range.one_mem)
  let jinv : j.range ≃* L := (MonoidHom.ofInjective hj).symm
  let ψ : E →* L ⧸ O :=
    (QuotientGroup.mk' O).comp (jinv.toMonoidHom.comp (Subgroup.inclusion hEL))
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hmem : jinv (Subgroup.inclusion hEL e) ∈ O := (QuotientGroup.eq_one_iff _).1 he
    obtain ⟨b, hb⟩ := hO ⟨_, hmem⟩
    have hb' : (jinv (Subgroup.inclusion hEL e)) ^ 2 ^ b = 1 := by
      simpa using congrArg Subtype.val hb
    have hp' : (jinv (Subgroup.inclusion hEL e)) ^ p = 1 := by
      rw [← map_pow]
      have : (Subgroup.inclusion hEL e) ^ p = 1 := Subtype.ext (by simpa using hE.2 e.1 e.2)
      rw [this, map_one]
    have h1 := key _ hp' ⟨b, hb'⟩
    exact Subgroup.inclusion_injective hEL (jinv.injective (h1.trans (map_one jinv).symm))
  have hR : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a', rfl⟩ ⟨_, b', rfl⟩
      apply Subtype.ext
      change ψ a' * ψ b' = ψ b' * ψ a'
      rw [← map_mul, ← map_mul, hE.1.is_comm.comm a' b']
    · rintro _ ⟨a', rfl⟩
      rw [← map_pow]
      have : a' ^ p = 1 := Subtype.ext (by simpa using hE.2 a'.1 a'.2)
      rw [this, map_one]
  have hcard : Nat.card ψ.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  rw [← hcard]
  exact hY p hp hp2 ψ.range hR

end CFSG.Quasithin.H13.U3.GC137.SQ
