module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesSplit
public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusNeg
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice Polynomial

namespace ExcFramesHalf

theorem not_seven_dvd_two_pow_add_one (f : ℕ) : ¬ 7 ∣ 2 ^ f + 1 := by
  intro h
  have h1 : 2 ^ f = 8 ^ (f / 3) * 2 ^ (f % 3) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : 8 ^ (f / 3) % 7 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h3 : f % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [h1, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, h2] at h
  interval_cases hr : f % 3 <;> simp at h

theorem eleven_le_of_dvd_two_pow_add_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ f + 1) (h3 : p ≠ 3) (h5 : p ≠ 5) : 11 ≤ p := by
  have h7 : p ≠ 7 := fun h => not_seven_dvd_two_pow_add_one f (h ▸ hpq)
  have h2 := hp.two_le
  by_contra hlt
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem orderOf_eq_two_of_dvd_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q + 1) :
    orderOf ((q : ℕ) : ZMod p) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((q : ℕ) : ZMod p) = -1 := by
    have h0 : (((q + 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  rw [h1]
  exact orderOf_eq_prime (neg_one_sq) (neg_one_ne_one_zmod hp hp2)

theorem not_dvd_of_eleven_le {p k : ℕ} (hp : p.Prime) (h11 : 11 ≤ p)
    (hk : k ∈ [1, 3, 4, 5, 6, 7, 9, 10, 12, 15]) : ¬ p ∣ k := by
  intro h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  have hk0 : 0 < k := by omega
  have hle := Nat.le_of_dvd hk0 h
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try omega
  all_goals interval_cases p <;> first | omega | exact absurd hp (by norm_num)

section Sylow


theorem sylowTorus_E8_half (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K + 1) : SylowTorus (adjointGroup .E8 K) p 8 := by
  have hp2 : p ≠ 2 := by omega
  have he := orderOf_eq_two_of_dvd_add_one hp hp2 hpq
  have hpK : ¬ p ∣ Nat.card K := fun h =>
    hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hpq))
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hchar : (wordMat Tag.E8 e8TwoWord).charpoly = cyclotomic 2 ℤ ^ 8 * 1 := by
    rw [e8Two_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hord : p ^ (Nat.card (adjointGroup .E8 K)).factorization p =
      (p ^ (Nat.card K ^ 2 - 1).factorization p) ^ 8 := by
    rw [ordProj_card_adjointGroup_E (Or.inr (Or.inr rfl)) hp (by omega) hpK,
      prod_ordProj_pow_sub_one hp hp2 hpK hq2 he (degreesE .E8) fun d hd _ => ?_]
    · rfl
    · simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by norm_num, not_dvd_of_eleven_le hp h11 (by decide)⟩
  exact sylowTorus_untwisted 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega) hpK
    (IsWeylMatrix.of_word Tag.E8 e8TwoWord) 1 (by norm_num) e8Two_pow
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) hchar he
    (by
      rw [eval_one]
      intro h
      exact hp.one_lt.ne' (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (by exact_mod_cast h))))
    hord

theorem sylowTorus_E7_half (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K + 1) : SylowTorus (adjointGroup .E7 K) p 7 := by
  have hp2 : p ≠ 2 := by omega
  have he := orderOf_eq_two_of_dvd_add_one hp hp2 hpq
  have hpK : ¬ p ∣ Nat.card K := fun h =>
    hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hpq))
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hchar : (wordMat Tag.E7 e7TwoWord).charpoly = cyclotomic 2 ℤ ^ 7 * 1 := by
    rw [e7Two_charpoly]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  have hord : p ^ (Nat.card (adjointGroup .E7 K)).factorization p =
      (p ^ (Nat.card K ^ 2 - 1).factorization p) ^ 7 := by
    rw [ordProj_card_adjointGroup_E (Or.inr (Or.inl rfl)) hp (by omega) hpK,
      prod_ordProj_pow_sub_one hp hp2 hpK hq2 he (degreesE .E7) fun d hd _ => ?_]
    · rfl
    · simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by norm_num, not_dvd_of_eleven_le hp h11 (by decide)⟩
  exact sylowTorus_untwisted 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega) hpK
    (IsWeylMatrix.of_word Tag.E7 e7TwoWord) 1 (by norm_num) e7Two_pow
    (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega) hchar he
    (by
      rw [eval_one]
      intro h
      exact hp.one_lt.ne' (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (by exact_mod_cast h))))
    hord

end Sylow

theorem pow_le_card_of_sylowTorus {C G : Type} [Group C] [Group G] [Finite G] {p m : ℕ}
    (h : SylowTorus C p m) (χ : C →* G) (hχ : Function.Injective χ) {Bs : Subgroup G}
    (hBsR : Bs ≤ χ.range) (hBs : IsElemAbelian p Bs)
    (hmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    p ^ m ≤ Nat.card Bs := by
  obtain ⟨T, E, hT, hconj, hET, -, hEel, hcard⟩ := h.exists_torus
  have := hT
  have hP : IsPGroup p (Bs.comap χ) :=
    isPGroup_of_isElemAbelian (ExcFrames.isElemAbelian_comap_frame χ hχ hBs)
  obtain ⟨g, hg⟩ := hconj _ hP
  have hle : (E.map (MulAut.conj g).toMonoidHom).map χ ≤ Bs := by
    rintro _ ⟨_, ⟨e, he, rfl⟩, rfl⟩
    refine hmax _ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨x, rfl⟩ := hBsR hb
      obtain ⟨t, ht, htx⟩ := hg (show x ∈ Bs.comap χ from hb)
      have hc : t * e = e * t := setLike_mul_comm ht (hET he)
      rw [← map_mul, ← map_mul]
      congr 1
      rw [← htx, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply]
      calc g * t * g⁻¹ * (g * e * g⁻¹) = g * (t * e) * g⁻¹ := by group
        _ = g * (e * t) * g⁻¹ := by rw [hc]
        _ = g * e * g⁻¹ * (g * t * g⁻¹) := by group
    · rw [← map_pow, ← map_pow, hEel.2 e he, map_one, map_one]
  calc p ^ m = Nat.card E := hcard.symm
    _ = Nat.card ((E.map (MulAut.conj g).toMonoidHom).map χ) := by
      rw [Subgroup.card_map_of_injective hχ,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le hle

end ExcFramesHalf

end CFSG.StandardType
