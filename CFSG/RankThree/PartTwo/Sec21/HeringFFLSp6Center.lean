module

public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLTransfer

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

private lemma not_sq_dvd_1451520 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 1451520 := by
  intro h
  have hprod : (2 : ℕ) ^ 9 * 3 ^ 4 * 5 * 7 = 1451520 := by norm_num
  have hd : p ∣ 2 ^ 9 * 3 ^ 4 * 5 * 7 := by
    rw [hprod]
    exact (dvd_pow_self p two_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).mp hd with hA | h7
  · rcases (Nat.Prime.dvd_mul hp).mp hA with hB | h5
    · rcases (Nat.Prime.dvd_mul hp).mp hB with h2' | h3'
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2'))
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3'))
    · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 5)).mp h5
      exact absurd h (by decide)
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7
    exact absurd h (by decide)

theorem center_eq_bot_of_sp6 {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (h2 : ¬ 2 ∣ Nat.card (Subgroup.center X)) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (hm : StatedClassicalModel (X ⧸ Subgroup.center X) .PSp 3 2 1) :
    Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_H6_of_stated hm
  have hQ : Nat.card (X ⧸ Subgroup.center X) = 1451520 := by
    rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.card_H6]
  by_contra hne
  have hZ : Nat.card (Subgroup.center X) ≠ 1 :=
    fun h => hne ((Subgroup.eq_bot_iff_card (Subgroup.center X)).mpr h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hZ
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h => h2 (h ▸ hpd)
  have hp3 : p ≠ 3 := fun h => h3 (h ▸ hpd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpd
  have hzp : (z : X) ^ p = 1 := by
    have h1 : z ^ p = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    exact congrArg Subtype.val h1
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p X))
  obtain ⟨f, hf⟩ : ∃ f : (P : Subgroup X) →* X ⧸ Subgroup.center X,
      f = (QuotientGroup.mk' (Subgroup.center X)).comp (P : Subgroup X).subtype := ⟨_, rfl⟩
  have hfp : IsPGroup p f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    exact P.isPGroup'.map _
  have hdvd : Nat.card f.range ∣ p := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hfp
    have h1 := Subgroup.card_subgroup_dvd_card f.range
    rw [hQ, hn] at h1
    rw [hn]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have h4 := pow_dvd_pow p (show n ≤ 1 by omega)
      rwa [pow_one] at h4
    · exact absurd ((pow_dvd_pow p hn2).trans h1) (not_sq_dvd_1451520 hp hp2 hp3)
  haveI : IsCyclic f.range := isCyclic_of_card_dvd_prime hdvd
  have hker : f.rangeRestrict.ker ≤ Subgroup.center (P : Subgroup X) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hf] at hx
    have hx' : ((x : X) : X ⧸ Subgroup.center X) = 1 := hx
    have hxZ : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff (x : X)).mp hx'
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    exact Subgroup.mem_center_iff.mp hxZ (g : X)
  have hcomm : IsMulCommutative (P : Subgroup X) :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f.rangeRestrict hker
  have hPab : ∀ x ∈ (P : Subgroup X), ∀ y ∈ (P : Subgroup X), x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hz1 : (z : X) = 1 := eq_one_of_mem_center_of_abelian_sylow hX.1 P hPab z.2 hzp
  have hz2 : z = 1 := Subtype.ext hz1
  rw [hz2, orderOf_one] at hz
  exact hp.one_lt.ne hz

end CFSG.RankThree.PartTwo.Sec21
