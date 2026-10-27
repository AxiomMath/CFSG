module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcGenuine
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CF67SL34
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Fam
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7

public section

namespace CFSG.StandardType

open CFSG.ComponentClassification.PSL3Four CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GH74.GLS.Stage2.Bender.Thm1.CF67S CFSG.Assembly CFSG.Blueprint

namespace PSL3FourThree

theorem prime_dvd_card_eq {q : ℕ} (hq : q.Prime) (h : q ∣ 20160) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 := by
  have h1 : q ∣ 2 ^ 6 * 3 ^ 2 * 5 * 7 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hq).mp h2 with h3 | h3
    · rcases (Nat.Prime.dvd_mul hq).mp h3 with h4 | h4
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h4))
      · exact Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h4)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h3)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h2)))

theorem isPGroup_centralizer_of_pow_three_eq_one
    {K : Type} [Group K] (e : K ≃* ↥S) {g : K} (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) : IsPGroup 3 ↥(Subgroup.centralizer ({g} : Set K)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcard, hcent, -⟩ := facts_of_equiv_S.{0, 0} e
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hg : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  rw [IsPGroup.iff_orderOf]
  rintro ⟨y, hy⟩
  rw [Subgroup.orderOf_mk]
  have hgy : Commute g y := (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hm0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  have hg3S : (↑(e g) : Equiv.Perm (Fin 42)) ^ 3 = 1 := by
    have : (e g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    simpa using congrArg Subtype.val this
  have hg1S : (↑(e g) : Equiv.Perm (Fin 42)) ≠ 1 := fun h =>
    hg1 (e.injective (Subtype.ext (by simpa using h)))
  have key : ∀ {q : ℕ}, q.Prime → q ∣ orderOf y → q = 3 := by
    intro q hq hqm
    by_contra hq3
    set z := y ^ (orderOf y / q) with hz
    have hzq : orderOf z = q := orderOf_pow_orderOf_div hm0 hqm
    have hgz : Commute g z := hgy.pow_right _
    have hqK : q ∣ 20160 := by
      rw [← hcard, ← hzq]
      exact orderOf_dvd_natCard z
    have hzq1 : z ≠ 1 := by
      rintro h
      rw [h, orderOf_one] at hzq
      exact hq.one_lt.ne hzq
    have hzp : z ^ q = 1 := hzq ▸ pow_orderOf_eq_one z
    rcases prime_dvd_card_eq hq hqK with h2 | h3 | h5 | h7
    ·
      subst h2
      have h64 := hcent z hzq
      have hmem : g ∈ Subgroup.centralizer ({z} : Set K) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hgz.eq
      have h3 : orderOf (⟨g, hmem⟩ : Subgroup.centralizer ({z} : Set K)) = 3 := by
        rw [Subgroup.orderOf_mk]; exact hg
      have hd := orderOf_dvd_natCard (⟨g, hmem⟩ : Subgroup.centralizer ({z} : Set K))
      rw [h3, h64] at hd
      exact absurd hd (by norm_num)
    · exact hq3 h3
    all_goals
      have hcommS : (↑(e g) : Equiv.Perm (Fin 42)) * ↑(e z) = ↑(e z) * ↑(e g) := by
        have : e g * e z = e z * e g := by rw [← map_mul, ← map_mul, hgz.eq]
        exact congrArg Subtype.val this
      have hzqS : (↑(e z) : Equiv.Perm (Fin 42)) ^ q = 1 := by
        have : (e z) ^ q = 1 := by rw [← map_pow, hzp, map_one]
        simpa using congrArg Subtype.val this
      have hz1S : (↑(e z) : Equiv.Perm (Fin 42)) ≠ 1 := fun h =>
        hzq1 (e.injective (Subtype.ext (by simpa using h)))
    · exact S_no_comm (e g).2 (e z).2 hcommS (Or.inl h5) hg3S hg1S hzqS hz1S
    · exact S_no_comm (e g).2 (e z).2 hcommS (Or.inr h7) hg3S hg1S hzqS hz1S
  have := Nat.eq_prime_pow_of_unique_prime_dvd hm0 fun {d} hd hdm => key hd hdm
  exact ⟨_, this⟩

theorem card_mulAut_S : Nat.card (MulAut ↥S) = 241920 := by
  rw [← Nat.card_congr (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.Cls3.conjIso).toEquiv, card_R]

theorem isPGroup_fixedSubgroup
    {K : Type} [Group K] (e : K ≃* ↥S) (E : Subgroup (MulAut K)) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) : IsPGroup 3 ↥(ggFixedSubgroup E) := by
  classical
  obtain ⟨hKcard, -, -⟩ := facts_of_equiv_S.{0, 0} e
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  have hc : Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨k, rfl⟩ := e.surjective s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
    rw [center_S_eq_bot, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (e.injective (hz'.trans (map_one e).symm))
  have hinj := conj_injective_of_center_bot hc
  have hA : Nat.card (MulAut K) = 241920 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_S]
  have hO : Nat.card (Outer K) = 12 := by
    have := card_mulAut_eq_outer_mul hc
    rw [hA, hKcard] at this
    omega
  obtain ⟨v, hvE, hv1, hvin⟩ := exists_inner_ne_one E hcard (by rw [hO]; norm_num)
  obtain ⟨g, rfl⟩ : ∃ g : K, MulAut.conj g = v := hvin
  have hv3 : (MulAut.conj g) ^ 3 = 1 := hE.2 _ hvE
  have hg3 : g ^ 3 = 1 := by apply hinj; rw [map_pow, hv3, map_one]
  have hg1 : g ≠ 1 := by rintro rfl; exact hv1 (map_one _)
  have hP := isPGroup_centralizer_of_pow_three_eq_one e hg3 hg1
  refine hP.of_injective (Subgroup.inclusion ?_) (Subgroup.inclusion_injective _)
  intro y hy
  have h1 := hy _ hvE
  rw [MulAut.conj_apply] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

end PSL3FourThree

theorem ggSeitzExcLThreeFourCentralizerInput_holds :
    GGSeitzExcLThreeFourCentralizerInput := by
  intro K _ _ d q hq2 hq3 hd he E hE hcard
  obtain ⟨e⟩ := he
  obtain ⟨e'⟩ := CFSG.ComponentClassification.CatFactsSmall.nonempty_equiv_psl34_of_lieModel
    (ggLieModel_lThreeFour d q hq2 hq3 hd e)
  exact PSL3FourThree.isPGroup_fixedSubgroup e' E hE hcard

end CFSG.StandardType
