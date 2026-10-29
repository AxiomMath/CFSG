module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.K432.AltRow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Equiv Equiv.Perm
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.K432 (exists_odd_mem_centralizer_of_pow_three)

theorem alt_zpow_eq_one {α : Type*} {σ : Perm α} (h3 : σ ^ 3 = 1) {x : α} (hx : σ x ≠ x)
    {j : ℤ} (hj : (σ ^ j) x = x) : σ ^ j = 1 := by
  have hσ : σ ≠ 1 := by
    rintro rfl
    exact hx rfl
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 hσ
  have hmod : σ ^ (j % 3) = σ ^ j := by
    have h := zpow_mod_orderOf σ j
    rw [hord] at h
    exact_mod_cast h
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h | h | h
  · rw [← hmod, h, zpow_zero]
  · rw [← hmod, h, zpow_one] at hj
    exact absurd hj hx
  · rw [← hmod, h, zpow_two, Equiv.Perm.mul_apply] at hj
    have h3x : σ (σ (σ x)) = x := by
      have := congrArg (fun π : Perm α => π x) h3
      simpa [pow_succ, Equiv.Perm.mul_apply] using this
    rw [hj] at h3x
    exact absurd h3x hx

theorem alt_exists_cycle_split {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h3 : σ ^ 3 = 1) {x : α} (hx : σ x ≠ x) :
    ∃ c z : Perm α, σ = c * z ∧ Equiv.Perm.Disjoint c z ∧ c ^ 3 = 1 ∧ c.IsCycle ∧ c x ≠ x := by
  have hmem : σ.cycleOf x ∈ σ.cycleFactorsFinset :=
    cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)
  have hdisj : Equiv.Perm.Disjoint (σ * (σ.cycleOf x)⁻¹) (σ.cycleOf x) :=
    disjoint_mul_inv_of_mem_cycleFactorsFinset hmem
  refine ⟨σ.cycleOf x, σ * (σ.cycleOf x)⁻¹, ?_, hdisj.symm, ?_, isCycle_cycleOf σ hx, ?_⟩
  · have hcomm : Commute (σ.cycleOf x) (σ * (σ.cycleOf x)⁻¹) := hdisj.symm.commute
    rw [hcomm.eq]
    simp
  · have h1 : orderOf (σ.cycleOf x) ∣ orderOf σ := orderOf_cycleOf_dvd_orderOf σ x
    have h2 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans h2)
  · rw [cycleOf_apply_self]
    exact hx

theorem alt_exists_conj_commute {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 6 ≤ Fintype.card α) {σ : Perm α} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) (hs : sign σ = 1) :
    ∃ y : Perm α, IsConj σ y ∧ Commute y σ ∧ (∀ k : ℤ, y ≠ σ ^ k) ∧ sign y = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  obtain ⟨c, z, hσ, hdisj, hc3, hcyc, hcx⟩ := alt_exists_cycle_split h3 hx
  have hzx : z x = x := by
    rcases (Equiv.Perm.disjoint_iff_eq_or_eq.mp hdisj x) with h | h
    · exact absurd h hcx
    · exact h
  by_cases hz : z = 1
  ·
    subst hz
    have hcyc' : σ.IsCycle := by
      rw [hσ, mul_one]
      exact hcyc
    have hthree : σ.IsThreeCycle :=
      card_support_eq_three_iff.mp (by rw [← hcyc'.orderOf, orderOf_eq_prime h3 h1])
    have hcard3 : σ.support.card = 3 := hthree.card_support
    have hcompl : 2 < σ.supportᶜ.card := by
      rw [Finset.card_compl, hcard3]
      omega
    obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := Finset.two_lt_card.mp hcompl
    have ha' : σ a = a := Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp ha)
    have hb' : σ b = b := Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp hb)
    have hd' : σ d = d := Equiv.Perm.notMem_support.mp (Finset.mem_compl.mp hd)
    obtain ⟨τ, hτ⟩ : ∃ τ : Perm α, τ = Equiv.swap a b * Equiv.swap a d := ⟨_, rfl⟩
    have hτ3 : τ.IsThreeCycle := by
      rw [hτ]
      exact isThreeCycle_swap_mul_swap_same hab had hbd
    have hdisjστ : Equiv.Perm.Disjoint σ τ := by
      rw [Equiv.Perm.disjoint_iff_eq_or_eq]
      intro w
      by_cases hw : σ w = w
      · exact Or.inl hw
      · right
        have hwa : w ≠ a := fun h => hw (by rw [h]; exact ha')
        have hwb : w ≠ b := fun h => hw (by rw [h]; exact hb')
        have hwd : w ≠ d := fun h => hw (by rw [h]; exact hd')
        rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwa hwd,
          Equiv.swap_apply_of_ne_of_ne hwa hwb]
    have hτa : τ a = d := by
      rw [hτ, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
    have hτnot : ∀ k : ℤ, τ ≠ σ ^ k := by
      intro k hk
      apply had
      rw [← hτa, hk]
      exact (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ha' k).symm
    refine ⟨τ, ?_, hdisjστ.commute.symm, hτnot, hτ3.sign⟩
    exact isConj_iff_cycleType_eq.mpr (by rw [hthree.cycleType, hτ3.cycleType])
  ·
    have hcz : Commute c z := hdisj.commute
    refine ⟨c⁻¹ * z, ?_, ?_, ?_, ?_⟩
    · refine isConj_iff_cycleType_eq.mpr ?_
      rw [hdisj.inv_left.cycleType_mul, cycleType_inv, hσ, hdisj.cycleType_mul]
    · rw [hσ]
      exact Commute.mul_right (Commute.mul_left (Commute.inv_left (Commute.refl c)) hcz.symm)
        (Commute.mul_left hcz.inv_left (Commute.refl z))
    · intro k hk
      have hzk : z = c * σ ^ k := by
        rw [← hk, mul_inv_cancel_left]
      have hcσ : c * σ = σ ^ k := by
        calc c * σ = c * (c * z) := by rw [hσ]
          _ = c * (c * (c * σ ^ k)) := by rw [hzk]
          _ = c * (c * c) * σ ^ k := by simp only [mul_assoc]
          _ = σ ^ k := by rw [← pow_three, hc3, one_mul]
      have hck : c = σ ^ k * σ⁻¹ := eq_mul_inv_of_mul_eq hcσ
      have hzj : z = σ ^ (2 * k - 1) := by
        rw [hzk, hck]
        group
      have hzσ : (σ ^ (2 * k - 1)) x = x := by
        rw [← hzj]
        exact hzx
      exact hz (hzj.trans (alt_zpow_eq_one h3 hx hzσ))
    · rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← Equiv.Perm.sign_mul, ← hσ, hs]

theorem alt_exists_conj_alt {n : ℕ} (hn : 5 ≤ n) {σ y : Perm (Fin n)} (h3 : σ ^ 3 = 1)
    (hy : IsConj σ y) :
    ∃ g : alternatingGroup (Fin n), (g : Perm (Fin n)) * σ * (g : Perm (Fin n))⁻¹ = y := by
  obtain ⟨g0, hg0⟩ := isConj_iff.mp hy
  by_cases hA : g0 ∈ alternatingGroup (Fin n)
  · exact ⟨⟨g0, hA⟩, hg0⟩
  · obtain ⟨c0, hc0, hc0A⟩ := exists_odd_mem_centralizer_of_pow_three hn h3
    have hsg0 : sign g0 = -1 := by
      rcases Int.units_eq_one_or (sign g0) with h | h
      · exact absurd (mem_alternatingGroup.mpr h) hA
      · exact h
    have hsc0 : sign c0 = -1 := by
      rcases Int.units_eq_one_or (sign c0) with h | h
      · exact absurd (mem_alternatingGroup.mpr h) hc0A
      · exact h
    have hmem : g0 * c0 ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, Equiv.Perm.sign_mul, hsg0, hsc0]
      decide
    refine ⟨⟨g0 * c0, hmem⟩, ?_⟩
    have hcσ : c0 * σ * c0⁻¹ = σ := by
      rw [hc0, mul_assoc, mul_inv_cancel, mul_one]
    show g0 * c0 * σ * (g0 * c0)⁻¹ = y
    rw [← hg0]
    calc g0 * c0 * σ * (g0 * c0)⁻¹ = g0 * (c0 * σ * c0⁻¹) * g0⁻¹ := by group
      _ = g0 * σ * g0⁻¹ := by rw [hcσ]

theorem alt_not_weaklyClosed {n : ℕ} (hn : 6 ≤ n) {z : alternatingGroup (Fin n)}
    (hz : orderOf z = 3) : ¬ WeaklyClosed (Subgroup.zpowers z) := by
  have hz3 : (z : Perm (Fin n)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : Perm (Fin n)) ≠ 1 := by
    intro h
    have h' : z = 1 := Subtype.ext h
    rw [h', orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hs : sign (z : Perm (Fin n)) = 1 := mem_alternatingGroup.mp z.2
  obtain ⟨y, hconj, hcomm, hnot, -⟩ :=
    alt_exists_conj_commute (by rw [Fintype.card_fin]; exact hn) hz3 hz1 hs
  obtain ⟨g, hg⟩ := alt_exists_conj_alt (by omega) hz3 hconj
  apply not_weaklyClosed_of_commute_conj (z := z) (g := g)
  · apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hg]
    exact hcomm
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hnot k
    have h := congrArg (fun w : alternatingGroup (Fin n) => (w : Perm (Fin n))) hk
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact hg.symm.trans h.symm

theorem alt_listRow_six {n : ℕ} (hn : 6 ≤ n) : ListRow (alternatingGroup (Fin n)) :=
  listRow_of_forall_not_weaklyClosed fun _ hz => alt_not_weaklyClosed hn hz

theorem alt_prime_eq_three_of_dvd {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    (hE : ∀ x ∈ E, x ^ 3 = 1) {p : ℕ} (hp : p.Prime) (hpd : p ∣ Nat.card E) : p = 3 := by
  haveI := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p hpd
  have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hE x.1 x.2)
  have hdiv : p ∣ 3 := by
    rw [← hx]
    exact orderOf_dvd_of_pow_eq_one hx3
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdiv

theorem alt_pRank_three_five : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 5))) = 1 := by
  apply le_antisymm
  · apply CFSG.SectionRank.pRank_le (by norm_num)
    intro E _ hE
    have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hdvd : Nat.card E ∣ 60 := by
      have := Subgroup.card_subgroup_dvd_card E
      rwa [hcard] at this
    have hexp : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => hE.2 x hx
    have h2 : ¬ 2 ∣ Nat.card E := fun h => by
      have := alt_prime_eq_three_of_dvd hexp Nat.prime_two h
      omega
    have h5 : ¬ 5 ∣ Nat.card E := fun h => by
      have := alt_prime_eq_three_of_dvd hexp (by norm_num : Nat.Prime 5) h
      omega
    have key : ∀ m : ℕ, m < 61 → m ∣ 60 → ¬ 2 ∣ m → ¬ 5 ∣ m → m ≤ 3 := by decide
    have hlt : Nat.card E < 61 := Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd)
    have := key _ hlt hdvd h2 h5
    simpa using this
  · obtain ⟨c3, hc3⟩ : ∃ c : Perm (Fin 5), c = Equiv.swap 0 1 * Equiv.swap 0 2 := ⟨_, rfl⟩
    have hthree : c3.IsThreeCycle := by
      rw [hc3]
      exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
    have hmem : c3 ∈ alternatingGroup (Fin 5) := mem_alternatingGroup.mpr hthree.sign
    obtain ⟨zA, hzA⟩ : ∃ zA : alternatingGroup (Fin 5), (zA : Perm (Fin 5)) = c3 :=
      ⟨⟨c3, hmem⟩, rfl⟩
    have hord : orderOf zA = 3 := by
      rw [← Subgroup.orderOf_coe, hzA]
      exact hthree.orderOf
    have h3 : zA ^ 3 = 1 := by
      apply Subtype.ext
      have h := pow_orderOf_eq_one c3
      rw [hthree.orderOf] at h
      rw [Subgroup.coe_pow, hzA, Subgroup.coe_one]
      exact h
    have hEl : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers zA) := by
      refine ⟨inferInstance, fun x hx => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
    have hk : Nat.card (Subgroup.zpowers zA) = 3 ^ 1 := by
      rw [Nat.card_zpowers, hord, pow_one]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_top hEl hk

theorem alt_listRow_five : ListRow (alternatingGroup (Fin 5)) :=
  listRow_of_pRank_eq_one alt_pRank_three_five

theorem goodRow_alternatingGroup {n : ℕ} (hn : 5 ≤ n) : GoodRow (alternatingGroup (Fin n)) := by
  refine And.intro ?_ ?_
  · rcases Nat.lt_or_ge n 6 with h | h
    · obtain rfl : n = 5 := by omega
      exact alt_listRow_five
    · exact alt_listRow_six h
  · apply outerRow_of_not_three_dvd_outer
    intro h3
    have h4 := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn
    have h34 : 3 ∣ 4 := h3.trans h4
    omega

theorem row_five : ∀ n : ℕ, 5 ≤ n → n ≤ 12 → RowOf (alternatingGroup (Fin n)) := by
  intro n hn _
  unfold RowOf
  intro S _ _ _ _ he
  obtain ⟨e⟩ := he
  exact GoodRow.of_mulEquiv e.symm (goodRow_alternatingGroup hn)

end CFSG.RankThree.PartTwo.Sec4.RonanK432
