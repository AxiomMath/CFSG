
module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin

namespace A38

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem three_le_pRank_conj [Finite G] {q : ℕ} [Fact q.Prime] {L : Subgroup G} {t : G}
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) {a b : G} (ha : a ∈ L) (hb : b ∈ L)
    (haq : a ^ q = 1) (hbq : b ^ q = 1) (hab : Commute a b) (hnc : ∃ l ∈ L, a * l ≠ l * a)
    (hind : ∀ n : ℕ, a ^ n ≠ b) : 3 ≤ CFSG.Open.pRank q (⊤ : Subgroup G) := by
  have hcomm' : ∀ u ∈ L, ∀ v ∈ L.map (MulAut.conj t).toMonoidHom, Commute u v := by
    intro u hu v hv
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hu) v hv).symm
  have hzmem : t * a * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, ha, by simp [MulAut.conj_apply]⟩
  refine ClassicalEven.three_le_pRank_of_gens (x := a) (y := b) (z := t * a * t⁻¹)
    haq hbq ?_ hab (hcomm' a ha _ hzmem) (hcomm' b hb _ hzmem) ?_ hind ?_
  · rw [conj_pow, haq]
    simp
  · rintro rfl
    obtain ⟨l, -, h⟩ := hnc
    simp at h
  · intro n m h
    have hzL : t * a * t⁻¹ ∈ L := by
      rw [← h]
      exact L.mul_mem (L.pow_mem ha n) (L.pow_mem hb m)
    obtain ⟨l, hl, hne⟩ := hnc
    apply hne
    have hl' : t * l * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨l, hl, by simp [MulAut.conj_apply]⟩
    have h1 : (t * a * t⁻¹) * (t * l * t⁻¹) = (t * l * t⁻¹) * (t * a * t⁻¹) :=
      hcomm' _ hzL _ hl'
    have h2 : t * (a * l) * t⁻¹ = t * (l * a) * t⁻¹ := by
      simpa [mul_assoc] using h1
    exact mul_left_cancel (mul_right_cancel h2)

theorem exists_pair {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime) {P : Subgroup X}
    (N : Subgroup X) (hexp : ∀ x ∈ P, x ^ q = 1) (hnc : ∃ x ∈ P, x ∉ N)
    (hcases : IsElemAbelianOfRank q 2 ↥P ∨ IsPOnePlusTwo q ↥P) :
    ∃ a ∈ P, ∃ b ∈ P, a ∉ N ∧ a * b = b * a ∧ ∀ n : ℕ, a ^ n ≠ b := by
  obtain ⟨x, hxP, hx⟩ := hnc
  have hq2 := hq.two_le
  have hzp : Nat.card ↥(Subgroup.zpowers x) ≤ q := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hq.pos (orderOf_dvd_of_pow_eq_one (hexp x hxP))
  rcases hcases with hE | ⟨hX, hcard, -⟩
  · obtain ⟨e⟩ := hE
    have hcardP : Nat.card ↥P = q ^ 2 := by
      rw [Nat.card_congr e.toEquiv]
      have : NeZero q := ⟨hq.ne_zero⟩
      simp [Nat.card_eq_fintype_card]
    have hcomm : ∀ u v : ↥P, u * v = v * u := fun u v =>
      e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    obtain ⟨b, hbP, hb⟩ : ∃ b ∈ P, b ∉ Subgroup.zpowers x := by
      by_contra hcon
      push Not at hcon
      have hle : P ≤ Subgroup.zpowers x := fun y hy => hcon y hy
      have h1 : Nat.card ↥P ≤ Nat.card ↥(Subgroup.zpowers x) := Subgroup.card_le_of_le hle
      rw [hcardP] at h1
      nlinarith
    exact ⟨x, hxP, b, hbP, hx, congrArg Subtype.val (hcomm ⟨x, hxP⟩ ⟨b, hbP⟩),
      fun n hn => hb (hn ▸ Subgroup.npow_mem_zpowers x n)⟩
  · have := hX
    have hZcard : Nat.card (Subgroup.center ↥P) = q := CFSG.IsExtraspecial.center_order_p q ↥P
    have hZne : Subgroup.center ↥P ≠ ⊤ := by
      intro h
      have h1 : Nat.card ↥(Subgroup.center ↥P) = Nat.card ↥P := by
        rw [h]
        exact Subgroup.card_top
      rw [hZcard, hcard] at h1
      have h2 : q < q ^ 3 := by nlinarith [pow_pos hq.pos 2]
      omega
    obtain ⟨y₀, hy₀⟩ : ∃ y : ↥P, y ∉ Subgroup.center ↥P := by
      by_contra hcon
      push Not at hcon
      exact hZne (eq_top_iff.mpr fun y _ => hcon y)
    obtain ⟨a₀, ha₀X, ha₀Z⟩ : ∃ a : ↥P, (a : X) ∉ N ∧ a ∉ Subgroup.center ↥P := by
      by_cases h1 : (y₀ : X) ∈ N
      · by_cases h2 : (⟨x, hxP⟩ : ↥P) ∈ Subgroup.center ↥P
        · refine ⟨⟨x, hxP⟩ * y₀, ?_, ?_⟩
          · intro hmem
            apply hx
            have := N.mul_mem hmem (N.inv_mem h1)
            simpa using this
          · intro hmem
            apply hy₀
            have := (Subgroup.center ↥P).mul_mem ((Subgroup.center ↥P).inv_mem h2) hmem
            simpa using this
        · exact ⟨⟨x, hxP⟩, hx, h2⟩
      · exact ⟨y₀, h1, hy₀⟩
    obtain ⟨b₀, hb₀Z, hb₀1⟩ : ∃ b : ↥P, b ∈ Subgroup.center ↥P ∧ b ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : Subgroup.center ↥P = ⊥ :=
        eq_bot_iff.mpr fun z hz => Subgroup.mem_bot.mpr (hcon z hz)
      rw [h1, Subgroup.card_bot] at hZcard
      omega
    have hexp' : ∀ y : ↥P, y ^ q = 1 := fun y => Subtype.ext (by
      have := hexp (y : X) y.2
      simpa using this)
    have ha₀1 : a₀ ≠ 1 := fun h => ha₀Z (h ▸ Subgroup.one_mem _)
    have hordA : orderOf a₀ = q :=
      (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one (hexp' a₀)) |>.resolve_left
        fun h => ha₀1 (orderOf_eq_one_iff.mp h)
    have hordB : orderOf b₀ = q :=
      (Nat.dvd_prime hq).mp (orderOf_dvd_of_pow_eq_one (hexp' b₀)) |>.resolve_left
        fun h => hb₀1 (orderOf_eq_one_iff.mp h)
    refine ⟨a₀, a₀.2, b₀, b₀.2, ha₀X, congrArg Subtype.val (Subgroup.mem_center_iff.mp hb₀Z a₀),
      fun n hn => ?_⟩
    have hn' : a₀ ^ n = b₀ := Subtype.ext (by simpa using hn)
    have hb₀mem : b₀ ∈ Subgroup.zpowers a₀ := hn' ▸ Subgroup.npow_mem_zpowers a₀ n
    have hle : Subgroup.zpowers b₀ ≤ Subgroup.zpowers a₀ := Subgroup.zpowers_le.mpr hb₀mem
    have heq : Subgroup.zpowers b₀ = Subgroup.zpowers a₀ := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hordA, hordB]
    apply ha₀Z
    have : a₀ ∈ Subgroup.zpowers b₀ := heq ▸ Subgroup.mem_zpowers a₀
    exact Subgroup.zpowers_le.mpr hb₀Z this

end A38

end CFSG.Quasithin
