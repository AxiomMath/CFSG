module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.RankThree.GF2n.Smith81

open Equiv Equiv.Perm Finset
open scoped commutatorElement

variable {α : Type*} [Fintype α] [DecidableEq α]

section SmallSupport

theorem commute_of_card_support_lt {A : Subgroup (Perm α)} {s : ℕ}
    (hmin : ∀ d ∈ A, d ≠ 1 → s ≤ d.support.card) {c : Perm α}
    (hc : c ∈ Subgroup.normalizer (A : Set (Perm α))) (hcs : 2 * c.support.card < s) :
    ∀ b ∈ A, c * b = b * c := by
  intro b hb
  have hcb : c * b * c⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hc b).mp hb
  have hd : c * b * c⁻¹ * b⁻¹ ∈ A := A.mul_mem hcb (A.inv_mem hb)
  have hsupp : (c * b * c⁻¹ * b⁻¹).support.card ≤ 2 * c.support.card := by
    have h1 : c * b * c⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by group
    rw [h1]
    calc (c * (b * c⁻¹ * b⁻¹)).support.card ≤ (c.support ⊔ (b * c⁻¹ * b⁻¹).support).card :=
          Finset.card_le_card (Perm.support_mul_le _ _)
      _ ≤ c.support.card + (b * c⁻¹ * b⁻¹).support.card := Finset.card_union_le _ _
      _ = 2 * c.support.card := by
          rw [Perm.card_support_conj, Perm.support_inv]
          ring
  by_contra hne
  have hd1 : c * b * c⁻¹ * b⁻¹ ≠ 1 := by
    intro h
    apply hne
    rw [mul_inv_eq_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have := hmin _ hd hd1
  omega

end SmallSupport

section PairSwap

variable {a : Perm α}

@[expose] def dblSwap (a : Perm α) (x y : α) : Perm α := swap x y * swap (a x) (a y)

structure DiffCycles (a : Perm α) (x y : α) : Prop where
  hx : a x ≠ x
  hy : a y ≠ y
  hxy : y ≠ x
  hyx : y ≠ a x

theorem DiffCycles.ne_a (haa : ∀ w, a (a w) = w) {x y : α} (h : DiffCycles a x y) : a y ≠ x := by
  intro e
  apply h.hyx
  rw [← e, haa]

theorem DiffCycles.ne_aa (haa : ∀ w, a (a w) = w) {x y : α} (h : DiffCycles a x y) : a x ≠ a y := by
  intro e
  apply h.hxy
  have := congrArg a e
  rw [haa, haa] at this
  exact this.symm

theorem dblSwap_apply_left (haa : ∀ w, a (a w) = w) {x y : α} (h : DiffCycles a x y) :
    dblSwap a x y x = y := by
  have h1 : x ≠ a x := h.hx.symm
  have h2 : x ≠ a y := (h.ne_a haa).symm
  simp [dblSwap, swap_apply_of_ne_of_ne h1 h2]

theorem dblSwap_apply_a (haa : ∀ w, a (a w) = w) {x y : α} (h : DiffCycles a x y) :
    dblSwap a x y (a x) = a y := by
  have h1 : a y ≠ x := h.ne_a haa
  have h2 : a y ≠ y := h.hy
  simp only [dblSwap, Perm.mul_apply, swap_apply_left]
  exact swap_apply_of_ne_of_ne h1 h2

theorem dblSwap_apply_of_notMem {x y w : α} (hw : w ∉ ({x, y, a x, a y} : Finset α)) :
    dblSwap a x y w = w := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  simp [dblSwap, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

theorem card_support_dblSwap_le (x y : α) : (dblSwap a x y).support.card ≤ 4 := by
  calc (dblSwap a x y).support.card ≤ ((swap x y).support ⊔ (swap (a x) (a y)).support).card :=
        Finset.card_le_card (Perm.support_mul_le _ _)
    _ ≤ (swap x y).support.card + (swap (a x) (a y)).support.card := Finset.card_union_le _ _
    _ ≤ 4 := by
        have h1 : (swap x y).support.card ≤ 2 := by
          by_cases hxy : x = y
          · simp [hxy]
          · rw [card_support_swap hxy]
        have h2 : (swap (a x) (a y)).support.card ≤ 2 := by
          by_cases hxy : a x = a y
          · simp [hxy]
          · rw [card_support_swap hxy]
        omega

theorem dblSwap_mem_alternatingGroup (haa : ∀ w, a (a w) = w) {x y : α} (h : DiffCycles a x y) :
    dblSwap a x y ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup]
  simp only [dblSwap, map_mul]
  rw [sign_swap h.hxy.symm, sign_swap (h.ne_aa haa)]
  decide

theorem dblSwap_commute (haa : ∀ w, a (a w) = w) {x y : α} (h : DiffCycles a x y) :
    dblSwap a x y * a = a * dblSwap a x y := by
  have e1 : a * swap x y * a⁻¹ = swap (a x) (a y) := (swap_apply_apply a x y).symm
  have e2 : a * swap (a x) (a y) * a⁻¹ = swap x y := by
    rw [← swap_apply_apply, haa, haa]
  have hdisj : Disjoint (swap x y) (swap (a x) (a y)) := by
    rw [Perm.disjoint_iff_disjoint_support, support_swap h.hxy.symm,
      support_swap (h.ne_aa haa)]
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    have := h.hx
    have := h.hy
    have := h.hyx
    have := h.ne_a haa
    grind
  have hcomm : swap x y * swap (a x) (a y) = swap (a x) (a y) * swap x y := hdisj.commute.eq
  have e3 : a * (swap x y * swap (a x) (a y)) * a⁻¹ = swap x y * swap (a x) (a y) := by
    calc a * (swap x y * swap (a x) (a y)) * a⁻¹
        = (a * swap x y * a⁻¹) * (a * swap (a x) (a y) * a⁻¹) := by group
      _ = swap (a x) (a y) * swap x y := by rw [e1, e2]
      _ = swap x y * swap (a x) (a y) := hcomm.symm
  have e4 := mul_inv_eq_iff_eq_mul.mp e3
  exact e4.symm

end PairSwap

section CaseLarge

theorem commute_swap_of_apply_eq_self {d : Perm α} {x y : α} (hx : d x = x) (hy : d y = y) :
    d * swap x y = swap x y * d := by
  have h := swap_apply_apply d x y
  rw [hx, hy] at h
  exact (eq_mul_inv_iff_mul_eq.mp h).symm

variable {A : Subgroup (Perm α)}

theorem apply_eq_of_commute_dblSwap {a b : Perm α} {x y : α}
    (hb : b * dblSwap a x y = dblSwap a x y * b) (hxy : dblSwap a x y x = y) :
    b y = dblSwap a x y (b x) := by
  have := congrArg (fun f : Perm α => f x) hb
  simp only [Perm.mul_apply] at this
  rw [hxy] at this
  exact this

theorem mem_of_commute_dblSwap {a b : Perm α} {x y : α}
    (hb : b * dblSwap a x y = dblSwap a x y * b) (hxy : dblSwap a x y x = y) (hyx : y ≠ x) :
    b x ∈ ({x, y, a x, a y} : Finset α) := by
  by_contra h
  have hfix := dblSwap_apply_of_notMem (a := a) h
  have h1 := apply_eq_of_commute_dblSwap hb hxy
  rw [hfix] at h1
  exact hyx (b.injective h1)

theorem eq_one_or_eq_of_large_support
    (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hT1 : ∀ u ∈ A, u ≠ 1 → ∀ c ∈ alternatingGroup α, c * u = u * c →
      c ∈ Subgroup.normalizer (A : Set (Perm α)))
    {a : Perm α} (ha : a ∈ A) (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hmin : ∀ d ∈ A, d ≠ 1 → a.support.card ≤ d.support.card)
    (h9 : 9 ≤ a.support.card) : ∀ b ∈ A, b = 1 ∨ b = a := by
  have haa : ∀ w, a (a w) = w := fun w => by
    have := congrArg (fun f : Perm α => f w) ha2
    simpa using this
  have hex : ∀ T : Finset α, T.card ≤ 8 → ∃ y ∈ a.support, y ∉ T := by
    intro T hT
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (show a.support ⊆ T from hcon)
    omega
  have hXcomm : ∀ x y : α, DiffCycles a x y → ∀ b ∈ A, b * dblSwap a x y = dblSwap a x y * b := by
    intro x y hxy b hb
    have hN := hT1 a ha ha1 _ (dblSwap_mem_alternatingGroup haa hxy) (dblSwap_commute haa hxy)
    have := commute_of_card_support_lt hmin hN
      (by have := card_support_dblSwap_le (a := a) x y; omega) b hb
    exact this.symm
  have hpair : ∀ x ∈ a.support, ∃ y ∈ a.support, DiffCycles a x y := by
    intro x hx
    obtain ⟨y, hy, hyT⟩ := hex {x, a x} (Finset.card_le_two.trans (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyT
    exact ⟨y, hy, ⟨Perm.mem_support.mp hx, Perm.mem_support.mp hy, hyT.1, hyT.2⟩⟩
  have hstep1 : ∀ b ∈ A, ∀ x ∈ a.support, b x = x ∨ b x = a x := by
    intro b hb x hx
    obtain ⟨y, hy, hxy⟩ := hpair x hx
    obtain ⟨y', hy', hyT⟩ : ∃ y' ∈ a.support, y' ∉ ({x, a x, y, a y} : Finset α) :=
      hex _ (Finset.card_le_four.trans (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyT
    obtain ⟨h1, h2, h3, h4⟩ := hyT
    have hxy' : DiffCycles a x y' := ⟨Perm.mem_support.mp hx, Perm.mem_support.mp hy', h1, h2⟩
    have m1 := mem_of_commute_dblSwap (hXcomm x y hxy b hb) (dblSwap_apply_left haa hxy)
      hxy.hxy
    have m2 := mem_of_commute_dblSwap (hXcomm x y' hxy' b hb) (dblSwap_apply_left haa hxy')
      hxy'.hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
    have e1 := hxy.ne_a haa
    have e2 := hxy'.ne_a haa
    have e3 := hxy.ne_aa haa
    have e4 := hxy'.ne_aa haa
    have e5 := haa y
    have e6 := haa y'
    have e7 := hxy.hyx
    have e8 := hxy.hxy
    grind
  have hstep2 : ∀ b ∈ A, (∀ y ∈ a.support, b y = y) ∨ (∀ y ∈ a.support, b y = a y) := by
    intro b hb
    obtain ⟨x₀, hx₀⟩ : a.support.Nonempty := Finset.card_pos.mp (by omega)
    have hba : ∀ w, b (a w) = a (b w) := fun w => by
      have := hAc b hb a ha
      simpa using congrArg (fun f : Perm α => f w) this
    rcases hstep1 b hb x₀ hx₀ with h0 | h0
    · left
      intro y hy
      by_cases hy1 : y = x₀
      · subst hy1
        exact h0
      by_cases hy2 : y = a x₀
      · subst hy2
        rw [hba, h0]
      · have hxy : DiffCycles a x₀ y :=
          ⟨Perm.mem_support.mp hx₀, Perm.mem_support.mp hy, hy1, hy2⟩
        rw [apply_eq_of_commute_dblSwap (hXcomm x₀ y hxy b hb) (dblSwap_apply_left haa hxy), h0,
          dblSwap_apply_left haa hxy]
    · right
      intro y hy
      by_cases hy1 : y = x₀
      · subst hy1
        exact h0
      by_cases hy2 : y = a x₀
      · subst hy2
        rw [hba, h0]
      · have hxy : DiffCycles a x₀ y :=
          ⟨Perm.mem_support.mp hx₀, Perm.mem_support.mp hy, hy1, hy2⟩
        rw [apply_eq_of_commute_dblSwap (hXcomm x₀ y hxy b hb) (dblSwap_apply_left haa hxy), h0,
          dblSwap_apply_a haa hxy]
  have hstep3 : ∀ d ∈ A, (∀ y ∈ a.support, d y = y) → d = 1 := by
    intro d hd hdS
    by_contra hd1
    obtain ⟨x, hx⟩ : a.support.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y, hy, hxy⟩ := hpair x hx
    obtain ⟨z, hz, hzT⟩ : ∃ z ∈ a.support, z ∉ ({x, a x, y, a y} : Finset α) :=
      hex _ (Finset.card_le_four.trans (by norm_num))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzT
    obtain ⟨h1, h2, h3, h4⟩ := hzT
    have hdx : d x = x := hdS x hx
    have hdy : d y = y := hdS y hy
    have hdz : d z = z := hdS z hz
    have hcd : (swap x y * swap x z) * d = d * (swap x y * swap x z) := by
      have e1 := commute_swap_of_apply_eq_self hdx hdy
      have e2 := commute_swap_of_apply_eq_self hdx hdz
      calc swap x y * swap x z * d = swap x y * (swap x z * d) := by rw [mul_assoc]
        _ = swap x y * (d * swap x z) := by rw [e2]
        _ = (swap x y * d) * swap x z := by rw [mul_assoc]
        _ = (d * swap x y) * swap x z := by rw [e1]
        _ = d * (swap x y * swap x z) := by rw [mul_assoc]
    have hcalt : swap x y * swap x z ∈ alternatingGroup α := by
      rw [Perm.mem_alternatingGroup]
      simp only [map_mul]
      rw [sign_swap hxy.hxy.symm, sign_swap (Ne.symm h1)]
      decide
    have hN := hT1 d hd hd1 _ hcalt hcd
    have hcs : (swap x y * swap x z).support.card ≤ 4 := by
      calc (swap x y * swap x z).support.card ≤ ((swap x y).support ⊔ (swap x z).support).card :=
            Finset.card_le_card (Perm.support_mul_le _ _)
        _ ≤ (swap x y).support.card + (swap x z).support.card := Finset.card_union_le _ _
        _ ≤ 4 := by
            rw [card_support_swap hxy.hxy.symm, card_support_swap (Ne.symm h1)]
    have hca := commute_of_card_support_lt hmin hN (by omega) a ha
    have hx' := congrArg (fun f : Perm α => f x) hca
    simp only [Perm.mul_apply] at hx'
    have e1 : swap x z x = z := swap_apply_left x z
    have e2 : swap x y z = z := swap_apply_of_ne_of_ne h1 h3
    have e3 : swap x z (a x) = a x :=
      swap_apply_of_ne_of_ne (Perm.mem_support.mp hx) (Ne.symm h2)
    have e4 : swap x y (a x) = a x :=
      swap_apply_of_ne_of_ne (Perm.mem_support.mp hx) (Ne.symm hxy.hyx)
    rw [e1, e2, e3, e4] at hx'
    exact h1 (a.injective hx').symm
  intro b hb
  rcases hstep2 b hb with h | h
  · exact Or.inl (hstep3 b hb h)
  · right
    have hab : a * b ∈ A := A.mul_mem ha hb
    have h1 : a * b = 1 := hstep3 _ hab fun y hy => by simp [Perm.mul_apply, h y hy, haa]
    exact mul_left_cancel (h1.trans ha2.symm)

end CaseLarge

section CaseFixed

@[expose] def altSupportedOn (F : Finset α) : Subgroup (Perm α) :=
  ((alternatingGroup α).subtype.comp (alternatingGroup.ofSubtype F)).range

theorem mem_altSupportedOn_iff {F : Finset α} {k : Perm α} :
    k ∈ altSupportedOn F ↔ k ∈ alternatingGroup α ∧ k.support ⊆ F := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(alternatingGroup.ofSubtype F g).2,
      (alternatingGroup.mem_range_ofSubtype_iff F (alternatingGroup.ofSubtype F g)).mp
        ⟨g, rfl⟩⟩
  · rintro ⟨hk, hs⟩
    obtain ⟨g, hg⟩ := (alternatingGroup.mem_range_ofSubtype_iff F ⟨k, hk⟩).mpr hs
    exact ⟨g, congrArg Subtype.val hg⟩

theorem altSupportedOn_le_alternatingGroup (F : Finset α) : altSupportedOn F ≤ alternatingGroup α :=
  fun _ hk => (mem_altSupportedOn_iff.mp hk).1

theorem isPerfect_altSupportedOn {F : Finset α} (h5 : 5 ≤ F.card) :
    Group.IsPerfect (altSupportedOn F) := by
  have hcard : 5 ≤ Nat.card (↥F) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact h5
  haveI : IsSimpleGroup (alternatingGroup (↥F)) := alternatingGroup.isSimpleGroup hcard
  haveI : Group.IsPerfect (alternatingGroup (↥F)) := by
    refine TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative ?_
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    omega
  exact Group.IsPerfect.range ((alternatingGroup α).subtype.comp (alternatingGroup.ofSubtype F))

theorem threeCycle_mem_altSupportedOn {F : Finset α} {x y z : α} (hx : x ∈ F) (hy : y ∈ F)
    (hz : z ∈ F)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : swap x y * swap x z ∈ altSupportedOn F := by
  rw [mem_altSupportedOn_iff]
  refine ⟨(isThreeCycle_swap_mul_swap_same hxy hxz hyz).mem_alternatingGroup, ?_⟩
  intro w hw
  have h := Perm.support_mul_le (swap x y) (swap x z) hw
  rw [Finset.sup_eq_union, Finset.mem_union, support_swap hxy, support_swap hxz] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with (rfl | rfl) | (rfl | rfl) <;> assumption

theorem apply_eq_self_of_commute_altSupportedOn {F : Finset α} (h5 : 5 ≤ F.card) {b : Perm α}
    (hb : ∀ k ∈ altSupportedOn F, k * b = b * k) : ∀ x ∈ F, b x = x := by
  intro x hx
  by_contra hne
  have hcard : 1 < (F \ {x, b x}).card := by
    have h1 := Finset.le_card_sdiff ({x, b x} : Finset α) F
    have h2 : ({x, b x} : Finset α).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨z, y, hz, hy, hzy⟩ := Finset.one_lt_card_iff.mp hcard
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hz hy
  have hc := hb _ (threeCycle_mem_altSupportedOn hx hy.1 hz.1 (Ne.symm hy.2.1) (Ne.symm hz.2.1)
    hzy.symm)
  have hcx := congrArg (fun f : Perm α => f x) hc
  simp only [Perm.mul_apply] at hcx
  have e1 : swap x z x = z := swap_apply_left x z
  have e2 : swap x y z = z := swap_apply_of_ne_of_ne hz.2.1 hzy
  have e3 : swap x z (b x) = b x := swap_apply_of_ne_of_ne hne (Ne.symm hz.2.2)
  have e4 : swap x y (b x) = b x := swap_apply_of_ne_of_ne hne (Ne.symm hy.2.2)
  rw [e1, e2, e3, e4] at hcx
  exact hz.2.1 (b.injective hcx).symm

theorem false_of_many_fixed_points {A Q : Subgroup (Perm α)}
    (hA2 : ∀ u ∈ A, u * u = 1)
    (hT1 : ∀ u ∈ A, u ≠ 1 → ∀ c ∈ alternatingGroup α, c * u = u * c →
      c ∈ Subgroup.normalizer (A : Set (Perm α)))
    (hT2 : ∀ P : Subgroup (Perm α), P ≤ alternatingGroup α →
      P ≤ Subgroup.normalizer (A : Set (Perm α)) → Group.IsPerfect P →
      ∀ p ∈ P, ∀ b ∈ A, p * b = b * p)
    (hQ2 : IsPGroup 2 Q) (hQN : Q ≤ Subgroup.normalizer (A : Set (Perm α)))
    (hNQ : ∀ t ∈ alternatingGroup α, t ∈ Subgroup.normalizer (A : Set (Perm α)) →
      t ∈ Subgroup.normalizer (Q : Set (Perm α)))
    (hCQ : ∀ c ∈ alternatingGroup α, (∀ q ∈ Q, c * q = q * c) → c ∈ A)
    {a : Perm α} (ha : a ∈ A) (ha1 : a ≠ 1)
    (h5 : 5 ≤ (Finset.univ.filter fun x => a x = x).card) : False := by
  classical
  set F : Finset α := Finset.univ.filter fun x => a x = x with hFdef
  have hFmem : ∀ x, x ∈ F ↔ a x = x := by
    intro x
    simp [hFdef]
  have hKalt := altSupportedOn_le_alternatingGroup F
  have hKa : ∀ k ∈ altSupportedOn F, k * a = a * k := by
    intro k hk
    have hs := (mem_altSupportedOn_iff.mp hk).2
    have hdisj : Perm.Disjoint k a := by
      rw [Perm.disjoint_iff_disjoint_support, Finset.disjoint_left]
      intro w hwk hwa
      have := (hFmem w).mp (hs hwk)
      exact (Perm.mem_support.mp hwa) this
    exact hdisj.commute.eq
  have hKN : altSupportedOn F ≤ Subgroup.normalizer (A : Set (Perm α)) := fun k hk =>
    hT1 a ha ha1 k (hKalt hk) (hKa k hk)
  have hKcent := hT2 (altSupportedOn F) hKalt hKN (isPerfect_altSupportedOn h5)
  have hAfix : ∀ b ∈ A, ∀ x ∈ F, b x = x := fun b hb =>
    apply_eq_self_of_commute_altSupportedOn h5 (fun k hk => hKcent k hk b hb)
  have hNF : ∀ t ∈ Subgroup.normalizer (A : Set (Perm α)), ∀ w ∈ F, t w ∈ F := by
    intro t ht w hw
    rw [hFmem]
    have h1 : t⁻¹ * a * t ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp ht (t⁻¹ * a * t)).mpr
        (by rw [show t * (t⁻¹ * a * t) * t⁻¹ = a by group]; exact ha)
      exact this
    have h2 := hAfix _ h1 w hw
    simp only [Perm.mul_apply] at h2
    have h3 := congrArg t h2
    simpa using h3
  have hKnorm : ∀ t ∈ Subgroup.normalizer (A : Set (Perm α)), ∀ k ∈ altSupportedOn F,
      t * k * t⁻¹ ∈ altSupportedOn F := by
    intro t ht k hk
    obtain ⟨hka, hks⟩ := mem_altSupportedOn_iff.mp hk
    rw [mem_altSupportedOn_iff]
    refine ⟨?_, ?_⟩
    · rw [Perm.mem_alternatingGroup] at hka ⊢
      simpa [hka] using Perm.sign_conj t k
    · rw [Perm.support_conj]
      intro w hw
      obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
      exact hNF t ht w' (hks hw')
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < F.card)
  have hc3 := isThreeCycle_swap_mul_swap_same hxy hxz hyz
  have hcK := threeCycle_mem_altSupportedOn hx hy hz hxy hxz hyz
  have hcalt := hKalt hcK
  let ι : alternatingGroup ↥F →* Perm α :=
    (alternatingGroup α).subtype.comp (alternatingGroup.ofSubtype F)
  let W : Subgroup (alternatingGroup ↥F) := Q.comap ι
  haveI hWn : W.Normal := ⟨fun w hw g => by
    show ι (g * w * g⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv]
    have hgK : ι g ∈ altSupportedOn F := ⟨g, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNQ (ι g) (hKalt hgK) (hKN hgK)) (ι w)).mp hw⟩
  haveI : IsSimpleGroup (alternatingGroup ↥F) := alternatingGroup.isSimpleGroup (by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact h5)
  have h3ord : orderOf (swap x y * swap x z) = 3 := hc3.orderOf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hW | hW
  · have hcomm : ∀ k ∈ altSupportedOn F, ∀ q ∈ Q, k * q = q * k := by
      intro k hk q hq
      have h1 : k * q * k⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hNQ k (hKalt hk) (hKN hk)) q).mp hq
      have hu1 : k * q * k⁻¹ * q⁻¹ ∈ Q := Q.mul_mem h1 (Q.inv_mem hq)
      have hu2 : k * q * k⁻¹ * q⁻¹ ∈ altSupportedOn F := by
        have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
        rw [e]
        exact (altSupportedOn F).mul_mem hk (hKnorm q (hQN hq) k⁻¹ ((altSupportedOn F).inv_mem hk))
      obtain ⟨g, hg⟩ := hu2
      have hgW : g ∈ W := by
        show ι g ∈ Q
        rw [hg]
        exact hu1
      rw [hW, Subgroup.mem_bot] at hgW
      rw [hgW, map_one] at hg
      have e2 : k * q = q * k := by
        have := hg.symm
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
        exact this
      exact e2
    have hcA : swap x y * swap x z ∈ A :=
      hCQ _ hcalt (fun q hq => hcomm _ hcK q hq)
    have h2 : orderOf (swap x y * swap x z) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hA2 _ hcA)
    rw [h3ord] at h2
    omega
  · obtain ⟨g₀, hg₀⟩ := hcK
    have hg₀Q : swap x y * swap x z ∈ Q := by
      have : g₀ ∈ W := by rw [hW]; exact Subgroup.mem_top _
      rw [← hg₀]
      exact this
    obtain ⟨k, hk⟩ := hQ2 ⟨_, hg₀Q⟩
    have hk' : (swap x y * swap x z) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have h2 : orderOf (swap x y * swap x z) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    rw [h3ord] at h2
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega

end CaseFixed

section Order

theorem not_two_pow_ten_dvd_factorial_div (n : ℕ) (h2 : 2 ≤ n) (hn : n ≤ 12) :
    ¬ 2 ^ 10 ∣ n.factorial / 2 := by
  interval_cases n <;> norm_num [Nat.factorial]

theorem thirteen_le_card_of_isPGroup {Q : Subgroup (Perm α)} (hQalt : Q ≤ alternatingGroup α)
    (hQ2 : IsPGroup 2 Q) (hQbig : 2 ^ 9 < Nat.card Q) : 13 ≤ Nat.card α := by
  by_contra hlt
  push Not at hlt
  rcases Nat.lt_or_ge (Nat.card α) 2 with h2 | h2
  · have h1 : Nat.card Q ≤ Nat.card (Perm α) := Subgroup.card_le_card_group Q
    rw [Nat.card_perm] at h1
    have : (Nat.card α).factorial = 1 := by
      interval_cases (Nat.card α) <;> rfl
    omega
  · haveI : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨k, hk⟩ := hQ2.exists_card_eq
    have hk10 : 10 ≤ k := by
      rw [hk] at hQbig
      by_contra hk9
      push Not at hk9
      have : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hdvd : Nat.card Q ∣ Nat.card (alternatingGroup α) := Subgroup.card_dvd_of_le hQalt
    rw [hk, nat_card_alternatingGroup] at hdvd
    exact not_two_pow_ten_dvd_factorial_div (Nat.card α) h2 (by omega)
      ((pow_dvd_pow 2 hk10).trans hdvd)

end Order

section Main

theorem false_of_alternating_config {A Q : Subgroup (Perm α)}
    (hA2 : ∀ u ∈ A, u * u = 1) (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hA4 : 4 ≤ Nat.card A)
    (hT1 : ∀ u ∈ A, u ≠ 1 → ∀ c ∈ alternatingGroup α, c * u = u * c →
      c ∈ Subgroup.normalizer (A : Set (Perm α)))
    (hT2 : ∀ P : Subgroup (Perm α), P ≤ alternatingGroup α →
      P ≤ Subgroup.normalizer (A : Set (Perm α)) → Group.IsPerfect P →
      ∀ p ∈ P, ∀ b ∈ A, p * b = b * p)
    (hQalt : Q ≤ alternatingGroup α) (hQ2 : IsPGroup 2 Q)
    (hQN : Q ≤ Subgroup.normalizer (A : Set (Perm α)))
    (hNQ : ∀ t ∈ alternatingGroup α, t ∈ Subgroup.normalizer (A : Set (Perm α)) →
      t ∈ Subgroup.normalizer (Q : Set (Perm α)))
    (hCQ : ∀ c ∈ alternatingGroup α, (∀ q ∈ Q, c * q = q * c) → c ∈ A)
    (hQbig : 2 ^ 9 < Nat.card Q) : False := by
  classical
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ d ∈ A, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : A = ⊥ := (Subgroup.eq_bot_iff_forall A).mpr hcon
    rw [hbot, Subgroup.card_bot] at hA4
    omega
  have hex : ∃ s, ∃ d ∈ A, d ≠ 1 ∧ d.support.card = s := ⟨_, d₀, hd₀, hd₀1, rfl⟩
  obtain ⟨a, ha, ha1, has⟩ := Nat.find_spec hex
  have hmin : ∀ d ∈ A, d ≠ 1 → a.support.card ≤ d.support.card := by
    intro d hd hd1
    rw [has]
    exact Nat.find_min' hex ⟨d, hd, hd1, rfl⟩
  have ha2 := hA2 a ha
  by_cases h9 : 9 ≤ a.support.card
  · have hsub := eq_one_or_eq_of_large_support hAc hT1 ha ha1 ha2 hmin h9
    have hle : Nat.card A ≤ 2 := by
      have hsub' : (A : Set (Perm α)) ⊆ {1, a} := fun b hb => by
        rcases hsub b hb with h | h
        · exact Or.inl h
        · exact Or.inr h
      calc Nat.card A = Set.ncard (A : Set (Perm α)) := (Nat.card_coe_set_eq _)
        _ ≤ Set.ncard ({1, a} : Set (Perm α)) := Set.ncard_le_ncard hsub' (Set.toFinite _)
        _ ≤ 2 := by
            have := Set.ncard_insert_le (1 : Perm α) ({a} : Set (Perm α))
            rw [Set.ncard_singleton] at this
            exact this
    omega
  · push Not at h9
    by_cases h5 : 5 ≤ (Finset.univ.filter fun x => a x = x).card
    · exact false_of_many_fixed_points hA2 hT1 hT2 hQ2 hQN hNQ hCQ ha ha1 h5
    · push Not at h5
      have hsum : (Finset.univ.filter fun x => a x = x).card + a.support.card =
          Fintype.card α := by
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
          (fun x => a x = x)
        simpa [Perm.support, Finset.card_univ] using this
      have h13 := thirteen_le_card_of_isPGroup hQalt hQ2 hQbig
      rw [Nat.card_eq_fintype_card] at h13
      omega

end Main

end CFSG.RankThree.GF2n.Smith81
