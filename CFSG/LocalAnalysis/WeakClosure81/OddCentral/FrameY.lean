module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.PropositionS
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.InvSets
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup CFSG.LocalAnalysis.WeakClosure81.OddCentral

section
variable {Y : Type} [Group Y] [Finite Y]

theorem le_center_of_comm {N : Subgroup Y} [hN : N.Normal] {d₀ : Y}
    (hgen : normalClosure ({d₀} : Set Y) = ⊤) (h : ∀ x ∈ N, d₀ * x = x * d₀) :
    N ≤ center Y := by
  intro x hx
  rw [mem_center_iff]
  have hcl : (⊤ : Subgroup Y) ≤ centralizer (N : Set Y) := by
    rw [← hgen, normalClosure, closure_le]
    intro e he
    obtain ⟨b, hb, hbe⟩ := (Group.mem_conjugatesOfSet_iff).mp he
    rw [Set.mem_singleton_iff] at hb
    rw [hb] at hbe
    obtain ⟨y, rfl⟩ := isConj_iff.mp hbe
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro n hn
    have h' := h _ (show y⁻¹ * n * y ∈ N by simpa using hN.conj_mem n hn y⁻¹)
    calc n * (y * d₀ * y⁻¹) = y * ((y⁻¹ * n * y) * d₀) * y⁻¹ := by group
      _ = y * (d₀ * (y⁻¹ * n * y)) * y⁻¹ := by rw [h']
      _ = y * d₀ * y⁻¹ * n := by group
  intro g
  exact (mem_centralizer_iff.mp (hcl (mem_top g)) x hx).symm

theorem commute_of_comm_mem {P Z₀ : Subgroup Y} (hZc : Z₀ ≤ center Y) (hZP : Z₀ ≤ P)
    (hPodd : Odd (Nat.card P)) {e x : Y} (he : e * e = 1) (h : e * x * e⁻¹ * x⁻¹ ∈ Z₀) :
    e * x = x * e := by
  obtain ⟨z, hz⟩ : ∃ z, z = e * x * e⁻¹ * x⁻¹ := ⟨_, rfl⟩
  rw [← hz] at h
  have hzc := mem_center_iff.mp (hZc h)
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hex : e * x * e⁻¹ = z * x := by rw [hz]; group
  have hezx : e * (z * x) * e⁻¹ = z * (z * x) := by
    rw [show e * (z * x) * e⁻¹ = (e * z) * x * e⁻¹ by group, hzc e,
      show z * e * x * e⁻¹ = z * (e * x * e⁻¹) by group, hex]
  have hxx : e * (e * x * e⁻¹) * e⁻¹ = x := by
    rw [show e * (e * x * e⁻¹) * e⁻¹ = (e * e) * x * (e * e)⁻¹ by group, he]; group
  rw [hex, hezx] at hxx
  have hz1 : z = 1 := eq_one_of_sq_of_odd hPodd (hZP h) (by
    calc z * z = z * (z * x) * x⁻¹ := by group
      _ = 1 := by rw [hxx, mul_inv_cancel])
  calc e * x = z * x * e := by rw [← hex]; group
    _ = x * e := by rw [hz1, one_mul]

theorem max_of_min {P : Subgroup Y} {d : Fin 3 → Y} (hgen : normalClosure ({d 0} : Set Y) = ⊤)
    (hmin : ∀ N : Subgroup Y, N.Normal → N < P → ∀ i, ∀ x ∈ N, d i * x = x * d i) :
    ∀ N : Subgroup Y, N.Normal → P ⊓ center Y ≤ N → N ≤ P → N = P ⊓ center Y ∨ N = P := by
  intro N hN hZN hNP
  by_cases hNe : N = P
  · exact Or.inr hNe
  · left
    have hlt : N < P := lt_of_le_of_ne hNP hNe
    have hc := le_center_of_comm hgen (hmin N hN hlt 0)
    exact le_antisymm (le_inf hNP hc) hZN

theorem comm_c_of_comm {P Z₀ R : Subgroup Y} [hPn : P.Normal] [hZn : Z₀.Normal] {d : Fin 3 → Y}
    (hS : ∀ i, ∀ r ∈ R, ∀ a ∈ P,
      (d i * r * (d i)⁻¹ * r⁻¹) * a * (d i * r * (d i)⁻¹ * r⁻¹)⁻¹ * a⁻¹ ∈ Z₀) :
    ∀ r ∈ R, ∀ x ∈ P, (r * (d 0 * d 1 * d 2) * r⁻¹ * (d 0 * d 1 * d 2)⁻¹) * x *
      (r * (d 0 * d 1 * d 2) * r⁻¹ * (d 0 * d 1 * d 2)⁻¹)⁻¹ * x⁻¹ ∈ Z₀ := by
  intro r hr x hx
  let C := secCent P Z₀
  let π := QuotientGroup.mk' C
  have hπ : ∀ g, π g = 1 ↔ g ∈ C := fun g => QuotientGroup.eq_one_iff g
  have hcomm : ∀ i, π (d i) * π r = π r * π (d i) := by
    intro i
    have h1 : π (d i * r * (d i)⁻¹ * r⁻¹) = 1 := (hπ _).mpr (hS i r hr)
    simp only [map_mul, map_inv] at h1
    calc π (d i) * π r = (π (d i) * π r * (π (d i))⁻¹ * (π r)⁻¹) * π r * π (d i) := by group
      _ = π r * π (d i) := by rw [h1, one_mul]
  have hc : π (r * (d 0 * d 1 * d 2) * r⁻¹ * (d 0 * d 1 * d 2)⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    have e : π r * (π (d 0) * π (d 1) * π (d 2)) = (π (d 0) * π (d 1) * π (d 2)) * π r := by
      rw [mul_assoc, mul_assoc, ← mul_assoc (π r), ← hcomm 0, mul_assoc, ← mul_assoc (π r),
        ← hcomm 1, mul_assoc, ← hcomm 2]
      group
    rw [e]; group
  exact (hπ _).mp hc x hx

theorem exists_mul_centralizer {R : Subgroup Y} [hRn : R.Normal] (hRodd : Odd (Nat.card R))
    {c : Y} (hc2 : c * c = 1) (hcR : ∀ g : Y, c⁻¹ * (g * c * g⁻¹) ∈ R) :
    ∀ y : Y, ∃ r ∈ R, ∃ g : Y, g * c * g⁻¹ = c ∧ y = r * g := by
  intro y
  set r₁ := c⁻¹ * (y * c * y⁻¹) with hr₁
  have hr₁R : r₁ ∈ R := hcR y
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hcy2 : (y * c * y⁻¹) * (y * c * y⁻¹) = 1 := by
    rw [show y * c * y⁻¹ * (y * c * y⁻¹) = y * (c * c) * y⁻¹ by group, hc2]; group
  have hc'i : (y * c * y⁻¹)⁻¹ = y * c * y⁻¹ := inv_eq_of_mul_eq_one_right hcy2
  have hinv : c * r₁ * c⁻¹ = r₁⁻¹ := by
    calc c * r₁ * c⁻¹ = (y * c * y⁻¹) * c⁻¹ := by rw [hr₁]; group
      _ = (y * c * y⁻¹)⁻¹ * c := by rw [hc'i, hci]
      _ = r₁⁻¹ := by rw [hr₁]; group
  obtain ⟨k, hk⟩ := hRodd
  set r := (r₁⁻¹) ^ (k + 1) with hrdef
  have hrR : r ∈ R := R.pow_mem (R.inv_mem hr₁R) _
  have hr1 : r₁ ^ (2 * k + 1) = 1 := by
    have := pow_card_eq_one' (G := R) (x := ⟨r₁, hr₁R⟩)
    rw [hk] at this
    exact congrArg Subtype.val this
  have hrr : r * r = r₁⁻¹ := by
    rw [hrdef, ← pow_add, inv_pow, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ,
      hr1, one_mul]
  have hcr : c * r * c⁻¹ = r⁻¹ := by
    rw [hrdef, ← MulAut.conj_apply, map_pow, map_inv, MulAut.conj_apply, hinv, inv_inv,
      ← inv_pow, inv_inv]
  have hrc : r * c * r⁻¹ = y * c * y⁻¹ := by
    calc r * c * r⁻¹ = r * (c * r⁻¹ * c⁻¹) * c := by group
      _ = r * r * c := by
          rw [show c * r⁻¹ * c⁻¹ = (c * r * c⁻¹)⁻¹ by group, hcr, inv_inv]
      _ = r₁⁻¹ * c := by rw [hrr]
      _ = c * r₁ := by
          rw [← hinv]
          calc (c * r₁ * c⁻¹) * c = c * r₁ * (c⁻¹ * c) := by group
            _ = c * r₁ := by rw [inv_mul_cancel, mul_one]
      _ = y * c * y⁻¹ := by rw [hr₁]; group
  refine ⟨r, hrR, r⁻¹ * y, ?_, by group⟩
  calc r⁻¹ * y * c * (r⁻¹ * y)⁻¹ = r⁻¹ * (y * c * y⁻¹) * r := by group
    _ = c := by rw [← hrc]; group

theorem invSet_nontrivial {P Z₀ : Subgroup Y} [hPn : P.Normal] [hZn : Z₀.Normal]
    (hZc : Z₀ ≤ center Y) (hP' : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ Z₀)
    (hPodd : Odd (Nat.card P)) {d : Fin 3 → Y} (hd : ∀ i, d i * d i = 1)
    (hdc : ∀ i j, d i * d j = d j * d i) {t : Y} (ht : ∀ i, t * d i * t⁻¹ = d (i + 1))
    (hc : ∀ x ∈ P, (d 0 * d 1 * d 2) * x * (d 0 * d 1 * d 2)⁻¹ * x ∈ Z₀)
    (hLA : ∀ i j, i ≠ j → ∀ x ∈ P, (d i * d j) * x * (d i * d j)⁻¹ * x⁻¹ ∈ Z₀ →
      d i * x * (d i)⁻¹ * x⁻¹ ∈ Z₀)
    (hmove : ∃ x ∈ P, d 0 * x * (d 0)⁻¹ * x⁻¹ ∉ Z₀) : ∀ i, ∃ a ∈ InvSet P d i, a ≠ 1 := by
  obtain ⟨x, hxP, hx⟩ := hmove
  obtain ⟨a, ha, hm⟩ := exists_inv_decomp hZc hP' hPodd hd hdc hc hLA hxP
  have h0 : ∃ b ∈ InvSet P d 0, b ≠ 1 := by
    refine ⟨a 0, ha 0, fun h1 => hx ?_⟩
    set m := x⁻¹ * (a 0 * a 1 * a 2) with hmdef
    have hxe : x = a 1 * a 2 * m⁻¹ := by rw [hmdef, h1]; group
    have hmc := mem_center_iff.mp (hZc (Z₀.inv_mem hm)) (d 0)
    have h1' : d 0 * a 1 = a 1 * d 0 := (ha 1).2.2 0 (by decide)
    have h2' : d 0 * a 2 = a 2 * d 0 := (ha 2).2.2 0 (by decide)
    have hcomm : d 0 * x = x * d 0 := by
      rw [hxe]
      calc d 0 * (a 1 * a 2 * m⁻¹) = (d 0 * a 1) * a 2 * m⁻¹ := by group
        _ = a 1 * (d 0 * a 2) * m⁻¹ := by rw [h1']; group
        _ = a 1 * a 2 * (d 0 * m⁻¹) := by rw [h2']; group
        _ = a 1 * a 2 * m⁻¹ * d 0 := by rw [hmc]; group
    rw [hcomm]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact Z₀.one_mem
  obtain ⟨b, hb, hb1⟩ := h0
  have h1 : ∃ b ∈ InvSet P d 1, b ≠ 1 :=
    ⟨t * b * t⁻¹, conj_mem_invSet_succ ht hb, fun h => hb1 (by
      calc b = t⁻¹ * (t * b * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group)⟩
  obtain ⟨b', hb', hb'1⟩ := h1
  have h2 : ∃ b ∈ InvSet P d 2, b ≠ 1 :=
    ⟨t * b' * t⁻¹, conj_mem_invSet_succ ht hb', fun h => hb'1 (by
      calc b' = t⁻¹ * (t * b' * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group)⟩
  intro i
  fin_cases i
  · exact ⟨b, hb, hb1⟩
  · exact ⟨b', hb', hb'1⟩
  · exact h2

end

end CFSG.LocalAnalysis.WeakClosure81.OddCentral
