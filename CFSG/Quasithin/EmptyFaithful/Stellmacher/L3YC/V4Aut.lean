module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace Stellmacher.L3YC

section Aut

variable {G : Type} [Group G]

theorem comm_of_sq_one {V : Subgroup G} (hsq : ∀ a ∈ V, a * a = 1) :
    ∀ a b : V, a * b = b * a := by
  intro a b
  have h1 : (a * b) * (a * b) = 1 := Subtype.ext (hsq _ (V.mul_mem a.2 b.2))
  have ha : a * a = 1 := Subtype.ext (hsq _ a.2)
  have hb : b * b = 1 := Subtype.ext (hsq _ b.2)
  have ha' : a⁻¹ = a := (inv_eq_of_mul_eq_one_right ha)
  have hb' : b⁻¹ = b := (inv_eq_of_mul_eq_one_right hb)
  have h2 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [h2, mul_inv_rev, ha', hb']

theorem card_mulAut_of_card_four [Finite G] {V : Subgroup G} (hV4 : Nat.card V = 4)
    (hsq : ∀ a ∈ V, a * a = 1) : Nat.card (MulAut V) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 2)
    (W := ↥V) (comm_of_sq_one hsq)
    (fun a => by rw [pow_two]; exact Subtype.ext (hsq _ a.2)) (by rw [hV4]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  decide

theorem pow_three_eq_one_of_odd {A : Type*} [Group A] (hA : Nat.card A = 6) {a : A}
    {m : ℕ} (hm : Odd m) (ha : a ^ m = 1) : a ^ 3 = 1 := by
  have h6 : a ^ 6 = 1 := by
    rw [← hA]
    exact pow_card_eq_one'
  have h := pow_gcd_eq_one.mpr ⟨ha, h6⟩
  have hg : Nat.gcd m 6 ∣ 3 := by
    have hcop : Nat.Coprime (Nat.gcd m 6) 2 :=
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left m 6) (Nat.coprime_two_right.mpr hm))
    have h63 : Nat.gcd m 6 ∣ 2 * 3 := Nat.gcd_dvd_right m 6
    exact hcop.dvd_of_dvd_mul_left h63
  exact (orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one h).trans hg))

@[expose] noncomputable def actAut {V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    MulAut V :=
  V.normalizerMonoidHom ⟨g, hg⟩

theorem actAut_apply {V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (x : V) : ((actAut hg x : V) : G) = g * x * g⁻¹ := rfl

theorem actAut_pow {V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (n : ℕ) :
    actAut hg ^ n = actAut (pow_mem hg n) := by
  unfold actAut
  rw [← map_pow]
  rfl

theorem actAut_eq_one_iff {V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    actAut hg = 1 ↔ ∀ x ∈ V, g * x * g⁻¹ = x := by
  constructor
  · intro h x hx
    have := congrArg (fun φ : MulAut V => ((φ ⟨x, hx⟩ : V) : G)) h
    simpa [actAut_apply] using this
  · intro h
    ext x
    exact h x x.2

theorem pow_three_centralizes {V : Subgroup G} (hA : Nat.card (MulAut V) = 6) {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) {m : ℕ} (hgm : g ^ 3 ^ m = 1) :
    ∀ x ∈ V, g ^ 3 * x * (g ^ 3)⁻¹ = x := by
  have h1 : actAut hg ^ 3 ^ m = 1 := by
    rw [actAut_pow, actAut_eq_one_iff]
    intro x _
    rw [hgm]
    group
  have h2 := pow_three_eq_one_of_odd hA (Odd.pow (by decide : Odd 3)) h1
  rw [actAut_pow, actAut_eq_one_iff] at h2
  exact h2

theorem exists_threePart_moves [Finite G] {V : Subgroup G} (hV4 : Nat.card V = 4)
    (hsq : ∀ a ∈ V, a * a = 1) {y : G} (hy : y ∈ Subgroup.normalizer (V : Set G))
    (hodd : Odd (orderOf y)) (hmove : ∃ x ∈ V, y * x * y⁻¹ ≠ x) :
    ∃ r a : ℕ, (y ^ r) ^ 3 ^ a = 1 ∧ ∃ x ∈ V, y ^ r * x * (y ^ r)⁻¹ ≠ x := by
  have hA := card_mulAut_of_card_four hV4 hsq
  have hpos : 0 < orderOf y := orderOf_pos y
  obtain ⟨a, r, hr3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' 3 (by norm_num)
  have hya : actAut hy ^ orderOf y = 1 := by
    rw [actAut_pow, actAut_eq_one_iff]
    intro x _
    rw [pow_orderOf_eq_one]
    group
  have h3 : actAut hy ^ 3 = 1 := pow_three_eq_one_of_odd hA hodd hya
  have hne : actAut hy ≠ 1 := by
    rw [Ne, actAut_eq_one_iff]
    push Not
    exact hmove
  have hord3 : orderOf (actAut hy) = 3 := by
    have h1 : orderOf (actAut hy) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  refine ⟨r, a, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one y
  · have hne' : actAut hy ^ r ≠ 1 := by
      intro h
      exact hr3 (hord3 ▸ orderOf_dvd_iff_pow_eq_one.mpr h)
    rw [actAut_pow, Ne, actAut_eq_one_iff] at hne'
    push Not at hne'
    exact hne'

end Aut

end Stellmacher.L3YC

end CFSG.Quasithin
