module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecBCoordPsi
public import CFSG.Quasithin.Vol2.Ch10SecQ34LE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.E9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

section Rank

variable {X : Type*} [Group X] [Finite X]

theorem three_le_pRank {p : ℕ} (hp : p.Prime) {A₁ A₂ A₃ : Subgroup X}
    (h12 : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x) (h13 : ∀ x ∈ A₁, ∀ y ∈ A₃, x * y = y * x)
    (h23 : ∀ x ∈ A₂, ∀ y ∈ A₃, x * y = y * x) {a₁ a₂ a₃ : X} (ha₁ : a₁ ∈ A₁) (ha₂ : a₂ ∈ A₂)
    (ha₃ : a₃ ∈ A₃) (ho₁ : orderOf a₁ = p) (ho₂ : orderOf a₂ = p) (ho₃ : orderOf a₃ = p)
    (hz₁ : ∀ x ∈ Subgroup.zpowers a₁, (∀ y ∈ A₁, x * y = y * x) → x = 1)
    (hz₃ : ∀ x ∈ Subgroup.zpowers a₃, (∀ y ∈ A₃, x * y = y * x) → x = 1) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hB₁ : Subgroup.zpowers a₁ ≤ A₁ := Subgroup.zpowers_le.mpr ha₁
  have hB₂ : Subgroup.zpowers a₂ ≤ A₂ := Subgroup.zpowers_le.mpr ha₂
  have hB₃ : Subgroup.zpowers a₃ ≤ A₃ := Subgroup.zpowers_le.mpr ha₃
  have hc12 : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₂, x * y = y * x :=
    fun x hx y hy => h12 x (hB₁ hx) y (hB₂ hy)
  have hi12 : Subgroup.zpowers a₁ ⊓ Subgroup.zpowers a₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hz₁ x hx.1 fun y hy => (h12 y hy x (hB₂ hx.2)).symm
  have hB12 : Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ≤ Subgroup.centralizer (A₃ : Set X) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => (h13 x (hB₁ hx) y hy).symm
    · rw [Subgroup.mem_centralizer_iff]
      exact fun y hy => (h23 x (hB₂ hx) y hy).symm
  have hc3 : ∀ x ∈ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂, ∀ y ∈ Subgroup.zpowers a₃,
      x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hB12 hx) y (hB₃ hy)).symm
  have hi3 : (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂) ⊓ Subgroup.zpowers a₃ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hz₃ x hx.2 fun y hy => (Subgroup.mem_centralizer_iff.mp (hB12 hx.1) y hy).symm
  have r1 := pRank_add_le_pRank_sup' hp hc12 hi12
  have r2 := pRank_add_le_pRank_sup' hp hc3 hi3
  have e1 := one_le_pRank_zpowers hp ho₁
  have e2 := one_le_pRank_zpowers hp ho₂
  have e3 := one_le_pRank_zpowers hp ho₃
  have hm := CFSG.SectionRank.pRank_mono (p := p) hp.one_lt
    (le_top : (Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂) ⊔ Subgroup.zpowers a₃ ≤ ⊤)
  omega

end Rank

section Order

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem card_quotient_dvd_of_sup_eq_top {N B : Subgroup X} [N.Normal] (h : B ⊔ N = ⊤) :
    Nat.card (X ⧸ N) ∣ Nat.card B := by
  have htop : B.map (QuotientGroup.mk' N) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hle : B ⊔ N ≤ (B.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
      refine sup_le (Subgroup.le_comap_map _ _) fun n hn => ?_
      rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff n).mpr hn]
      exact Subgroup.one_mem _
    exact hle (h ▸ Subgroup.mem_top x)
  rw [← Subgroup.card_top (G := X ⧸ N), ← htop]
  exact Subgroup.card_map_dvd (H := B) _

omit [Finite X] in
theorem card_dvd_card_quotient_of_inf_eq_bot {N K : Subgroup X} [N.Normal] (h : K ⊓ N = ⊥) :
    Nat.card K ∣ Nat.card (X ⧸ N) := by
  refine Subgroup.card_dvd_of_injective ((QuotientGroup.mk' N).comp K.subtype) ?_
  rw [injective_iff_map_eq_one]
  intro k hk
  have hkN : (k : X) ∈ N := (QuotientGroup.eq_one_iff _).mp hk
  have hk' : (k : X) ∈ K ⊓ N := ⟨k.2, hkN⟩
  rw [h, Subgroup.mem_bot] at hk'
  exact Subtype.ext hk'

end Order

section PSL

variable {p : ℕ} [hp : Fact p.Prime]

theorem twentyfour_dvd (h24 : p % 24 = 11 ∨ p % 24 = 13) : 24 ∣ p ^ 2 - 1 := by
  have h := Nat.pow_mod p 2 24
  have h1 : p ^ 2 % 24 = 1 := by
    rcases h24 with h' | h' <;> rw [h'] at h <;> simpa using h
  have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
  generalize p ^ 2 = q at h1 h2 ⊢
  omega

theorem twelve_mul_dvd_card (h24 : p % 24 = 11 ∨ p % 24 = 13) :
    12 * p ∣ Nat.card PSL(2, ZMod p) := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  rw [CFSG.GorensteinWalter.psl2_card_formula (ZMod p) (C10P34.isOddPrimePower_card hp2),
    Nat.card_zmod]
  obtain ⟨m, hm⟩ := twentyfour_dvd h24
  rw [hm, show p * (24 * m) = 2 * (12 * p * m) by ring, Nat.mul_div_cancel_left _ two_pos]
  exact Dvd.intro m rfl

theorem twelve_mul_dvd_card_of {Y : Type*} [Group Y] [Finite Y]
    (h24 : p % 24 = 11 ∨ p % 24 = 13) (e : Y ⧸ CFSG.pCore 2 Y ≃* PSL(2, ZMod p)) :
    12 * p ∣ Nat.card Y :=
  ((Nat.card_congr e.toEquiv).symm ▸ twelve_mul_dvd_card h24).trans
    (Subgroup.card_quotient_dvd_card _)

theorem isSimpleGroup_psl2 (h24 : p % 24 = 11 ∨ p % 24 = 13) : IsSimpleGroup PSL(2, ZMod p) :=
  Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)

theorem exists_mul_ne_mul_psl2 {A : Type*} [Group A] (h24 : p % 24 = 11 ∨ p % 24 = 13)
    (e : A ≃* PSL(2, ZMod p)) : ∃ a b : A, a * b ≠ b * a := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  have hcen := C10P34.center_eq_bot_of_mulEquiv e
  have htop : Subgroup.center A = ⊤ := by
    rw [eq_top_iff]
    intro a _
    rw [Subgroup.mem_center_iff]
    exact fun b => hc b a
  have h2 := twelve_mul_dvd_card h24 (p := p)
  rw [← Nat.card_congr e.toEquiv, ← Subgroup.card_top (G := A), ← htop, hcen,
    Subgroup.card_bot] at h2
  have := Nat.le_of_dvd one_pos h2
  have := hp.out.two_le
  omega

theorem eq_bot_of_normal_of_odd {Y : Type*} [Group Y] [Finite Y]
    (h24 : p % 24 = 11 ∨ p % 24 = 13) (e : Y ⧸ CFSG.pCore 2 Y ≃* PSL(2, ZMod p))
    {N : Subgroup Y} [hN : N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_psl2 h24 (p := p)
  set π : Y →* PSL(2, ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 Y)) with hπ
  have hsurj : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have := hN.map π hsurj
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · have hle : N ≤ CFSG.pCore 2 Y := by
      intro n hn
      have h1 : π n ∈ N.map π := Subgroup.mem_map_of_mem π hn
      rw [h, Subgroup.mem_bot, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    obtain ⟨k, hk⟩ := ((CFSG.pCore_isPGroup (p := 2) (G := Y)).to_le hle).exists_card_eq
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq N (by simpa using hk)
    · rw [hk, pow_succ] at hodd
      exact absurd hodd (by simp [Nat.odd_mul])
  · exfalso
    have h1 := Subgroup.card_map_dvd (H := N) π
    rw [h, Subgroup.card_top] at h1
    have h3 : 2 ∣ Nat.card N :=
      ((Dvd.intro (6 * p) (by ring)).trans (twelve_mul_dvd_card h24 (p := p))).trans h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h3)

end PSL

theorem eq_three_or_seven {Y : Type*} [Group Y] [Finite Y]
    (e : Y ⧸ CFSG.pCore 2 Y ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hd : r ∣ Nat.card Y) : r = 3 ∨ r = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 Y),
    Nat.card_congr e.toEquiv, card_Γ] at hd
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  rw [hk, show (168 : ℕ) = 2 ^ 3 * 3 * 7 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
  · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hr).mp h with h | h
      · exact absurd (hr.dvd_of_dvd_pow h) h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h)
  · exact absurd (hr.dvd_of_dvd_pow h) h2

theorem five_dvd_card_of_isSL2 {X : Type} [Group X] (h : IsSL2 5 X) : 5 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field, Fin.prod_univ_two, ZMod.card]
  norm_num

end CFSG.Quasithin.Vol2.Ch10.SecB.E9
