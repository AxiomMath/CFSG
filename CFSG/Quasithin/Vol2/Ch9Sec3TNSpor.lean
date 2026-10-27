module

public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.Quasithin.Background.A318POutMore
public import CFSG.Quasithin.Background.A318PQR2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveQ5
public import CFSG.Quasithin.H13.NQCatT513Inner

public section

namespace CFSG.Quasithin.H13.Ch9.TN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem three_inner_of_not_dvd {X : Type} [Group X] [Finite X]
    (h : ¬ 3 ∣ Nat.card (Outer X)) :
    ∀ α : MulAut X, α ^ 3 = 1 → ∃ x : X, α = MulAut.conj x := by
  intro α hα
  have : Finite (Outer X) := A318P.finite_outer X
  have h1 : (QuotientGroup.mk α : Outer X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk α : Outer X) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk α : Outer X) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp h2 with h' | h'
    · exact h'
    · exact absurd (h' ▸ orderOf_dvd_natCard _) h
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  obtain ⟨x, hx⟩ := h3
  exact ⟨x, hx.symm⟩

theorem three_inner_of_quot {X M : Type} [Group X] [Group M] (hX : Group.IsPerfect X)
    (e : X ⧸ Subgroup.center X ≃* M)
    (hM : ∀ β : MulAut M, Odd (orderOf β) → ∃ x : M, β = MulAut.conj x) :
    ∀ α : MulAut X, α ^ 3 = 1 → ∃ x : X, α = MulAut.conj x := by
  intro α hα
  set β : MulAut M := MulAut.congr e (NQCat.T513P.descZ X α) with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, ← map_pow, hα, map_one, map_one]
  have hβo : Odd (orderOf β) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hβ3)
  obtain ⟨m, hm⟩ := hM β hβo
  have hmem : NQCat.T513P.descZ X α ∈ inner (X ⧸ Subgroup.center X) := by
    refine ⟨e.symm m, ?_⟩
    apply MulEquiv.ext
    intro y
    have h1 := congrArg (fun γ : MulAut M => γ (e y)) hm
    simp only [hβ, MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply] at h1
    apply e.injective
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1.symm
  obtain ⟨x, hx⟩ := NQCat.T513P.mem_inner_of_descZ_mem_inner hX hmem
  exact ⟨x, hx.symm⟩

theorem exists_not_commute_of_a5 {Y : Type} [Group Y] {L B : Subgroup Y} (hBL : B ≤ L)
    (hA5 : IsAlt 5 (ModO2 B)) {b : Y} (hbB : b ∈ B) (hb3 : orderOf b = 3) :
    ∃ l ∈ L, l * b ≠ b * l := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  obtain ⟨e⟩ := hA5
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥B) with hπ
  have hc : ∀ g : ModO2 B, π ⟨b, hbB⟩ * g = g * π ⟨b, hbB⟩ := by
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h g' (hBL g'.2)).symm
  have hcen : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have he : e (π ⟨b, hbB⟩) ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, hc]
  rw [hcen, Subgroup.mem_bot, MulEquiv.map_eq_one_iff, hπ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at he
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) ⟨_, he⟩
  have hbk : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val (congrArg Subtype.val hk)
  have h1 := orderOf_dvd_of_pow_eq_one hbk
  rw [hb3] at h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

theorem exists_center_three_of_card {Y : Type} [Group Y] {L : Subgroup Y} [Finite ↥L]
    (h : Nat.card (Subgroup.center ↥L) = 3) :
    ∃ z ∈ L, (∀ l ∈ L, l * z = z * l) ∧ z ≠ 1 ∧ z ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 3 (by rw [h])
  refine ⟨((z : ↥L) : Y), (z : ↥L).2, fun l hl => ?_, fun h1 => ?_, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨l, hl⟩)
  · have : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hz
    omega
  · have h3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    simpa using congrArg (fun t : ↥(Subgroup.center ↥L) => ((t : ↥L) : Y)) h3

section Cases


theorem center_or_inner_of_a314 {Y : Type} [Group Y] [Finite Y] {T B L : Subgroup Y}
    (hLp : ⁅L, L⁆ = L) (h314 : A314Statement T B L)
    (hLie : ¬ (IsPSL 3 2 2 ↥L ∨ IsSL3 4 ↥L ∨ IsPSp4 2 2 ↥L ∨ IsG2 2 2 ↥L ∨ Is3D4 2 2 ↥L)) :
    ((∃ z ∈ L, (∀ l ∈ L, l * z = z * l) ∧ z ≠ 1 ∧ z ^ 3 = 1) ∨
      ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ x : ↥L, α = MulAut.conj x) ∨
    ((IsSL2 5 ↥B ∧ (IsPSLEps3 false 5 1 ↥L ∨ IsSLEps3 false 5 ↥L) ∧
        B = perfectCore (L ⊓ Subgroup.centralizer (pCoreOf 2 B : Set Y))) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L))) := by
  have hinn : ¬ 3 ∣ Nat.card (Outer ↥L) →
      ((∃ z ∈ L, (∀ l ∈ L, l * z = z * l) ∧ z ≠ 1 ∧ z ^ 3 = 1) ∨
        ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ x : ↥L, α = MulAut.conj x) := fun h =>
    Or.inr (three_inner_of_not_dvd h)
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have h32 : (3 : ℕ) ≠ 2 := by norm_num
  have hLperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  rcases h314 with ⟨-, -, h1, -⟩ | ⟨-, hL, -⟩ | ⟨-, hL⟩ | ⟨hB5, ⟨s, hL⟩, hB⟩ | ⟨-, hL, -⟩ |
    ⟨-, -, -, hL⟩ | ⟨-, -, -, hL⟩ | ⟨-, hL, -⟩ | ⟨-, hL, -⟩ | ⟨-, -, hL⟩ |
    ⟨-, hL, -⟩ | ⟨-, -, hL, -⟩ | h13 | h14
  · exact absurd h1 hLie
  · rcases hL with hL | ⟨-, hc, -⟩
    · obtain ⟨e⟩ := hL
      exact Or.inl (hinn (A318P.not_dvd_outer_alternating (Or.inr le_rfl) e hp3 h32))
    · exact Or.inl (Or.inl (exists_center_three_of_card hc))
  · rcases hL with hL | ⟨p, -, -, -, hL⟩
    · exact Or.inl (hinn (A318P.not_dvd_outer_psl_two_odd (Or.inr rfl) hL hp3 h32))
    · exact Or.inl (hinn (A318P.not_dvd_outer_psl_two_odd (Or.inl rfl) hL hp3 h32))
  · cases s with
    | false => exact Or.inr (Or.inl ⟨hB5, hL, hB⟩)
    | true =>
      obtain ⟨e⟩ := FiveNorm.quot_G35_of hL
      exact Or.inl (Or.inr (three_inner_of_quot hLperf e NQCat.T513.inner_of_odd_sl35))
  · obtain ⟨e⟩ := FiveNorm.quot_G35_of hL
    exact Or.inl (Or.inr (three_inner_of_quot hLperf e NQCat.T513.inner_of_odd_sl35))
  · rcases hL with hL | ⟨-, hc, -⟩
    · obtain ⟨e⟩ := hL
      exact Or.inl (hinn (A318P.not_dvd_outer_M22 e hp3 h32))
    · exact Or.inl (Or.inl (exists_center_three_of_card hc))
  · obtain ⟨e⟩ := hL
    exact Or.inl (hinn (A318P.not_dvd_outer_M23 e hp3 h32))
  · obtain ⟨e⟩ := hL
    exact Or.inl (hinn (A318P.not_dvd_outer_J1 e hp3 h32))
  · obtain ⟨e⟩ := hL
    exact Or.inl (hinn (A318P.not_dvd_outer_J2 e hp3 h32))
  · obtain ⟨e⟩ := hL
    exact Or.inl (hinn (A318P.not_dvd_outer_J4 e qSporOutTwo_holds hp3 h32))
  · obtain ⟨e⟩ := hL
    exact Or.inl (hinn (A318P.not_dvd_outer_HS e hp3 h32))
  · obtain ⟨e⟩ := hL
    exact Or.inl (hinn (A318P.not_dvd_outer_Ru e hp3 h32))
  · exact Or.inr (Or.inr (Or.inl h13))
  · exact Or.inr (Or.inr (Or.inr h14))

end Cases

end CFSG.Quasithin.H13.Ch9.TN
