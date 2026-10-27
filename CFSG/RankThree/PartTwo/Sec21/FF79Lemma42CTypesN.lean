module

public import CFSG.GroupTheory.GL52.OrderThreeCover

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.GroupTheory.GL52 Matrix

variable {G : Type} [Group G]

theorem count_trace_one : (Finset.univ.filter fun p : Fin 3 × Fin 3 =>
    ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ) ≠ 1 ∧
    Matrix.trace (ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ)) = 1).card = 4 := by
  decide +kernel

theorem count_trace_zero : (Finset.univ.filter fun p : Fin 3 × Fin 3 =>
    ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ) ≠ 1 ∧
    Matrix.trace (ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ)) = 0).card = 4 := by
  decide +kernel

theorem inj_pow_pow : ∀ p q : Fin 3 × Fin 3,
    ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ) = ord3T2M ^ (q.1 : ℕ) * syl3TbM ^ (q.2 : ℕ) →
    p = q := by
  decide +kernel

@[expose] def e9Elt (p : Fin 3 × Fin 3) : G52 := ord3T2 ^ (p.1 : ℕ) * syl3Tb ^ (p.2 : ℕ)

theorem coe_e9Elt (p : Fin 3 × Fin 3) :
    ((e9Elt p : G52) : M5) = ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ) := by
  rw [e9Elt, Units.val_mul, syl3_pow_matrix_a, syl3_pow_matrix_b]

theorem e9Elt_mem (p : Fin 3 × Fin 3) : e9Elt p ∈ syl3R :=
  mul_mem (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
    (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)

theorem e9Elt_injective : Function.Injective e9Elt := fun p q h => by
  refine inj_pow_pow p q ?_
  rw [← coe_e9Elt, ← coe_e9Elt, h]

theorem e9Elt_surj {s : G52} (hs : s ∈ syl3R) : ∃ p, e9Elt p = s := by
  obtain ⟨i, hi, j, hj, rfl⟩ := syl3_mem_R hs
  exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩

theorem card_subtype_param {α β : Type} (ρ : α → β) (hinj : Function.Injective ρ) (S : Set β)
    (hS : ∀ b, b ∈ S ↔ ∃ a, ρ a = b) (P : β → Prop) :
    Nat.card {b : β // b ∈ S ∧ P b} = Nat.card {a : α // P (ρ a)} := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨ρ a.1, (hS _).mpr ⟨a.1, rfl⟩, a.2⟩)
    ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)), ?_⟩)
  rintro ⟨b, hbS, hb⟩
  obtain ⟨a, rfl⟩ := (hS b).mp hbS
  exact ⟨⟨a, hb⟩, rfl⟩

theorem zmod_two_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

theorem card_trace {J R : Subgroup G} (e : ↥J ≃* G52) (hRJ : R ≤ J) (hRcard : Nat.card R = 9)
    (t : ZMod 2) :
    Nat.card {x : G // x ∈ R ∧ x ≠ 1 ∧ ∃ hx : x ∈ J, Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = t}
      = 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R' : Subgroup G52 := (R.subgroupOf J).map e.toMonoidHom
  have hmem : ∀ r : ↥J, e r ∈ R' ↔ (r : G) ∈ R := by
    intro r
    constructor
    · rintro ⟨w, hw, hwr⟩
      have : w = r := e.injective hwr
      subst this
      exact hw
    · intro hr
      exact ⟨r, hr, rfl⟩
  have hR'card : Nat.card R' = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ).toEquiv, hRcard]
    norm_num
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2) (H := R') hR'card
    (fun P => by rw [syl3_card_sylow P]; norm_num)
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_eq_of_card_pow (p := 3) (k := 2) (H := syl3R)
    (by rw [syl3_card_R]; norm_num) (fun P => by rw [syl3_card_sylow P]; norm_num)
  obtain ⟨c, hc⟩ := exists_eq_map_conj_sylow Q₀ Q
  have hR'eq : R' = syl3R.map (MulAut.conj c).toMonoidHom := by rw [← hQ, hc, hQ₀]
  let ρ : Fin 3 × Fin 3 → G := fun p => ((e.symm (c * e9Elt p * c⁻¹) : ↥J) : G)
  have hρe : ∀ p, e (e.symm (c * e9Elt p * c⁻¹)) = c * e9Elt p * c⁻¹ :=
    fun p => e.apply_symm_apply _
  have hρR : ∀ p, ρ p ∈ R := fun p => (hmem _).mp (by
    rw [hρe, hR'eq]
    exact ⟨e9Elt p, e9Elt_mem p, rfl⟩)
  have hρinj : Function.Injective ρ := fun p q h => by
    have h1 : e.symm (c * e9Elt p * c⁻¹) = e.symm (c * e9Elt q * c⁻¹) := Subtype.ext h
    have h2 := e.symm.injective h1
    exact e9Elt_injective (mul_left_cancel (mul_right_cancel h2))
  have hρsurj : ∀ r ∈ R, ∃ p, ρ p = r := by
    intro r hr
    have hrJ := hRJ hr
    have h1 : e ⟨r, hrJ⟩ ∈ R' := (hmem ⟨r, hrJ⟩).mpr hr
    rw [hR'eq] at h1
    obtain ⟨s, hs, hsr⟩ := h1
    obtain ⟨p, rfl⟩ := e9Elt_surj hs
    refine ⟨p, ?_⟩
    have hsr' : c * e9Elt p * c⁻¹ = e ⟨r, hrJ⟩ := hsr
    show ((e.symm (c * e9Elt p * c⁻¹) : ↥J) : G) = r
    rw [hsr', e.symm_apply_apply]
  have hρtr : ∀ p (h : ρ p ∈ J), e ⟨ρ p, h⟩ = c * e9Elt p * c⁻¹ := fun p h => by
    have : (⟨ρ p, h⟩ : ↥J) = e.symm (c * e9Elt p * c⁻¹) := Subtype.ext rfl
    rw [this, e.apply_symm_apply]
  have hρtrace : ∀ p, Matrix.trace ((c * e9Elt p * c⁻¹ : G52) : M5) =
      Matrix.trace ((e9Elt p : G52) : M5) := fun p =>
    trace_eq_of_isConj (isConj_iff.mpr ⟨c, rfl⟩)
  have hρone : ∀ p, ρ p ≠ 1 ↔ (ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ)) ≠ 1 := by
    intro p
    rw [← coe_e9Elt, Ne, Ne, Units.val_eq_one]
    refine not_congr ?_
    constructor
    · intro h
      have h1 : (e.symm (c * e9Elt p * c⁻¹) : ↥J) = 1 := Subtype.ext h
      have h2 : c * e9Elt p * c⁻¹ = 1 := by simpa using h1
      simpa using h2
    · intro h
      have h2 : c * e9Elt p * c⁻¹ = 1 := by rw [h]; group
      have h1 : (e.symm (c * e9Elt p * c⁻¹) : ↥J) = 1 := by rw [h2]; simp
      exact congrArg Subtype.val h1
  have hS : ∀ x, x ∈ R ↔ ∃ p, ρ p = x := fun x =>
    ⟨hρsurj x, fun ⟨p, hp⟩ => hp ▸ hρR p⟩
  refine (card_subtype_param ρ hρinj (R : Set G) hS (fun x => x ≠ 1 ∧ ∃ hx : x ∈ J,
    Matrix.trace ((e ⟨x, hx⟩ : G52) : M5) = t)).trans ?_
  have key : Nat.card {p : Fin 3 × Fin 3 // ρ p ≠ 1 ∧ ∃ hx : ρ p ∈ J,
      Matrix.trace ((e ⟨ρ p, hx⟩ : G52) : M5) = t} =
      Nat.card {p : Fin 3 × Fin 3 // (ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ)) ≠ 1 ∧
        Matrix.trace (ord3T2M ^ (p.1 : ℕ) * syl3TbM ^ (p.2 : ℕ)) = t} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
    rw [hρone]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨hx, h⟩
      rw [hρtr p hx, hρtrace, coe_e9Elt] at h
      exact h
    · intro h
      refine ⟨(e.symm (c * e9Elt p * c⁻¹)).2, ?_⟩
      rw [hρtr p _, hρtrace, coe_e9Elt]
      exact h
  have ht : t = 0 ∨ t = 1 := zmod_two_cases t
  rw [key]
  rcases ht with rfl | rfl
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact count_trace_zero
  · simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact count_trace_one

end CFSG.RankThree.PartTwo.Sec21.FF79
