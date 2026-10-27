module

public import CFSG.RankThree.SubgroupLists.SchurCommutant
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.RankThree.SubgroupLists
open scoped Matrix

theorem nk_exists_fixed_vector {E : Type} [Field E] [Finite E] [CharP E 2] {n : ℕ} (hn : 0 < n)
    (R : Subgroup (GL (Fin n) E)) (hR : IsPGroup 2 R) :
    ∃ w : Fin n → E, w ≠ 0 ∧ ∀ r ∈ R, (r : Matrix (Fin n) (Fin n) E) *ᵥ w = w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : MulAction ↥R (Fin n → E) :=
    { smul := fun r w => ((r : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ w
      one_smul := fun w => by
        show ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ w = w
        simp
      mul_smul := fun r s w => by
        show (((r : GL (Fin n) E) * (s : GL (Fin n) E) : GL (Fin n) E) :
            Matrix (Fin n) (Fin n) E) *ᵥ w =
          ((r : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ
            (((s : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ w)
        rw [Units.val_mul, Matrix.mulVec_mulVec] }
  have h2 : 2 ∣ Nat.card (Fin n → E) := by
    haveI := Fintype.ofFinite E
    obtain ⟨m, -, hm⟩ := FiniteField.card E 2
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hm]
    exact dvd_pow (dvd_pow_self 2 (PNat.ne_zero m)) (by omega)
  have h0 : (0 : Fin n → E) ∈ MulAction.fixedPoints ↥R (Fin n → E) := by
    intro r
    show ((r : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ 0 = 0
    simp
  obtain ⟨b, hb, hb0⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin n → E) h2 h0
  refine ⟨b, fun h => hb0 h.symm, fun r hr => ?_⟩
  exact hb ⟨r, hr⟩

theorem nk_two_group_trivial {E : Type} [Field E] [Finite E] [CharP E 2] {n : ℕ}
    (N R : Subgroup (GL (Fin n) E)) (hirr : IsIrreducibleOn N) (hR : IsPGroup 2 R)
    (hnorm : ∀ g ∈ N, ∀ r ∈ R, g⁻¹ * r * g ∈ R) : R = ⊥ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : Subsingleton (GL (Fin 0) E) := inferInstance
    exact Subsingleton.elim _ _
  obtain ⟨w₀, hw₀, hfix⟩ := nk_exists_fixed_vector hn R hR
  let U : Submodule E (Fin n → E) :=
    { carrier := {w | ∀ r ∈ R, (r : Matrix (Fin n) (Fin n) E) *ᵥ w = w}
      add_mem' := fun {a b} ha hb r hr => by
        rw [Matrix.mulVec_add, ha r hr, hb r hr]
      zero_mem' := fun r _ => by simp
      smul_mem' := fun c a ha r hr => by
        rw [Matrix.mulVec_smul, ha r hr] }
  have hUinv : ∀ g ∈ N, ∀ w ∈ U, (g : Matrix (Fin n) (Fin n) E) *ᵥ w ∈ U := by
    intro g hg w hw r hr
    have h1 := hnorm g hg r hr
    have h2 := hw _ h1
    have e : (r : Matrix (Fin n) (Fin n) E) *ᵥ ((g : Matrix (Fin n) (Fin n) E) *ᵥ w) =
        (g : Matrix (Fin n) (Fin n) E) *ᵥ (((g⁻¹ * r * g : GL (Fin n) E) :
          Matrix (Fin n) (Fin n) E) *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      simp [Units.val_mul, mul_assoc]
    rw [e, h2]
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply hw₀
    have : w₀ ∈ U := hfix
    rw [hbot, Submodule.mem_bot] at this
    exact this
  have hUtop : U = ⊤ := (hirr U hUinv).resolve_left hUne
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hall : ∀ w : Fin n → E, (r : Matrix (Fin n) (Fin n) E) *ᵥ w = w := by
    intro w
    have : w ∈ U := by rw [hUtop]; exact Submodule.mem_top
    exact this r hr
  apply Units.ext
  apply Matrix.ext
  intro i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.one_apply, Pi.single_apply, Matrix.mulVec_single_one] using this

theorem nk_centralizer_odd_order {E : Type} [Field E] [Finite E] [CharP E 2] {n : ℕ}
    (N : Subgroup (GL (Fin n) E)) (hirr : IsIrreducibleOn N) (c : GL (Fin n) E)
    (hc : ∀ g ∈ N, c * g = g * c) : Odd (orderOf c) := by
  haveI : Finite (GL (Fin n) E) := inferInstance
  have hpos : 0 < orderOf c := orderOf_pos c
  obtain ⟨a, r, hr, hor⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hrdvd : r ∣ orderOf c := ⟨2 ^ a, by rw [hor]; ring⟩
  have hord2 : orderOf (c ^ r) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hr.pos.ne' hrdvd, hor]
    exact Nat.mul_div_cancel _ hr.pos
  have hR : IsPGroup 2 (Subgroup.zpowers (c ^ r)) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hord2])
  have hcomm : ∀ g ∈ N, ∀ k : ℤ, g⁻¹ * (c ^ r) ^ k * g = (c ^ r) ^ k := by
    intro g hg k
    have h1 : Commute (c ^ r) g := ((Commute.pow_left (show Commute c g from hc g hg) r))
    have h2 : Commute ((c ^ r) ^ k) g := h1.zpow_left k
    calc g⁻¹ * (c ^ r) ^ k * g = g⁻¹ * ((c ^ r) ^ k * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * (c ^ r) ^ k) := by rw [h2.eq]
      _ = (c ^ r) ^ k := by simp
  have hnorm : ∀ g ∈ N, ∀ x ∈ Subgroup.zpowers (c ^ r), g⁻¹ * x * g ∈ Subgroup.zpowers (c ^ r) := by
    intro g hg x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [hcomm g hg k]
    exact Subgroup.zpow_mem_zpowers _ _
  have hbot := nk_two_group_trivial N _ hirr hR hnorm
  have hone : c ^ r = 1 := by
    have : c ^ r ∈ Subgroup.zpowers (c ^ r) := Subgroup.mem_zpowers _
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have ha : 2 ^ a = 1 := by
    rw [← hord2, hone, orderOf_one]
  have ha0 : a = 0 := by
    by_contra hne
    have : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hor, ha0, pow_zero, one_mul]
  exact hr

end CFSG.Quasithin.H13.L829NK
