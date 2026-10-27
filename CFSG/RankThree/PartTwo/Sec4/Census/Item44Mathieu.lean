module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Sections
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Blueprint CFSG.Sporadic.Mathieu Subgroup

theorem card_m12_eq : Nat.card NativeSporadic.M12 = 95040 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M12.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M12.toNative_surjective).trans hle) CFSG.Sporadic.Bridge.M12.le_card_native

@[expose] def m12y : NativeSporadic.M12 := m12a * m12b

@[expose] def m12g : NativeSporadic.M12 :=
  [m12b, m12a, m12b, m12a, m12b, m12a, m12b, m12a, m12b, m12a, m12b, m12b, m12a, m12b, m12a, m12b,
    m12a, m12b, m12b, m12a, m12b, m12a, m12b, m12b, m12a, m12b, m12b, m12a, m12b, m12a, m12b, m12a,
    m12b, m12a, m12b, m12a].prod

theorem m12y_pow_eleven : m12y ^ 11 = 1 := by decide +kernel

theorem m12y_ne_one : m12y ≠ 1 := by decide +kernel

theorem m12g_mul_m12y : m12g * m12y = m12y ^ 5 * m12g := by decide +kernel

theorem isEmpty_mulEquiv_m12 {p : ℕ} [Fact p.Prime] {X Y : Type*} [Group X] [Finite X]
    [Group Y] (ρ : X →* GL (Fin 4) (ZMod p)) (π : X →* Y)
    (hπ : Function.Surjective π) (hker : ρ.ker ≤ π.ker) :
    IsEmpty (Y ≃* NativeSporadic.M12) := by
  refine ⟨fun e => ?_⟩
  by_cases hp : p = 11
  · subst hp
    have h1 := card_dvd_card_of_ker_le ρ π hπ hker
    rw [Nat.card_congr e.toEquiv, card_m12_eq, Matrix.card_GL_field, ZMod.card,
      Fin.prod_univ_four] at h1
    norm_num at h1
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    have hy : orderOf (e.symm m12y) = 11 := by
      rw [MulEquiv.orderOf_eq]
      exact orderOf_eq_prime m12y_pow_eleven m12y_ne_one
    have hgy : e.symm m12g * e.symm m12y = e.symm m12y ^ 5 * e.symm m12g := by
      rw [← map_mul, m12g_mul_m12y, map_mul, map_pow]
    obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_modEq_one (r := 11) (by norm_num) (Ne.symm hp)
      ρ π hπ hker hy hgy
    interval_cases k <;> revert hk <;> decide

theorem card_m22_eq : Nat.card NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle) CFSG.Sporadic.Bridge.M22.le_card_native

@[expose] def m22y : NativeSporadic.M22 := m22a * m22b

@[expose] def m22g : NativeSporadic.M22 :=
  [m22b, m22b, m22a, m22b, m22b, m22a, m22b, m22a, m22b, m22a, m22b, m22b, m22a, m22b, m22a, m22b,
    m22a, m22b, m22a, m22b, m22b, m22b, m22a, m22b, m22b, m22a].prod

theorem m22y_pow_eleven : m22y ^ 11 = 1 := by decide +kernel

theorem m22y_ne_one : m22y ≠ 1 := by decide +kernel

theorem m22g_mul_m22y : m22g * m22y = m22y ^ 4 * m22g := by decide +kernel

theorem isEmpty_mulEquiv_m22_of_ne {p : ℕ} [Fact p.Prime] (hp11 : p ≠ 11) {X Y : Type*}
    [Group X] [Finite X] [Group Y] (ρ : X →* GL (Fin 4) (ZMod p)) (π : X →* Y)
    (hπ : Function.Surjective π) (hker : ρ.ker ≤ π.ker) :
    IsEmpty (Y ≃* NativeSporadic.M22) := by
  refine ⟨fun e => ?_⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hy : orderOf (e.symm m22y) = 11 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime m22y_pow_eleven m22y_ne_one
  have hgy : e.symm m22g * e.symm m22y = e.symm m22y ^ 4 * e.symm m22g := by
    rw [← map_mul, m22g_mul_m22y, map_mul, map_pow]
  obtain ⟨k, hk1, hk4, hk⟩ := exists_pow_modEq_one (r := 11) (by norm_num) (Ne.symm hp11)
    ρ π hπ hker hy hgy
  interval_cases k <;> revert hk <;> decide

theorem isEmpty_mulEquiv_m22 {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (ρ : X →* GL (Fin 4) (ZMod p))
    (hdet : ∀ x, (ρ x : Matrix (Fin 4) (Fin 4) (ZMod p)).det = 1) {N : Subgroup X} [N.Normal]
    (hN : ρ.ker ≤ N) (hZ : Nat.card (center (X ⧸ N)) = 4) :
    IsEmpty ((X ⧸ N) ⧸ center (X ⧸ N) ≃* NativeSporadic.M22) := by
  refine ⟨fun e => ?_⟩
  by_cases hp : p = 11
  · subst hp
    have h1 := index_dvd_card_of_ker_le (N := N) (glToSL ρ hdet) (by rw [ker_glToSL]; exact hN)
    have h2 : N.index = 443520 * 4 := by
      rw [Subgroup.index, Subgroup.card_eq_card_quotient_mul_card_subgroup (center (X ⧸ N)),
        Nat.card_congr e.toEquiv, card_m22_eq, hZ]
    rw [h2, Matrix.card_SL_field, ZMod.card, Fin.prod_univ_four] at h1
    norm_num at h1
  · exact (isEmpty_mulEquiv_m22_of_ne hp ρ
      ((QuotientGroup.mk' (center (X ⧸ N))).comp (QuotientGroup.mk' N))
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
      (fun x hx => by
        have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr (hN hx)
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1, map_one])).false e

end CFSG.RankThree.PartTwo.Sec4.Census
