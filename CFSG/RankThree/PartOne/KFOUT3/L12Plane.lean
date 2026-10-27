module

public import CFSG.RankThree.PartOne.KF.R9Plane
public import CFSG.RankThree.PartOne.KF.R9Perm

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K]

@[expose] def torusPi (K : Type) [Field K] : Subgroup (Fin 5 → Kˣ) where
  carrier := {d | (∀ i, d i ^ 5 = 1) ∧ ∏ i, d i = 1 ∧ d 0 = d 1}
  mul_mem' := fun {a b} ha hb => ⟨fun i => by simp [mul_pow, ha.1 i, hb.1 i],
    by simp [Finset.prod_mul_distrib, ha.2.1, hb.2.1], by simp [ha.2.2, hb.2.2]⟩
  one_mem' := ⟨fun i => by simp, by simp, rfl⟩
  inv_mem' := fun {a} ha => ⟨fun i => by simp [inv_pow, ha.1 i],
    by simp [Finset.prod_inv_distrib, ha.2.1], by simp [ha.2.2]⟩

@[expose] def piGL (K : Type) [Field K] : Subgroup (GL (Fin 5) K) := (torusPi K).map diagUHom

@[expose] def piSU (f : ℕ) (K : Type) [Field K] : Subgroup ↥(unitarySU 2 f K 5) :=
  (piGL K).subgroupOf (unitarySU 2 f K 5)

theorem mem_piGL_iff {g : GL (Fin 5) K} :
    g ∈ piGL K ↔ ∃ d : Fin 5 → Kˣ, (∀ i, d i ^ 5 = 1) ∧ ∏ i, d i = 1 ∧ d 0 = d 1 ∧
      diagU d = g := by
  constructor
  · rintro ⟨d, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨d, h1, h2, h3, rfl⟩
  · rintro ⟨d, h1, h2, h3, rfl⟩
    exact ⟨d, ⟨h1, h2, h3⟩, rfl⟩

theorem eq_of_sq_eq_of_pow_five {x y : Kˣ} (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (h : x * x = y * y) :
    x = y := by
  calc x = x ^ 5 * ((x * x)⁻¹) ^ 2 := by group
    _ = y ^ 5 * ((y * y)⁻¹) ^ 2 := by rw [hx, hy, h]
    _ = y := by group

theorem card_torusPi_le [Finite K] : Nat.card (torusPi K) ≤ 5 ^ 3 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let φ : torusPi K → (Fin 3 → rootsOfUnity 5 K) := fun d i =>
    ⟨d.1 ⟨i.val + 2, by omega⟩, (mem_rootsOfUnity 5 _).mpr (d.2.1 _)⟩
  have hφ : Function.Injective φ := by
    intro d e hde
    have h2 : d.1 2 = e.1 2 := congrArg (fun x : rootsOfUnity 5 K => (x : Kˣ)) (congrFun hde 0)
    have h3 : d.1 3 = e.1 3 := congrArg (fun x : rootsOfUnity 5 K => (x : Kˣ)) (congrFun hde 1)
    have h4 : d.1 4 = e.1 4 := congrArg (fun x : rootsOfUnity 5 K => (x : Kˣ)) (congrFun hde 2)
    have hd := d.2.2.1
    have he := e.2.2.1
    rw [Fin.prod_univ_five] at hd he
    have hd01 := d.2.2.2
    have he01 := e.2.2.2
    rw [hd01, h2, h3, h4] at hd
    rw [he01] at he
    have hx : d.1 1 = e.1 1 := by
      refine eq_of_sq_eq_of_pow_five (d.2.1 1) (e.2.1 1) ?_
      have hd' : (d.1 1 * d.1 1) * (e.1 2 * e.1 3 * e.1 4) = 1 := by
        rw [show (d.1 1 * d.1 1) * (e.1 2 * e.1 3 * e.1 4) =
          d.1 1 * d.1 1 * e.1 2 * e.1 3 * e.1 4 by group]
        exact hd
      have he' : (e.1 1 * e.1 1) * (e.1 2 * e.1 3 * e.1 4) = 1 := by
        rw [show (e.1 1 * e.1 1) * (e.1 2 * e.1 3 * e.1 4) =
          e.1 1 * e.1 1 * e.1 2 * e.1 3 * e.1 4 by group]
        exact he
      exact mul_right_cancel (hd'.trans he'.symm)
    apply Subtype.ext
    funext k
    fin_cases k
    · exact hd01.trans (hx.trans he01.symm)
    · exact hx
    · exact h2
    · exact h3
    · exact h4
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card (Fin 3 → rootsOfUnity 5 K) = Nat.card (rootsOfUnity 5 K) ^ 3 := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h3 : Nat.card (rootsOfUnity 5 K) ≤ 5 := card_rootsOfUnity K 5
  calc Nat.card (torusPi K) ≤ Nat.card (Fin 3 → rootsOfUnity 5 K) := h1
    _ = Nat.card (rootsOfUnity 5 K) ^ 3 := h2
    _ ≤ 5 ^ 3 := Nat.pow_le_pow_left h3 3

theorem card_piGL_le [Finite K] : Nat.card (piGL K) ≤ 5 ^ 3 := by
  rw [piGL, Subgroup.card_map_of_injective diagU_injective]
  exact card_torusPi_le

theorem exists_eq_char (hU : UnitaryFieldData 2 f K) (P T : Subgroup ↥(unitarySU 2 f K 5))
    (hPd : ∀ g ∈ P, ∃ d : Fin 5 → Kˣ, diagU d = (g : GL (Fin 5) K)) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hPT : ∀ a ∈ P, ∀ t ∈ T, a * t * a⁻¹ ∈ T) :
    ∃ i j : Fin 5, i ≠ j ∧
      ∀ g ∈ P, ent (g : GL (Fin 5) K) i i = ent (g : GL (Fin 5) K) j j := by
  by_contra hcon
  push Not at hcon
  apply hT
  have hbot := eq_bot_of_two_group_separated hU (T.map (unitarySU 2 f K 5).subtype)
    (by rintro _ ⟨t, -, rfl⟩; exact t.2) (hT2.map _) (P.map (unitarySU 2 f K 5).subtype)
    (by rintro _ ⟨g, hg, rfl⟩; exact hPd g hg)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨t, ht, rfl⟩
      exact ⟨a * t * a⁻¹, hPT a ha t ht, by simp⟩)
    (fun i j hij => by
      obtain ⟨g, hg, hne⟩ := hcon i j hij
      exact ⟨g, ⟨g, hg, rfl⟩, hne⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ (unitarySU 2 f K 5).subtype_injective).mp hbot

theorem exists_perm_zero_one : ∀ i j : Fin 5, i ≠ j →
    ∃ σ : Equiv.Perm (Fin 5), σ i = 0 ∧ σ j = 1 := by
  decide +kernel

theorem exists_perm_conj_eq_piSU (hU : UnitaryFieldData 2 f K) (P T : Subgroup ↥(unitarySU 2 f K 5))
    (hPtor : ∀ g ∈ P, (g : GL (Fin 5) K) ∈ torusSU 5 5 K) (hPcard : Nat.card P = 5 ^ 3)
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hPT : ∀ a ∈ P, ∀ t ∈ T, a * t * a⁻¹ ∈ T) :
    ∃ σ : Equiv.Perm (Fin 5),
      P.map (MulAut.conj (⟨permGL σ, permGL_mem_unitarySU hU σ⟩ : ↥(unitarySU 2 f K 5))).toMonoidHom
        = piSU f K := by
  have := hU.finite
  have hPd : ∀ g ∈ P, ∃ d : Fin 5 → Kˣ, diagU d = (g : GL (Fin 5) K) := fun g hg => by
    obtain ⟨d, -, -, hd⟩ := mem_torusSU_iff.mp (hPtor g hg)
    exact ⟨d, hd⟩
  obtain ⟨i, j, hij, hchar⟩ := exists_eq_char hU P T hPd hT hT2 hPT
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_zero_one i j hij
  refine ⟨σ, ?_⟩
  have hs0 : σ.symm 0 = i := (Equiv.symm_apply_eq σ).mpr hσi.symm
  have hs1 : σ.symm 1 = j := (Equiv.symm_apply_eq σ).mpr hσj.symm
  have hle : P.map (MulAut.conj (⟨permGL σ, permGL_mem_unitarySU hU σ⟩ :
      ↥(unitarySU 2 f K 5))).toMonoidHom ≤ piSU f K := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨d, hd1, hd2, hd⟩ := mem_torusSU_iff.mp (hPtor g hg)
    have hdij : d i = d j := by
      have := hchar g hg
      rw [← hd] at this
      simp only [ent, diagU_val, Matrix.diagonal_apply_eq] at this
      exact Units.ext this
    rw [piSU, Subgroup.mem_subgroupOf]
    refine mem_piGL_iff.mpr ⟨d ∘ σ.symm, fun k => hd1 _, ?_, ?_, ?_⟩
    · exact (Equiv.prod_comp σ.symm d).trans hd2
    · simp only [Function.comp_apply, hs0, hs1]
      exact hdij
    · show diagU (d ∘ σ.symm) = permGL σ * (g : GL (Fin 5) K) * (permGL σ)⁻¹
      rw [← hd]
      exact (permGL_conj_diagU σ d).symm
  have hcard : Nat.card (piSU f K) ≤ 5 ^ 3 := by
    have h1 : Nat.card (piSU f K) ≤ Nat.card (piGL K) :=
      Nat.card_le_card_of_injective (fun g => ⟨(g.1 : GL (Fin 5) K), g.2⟩) (fun a b h => by
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : piGL K => (x : GL (Fin 5) K)) h)
    exact h1.trans card_piGL_le
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hPcard]
  exact hcard

end CFSG.RankThree.PartOne.KFOUT3
