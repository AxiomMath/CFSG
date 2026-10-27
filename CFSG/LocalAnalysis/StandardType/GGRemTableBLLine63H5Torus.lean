module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.StandardType.TableBU

variable {K : Type} [Field K] {n : ℕ}

theorem diagHom_mem_unitarySU (h : UnitaryFieldData 2 n K) {t : Fin 6 → Kˣ}
    (ht : ∀ i, (t i : K) ^ (2 ^ n + 1) = 1) (hp : ∏ i, (t i : K) = 1) :
    (diagHom 6 t : GL (Fin 6) K) ∈ unitarySU 2 n K 6 := by
  rw [mem_unitarySU_iff h]
  exact ⟨by rw [det_diagHom, hp], diagHom_unitary h ht⟩

theorem permGL_swap_mem_unitarySU (h : UnitaryFieldData 2 n K) {i j : Fin 6} (hij : i ≠ j) :
    (permGL (Equiv.swap i j) : GL (Fin 6) K) ∈ unitarySU 2 n K 6 := by
  have : CharP K 2 := h.charP
  rw [mem_unitarySU_iff h]
  refine ⟨?_, permGL_unitary h _⟩
  rw [det_permGL, Equiv.Perm.sign_swap hij]
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  linear_combination -h2K

@[expose] noncomputable def swapSU (h : UnitaryFieldData 2 n K) : ↥(unitarySU 2 n K 6) :=
  ⟨permGL (Equiv.swap (0 : Fin 6) 1),
    permGL_swap_mem_unitarySU h (by simp [Fin.ext_iff])⟩

theorem swapSU_sq (h : UnitaryFieldData 2 n K) : swapSU h ^ 2 = 1 := by
  apply Subtype.ext
  show (permGL (Equiv.swap (0 : Fin 6) 1) : GL (Fin 6) K) ^ 2 = 1
  rw [← map_pow, sq, Equiv.swap_mul_self, map_one]

theorem swapSU_ne_one (h : UnitaryFieldData 2 n K) {ζ : Kˣ} (hζ : ζ ≠ 1) : swapSU h ≠ 1 := by
  intro h1
  have h2 : (permGL (Equiv.swap (0 : Fin 6) 1) : GL (Fin 6) K) = 1 :=
    congrArg Subtype.val h1
  have h3 := permGL_swap_not_mem_center (K := K) (d := 6) (i := 0) (j := 1)
    (by simp [Fin.ext_iff]) hζ
  exact h3 (h2 ▸ Subgroup.one_mem _)

theorem swap_commute_diagHom {t : Fin 6 → Kˣ} (ht : t 0 = t 1) :
    Commute (permGL (Equiv.swap (0 : Fin 6) 1) : GL (Fin 6) K) (diagHom 6 t) := by
  have hts : t ∘ (Equiv.swap (0 : Fin 6) 1).symm = t := by
    funext i
    rw [Function.comp_apply, Equiv.symm_swap]
    by_cases h0 : i = 0
    · rw [h0, Equiv.swap_apply_left, ht]
    · by_cases h1 : i = 1
      · rw [h1, Equiv.swap_apply_right, ht]
      · rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
  have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap (0 : Fin 6) 1) t
  rw [hts] at h1
  show _ * _ = _ * _
  calc (permGL (Equiv.swap (0 : Fin 6) 1) : GL (Fin 6) K) * diagHom 6 t
      = permGL (Equiv.swap (0 : Fin 6) 1) * diagHom 6 t *
          (permGL (Equiv.swap (0 : Fin 6) 1))⁻¹ * permGL (Equiv.swap (0 : Fin 6) 1) := by
        group
    _ = diagHom 6 t * permGL (Equiv.swap (0 : Fin 6) 1) := by rw [h1]

theorem exists_torusFour [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) :
    ∃ E : Subgroup ↥(unitarySU 2 n K 6), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧
      ∀ e ∈ E, ∃ t : Fin 6 → Kˣ, (e : GL (Fin 6) K) = diagHom 6 t ∧ t 0 = t 1 ∧
        ∀ i, t i ^ 3 = 1 := by
  classical
  have := Fact.mk Nat.prime_three
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hKd Nat.prime_three hpq
  have hζp : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hm : 4 + 2 ≤ 6 := by norm_num
  set c := torusGen ζ hm with hc
  have hcp : ∀ j i, c j i ^ 3 = 1 := fun j i => torusGen_pow hζp hm j i
  have hcprod : ∀ j, ∏ i, c j i = 1 := fun j => prod_torusGen ζ hm j
  have hcnorm : ∀ j i, c j i ^ (2 ^ n + 1) = 1 := fun j i => torusGen_pow hζq hm j i
  have hmemH : ∀ a, diagHom 6 (expHom c hcp a) ∈ unitarySU 2 n K 6 := fun a =>
    diagHom_expHom_mem_unitarySU hKd c hcp hcprod hcnorm a
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = 3 := by
    intro j
    refine ⟨⟨j + 2, by omega⟩, fun j' hj' => torusGen_other ζ hm hj', ?_⟩
    rw [hc, torusGen_self, Nat.Coprime.orderOf_pow, orderOf_inv, hζo]
    rw [orderOf_inv, hζo]
    decide
  have hexpinj := expHom_injective c hcp hpriv
  set φ : Multiplicative (Fin 4 → ZMod 3) →* ↥(unitarySU 2 n K 6) :=
    ((diagHom 6).comp (expHom c hcp)).codRestrict _ hmemH with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : diagHom 6 (expHom c hcp a) = diagHom 6 (expHom c hcp b) := congrArg Subtype.val hab
    exact hexpinj (diagHom_injective 6 h1)
  have hapow : ∀ a : Multiplicative (Fin 4 → ZMod 3), a ^ 3 = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    have h3 : (3 : ZMod 3) = 0 := by exact_mod_cast ZMod.natCast_self 3
    simp [Pi.smul_apply, nsmul_eq_mul, h3]
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · exact isElemAbelian_range (fun a b => mul_comm a b) hapow φ
  · rw [Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · rintro _ ⟨a, rfl⟩
    refine ⟨expHom c hcp a, rfl, ?_, ?_⟩
    · have h01 : ∀ j, c j 0 = c j 1 := by
        intro j
        simp [hc, torusGen_apply]
      rw [expHom_apply, expHom_apply]
      exact Finset.prod_congr rfl fun j _ => by rw [h01 j]
    · intro i
      have h1 : expHom c hcp a ^ 3 = 1 := by rw [← map_pow, hapow, map_one]
      exact congrFun h1 i

end CFSG.StandardType.Line63.H5

end
