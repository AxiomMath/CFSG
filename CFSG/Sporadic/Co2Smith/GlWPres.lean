module

public import CFSG.Sporadic.Co2Smith.GlC0QuotCheck
public import CFSG.Sporadic.Co2Smith.GlWChart

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.CosetTable

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

abbrev PGw : Type := PG 7 Native.glWRels

theorem lift_glWRels {H : Type} [Group H] (g : ℕ → H)
    (hg : ∀ w ∈ Native.glWRelsN, (w.map g).prod = 1) :
    ∀ r ∈ {r : FreeGroup (Fin 7) | r ∈ Native.glWRels.map FreeGroup.mk},
      FreeGroup.lift (fun i : Fin 7 => g i) r = 1 := by
  intro r hr
  obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hw'
  rw [FreeGroup.lift_mk, List.map_map, ← hg w hw]
  congr 1
  apply List.map_congr_left
  intro k hk
  show g (k % 7) = g k
  rw [Nat.mod_eq_of_lt (glWRelsN_lt hw k hk)]

section Letters

theorem genLetters_elt_zero : genLetters.elt 0 = z0 := by
  show (if 0 = 0 then z0 else if 0 < 6 then tK (0 - 1) else 1) = z0
  exact ite_eq_left rfl

theorem genLetters_elt_succ {j : ℕ} (hj : j < 5) : genLetters.elt (j + 1) = tK j := by
  show (if j + 1 = 0 then z0 else if j + 1 < 6 then tK (j + 1 - 1) else 1) = tK j
  rw [ite_eq_right (Nat.succ_ne_zero j), ite_eq_left (by omega), Nat.add_sub_cancel]

theorem w7Letters_elt_ge {k : ℕ} (hk : 7 ≤ k) : w7Letters.elt k = 1 := by
  show (if k < 6 then genLetters.elt k else if k = 6 then δ1hK else 1) = 1
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem w7Letters_mem_C0c (k : ℕ) : w7Letters.elt k ∈ C0c := by
  show (if k < 6 then genLetters.elt k else if k = 6 then δ1hK else 1) ∈ C0c
  split_ifs
  · exact (mem_inf.1 (genLetters_mem_D k)).1
  · exact δ1hK_mem_C0c
  · exact C0c.one_mem

@[expose] noncomputable def w7C (k : ℕ) : C0c := ⟨w7Letters.elt k, w7Letters_mem_C0c k⟩

theorem w7C_word : ∀ w : List ℕ, ((w.map w7C).prod : K) = lWord w7Letters w
  | [] => by rw [List.map_nil, List.prod_nil, lWord, Subgroup.coe_one]
  | k :: w => by rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, w7C_word w, lWord]; rfl

theorem w7C_rel {w : List ℕ} (hw : w ∈ Native.glWRelsN) : (w.map w7C).prod = 1 :=
  Subtype.ext (by rw [w7C_word, lWord_w7_rel hw, Subgroup.coe_one])

@[expose] noncomputable def wHomC : PGw →* C0c :=
  PresentedGroup.toGroup (lift_glWRels w7C fun _ hw => w7C_rel hw)

theorem wHomC_of (i : Fin 7) : wHomC (PresentedGroup.of i) = w7C i :=
  PresentedGroup.toGroup.of _

end Letters

section Iso

theorem wHomC_surjective : Function.Surjective wHomC := by
  set S : Subgroup K := wHomC.range.map C0c.subtype
  have hS : ∀ k, w7Letters.elt k ∈ S := by
    intro k
    by_cases hk : k < 7
    · exact ⟨w7C k, ⟨PresentedGroup.of ⟨k, hk⟩, wHomC_of _⟩, rfl⟩
    · rw [w7Letters_elt_ge (by omega)]
      exact S.one_mem
  have hz : z0 ∈ S := by
    rw [← genLetters_elt_zero, ← w7Letters_elt_lt (by norm_num)]
    exact hS 0
  have ht : ∀ j < 5, tK j ∈ S := fun j hj => by
    rw [← genLetters_elt_succ hj, ← w7Letters_elt_lt (by omega)]
    exact hS (j + 1)
  have hr : reflK 16 ∈ S := by
    rw [reflK16_eq]
    exact lWord_mem_closure w7Letters S hS _
  have hle : C0c ≤ S := C0c_le_closure.trans ((closure_le S).2
    (Set.union_subset (D_le_of_mem hz ht) (Set.singleton_subset_iff.2 hr)))
  intro g
  obtain ⟨x, ⟨p, rfl⟩, hx⟩ := hle g.2
  exact ⟨p, Subtype.ext hx⟩

theorem finite_card_PGw :
    Finite PGw ∧ Nat.card PGw ≤ 51840 := by
  obtain ⟨hf1, h1⟩ := card_le_of_subsetCheckC_nil _ glW_e1
  obtain ⟨hf, h⟩ := card_le_of_subsetCheckC Native.glWRels [0, 1, 2, 3, 4, 5] glW_e2
  exact ⟨hf, h.trans (by omega)⟩

theorem wHomC_bijective : Function.Bijective wHomC := by
  have := finite_card_PGw.1
  exact wHomC_surjective.bijective_of_nat_card_le (by rw [card_C0c]; exact finite_card_PGw.2)

@[expose] noncomputable def wEquivC : PGw ≃* C0c := MulEquiv.ofBijective wHomC wHomC_bijective

theorem wEquivC_symm_w7C {k : ℕ} (hk : k < 7) :
    wEquivC.symm (w7C k) = PresentedGroup.of ⟨k, hk⟩ := by
  rw [MulEquiv.symm_apply_eq]
  exact (wHomC_of ⟨k, hk⟩).symm

end Iso

section Hom

variable {G : Type} [Group G] {z : G}

@[expose] noncomputable def agreeSub (φ : centralizer ({z} : Set G) ≃* Cz) (ρ : C0c →* G) :
    Subgroup K where
  carrier := {x | ∃ (h0 : x ∈ C0c) (h1 : x ∈ Cz), ρ ⟨x, h0⟩ = phiH φ ⟨x, h1⟩}
  mul_mem' := by
    rintro a b ⟨ha0, ha1, ha⟩ ⟨hb0, hb1, hb⟩
    refine ⟨C0c.mul_mem ha0 hb0, Cz.mul_mem ha1 hb1, ?_⟩
    rw [show (⟨a * b, C0c.mul_mem ha0 hb0⟩ : C0c) = ⟨a, ha0⟩ * ⟨b, hb0⟩ from rfl,
      show (⟨a * b, Cz.mul_mem ha1 hb1⟩ : Cz) = ⟨a, ha1⟩ * ⟨b, hb1⟩ from rfl, map_mul, map_mul,
      ha, hb]
  one_mem' := ⟨C0c.one_mem, Cz.one_mem, by
    rw [show (⟨1, C0c.one_mem⟩ : C0c) = 1 from rfl, show (⟨1, Cz.one_mem⟩ : Cz) = 1 from rfl,
      map_one, map_one]⟩
  inv_mem' := by
    rintro a ⟨ha0, ha1, ha⟩
    refine ⟨C0c.inv_mem ha0, Cz.inv_mem ha1, ?_⟩
    rw [show (⟨a⁻¹, C0c.inv_mem ha0⟩ : C0c) = (⟨a, ha0⟩ : C0c)⁻¹ from rfl,
      show (⟨a⁻¹, Cz.inv_mem ha1⟩ : Cz) = (⟨a, ha1⟩ : Cz)⁻¹ from rfl, map_inv, map_inv, ha]

theorem eq_phiH_of_gen (φ : centralizer ({z} : Set G) ≃* Cz) (ρ : C0c →* G)
    (hgen : ∀ k < 6, ∀ (h0 : genLetters.elt k ∈ C0c) (h1 : genLetters.elt k ∈ Cz),
      ρ ⟨_, h0⟩ = phiH φ ⟨_, h1⟩)
    (w : C0c) (hw : (w : K) ∈ Cz) : ρ w = phiH φ ⟨w, hw⟩ := by
  have hT : ∀ k < 6, genLetters.elt k ∈ agreeSub φ ρ := fun k hk =>
    ⟨(mem_inf.1 (genLetters_mem_D k)).1, (mem_inf.1 (genLetters_mem_D k)).2, hgen k hk _ _⟩
  have hz0 : z0 ∈ agreeSub φ ρ := genLetters_elt_zero ▸ hT 0 (by norm_num)
  have ht : ∀ j < 5, tK j ∈ agreeSub φ ρ := fun j hj =>
    genLetters_elt_succ hj ▸ hT (j + 1) (by omega)
  obtain ⟨_, _, h⟩ := D_le_of_mem hz0 ht (mem_inf.2 ⟨w.2, hw⟩)
  exact h

end Hom

end CFSG.Sporadic.Co2Smith
