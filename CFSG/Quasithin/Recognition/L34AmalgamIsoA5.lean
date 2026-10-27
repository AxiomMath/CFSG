module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoRef
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5Inputs
public import Certificates.Certificate7038

public section

namespace CFSG.Quasithin.L34Amalgam

open CFSG.CosetTable

@[expose] def enc (x : Fin 16) : Fin 4 → ZMod 2 := fun i => if bit i x then 1 else 0

@[expose] def dec (v : Fin 4 → ZMod 2) : Fin 16 :=
  ⟨(v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val, by
    have h : ∀ a : ZMod 2, a.val < 2 := fun a => ZMod.val_lt a
    have := h (v 0); have := h (v 1); have := h (v 2); have := h (v 3)
    omega⟩

theorem enc_bxor : ∀ x y : Fin 16, enc (bxor x y) = enc x + enc y := by
  decide

theorem dec_enc : ∀ x : Fin 16, dec (enc x) = x := by
  decide

theorem enc_dec : ∀ v : Fin 4 → ZMod 2, enc (dec v) = v := by
  decide

section Coord

variable {E : Type*} [Group E] (η : E ≃* Multiplicative (Fin 4 → ZMod 2))

@[expose] noncomputable def bitCoord (x : Fin 16) : E := η.symm (Multiplicative.ofAdd (enc x))

@[expose] noncomputable def bitDecode (e : E) : Fin 16 := dec (Multiplicative.toAdd (η e))

theorem bitCoord_bxor (x y : Fin 16) :
    bitCoord η (bxor x y) = bitCoord η x * bitCoord η y := by
  rw [bitCoord, bitCoord, bitCoord, enc_bxor, ofAdd_add, map_mul]

theorem bitDecode_bitCoord (x : Fin 16) : bitDecode η (bitCoord η x) = x := by
  rw [bitDecode, bitCoord, MulEquiv.apply_symm_apply, toAdd_ofAdd, dec_enc]

theorem bitCoord_bitDecode (e : E) : bitCoord η (bitDecode η e) = e := by
  rw [bitDecode, bitCoord, enc_dec, ofAdd_toAdd, MulEquiv.symm_apply_apply]

theorem bitCoord_injective : Function.Injective (bitCoord η) := fun x y h => by
  rw [← bitDecode_bitCoord η x, h, bitDecode_bitCoord]

theorem bitDecode_mul (e e' : E) :
    bitDecode η (e * e') = bxor (bitDecode η e) (bitDecode η e') := by
  apply bitCoord_injective η
  rw [bitCoord_bxor, bitCoord_bitDecode, bitCoord_bitDecode, bitCoord_bitDecode]

theorem bitCoord_zero : bitCoord η 0 = 1 := by
  rw [bitCoord, show enc 0 = 0 by decide, ofAdd_zero, map_one]

end Coord

theorem additive_eq_lin (f : Fin 16 → Fin 16) (hf : ∀ x y, f (bxor x y) = bxor (f x) (f y))
    (x : Fin 16) : f x = lin (fun i => f (basisVec i)) x := by
  have h0 : f 0 = 0 := by
    have h := hf 0 0
    rw [bxor_self] at h
    have h2 : bxor (f 0) (f 0) = 0 := bxor_self _
    rw [← h] at h2
    exact h2
  have hsel : ∀ (b : Bool) (m : Fin 16), f (sel b m) = sel b (f m) := by
    intro b m
    cases b
    · simp [sel, h0]
    · simp [sel]
  conv_lhs => rw [← eq_lin_basis x]
  show f (bxor (bxor (sel (bit 0 x) _) (sel (bit 1 x) _)) (bxor (sel (bit 2 x) _)
    (sel (bit 3 x) _))) = _
  rw [hf, hf, hf, hsel, hsel, hsel, hsel]
  rfl

theorem a5_check : subsetCheck a5Rels [] 100000 60 = true :=
  Certificates.certificate7038

theorem card_a5_le :
    Finite (PG 2 a5Rels) ∧ Nat.card (PG 2 a5Rels) ≤ 60 :=
  card_le_of_subsetCheck_nil a5Rels a5_check

@[expose] noncomputable def a5Hom {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 5 = 1) : PG 2 a5Rels →* G :=
  PresentedGroup.toGroup (f := ![a, b]) fun r hr => by
    simp only [a5Rels, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [FreeGroup.lift_mk, ha]
    · have h := hb
      simp only [pow_succ, pow_zero, one_mul, mul_assoc] at h
      simpa [FreeGroup.lift_mk, mul_assoc] using h
    · have h := hab
      simp only [pow_succ, pow_zero, one_mul, mul_assoc] at h
      simpa [FreeGroup.lift_mk, mul_assoc] using h

theorem a5Hom_of {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 5 = 1) (j : Fin 2) : a5Hom ha hb hab (PresentedGroup.of j) = ![a, b] j :=
  PresentedGroup.toGroup.of _

theorem range_a5Hom {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b ^ 3 = 1)
    (hab : (a * b) ^ 5 = 1) : (a5Hom ha hb hab).range = Subgroup.closure {a, b} := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply, a5Hom_of, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

@[expose] noncomputable def a5Equiv {G : Type*} [Group G]
    {C : Subgroup G} {a b : G}
    (ha : a * a = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1) (hC : Subgroup.closure {a, b} = C)
    (hcard : Nat.card C = 60) : PG 2 a5Rels ≃* C := by
  have : Finite (PG 2 a5Rels) := card_a5_le.1
  let f : PG 2 a5Rels →* C := (a5Hom ha hb hab).codRestrict C fun x => by
    rw [← hC, ← range_a5Hom ha hb hab]
    exact ⟨x, rfl⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨c, hc⟩
    rw [← hC, ← range_a5Hom ha hb hab] at hc
    obtain ⟨x, rfl⟩ := hc
    exact ⟨x, rfl⟩
  exact MulEquiv.ofBijective f (hsurj.bijective_of_nat_card_le (by rw [hcard]; exact card_a5_le.2))

theorem a5Equiv_of {G : Type*} [Group G] {C : Subgroup G} {a b : G}
    (ha : a * a = 1) (hb : b ^ 3 = 1) (hab : (a * b) ^ 5 = 1) (hC : Subgroup.closure {a, b} = C)
    (hcard : Nat.card C = 60) (j : Fin 2) :
    ((a5Equiv ha hb hab hC hcard (PresentedGroup.of j) : C) : G) = ![a, b] j := by
  unfold a5Equiv
  exact a5Hom_of ha hb hab j

end CFSG.Quasithin.L34Amalgam
