module

public import Certificates.Data.G24DCCode
import all Certificates.Data.G24DCCode
public import CFSG.Assembly.LowTwoRankDefs

public section

open CFSG.Fischer CFSG.Quasithin.St84.G24DC.Native CFSG.Quasithin.St84.G24DC.Code
open CFSG.LieType.Multipliers.G24 (genArr wordArr toMat)

namespace CFSG.Quasithin.St84.G24Table

theorem getD_toArray_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (d : β) (e : α)
    (hi : i < l.length) : (l.map f).toArray.getD i d = f (l.getD i e) := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

theorem getD_map_of_lt {α β : Type*} (f : α → β) (a : Array α) (i : Nat) (d : α) (e : β)
    (hi : i < a.size) : (a.map f).getD i e = f (a.getD i d) := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  rfl

theorem decode_foldl_mulN {α : Type*} (l : List α) (f : α → Mat) (A : Mat) :
    decode (l.foldl (fun acc a => mulN acc (f a)) A) =
      decode A * (l.map fun a => decode (f a)).prod := by
  induction l generalizing A with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, decode_mulN, List.map_cons, List.prod_cons, mul_assoc]

theorem decode_evalP_eq (im : Array Mat) (w : List Nat) :
    decode (evalP im w) = (w.map fun l => decode (im.getD l oneM)).prod := by
  unfold evalP
  rw [decode_foldl_mulN w (fun l => im.getD l oneM) oneM, decode_oneM, one_mul]

section Hom

variable {Y : Type*} [Group Y] (φ : Y →* GL (Fin 14) F4)

private theorem decode_evalP {m : ℕ} {im : Array Mat} {z : Fin m → Y}
    (h : ∀ l : Fin m, decode (im.getD l.val oneM) =
      (φ (z l) : Matrix (Fin 14) (Fin 14) F4))
    (w : List (Fin m)) :
    decode (evalP im (w.map Fin.val)) =
      (φ (w.map z).prod : Matrix (Fin 14) (Fin 14) F4) := by
  rw [decode_evalP_eq, List.map_map]
  rw [show ((fun l : Nat => decode (im.getD l oneM)) ∘ Fin.val) =
      (fun l => (φ (z l) : Matrix (Fin 14) (Fin 14) F4)) from by
    funext l
    exact h l]
  change (List.map ((fun a => (φ a : Matrix (Fin 14) (Fin 14) F4)) ∘ z) w).prod =
    (φ ((w.map z).prod) : Matrix (Fin 14) (Fin 14) F4)
  rw [← List.map_map]
  change (List.map (fun a => (φ a : Matrix (Fin 14) (Fin 14) F4)) (w.map z)).prod =
    (φ ((w.map z).prod) : Matrix (Fin 14) (Fin 14) F4)
  exact (map_list_prod ((Units.coeHom (Matrix (Fin 14) (Fin 14) F4)).comp φ) (w.map z)).symm

theorem decode_evalF {im : Array Mat} {z : Fin 4 → Y}
    (h : ∀ l : Fin 4, decode (im.getD l.val oneM) =
      (φ (z l) : Matrix (Fin 14) (Fin 14) F4))
    (w : List (Fin 4)) :
    decode (evalF im w) = (φ (w.map z).prod : Matrix (Fin 14) (Fin 14) F4) := by
  have h' := decode_evalP (φ := φ) h w
  rw [show evalP im (w.map Fin.val) = evalF im w from by
    unfold evalP evalF
    rw [List.foldl_map]] at h'
  exact h'

@[expose] noncomputable def pcEltY (y : Fin 10 → Y) (j : Nat) : Y :=
  (((List.finRange 10).filter fun m => j.testBit m.val).map y).prod

theorem pcEltY_def (y : Fin 10 → Y) (j : Nat) :
    pcEltY y j = (((List.finRange 10).filter fun m => j.testBit m.val).map y).prod := rfl

theorem pcEltY_mem_closure (y : Fin 10 → Y) (j : Nat) :
    pcEltY y j ∈ Subgroup.closure (Set.range y) := by
  rw [pcEltY_def]
  refine Subgroup.list_prod_mem _ ?_
  intro z hz
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp hz
  exact Subgroup.subset_closure ⟨m, rfl⟩

theorem pcEltY_mem_closure_ge (y : Fin 10 → Y) {c j : Nat} (hdiv : 2 ^ c ∣ j) :
    pcEltY y j ∈ Subgroup.closure (Set.range fun m : {m : Fin 10 // c ≤ m.val} => y m.1) := by
  rw [pcEltY_def]
  refine Subgroup.list_prod_mem _ ?_
  intro z hz
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
  rw [List.mem_filter] at hm
  have hcm : c ≤ m.val := by
    obtain ⟨q, rfl⟩ := hdiv
    rw [Nat.testBit_two_pow_mul, Bool.and_eq_true, decide_eq_true_eq] at hm
    exact hm.2.1
  exact Subgroup.subset_closure ⟨⟨m, hcm⟩, rfl⟩

end Hom

end CFSG.Quasithin.St84.G24Table
