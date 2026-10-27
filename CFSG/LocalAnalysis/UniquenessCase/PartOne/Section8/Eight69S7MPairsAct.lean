module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69S7MPairsBlock

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs

open CFSG.AGLEmbedding.FusD2 CFSG.RankThree.Native Certificates.McLFivePairs
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
open Certificates.MaxD2Perm (nGens)
open Certificates.MaxD2Heis (mclFiveDataP)

private def Good (b : Equiv.Perm (Fin 275)) : Prop :=
  ∀ i : Fin 3, ∃ l : Fin 3, (mclB5 i).map (MulAut.conj b).toMonoidHom = mclB5 l

private theorem good_one : Good 1 := by
  intro i
  refine ⟨i, ?_⟩
  have h1 : (MulAut.conj (1 : Equiv.Perm (Fin 275))).toMonoidHom =
      MonoidHom.id (Equiv.Perm (Fin 275)) := by
    ext x
    simp
  rw [h1, Subgroup.map_id]

private theorem good_mul {b c : Equiv.Perm (Fin 275)} (hb : Good b) (hc : Good c) :
    Good (b * c) := by
  intro i
  obtain ⟨l, hl⟩ := hc i
  obtain ⟨m, hm⟩ := hb l
  refine ⟨m, ?_⟩
  have hcomp : (MulAut.conj (b * c)).toMonoidHom =
      (MulAut.conj b).toMonoidHom.comp (MulAut.conj c).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hm, ← hl, Subgroup.map_map, hcomp]

private theorem good_inv {b : Equiv.Perm (Fin 275)} (hb : Good b) : Good b⁻¹ := by
  have hpow : ∀ m : ℕ, Good (b ^ m) := by
    intro m
    induction m with
    | zero => simpa using good_one
    | succ m ih => rw [pow_succ]; exact good_mul ih hb
  have hpos : 0 < orderOf b := orderOf_pos b
  have h1 : b ^ (orderOf b - 1) * b = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have hinv : b⁻¹ = b ^ (orderOf b - 1) := inv_eq_of_mul_eq_one_left h1
  rw [hinv]
  exact hpow _

private theorem mclB5_map_conj_gen
    (i : Fin 3) (j : ℕ) (hj : j < 4) :
    ∃ l : Fin 3,
      (mclB5 i).map (MulAut.conj (mclNGens5.getD j 1)⁻¹).toMonoidHom = mclB5 l := by
  classical
  obtain ⟨-, -, -, -, -, -, hgensOK, hact, hactOK, -, -, -⟩ := mcl_pairs_check_spec
  have hmemIdx : (i.val, j) ∈ actIndex := by
    simp only [actIndex, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨i.val, i.isLt, j, hj, rfl⟩
  have hmem : (i.val, j) ∈ actWords.map (fun e => (e.1, e.2.1)) := by
    rw [hact]
    exact hmemIdx
  obtain ⟨e, he, heij⟩ := List.mem_map.mp hmem
  have he1 : e.1 = i.val := congrArg Prod.fst heij
  have he2 : e.2.1 = j := congrArg Prod.snd heij
  have hOK := hactOK e he
  simp only [actOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_eq_true] at hOK
  obtain ⟨⟨⟨hk, hInvN⟩, -⟩, hwords⟩ := hOK
  rw [he1] at hwords
  rw [he2] at hwords hInvN
  refine ⟨⟨e.2.2.1, hk⟩, ?_⟩
  have hmclB5i : mclB5 i = Subgroup.closure {g | g ∈ mclBGens5 (i : ℕ)} := rfl
  have hle : (mclB5 i).map (MulAut.conj (mclNGens5.getD j 1)⁻¹).toMonoidHom ≤
      mclB5 ⟨e.2.2.1, hk⟩ := by
    rw [hmclB5i, MonoidHom.map_closure]
    refine (Subgroup.closure_le (mclB5 ⟨e.2.2.1, hk⟩)).mpr ?_
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨l0, hl0, hxl⟩ := List.mem_iff_getElem.mp hx
    have hgetD : (mclBGens5 (i : ℕ)).getD l0 1 = x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨hl0, hxl⟩]
      rfl
    have hgi : TabRep ((mclBT5.getD (i : ℕ) #[]).getD l0 (idTab 275)) x := by
      rw [← hgetD]
      exact rep_mclBT5 (k := (i : ℕ)) i.isLt l0
    have hnt : TabRep ((nGens mclFiveDataP).getD j (idTab 275)) (mclNGens5.getD j 1) := by
      simpa using mcl_rep_nGens j
    have hconj : TabRep (conjBy ((nGens mclFiveDataP).getD j (idTab 275))
        ((mclBT5.getD (i : ℕ) #[]).getD l0 (idTab 275)))
        ((mclNGens5.getD j 1)⁻¹ * x * (mclNGens5.getD j 1)) :=
      rep_conjBy hnt hInvN hgi
    have hw := hwords l0 hl0
    have hmem' := mem_closure_of_wordIn (L := mclBGens5 e.2.2.1)
      (gs := mclBT5.getD e.2.2.1 #[])
      (rep_mclBT5 (k := e.2.2.1) hk) (hgensOK e.2.2.1 hk) hconj hw
    have hx' : ((MulAut.conj (mclNGens5.getD j 1)⁻¹).toMonoidHom) x =
        (mclNGens5.getD j 1)⁻¹ * x * (mclNGens5.getD j 1) := by
      change MulAut.conj (mclNGens5.getD j 1)⁻¹ x = _
      rw [MulAut.conj_apply, inv_inv]
    rw [hx']
    exact hmem'
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcard := Subgroup.card_map_of_injective (K := mclB5 i)
    (f := (MulAut.conj (mclNGens5.getD j 1)⁻¹).toMonoidHom)
    (MulAut.conj (mclNGens5.getD j 1)⁻¹).injective
  rw [hcard, card_mclB5 i, card_mclB5 ⟨e.2.2.1, hk⟩]

private theorem good_of_mem
    (x : Equiv.Perm (Fin 275)) (hx : x ∈ mclNGens5) : Good x := by
  obtain ⟨j, hj, hxj⟩ := List.mem_iff_getElem.mp hx
  have hj4 : j < 4 := mclNGens5_length ▸ hj
  have hgetD : mclNGens5.getD j 1 = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_some_iff.mpr ⟨hj, hxj⟩]
    rfl
  rw [← hgetD]
  have hgen : Good ((mclNGens5.getD j 1)⁻¹) := fun i => mclB5_map_conj_gen i j hj4
  simpa only [inv_inv] using good_inv hgen

theorem mclB5_map_conj
    {b : Equiv.Perm (Fin 275)}
    (hb : b ∈ mclN5) (k : Fin 3) : ∃ l, (mclB5 k).map (MulAut.conj b).toMonoidHom = mclB5 l := by
  have hgood : Good b := by
    rw [mclN5_eq] at hb
    induction hb using Subgroup.closure_induction with
    | mem x hx => exact good_of_mem x hx
    | one => exact good_one
    | mul x y hx hy ihx ihy => exact good_mul ihx ihy
    | inv x hx ih => exact good_inv ih
  exact hgood k

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs
