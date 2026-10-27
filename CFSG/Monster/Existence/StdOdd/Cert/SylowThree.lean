module

public import CFSG.Monster.Existence.StdOdd.P5
public import CFSG.Monster.Existence.StdOdd.Defs
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeExt
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeTorus
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
public meta import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeData
public meta import CFSG.Monster.B.Classical.E6AdjointTable
public meta import CFSG.Monster.Existence.StdOdd.P5
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeInputs
public import Certificates.Certificate6038
public import Certificates.Certificate6039
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate6040
public import Certificates.Certificate16038
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.Monster.B.Geometry.CoxeterWords

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Monster.Existence.StdOdd.P5 (E5 GL5 M5 rk refl reflGL genA genB Pbar IsExt)
open CFSG.LieType.Chevalley.C2E6Std (card_stdGroup)

theorem fixed_r_ok :
    CertNative.fixedOK bracketCodes formBits gamTable
    ((List.range 6).map rWord) = true :=
  Certificates.certificate6038.1

theorem rWord_lt : ∀ i < 6, ∀ l ∈ rWord i, l.1 < 72 :=
  Certificates.certificate6038.2.1

theorem rWord_mem_std
    (i : Fin 6) : wordElt (rWord i) ∈ stdGroup := by
  refine wordElt_mem_stdGroup _ (rWord_lt i i.2) ?_
  have h := fixed_r_ok
  simp only [CertNative.fixedOK, List.all_eq_true] at h
  exact h (rWord i) (List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)

@[expose] noncomputable def rR
    (i : Fin 6) : Rgrp := ⟨wordElt (rWord i), rWord_mem_std i⟩

theorem glR_rR
    (i : Fin 6) :
    glR (rR i) = toMat (CertNative.wordMat bracketCodes formBits (rWord i)) :=
  glMat_wordElt _ (rWord_lt i i.2)

theorem glR_eR
    (j : Fin 5) :
    glR (eR j) = toMat (CertNative.wordMat bracketCodes formBits (eWord j)) :=
  glMat_wordElt _ (eWord_lt j j.2)

theorem conj_ok :
    CertNative.conjOK bracketCodes formBits ((List.range 6).map rWord)
    ((List.range 5).map eWord) colsData = true :=
  Certificates.certificate6038.2.2.1

theorem colsData_eq :
    ∀ (i : Fin 6) (j : Fin 5), colsData.getD (5 * i + j) [] =
    [(colVec i j 0).val, (colVec i j 1).val, (colVec i j 2).val, (colVec i j 3).val,
      (colVec i j 4).val] :=
  Certificates.certificate6038.2.2.2.1

theorem getD_map_range {α : Type*} (f : ℕ → α) (n i : ℕ) (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem toMat_psiMat
    (v : E5) :
    toMat (CertNative.psiMat (((List.range 5).map eWord).map
      (CertNative.wordMat bracketCodes formBits))
      [(v 0).val, (v 1).val, (v 2).val, (v 3).val, (v 4).val]) = glR (psiFun v) := by
  have hE : ∀ k : ℕ, k < 5 → (((List.range 5).map eWord).map
      (CertNative.wordMat bracketCodes formBits)).getD k Native.one =
      CertNative.wordMat bracketCodes formBits (eWord k) := fun k hk => by
    simp [List.getD_eq_getElem?_getD, hk]
  simp only [CertNative.psiMat, List.getD_cons_zero, List.getD_cons_succ]
  rw [hE 0 (by norm_num), hE 1 (by norm_num), hE 2 (by norm_num), hE 3 (by norm_num),
    hE 4 (by norm_num)]
  simp only [toMat_mul, toMat_pow, psiFun, map_mul, map_pow]
  rw [glR_eR 0, glR_eR 1, glR_eR 2, glR_eR 3, glR_eR 4]
  rfl

theorem rR_conj_mat
    (i : Fin 6) (j : Fin 5) :
    glR (rR i) * glR (eR j) = glR (psiFun (colVec i j)) * glR (rR i) := by
  have h := conj_ok
  simp only [CertNative.conjOK, List.all_eq_true, List.mem_range] at h
  have h := h i i.2 j j.2
  have hR : (((List.range 6).map rWord).map (CertNative.wordMat bracketCodes formBits)).getD i
      Native.one = CertNative.wordMat bracketCodes formBits (rWord i) := by
    simp [List.getD_eq_getElem?_getD, i.2]
  have hE : (((List.range 5).map eWord).map (CertNative.wordMat bracketCodes formBits)).getD j
      Native.one = CertNative.wordMat bracketCodes formBits (eWord j) := by
    simp [List.getD_eq_getElem?_getD, j.2]
  rw [hR, hE, colsData_eq i j] at h
  have h := toMat_eq_of_eqM h
  rw [toMat_mul, toMat_mul, toMat_psiMat (colVec i j), ← glR_rR, ← glR_eR] at h
  exact h

theorem rR_conj
    (i : Fin 6) (j : Fin 5) : rR i * eR j * (rR i)⁻¹ = psiFun (colVec i j) := by
  have h : rR i * eR j = psiFun (colVec i j) * rR i :=
    glR_injective (by rw [map_mul, map_mul]; exact rR_conj_mat i j)
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem conjAmb_rR
    (i : Fin 6) : ConjAmb psi (rR i) (reflGL i) := by
  refine ConjAmb.of_basis _ _ fun j => ?_
  rw [psi_apply, psiFun_single, rR_conj]
  rfl

@[expose] noncomputable def sylowTA :
    Rgrp := rR 1 * rR 3

@[expose] noncomputable def sylowTB :
    Rgrp :=
  rR 2 * rR 3 * rR 4 * rR 5 * rR 0 * rR 2 * rR 3 * rR 4

theorem conjAmb_sylowTA :
    ConjAmb psi sylowTA genA := (conjAmb_rR 1).mul (conjAmb_rR 3)

theorem conjAmb_sylowTB :
    ConjAmb psi sylowTB genB :=
  (((((((conjAmb_rR 2).mul (conjAmb_rR 3)).mul (conjAmb_rR 4)).mul (conjAmb_rR 5)).mul
    (conjAmb_rR 0)).mul (conjAmb_rR 2)).mul (conjAmb_rR 3)).mul (conjAmb_rR 4)

theorem sylow_split :
    CertNative.splitOK bracketCodes formBits ((List.range 6).map rWord)
    tAidx tBidx pwData raData rbData = true :=
  Certificates.certificate6038.2.2.2.2.1

theorem pw_zero : P5.pw 0 = [] :=
  Certificates.certificate6038.2.2.2.2.2

theorem glR_Wd
    (x y : Rgrp) (w : List (Fin 2)) :
    glR (Wd x y w) = lineProdG #[glR x, glR y] (w.map Fin.val) := by
  have key : ∀ (w : List (Fin 2)) (acc : Matrix (Fin 78) (Fin 78) K),
      (w.map Fin.val).foldl (fun acc i => acc * (#[glR x, glR y] : Array _).getD i 1) acc =
        acc * glR (Wd x y w) := by
    intro w
    induction w with
    | nil => intro acc; simp [Wd_nil]
    | cons c w ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, ih, Wd_cons, map_mul, mul_assoc]
      fin_cases c <;> simp
  rw [lineProdG, key, one_mul]

theorem getD_lineProd_R
    (i : ℕ) (hi : i < 6) :
    (((((List.range 6).map rWord).map (CertNative.wordMat bracketCodes formBits)).toArray).map
      toMat).getD i 1 = glR (rR ⟨i, hi⟩) := by
  have h := getD_map toMat
    ((((List.range 6).map rWord).map (CertNative.wordMat bracketCodes formBits)).toArray) i
    Native.one
  rw [toMat_one] at h
  rw [h, glR_rR]
  congr 1
  simp [Array.getD_eq_getD_getElem?, hi]

theorem toMat_tA :
    toMat (Native.lineProd
    ((((List.range 6).map rWord).map (CertNative.wordMat bracketCodes formBits)).toArray)
    tAidx) = glR sylowTA := by
  rw [toMat_lineProd]
  simp only [tAidx, lineProdG, List.foldl_cons, List.foldl_nil, one_mul, sylowTA, map_mul]
  rw [getD_lineProd_R 1 (by norm_num), getD_lineProd_R 3 (by norm_num)]
  rfl

theorem toMat_tB :
    toMat (Native.lineProd
    ((((List.range 6).map rWord).map (CertNative.wordMat bracketCodes formBits)).toArray)
    tBidx) = glR sylowTB := by
  rw [toMat_lineProd]
  simp only [tBidx, lineProdG, List.foldl_cons, List.foldl_nil, one_mul, sylowTB, map_mul]
  rw [getD_lineProd_R 2 (by norm_num), getD_lineProd_R 3 (by norm_num),
    getD_lineProd_R 4 (by norm_num), getD_lineProd_R 5 (by norm_num),
    getD_lineProd_R 0 (by norm_num)]
  rfl

theorem getD_pwData (j : Fin 81) : pwData.getD j [] = (P5.pw j).map Fin.val := by
  rw [pwData, getD_map_range _ 81 j j.2]
  have : Fin.ofNat 81 (j : ℕ) = j := Fin.ext (Nat.mod_eq_of_lt j.2)
  rw [this]

theorem getD_raData (j : Fin 81) : raData.getD j 0 = (P5.ra j : ℕ) := by
  rw [raData, getD_map_range _ 81 j j.2]
  have : Fin.ofNat 81 (j : ℕ) = j := Fin.ext (Nat.mod_eq_of_lt j.2)
  rw [this]

theorem getD_rbData (j : Fin 81) : rbData.getD j 0 = (P5.rb j : ℕ) := by
  rw [rbData, getD_map_range _ 81 j j.2]
  have : Fin.ofNat 81 (j : ℕ) = j := Fin.ext (Nat.mod_eq_of_lt j.2)
  rw [this]

theorem toMat_W
    (j : Fin 81) : toMat ((pwData.map (Native.lineProd
    #[Native.lineProd ((((List.range 6).map rWord).map
        (CertNative.wordMat bracketCodes formBits)).toArray) tAidx,
      Native.lineProd ((((List.range 6).map rWord).map
        (CertNative.wordMat bracketCodes formBits)).toArray) tBidx])).getD j Native.one) =
      glR (Wd sylowTA sylowTB (P5.pw j)) := by
  have h1 : ∀ (f : List ℕ → Native.Mat), f [] = Native.one →
      (pwData.map f).getD j Native.one = f (pwData.getD j []) := fun f hf => by
    rw [← hf]
    exact List.getD_map pwData [] f
  rw [h1 _ rfl, getD_pwData, toMat_lineProd, glR_Wd]
  congr 1
  have h2 : (#[Native.lineProd ((((List.range 6).map rWord).map
        (CertNative.wordMat bracketCodes formBits)).toArray) tAidx,
      Native.lineProd ((((List.range 6).map rWord).map
        (CertNative.wordMat bracketCodes formBits)).toArray) tBidx] : Array Native.Mat).map
      toMat = #[glR sylowTA, glR sylowTB] := by
    simp only [List.map_toArray, List.map_cons, List.map_nil, toMat_tA, toMat_tB]
  exact h2

theorem sylow_split_facts :
    sylowTA ^ 3 = 1 ∧ sylowTB ^ 3 = 1 ∧
      (∀ j : Fin 81, Wd sylowTA sylowTB (P5.pw j) * sylowTA =
        Wd sylowTA sylowTB (P5.pw (P5.ra j))) ∧
      (∀ j : Fin 81, Wd sylowTA sylowTB (P5.pw j) * sylowTB =
        Wd sylowTA sylowTB (P5.pw (P5.rb j))) := by
  have h := sylow_split
  unfold CertNative.splitOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hA3, hB3⟩, hW⟩ := h
  refine ⟨?_, ?_, fun j => ?_, fun j => ?_⟩
  · have h := toMat_eq_of_eqM hA3
    rw [toMat_pow, toMat_tA, toMat_one] at h
    exact glR_injective (by rw [map_pow, h, map_one])
  · have h := toMat_eq_of_eqM hB3
    rw [toMat_pow, toMat_tB, toMat_one] at h
    exact glR_injective (by rw [map_pow, h, map_one])
  · have h := toMat_eq_of_eqM (hW j j.2).1
    rw [toMat_mul, getD_raData, toMat_W, toMat_tA, toMat_W] at h
    exact glR_injective (by rw [map_mul]; exact h)
  · have h := toMat_eq_of_eqM (hW j j.2).2
    rw [toMat_mul, getD_rbData, toMat_W, toMat_tB, toMat_W] at h
    exact glR_injective (by rw [map_mul]; exact h)

theorem exists_isExt_stdGroup_fixDim :
    ∃ (T : Subgroup Rgrp) (E : Subgroup T) (ι : E ≃* Multiplicative E5) (ρ : T →* GL5),
      IsExt Pbar E ι ρ ∧
        (∀ x : E5, fixDim (((ι.symm (Multiplicative.ofAdd x) : E) : T) : Rgrp) = 6 + rk x) ∧
        (∀ e : E, fixDim (((e : T) : Rgrp)) = 6 + rk (P5.ivec E ι e)) := by
  obtain ⟨hA3, hB3, htA, htB⟩ := sylow_split_facts
  obtain ⟨T, E, ι, ρ, hρ, hι⟩ := exists_isExt_of_split psi psi_injective sylowTA sylowTB
    conjAmb_sylowTA conjAmb_sylowTB hA3 hB3 htA htB (by rw [pw_zero]; rfl)
  have h1 : ∀ x : E5, fixDim (((ι.symm (Multiplicative.ofAdd x) : E) : T) : Rgrp) = 6 + rk x :=
    fun x => by rw [hι]; exact fixDim_psi x
  refine ⟨T, E, ι, ρ, hρ, h1, fun e => ?_⟩
  have := h1 (P5.ivec E ι e)
  rwa [P5.ivec, ofAdd_toAdd, MulEquiv.symm_apply_apply] at this

theorem sylowThree_card_factorization :
    (Nat.card Rgrp).factorization 3 = 9 := by
  rw [card_stdGroup, Nat.factorization_def _ Nat.prime_three]
  decide +kernel

theorem exists_sylow_isExt_fixDim :
    ∃ (P : Sylow 3 Rgrp) (E : Subgroup P) (ι : E ≃* Multiplicative E5) (ρ : P →* GL5),
      IsExt Pbar E ι ρ ∧
        (∀ x : E5, fixDim (((ι.symm (Multiplicative.ofAdd x) : E) : P) : Rgrp) = 6 + rk x) ∧
        (∀ e : E, fixDim (((e : P) : Rgrp)) = 6 + rk (P5.ivec E ι e)) := by
  obtain ⟨T, E, ι, ρ, h, h1, h2⟩ := exists_isExt_stdGroup_fixDim
  have hcard : Nat.card T = 3 ^ 9 := h.pbar_card
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Rgrp := Nat.finite_of_card_ne_zero (by rw [card_stdGroup]; norm_num)
  exact ⟨Sylow.ofCard T (by rw [hcard, sylowThree_card_factorization]), E, ι, ρ, h, h1, h2⟩

end CFSG.Monster.Existence.StdOdd.Cert
