module

public import CFSG.Quasithin.AppendixH.H16.MaskChief
public import CFSG.Quasithin.Background.HLUBlocks
public import CFSG.Quasithin.Background.HLUCode24Gen
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.Quasithin.AppendixH.H16.SextetPack

public section

namespace CFSG.ASVolI.H16

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Parab CFSG.Quasithin.H.Coc CFSG.Quasithin.H.LU
  CFSG.Quasithin.H.LU24

@[expose] def sxTC : List ℕ := [1547, 790, 126, 38, 1430, 310, 598, 1268, 592, 1168, 1300]

theorem sxTC_eq : matOf 11 (actC11 sxTArr) = sxTC := by
  decide +kernel

theorem sxTC_lt : ∀ c ∈ sxTC, c < 2 ^ 11 := by
  decide +kernel

@[expose] def ksConjT (i : ℕ) : ℕ := [30, 57, 58, 41, 9, 43].getD i 0

@[expose] def ksConjTInv (i : ℕ) : ℕ := [46, 40, 29, 62, 10, 24].getD i 0

theorem ks6_conj_t : ∀ i < 6,
    cArr (cArr sxTArr (ks6Arr i)) sxTInv =
        wArr ((List.range 6).map ks6Arr) (subW (ksConjT i)) ∧
      cArr (cArr sxTInv (ks6Arr i)) sxTArr =
        wArr ((List.range 6).map ks6Arr) (subW (ksConjTInv i)) :=
  SxPack.conj_of_conjB ksConjT ksConjTInv (by decide +kernel)

@[expose] def sTP : Equiv.Perm (Fin 6) :=
  perm6 ![0, 3, 4, 5, 2, 1] ![0, 5, 4, 1, 2, 3] (by decide)

theorem sign_sTP : Equiv.Perm.sign sTP ≠ 1 := by
  decide

theorem th_t_ok : ∀ m ∈ combos uSBasis, ∀ i : Fin 6,
    bvec 6 (actM thC (actM sxTC m)) i =
      bvec 6 (actM thC m) (sTP⁻¹ i) + bvec 6 (actM thC m) (sTP⁻¹ 5) := by
  decide +kernel

@[expose] def popPar : ℕ → ℕ → Bool
  | 0, _ => false
  | k + 1, m => (m % 2 == 1) != popPar k (m / 2)

@[expose] def v10Basis : List ℕ := [1477, 1894, 671, 143, 568, 1562, 82, 1355, 1572, 948]

theorem v10Basis_lt : ∀ a ∈ v10Basis, a < 2 ^ 11 := by
  decide +kernel

theorem v10Basis_comm :
    v10Basis = [actM sxG1C 1 ^^^ 1, actM sxG1C 2 ^^^ 2, actM sxG1C 4 ^^^ 4, actM sxG1C 8 ^^^ 8,
      actM sxG1C 16 ^^^ 16, actM sxG1C 32 ^^^ 32, actM sxG1C 128 ^^^ 128,
      actM sxG1C 256 ^^^ 256, actM sxG2C 1 ^^^ 1, actM sxG2C 16 ^^^ 16] := by
  decide +kernel

theorem v10_nodup : (combos v10Basis).Nodup :=
  (nodup_of_nodupB _ 0 (by decide +kernel)).1

theorem v10_par_of_mem : ∀ m ∈ combos v10Basis, popPar 11 (m &&& 1192) = false := by
  decide +kernel

theorem v10_red_of_par : ∀ m < 2 ^ 11, popPar 11 (m &&& 1192) = false →
    reduceBy (echelon v10Basis) m = 0 := by
  have hp := SxPack.parK_eq (p := popPar) (fun _ => rfl) (fun _ _ => rfl)
  have hE : echelon v10Basis = [1477, 675, 60, 143, 20, 320, 70, 1, 2, 4] := by
    decide +kernel
  have h := SxPack.of_allLt64 (f := SxPack.redB [1477, 675, 60, 143, 20, 320, 70, 1, 2, 4])
    (a := 32) (by decide +kernel)
  intro m hm hq
  rw [hE]
  rw [hp] at hq
  exact SxPack.redB_spec (h m (lt_of_lt_of_eq hm (by norm_num))) hq

theorem v10_pres : ∀ m < 2 ^ 11,
    popPar 11 (actM sxG1C m &&& 1192) = popPar 11 (m &&& 1192) ∧
    popPar 11 (actM sxG2C m &&& 1192) = popPar 11 (m &&& 1192) ∧
    popPar 11 (actM sxTC m &&& 1192) = popPar 11 (m &&& 1192) := by
  have hp := SxPack.parK_eq (p := popPar) (fun _ => rfl) (fun _ _ => rfl)
  have h := SxPack.of_allLt64 (f := SxPack.presB sxTC) (a := 32) (by decide +kernel)
  intro m hm
  rw [hp, hp, hp, hp]
  exact SxPack.presB_spec (h m (lt_of_lt_of_eq hm (by norm_num)))

theorem us_le_v10 : ∀ u ∈ uSMasks, popPar 11 (u &&& 1192) = false := by
  decide +kernel

theorem par_eight : popPar 11 (8 &&& 1192) = true := by
  decide +kernel

@[expose] def words2 : List (List ℕ) := [[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1]]

@[expose] def words3 : List (List ℕ) :=
  words2 ++ [[0, 0, 0], [0, 0, 1], [0, 1, 0], [0, 1, 1], [1, 0, 0], [1, 0, 1], [1, 1, 0], [1, 1, 1]]

theorem chief_US : chiefCheck [sxG1C, sxG2C] [] uSBasis words2 = true := by
  decide +kernel

theorem chief_V10_US : chiefCheck [sxG1C, sxG2C] uSBasis v10Basis words3 = true := by
  rw [SxPack.chiefCheck_eq]
  decide +kernel

@[expose] def ctr (i : ℕ) : ℕ := [22, 153, 80, 207, 202, 71].getD i 0

@[expose] def xorCtr (J : ℕ) : ℕ :=
  (List.range 6).foldl (fun a j => if J.testBit j then a ^^^ ctr j else a) 0

theorem ks6_transv : ∀ i < 6, ∀ m < 2 ^ 11,
    (popPar 11 (m &&& 1192) = false → (actM (ksC6 i) m ^^^ m) ∈ uSMasks) ∧
    (popPar 11 (m &&& 1192) = true → (actM (ksC6 i) m ^^^ m ^^^ ctr i) ∈ uSMasks) := by
  have hp := SxPack.parK_eq (p := popPar) (fun _ => rfl) (fun _ _ => rfl)
  have h := SxPack.of_allLt (f := fun i => SxPack.allLt64 (SxPack.transvB ctr i) 32) (n := 6)
    (by decide +kernel)
  intro i hi m hm
  rw [hp]
  exact SxPack.transvB_spec (SxPack.of_allLt64 (h i hi) m (lt_of_lt_of_eq hm (by norm_num)))

theorem ctr_par : ∀ i < 6, popPar 11 (ctr i &&& 1192) = false := by
  decide +kernel

theorem ctr_span : ∀ m < 2 ^ 11, popPar 11 (m &&& 1192) = false →
    ∃ J < 64, (m ^^^ xorCtr J) ∈ uSMasks := by
  have hp := SxPack.parK_eq (p := popPar) (fun _ => rfl) (fun _ _ => rfl)
  have hx : ∀ J < 64, xorCtr J = SxPack.xcK J := by
    decide +kernel
  have h := SxPack.of_allLt64 (f := SxPack.spanB) (a := 32) (by decide +kernel)
  intro m hm hq
  rw [hp] at hq
  obtain ⟨J, hJ, hmem⟩ := SxPack.spanB_spec (h m (lt_of_lt_of_eq hm (by norm_num))) hq
  exact ⟨J, hJ, by rwa [hx J hJ]⟩

theorem fix_ks6 : ∀ m < 2 ^ 11, (∀ i < 6, actM (ksC6 i) m = m) → m ∈ uSMasks := by
  have h := SxPack.of_allLt64 (f := SxPack.fixB) (a := 32) (by decide +kernel)
  intro m hm hf
  exact SxPack.fixB_spec (h m (lt_of_lt_of_eq hm (by norm_num))) hf

end CFSG.ASVolI.H16
