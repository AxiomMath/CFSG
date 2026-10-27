module

public import Certificates.Kernel.Co3Cent.ChecksL
public import Certificates.Kernel.Co3T.Facts
public import CFSG.Certificates.Kernel.K426KSound
public import CFSG.Certificates.Kernel.HeDihKSound
public import CFSG.Certificates.Kernel.D4Sound
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.OrbRow.WordRep
public import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import CFSG.RankThree.PartTwo.KFacts.K426Kit
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo3Cent

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
open CFSG.KC.K426K CFSG.KC.HeDih CFSG.KC.PGrp CFSG.KD.Co3Cent CertificateChecks.KernelCo3T
open CFSG.KC.OrbRow (getLs lettersK)
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.Monster.B.Mathieu CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.HardMathSupport.Dickson.I271.Co3Cent
open CFSG.HardMathSupport.Dickson.I271.L28Presentation
open CFSG.Monster.B.Co2 (allLt_iff permOfArr eqA_iff rep_idA)
open CFSG.KS.Raw.Orb (PRep prep_of_rep)

theorem keys_lt : ∀ q ∈ keys, q < 276 := by decide

theorem arr_eq : ∀ k < 38, arr k = unpack 276 9 (CH.F k) := by
  intro k hk
  rw [arr, CH.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound CH.all k hk

theorem gLf : Nat.beq (EL.G 0) (CH.F 36) = true ∧ Nat.beq (EL.G 1) (CH.F 37) = true ∧
    Nat.beq (EL.G 0) (posWordK 276 9 EC.G (getLs WL 0)) = true ∧
    Nat.beq (EL.G 1) (posWordK 276 9 EC.G (getLs WL 1)) = true ∧
    allN 2 (fun l => lettersK 3 7 (getLs WL l)) = true ∧ Nat.beq EL.ng 2 = true ∧
    Nat.beq EL.N 504 = true := by
  have h := ch17370_lg
  simp only [bAnd_iff] at h
  exact h

theorem ngL : EL.ng = 2 := Nat.eq_of_beq_eq_true gLf.2.2.2.2.2.1

theorem nL : EL.N = 504 := Nat.eq_of_beq_eq_true gLf.2.2.2.2.2.2

theorem gL_hex {k : ℕ} (hk : k < 2) : EL.G k = CH.F (36 + k) := by
  interval_cases k
  · exact Nat.eq_of_beq_eq_true gLf.1
  · exact Nat.eq_of_beq_eq_true gLf.2.1

theorem gL_word {k : ℕ} (hk : k < 2) : EL.G k = posWordK 276 9 EC.G (getLs WL k) := by
  interval_cases k
  · exact Nat.eq_of_beq_eq_true gLf.2.2.1
  · exact Nat.eq_of_beq_eq_true gLf.2.2.2.1

theorem lGens_get {k : ℕ} (hk : k < 2) : (lGens ())[k]! = unpack 276 9 (EL.G k) := by
  unfold lGens
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, gL_hex hk]
  exact arr_eq _ (by omega)

theorem pp_posWord {G : ℕ → ℕ} :
    ∀ (wd : List ℕ), (∀ l ∈ wd, PP 276 9 (G l)) → ∀ (acc : ℕ), PP 276 9 acc →
      PP 276 9 (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => strictN (pcomp 276 9 (mask 9) acc (G l)) ih) wd acc)
  | [], _, _, h => h
  | l :: wd, hG, acc, h => by
    change PP 276 9 (strictN (pcomp 276 9 (mask 9) acc (G l)) _)
    rw [CFSG.KC.OrbRow.strictN_apply]
    exact pp_posWord wd (fun l' hl' => hG l' (List.mem_cons_of_mem _ hl')) _
      (PP.mul h (hG l List.mem_cons_self))

theorem ngC : EC.ng = 3 := Nat.eq_of_beq_eq_true eC.1

theorem letL {k : ℕ} (hk : k < 2) : ∀ l ∈ getLs WL k, l < 3 := fun l hl =>
  (CFSG.KC.OrbRow.lettersK_sound (allN_spec gLf.2.2.2.2.1 k hk) l hl).1

theorem ppL {k : ℕ} (hk : k < 2) : PP 276 9 (EL.G k) := by
  rw [gL_word hk]
  exact pp_posWord _ (fun l hl => pp_of_permB hw (pCG l (by rw [ngC]; exact letL hk l hl))) _
    (PP.id hw)

theorem bindL : BindA 276 9 (lGens ()) EL.ng EL.G :=
  ⟨by rw [ngL]; simp [lGens], fun k hk => lGens_get (by rw [ngL] at hk; exact hk)⟩

theorem pL : ∀ k < EL.ng, permB 276 9 (EL.G k) = true := fun k hk =>
  permB_of_pp (ppL (by rw [ngL] at hk; exact hk))

theorem okL : bfsK 276 9 EL.ng EL.G EL.N EL.T EL.E EL.S = true :=
  bfsK_of_slices (L := 56) (K := 9) (C := EL.C) (by decide) (by norm_num) hw EL.g EL.csAll EL.t0
    EL.dist (Nat.eq_of_beq_eq_true EL.c0) (Nat.eq_of_beq_eq_true EL.cK) EL.rsAll

theorem enumL : enumOK 276 (lGens ()) keys (lCert ()) = true ∧ (lCert ()).pts.size = EL.N ∧
    ∀ i < EL.N, (lCert ()).pts[i]! = unpack 276 9 (EL.T i) := by
  exact enum_of (fuel := 520) bindL pL okL keys_lt EL.keys (by rw [nL]; norm_num)

theorem sizeL : (lGens ()).size = 2 := bindL.1.trans ngL

theorem sizeC : (cGens ()).size = 3 := bindC.1.trans ngC

theorem derived_ok : derivedLeOK 276 (cGens ()) (lGens ()) keys (lCert ()) 504 = true :=
  derivedLeOK_of hw enumL.1 enumL.2.1 enumL.2.2 (CFSG.KC.D4K.permB_pts okL pL) bindC pCG bindL pL nL
    ch17370_ld

theorem cEnum : enumOK 276 (cGens ()) keys (cCert ()) = true := by
  unfold cCert
  rw [keys_eq]
  exact enumC.1

theorem words_ok : wordsOneOK 276 (lGens ()) l28Words = true := by
  have hg : ∀ k < 2, (lGens ())[k]! = unpack 276 9 (EL.G k) := fun k hk => lGens_get hk
  have hp : ∀ k < 2, PP 276 9 (EL.G k) := fun k hk => ppL hk
  unfold wordsOneOK
  rw [Bool.and_eq_true, allLt_iff, List.all_eq_true]
  refine ⟨fun k hk => enumOK_gens_valid enumL.1 hk, fun wd hwd => ?_⟩
  obtain ⟨h1, h2⟩ := evalWA_unpack hw hg hp wd
  rw [h1, idA_eq hw, eqA_PP h2 (PP.id hw)]
  exact List.all_eq_true.1 ch17370_lr wd hwd

theorem gL_mem {k : ℕ} (hk : k < 2) :
    permOfArr 276 (lGens ())[k]! ∈ closure (permsA 276 (cGens ())) := by
  have hrL : PRep 276 9 (EL.G k) (permOfArr 276 (lGens ())[k]!) := by
    have h := rep_of_validA (enumOK_gens_valid enumL.1 (k := k) (by rw [sizeL]; exact hk))
    rw [lGens_get hk] at h ⊢
    exact prep_of_rep h
  have hrC : ∀ l ∈ getLs WL k, PRep 276 9 (EC.G l) (permOfArr 276 (cGens ())[l]!) := by
    intro l hl
    have hl3 := letL hk l hl
    have h := rep_of_validA (enumOK_gens_valid cEnum (k := l) (by rw [sizeC]; exact hl3))
    rw [bindC.2 l (by rw [ngC]; exact hl3)] at h ⊢
    exact prep_of_rep h
  have hw' := CFSG.KC.OrbRow.posWordK_rep (n := 276) (w := 9) (by norm_num) (by norm_num) hrC
  rw [← gL_word hk] at hw'
  rw [CFSG.KC.OrbRow.prep_unique hrL hw']
  refine list_prod_mem fun g hg => ?_
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
  exact subset_closure ⟨l, by change l < (cGens ()).size; rw [sizeC]; exact letL hk l hl, rfl⟩

theorem caseC :
    closure (permsA 276 (lGens ())) ≤ closure (permsA 276 (cGens ())) ∧
    ⁅closure (permsA 276 (cGens ())), closure (permsA 276 (cGens ()))⁆ ≤
      closure (permsA 276 (lGens ())) ∧
    Nat.card (closure (permsA 276 (lGens ()))) = 504 ∧
    ∀ w ∈ l28Words,
      CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
        (fun i : Fin 2 => permOfArr 276 (lGens ())[i.val]!) w = 1 := by
  have hval : ∀ k < (cGens ()).size, validA 276 (cGens ())[k]! = true :=
    fun k hk => enumOK_gens_valid cEnum hk
  obtain ⟨hder, hLcard⟩ := commutator_le_of_derivedLeOK keys_lt hval derived_ok
  have hLC : closure (permsA 276 (lGens ())) ≤ closure (permsA 276 (cGens ())) := by
    rw [closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by rw [← sizeL]; exact hk
    exact gL_mem hk2
  have hl2 : (lGens ()).size = 2 := sizeL
  have h5 := words_ok
  have hrels : ∀ w ∈ l28Words,
      CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW
        (fun i : Fin 2 => permOfArr 276 (lGens ())[i.val]!) w = 1 := by
    simp only [wordsOneOK, Bool.and_eq_true, List.all_eq_true] at h5
    intro w hw
    have hv := rep_evalWA (m := 2) (gs := lGens ()) (fun k hk => enumOK_gens_valid enumL.1 hk)
      (by rw [hl2]) w
    exact (eqA_iff hv rep_idA).1 (h5.2 w hw)
  exact ⟨hLC, hder, hLcard, hrels⟩

end CertificateChecks.KernelCo3Cent

end
