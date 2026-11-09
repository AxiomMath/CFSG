module

public import Certificates.Kernel.LocalComp.HeGS36
public import Certificates.Data.Kernel.CF23L34.RegRun1
public import Certificates.Data.Kernel.CF23L34.HeGSRVals
public import CFSG.Certificates.Kernel.Enum.DefsC
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PK.Perm.CompC

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGSR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool CFSG.KC.CF23L34
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.GrSLit.HeGS
open CertificateChecks.KernelLC.HeFix CertificateChecks.KernelLC.HeGS36

@[expose] def ew (k : Nat) : List Nat := heDWords.getD (k % 5) []

@[expose] noncomputable def R0 : List (Nat × Nat) :=
  (List.range 10).map fun k =>
    if k < 5 then (K (ew k), K (ew k).reverse)
    else (pc (pc gT (K (ew k))) gI, pc (pc gT (K (ew k).reverse)) gI)

@[expose] noncomputable def gsrPc (p q : Nat) : Nat := pcompC 8330 14 (mask 14) p q

theorem gsrPc_eq : gsrPc = pc :=
  funext fun p => funext fun q => CFSG.KS.PK.pcompC_eq 8330 14 p q

@[expose] noncomputable def gsrK (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 8330 14)
    (fun j _ acc => gsrPc (CertificateChecks.KernelSporSch.HeB14.C0 j) acc) w

theorem gsrK_eq' : ∀ w, gsrK w = K w
  | [] => rfl
  | j :: w => by
    change gsrPc (CertificateChecks.KernelSporSch.HeB14.C0 j) (gsrK w) =
      pc (CertificateChecks.KernelSporSch.HeB14.C0 j) (K w)
    rw [gsrPc_eq, gsrK_eq' w]

theorem gsrK_eq : gsrK = K := funext gsrK_eq'

@[expose] noncomputable def gsrGT : Nat :=
  gsrPc (gsrPc (gsrPc (gsrPc (gsrPc G1I (HG.F 0)) (HG.F 1)) (gsrK heGSVWord))
    (gsrPc (gsrPc (gsrPc G1I (HG.F 0)) (HG.F 1)) (gsrK heGSVWord))) G1I

theorem gsrGT_eq : gsrGT = gT := by
  unfold gsrGT
  rw [gsrPc_eq, gsrK_eq]
  rfl

@[expose] noncomputable def gsrStep (k : Nat) : Bool :=
  Nat.beq (heGSRT.getD (10 + k) (0, 0)).1
      (rW1 gsrPc (pidn 8330 14) (heGSRT.take (10 + k)) (heGSProg.getD k [])).1 &&
    Nat.beq (heGSRT.getD (10 + k) (0, 0)).2
      (rW1 gsrPc (pidn 8330 14) (heGSRT.take (10 + k)) (heGSProg.getD k [])).2

@[expose] noncomputable def gsrR0B (i : Nat) : Bool :=
  Nat.beq (heGSRT.getD i (0, 0)).1
      (if i < 5 then gsrK (ew i) else gsrPc (gsrPc heGSRG (gsrK (ew i))) heGSRGI) &&
    Nat.beq (heGSRT.getD i (0, 0)).2
      (if i < 5 then gsrK (ew i).reverse else gsrPc (gsrPc heGSRG (gsrK (ew i).reverse)) heGSRGI)

theorem gsrG_eq : gT = heGSRG := by
  have h : Nat.beq gsrGT heGSRG = true := by quickRfl
  rw [← gsrGT_eq]
  exact Nat.eq_of_beq_eq_true h

theorem gsrGI_eq : gI = heGSRGI := by
  have h : Nat.beq (pinvS 8330 14 (mask 14) heGSRG) heGSRGI = true := by quickRfl
  unfold gI
  rw [gsrG_eq]
  exact Nat.eq_of_beq_eq_true h

theorem gsrStep_eq {k : Nat} (h : gsrStep k = true) :
    heGSRT.getD (10 + k) (0, 0) =
      rW1 pc (pidn 8330 14) (heGSRT.take (10 + k)) (heGSProg.getD k []) := by
  unfold gsrStep at h
  rw [Bool.and_eq_true] at h
  rw [← gsrPc_eq]
  exact Prod.ext (Nat.eq_of_beq_eq_true h.1) (Nat.eq_of_beq_eq_true h.2)

theorem gsrFold (m : Nat → Nat → Nat) (e : Nat) (T : List (Nat × Nat)) :
    ∀ (P : List (List Int)) (S : List (Nat × Nat)), T.take S.length = S →
      S.length + P.length = T.length →
      (∀ k < P.length, T.getD (S.length + k) (0, 0) =
        rW1 m e (T.take (S.length + k)) (P.getD k [])) →
      P.foldl (fun R w => R ++ [rW1 m e R w]) S = T
  | [], S, hS, hl, _ => by
    rw [List.length_nil, Nat.add_zero] at hl
    rw [List.foldl_nil, ← hS]
    exact List.take_of_length_le (Nat.le_of_eq hl.symm)
  | w :: P, S, hS, hl, hs => by
    rw [List.length_cons] at hl
    have hlt : S.length < T.length := by omega
    have h0 := hs 0 (by simp)
    rw [Nat.add_zero, hS, List.getD_cons_zero] at h0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some] at h0
    rw [List.foldl_cons]
    refine gsrFold m e T P (S ++ [rW1 m e S w]) ?_ ?_ ?_
    · rw [List.length_append, List.length_singleton, List.take_add_one, hS,
        List.getElem?_eq_getElem hlt, Option.toList_some, h0]
    · rw [List.length_append, List.length_singleton]
      omega
    · intro k hk
      have e1 : S.length + (k + 1) = (S ++ [rW1 m e S w]).length + k := by
        rw [List.length_append, List.length_singleton]
        omega
      have := hs (k + 1) (by rw [List.length_cons]; omega)
      rw [e1, List.getD_cons_succ] at this
      exact this

theorem gsrSt0 : gsrStep 0 = true := by
  quickRfl

theorem gsrSt1 : gsrStep 1 = true := by
  quickRfl

theorem gsrSt2 : gsrStep 2 = true := by
  quickRfl

theorem gsrSt3 : gsrStep 3 = true := by
  quickRfl

theorem gsrSt4 : gsrStep 4 = true := by
  quickRfl

theorem gsrSt5 : gsrStep 5 = true := by
  quickRfl

theorem gsrSt6 : gsrStep 6 = true := by
  quickRfl

theorem gsrSt7 : gsrStep 7 = true := by
  quickRfl

theorem gsrSt8 : gsrStep 8 = true := by
  quickRfl

theorem gsrSt9 : gsrStep 9 = true := by
  quickRfl

theorem gsrSt10 : gsrStep 10 = true := by
  quickRfl

theorem gsrSt11 : gsrStep 11 = true := by
  quickRfl

theorem gsrSt12 : gsrStep 12 = true := by
  quickRfl

theorem gsrSt13 : gsrStep 13 = true := by
  quickRfl

theorem gsrSt14 : gsrStep 14 = true := by
  quickRfl

theorem gsrSt15 : gsrStep 15 = true := by
  quickRfl

theorem gsrSt16 : gsrStep 16 = true := by
  quickRfl

theorem gsrSt17 : gsrStep 17 = true := by
  quickRfl

theorem gsrSt18 : gsrStep 18 = true := by
  quickRfl

theorem gsrSt19 : gsrStep 19 = true := by
  quickRfl

theorem gsrSt20 : gsrStep 20 = true := by
  quickRfl

theorem gsrSt21 : gsrStep 21 = true := by
  quickRfl

theorem gsrSt22 : gsrStep 22 = true := by
  quickRfl

theorem gsrSt23 : gsrStep 23 = true := by
  quickRfl

theorem gsrSt24 : gsrStep 24 = true := by
  quickRfl

theorem gsrSt25 : gsrStep 25 = true := by
  quickRfl

theorem gsrSt26 : gsrStep 26 = true := by
  quickRfl

theorem gsrSt27 : gsrStep 27 = true := by
  quickRfl

theorem gsrSt28 : gsrStep 28 = true := by
  quickRfl

theorem gsrSt29 : gsrStep 29 = true := by
  quickRfl

theorem gsrSt30 : gsrStep 30 = true := by
  quickRfl

theorem gsrSt31 : gsrStep 31 = true := by
  quickRfl

theorem gsrSt32 : gsrStep 32 = true := by
  quickRfl

theorem gsrSt33 : gsrStep 33 = true := by
  quickRfl

theorem gsrSt34 : gsrStep 34 = true := by
  quickRfl

theorem gsrSt35 : gsrStep 35 = true := by
  quickRfl

theorem gsrSt36 : gsrStep 36 = true := by
  quickRfl

theorem gsrSt37 : gsrStep 37 = true := by
  quickRfl

theorem gsrSt38 : gsrStep 38 = true := by
  quickRfl

theorem gsrSt39 : gsrStep 39 = true := by
  quickRfl

theorem gsrSt40 : gsrStep 40 = true := by
  quickRfl

theorem gsrSt41 : gsrStep 41 = true := by
  quickRfl

theorem gsrSt42 : gsrStep 42 = true := by
  quickRfl

theorem gsrSt43 : gsrStep 43 = true := by
  quickRfl

theorem gsrSt44 : gsrStep 44 = true := by
  quickRfl

theorem gsrSt45 : gsrStep 45 = true := by
  quickRfl

theorem gsrSt46 : gsrStep 46 = true := by
  quickRfl

theorem gsrSt47 : gsrStep 47 = true := by
  quickRfl

theorem gsrSt48 : gsrStep 48 = true := by
  quickRfl

theorem gsrSt49 : gsrStep 49 = true := by
  quickRfl

theorem gsrSt50 : gsrStep 50 = true := by
  quickRfl

theorem gsrSt51 : gsrStep 51 = true := by
  quickRfl

theorem gsrSt52 : gsrStep 52 = true := by
  quickRfl

theorem gsrSt53 : gsrStep 53 = true := by
  quickRfl

theorem gsrSt54 : gsrStep 54 = true := by
  quickRfl

theorem gsrSt55 : gsrStep 55 = true := by
  quickRfl

theorem gsrSt56 : gsrStep 56 = true := by
  quickRfl

theorem gsrSt57 : gsrStep 57 = true := by
  quickRfl

theorem gsrSt58 : gsrStep 58 = true := by
  quickRfl

theorem gsrSt59 : gsrStep 59 = true := by
  quickRfl

theorem gsrSt60 : gsrStep 60 = true := by
  quickRfl

theorem gsrSt61 : gsrStep 61 = true := by
  quickRfl

theorem gsrSt62 : gsrStep 62 = true := by
  quickRfl

theorem gsrSt63 : gsrStep 63 = true := by
  quickRfl

theorem gsrSt64 : gsrStep 64 = true := by
  quickRfl

theorem gsrSt65 : gsrStep 65 = true := by
  quickRfl

theorem gsrSt66 : gsrStep 66 = true := by
  quickRfl

theorem gsrSt67 : gsrStep 67 = true := by
  quickRfl

theorem gsrSt68 : gsrStep 68 = true := by
  quickRfl

theorem gsrSt69 : gsrStep 69 = true := by
  quickRfl

theorem gsrSt70 : gsrStep 70 = true := by
  quickRfl

theorem gsrSt71 : gsrStep 71 = true := by
  quickRfl

theorem gsrSt72 : gsrStep 72 = true := by
  quickRfl

theorem gsrSt73 : gsrStep 73 = true := by
  quickRfl

theorem gsrSt74 : gsrStep 74 = true := by
  quickRfl

theorem gsrSt75 : gsrStep 75 = true := by
  quickRfl

theorem gsrSt76 : gsrStep 76 = true := by
  quickRfl

theorem gsrSt77 : gsrStep 77 = true := by
  quickRfl

theorem gsrSt78 : gsrStep 78 = true := by
  quickRfl

theorem gsrSt79 : gsrStep 79 = true := by
  quickRfl

theorem gsrSt80 : gsrStep 80 = true := by
  quickRfl

theorem gsrSt81 : gsrStep 81 = true := by
  quickRfl

theorem gsrSt82 : gsrStep 82 = true := by
  quickRfl

theorem gsrSt83 : gsrStep 83 = true := by
  quickRfl

theorem gsrSt84 : gsrStep 84 = true := by
  quickRfl

theorem gsrSt85 : gsrStep 85 = true := by
  quickRfl

theorem gsrSt86 : gsrStep 86 = true := by
  quickRfl

theorem gsrSt87 : gsrStep 87 = true := by
  quickRfl

theorem gsrSt88 : gsrStep 88 = true := by
  quickRfl

theorem gsrSt89 : gsrStep 89 = true := by
  quickRfl

theorem gsrSt90 : gsrStep 90 = true := by
  quickRfl

theorem gsrSt91 : gsrStep 91 = true := by
  quickRfl

theorem gsrSt92 : gsrStep 92 = true := by
  quickRfl

theorem gsrSt93 : gsrStep 93 = true := by
  quickRfl

theorem gsrSt94 : gsrStep 94 = true := by
  quickRfl

theorem gsrSt95 : gsrStep 95 = true := by
  quickRfl

theorem gsrSt96 : gsrStep 96 = true := by
  quickRfl

theorem gsrSt97 : gsrStep 97 = true := by
  quickRfl

theorem gsrSt98 : gsrStep 98 = true := by
  quickRfl

theorem gsrSt99 : gsrStep 99 = true := by
  quickRfl

theorem gsrSt100 : gsrStep 100 = true := by
  quickRfl

theorem gsrSt101 : gsrStep 101 = true := by
  quickRfl

theorem gsrSt102 : gsrStep 102 = true := by
  quickRfl

theorem gsrSt103 : gsrStep 103 = true := by
  quickRfl

theorem gsrSt104 : gsrStep 104 = true := by
  quickRfl

theorem gsrSt105 : gsrStep 105 = true := by
  quickRfl

theorem gsrSt106 : gsrStep 106 = true := by
  quickRfl

theorem gsrSt107 : gsrStep 107 = true := by
  quickRfl

theorem gsrSt108 : gsrStep 108 = true := by
  quickRfl

theorem gsrSt109 : gsrStep 109 = true := by
  quickRfl

theorem gsrSt110 : gsrStep 110 = true := by
  quickRfl

theorem gsrSt111 : gsrStep 111 = true := by
  quickRfl

theorem gsrSt112 : gsrStep 112 = true := by
  quickRfl

theorem gsrSt113 : gsrStep 113 = true := by
  quickRfl

theorem gsrSt114 : gsrStep 114 = true := by
  quickRfl

theorem gsrSt115 : gsrStep 115 = true := by
  quickRfl

theorem gsrSt116 : gsrStep 116 = true := by
  quickRfl

theorem gsrSt117 : gsrStep 117 = true := by
  quickRfl

theorem gsrSt118 : gsrStep 118 = true := by
  quickRfl

theorem gsrSt119 : gsrStep 119 = true := by
  quickRfl

theorem gsrSt120 : gsrStep 120 = true := by
  quickRfl

theorem gsrSt121 : gsrStep 121 = true := by
  quickRfl

theorem gsrSt122 : gsrStep 122 = true := by
  quickRfl

theorem gsrSt123 : gsrStep 123 = true := by
  quickRfl

theorem gsrSt124 : gsrStep 124 = true := by
  quickRfl

theorem gsrStAll : ∀ k < 125, gsrStep k = true
  | 0, _ => gsrSt0
  | 1, _ => gsrSt1
  | 2, _ => gsrSt2
  | 3, _ => gsrSt3
  | 4, _ => gsrSt4
  | 5, _ => gsrSt5
  | 6, _ => gsrSt6
  | 7, _ => gsrSt7
  | 8, _ => gsrSt8
  | 9, _ => gsrSt9
  | 10, _ => gsrSt10
  | 11, _ => gsrSt11
  | 12, _ => gsrSt12
  | 13, _ => gsrSt13
  | 14, _ => gsrSt14
  | 15, _ => gsrSt15
  | 16, _ => gsrSt16
  | 17, _ => gsrSt17
  | 18, _ => gsrSt18
  | 19, _ => gsrSt19
  | 20, _ => gsrSt20
  | 21, _ => gsrSt21
  | 22, _ => gsrSt22
  | 23, _ => gsrSt23
  | 24, _ => gsrSt24
  | 25, _ => gsrSt25
  | 26, _ => gsrSt26
  | 27, _ => gsrSt27
  | 28, _ => gsrSt28
  | 29, _ => gsrSt29
  | 30, _ => gsrSt30
  | 31, _ => gsrSt31
  | 32, _ => gsrSt32
  | 33, _ => gsrSt33
  | 34, _ => gsrSt34
  | 35, _ => gsrSt35
  | 36, _ => gsrSt36
  | 37, _ => gsrSt37
  | 38, _ => gsrSt38
  | 39, _ => gsrSt39
  | 40, _ => gsrSt40
  | 41, _ => gsrSt41
  | 42, _ => gsrSt42
  | 43, _ => gsrSt43
  | 44, _ => gsrSt44
  | 45, _ => gsrSt45
  | 46, _ => gsrSt46
  | 47, _ => gsrSt47
  | 48, _ => gsrSt48
  | 49, _ => gsrSt49
  | 50, _ => gsrSt50
  | 51, _ => gsrSt51
  | 52, _ => gsrSt52
  | 53, _ => gsrSt53
  | 54, _ => gsrSt54
  | 55, _ => gsrSt55
  | 56, _ => gsrSt56
  | 57, _ => gsrSt57
  | 58, _ => gsrSt58
  | 59, _ => gsrSt59
  | 60, _ => gsrSt60
  | 61, _ => gsrSt61
  | 62, _ => gsrSt62
  | 63, _ => gsrSt63
  | 64, _ => gsrSt64
  | 65, _ => gsrSt65
  | 66, _ => gsrSt66
  | 67, _ => gsrSt67
  | 68, _ => gsrSt68
  | 69, _ => gsrSt69
  | 70, _ => gsrSt70
  | 71, _ => gsrSt71
  | 72, _ => gsrSt72
  | 73, _ => gsrSt73
  | 74, _ => gsrSt74
  | 75, _ => gsrSt75
  | 76, _ => gsrSt76
  | 77, _ => gsrSt77
  | 78, _ => gsrSt78
  | 79, _ => gsrSt79
  | 80, _ => gsrSt80
  | 81, _ => gsrSt81
  | 82, _ => gsrSt82
  | 83, _ => gsrSt83
  | 84, _ => gsrSt84
  | 85, _ => gsrSt85
  | 86, _ => gsrSt86
  | 87, _ => gsrSt87
  | 88, _ => gsrSt88
  | 89, _ => gsrSt89
  | 90, _ => gsrSt90
  | 91, _ => gsrSt91
  | 92, _ => gsrSt92
  | 93, _ => gsrSt93
  | 94, _ => gsrSt94
  | 95, _ => gsrSt95
  | 96, _ => gsrSt96
  | 97, _ => gsrSt97
  | 98, _ => gsrSt98
  | 99, _ => gsrSt99
  | 100, _ => gsrSt100
  | 101, _ => gsrSt101
  | 102, _ => gsrSt102
  | 103, _ => gsrSt103
  | 104, _ => gsrSt104
  | 105, _ => gsrSt105
  | 106, _ => gsrSt106
  | 107, _ => gsrSt107
  | 108, _ => gsrSt108
  | 109, _ => gsrSt109
  | 110, _ => gsrSt110
  | 111, _ => gsrSt111
  | 112, _ => gsrSt112
  | 113, _ => gsrSt113
  | 114, _ => gsrSt114
  | 115, _ => gsrSt115
  | 116, _ => gsrSt116
  | 117, _ => gsrSt117
  | 118, _ => gsrSt118
  | 119, _ => gsrSt119
  | 120, _ => gsrSt120
  | 121, _ => gsrSt121
  | 122, _ => gsrSt122
  | 123, _ => gsrSt123
  | 124, _ => gsrSt124
  | _ + 125, h => absurd h (by omega)

theorem gsrR0 : gsrR0B 0 = true := by
  quickRfl

theorem gsrR1 : gsrR0B 1 = true := by
  quickRfl

theorem gsrR2 : gsrR0B 2 = true := by
  quickRfl

theorem gsrR3 : gsrR0B 3 = true := by
  quickRfl

theorem gsrR4 : gsrR0B 4 = true := by
  quickRfl

theorem gsrR5 : gsrR0B 5 = true := by
  quickRfl

theorem gsrR6 : gsrR0B 6 = true := by
  quickRfl

theorem gsrR7 : gsrR0B 7 = true := by
  quickRfl

theorem gsrR8 : gsrR0B 8 = true := by
  quickRfl

theorem gsrR9 : gsrR0B 9 = true := by
  quickRfl

theorem gsrRAll : ∀ i < 10, gsrR0B i = true
  | 0, _ => gsrR0
  | 1, _ => gsrR1
  | 2, _ => gsrR2
  | 3, _ => gsrR3
  | 4, _ => gsrR4
  | 5, _ => gsrR5
  | 6, _ => gsrR6
  | 7, _ => gsrR7
  | 8, _ => gsrR8
  | 9, _ => gsrR9
  | _ + 10, h => absurd h (by omega)

theorem gsrR0_eq : heGSRT.take 10 = R0 := by
  have hT : heGSRT.length = 135 := rfl
  apply List.ext_getElem
  · rw [List.length_take, hT]
    simp [R0]
  · intro i h1 h2
    have hi : i < 10 := by simpa [R0] using h2
    have h := gsrRAll i hi
    unfold gsrR0B at h
    rw [gsrK_eq, gsrPc_eq, Bool.and_eq_true] at h
    have hlt : i < heGSRT.length := by
      have hl : heGSRT.length = 135 := rfl
      omega
    have hg : heGSRT.getD i (0, 0) = heGSRT[i] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [List.getElem_take, ← hg]
    simp only [R0, List.getElem_map, List.getElem_range, gsrG_eq, gsrGI_eq]
    refine Prod.ext ((Nat.eq_of_beq_eq_true h.1).trans ?_) ((Nat.eq_of_beq_eq_true h.2).trans ?_)
    · split <;> rfl
    · split <;> rfl

theorem gsrRun : rRun1 pc (pidn 8330 14) R0 heGSProg = heGSRT := by
  have hl : R0.length = 10 := by simp [R0]
  have hp : heGSProg.length = 125 := rfl
  have hT : heGSRT.length = 135 := rfl
  unfold rRun1
  refine gsrFold pc (pidn 8330 14) heGSRT heGSProg R0 ?_ ?_ ?_
  · rw [hl]
    exact gsrR0_eq
  · rw [hl, hp, hT]
  · intro k hk
    rw [hp] at hk
    rw [hl]
    exact gsrStep_eq (gsrStAll k hk)

theorem ch22702_g : Nat.beq (pc gT (HG.F 0)) (pc (K heGSVWord) gT) = true := by
  rw [gsrG_eq, ← gsrPc_eq, ← gsrK_eq]
  quickRfl

theorem ch22702_run :
    (Nat.beq ((rRun1 pc (pidn 8330 14) R0 heGSProg).getD 133 (0, 0)).1 (HG.F 0) &&
      Nat.beq ((rRun1 pc (pidn 8330 14) R0 heGSProg).getD 134 (0, 0)).1 (HG.F 1)) = true := by
  rw [gsrRun]
  quickRfl

end CertificateChecks.KernelLC.HeGSR

end
