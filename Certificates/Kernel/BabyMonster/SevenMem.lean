module

public import Certificates.Kernel.BabyMonster.MemChain
public import Certificates.Kernel.BabyMonster.Chain
public import CFSG.Certificates.Kernel.BabyMonster.Seven.All
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check7
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check9

public section

namespace CFSG.KC.BM.SevenMem

open CFSG.KC.BM CFSG.KC.BM.MemChain

local notation "sm" => stripMat

variable {S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2))}

theorem fc {W : List Nat} {Ws : List (List Nat)} (w : wfMat W = true) (m : sm W ∈ S)
    (h : ∀ V ∈ Ws, wfMat V = true ∧ sm V ∈ S) : ∀ V ∈ W :: Ws, wfMat V = true ∧ sm V ∈ S := by
  intro V hV
  rcases List.mem_cons.1 hV with rfl | hV
  · exact ⟨w, m⟩
  · exact h V hV

theorem fn : ∀ V ∈ ([] : List (List Nat)), wfMat V = true ∧ sm V ∈ S := by
  intro V hV
  simp at hV

theorem foldl_mem {M : Type*} [Monoid M] {T : Submonoid M} :
    ∀ (L : List M) (x : M), x ∈ T → (∀ y ∈ L, y ∈ T) → L.foldl (· * ·) x ∈ T
  | [], _, hx, _ => hx
  | y :: L, x, hx, hL => foldl_mem L (x * y) (T.mul_mem hx (hL y (List.mem_cons_self ..)))
      fun z hz => hL z (List.mem_cons_of_mem _ hz)

theorem memN {Ws : List (List Nat)} {A C : List Nat} (wA : wfMat A = true) (mA : sm A ∈ S)
    (hW : ∀ V ∈ Ws, wfMat V = true ∧ sm V ∈ S) (h : AllStrips Ws A C) : sm C ∈ S := by
  rw [← stripMat_mul_of_allStrips (fun V hV => (hW V hV).1) wA h]
  refine foldl_mem (T := S) _ _ mA fun y hy => ?_
  obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hy
  exact (hW V hV).2

theorem memInv {A B : List Nat} (wA : wfMat A = true) (wB : wfMat B = true) (mA : sm A ∈ S)
    (h : AllStrips [B] A idStrips) : sm B ∈ S := by
  have e := stripMat_mul_eq_one (Ws := [B]) (by simp [wB]) wA h
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  exact mem_of_mul_eq_one mA e

theorem seven_mem_all (hA1 : sm Seeds.A1 ∈ S) (hA2 : sm Seeds.A2 ∈ S) :
    sm Seven.g ∈ S ∧ sm SevenGen.gi ∈ S ∧ sm SevenGen.s2 ∈ S ∧ sm SevenGen.s2i ∈ S ∧
      sm Seven.al ∈ S ∧ sm Seven.t1 ∈ S := by
  have m_Seven_r0 : sm Seven.r0 ∈ S := memN Seeds.wf_A1 hA1
    (fc Seeds.wf_A2 hA2 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r0 69)
  have m_Seven_r22 : sm Seven.r22 ∈ S := memN Seven.wf_r0 m_Seven_r0
    (fc Seven.wf_r0 m_Seven_r0 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r22 69)
  have m_Seven_r23 : sm Seven.r23 ∈ S := memN Seven.wf_r22 m_Seven_r22
    (fc Seven.wf_r22 m_Seven_r22 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r23 69)
  have m_Seven_r24 : sm Seven.r24 ∈ S := memN Seven.wf_r23 m_Seven_r23
    (fc Seven.wf_r23 m_Seven_r23 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r24 69)
  have m_Seven_r25 : sm Seven.r25 ∈ S := memN Seven.wf_r23 m_Seven_r23
    (fc Seven.wf_r24 m_Seven_r24 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r25 69)
  have m_Seven_r1 : sm Seven.r1 ∈ S := memN Seven.wf_r22 m_Seven_r22
    (fc Seven.wf_r25 m_Seven_r25 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r1 69)
  have m_Seven_m2 : sm Seven.m2 ∈ S := memN Seven.wf_r1 m_Seven_r1
    (fc Seven.wf_r0 m_Seven_r0 <| fc Seeds.wf_A2 hA2 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_m2 69)
  have m_Seven_r26 : sm Seven.r26 ∈ S := memN Seven.wf_m2 m_Seven_m2
    (fc Seven.wf_m2 m_Seven_m2 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r26 69)
  have m_Seven_r27 : sm Seven.r27 ∈ S := memN Seven.wf_r26 m_Seven_r26
    (fc Seven.wf_r26 m_Seven_r26 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r27 69)
  have m_Seven_r28 : sm Seven.r28 ∈ S := memN Seven.wf_r27 m_Seven_r27
    (fc Seven.wf_r27 m_Seven_r27 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r28 69)
  have m_Seven_r29 : sm Seven.r29 ∈ S := memN Seven.wf_r28 m_Seven_r28
    (fc Seven.wf_r28 m_Seven_r28 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r29 69)
  have m_Seven_r30 : sm Seven.r30 ∈ S := memN Seven.wf_r26 m_Seven_r26
    (fc Seven.wf_r29 m_Seven_r29 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r30 69)
  have m_Seven_al : sm Seven.al ∈ S := memN Seven.wf_m2 m_Seven_m2
    (fc Seven.wf_r30 m_Seven_r30 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_al 69)
  have m_Seven_r4 : sm Seven.r4 ∈ S := memN Seeds.wf_A1 hA1
    (fc Seven.wf_al m_Seven_al <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r4 69)
  have m_Seven_r31 : sm Seven.r31 ∈ S := memN Seven.wf_r4 m_Seven_r4
    (fc Seven.wf_r4 m_Seven_r4 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r31 69)
  have m_Seven_m1 : sm Seven.m1 ∈ S := memN Seven.wf_r4 m_Seven_r4
    (fc Seven.wf_r31 m_Seven_r31 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_m1 69)
  have m_Seven_r42 : sm Seven.r42 ∈ S := memN Seven.wf_m1 m_Seven_m1
    (fc Seven.wf_m2 m_Seven_m2 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r42 69)
  have m_Seven_r46 : sm Seven.r46 ∈ S := memN Seven.wf_r42 m_Seven_r42
    (fc Seven.wf_r26 m_Seven_r26 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r46 69)
  have m_Seven_m2i : sm Seven.m2i ∈ S := memInv Seven.wf_m2 Seven.wf_m2i m_Seven_m2
    (by bm_strips CFSG.KC.BM.Seven.c_m2i 69)
  have m_Seven_r41 : sm Seven.r41 ∈ S := memN Seven.wf_m1 m_Seven_m1
    (fc Seven.wf_m2i m_Seven_m2i <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r41 69)
  have m_Seven_r45 : sm Seven.r45 ∈ S := memN Seven.wf_r41 m_Seven_r41
    (fc Seven.wf_m2i m_Seven_m2i <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r45 69)
  have m_Seven_g : sm Seven.g ∈ S := memN Seven.wf_r46 m_Seven_r46
    (fc Seven.wf_m2 m_Seven_m2 <| fc Seven.wf_r45 m_Seven_r45 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_g 69)
  have m_SevenGen_gi : sm SevenGen.gi ∈ S := memInv Seven.wf_g SevenGen.wf_gi m_Seven_g
    (by bm_strips CFSG.KC.BM.SevenGen.c_gi 69)
  have m_SevenGen_r48 : sm SevenGen.r48 ∈ S := memN Seven.wf_r22 m_Seven_r22
    (fc Seven.wf_r0 m_Seven_r0 <| fc Seeds.wf_A2 hA2 <| fc Seven.wf_r22 m_Seven_r22 <|
      fc Seeds.wf_A2 hA2 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r48 69)
  have m_SevenGen_r74 : sm SevenGen.r74 ∈ S := memN SevenGen.wf_r48 m_SevenGen_r48
    (fc SevenGen.wf_r48 m_SevenGen_r48 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r74 69)
  have m_SevenGen_r75 : sm SevenGen.r75 ∈ S := memN SevenGen.wf_r74 m_SevenGen_r74
    (fc SevenGen.wf_r74 m_SevenGen_r74 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r75 69)
  have m_SevenGen_r76 : sm SevenGen.r76 ∈ S := memN SevenGen.wf_r75 m_SevenGen_r75
    (fc SevenGen.wf_r75 m_SevenGen_r75 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r76 69)
  have m_SevenGen_x9 : sm SevenGen.x9 ∈ S := memN SevenGen.wf_r48 m_SevenGen_r48
    (fc SevenGen.wf_r76 m_SevenGen_r76 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_x9 69)
  have m_SevenGen_r50 : sm SevenGen.r50 ∈ S := memN Seeds.wf_A1 hA1
    (fc SevenGen.wf_x9 m_SevenGen_x9 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r50 69)
  have m_SevenGen_r77 : sm SevenGen.r77 ∈ S := memN SevenGen.wf_r50 m_SevenGen_r50
    (fc SevenGen.wf_r50 m_SevenGen_r50 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r77 69)
  have m_SevenGen_r78 : sm SevenGen.r78 ∈ S := memN SevenGen.wf_r77 m_SevenGen_r77
    (fc SevenGen.wf_r77 m_SevenGen_r77 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r78 69)
  have m_SevenGen_r79 : sm SevenGen.r79 ∈ S := memN SevenGen.wf_r78 m_SevenGen_r78
    (fc SevenGen.wf_r78 m_SevenGen_r78 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r79 69)
  have m_SevenGen_d7 : sm SevenGen.d7 ∈ S := memN SevenGen.wf_r78 m_SevenGen_r78
    (fc SevenGen.wf_r79 m_SevenGen_r79 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_d7 69)
  have m_Seven_h : sm Seven.h ∈ S := memN Seven.wf_r26 m_Seven_r26
    (fc Seven.wf_r41 m_Seven_r41 <| fc Seven.wf_r46 m_Seven_r46 <| fc Seven.wf_r41 m_Seven_r41 <|
      fc Seven.wf_r42 m_Seven_r42 <| fc Seven.wf_r45 m_Seven_r45 <|
      fc Seven.wf_r41 m_Seven_r41 <| fc Seven.wf_r41 m_Seven_r41 <| fc Seven.wf_m1 m_Seven_m1 <|
      fn)
    (by bm_strips CFSG.KC.BM.Seven.c_h 69)
  have m_Seven_hi : sm Seven.hi ∈ S := memInv Seven.wf_h Seven.wf_hi m_Seven_h
    (by bm_strips CFSG.KC.BM.Seven.c_hi 69)
  have m_Seven_w : sm Seven.w ∈ S := memN Seven.wf_r46 m_Seven_r46
    (fc Seven.wf_r45 m_Seven_r45 <| fc Seven.wf_r45 m_Seven_r45 <| fc Seven.wf_m2i m_Seven_m2i <|
      fc Seven.wf_m2i m_Seven_m2i <| fc Seven.wf_r42 m_Seven_r42 <|
      fc Seven.wf_r42 m_Seven_r42 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_w 69)
  have m_Seven_r35 : sm Seven.r35 ∈ S := memN Seven.wf_w m_Seven_w
    (fc Seven.wf_w m_Seven_w <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r35 69)
  have m_Seven_r36 : sm Seven.r36 ∈ S := memN Seven.wf_r35 m_Seven_r35
    (fc Seven.wf_r35 m_Seven_r35 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r36 69)
  have m_Seven_r37 : sm Seven.r37 ∈ S := memN Seven.wf_r36 m_Seven_r36
    (fc Seven.wf_r36 m_Seven_r36 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r37 69)
  have m_Seven_r38 : sm Seven.r38 ∈ S := memN Seven.wf_r37 m_Seven_r37
    (fc Seven.wf_r37 m_Seven_r37 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r38 69)
  have m_Seven_r39 : sm Seven.r39 ∈ S := memN Seven.wf_r36 m_Seven_r36
    (fc Seven.wf_r38 m_Seven_r38 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_r39 69)
  have m_Seven_z : sm Seven.z ∈ S := memN Seven.wf_w m_Seven_w
    (fc Seven.wf_r39 m_Seven_r39 <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_z 69)
  have m_Seven_t1 : sm Seven.t1 ∈ S := memN Seven.wf_hi m_Seven_hi
    (fc Seven.wf_z m_Seven_z <| fc Seven.wf_h m_Seven_h <| fn)
    (by bm_strips CFSG.KC.BM.Seven.c_t1 69)
  have m_SevenGen_alt1 : sm SevenGen.alt1 ∈ S := memN Seven.wf_al m_Seven_al
    (fc Seven.wf_t1 m_Seven_t1 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_alt1 69)
  have m_SevenGen_r66 : sm SevenGen.r66 ∈ S := memN SevenGen.wf_r50 m_SevenGen_r50
    (fc Seeds.wf_A1 hA1 <| fc SevenGen.wf_alt1 m_SevenGen_alt1 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r66 69)
  have m_SevenGen_r82 : sm SevenGen.r82 ∈ S := memN SevenGen.wf_r66 m_SevenGen_r66
    (fc SevenGen.wf_r66 m_SevenGen_r66 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r82 69)
  have m_SevenGen_r83 : sm SevenGen.r83 ∈ S := memN SevenGen.wf_r82 m_SevenGen_r82
    (fc SevenGen.wf_r82 m_SevenGen_r82 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r83 69)
  have m_SevenGen_r84 : sm SevenGen.r84 ∈ S := memN SevenGen.wf_r83 m_SevenGen_r83
    (fc SevenGen.wf_r83 m_SevenGen_r83 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r84 69)
  have m_SevenGen_r67 : sm SevenGen.r67 ∈ S := memN SevenGen.wf_r82 m_SevenGen_r82
    (fc SevenGen.wf_r84 m_SevenGen_r84 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r67 69)
  have m_SevenGen_d : sm SevenGen.d ∈ S := memN SevenGen.wf_d7 m_SevenGen_d7
    (fc SevenGen.wf_r67 m_SevenGen_r67 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_d 69)
  have m_SevenGen_di : sm SevenGen.di ∈ S := memInv SevenGen.wf_d SevenGen.wf_di m_SevenGen_d
    (by bm_strips CFSG.KC.BM.SevenGen.c_di 69)
  have m_SevenGen_abi : sm SevenGen.abi ∈ S := memInv Seven.wf_r0 SevenGen.wf_abi m_Seven_r0
    (by bm_strips CFSG.KC.BM.SevenGen.c_abi 69)
  have m_SevenGen_r53 : sm SevenGen.r53 ∈ S := memN SevenGen.wf_x9 m_SevenGen_x9
    (fc SevenGen.wf_abi m_SevenGen_abi <| fc SevenGen.wf_x9 m_SevenGen_x9 <|
      fc Seven.wf_r0 m_Seven_r0 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r53 69)
  have m_SevenGen_r80 : sm SevenGen.r80 ∈ S := memN SevenGen.wf_r53 m_SevenGen_r53
    (fc SevenGen.wf_r53 m_SevenGen_r53 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r80 69)
  have m_SevenGen_r81 : sm SevenGen.r81 ∈ S := memN SevenGen.wf_r80 m_SevenGen_r80
    (fc SevenGen.wf_r80 m_SevenGen_r80 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r81 69)
  have m_SevenGen_r54 : sm SevenGen.r54 ∈ S := memN SevenGen.wf_r53 m_SevenGen_r53
    (fc SevenGen.wf_r81 m_SevenGen_r81 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r54 69)
  have m_SevenGen_n2 : sm SevenGen.n2 ∈ S := memN Seven.wf_r0 m_Seven_r0
    (fc SevenGen.wf_r54 m_SevenGen_r54 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_n2 69)
  have m_SevenGen_n2i : sm SevenGen.n2i ∈ S :=
    memInv SevenGen.wf_n2 SevenGen.wf_n2i m_SevenGen_n2
      (by bm_strips CFSG.KC.BM.SevenGen.c_n2i 69)
  have m_SevenGen_r96 : sm SevenGen.r96 ∈ S := memN SevenGen.wf_n2i m_SevenGen_n2i
    (fc SevenGen.wf_n2i m_SevenGen_n2i <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r96 69)
  have m_SevenGen_n1 : sm SevenGen.n1 ∈ S := memN SevenGen.wf_r50 m_SevenGen_r50
    (fc SevenGen.wf_d7 m_SevenGen_d7 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_n1 69)
  have m_SevenGen_r94 : sm SevenGen.r94 ∈ S := memN SevenGen.wf_n1 m_SevenGen_n1
    (fc SevenGen.wf_n2 m_SevenGen_n2 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r94 69)
  have m_SevenGen_r93 : sm SevenGen.r93 ∈ S := memN SevenGen.wf_n1 m_SevenGen_n1
    (fc SevenGen.wf_n2i m_SevenGen_n2i <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r93 69)
  have m_SevenGen_r98 : sm SevenGen.r98 ∈ S := memN SevenGen.wf_r94 m_SevenGen_r94
    (fc SevenGen.wf_r93 m_SevenGen_r93 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r98 69)
  have m_SevenGen_r95 : sm SevenGen.r95 ∈ S := memN SevenGen.wf_n2 m_SevenGen_n2
    (fc SevenGen.wf_n2 m_SevenGen_n2 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r95 69)
  have m_SevenGen_r99 : sm SevenGen.r99 ∈ S := memN SevenGen.wf_r94 m_SevenGen_r94
    (fc SevenGen.wf_r95 m_SevenGen_r95 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r99 69)
  have m_SevenGen_r97 : sm SevenGen.r97 ∈ S := memN SevenGen.wf_r93 m_SevenGen_r93
    (fc SevenGen.wf_r96 m_SevenGen_r96 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_r97 69)
  have m_SevenGen_q : sm SevenGen.q ∈ S := memN SevenGen.wf_r96 m_SevenGen_r96
    (fc SevenGen.wf_r98 m_SevenGen_r98 <| fc SevenGen.wf_r99 m_SevenGen_r99 <|
      fc SevenGen.wf_r97 m_SevenGen_r97 <| fc SevenGen.wf_r99 m_SevenGen_r99 <|
      fc SevenGen.wf_r95 m_SevenGen_r95 <| fc SevenGen.wf_r98 m_SevenGen_r98 <|
      fc SevenGen.wf_n2i m_SevenGen_n2i <| fc SevenGen.wf_r93 m_SevenGen_r93 <|
      fc SevenGen.wf_r93 m_SevenGen_r93 <| fc SevenGen.wf_r97 m_SevenGen_r97 <|
      fc SevenGen.wf_r93 m_SevenGen_r93 <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_q 69)
  have m_SevenGen_c : sm SevenGen.c ∈ S := memN SevenGen.wf_di m_SevenGen_di
    (fc SevenGen.wf_q m_SevenGen_q <| fc SevenGen.wf_d m_SevenGen_d <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_c 69)
  have m_SevenGen_ci : sm SevenGen.ci ∈ S := memInv SevenGen.wf_c SevenGen.wf_ci m_SevenGen_c
    (by bm_strips CFSG.KC.BM.SevenGen.c_ci 69)
  have m_SevenGen_s2 : sm SevenGen.s2 ∈ S := memN SevenGen.wf_ci m_SevenGen_ci
    (fc Seven.wf_g m_Seven_g <| fc SevenGen.wf_c m_SevenGen_c <| fn)
    (by bm_strips CFSG.KC.BM.SevenGen.c_s2 69)
  have m_SevenGen_s2i : sm SevenGen.s2i ∈ S :=
    memInv SevenGen.wf_s2 SevenGen.wf_s2i m_SevenGen_s2
      (by bm_strips CFSG.KC.BM.SevenGen.c_s2i 69)
  exact ⟨m_Seven_g, m_SevenGen_gi, m_SevenGen_s2, m_SevenGen_s2i, m_Seven_al, m_Seven_t1⟩

theorem seven_mem (hA1 : sm Seeds.A1 ∈ S) (hA2 : sm Seeds.A2 ∈ S) :
    sm Seven.g ∈ S ∧ sm SevenGen.gi ∈ S ∧ sm SevenGen.s2 ∈ S ∧ sm SevenGen.s2i ∈ S :=
  have h := seven_mem_all hA1 hA2
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

end CFSG.KC.BM.SevenMem

end
