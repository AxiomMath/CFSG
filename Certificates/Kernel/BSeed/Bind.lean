
module

public import CFSG.Certificates.Kernel.BSeed.Sound
public import CFSG.Monster.B.Pinned.GeneratorDeterminantsBase
public import CFSG.Certificates.Kernel.BSeed.LitEq1
public import CFSG.Certificates.Kernel.BSeed.LitEq2

public section

namespace CertificateChecks.KernelBSeed

open CFSG.KC.BSeed

theorem decChunkSC_eq (len : Nat) : ∀ (N : Nat) (t : List Nat),
    decChunkSC len N (t.map Char.ofNat) = (decChunkS len N t).map Char.ofNat := by
  induction len with
  | zero => intro N t; rfl
  | succ len ih =>
    intro N t
    change List.cons _ (decChunkSC len _ _) = (List.cons _ (decChunkS len _ _)).map Char.ofNat
    rw [ih, List.map_cons]

theorem charsOfS_eq (L : List (Nat × Nat)) : charsOfS L = (bytesOfS L).map Char.ofNat := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨N, len⟩ := p
    change decChunkSC len N (charsOfS L) = (decChunkS len N (bytesOfS L)).map Char.ofNat
    rw [ih, decChunkSC_eq]

theorem decChunkS_append (len : Nat) : ∀ (N : Nat) (t u : List Nat),
    decChunkS len N t ++ u = decChunkS len N (t ++ u) := by
  induction len with
  | zero => intro N t u; rfl
  | succ len ih =>
    intro N t u
    change List.cons _ (decChunkS len _ _) ++ u = List.cons _ (decChunkS len _ _)
    rw [List.cons_append, ih]

theorem bytesOfS_append (L M : List (Nat × Nat)) : bytesOfS (L ++ M) = bytesOfS L ++ bytesOfS M := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨N, len⟩ := p
    change decChunkS len N (bytesOfS (L ++ M)) = decChunkS len N (bytesOfS L) ++ bytesOfS M
    rw [ih, decChunkS_append]

@[expose] noncomputable def B1 (k : Nat) : List Nat := bytesOfS
  ([CFSG.KD.BSeed.M1C00.CH, CFSG.KD.BSeed.M1C01.CH, CFSG.KD.BSeed.M1C02.CH, CFSG.KD.BSeed.M1C03.CH,
    CFSG.KD.BSeed.M1C04.CH, CFSG.KD.BSeed.M1C05.CH, CFSG.KD.BSeed.M1C06.CH, CFSG.KD.BSeed.M1C07.CH,
    CFSG.KD.BSeed.M1C08.CH, CFSG.KD.BSeed.M1C09.CH, CFSG.KD.BSeed.M1C10.CH, CFSG.KD.BSeed.M1C11.CH,
    CFSG.KD.BSeed.M1C12.CH, CFSG.KD.BSeed.M1C13.CH, CFSG.KD.BSeed.M1C14.CH, CFSG.KD.BSeed.M1C15.CH,
    CFSG.KD.BSeed.M1C16.CH, CFSG.KD.BSeed.M1C17.CH, CFSG.KD.BSeed.M1C18.CH].getD k [])

@[expose] noncomputable def B2 (k : Nat) : List Nat := bytesOfS
  ([CFSG.KD.BSeed.M2C00.CH, CFSG.KD.BSeed.M2C01.CH, CFSG.KD.BSeed.M2C02.CH, CFSG.KD.BSeed.M2C03.CH,
    CFSG.KD.BSeed.M2C04.CH, CFSG.KD.BSeed.M2C05.CH, CFSG.KD.BSeed.M2C06.CH, CFSG.KD.BSeed.M2C07.CH,
    CFSG.KD.BSeed.M2C08.CH, CFSG.KD.BSeed.M2C09.CH, CFSG.KD.BSeed.M2C10.CH, CFSG.KD.BSeed.M2C11.CH,
    CFSG.KD.BSeed.M2C12.CH, CFSG.KD.BSeed.M2C13.CH, CFSG.KD.BSeed.M2C14.CH, CFSG.KD.BSeed.M2C15.CH,
    CFSG.KD.BSeed.M2C16.CH, CFSG.KD.BSeed.M2C17.CH, CFSG.KD.BSeed.M2C18.CH].getD k [])

@[expose] def st (k : Nat) : Nat := min (236 * k) 4370

theorem flat1 : (List.range 19).flatMap B1 =
    B1 0 ++ B1 1 ++ B1 2 ++ B1 3 ++ B1 4 ++ B1 5 ++ B1 6 ++ B1 7 ++ B1 8 ++ B1 9 ++ B1 10 ++
      B1 11 ++ B1 12 ++ B1 13 ++ B1 14 ++ B1 15 ++ B1 16 ++ B1 17 ++ B1 18 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem seed1_eq : CFSG.Blueprint.NativeSporadic.BSeed1 =
    String.ofList (((List.range 19).flatMap B1).map Char.ofNat) := by
  rw [bseed1_lit, charsOfS_eq, flat1]
  simp only [B1, List.getD_cons_zero, List.getD_cons_succ, bytesOfS_append, List.append_assoc]

theorem flat2 : (List.range 19).flatMap B2 =
    B2 0 ++ B2 1 ++ B2 2 ++ B2 3 ++ B2 4 ++ B2 5 ++ B2 6 ++ B2 7 ++ B2 8 ++ B2 9 ++ B2 10 ++
      B2 11 ++ B2 12 ++ B2 13 ++ B2 14 ++ B2 15 ++ B2 16 ++ B2 17 ++ B2 18 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem seed2_eq : CFSG.Blueprint.NativeSporadic.BSeed2 =
    String.ofList (((List.range 19).flatMap B2).map Char.ofNat) := by
  rw [bseed2_lit, charsOfS_eq, flat2]
  simp only [B2, List.getD_cons_zero, List.getD_cons_succ, bytesOfS_append, List.append_assoc]

theorem genA₁_eq : CFSG.Monster.B.genA₁ = rowsMat 4370 A1R := by
  rw [CFSG.Monster.B.genA₁, seed1_eq]
  apply decode_of_seedChunkOK (d := 4370) (K := 19) (B := B1) (st := st) (R := A1R) (by norm_num)
    rfl rfl
  intro k hk
  interval_cases k
  exacts [CFSG.KD.BSeed.M1C00.ok, CFSG.KD.BSeed.M1C01.ok, CFSG.KD.BSeed.M1C02.ok,
    CFSG.KD.BSeed.M1C03.ok, CFSG.KD.BSeed.M1C04.ok, CFSG.KD.BSeed.M1C05.ok, CFSG.KD.BSeed.M1C06.ok,
    CFSG.KD.BSeed.M1C07.ok, CFSG.KD.BSeed.M1C08.ok, CFSG.KD.BSeed.M1C09.ok, CFSG.KD.BSeed.M1C10.ok,
    CFSG.KD.BSeed.M1C11.ok, CFSG.KD.BSeed.M1C12.ok, CFSG.KD.BSeed.M1C13.ok, CFSG.KD.BSeed.M1C14.ok,
    CFSG.KD.BSeed.M1C15.ok, CFSG.KD.BSeed.M1C16.ok, CFSG.KD.BSeed.M1C17.ok, CFSG.KD.BSeed.M1C18.ok]

theorem genA₂_eq : CFSG.Monster.B.genA₂ = rowsMat 4370 A2R := by
  rw [CFSG.Monster.B.genA₂, seed2_eq]
  apply decode_of_seedChunkOK (d := 4370) (K := 19) (B := B2) (st := st) (R := A2R) (by norm_num)
    rfl rfl
  intro k hk
  interval_cases k
  exacts [CFSG.KD.BSeed.M2C00.ok, CFSG.KD.BSeed.M2C01.ok, CFSG.KD.BSeed.M2C02.ok,
    CFSG.KD.BSeed.M2C03.ok, CFSG.KD.BSeed.M2C04.ok, CFSG.KD.BSeed.M2C05.ok, CFSG.KD.BSeed.M2C06.ok,
    CFSG.KD.BSeed.M2C07.ok, CFSG.KD.BSeed.M2C08.ok, CFSG.KD.BSeed.M2C09.ok, CFSG.KD.BSeed.M2C10.ok,
    CFSG.KD.BSeed.M2C11.ok, CFSG.KD.BSeed.M2C12.ok, CFSG.KD.BSeed.M2C13.ok, CFSG.KD.BSeed.M2C14.ok,
    CFSG.KD.BSeed.M2C15.ok, CFSG.KD.BSeed.M2C16.ok, CFSG.KD.BSeed.M2C17.ok, CFSG.KD.BSeed.M2C18.ok]

end CertificateChecks.KernelBSeed

end
