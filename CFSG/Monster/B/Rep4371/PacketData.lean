module

public import CFSG.Monster.B.Rep4371.Records
public import CFSG.Monster.B.Rep4371.RawOrder
public import CFSG.Monster.B.Rep4371.PacketShape
public import CFSG.Monster.B.Co2.Data
public import CFSG.Monster.B.Rep4371.KeyActXi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.B.Rep4371

@[expose] def packetNum (k t u : ℕ) : ℤ :=
  ((Native.packetRows[k]!)[t]!).foldl (fun s e => if e.1 = u then s + e.2 else s) 0

@[expose] def packetQ (k : Fin 48) (t u : Fin 4371) : ℚ := (packetNum k t u : ℚ) / 8

@[expose] def packetN (k : Fin 48) : Matrix (Fin 4371) (Fin 4371) ℚ := Matrix.of (packetQ k)

@[expose] def GR : Matrix (Fin 4371) (Fin 4371) ℚ :=
  Matrix.diagonal fun t => if (t : ℕ) = 0 then 2 else if (t : ℕ) ≤ 22 then 4 else 2

@[expose] noncomputable def recPerm (i : Fin 24) : AutPerm := wordPerm (Co2.genRecord i).word

@[expose] noncomputable def recCode (i : Fin 24) : C := frameSum (Co2.genRecord i).word

@[expose] noncomputable def hPair (i : Fin 24) : Pvis :=
  match (Co2.genRecord i).kind with
  | .pairStabilizer => permPair (recPerm i)
  | .codeSign => ⟨(YU ⟨recCode i, 0⟩, gO (recCode i)), YU_gO_mem_Pvis ⟨recCode i, 0⟩⟩
  | .xiSign => xiSignPair

@[expose] noncomputable def hElt (i : Fin 24) : SpaceB ≃ₗ[ℚ] SpaceB := thetaEquiv (hPair i)

theorem hElt_mem_Gvis (i : Fin 24) : hElt i ∈ Gvis := ⟨hPair i, rfl⟩

theorem genRecord_kind (i : Fin 24) :
    (Co2.genRecord i).kind = if (i : ℕ) < 12 then .pairStabilizer
      else if (i : ℕ) < 23 then .codeSign else .xiSign := by
  revert i
  decide +kernel

theorem repPerm_recPerm : ∀ i : Fin 24, (i : ℕ) < 12 →
    RepPerm (recPerm i : Equiv.Perm (Fin 24)) Model.recPerms[(i : ℕ)]! := by
  unfold RepPerm recPerm
  decide +kernel

theorem genRecord_word_codeSign : ∀ i : Fin 24, 12 ≤ (i : ℕ) → (i : ℕ) < 23 →
    (∀ k ∈ (Co2.genRecord i).word, k.toNat - 3 < 12) ∧
      Model.frameCode (Co2.genRecord i).word =
        [3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][(i : ℕ) - 12]! := by
  decide +kernel

theorem recCode_eq {i : Fin 24} (h1 : 12 ≤ (i : ℕ)) (h2 : (i : ℕ) < 23) :
    recCode i = toC ([3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][(i : ℕ) - 12]!) := by
  rw [recCode, frameSum_eq _ (genRecord_word_codeSign i h1 h2).1,
    (genRecord_word_codeSign i h1 h2).2]

theorem genRecord_word_xi : (Co2.genRecord 23).word = [0, 3] := by decide +kernel

theorem hPair_of_lt_twelve {i : Fin 24} (h : (i : ℕ) < 12) : hPair i = permPair (recPerm i) := by
  rw [hPair, genRecord_kind, ite_eq_left h]

theorem hPair_of_codeSign {i : Fin 24} (h1 : 12 ≤ (i : ℕ)) (h2 : (i : ℕ) < 23) :
    hPair i = ⟨(YU ⟨recCode i, 0⟩, gO (recCode i)), YU_gO_mem_Pvis ⟨recCode i, 0⟩⟩ := by
  rw [hPair, genRecord_kind, ite_eq_right (by omega), ite_eq_left h2]

theorem hPair_xi : hPair 23 = xiSignPair := by
  rw [hPair, genRecord_kind]
  rfl

theorem rational_4371_generator_packet_data :
    (Rraw 0 = inA (basisA s(0, 0) - basisA s(1, 1)) ∧
      (∀ j : Fin 24, 2 ≤ (j : ℕ) →
        Rraw ((j : ℕ) - 1) = inA (basisA s(0, j) - basisA s(1, j)) ∧
        Rraw (23 + 2 * ((j : ℕ) - 2)) = inX (Xlift (rMinus 0 j) - Xlift (rMinus 1 j)) ∧
        Rraw (24 + 2 * ((j : ℕ) - 2)) = inX (Xlift (rPlus 0 j) - Xlift (rPlus 1 j))) ∧
      (∀ t < 1024, Rraw (67 + t) = inX (Xlift (rOdd (oddC t) 0) - Xlift (rOdd (oddC t) 1))) ∧
      (∀ b < 77, ∀ i < 16, Rraw (1091 + 16 * b + i) =
        inX (Xlift (rOct (octC b) (octSet b (Model.localPairs[i]!).1)) -
          Xlift (rOct (octC b) (octSet b (Model.localPairs[i]!).2)))) ∧
      (∀ t < 1024, Rraw (2323 + t) = inW (tensor (E 0 (oddC t)) wvec) ∧
        Rraw (3347 + t) = inW (tensor (E 1 (oddC t)) wvec))) ∧
    ((∀ a, a ∈ Model.oddCodes.toList ↔
        a < 4096 ∧ a % 2 = 0 ∧ (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1) ∧
      Model.oddCodes.toList.Pairwise (· < ·) ∧ Model.oddCodes.size = 1024 ∧
      (∀ t, oddC t = π₀ (toC Model.oddCodes[t]!)) ∧
      (∀ a, a ∈ Model.octCoeffs.toList ↔
        a < 4096 ∧ Model.popcN 24 (Model.wordN a) = 8 ∧ Model.wordN a % 4 = 3) ∧
      (Model.octCoeffs.toList.map Model.wordN).Pairwise (· ≤ ·) ∧
      (∀ b, octC b = toC Model.octCoeffs[b]!)) ∧
    (Native.packetShapeOK = true ∧
      ∀ (k : Fin 48) (t u : Fin 4371), packetN k t u = (packetNum k t u : ℚ) / 8) ∧
    GR = Matrix.diagonal (fun t : Fin 4371 =>
      (if (t : ℕ) = 0 then 2 else if (t : ℕ) ≤ 22 then 4 else 2 : ℚ)) ∧
    (Short.rStar = pauliQ (false, 0, 191) ∧ qElt 0 = zQ ∧
      (∀ i : Fin 23, 1 ≤ (i : ℕ) → (hi : (i : ℕ) ≤ 11) →
        qElt i = TQ (basisC ⟨i, by omega⟩ + epsStar i • basisC 0)) ∧
      (∀ i : Fin 23, 12 ≤ (i : ℕ) → qElt i = DQ (deltaBasis ⟨i - 11, by omega⟩))) ∧
    (∀ i : Fin 24, (Co2.genRecord i).kind = if (i : ℕ) < 12 then .pairStabilizer
      else if (i : ℕ) < 23 then .codeSign else .xiSign) ∧
    (∀ i : Fin 24, (i : ℕ) < 12 →
      RepPerm (recPerm i : Equiv.Perm (Fin 24)) Model.recPerms[(i : ℕ)]! ∧
      hPair i = permPair (recPerm i)) ∧
    (∀ i : Fin 24, 12 ≤ (i : ℕ) → (i : ℕ) < 23 →
      recCode i = ((Co2.genRecord i).word.map fun k =>
        if h : k.toNat - 3 < 12 then basisC ⟨k.toNat - 3, h⟩ else 0).sum ∧
      hPair i = ⟨(YU ⟨recCode i, 0⟩, gO (recCode i)), YU_gO_mem_Pvis ⟨recCode i, 0⟩⟩) ∧
    hPair 23 = xiPair * signPair 1 ∧
    (∀ i : Fin 24, hElt i = thetaEquiv (hPair i) ∧ hElt i ∈ Gvis) := by
  refine ⟨Rraw_description, ⟨mem_oddCodes_iff, oddCodes_sorted, oddCodes_size, fun _ => rfl,
    mem_octCoeffs_iff, octCoeffs_sorted, fun _ => rfl⟩, ⟨packetShapeOK_eq_true,
    fun _ _ _ => rfl⟩, rfl, ⟨rStar_eq, ?_, fun i h1 h11 => ?_, fun i h12 => ?_⟩, genRecord_kind,
    fun i hi => ⟨repPerm_recPerm i hi, hPair_of_lt_twelve hi⟩,
    fun i h1 h2 => ⟨rfl, hPair_of_codeSign h1 h2⟩, hPair_xi, fun i => ⟨rfl, hElt_mem_Gvis i⟩⟩
  · simp [qElt]
  · rw [qElt, ite_eq_right (by omega), dite_eq_left h11]
  · rw [qElt, ite_eq_right (by omega), dite_eq_right (by omega)]

end CFSG.Monster.B
