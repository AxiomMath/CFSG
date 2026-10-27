module

public import CFSG.Sporadic.HNSchreier.ArchCheck
public import CFSG.Sporadic.HNSchreier.Faithful
public import Certificates.Certificate2095

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[irreducible] def archBytes : ByteArray := hexDumpBytes arraysPayload

theorem archBytes_eq : archBytes = hexDumpBytes arraysPayload := by unfold archBytes; rfl

theorem arch_parts : archBytes.size = 12 + 8 * 1140000 ∧
    (List.range 8).map (fun k => (archBytes.get! k).toNat) = "HNPAIR01".toList.map Char.toNat ∧
    le32 archBytes 8 = 1140000 ∧
    ∀ i < 1140000, le32 archBytes (12 + 8 * i) < 1140000 ∧
      le32 archBytes (12 + 8 * i + 4) < 1140000 := by
  have h := arch_data_cert
  unfold archDataChecks at h
  rw [← archBytes_eq] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  have := (allIn_eq_true.1 h4) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

@[expose] def qRaw (s : Fin 2) (i : ℕ) : ℕ := le32 archBytes (12 + 8 * i + 4 * s.val)

theorem qRaw_lt (s : Fin 2) (i : X) : qRaw s i < hnsData.n := by
  have hi : (i : ℕ) < 1140000 := i.isLt
  obtain ⟨h0, h1⟩ := arch_parts.2.2.2 i hi
  show qRaw s i < 1140000
  match s with
  | 0 => simpa [qRaw] using h0
  | 1 => simpa [qRaw] using h1

@[expose] def qArch
    (s : Fin 2) (i : X) : X := ⟨qRaw s i, qRaw_lt s i⟩

theorem ctuc_hn_archived_action_array_data :
    nPts = 1140000 ∧ archBytes.size = 12 + 8 * nPts ∧
    (List.range 8).map (fun k => (archBytes.get! k).toNat) = "HNPAIR01".toList.map Char.toNat ∧
    le32 archBytes 8 = nPts ∧
    ∀ (s : Fin 2) (i : X), ((qArch s i : X) : ℕ) = le32 archBytes (12 + 8 * i + 4 * s.val) :=
  ⟨rfl, arch_parts.1, arch_parts.2.1, arch_parts.2.2.1, fun _ _ => rfl⟩

end CFSG.Sporadic.HNSchreier
