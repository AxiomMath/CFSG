module

public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1Cover.O24550
public import CFSG.Certificates.Kernel.VOrbRecSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.OrbitInputs

public section

namespace CertificateChecks.KernelCo1Cover.ECore

open CFSG.KC.Co1F2 CFSG.KC.VOrbRec CFSG.KLie.CT CFSG.EvenSporadicStandard.TwoCo1
  CFSG.Sporadic.SmallF2.Native
  CertificateChecks.KernelCo1Cover

theorem colsAa_eq : colsAa = unpackR 11 TAP := by
  rw [colsAa, Aa_eq, tr_sound trA_ok]

theorem colsBa_eq : colsBa = unpackR 11 TBP := by
  rw [colsBa, Ba_eq, tr_sound trB_ok]

private theorem andB_eq' (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private theorem orB_eq' (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

private theorem notB_eq' (a : Bool) : notB a = !a := by cases a <;> rfl

private theorem allN_iff' (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq', Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem ofC : orbitOf11 eMaskC 1288 = vOrbitBFS 11 (unpackR 11 TAP) (unpackR 11 TBP) 1 1288 := by
  rw [orbitOf11, colsAa_eq, colsBa_eq]
  rfl

theorem ofA : orbitOf11 eMaskA 759 = vOrbitBFS 11 (unpackR 11 TAP) (unpackR 11 TBP) 3 759 := by
  rw [orbitOf11, colsAa_eq, colsBa_eq]
  rfl

theorem check_xC : orbitCheck11 eMaskC 1288 [] = true := by
  obtain ⟨h1, h2, h3, h4, -⟩ := vorbRec_bfs orbC_ok (by norm_num)
  unfold orbitCheck11
  simp only [ofC, colsAa_eq, colsBa_eq, Bool.and_eq_true, beq_iff_eq, List.all_nil, and_true]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

theorem check_xA : orbitCheck11 eMaskA 759 [eMaskC] = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := vorbRec_bfs orbA_ok (by norm_num)
  have hx : (KA.testBit 1) = false := by
    have := xC_notA
    rw [notB_eq', Bool.not_eq_true', CFSG.KC.F2W.bit_eq] at this
    exact this
  unfold orbitCheck11
  simp only [ofA, colsAa_eq, colsBa_eq, Bool.and_eq_true, beq_iff_eq, List.all_cons, List.all_nil,
    Bool.and_true, Bool.not_eq_true', h5]
  exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hx⟩

theorem check_cover : coverCheck11 = true := by
  have hC := (vorbRec_bfs orbC_ok (by norm_num)).2.2.2.2
  have hA := (vorbRec_bfs orbA_ok (by norm_num)).2.2.2.2
  unfold coverCheck11
  simp only [ofC, ofA]
  rw [List.all_eq_true]
  intro w hw
  have h := (allN_iff' _ _).1 cover_ok w (List.mem_range.1 hw)
  rw [orB_eq', orB_eq', CFSG.KC.F2W.bit_eq, CFSG.KC.F2W.bit_eq] at h
  rw [hC, hA]
  have hb : Nat.beq w 0 = (w == 0) := rfl
  rw [hb] at h
  rw [Bool.or_assoc]
  exact h

theorem facts24550 :
    (orbitCheck11 eMaskC 1288 [] = true)
    ∧ (orbitCheck11 eMaskA 759 [eMaskC] = true)
    ∧ (coverCheck11 = true) :=
  ⟨check_xC, check_xA, check_cover⟩

end CertificateChecks.KernelCo1Cover.ECore

end
