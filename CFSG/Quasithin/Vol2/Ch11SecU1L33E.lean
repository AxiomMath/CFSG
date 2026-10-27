module

public import CFSG.Quasithin.Vol2.Ch11SecU1L33D

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L33

open CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

set_option maxRecDepth 100000

@[expose] def cpow16 (c : Code) : Code :=
  cmul (cmul (cmul (cmul c c) (cmul c c)) (cmul (cmul c c) (cmul c c)))
    (cmul (cmul (cmul c c) (cmul c c)) (cmul (cmul c c) (cmul c c)))

abbrev SubFacts (l : List Code) (n : Nat) : Prop :=
  cone ∈ l ∧ (∀ a ∈ l, ∀ b ∈ l, cmul a b ∈ l) ∧ (∀ a ∈ l, ∃ b ∈ l, cmul a b = cone) ∧
    (∀ a ∈ l, a.1 < 19683 ∧ ndet a.1 = 1) ∧ l.Nodup ∧ l.length = n

theorem tl_facts : SubFacts tl 32 := by decide +kernel

theorem k0l_facts : SubFacts k0l 48 := by decide +kernel

theorem q0l_facts : SubFacts q0l 8 := by decide +kernel

theorem r0l_facts : SubFacts r0l 24 := by decide +kernel

theorem tk0l_facts : SubFacts tk0l 16 := by decide +kernel

theorem tk0l_check : (∀ c ∈ tl, c ∈ k0l → c ∈ tk0l) ∧ ∀ c ∈ tk0l, c ∈ tl ∧ c ∈ k0l := by
  decide +kernel

theorem sub_check : (∀ q ∈ q0l, q ∈ tk0l ∧ q ∈ r0l) ∧ (∀ r ∈ r0l, r ∈ k0l) ∧
    ∃ r ∈ r0l, r ∉ q0l := by
  decide +kernel

theorem normal_check : (∀ k ∈ k0l, ∀ q ∈ q0l, ∃ q' ∈ q0l, cmul k q = cmul q' k) ∧
    ∀ k ∈ k0l, ∀ r ∈ r0l, ∃ r' ∈ r0l, cmul k r = cmul r' k := by
  decide +kernel

theorem power_check : (∀ q ∈ q0l, cmul q q = cone) ∧ (∀ r ∈ r0l, cmul (cmul r r) r ∈ q0l) ∧
    ∀ k ∈ k0l, cmul k k ∈ r0l := by
  decide +kernel

theorem pcore_check : ∀ x ∈ tk0l, x ∉ q0l → ∃ e ∈ pcoreData, e.1 = x ∧ e.2.1 ∈ k0l ∧
    e.2.2 ∈ k0l ∧ cmul e.2.1 x = cmul e.2.2 e.2.1 ∧ cpow16 (cmul x e.2.2) ≠ cone := by
  decide +kernel

@[expose] def commC (e : Code × Code × Code × Code) : Code :=
  cmul (cmul (cmul e.2.1 e.1) e.2.2.1) e.2.2.2

theorem comm_check : ∀ a ∈ tk0l, a ∉ q0l → ∃ e ∈ commData, e.1 = a ∧ e.2.1 ∈ r0l ∧
    e.2.2.1 ∈ r0l ∧ e.2.2.2 ∈ tk0l ∧ cmul e.2.1 e.2.2.1 = cone ∧ cmul a e.2.2.2 = cone ∧
    ∀ x ∈ r0l, ∃ q ∈ q0l, x = q ∨ x = cmul (commC e) q ∨ x = cmul (cmul (commC e) (commC e)) q := by
  decide +kernel

theorem index_check : ∀ x ∈ tk0l, ∀ a ∈ tk0l, a ∉ q0l → x ∈ q0l ∨ cmul x a ∈ q0l := by
  decide +kernel

theorem z0_check : z0c ∈ tl ∧ (∀ c ∈ tl, cmul c z0c = cmul z0c c) ∧ cmul z0c z0c = cone ∧
    z0c ≠ cone ∧ z0c.2 = false ∧ ∃ k ∈ k0l, cmul k z0c ≠ cmul z0c k := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
theorem caseA_check : ∀ x ∈ tl, ∀ y ∈ tl, x.2 = false → y.2 = false → x ≠ cone → y ≠ cone →
    x ≠ y → cmul x x = cone → cmul y y = cone → cmul x y = cmul y x →
    ∃ e ∈ tableA, e.1 = x ∧ e.2.1 = y ∧ e.2.2.1 ∈ tl ∧ e.2.2.2.1 ∈ tl ∧ e.2.2.2.2 ∈ tl ∧
      cmul e.2.2.1 x = cmul e.2.2.2.1 e.2.2.1 ∧ cmul e.2.2.1 y = cmul e.2.2.2.2 e.2.2.1 ∧
      (∀ c ∈ tl, cmul c e.2.2.2.1 = cmul e.2.2.2.1 c → cmul c e.2.2.2.2 = cmul e.2.2.2.2 c →
        c ∈ k0l) ∧ ¬ (e.2.2.2.1 ∈ q0l ∧ e.2.2.2.2 ∈ q0l) := by
  decide +kernel

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
theorem caseB_check : ∀ v ∈ tl, ∀ b ∈ tl, v.2 = false → b.2 = true → v ≠ cone →
    cmul v v = cone → cmul b b = cone → cmul v b = cmul b v →
    ∃ e ∈ tableB, e.1 = v ∧ e.2.1 = b ∧ e.2.2.1.1 < 19683 ∧ ndet e.2.2.1.1 = 1 ∧
      e.2.2.2.1 ∈ tl ∧ e.2.2.2.2.1 ∈ tl ∧ e.2.2.2.2.2 ∈ tl ∧
      cmul e.2.2.1 v = cmul e.2.2.2.1 e.2.2.1 ∧ cmul e.2.2.1 b = cmul e.2.2.2.2.1 e.2.2.1 ∧
      cmul e.2.2.1 (cmul v b) = cmul e.2.2.2.2.2 e.2.2.1 ∧
      (∀ c ∈ tl, cmul c e.2.2.2.1 = cmul e.2.2.2.1 c →
        cmul c e.2.2.2.2.1 = cmul e.2.2.2.2.1 c → c ∈ k0l) ∧
      ¬ (e.2.2.2.1 ∈ q0l ∧ e.2.2.2.2.1 ∈ q0l) := by
  decide +kernel

end CFSG.Quasithin.Vol2.Ch11.SecU1.L33
