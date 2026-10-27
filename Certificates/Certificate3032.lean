module

public import CFSG.Monster.B.Fischer.HexadAffineInputs
public import CFSG.Certificates.Kernel.SortTreeSound
public import Certificates.Kernel.MonsterB.Orb3032Data
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.SortTree CFSG.KLie.CT

namespace CertificateChecks.Batch3032

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

abbrev actB (b : Bool) : ℕ → ℕ → ℕ := fun k m => if b then alpha k m else linQ k m

noncomputable abbrev recO (o : ℕ) : ℕ → ℕ := fun i => recT Orb3032.R 6 16 (Nat.add o i)

noncomputable abbrev edgeO (o : ℕ) : ℕ → ℕ → ℕ := fun i k => fget (recT Orb3032.E 6 12 (Nat.add o i)) k 4

noncomputable abbrev orbOK (b : Bool) (r o n : ℕ) : Bool :=
  andB (treeOK (actB b) 3 (fun m => decide (m < 32)) r (recO o) n 5 3 4 64 1)
    (closeOK (actB b) 3 (recO o) (edgeO o) n 5 64 1)

theorem k0 : orbOK false 0 0 1 = true := by quickRfl
theorem k1 : orbOK false 3 1 15 = true := by quickRfl
theorem k2 : orbOK false 1 16 16 = true := by quickRfl
theorem k3 : orbOK true 0 32 6 = true := by quickRfl
theorem k4 : orbOK true 3 38 10 = true := by quickRfl
theorem k5 : orbOK true 1 48 16 = true := by quickRfl

noncomputable abbrev covOK (o0 n0 o3 n3 o1 n1 : ℕ) : Bool :=
  allN 32 fun m => orB (memK (recO o0) n0 5 m) (orB (memK (recO o3) n3 5 m) (memK (recO o1) n1 5 m))

theorem kc0 : covOK 0 1 1 15 16 16 = true := by quickRfl
theorem kc1 : covOK 32 6 38 10 48 16 = true := by quickRfl

theorem orb {b : Bool} {r o n : ℕ} (hn : 0 < n) (hfuel : n ≤ 40) (h : orbOK b r o n = true) :
    natCertOK (actB b) 3 (fun m => decide (m < 32)) r (orbCert b r) = true ∧
      (orbCert b r).pts.size = n ∧
      ∀ x, x ∈ (orbCert b r).pts.toList ↔ ∃ i < n, valF 5 (recO o i) = x := by
  rw [andB_true_iff] at h
  obtain ⟨h1, h2, h3⟩ := natBfs_tree (fuel := 40) hn hfuel h.1 h.2
  exact ⟨h1, h2, fun x => Array.mem_toList_iff.trans (h3 x)⟩

theorem orB_true {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem cover {b : Bool} {o0 n0 o3 n3 o1 n1 : ℕ}
    (h0 : ∀ x, x ∈ (orbCert b 0).pts.toList ↔ ∃ i < n0, valF 5 (recO o0 i) = x)
    (h3 : ∀ x, x ∈ (orbCert b 3).pts.toList ↔ ∃ i < n3, valF 5 (recO o3 i) = x)
    (h1 : ∀ x, x ∈ (orbCert b 1).pts.toList ↔ ∃ i < n1, valF 5 (recO o1 i) = x)
    (hc : covOK o0 n0 o3 n3 o1 n1 = true) : ∀ m < 32,
      m ∈ (orbCert b 0).pts.toList ∨ m ∈ (orbCert b 3).pts.toList ∨
        m ∈ (orbCert b 1).pts.toList := by
  intro m hm
  have := (allN_iff _ _).1 hc m hm
  rcases orB_true this with e | e
  · exact Or.inl ((h0 m).2 (memK_sound e))
  · rcases orB_true e with e | e
    · exact Or.inr (Or.inl ((h3 m).2 (memK_sound e)))
    · exact Or.inr (Or.inr ((h1 m).2 (memK_sound e)))

end CertificateChecks.Batch3032

namespace Certificates

open CertificateChecks

open CertificateChecks.Batch3032 in
open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer in
theorem certificate3032 : (∀ b : Bool, ∀ r ∈ [0, 1, 3],
       natCertOK (fun k m => if b then alpha k m else linQ k m) 3 (fun m => decide (m < 32)) r
         (orbCert b r) = true)
    ∧ ((orbCert false 0).pts.size = 1 ∧ (orbCert false 3).pts.size = 15 ∧
       (orbCert false 1).pts.size = 16 ∧ (orbCert true 0).pts.size = 6 ∧
       (orbCert true 3).pts.size = 10 ∧ (orbCert true 1).pts.size = 16)
    ∧ (∀ b : Bool, ∀ m < 32,
       m ∈ (orbCert b 0).pts.toList ∨ m ∈ (orbCert b 3).pts.toList ∨
         m ∈ (orbCert b 1).pts.toList) := by
  have o0 := orb (by norm_num) (by norm_num) k0
  have o1 := orb (by norm_num) (by norm_num) k1
  have o2 := orb (by norm_num) (by norm_num) k2
  have o3 := orb (by norm_num) (by norm_num) k3
  have o4 := orb (by norm_num) (by norm_num) k4
  have o5 := orb (by norm_num) (by norm_num) k5
  refine ⟨fun b r hr => ?_, ⟨o0.2.1, o1.2.1, o2.2.1, o3.2.1, o4.2.1, o5.2.1⟩, fun b => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    cases b <;> rcases hr with rfl | rfl | rfl
    exacts [o0.1, o2.1, o1.1, o3.1, o5.1, o4.1]
  · cases b
    · exact cover o0.2.2 o1.2.2 o2.2.2 kc0
    · exact cover o3.2.2 o4.2.2 o5.2.2 kc1

end Certificates
