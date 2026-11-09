module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEFCertInputs
public import Certificates.Kernel.Census.Small.SEList
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

namespace C22604

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.GHFus

@[expose] noncomputable def chk1 : Bool :=
  (codesP fun c => o4EK c && !predFK c).all fun a =>
    (codesP fun c => o4FK c && !predEK c).all fun b => !isZ (commC a b)

@[expose] noncomputable def chk2 : Bool :=
  (codesP predEK).all fun a => (codesP predEK).all fun b => isZ (commC a b)

@[expose] noncomputable def chk3 : Bool :=
  (codesP predFK).all fun a => (codesP predFK).all fun b => isZ (commC a b)

@[expose] noncomputable def chk4 : Bool :=
  (codesP predEK).all fun a => o4EK a || (codesP o4EK).any fun u => o4EK (mulT (invK u) a)

@[expose] noncomputable def chk5 : Bool :=
  (codesP predFK).all fun a => o4FK a || (codesP o4FK).any fun u => o4FK (mulT (invK u) a)

theorem chk1_ok : chk1 = true := by quickRfl
theorem chk2_ok : chk2 = true := by quickRfl
theorem chk3_ok : chk3 = true := by quickRfl
theorem chk4_ok : chk4 = true := by quickRfl
theorem chk5_ok : chk5 = true := by quickRfl

theorem part1 :
    ∀ e f : SE, SE.O4E e → ¬ SE.predF e → SE.O4F f → ¬ SE.predE f → ¬ SE.commZ e f := by
  intro e f h1 h2 h3 h4
  have := pair_of (P := fun s => SE.O4E s ∧ ¬ SE.predF s) (Q := fun s => SE.O4F s ∧ ¬ SE.predE s)
    (p := fun c => o4EK c && !predFK c) (q := fun c => o4FK c && !predEK c)
    (R := fun s t => ¬ SE.commZ s t) (r := fun a b => !isZ (commC a b))
    (fun s hs => band2 ((o4E_iff s).1 hs.1) (bnot_of (mt (predF_iff s).2 hs.2)))
    (fun s hs => band2 ((o4F_iff s).1 hs.1) (bnot_of (mt (predE_iff s).2 hs.2)))
    (fun s t h => mt (commZ_iff s t).1 (of_bnot h)) chk1_ok
  exact this e f ⟨h1, h2⟩ ⟨h3, h4⟩

theorem part2 : ∀ e f : SE, SE.predE e → SE.predE f → SE.commZ e f :=
  pair_of (P := SE.predE) (Q := SE.predE) (R := SE.commZ)
    (p := predEK) (q := predEK) (r := fun a b => isZ (commC a b))
    (fun s hs => (predE_iff s).1 hs) (fun s hs => (predE_iff s).1 hs)
    (fun s t h => (commZ_iff s t).2 h) chk2_ok

theorem part3 : ∀ e f : SE, SE.predF e → SE.predF f → SE.commZ e f :=
  pair_of (P := SE.predF) (Q := SE.predF) (R := SE.commZ)
    (p := predFK) (q := predFK) (r := fun a b => isZ (commC a b))
    (fun s hs => (predF_iff s).1 hs) (fun s hs => (predF_iff s).1 hs)
    (fun s t h => (commZ_iff s t).2 h) chk3_ok

theorem part4 :
    ∀ e : SE, SE.predE e → SE.O4E e ∨ ∃ u v : SE, SE.O4E u ∧ SE.O4E v ∧ e = u * v := by
  intro e he
  have h := List.all_eq_true.1 chk4_ok _ (enc_mem_codesP ((predE_iff e).1 he))
  simp only [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨u, hu, hv⟩
  · exact Or.inl ((o4E_iff e).2 h)
  · exact Or.inr (prod_of o4E_iff hu hv)

theorem part5 :
    ∀ e : SE, SE.predF e → SE.O4F e ∨ ∃ u v : SE, SE.O4F u ∧ SE.O4F v ∧ e = u * v := by
  intro e he
  have h := List.all_eq_true.1 chk5_ok _ (enc_mem_codesP ((predF_iff e).1 he))
  simp only [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨u, hu, hv⟩
  · exact Or.inl ((o4F_iff e).2 h)
  · exact Or.inr (prod_of o4F_iff hu hv)

end C22604

open CFSG.ComponentClassification.GHarris.SCert in
theorem check22604 :
    (∀ e f : SE, SE.O4E e → ¬ SE.predF e → SE.O4F f → ¬ SE.predE f → ¬ SE.commZ e f) ∧
    (∀ e f : SE, SE.predE e → SE.predE f → SE.commZ e f) ∧
    (∀ e f : SE, SE.predF e → SE.predF f → SE.commZ e f) ∧
    (∀ e : SE, SE.predE e → SE.O4E e ∨ ∃ u v : SE, SE.O4E u ∧ SE.O4E v ∧ e = u * v) ∧
    (∀ e : SE, SE.predF e → SE.O4F e ∨ ∃ u v : SE, SE.O4F u ∧ SE.O4F v ∧ e = u * v) :=
  ⟨C22604.part1, C22604.part2, C22604.part3, C22604.part4, C22604.part5⟩

end CertificateChecks.KernelCensus
