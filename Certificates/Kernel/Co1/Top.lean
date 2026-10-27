module

public import Certificates.Kernel.Co2.Words
public import CFSG.Certificates.Kernel.Co1.TauCeti
public import CFSG.Certificates.Kernel.Orders.Co1.RelsBind

public section

namespace CertificateChecks.KernelCo1

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

abbrev P : TauCeti.GroupPresentation := TauCeti.Sporadic.co1Presentation

abbrev PG : Type := PresentedGroup P.relatorSet

noncomputable abbrev g0 : ℕ → PG := pgen P.relatorSet

theorem gens_eq : P.generatorCount = 8 := by
  simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.co1Presentation_generatorNames]

theorem lceEntry_eq (w : List (ℕ × Bool)) : CFSG.KC.Co1Top.lceEntry w = Co2B.ent w := by
  unfold CFSG.KC.Co1Top.lceEntry Co2B.ent
  congr 2
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.foldr_cons, ih]
    rfl

theorem top_val {h : ℕ} (hh : h < 45) :
    bval g0 (wWord (CFSG.KD.Co1B.TOPT h)) (wLen (CFSG.KD.Co1B.TOPT h)) = 1 := by
  have hb : ∀ w ∈ P.relatorLetters, (∀ l ∈ w, l.1 < 127) ∧ w.length < 1024 := by
    rw [CFSG.KD.OrdCo1.rels_eq]
    decide +kernel
  have hl : (P.relatorLetters.map CFSG.KC.Co1Top.lceEntry).length = 45 := by
    rw [CFSG.KC.Co1Top.top_eq, List.length_map, List.length_range]
  rw [List.length_map] at hl
  have e := List.getElem_of_eq CFSG.KC.Co1Top.top_eq
    (by rw [List.length_map]; omega : h < (P.relatorLetters.map CFSG.KC.Co1Top.lceEntry).length)
  rw [List.getElem_map, List.getElem_map, List.getElem_range] at e
  have hm := List.getElem_mem (by omega : h < P.relatorLetters.length)
  rw [← e, lceEntry_eq, bval_ent _ _ (hb _ hm).1 (hb _ hm).2]
  exact swd_relatorLetters P _ hm

theorem closure_g0 : Subgroup.closure (g0 '' {g | 2 * g < nat_lit 16}) = ⊤ := by
  rw [← closure_pgen P.relatorSet]
  congr 2
  ext g
  change 2 * g < 16 ↔ g < P.generatorCount
  rw [gens_eq]
  omega

end CertificateChecks.KernelCo1

end
