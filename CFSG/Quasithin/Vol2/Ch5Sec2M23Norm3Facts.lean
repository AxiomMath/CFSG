module

public import Certificates.Certificate7103

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.M23Norm3 CFSG.M23Heptad CFSG.A7Fano CFSG.QuasithinUnique.Vol2Native.L239
open CFSG.ComponentClassification.WittDesign

theorem m22Count_borel_eq_zero :
    m22Count (fun x => badBorel x = true) = 0 :=
  Certificates.certificate7103.1

theorem mem_k4List_of {σ : Perm (Fin 7)}
    (hs : Perm.sign σ = 1) (h4 : σ ^ 4 = 1) (h4' : σ 4 = 4) (h5 : σ 5 = 5) (h6 : σ 6 = 6) :
    σ ∈ k4List :=
  Certificates.certificate7103.2.1 σ hs h4 h4' h5 h6

theorem exists_eq_of_commute_c33 {σ : Perm (Fin 7)}
    (hs : Perm.sign σ = 1) (hc : σ * c33 = c33 * σ) :
    ∃ a b : Fin 3, σ = c33 ^ (a : ℕ) * c123 ^ (b : ℕ) :=
  Certificates.certificate7103.2.2.1 σ hs hc

theorem coset_facts (i : Fin 16) (a b : Fin 3)
    (h1 : M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * yBar =
      yBar * (M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ)))
    (h2 : M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ) * uBar =
      uBar * (M23Insp.es.getD i 1 * yBar ^ (a : ℕ) * y1Bar ^ (b : ℕ))) :
    b = 0 ∧ M23Insp.es.getD i 1 * yBar = yBar * M23Insp.es.getD i 1 :=
  Certificates.certificate7103.2.2.2.1 i a b h1 h2

theorem yBar_facts :
    (∀ i : Fin 7, ((yBar : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
        ιbar (c33 i)) ∧
      (∀ i : Fin 7, ((y1Bar : ↥CFSG.Blueprint.NativeSporadic.M23) : Perm (Fin 23)) (ιbar i) =
        ιbar (c123 i)) ∧
      yBar ^ 3 = 1 ∧ yBar ≠ 1 ∧ y1Bar ^ 3 = 1 ∧ uBar * yBar = yBar * uBar ∧ uBar ≠ 1 ∧
      rBar * uBar = uBar * rBar ∧ rBar * yBar * rBar⁻¹ = yBar⁻¹ ∧
      (M23Insp.es.filter (fun e => e * yBar = yBar * e)).length = 4 :=
  Certificates.certificate7103.2.2.2.2.1

theorem perm7_facts :
    (∀ x ∈ k4List, ∀ y ∈ k4List, x * y ∈ k4List) ∧ (∀ x ∈ k4List, x⁻¹ ∈ k4List) ∧
      k4List.Nodup ∧ (∀ x ∈ k4List, c123 * x * c123⁻¹ ∈ k4List) ∧
      (∀ x ∈ k4List, c456 * x * c456⁻¹ ∈ k4List) ∧
      (∀ x ∈ k4List, s1245 * x * s1245⁻¹ ∈ k4List) ∧ c123 * c456 = c456 * c123 ∧
      c123 ^ 3 = 1 ∧ c456 ^ 3 = 1 ∧ Perm.sign c123 = 1 ∧ Perm.sign c456 = 1 ∧
      Perm.sign s1245 = 1 ∧ s1245 * c123 * s1245⁻¹ = c123⁻¹ ∧
      s1245 * c456 * s1245⁻¹ = c456⁻¹ ∧ e9List.Nodup :=
  Certificates.certificate7103.2.2.2.2.2

end CFSG.Quasithin.H13
