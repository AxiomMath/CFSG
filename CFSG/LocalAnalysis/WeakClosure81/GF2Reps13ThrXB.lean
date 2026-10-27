module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXBA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s13IsoComps_commSub_eq (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {L : Subgroup (MulAut W)} (hLX : L ≤ X)
    {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    (L ≤ s13KerOn X U → commSub U L = ⊥) ∧ (¬ L ≤ s13KerOn X U → commSub U L = U) :=
  w16g_s13IsoComps_commSub_eq hW hp hp2 hX hLX hU

theorem commSub_top_eq_iSup_s13Supp (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X)
    {L : Subgroup (MulAut W)} (hLX : L ≤ X) :
    commSub ⊤ L = ⨆ U ∈ s13Supp X L, U :=
  w16g_commSub_top_eq_iSup_s13Supp hW hp hp2 hX hLX

theorem map_mem_s13IsoComps {X : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) {U : Subgroup W}
    (hU : U ∈ s13IsoComps X) : U.map g.toMonoidHom ∈ s13IsoComps X :=
  w16g_map_mem_s13IsoComps hg hg' hU

theorem s13Supp_conj {X L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hg' : ∀ x ∈ X, g⁻¹ * x * g ∈ X) :
    s13Supp X (L.map (MulAut.conj g).toMonoidHom) =
      (fun U : Subgroup W => U.map g.toMonoidHom) '' s13Supp X L :=
  w16g_s13Supp_conj hg hg'

theorem sSupIndep_conjSubs_of_s13Supp (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A X L : Subgroup (MulAut W)} (hX : IsElemAbelian p X)
    (hXA : ∀ g ∈ A, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hLX : L ≤ X)
    (hdisj : ∀ g ∈ A, s13Supp X (L.map (MulAut.conj g).toMonoidHom) = s13Supp X L ∨
      Disjoint (s13Supp X (L.map (MulAut.conj g).toMonoidHom)) (s13Supp X L)) :
    sSupIndep (conjSubs A (commSub ⊤ L)) :=
  w16g_sSupIndep_conjSubs_of_s13Supp hW hp hp2 hX hXA hLX hdisj

end CFSG.LocalAnalysis.WeakClosure81
