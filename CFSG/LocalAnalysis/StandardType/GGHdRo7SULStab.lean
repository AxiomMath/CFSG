module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7LNC
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLStab
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7SULStabAux_normalizes
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hx : x ∈ Bs) {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer ⊤ Bs)
    (hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ φ ∈ ggAutomizer L Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer L Bs :=
  hdRo7CLStab_normalizes hH hnc hx hψ hψx

lemma hdRo7SULStabAux_main
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin m) (ZMod p) V) (hx : x ∈ Bs)
    (hx0 : ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = SUOnes p b)
    (hAL : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ SUPerm p b a) :
    ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (SUOnes p b) = SUOnes p b →
      ∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹) := by
  intro a ha hfix s hs
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
  have hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    (ggLin_fix_iff (p := p) ι ψ (⟨x, hx⟩ : ↥Bs)).mpr (by rw [hx0]; exact hfix)
  have hnorm := hdRo7SULStabAux_normalizes hH hnc hx hψ hψx
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp ((hAL s).mpr hs)
  have hconj : ggLin (p := p) ι ψ * ggLin (p := p) ι φ * (ggLin (p := p) ι ψ)⁻¹ =
      ggLin (p := p) ι (ψ * φ * ψ⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hconj]
  exact (hAL _).mp (Subgroup.mem_map.mpr ⟨ψ * φ * ψ⁻¹, hnorm φ hφ, rfl⟩)

theorem su_lstab_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], GGResRowAt ggRowSUCorank2 p J L →
      ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
        (b : Module.Basis (Fin m) (ZMod p) V) (hx : x ∈ Bs), p = 3 → 7 ≤ m → ¬ 3 ∣ m →
        ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = SUOnes p b →
        (∀ g, g ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ SUPerm p b g) →
        ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (SUOnes p b) = SUOnes p b →
          ∀ s, SUPerm p b s → SUPerm p b (a * s * a⁻¹) := by
  intro G _ _ p B Bs x L D J y K hH hpFact hrow m V _ _ ι b hx hp hm h3 hx0 hAL
  obtain ⟨S, hSle, hSp, hSnc⟩ :=
    CFSG.StandardType.HdRo7LNC.lnc_holds G p B Bs x L D J y K hH (Or.inr hrow)
  exact hdRo7SULStabAux_main hH ⟨S, hSle, hSp, hSnc⟩ ι b hx hx0 hAL

end CFSG.StandardType.HdRo7SU
