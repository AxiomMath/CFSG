module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7LNC
import CFSG.GroupTheory.GL52.SylowTools

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma hdRo7CLStab_normalizes
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hx : x ∈ Bs) {ψ : MulAut ↥Bs} (hψ : ψ ∈ ggAutomizer ⊤ Bs)
    (hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∀ φ ∈ ggAutomizer L Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer L Bs := by
  have hS := hH.1.1.2.2.2.2.2.2.1
  obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hψ
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := by
    refine mem_normalizer_of_sstar' hS hnc ?_
    apply CFSG.GroupTheory.GL52.mem_normalizer_zpowers_of_conj_mem
    have hconj : g * x * g⁻¹ = x := by
      have h1 : g * (⟨x, hx⟩ : ↥Bs) * g⁻¹ = (⟨x, hx⟩ : ↥Bs) := by
        rw [← hφg (⟨x, hx⟩ : ↥Bs), hψx]
      simpa using h1
    rw [hconj]
    exact Subgroup.mem_zpowers x
  intro φ hφ
  obtain ⟨l, hl, hlN, hφl⟩ := mem_ggAutomizer_iff.mp hφ
  refine mem_ggAutomizer_iff.mpr ⟨g * l * g⁻¹, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hgL l).mp hl
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hlN) (Subgroup.inv_mem _ hgN)
  · intro b
    rw [MulAut.mul_apply, MulAut.mul_apply, hφg, hφl, inv_apply_of_forall hφg]
    group

lemma hdRo7CLStab_main
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hx : x ∈ Bs)
    (hx0 : ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = b 0)
    (hAL : ∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a) :
    ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (b 0) = b 0 →
      ∀ s, C2SP p b s → C2SP p b (a * s * a⁻¹) := by
  intro a ha hfix s hs
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
  have hψx : ψ ⟨x, hx⟩ = ⟨x, hx⟩ :=
    (ggLin_fix_iff (p := p) ι ψ (⟨x, hx⟩ : ↥Bs)).mpr (by rw [hx0]; exact hfix)
  have hnorm := hdRo7CLStab_normalizes hH hnc hx hψ hψx
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp ((hAL s).mpr hs)
  have hconj : ggLin (p := p) ι ψ * ggLin (p := p) ι φ * (ggLin (p := p) ι ψ)⁻¹ =
      ggLin (p := p) ι (ψ * φ * ψ⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [hconj]
  exact (hAL _).mp (Subgroup.mem_map.mpr ⟨ψ * φ * ψ⁻¹, hnorm φ hφ, rfl⟩)

theorem c2_lstab_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], GGResRowAt ggRowCorank2C p J L →
      ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
        (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (hx : x ∈ Bs), p = 3 → 5 ≤ n →
        ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = b 0 →
        (∀ a, a ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι) ↔ C2SP p b a) →
        ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (b 0) = b 0 →
          ∀ s, C2SP p b s → C2SP p b (a * s * a⁻¹) := by
  intro G _ _ p B Bs x L D J y K hH hpFact hrow n V _ _ ι b hx hp hn hx0 hAL
  obtain ⟨S, hSle, hSp, hSnc⟩ :=
    CFSG.StandardType.HdRo7LNC.lnc_holds G p B Bs x L D J y K hH (Or.inl hrow)
  exact hdRo7CLStab_main hH ⟨S, hSle, hSp, hSnc⟩ ι b hx hx0 hAL

end CFSG.StandardType.HdRo7C
