module

public import CFSG.LocalAnalysis.StandardType.GGLargeFixDefs
public import CFSG.LocalAnalysis.StandardType.GGResXDichotomyDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeRowDimDefs
import CFSG.LocalAnalysis.StandardType.GGResXDatumLFrame
import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrame
import CFSG.LocalAnalysis.StandardType.GGDepAConfig
import CFSG.LocalAnalysis.StandardType.GGSecFiveBarBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l04fFS_core
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput) (hDim : GGTwoNodeRowDimKnown)
    (hH : GGResHyp p B Bs x L D J y K) {N : ℕ}
    (hrow : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J K)
    (hp2 : p ≠ 2) (hN5 : 5 ≤ N) (hpN : p ∣ N) (hLd : GGResXDatum p Bs L) (hx : x ∈ Bs)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Λ → MulAut ↥Bs) (h₀ : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V) (e : Fin (N - 1) ≃ Λ)
    (hM : M = (CoxeterMatrix.A (N - 1)).reindex e)
    (hInt : GGIntCartan M C)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h₀ i)
    (hpair : ∀ i j, α i (h₀ j) = (C i j : ZMod p))
    (hclosK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hlast : GGResXDatumAIndep p Bs K (N - 1) →
      LinearIndependent (ZMod p) (fun i => h₀ (e i))) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
      (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (T : Type) (_ : Finite T) (s : T → (V ≃ₗ[ZMod p] V)),
      Module.finrank (ZMod p) V ≤ N ∧
      (∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)) ∧
      (∀ i v, r i v = v - α i v • h i) ∧
      Subgroup.closure (Set.range r) = (ggAutomizer K Bs).map (ggLin (p := p) ι) ∧
      (∀ k, GGLinRefl (s k)) ∧
      (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected ∧
      Subgroup.closure (Set.range s) = (ggAutomizer L Bs).map (ggLin (p := p) ι) ∧
      ggLinFix (Set.range s) = Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)} ∧
      ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 ∧ ι (Additive.ofMul ⟨x, hx⟩) ∉ ggLinFix (Set.range r) ∧
      (∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      (GGResXDatumAIndep p Bs K (N - 1) → LinearIndependent (ZMod p) h) := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  obtain ⟨T, iT, s, hsrefl, hsconn, hsclos, hsfix, hsx0⟩ :=
    ggResXDatum_lframe hFix hH hx hLd V ι
  let h' : Fin (N - 1) → V := fun i => h₀ (e i)
  let α' : Fin (N - 1) → Module.Dual (ZMod p) V := fun i => α (e i)
  let r' : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  have hrclos : Subgroup.closure (Set.range r') = (ggAutomizer K Bs).map (ggLin (p := p) ι) := by
    rw [hclosK, MonoidHom.map_closure]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨φ (e i), ⟨e i, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
      exact ⟨e.symm j, by simp [r']⟩
  have hxnot : ι (Additive.ofMul ⟨x, hx⟩) ∉ ggLinFix (Set.range r') := by
    intro hxfix
    have hfixphi : ∀ j : Λ, φ j ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro j
      apply (ggLin_fix_iff (p := p) ι (φ j) ⟨x, hx⟩).mpr
      have hmem := hxfix (r' (e.symm j)) (Set.mem_range_self (e.symm j))
      simpa [r'] using hmem
    have hfixaut : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      rw [hclosK]
      exact ggFixed_of_mem_closure φ ⟨x, hx⟩ hfixphi
    have hx1 : x = 1 := by
      have h := hWA G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K
        hH.2.2.2.2.1 hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 ⟨x, hx⟩
        (Subgroup.mem_zpowers x) hfixaut
      simpa using h
    exact l05nDD1_x_ne_one hH hx1
  have hnotransv : ∀ g ∈ Subgroup.closure (Set.range r' ∪ Set.range s),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    intro g hg
    rw [Subgroup.closure_union] at hg
    rw [hrclos, hsclos, ← Subgroup.map_sup] at hg
    obtain ⟨ψ, hψ, hψg⟩ := Subgroup.mem_map.mp hg
    have hψtop : ψ ∈ ggAutomizer ⊤ Bs :=
      sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hψ
    have hψind : ψ ∈ ggInduced ⊤ Bs := by
      rwa [ggAutomizer_eq] at hψtop
    have hNT2 : ¬ (Module.finrank (ZMod p) (ggLinMove (ggLin (p := p) ι ψ)) = 1 ∧
        ggLinMove (ggLin (p := p) ι ψ) ≤ ggLinFix {ggLin (p := p) ι ψ}) := by
      rw [← ggIsTransvection_iff_ggLin (p := p) ι ψ]
      exact hH.2.2.2.1 ψ hψind
    rw [← hψg]
    intro hconj
    refine hNT2 ⟨hconj.1, ?_⟩
    intro z hz
    rw [ggLinMove, LinearMap.mem_range] at hz
    obtain ⟨w, rfl⟩ := hz
    show ∀ a : V ≃ₗ[ZMod p] V, a ∈ ({ggLin (p := p) ι ψ} : Set (V ≃ₗ[ZMod p] V)) →
      a (((ggLin (p := p) ι ψ : V →ₗ[ZMod p] V) -
          (LinearMap.id : V →ₗ[ZMod p] V)) w) =
        (((ggLin (p := p) ι ψ : V →ₗ[ZMod p] V) -
          (LinearMap.id : V →ₗ[ZMod p] V)) w)
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact hconj.2 w
  refine ⟨V, inferInstance, inferInstance, ι, h', α', r', T, iT, s, ?_, ?_, ?_, hrclos,
    hsrefl, hsconn, hsclos, hsfix, hsx0, hxnot, hnotransv, ?_⟩
  · have hcardBs : Nat.card ↥Bs ≤ p ^ N := hDim G p B Bs x L D J y K N hH hrow hp2 hN5 hpN
    have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
    have hcardV : Nat.card V = Nat.card ↥Bs := (card_eq_of_ggLin ι).symm
    have hpow : p ^ Module.finrank (ZMod p) V = Nat.card V :=
      FiniteField.pow_finrank_eq_natCard p V
    have hle : p ^ Module.finrank (ZMod p) V ≤ p ^ N := by rw [hpow, hcardV]; exact hcardBs
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle
  · intro i j
    change α (e i) (h₀ (e j)) = (CartanMatrix.A (N - 1) i j : ZMod p)
    rw [← ggIndep_cartan_of_reindex e hInt hM i j]
    exact hpair (e i) (e j)
  · intro i v
    change ggLin (p := p) ι (φ (e i)) v = v - α (e i) v • h₀ (e i)
    exact hlin (e i) v
  · exact hlast

theorem ggTwoNodeFrame_of_datums (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    (hDim : GGTwoNodeRowDimKnown) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {N : ℕ}
    (hrow : GGResRowAt (fun p labJ labK => ggRowTwoNode p labJ labK ∧ labK.rank + 1 = N) p J K)
    (hp2 : p ≠ 2) (hN5 : 5 ≤ N) (hpN : p ∣ N) (hKd : GGResXDatumA p Bs K (N - 1))
    (hLd : GGResXDatum p Bs L) (hx : x ∈ Bs) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
      (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V)
      (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (T : Type) (_ : Finite T) (s : T → (V ≃ₗ[ZMod p] V)),
      Module.finrank (ZMod p) V ≤ N ∧
      (∀ i j, α i (h j) = (CartanMatrix.A (N - 1) i j : ZMod p)) ∧
      (∀ i v, r i v = v - α i v • h i) ∧
      Subgroup.closure (Set.range r) = (ggAutomizer K Bs).map (ggLin (p := p) ι) ∧
      (∀ k, GGLinRefl (s k)) ∧
      (SimpleGraph.fromRel fun i j => s i * s j ≠ s j * s i).Connected ∧
      Subgroup.closure (Set.range s) = (ggAutomizer L Bs).map (ggLin (p := p) ι) ∧
      ggLinFix (Set.range s) = Submodule.span (ZMod p) {ι (Additive.ofMul ⟨x, hx⟩)} ∧
      ι (Additive.ofMul ⟨x, hx⟩) ≠ 0 ∧ ι (Additive.ofMul ⟨x, hx⟩) ∉ ggLinFix (Set.range r) ∧
      (∀ g ∈ Subgroup.closure (Set.range r ∪ Set.range s),
        ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) ∧
      (GGResXDatumAIndep p Bs K (N - 1) → LinearIndependent (ZMod p) h) := by
  classical
  by_cases hI : GGResXDatumAIndep p Bs K (N - 1)
  · obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h₀, α, e, hM, _hW, hInt, hlin, _hrefl, hpair, _hf,
      hclosK, hindep⟩ := hI
    let := i1
    let := i2
    let := i3
    let := i4
    exact l04fFS_core (M := M) (C := C) hFix hWA hDim hH hrow hp2 hN5 hpN hLd hx
      ι φ h₀ α e hM hInt hlin hpair hclosK (fun _ => hindep.comp e e.injective)
  · obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h₀, α, e, hM, _hW, hInt, hlin, _hrefl, hpair, _hf,
      hclosK⟩ := hKd
    let := i1
    let := i2
    let := i3
    let := i4
    exact l04fFS_core (M := M) (C := C) hFix hWA hDim hH hrow hp2 hN5 hpN hLd hx
      ι φ h₀ α e hM hInt hlin hpair hclosK (fun hI' => absurd hI' hI)

end CFSG.StandardType

end
