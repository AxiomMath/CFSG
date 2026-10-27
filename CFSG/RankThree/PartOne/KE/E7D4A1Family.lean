module

public import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic
public import CFSG.RankThree.PartOne.KE.SigmaFactorTransport
public import CFSG.RankThree.PartOne.KE.A1Fixed
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.RankThree.PartOne.KGD (iterateFrobenius_bijective)
open scoped MatrixGroups Pointwise

variable {L : Type} [Field L]

theorem e7_d4_swap_factor (hD4 : D4TranspositionLayer Tag.E7) [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L]
    [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (v : WeylGroup Tag.E7) (n : ModGL Tag.E7 L)
    (hn : n ∈ monomialSubgroup Tag.E7 L) (hnC : n ∈ adjointGroup Tag.E7 L)
    (a b : Fin Tag.E7.rank) (hab : a ≠ b)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (d4Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • α =
          u • permLattice (Equiv.swap a b) α) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      P = rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) ∧
      ∀ m : Fin Tag.E7.rank, m.val = 3 → ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L m
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hVadj : V ∈ adjointGroup Tag.E7 L := canonicalRep_mem_adjointGroup _ L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hn'adj : n' ∈ adjointGroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVadj) hnC) hVadj
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  set P' : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓ twistedFixedPoints n' Φ
    with hP'
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have hAlg : (letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L) :=
    isAlgebraic_zmod_of_isAlgClosure (k := k)
  obtain ⟨hfin, hq, hcent, hsl⟩ := hD4 L ℓ f hf hAlg a b hab ha hb n' hn'm hn'adj
    (by rw [hπn']; exact hcert) P' rfl
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  have hstd : SigmaFactor n' Fr (parabolicRoots Tag.E7 (d4Nodes Tag.E7)) (fun _ : Unit => P')
      (Subgroup.normalizer
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (d4Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
    refine ⟨fun _ => hfin, fun _ => hq, fun _ => inf_le_left, fun _ => inf_le_right,
      fun _ => inf_le_left.trans (rootSpan_le_adjointGroup L _), fun _ y hy hyR u hu => ?_,
      fun y hy hc => hcent y hy fun u hu => hc () u hu⟩
    have hu2 : u ∈ twistedFixedPoints n' Φ := hu.2
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy u).1 hu.1,
      mul_mem (mul_mem hyR hu2) (inv_mem hyR)⟩
  have htr := SigmaFactor.transport Fr hFrbij v n hroots hstd
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hPeq : P'.map c₀ =
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓
        twistedFixedPoints n Φ := by
    have hQ : (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (d4Nodes Tag.E7))).map c₀ =
        rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) :=
      map_conj_rootSpan v hroots
    have hR : (twistedFixedPoints n' Φ).map c₀ = twistedFixedPoints n Φ := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hcapp]
        exact (mem_twistedFixedPoints_conj hΦV).1 hx
      · intro hy
        refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
        · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
          rw [e]
          exact hy
        · rw [hcapp]
          group
    rw [hP', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  refine ⟨P'.map c₀, hPeq, ⟨htr.finite, htr.quasi, htr.le_root, htr.le_fix, htr.le_adj,
    fun _ y hy hyR u hu => ?_, htr.thetaFree⟩, fun m hm => ?_⟩
  · rw [hPeq] at hu ⊢
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy u).1 hu.1,
      mul_mem (mul_mem hyR hu.2) (inv_mem hyR)⟩
  · obtain ⟨h₀, hh₀⟩ := hsl m hm k hk
    refine ⟨V * h₀, fun Y => ?_⟩
    refine ⟨h₀ * simpleRootSL2 Tag.E7 L m
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹, hh₀ Y, ?_⟩
    rw [hcapp]
    group

theorem e7_d4a1_sigma_family (hD4 : D4TranspositionLayer Tag.E7) [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Finite k] [Algebra k L]
    [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) (hk4 : 4 ≤ Nat.card k) (v : WeylGroup Tag.E7)
    (n : ModGL Tag.E7 L) (hn : n ∈ monomialSubgroup Tag.E7 L) (hnC : n ∈ adjointGroup Tag.E7 L)
    (a b : Fin Tag.E7.rank) (hab : a ≠ b)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (d4Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (d4Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • α =
          u • permLattice (Equiv.swap a b) α)
    {r : Fin Tag.E7.rank → ℤ} (hr : IsRoot Tag.E7 r)
    (hnr : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • r = r)
    (horth : ∀ α ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7),
      α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r) = 0) :
    ∃ P : Unit ⊕ Unit → Subgroup (ModGL Tag.E7 L),
      IsSigmaFamily n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7) ∪ {r, -r}) P ∧
      P (Sum.inl ()) =
        rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7)) ⊓
          twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) ∧
      ∀ m : Fin Tag.E7.rank, m.val = 3 → ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L m
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P (Sum.inl ()) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card k := fun c => by
    rw [hk]
    exact iterateFrobenius_def ℓ f c
  obtain ⟨PD, hPD, hfD, hslD⟩ := e7_d4_swap_factor hD4 hf hk v n hn hnC a b hab ha hb hcert
  have hmw := mapsRootLines_weylQuotientHom (τ := .E7) (R := L) ⟨n, hn⟩
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq hn hmw hr hnr
  obtain ⟨PA, -, hfA⟩ := a1_fixed_factor (K := k) (iterateFrobenius L ℓ f) hFr hk4 hr n s hs
  have hroots : ∀ α ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7),
      IsRoot Tag.E7 α := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 v
  have hrootsA : ∀ α ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)), IsRoot Tag.E7 α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  have horth' : ∀ α ∈ (fun γ => v • γ) '' parabolicRoots Tag.E7 (d4Nodes Tag.E7),
      ∀ β ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    intro α hα β hβ
    rcases hβ with rfl | rfl
    · exact horth α hα
    · rw [Matrix.mulVec_neg, dotProduct_neg, horth α hα, neg_zero]
  have hU := SigmaFactor.union (Or.inr (Or.inr (Or.inl rfl))) hroots hrootsA horth' hfD hfA
  refine ⟨Sum.elim (fun _ => PD) (fun _ => PA),
    hU.toSigma (torus_sup_union_le_normalizers (Or.inr (Or.inr (Or.inl rfl))) hroots hrootsA
      horth'), hPD, hslD⟩

end CFSG.RankThree.PartOne.KE
