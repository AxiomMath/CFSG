module

public import CFSG.RankThree.PartOne.KE.A5Interface
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents
public import CFSG.RankThree.PartOne.KE.SigmaFactorTransport

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Algebraic

theorem isAlgebraic_zmod_of_card {ℓ f : ℕ} [Fact ℓ.Prime] {k L : Type} [Field k]
    [Field L] [Algebra k L] [IsAlgClosure k L] [CharP L ℓ] (hk : Nat.card k = ℓ ^ f) :
    letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L := by
  have hℓ : ℓ.Prime := Fact.out
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have hkc : CharP k ℓ := ⟨fun x => by
    rw [← (algebraMap k L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L ℓ x⟩
  exact CFSG.LieType.AlgebraicGroups.isAlgebraic_zmod_of_isAlgClosure ℓ k L

end Algebraic

section Commutator

theorem conj_mem_commutator_of_normalizes {G : Type*} [Group G] {Γ : Subgroup G} {y : G}
    (hy : ∀ γ ∈ Γ, y * γ * y⁻¹ ∈ Γ) {u : G} (hu : u ∈ ⁅Γ, Γ⁆) : y * u * y⁻¹ ∈ ⁅Γ, Γ⁆ := by
  have hmap : Γ.map (MulAut.conj y).toMonoidHom ≤ Γ := by
    rintro _ ⟨γ, hγ, rfl⟩
    simpa [MulAut.conj_apply] using hy γ hγ
  have h1 : (⁅Γ, Γ⁆).map (MulAut.conj y).toMonoidHom ≤ ⁅Γ, Γ⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmap hmap
  have := h1 ⟨u, hu, rfl⟩
  simpa [MulAut.conj_apply] using this

theorem commutator_le_self_subgroup {G : Type*} [Group G] (Γ : Subgroup G) : ⁅Γ, Γ⁆ ≤ Γ := by
  refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)

end Commutator

variable {L : Type} [Field L]

theorem e7_a5_factor (hA5 : A5Layer Tag.E7) [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L]
    [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) (v : WeylGroup Tag.E7) (n : ModGL Tag.E7 L)
    (hn : n ∈ monomialSubgroup Tag.E7 L) (hnC : n ∈ adjointGroup Tag.E7 L)
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E7 (a5Nodes Tag.E7),
      ∀ α ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7),
        (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hn⟩ * v) • α = u • (ε • α)) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) ∧
      ∃ h₀ : ModGL Tag.E7 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E7 L (e7Index 3)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
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
  have halg := isAlgebraic_zmod_of_card (ℓ := ℓ) (L := L) hk
  set Γ' : Subgroup (ModGL Tag.E7 L) :=
    rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓ twistedFixedPoints n' Φ
    with hΓ'
  set P' : Subgroup (ModGL Tag.E7 L) := ⁅Γ', Γ'⁆ with hP'
  obtain ⟨hfin, hq, hcent, hsl⟩ := hA5 L ℓ f hf halg ε hε hq2 n' hn'm hn'adj
    (by
      obtain ⟨u, hu, hact⟩ := hcert
      exact ⟨u, hu, fun α hα => by rw [hπn']; exact hact α hα⟩) Γ' P' rfl rfl
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (a5Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  have hnormΓ : ∀ y ∈ Subgroup.normalizer
      (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L)),
      y ∈ twistedFixedPoints n' Φ → ∀ γ ∈ Γ', y * γ * y⁻¹ ∈ Γ' := fun y hy hyR γ hγ =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy γ).1 hγ.1,
      mul_mem (mul_mem hyR hγ.2) (inv_mem hyR)⟩
  have hstd : SigmaFactor n' Fr (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) (fun _ : Unit => P')
      (Subgroup.normalizer
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
    refine ⟨fun _ => hfin, fun _ => hq,
      fun _ => (commutator_le_self_subgroup Γ').trans inf_le_left,
      fun _ => (commutator_le_self_subgroup Γ').trans inf_le_right,
      fun _ => ((commutator_le_self_subgroup Γ').trans inf_le_left).trans
        (rootSpan_le_adjointGroup L _),
      fun _ y hy hyR u hu => conj_mem_commutator_of_normalizes (hnormΓ y hy hyR) hu,
      fun y hy hc => hcent y hy fun u hu => hc () u hu⟩
  have htr := SigmaFactor.transport Fr hFrbij v n hroots hstd
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hΓeq : Γ'.map c₀ =
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) ⊓
        twistedFixedPoints n Φ := by
    have hQ : (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a5Nodes Tag.E7))).map c₀ =
        rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a5Nodes Tag.E7)) :=
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
    rw [hΓ', Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]
  have hPeq : P'.map c₀ = ⁅Γ'.map c₀, Γ'.map c₀⁆ := by
    rw [hP', Subgroup.map_commutator]
  refine ⟨P'.map c₀, ⟨htr.finite, htr.quasi, htr.le_root, htr.le_fix, htr.le_adj,
    fun _ y hy hyR u hu => ?_, htr.thetaFree⟩, ?_⟩
  · rw [hPeq, hΓeq] at hu ⊢
    refine conj_mem_commutator_of_normalizes (fun γ hγ => ?_) hu
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy γ).1 hγ.1,
      mul_mem (mul_mem hyR hγ.2) (inv_mem hyR)⟩
  · obtain ⟨h₀, hh₀⟩ := hsl (e7Index 3) rfl k hk
    refine ⟨V * h₀, fun Y => ?_⟩
    refine ⟨h₀ * simpleRootSL2 Tag.E7 L (e7Index 3)
      (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹, hh₀ Y, ?_⟩
    rw [hcapp]
    group

end CFSG.RankThree.PartOne.KE
