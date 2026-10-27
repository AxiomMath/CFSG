module

public import CFSG.RankThree.PartOne.KE6.E8T3LayerA2
public import CFSG.RankThree.PartOne.KE6.E8T3D4
public import CFSG.RankThree.PartOne.KE6.E8T3E6

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.Steinberg.Adjoint
open scoped MatrixGroups

variable {L : Type} [Field L]

@[expose] def LayerConclusion (n : ModGL Tag.E8 L) (Fr : L →+* L) (S : Set V8)
    (k : Type) [Field k] [Algebra k L] : Prop :=
  ∃ (ι' : Type) (P : ι' → Subgroup (ModGL Tag.E8 L)), IsSigmaFamily n Fr S P ∧
    (S.Nonempty → ∃ (i₀ : ι') (m : Fin Tag.E8.rank) (h₀ : ModGL Tag.E8 L), ∀ Y : SL(2, k),
      h₀ * simpleRootSL2 Tag.E8 L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈
        P i₀)

theorem layer_empty (n : ModGL Tag.E8 L) (Fr : L →+* L) (k : Type) [Field k]
    [Algebra k L] : LayerConclusion n Fr ∅ k := by
  classical
  have hspan : rootSpan Tag.E8 L (∅ : Set V8) = ⊥ := by simp [rootSpan]
  refine ⟨Empty, fun e => e.elim, ⟨fun e => e.elim, fun e => e.elim, fun e => e.elim,
    fun e => e.elim, fun e => e.elim, fun e => e.elim, fun y hy hyR _ => ?_⟩, fun h => ?_⟩
  · rw [hspan, sup_bot_eq] at hy
    refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hspan] at hg
    have : g = 1 := hg
    rw [this, one_mul, mul_one]
  · exact absurd h Set.not_nonempty_empty

theorem sigmaFactor_toSigma_of_normalizer {S : Set V8} (hS : ∀ r ∈ S, IsRoot Tag.E8 r)
    {n : ModGL Tag.E8 L} {Fr : L →+* L} {P : Subgroup (ModGL Tag.E8 L)}
    (h : SigmaFactor n Fr S (fun _ : Unit => P)
      (Subgroup.normalizer (rootSpan Tag.E8 L S : Set (ModGL Tag.E8 L)))) :
    IsSigmaFamily n Fr S (fun _ : Unit => P) :=
  h.toSigma (sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS)
    Subgroup.le_normalizer)

theorem sigmaFactor_union {S₁ S₂ : Set V8} (hS₁ : ∀ r ∈ S₁, IsRoot Tag.E8 r)
    (hS₂ : ∀ r ∈ S₂, IsRoot Tag.E8 r)
    (horth : ∀ α ∈ S₁, ∀ β ∈ S₂, iform (τ := Tag.E8) α β = 0)
    {n : ModGL Tag.E8 L} {Fr : L →+* L} {P₁ P₂ : Subgroup (ModGL Tag.E8 L)}
    (h₁ : SigmaFactor n Fr S₁ (fun _ : Unit => P₁)
      (Subgroup.normalizer (rootSpan Tag.E8 L S₁ : Set (ModGL Tag.E8 L))))
    (h₂ : SigmaFactor n Fr S₂ (fun _ : Unit => P₂)
      (Subgroup.normalizer (rootSpan Tag.E8 L S₂ : Set (ModGL Tag.E8 L)))) :
    IsSigmaFamily n Fr (S₁ ∪ S₂) (Sum.elim (fun _ : Unit => P₁) (fun _ : Unit => P₂)) := by
  have horth' : ∀ α ∈ S₁, ∀ β ∈ S₂, α ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ β) = 0 := fun α hα β hβ => by
    rw [dotProduct_mulVec_eq_iform]
    exact horth α hα β hβ
  have hU := SigmaFactor.union (Or.inr (Or.inr (Or.inr rfl))) hS₁ hS₂ horth' h₁ h₂
  exact hU.toSigma (torus_sup_union_le_normalizers (Or.inr (Or.inr (Or.inr rfl))) hS₁ hS₂ horth')

theorem layer_A2_conclusion [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]
    (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (v : WeylGroup Tag.E8)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (hSv : ∀ α ∈ sigmaSetE8 v, e8T3We ε • α ∈ sigmaSetE8 v)
    (hSneg : ∀ α ∈ sigmaSetE8 v, -α ∈ sigmaSetE8 v) :
    LayerConclusion n (iterateFrobenius L ℓ f) (sigmaSetE8 v) k := by
  obtain ⟨P, hP1, hfac, h₀, hh₀⟩ := layer_A2 hf hk hε hq2 v n hnm hnC hnW hSv hSneg
  refine ⟨Unit, fun _ => P, sigmaFactor_toSigma_of_normalizer (sigmaSetE8_isRoot v) hfac,
    fun _ => ⟨(), e8Index 0, h₀, hh₀⟩⟩

theorem layer_2A2 [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hq2 : ε = -1 → 2 < ℓ ^ f) (v₁ v₂ : WeylGroup Tag.E8)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (hSv₁ : ∀ α ∈ sigmaSetE8 v₁, e8T3We ε • α ∈ sigmaSetE8 v₁)
    (hSneg₁ : ∀ α ∈ sigmaSetE8 v₁, -α ∈ sigmaSetE8 v₁)
    (hSv₂ : ∀ α ∈ sigmaSetE8 v₂, e8T3We ε • α ∈ sigmaSetE8 v₂)
    (hSneg₂ : ∀ α ∈ sigmaSetE8 v₂, -α ∈ sigmaSetE8 v₂)
    (horth : ∀ α ∈ sigmaSetE8 v₁, ∀ β ∈ sigmaSetE8 v₂, iform (τ := Tag.E8) α β = 0) :
    LayerConclusion n (iterateFrobenius L ℓ f) (sigmaSetE8 v₁ ∪ sigmaSetE8 v₂) k := by
  obtain ⟨P₁, hP₁, hfac₁, h₀, hh₀⟩ := layer_A2 hf hk hε hq2 v₁ n hnm hnC hnW hSv₁ hSneg₁
  obtain ⟨P₂, hP₂, hfac₂, -⟩ := layer_A2 hf hk hε hq2 v₂ n hnm hnC hnW hSv₂ hSneg₂
  exact ⟨Unit ⊕ Unit, Sum.elim (fun _ => P₁) (fun _ => P₂),
    sigmaFactor_union (sigmaSetE8_isRoot v₁) (sigmaSetE8_isRoot v₂) horth hfac₁ hfac₂,
    fun _ => ⟨Sum.inl (), e8Index 0, h₀, hh₀⟩⟩

theorem layer_D4 (hD4 : D4TrialityLayer Tag.E8) [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (v : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (a b c : Fin Tag.E8.rank) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • α =
          u • permLattice (List.formPerm [a, b, c]) α) :
    LayerConclusion n (iterateFrobenius L ℓ f)
      ((fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8)) k := by
  obtain ⟨P, hP, hfac, h₀, hh₀⟩ := e8_d4_factor hD4 hf hk v n hnm hnC a b c hab hbc hac ha hb hc
    hcert
  have hroots : ∀ r ∈ (fun γ => v • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      IsRoot Tag.E8 r := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 v
  exact ⟨Unit, fun _ => P, sigmaFactor_toSigma_of_normalizer hroots hfac,
    fun _ => ⟨(), e8Index 3, h₀, hh₀⟩⟩

theorem layer_E6 (hE6 : E6Layer Tag.E8) [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (v : WeylGroup Tag.E8)
    (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hmaps : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8))
    (hrel : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) •
          (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • α +
        ε • ((v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • α) + α = 0) :
    LayerConclusion n (iterateFrobenius L ℓ f)
      ((fun γ => v • γ) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8)) k := by
  obtain ⟨P, hP, hP1, h₀, hh₀⟩ := e8_e6_family hE6 hf hk hε v n hnm hnC hmaps hrel
  exact ⟨Unit, P, hP, fun _ => ⟨(), e8Index 3, h₀, hh₀ ⟩⟩

theorem layer_D4A2 (hD4 : D4TrialityLayer Tag.E8) [IsAlgClosed L] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L]
    [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hq2 : ε = -1 → 2 < ℓ ^ f) (v₁ v₂ : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) (hnC : n ∈ adjointGroup Tag.E8 L)
    (hnW : ∀ x : V8, weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x = e8T3We ε • x)
    (a b c : Fin Tag.E8.rank) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (hcert : ∃ u ∈ parabolicWeylGroup Tag.E8 (d4Nodes Tag.E8),
      ∀ α ∈ parabolicRoots Tag.E8 (d4Nodes Tag.E8),
        (v₁⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v₁) • α =
          u • permLattice (List.formPerm [a, b, c]) α)
    (hSv₂ : ∀ α ∈ sigmaSetE8 v₂, e8T3We ε • α ∈ sigmaSetE8 v₂)
    (hSneg₂ : ∀ α ∈ sigmaSetE8 v₂, -α ∈ sigmaSetE8 v₂)
    (horth : ∀ α ∈ (fun γ => v₁ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      ∀ β ∈ sigmaSetE8 v₂, iform (τ := Tag.E8) α β = 0) :
    LayerConclusion n (iterateFrobenius L ℓ f)
      ((fun γ => v₁ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8) ∪ sigmaSetE8 v₂) k := by
  obtain ⟨P₁, hP₁, hfac₁, h₀, hh₀⟩ := e8_d4_factor hD4 hf hk v₁ n hnm hnC a b c hab hbc hac ha hb
    hc hcert
  obtain ⟨P₂, hP₂, hfac₂, -⟩ := layer_A2 hf hk hε hq2 v₂ n hnm hnC hnW hSv₂ hSneg₂
  have hroots : ∀ r ∈ (fun γ => v₁ • γ) '' parabolicRoots Tag.E8 (d4Nodes Tag.E8),
      IsRoot Tag.E8 r := by
    rintro _ ⟨α, hα, rfl⟩
    exact IsRoot.smul hα.1 v₁
  exact ⟨Unit ⊕ Unit, Sum.elim (fun _ => P₁) (fun _ => P₂),
    sigmaFactor_union hroots (sigmaSetE8_isRoot v₂) horth hfac₁ hfac₂,
    fun _ => ⟨Sum.inl (), e8Index 3, h₀, hh₀⟩⟩

end CFSG.RankThree.PartOne.KE6
