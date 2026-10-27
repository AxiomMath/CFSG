module

public import CFSG.LocalAnalysis.StandardType.GGHLDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGPropFourOneTransfer
public import CFSG.LocalAnalysis.StandardType.GGStdSubExist
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmallLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel
public import CFSG.LocalAnalysis.StandardType.GGTBWNormMpCellLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTorusWNormSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A → ∀ [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
      (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix M → GGIntCartan M C → (∀ i j, α i (h j) = (C i j : ZMod p)) →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A = Subgroup.closure (Set.range φ) →
      ∀ φ' ∈ ggInduced (⊤ : Subgroup (MulAut L')) A, GGWNormConcl ι φ h α φ'

@[expose] def GGTorusWNormSCLift (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      (∀ r, GGTorusLift p r R → p ^ r ≤ Nat.card A) → ∀ [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥A ≃+ V)
      (φ : Λ → MulAut ↥A) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix M → GGIntCartan M C → (∀ i j, α i (h j) = (C i j : ZMod p)) →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      ggAutomizer (MulAut.conj : L' →* MulAut L').range A = Subgroup.closure (Set.range φ) →
      ∀ φ' ∈ ggInduced (⊤ : Subgroup (MulAut L')) A, GGWNormConcl ι φ h α φ'

theorem GGTorusWNormSC.toLift {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusWNormSC p R I) : GGTorusWNormSCLift p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc _
  exact h L' ψ hψ hker hperf A hA hAI h3 hsc

theorem ggTorusWNormSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTorusWNormSC p R' I') :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_
  · intro l hl
    apply hker
    simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ← e.map_one, e.injective.eq_iff] using hl
  · intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφI, fun l => ?_⟩
    change e (φ (e.symm (e (ψ l)))) = e (ψ (a l))
    rw [e.symm_apply_apply, hφ]

theorem ggTorusWNormSC_of_forall_mulAut_eq_conj {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hall : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ α : MulAut L', ∃ l : L', α = MulAut.conj l) :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A _hA _hAI _h3 _hsc _ Λ _ _ M C V _ _ ι φ h α
    _hMw _hC _hpair _hlin hAeq φ' hφ'
  obtain ⟨g, -, hgA, hgact⟩ := hφ'
  obtain ⟨l, hl⟩ := hall L' ψ hψ hker hperf g
  have hmem : φ' ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
    Subgroup.subset_closure
      ⟨MulAut.conj l, ⟨l, rfl⟩, by simpa [hl] using hgA, by simpa [hl] using hgact⟩
  have hcl : φ' ∈ Subgroup.closure (Set.range φ) := by
    rw [← hAeq]
    exact hmem
  have hw : ggLin (p := p) ι φ' ∈ ggHL ι φ h α := by
    have hclosure : Subgroup.closure (Set.range φ) ≤
        (ggHL ι φ h α).comap (ggLin (p := p) ι) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure (Or.inl (Or.inl (Set.mem_range_self i)))
    exact hclosure hcl
  refine ⟨⟨1, ggLin (p := p) ι φ', hw, ?_⟩, fun _ => hw⟩
  intro v
  simp

theorem ggTorusWNormSC_of_lift_card_lt {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hbound : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A < p ^ 3) :
    GGTorusWNormSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3
  exact (not_le.mpr (hbound L' ψ hψ hker hperf A hA hAI) h3).elim

@[expose] def GGTBWExcl (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∨ ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2)

theorem largeEvenLabelAll_wnorm_toLift {p : ℕ} {lab : LargeEvenLabel}
    (h : LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSCLift p R I := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, hq.2.toLift⟩) (h Q hQ)

@[expose] def GGTBWNormLabelInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → ¬ GGTBWExcl lab →
    lab.tag ≠ .twE6 → LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSCLift p R I

@[expose] def GGTBWNormLabelRest : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → ¬ GGTBWExcl lab →
    ¬ ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ lab.n = 1) →
    ¬ (lab.tag = .E8 ∧ p = 5 ∧ 5 ∣ (2 ^ lab.n) ^ 2 + 1) →
    ¬ (lab.tag = .E8 ∧ p = 5 ∧ 5 ∣ 2 ^ lab.n - 1) →
    ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ lab.n = 1) →
    ¬ ((lab.tag = .A ∧ lab.rank ≤ 2) ∨
      ((lab.tag = .twA ∨ lab.tag = .twD) ∧ lab.rank = 2)) →
    ¬ GGTableBNbrInnerNineSmallLabel p lab →
    ¬ GGTableBNbrInnerNineClassicalLabel p lab →
    ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) →
    ¬ ((lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1) →
    ¬ (lab.tag = .E6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) →
    ¬ ((lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n - 1) →
    ¬ (lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ ((lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1) →
    lab.tag ≠ .triD4 →
    lab.tag ≠ .twE6 →
    ¬ ((lab.tag = .D ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
      (lab.tag = .twD ∧ 4 ≤ lab.rank ∧
        (p ∣ 2 ^ lab.n - 1 ∨ (Even lab.rank ∧ p ∣ 2 ^ lab.n + 1)))) →
    ¬ (lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) →
    ¬ (lab.tag = .E6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ ((lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1) →
    ¬ ((lab.tag = .D ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twD ∧ 5 ≤ lab.rank ∧ Odd lab.rank ∧ p ∣ 2 ^ lab.n + 1)) →
    ¬ (lab.tag = .twA ∧ 5 ≤ p ∧ lab.rank + 1 = p ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ (lab.tag = .A ∧ 5 ≤ p ∧ lab.rank + 1 = p ∧ p ∣ 2 ^ lab.n - 1) →
    ¬ (lab.tag = .E8 ∧ 7 ≤ p ∧ p ∣ 2 ^ lab.n - 1) →
    ¬ (lab.tag = .E7 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n - 1) →
    ¬ (lab.tag = .E8 ∧ 7 ≤ p ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ (lab.tag = .E7 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1) →
    lab.tag ≠ .twF4 →
    ¬ ((lab.tag = .E8 ∧ ¬ p ∣ (2 ^ lab.n) ^ 4 - 1 ∧ ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) ∨
      (lab.tag = .E7 ∧ ¬ p ∣ (2 ^ lab.n) ^ 6 - 1) ∨
      (lab.tag = .E6 ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ p ∣ (2 ^ lab.n) ^ 3 - 1) ∨
      (lab.tag = .twE6 ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ p ∣ (2 ^ lab.n) ^ 3 + 1)) →
    ¬ (lab.tag = .D ∧ 6 ≤ lab.rank ∧ Even lab.rank ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) →
    ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) →
    ¬ (lab.tag = .A ∧ lab.rank + 1 = 2 * p ∧ p ∣ 2 ^ lab.n - 1) →
    ¬ (lab.tag = .A ∧ 5 ≤ p ∧ lab.rank + 1 = 3 * p ∧ p ∣ 2 ^ lab.n - 1) →
    ¬ GGTBWNormW4SplitLabel p lab →
    ¬ (lab.tag = .twA ∧ lab.rank + 1 = 2 * p ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ (lab.tag = .E8 ∧ p ≠ 3 ∧ p ∣ (2 ^ lab.n) ^ 2 - 2 ^ lab.n + 1) →
    ¬ (lab.tag = .E8 ∧ 7 ≤ p ∧ p ∣ (2 ^ lab.n) ^ 2 + 1) →
    ¬ (lab.tag = .E6 ∧ 7 ≤ p ∧ p ∣ (2 ^ lab.n) ^ 2 + 2 ^ lab.n + 1) →
    ¬ (lab.tag = .E8 ∧ p ≠ 3 ∧ p ∣ (2 ^ lab.n) ^ 2 + 2 ^ lab.n + 1) →
    ¬ (lab.tag = .E8 ∧ p = 3) →
    ¬ (lab.tag = .E7 ∧ p = 3) →
    ¬ ((lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧
      ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) →
    ¬ (lab.tag = .E7 ∧ 5 ≤ p ∧ p ∣ (2 ^ lab.n) ^ 6 - 1 ∧ ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) →
    ¬ (lab.tag = .E8 ∧ p = 5 ∧ 5 ∣ 2 ^ lab.n + 1) →
    ¬ ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) →
    ¬ ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank ∧
      ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) →
    ¬ (lab.tag = .twE6 ∧ 7 ≤ p ∧ p ∣ (2 ^ lab.n) ^ 2 - 2 ^ lab.n + 1) →
    ¬ ((lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)) ∧ 3 ≤ lab.rank ∧
      ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) →
    ¬ (lab.tag = .twA ∧ 5 ≤ p ∧ lab.rank + 1 = 4 * p ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ GGTBWNormW5UnitLabel p lab →
    ¬ GGTBWNormW5SplitLabel p lab →
    ¬ GGTBWNormW3UnitLabel p lab →
    ¬ GGTBWNormW3SplitLabel p lab →
    ¬ (lab.tag = .twA ∧ 5 ≤ p ∧ lab.rank + 1 = 3 * p ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ (lab.tag = .twA ∧ p = 3 ∧ lab.rank + 1 = 9 ∧ p ∣ 2 ^ lab.n + 1) →
    ¬ (lab.tag = .E6 ∧ p = 3) →
    ¬ (lab.tag = .A ∧ p = 3 ∧ lab.rank + 1 = 9 ∧ 3 ∣ 2 ^ lab.n - 1) →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I

@[expose] def GGTBWNormInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagOnLab S p Bs L →
    ∀ (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) [Fact p.Prime]
      (Λ : Type) [Fintype Λ] [DecidableEq Λ] (M : CoxeterMatrix Λ) (C : Matrix Λ Λ ℤ)
      (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (ι : Additive ↥(ggGamma L hBsN).range ≃+ V) (φ : Λ → MulAut ↥(ggGamma L hBsN).range)
      (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V),
      GGIsWeylMatrix M → GGIntCartan M C → (∀ i j, α i (h j) = (C i j : ZMod p)) →
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) →
      ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
        Subgroup.closure (Set.range φ) →
      ∀ g ∈ Subgroup.normalizer (Bs : Set G), ∀ hgL : g ∈ Subgroup.normalizer (L : Set G),
        ∀ φ' : MulAut ↥(ggGamma L hBsN).range,
          (∀ a, ((φ' a : ↥(ggGamma L hBsN).range) : MulAut L) =
            L.normalizerMonoidHom ⟨g, hgL⟩ * a * (L.normalizerMonoidHom ⟨g, hgL⟩)⁻¹) →
          GGWNormConcl ι φ h α φ'

theorem ggGamma_range_hypsSC_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    IsElemAbelian p (ggGamma L hBsN).range ∧
      (∀ a ∈ (ggGamma L hBsN).range, ∃ φ ∈ I, ∀ l : L,
        φ (ggQuotHom θ l) = ggQuotHom θ (a l)) ∧
      p ^ 3 ≤ Nat.card (ggGamma L hBsN).range ∧ GGTorusSelfCent p (ggGamma L hBsN).range := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  refine ⟨isElemAbelian_range hBc hBp _, ?_, ?_,
    ggTorusSelfCent_ggGamma hBsN hcfg.2.1.2.2.2⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBs3 b,
      fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  · have hcA := card_range_ggGamma_mul L hBN hp hS
    have hle : Nat.card (ggGamma L hBN).range ≤ Nat.card (ggGamma L hBsN).range := by
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, hBBs b.2⟩, rfl⟩
    refine le_trans ?_ hle
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos

theorem normalizerMonoidHom_mem_normalizer_range_ggGamma {G : Type} [Group G] [Finite G]
    {Bs L : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G)) :
    L.normalizerMonoidHom ⟨g, hgL⟩ ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut L)) := by
  set σ := L.normalizerMonoidHom ⟨g, hgL⟩
  have h := mem_normalizer_of_forall_conj_mem (W := (ggGamma L hBsN).range) (g := σ⁻¹)
    (fun w hw => by
      obtain ⟨b, rfl⟩ := hw
      have hgb : g * (b : G) * g⁻¹ ∈ Bs :=
        (Subgroup.mem_normalizer_iff.mp hg b).mp b.2
      rw [inv_inv, ggGamma_conj_normalizer L hBsN ⟨g, hgL⟩ b hgb]
      exact ⟨_, rfl⟩)
  simpa using Subgroup.inv_mem _ h

theorem ggTBWNormInputOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSCLift p R I) :
    GGTBWNormInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM hBsN _ Λ _ _ M C V _ _ ι φ hh α hMw hC hpair hlin hA g hg
    hgL φ' hφ'
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hLc, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, -, hBs3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hAe, hAI, h3, hsc⟩ := ggGamma_range_hypsSC_L hcfg θ hBsN hBs3
  have hrank : ∀ r, GGTorusLift p r R → p ^ r ≤ Nat.card (ggGamma L hBsN).range := by
    intro r hlift
    obtain ⟨-, -, -, hLx, -⟩ := hcfg.tableB_facts
    have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
    have hBBs : B ≤ Bs := hcfg.2.1.1
    have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hBsN
    have hcB := card_range_ggGamma_mul L hBN hp hS
    have hle : Nat.card (ggGamma L hBN).range ≤ Nat.card (ggGamma L hBsN).range := by
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨⟨b, hBBs b.2⟩, rfl⟩
    have h1 := succ_le_twoLocalRank_of_torusLift hp hLx (hS.1.1.2 x hS.2.1) hS.2.2.1 hLc θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma L hBN).range * p := by
      rw [hcB, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle
  exact hT L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hLc _ hAe hAI h3 hsc
    hrank Λ M C V ι φ hh α hMw hC hpair hlin hA φ'
    ⟨_, Subgroup.mem_top _, normalizerMonoidHom_mem_normalizer_range_ggGamma hBsN hg hgL, hφ'⟩

theorem ggXFixedRefl_mem_ggHL {G : Type} [Group G] [Finite G] {S : ℕ → LargeEvenLabel → Prop}
    (hW : GGTBWNormInputOn S)
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hM : GGInnerDiagOnLab S p Bs L)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥(ggGamma L hBsN).range ≃+ V) (φ : Λ → MulAut ↥(ggGamma L hBsN).range)
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hMw : GGIsWeylMatrix M) (hC : GGIntCartan M C) (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hA : ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range =
      Subgroup.closure (Set.range φ))
    (t : MulAut ↥Bs) (ht : t ∈ ggInduced ⊤ Bs) (htr : GGIsReflection p t) (hxB : x ∈ Bs)
    (htx : t ⟨x, hxB⟩ = ⟨x, hxB⟩) :
    ∃ g ∈ Subgroup.normalizer (Bs : Set G), ∃ hgL : g ∈ Subgroup.normalizer (L : Set G),
      (∀ b : ↥Bs, ((t b : ↥Bs) : G) = g * b * g⁻¹) ∧
      ∀ φ' : MulAut ↥(ggGamma L hBsN).range,
        (∀ a, ((φ' a : ↥(ggGamma L hBsN).range) : MulAut L) =
          L.normalizerMonoidHom ⟨g, hgL⟩ * a * (L.normalizerMonoidHom ⟨g, hgL⟩)⁻¹) →
        ggLin (p := p) ι φ' ∈ ggHL ι φ h α := by
  obtain ⟨hp, hBs, -, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨g, -, hgB, hg⟩ := ht
  have hgx : g * x * g⁻¹ = x := by
    have h2 := hg ⟨x, hxB⟩
    rw [htx] at h2
    exact h2.symm
  have hnx : g * x = x * g := by
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [hgx]
  have hgZ : g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    have h1 := Subgroup.normalizer_le_normalizer_closure ({x} : Set G)
      (Subgroup.centralizer_le_normalizer ({x} : Set G)
        (Subgroup.mem_centralizer_singleton_iff.mpr hnx))
    rw [← Subgroup.zpowers_eq_closure] at h1
    exact h1
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_sstar' hS hnc hgZ
  refine ⟨g, hgB, hgL, hg, fun φ' hφ' => ?_⟩
  refine (hW G p B Bs x L D J hcfg hM hBsN Λ M C V ι φ h α hMw hC hpair hlin hA g hgB
    hgL φ' hφ').2 ?_
  have hkey : ∀ b : ↥Bs, φ' ((ggGamma L hBsN).rangeRestrict b) =
      (ggGamma L hBsN).rangeRestrict (t b) := by
    intro b
    apply Subtype.ext
    have hgb : g * (b : G) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB b).mp b.2
    have htb : (⟨g * (b : G) * g⁻¹, hgb⟩ : ↥Bs) = t b := Subtype.ext (hg b).symm
    rw [hφ', MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict,
      ggGamma_conj_normalizer L hBsN ⟨g, hgL⟩ b hgb, htb]
  have htt : ∀ b : ↥Bs, t (t b) = b := fun b => by
    have := congrArg (fun f : MulAut ↥Bs => f b) htr.1
    simpa [pow_two] using this
  have hfixB : ∀ b : ↥Bs, ggGamma L hBsN (t b) = ggGamma L hBsN b → t b = b := by
    intro b hb
    set u : ↥Bs := t b * b⁻¹ with hu_def
    have hu1 : ggGamma L hBsN u = 1 := by
      rw [hu_def, map_mul, map_inv, hb, mul_inv_cancel]
    have h2 : (u : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨u.2, (ggGamma_eq_one_iff L hBsN u).mp hu1⟩
    rw [inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1 hLx
      hS.2.2.2.2] at h2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
    have hu : u = (⟨x, hxB⟩ : ↥Bs) ^ k :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    have htu : t u = u := by rw [hu, map_zpow, htx]
    have htu' : t u = u⁻¹ := by rw [hu_def, map_mul, map_inv, htt, mul_inv_rev, inv_inv]
    have hu2 : u ^ 2 = 1 := by
      rw [pow_two]
      calc u * u = u * t u := by rw [htu]
        _ = 1 := by rw [htu', mul_inv_cancel]
    have hup : u ^ p = 1 := Subtype.ext (by simpa using hBs.2 _ u.2)
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    have ho : orderOf u = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hu2) hcop)
        (orderOf_dvd_of_pow_eq_one hup)
    have hu1' : u = 1 := orderOf_eq_one_iff.mp ho
    rw [hu_def, mul_inv_eq_one] at hu1'
    exact hu1'
  set E : Subgroup G := (ggFix t).map Bs.subtype with hE_def
  have hEBs : E ≤ Bs := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEBs.trans hBsN
  have hxE : x ∈ E := ⟨⟨x, hxB⟩, htx, rfl⟩
  have hcA := card_range_ggGamma_mul_of hp hBs hxB hS.2.2.1 hLx hS.2.2.2.2 hBsN
  have hEab : IsElemAbelian p E :=
    ⟨⟨⟨fun a b => Subtype.ext (TableB.IsElemAbelian.comm hBs (hEBs a.2) (hEBs b.2))⟩⟩,
      fun a ha => hBs.2 a (hEBs ha)⟩
  have hcE := card_range_ggGamma_mul_of hp hEab hxE hS.2.2.1 hLx hS.2.2.2.2 hEN
  have hEF : Nat.card E = Nat.card {b : ↥Bs // t b = b} :=
    (Nat.card_congr (Subgroup.equivMapOfInjective (ggFix t) Bs.subtype
      Bs.subtype_injective).toEquiv).symm
  have hfix : Nat.card {a : ↥(ggGamma L hBsN).range // φ' a = a} =
      Nat.card (ggGamma L hEN).range := by
    refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨(a.1 : MulAut L), ?_⟩) ⟨?_, ?_⟩)
    · obtain ⟨⟨_, b, rfl⟩, ha⟩ := a
      have hrr : (⟨ggGamma L hBsN b, b, rfl⟩ : ↥(ggGamma L hBsN).range) =
          (ggGamma L hBsN).rangeRestrict b := rfl
      rw [hrr, hkey] at ha
      have hb := hfixB b (congrArg Subtype.val ha)
      exact ⟨⟨b, ⟨b, hb, rfl⟩⟩, rfl⟩
    · intro a a' haa
      simp only [Subtype.mk.injEq] at haa
      exact Subtype.ext (Subtype.ext haa)
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩⟩, rfl⟩
      refine ⟨⟨(ggGamma L hBsN).rangeRestrict b, ?_⟩, rfl⟩
      rw [hkey]
      exact congrArg _ hb
  refine ⟨?_, ?_⟩
  · refine MulEquiv.ext fun a => ?_
    obtain ⟨b, rfl⟩ := (ggGamma L hBsN).rangeRestrict_surjective a
    rw [pow_two, MulAut.mul_apply, hkey, hkey, htt, MulAut.one_apply]
  · rw [hfix]
    refine Nat.eq_of_mul_eq_mul_right hp.pos ?_
    rw [hcE, hEF, htr.2, ← hcA]

end CFSG.StandardType
