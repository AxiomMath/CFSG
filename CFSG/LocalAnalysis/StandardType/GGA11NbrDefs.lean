module

public import CFSG.LocalAnalysis.StandardType.GGA11FrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

@[expose] def fPow {G : Type} [Group G] (f : Fin 4 → G) (v : Fin 4 → ZMod 7) : G :=
  f 0 ^ (v 0).val * f 1 ^ (v 1).val * f 2 ^ (v 2).val * f 3 ^ (v 3).val

@[expose] def ConjMat {G : Type} [Group G] (f : Fin 4 → G) (h : G) (M : Certificates.A8Nbr476.M4) :
    Prop :=
  ∀ v : Fin 4 → ZMod 7, h * fPow f v * h⁻¹ = fPow f (Matrix.vecMul v M)

@[expose] def ell {G : Type} [Group G] (f : Fin 4 → G) (c : ZMod 7) : G :=
  f 0 * f 1 * f 2 * f 3 ^ c.val

@[expose] def A11Ctx {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G) : Prop :=
  GGSecFiveRestHyp 7 B Bs x L D J ∧ GGSecFiveA11Config 7 B Bs x L D J ∧
    A11FrameSpec B Bs x L D J y K φ₃ f n ∧ A11FrameExtra Bs J f ∧ A11CohSpec φ₃ f n Φ ∧ A11RhoSpec Φ ρ

@[expose] def A11NbrLineInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      Subgroup.zpowers y' = Subgroup.zpowers (f 3) ∨
        ∃ c : ZMod 7, c ≠ 1 ∧ Subgroup.zpowers y' = Subgroup.zpowers (ell f c)

@[expose] def A11NbrInftyInput : Prop :=
  GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      Subgroup.zpowers y' = Subgroup.zpowers (f 3) → K' = K

@[expose] noncomputable def X8 (i j : Fin 3) : Set (SL 9) :=
  {g | ∃ M : Matrix (Fin 3) (Fin 3) F2, M * Om = Om * M ∧ ∀ a b : Fin 9,
    g.1 a b = (if a = b then 1 else 0) +
      (if blk (Fin.castLE (by omega) a) = (i.castSucc : Fin 4) ∧
          blk (Fin.castLE (by omega) b) = (j.castSucc : Fin 4)
        then M (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b)) else 0)}

@[expose] noncomputable def GJ : Subgroup (SL 9) :=
  Subgroup.closure {g | ∃ i j : Fin 3, i ≠ j ∧ g ∈ X8 i j}

@[expose] def A11NbrFrobInput : Prop :=
  GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' → ∀ c : ZMod 7, (c = 2 ∨ c = 4) →
      Subgroup.zpowers y' = Subgroup.zpowers (ell f c) → K' ≤ Clos φ₃ ρ

@[expose] def A11LemmaRInput : Prop :=
  ∀ A : Submonoid Certificates.A8Nbr476.M4, G314gens ⊆ (A : Set Certificates.A8Nbr476.M4) →
    (∀ a ∈ A, IsUnit a.det ∧ a⁻¹ ∈ A) → (∀ t ∈ A, ¬ Certificates.A8Nbr476.IsTransv t) →
    (∀ h ∈ A, ∀ j : Fin 4, Matrix.vecMul (ev j) h = ev j → Good9B j h) →
    ∀ r ∈ A, (r - 1).rank = 1 → r ∈ Submonoid.closure G314gens

@[expose] def A11BadFixInput : Prop :=
  ∀ c : ZMod 7, (c = 0 ∨ c = 3 ∨ c = 5 ∨ c = 6) →
    ∀ r ∈ Submonoid.closure G314gens, (r - 1).rank = 1 →
      Matrix.vecMul ![1, 1, 1, c] r = ![1, 1, 1, c] →
      r = !![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1] ∨ r = !![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,1] ∨
        r = !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1] ∨
        (c = 0 ∧ (r = !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,2] ∨ r = !![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,4]))

@[expose] def A11NbrLabelInput : Prop :=
  GGNbrTablePNbrInputOn GGRegimeA11 → GGLabelRigidInput → GGTCJKnown →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      StatedClassicalModel (K' ⧸ Subgroup.center K') .PSL 9 2 1 ∨
        GGHasLabel ⟨.A, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.C, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.twD, 4, 3⟩ (K' ⧸ Subgroup.center K')

@[expose] def A11NbrReflGenInput :
    Prop :=
  GGNbrTableBWeylInput → GGNbrReflGenNonSplitInput → GGLabelRigidInput → GGInnerDiagMpInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      (GGHasLabel ⟨.A, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.C, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.twD, 4, 3⟩ (K' ⧸ Subgroup.center K')) →
      GGReflGenerated 7 (ggAutomizer K' Bs)

@[expose] def A11AMatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∃ A : Submonoid Certificates.A8Nbr476.M4,
      (∀ h ∈ Subgroup.normalizer (Bs : Set G), ∃ M ∈ A, ConjMat f h M) ∧
      (∀ M ∈ A, ∃ h ∈ Subgroup.normalizer (Bs : Set G), ConjMat f h M) ∧
      G314gens ⊆ (A : Set Certificates.A8Nbr476.M4) ∧
      (∀ a ∈ A, IsUnit a.det ∧ a⁻¹ ∈ A) ∧ (∀ t ∈ A, ¬ Certificates.A8Nbr476.IsTransv t) ∧
      (∀ h ∈ A, ∀ j : Fin 4, Matrix.vecMul (ev j) h = ev j → Good9B j h)

@[expose] def A11A8HomolInput :
    Prop :=
  GGInnerDiagMpInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      StatedClassicalModel (K' ⧸ Subgroup.center K') .PSL 9 2 1 → ∀ c : ZMod 7,
      Subgroup.zpowers y' = Subgroup.zpowers (ell f c) →
      ∃ M : Fin 3 → Certificates.A8Nbr476.M4, Function.Injective M ∧ ∀ i : Fin 3,
        (∃ h ∈ K', h ∈ Subgroup.normalizer (Bs : Set G) ∧ ConjMat f h (M i)) ∧ (M i - 1).rank = 1 ∧
          M i ^ 3 = 1 ∧ Matrix.vecMul ![1, 1, 1, c] (M i) = ![1, 1, 1, c]

@[expose] def A11NbrBadA8Input :
    Prop :=
  GGInnerDiagMpInput → GGLBalanceInput → A11AMatInput → A11A8HomolInput → A11LemmaRInput → A11BadFixInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      StatedClassicalModel (K' ⧸ Subgroup.center K') .PSL 9 2 1 → ∀ c : ZMod 7,
      (c = 0 ∨ c = 3 ∨ c = 5 ∨ c = 6) → Subgroup.zpowers y' = Subgroup.zpowers (ell f c) → False

@[expose] def A11ReflFixInput : Prop :=
  A11AMatInput → A11LemmaRInput → A11BadFixInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' → GGReflGenerated 7 (ggAutomizer K' Bs) →
      ∀ c : ZMod 7, (c = 0 ∨ c = 3 ∨ c = 5 ∨ c = 6) → Subgroup.zpowers y' = Subgroup.zpowers (ell f c) →
      ∀ g ∈ K', g ∈ Subgroup.normalizer (Bs : Set G) → g * x * g⁻¹ = x

@[expose] def A11SylowSplitInput :
    Prop :=
  GGInnerDiagMpInput → GGLBalanceInput → GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      (GGHasLabel ⟨.A, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.C, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.twD, 4, 3⟩ (K' ⧸ Subgroup.center K')) →
      ∃ E : Subgroup G, E ≤ K' ∧ E ≤ Bs ∧ commutator ↥K' = ⊤ ∧ Nat.card E = 7 ^ 3 ∧
        ¬ 7 ^ 4 ∣ Nat.card K' ∧ Bs = Subgroup.zpowers y' ⊔ E ∧ y' ∉ E

@[expose] def A11NbrBadReflInput :
    Prop :=
  A11AMatInput → A11LemmaRInput → A11BadFixInput → A11ReflFixInput → A11SylowSplitInput →
  GGInnerDiagMpInput → GGLBalanceInput → GGLabelRigidInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' →
      (GGHasLabel ⟨.A, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.C, 3, 3⟩ (K' ⧸ Subgroup.center K') ∨
        GGHasLabel ⟨.twD, 4, 3⟩ (K' ⧸ Subgroup.center K')) →
      GGReflGenerated 7 (ggAutomizer K' Bs) → ∀ c : ZMod 7, (c = 0 ∨ c = 3 ∨ c = 5 ∨ c = 6) →
      Subgroup.zpowers y' = Subgroup.zpowers (ell f c) → False

@[expose] def A11NbrBadInput :
    Prop :=
  GGNbrTablePNbrInputOn GGRegimeA11 → GGLabelRigidInput → GGTCJKnown → GGNbrTableBWeylInput →
  GGNbrReflGenNonSplitInput →
  GGInnerDiagMpInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' → ∀ c : ZMod 7,
      (c = 0 ∨ c = 3 ∨ c = 5 ∨ c = 6) → Subgroup.zpowers y' = Subgroup.zpowers (ell f c) → False

theorem a11NbrBadInput_of_pieces
    (hLab : A11NbrLabelInput) (hRG : A11NbrReflGenInput) (hA8 : A11NbrBadA8Input)
    (hRf : A11NbrBadReflInput) (hAM : A11AMatInput) (hH : A11A8HomolInput) (hRF : A11ReflFixInput)
    (hSS : A11SylowSplitInput) (hLR : A11LemmaRInput) (hBF : A11BadFixInput) : A11NbrBadInput := by
  intro hTP hRig hTCJ hTB hNS hMp hLB G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb c hc hline
  have hlab := hLab hTP hRig hTCJ G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb
  rcases hlab with h8 | h3
  · exact hA8 hMp hLB hAM hH hLR hBF G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb h8 c hc hline
  · exact hRf hAM hLR hBF hRF hSS hMp hLB hRig G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb h3
      (hRG hTB hNS hRig hMp hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb h3) c hc hline

@[expose] def A11NbrInput' :
    Prop :=
  GGNbrTablePNbrInputOn GGRegimeA11 → GGLabelRigidInput → GGTCJKnown → GGNbrTableBWeylInput →
  GGNbrReflGenNonSplitInput →
  GGInnerDiagMpInput → GGLBalanceInput →
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G)
    (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
    (ρ : Equiv.Perm (Fin 12) →* G), A11Ctx B Bs x L D J y K φ₃ f n Φ ρ →
    ∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' → K' ≤ Clos φ₃ ρ

theorem a11NbrInput'_of_pieces
    (hLine : A11NbrLineInput) (hInf : A11NbrInftyInput)
    (hFrob : A11NbrFrobInput) (hBad : A11NbrBadInput) : A11NbrInput' := by
  intro hTP hRig hTCJ hTB hNS hMp hLB G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb
  rcases hLine G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb with h | ⟨c, hc, h⟩
  · have hKK : K' = K := hInf hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb h
    obtain ⟨-, -, ⟨-, hφ₃K, -⟩, -, ⟨hΦ3, -, -, -, -⟩, ⟨-, hClos, -⟩⟩ := hctx
    rw [hKK, ← hφ₃K]
    simpa only [hΦ3] using hClos 3
  · have hc7 : ∀ c : ZMod 7, c ≠ 1 → c = 0 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 := by decide
    rcases hc7 c hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hBad hTP hRig hTCJ hTB hNS hMp hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb 0
        (Or.inl rfl) h).elim
    · exact hFrob hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb 2 (Or.inl rfl) h
    · exact (hBad hTP hRig hTCJ hTB hNS hMp hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb 3
        (Or.inr (Or.inl rfl)) h).elim
    · exact hFrob hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb 4 (Or.inr rfl) h
    · exact (hBad hTP hRig hTCJ hTB hNS hMp hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb 5
        (Or.inr (Or.inr (Or.inl rfl))) h).elim
    · exact (hBad hTP hRig hTCJ hTB hNS hMp hLB G B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb 6
        (Or.inr (Or.inr (Or.inr rfl))) h).elim

end CFSG.StandardType.A11

end
