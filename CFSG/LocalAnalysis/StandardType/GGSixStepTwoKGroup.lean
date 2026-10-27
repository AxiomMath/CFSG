module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section HypDefs

variable {W : Type} [Group W]

abbrev GGHypQuot (H : Subgroup W) : Type := ↥H ⧸ CFSG.pCore 2 ↥H

@[expose] noncomputable def ggHypLayer (H : Subgroup W) : Subgroup W :=
  ((LargeEvenLayer (⊤ : Subgroup (GGHypQuot H))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

@[expose] noncomputable def ggHypImage (H E : Subgroup W) : Subgroup (GGHypQuot H) :=
  (E.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

@[expose] def GGChevStTag (lab : LargeEvenLabel) : Prop :=
  lab.tag ≠ .twB2 ∧ lab.tag ≠ .twF4 ∧ lab.tag ≠ .twF4der

@[expose] def GGTwoConstrained (X : Type) [Group X] : Prop :=
  Subgroup.centralizer (CFSG.pCore 2 (X ⧸ oddCore X) : Set (X ⧸ oddCore X)) ≤
    CFSG.pCore 2 (X ⧸ oddCore X)

@[expose] def GGHypThreeSixteenRest [Finite W] (p : ℕ) (H E : Subgroup W) : Prop :=
  (IsSimpleGroup ↥(CFSG.generalizedFitting W) ∧
    (∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a) ∧
    InCatalog ↥(CFSG.generalizedFitting W)) ∧
  (∀ C : Subgroup (GGHypQuot H), IsComponentOf C ⊤ →
    ggHypImage H E ≤ Subgroup.normalizer (C : Set (GGHypQuot H)) ∧
      LargeEvenMarking ↥C (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ e ∈ ggHypImage H E, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GGHypQuot H) = e⁻¹ * l * e) φ)) ∧
  (commutator ↥(ggHypLayer H) = ⊤ ∨ LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥) ∧
  (∃ k : ℕ, derivedSeries ↥H k ≤ (ggHypLayer H).subgroupOf H) ∧
  (LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥ →
    GGTwoConstrained ↥(ggHypLayer H) ∨
      (CFSG.Assembly.IsQuasisimple ↥(ggHypLayer H) ∧
        Odd (Nat.card (Subgroup.center ↥(ggHypLayer H))))) ∧
  (LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) = ⊥ →
    pRank p (⊤ : Subgroup ↥(CFSG.generalizedFitting W)) = 1 ∨
      ∃ (Kh : Type) (_ : Group Kh) (_ : Finite Kh) (π : Kh →* ↥(CFSG.generalizedFitting W)),
        Function.Surjective π ∧ π.ker ≤ Subgroup.center Kh ∧ IsCyclic ↥π.ker ∧
          IsPGroup p ↥π.ker ∧ commutator Kh = ⊤ ∧ pRank p (⊤ : Subgroup Kh) = 2) ∧
  ((∀ x ∈ E, x ≠ 1 →
    CFSG.Assembly.IsQuasisimple ↥(LargeEvenPLayer p (Subgroup.centralizer {x})) ∨
      LargeEvenPLayer p (Subgroup.centralizer {x}) = ⊥) ∧
    (∀ x ∈ E, x ≠ 1 → ∀ C : Subgroup W, LargeEvenPComponent p (Subgroup.centralizer {x}) C →
      CFSG.Assembly.IsQuasisimple ↥C ∧ LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True)))

@[expose] def GGHypThreeSixteen [Finite W] (p : ℕ) (H E : Subgroup W) : Prop :=
  (p.Prime ∧ p ≠ 2 ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ GGControlsStrongFusion H E) ∧
    GGHypThreeSixteenRest p H E

@[expose] def GGFusionException [Finite W] (p : ℕ) (H E : Subgroup W) : Prop :=
  (p = 3 ∧ Nonempty (↥(CFSG.generalizedFitting W) ≃* alternatingGroup (Fin 6)) ∧
    ∀ C : Subgroup W, ¬ IsComponentOf C (H ⊓ CFSG.generalizedFitting W)) ∨
  (p = 5 ∧ (∃ s : ℕ, 2 ≤ s ∧ s ≤ 4 ∧
      Nonempty (↥(CFSG.generalizedFitting W) ≃* alternatingGroup (Fin (5 * s)))) ∧
    ∀ C : Subgroup W, IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃* alternatingGroup (Fin 5))) ∨
  (IsPGroup p ↥(CFSG.generalizedFitting W ⊓ Subgroup.centralizer (E : Set W)) ∧
    ((p = 3 ∧ LieModel ↥(CFSG.generalizedFitting W) .PSp 4 2 1 ∧
        ∀ C : Subgroup W, IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
          LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1) ∨
      (p = 3 ∧ LieModel ↥(CFSG.generalizedFitting W) .PSp 3 2 1 ∧
        ∀ C : Subgroup W, IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
          LieModel (↥C ⧸ Subgroup.center ↥C) .PSU 4 2 1) ∨
      (p = 3 ∧ LieModel ↥(CFSG.generalizedFitting W) .PSL 3 2 2 ∧
        ∀ C : Subgroup W, IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
          Nonempty (↥C ⧸ Subgroup.center ↥C ≃* alternatingGroup (Fin 6))) ∨
      (p = 5 ∧ LieModel ↥(CFSG.generalizedFitting W) .twistedB2 0 2 5 ∧
        ∀ C : Subgroup W, ¬ IsComponentOf C (H ⊓ CFSG.generalizedFitting W)) ∨
      (p = 3 ∧ LieModel ↥(CFSG.generalizedFitting W) .PSL 2 2 3 ∧
        ∀ C : Subgroup W, ¬ IsComponentOf C (H ⊓ CFSG.generalizedFitting W)))) ∨
  (p = 5 ∧ Nonempty (↥(CFSG.generalizedFitting W) ≃* TauCeti.SporadicName.Fi22.Group) ∧
    ∀ C : Subgroup W, IsComponentOf C (H ⊓ CFSG.generalizedFitting W) →
      LieModel (↥C ⧸ Subgroup.center ↥C) .POmegaPlus 4 2 1)

end HypDefs

@[expose] def GGKGroupFusionLegacyUnrestrictedInput : Prop :=
  ∀ (W : Type) [Group W] [Finite W] (p : ℕ) (H E : Subgroup W),
    GGHypThreeSixteen p H E → H = ⊤ ∨ GGFusionException p H E

section AutK

variable {G : Type} [Group G]

@[expose] noncomputable def ggAutKW (D K : Subgroup G) (m : G) : Subgroup G :=
  D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ K

@[expose] noncomputable def ggAutKH (D K M : Subgroup G) (m : G) : Subgroup G :=
  D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ (K ⊓ M)

theorem ggAutK_le_of_map_eq_top {W₀ H₀ : Subgroup G} {W' : Type} [Group W'] (π : ↥W₀ →* W')
    (hker : π.ker ≤ H₀.subgroupOf W₀) (htop : (H₀.subgroupOf W₀).map π = ⊤) : W₀ ≤ H₀ := by
  intro w hw
  have hmem : π ⟨w, hw⟩ ∈ (H₀.subgroupOf W₀).map π := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hπh⟩ := Subgroup.mem_map.mp hmem
  have hk : h⁻¹ * ⟨w, hw⟩ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπh, inv_mul_cancel]
  have h' := Subgroup.mul_mem _ hh (hker hk)
  rw [mul_inv_cancel_left, Subgroup.mem_subgroupOf] at h'
  exact h'

end AutK

section Inputs

@[expose] def GGStepTwoAutKInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J →
        ∃ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
          ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(ggAutKW D K m) →* W'),
            Function.Surjective π ∧
            π.ker ≤ (ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m) ∧
            GGHypThreeSixteen p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π) ∧
            ¬ GGFusionException p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

theorem ggStepTwoComponentInput_of_kgroup (hKF : GGKGroupFusionLegacyUnrestrictedInput)
    (hV : GGStepTwoAutKInput) : GGStepTwoComponentInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK
  by_contra hKM
  obtain ⟨m, hm, -, W', _, _, π, -, hker, hhyp, hexc⟩ :=
    hV G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM
  rcases hKF W' p _ _ hhyp with htop | hex
  · apply hKM
    obtain ⟨⟨hBBs, -, -⟩, ⟨⟨hDB, -⟩, -⟩, -, -, -, ⟨hBsM, -⟩, -⟩ := hctx.2
    have hEM : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggM p B x L D J := by
      rintro _ ⟨d, hd, rfl⟩
      have h' := (ggM p B x L D J).mul_mem ((ggM p B x L D J).mul_mem
        ((ggM p B x L D J).inv_mem hm) (hBsM (hBBs (hDB hd)))) hm
      simpa [MulAut.conj_apply] using h'
    exact (le_sup_right.trans (ggAutK_le_of_map_eq_top π hker htop)).trans
      (sup_le hEM inf_le_right)
  · exact hexc hex

theorem ggSixStepTwoV2Input_of_kgroup (hfus : GGStepTwoBstarFusionInput)
    (hA : GGStepTwoLinearFusionInput) (h314 : GGLemmaThreeFourteenInput)
    (hKF : GGKGroupFusionLegacyUnrestrictedInput) (hV : GGStepTwoAutKInput) (h615 : GGStepTwoCentralizerInput) :
    GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_split hfus hA h314 (ggStepTwoComponentInput_of_kgroup hKF hV) h615

end Inputs

end CFSG.StandardType
