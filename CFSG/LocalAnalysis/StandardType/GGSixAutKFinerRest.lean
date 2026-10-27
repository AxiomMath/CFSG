module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section HypParts

@[expose] def GGHypRestII (W : Type) [Group W] [Finite W] : Prop :=
  IsSimpleGroup ↥(CFSG.generalizedFitting W) ∧
    (∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a) ∧
    InCatalog ↥(CFSG.generalizedFitting W)

@[expose] def GGHypRestIII {W : Type} [Group W] [Finite W] (p : ℕ) (H E : Subgroup W) : Prop :=
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
          IsPGroup p ↥π.ker ∧ commutator Kh = ⊤ ∧ pRank p (⊤ : Subgroup Kh) = 2)

@[expose] def GGHypRestIVComponentwise {W : Type} [Group W] [Finite W] (p : ℕ) (E : Subgroup W) : Prop :=
  (∀ x ∈ E, x ≠ 1 → ∀ C : Subgroup W, LargeEvenPComponent p (Subgroup.centralizer {x}) C →
    CFSG.Assembly.IsQuasisimple ↥C ∧ LargeEvenMarking ↥C (fun _ _ _ _ _ _ => True))

@[expose] def GGHypRestIV {W : Type} [Group W] [Finite W] (p : ℕ) (E : Subgroup W) : Prop :=
  (∀ x ∈ E, x ≠ 1 →
    CFSG.Assembly.IsQuasisimple ↥(LargeEvenPLayer p (Subgroup.centralizer {x})) ∨
      LargeEvenPLayer p (Subgroup.centralizer {x}) = ⊥) ∧
    GGHypRestIVComponentwise p E

theorem ggHypRestIV_componentwise {W : Type} [Group W] [Finite W] {p : ℕ}
    {E : Subgroup W} (hypothesis : GGHypRestIV p E) : GGHypRestIVComponentwise p E :=
  hypothesis.2

theorem ggHypThreeSixteenRest_of_parts {W : Type} [Group W] [Finite W] {p : ℕ}
    {H E : Subgroup W} (h2 : GGHypRestII W) (h3 : GGHypRestIII p H E) (h4 : GGHypRestIV p E) :
    GGHypThreeSixteenRest p H E :=
  ⟨h2, h3.1, h3.2.1, h3.2.2.1, h3.2.2.2.1, h3.2.2.2.2, h4⟩

end HypParts

section Quotient

variable {G : Type} [Group G]

@[expose] noncomputable def ggAutKV (D K M : Subgroup G) (m : G) : Subgroup G :=
  ggAutKH D K M m ⊓ Subgroup.centralizer (K : Set G)

theorem ggAutKV_normal {D K M : Subgroup G} {m : G}
    (hEK : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G)) :
    ((ggAutKV D K M m).subgroupOf (ggAutKW D K m)).Normal := by
  set E₀ := D.map (MulAut.conj m⁻¹).toMonoidHom with hE₀
  have hVW : ggAutKV D K M m ≤ ggAutKW D K m := fun v hv =>
    (sup_le_sup_left inf_le_left E₀ : E₀ ⊔ (K ⊓ M) ≤ E₀ ⊔ K) (Subgroup.mem_inf.mp hv).1
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVW]
  have fwdE : ∀ e ∈ E₀, ∀ v ∈ ggAutKV D K M m, e * v * e⁻¹ ∈ ggAutKV D K M m := by
    intro e he v hv
    obtain ⟨hvH, hvC⟩ := Subgroup.mem_inf.mp hv
    have heH : e ∈ ggAutKH D K M m := (le_sup_left : E₀ ≤ E₀ ⊔ (K ⊓ M)) he
    refine Subgroup.mem_inf.mpr ⟨(ggAutKH D K M m).mul_mem
      ((ggAutKH D K M m).mul_mem heH hvH) ((ggAutKH D K M m).inv_mem heH), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : e⁻¹ * k * e ∈ K := by
      have h0 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (K : Set G)).inv_mem (hEK he)) k).mp hk
      simpa using h0
    have h := Subgroup.mem_centralizer_iff.mp hvC (e⁻¹ * k * e) hk'
    calc k * (e * v * e⁻¹) = e * ((e⁻¹ * k * e) * v) * e⁻¹ := by group
      _ = e * (v * (e⁻¹ * k * e)) * e⁻¹ := by rw [h]
      _ = e * v * e⁻¹ * k := by group
  have fwdK : ∀ k ∈ K, ∀ v ∈ ggAutKV D K M m, k * v * k⁻¹ ∈ ggAutKV D K M m := by
    intro k hk v hv
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 k hk
    rw [h, mul_inv_cancel_right]
    exact hv
  have hnorm : ∀ X : Subgroup G,
      (∀ g ∈ X, ∀ v ∈ ggAutKV D K M m, g * v * g⁻¹ ∈ ggAutKV D K M m) →
      X ≤ Subgroup.normalizer (ggAutKV D K M m : Set G) := by
    intro X hX g hg
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hX g hg v, fun hv => ?_⟩
    have h0 := hX g⁻¹ (X.inv_mem hg) _ hv
    simpa [mul_assoc] using h0
  exact sup_le (hnorm E₀ fwdE) (hnorm K fwdK)

@[expose] noncomputable def ggAutKPi (D K M : Subgroup G) (m : G)
    [((ggAutKV D K M m).subgroupOf (ggAutKW D K m)).Normal] :
    ↥(ggAutKW D K m) →* ↥(ggAutKW D K m) ⧸ (ggAutKV D K M m).subgroupOf (ggAutKW D K m) :=
  QuotientGroup.mk' _

@[expose] def GGAutKConjConfig [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (b : G) (L₁ K : Subgroup G) (m : G) : Prop :=
  b ∈ Bs ∧ b ≠ 1 ∧ IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
    IsComponentOf K (Subgroup.centralizer {b}) ∧ L₁ ≤ K ∧ ¬ K ≤ ggM p B x L D J ∧
    m ∈ ggM p B x L D J ∧ D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b}

end Quotient

section Inputs

@[expose] def GGAutKCanonIIInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestII
          (↥(ggAutKW D K m) ⧸ (ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m))

@[expose] def GGAutKCanonIIIInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestIII p
          (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))
          (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))

@[expose] def GGAutKCanonIVInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestIV p
          (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))

theorem ggSixAutKHypRestAtInput_of_canon (h2 : GGAutKCanonIIInput) (h3 : GGAutKCanonIIIInput)
    (h4 : GGAutKCanonIVInput) : GGSixAutKHypRestAtInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b hb hb1 L₁ hL₁ K hK hLK hKM m hm hEC
  have hcfg : GGAutKConjConfig p B Bs x L D J b L₁ K m := ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1 (ggStepTwo_centralizer_ne_top hctx.1.2.1 hb1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hN := ggAutKV_normal (M := ggM p B x L D J) hnorm
  refine ⟨_, inferInstance, inferInstance, ggAutKPi D K (ggM p B x L D J) m,
    QuotientGroup.mk'_surjective _, ?_, ggHypThreeSixteenRest_of_parts
      (h2 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg)
      (h3 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg)
      (h4 G p B Bs x L D J t n f ψ hctx s1 b L₁ K m hcfg)⟩
  intro w hw
  rw [ggAutKPi, QuotientGroup.ker_mk'] at hw
  exact hw

end Inputs

end CFSG.StandardType
