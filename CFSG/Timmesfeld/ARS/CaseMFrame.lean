module

public import CFSG.Timmesfeld.ARS.InductionMax

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal CFSG.Blueprint CFSG.Timmesfeld
open CFSG.Assembly.LowTwoRank

@[expose] def IsCTFrame {K : Type} [Group K] (D : UniversalRootDatum K) (H : Type) [Group H]
    (ψ : ∀ γ, D.rootGroup γ → H) : Prop :=
  (∀ i j, ∀ α ∈ pairRoots D i j, ∀ β ∈ pairRoots D i j, ¬ Universal.IsNegMultiple α β →
      ExtendsToHom D.rootGroup (D.cone α β ∩ pairRoots D i j) ψ) ∧
    (∀ k, ExtendsToHom D.rootGroup {Pi.single k 1, -Pi.single k 1} ψ) ∧
    Subgroup.closure (⋃ k, Set.range (ψ (Pi.single k 1)) ∪ Set.range (ψ (-Pi.single k 1))) = ⊤ ∧
    ∃ k, ∃ x, ψ (Pi.single k 1) x ≠ 1

theorem IsCTFrame.lieModel {K : Type} [Group K] {D : UniversalRootDatum K} {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    {H : Type} [Group H] (hZ : Subgroup.center H = ⊥) {ψ : ∀ γ, D.rootGroup γ → H}
    (h : IsCTFrame D H ψ) : LieModel H t n p f :=
  lieModel_of_frame hCT hL hZ ψ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem IsCTFrame.nslFrame {K : Type} [Group K] {D : UniversalRootDatum K} [hc : NSLConcrete D]
    {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    {nw : Fin D.rank → K} {T : Fin D.rank → Subgroup K}
    (hct : CurtisTits.IsCTGroupDatum (RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup nw T)
    (hext : SteinbergExtras D nw T) (hdiv : D.divisible = ∅) {i₀ : Fin D.rank}
    (htype : NSLType D.rank D.cartan i₀) (hpg : ∀ γ ∈ D.roots, IsPGroup 2 ↥(D.rootGroup γ))
    (hcomm : D.cartan = Symplectic.cartanC D.rank → ∀ i j, D.cartan i j = -2 →
      Commuting (D.rootGroup (Pi.single i 1)) (D.rootGroup (Pi.single i 1 + Pi.single j 1)))
    {G : Type} [Group G] {R : Set (Subgroup G)} {ψ : ∀ γ, D.rootGroup γ → G}
    (h : IsCTFrame D G ψ) {X Y : Subgroup G} (hX : X ∈ R)
    (hXψ : (X : Set G) = Set.range (ψ (Pi.single i₀ 1)))
    (hYψ : (Y : Set G) = Set.range (ψ (-Pi.single i₀ 1))) (hXY : Opposite X Y) :
    NSLFrame G R := by
  obtain ⟨Ψ, hΨ₁, hΨ₂, hsurj, hker, -⟩ :=
    exists_surjective_of_frame hCT hL ψ h.1 h.2.1 h.2.2.1 h.2.2.2
  have hmap : ∀ γ, (∀ x : D.rootGroup γ, Ψ x = ψ γ x) → ∀ Z : Subgroup G,
      (Z : Set G) = Set.range (ψ γ) → (D.rootGroup γ).map Ψ = Z := by
    intro γ hγ Z hZ
    refine SetLike.coe_injective ?_
    rw [Subgroup.coe_map, hZ]
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hγ ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, hγ x⟩
  have h₁ := hmap _ (hΨ₁ i₀) X hXψ
  have h₂ := hmap _ (hΨ₂ i₀) Y hYψ
  exact ⟨NSLFrameData.mk K D nw T hct hext hdiv i₀ htype hpg Ψ hsurj hker (by rw [h₁]; exact hX)
    (by rw [h₁, h₂]; exact hXY) hcomm hc⟩

theorem isPGroup_rootGroup_f4Datum (K : Type) [Field K] [CharP K 2]
    {γ : Fin (Adjoint.f4Datum K).rank → ℤ} (hγ : γ ∈ (Adjoint.f4Datum K).roots) :
    IsPGroup 2 ((Adjoint.f4Datum K).rootGroup γ) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨c, hc⟩ := (Adjoint.mem_rootGroup_iff (Adjoint.mem_adjDatum_roots.1 hγ) x.1).1 x.2
  rw [pow_one, Subgroup.coe_pow, ← hc, sq, ← Adjoint.xPar_add, CharTwo.add_self_eq_zero,
    Adjoint.xPar_zero]
  rfl

theorem isPGroup_rootGroup_twistedE6Datum {k : Type*} [Field k] [CharP k 2] (θ : k →+* k)
    {β : Fin (TwistedE6.twistedDatum k θ).rank → ℤ}
    (hβ : β ∈ (TwistedE6.twistedDatum k θ).roots) :
    IsPGroup 2 ((TwistedE6.twistedDatum k θ).rootGroup β) := by
  obtain ⟨α, hα, hp⟩ :=
    TwistedE6.exists_proj_eq (TwistedE6.isRoot_of_mem_twistedDatum_roots θ hβ)
  have key : ∀ g ∈ Minuscule.e6Data_valid.rootGroup k α ⊔
      Minuscule.e6Data_valid.rootGroup k (TwistedE6.rho α), g ^ 2 = 1 := by
    intro g hg
    by_cases hfix : TwistedE6.rho α = α
    · rw [hfix, sup_idem] at hg
      obtain ⟨c, rfl⟩ := (Minuscule.e6Data_valid.mem_rootGroup k).1 hg
      rw [sq, ← Minuscule.e6Data_valid.xm_add, CharTwo.add_self_eq_zero,
        Minuscule.e6Data_valid.xm_zero]
    · obtain ⟨c, d, rfl⟩ :=
        (TwistedE6.mem_sup_rootGroup_of_commute (TwistedE6.commute_xm_rho hα hfix)).1 hg
      have hcd := (TwistedE6.commute_xm_rho (k := k) hα hfix c d).eq
      calc (Minuscule.e6Data_valid.xm k α c *
            Minuscule.e6Data_valid.xm k (TwistedE6.rho α) d) ^ 2
          = Minuscule.e6Data_valid.xm k α c * (Minuscule.e6Data_valid.xm k (TwistedE6.rho α) d *
              Minuscule.e6Data_valid.xm k α c) *
                Minuscule.e6Data_valid.xm k (TwistedE6.rho α) d := by
            rw [sq]; simp only [mul_assoc]
        _ = Minuscule.e6Data_valid.xm k α (c + c) *
              Minuscule.e6Data_valid.xm k (TwistedE6.rho α) (d + d) := by
            rw [← hcd, Minuscule.e6Data_valid.xm_add, Minuscule.e6Data_valid.xm_add]; group
        _ = 1 := by
            rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
              Minuscule.e6Data_valid.xm_zero, Minuscule.e6Data_valid.xm_zero, mul_one]
  intro x
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  have hx := (TwistedE6.mem_twistedRootGroup_iff θ hα hp x.1).1 x.2
  simpa [pow_one] using key _ hx

private theorem cartan_F4_ne_cartanC : CFSG.Blueprint.Chevalley.Tag.cartan .F4 ≠
    Symplectic.cartanC (CFSG.Blueprint.Chevalley.Tag.rank .F4) :=
  fun h => absurd (congrFun (congrFun h ⟨2, by decide⟩) ⟨1, by decide⟩) (by decide)

theorem IsCTFrame.nslFrame_f4 {G : Type} [Group G] {R : Set (Subgroup G)} {f : ℕ} (hf : 1 ≤ f)
    {ψ : ∀ γ, (Adjoint.f4Datum (GaloisField 2 f)).rootGroup γ → G}
    (h : IsCTFrame (Adjoint.f4Datum (GaloisField 2 f)) G ψ)
    (i₀ : Fin (Adjoint.f4Datum (GaloisField 2 f)).rank) (hi₀ : i₀.val < 2) {X Y : Subgroup G}
    (hX : X ∈ R)
    (hXψ : (X : Set G) = Set.range (ψ (Pi.single i₀ 1)))
    (hYψ : (Y : Set G) = Set.range (ψ (-Pi.single i₀ 1))) (hXY : Opposite X Y) :
    NSLFrame G R :=
  have hadm : StatedLieAdmissible .F4 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  h.nslFrame (CurtisTits.curtisTitsConclusion_f4 2 f hadm) (leviConePresented_f4 _)
    (Adjoint.f4_isCTGroupDatum _) (Adjoint.f4_steinbergExtras _) rfl (NSLType.f4Datum _ i₀ hi₀)
    (fun _ hγ => isPGroup_rootGroup_f4Datum _ hγ) (fun hC => absurd hC cartan_F4_ne_cartanC) hX
    hXψ hYψ hXY

theorem IsCTFrame.nslFrame_twistedE6 {G : Type} [Group G] {R : Set (Subgroup G)} {f : ℕ}
    (hf : 1 ≤ f) {ψ : ∀ γ, (Exceptional.twistedE6Datum 2 f).rootGroup γ → G}
    (h : IsCTFrame (Exceptional.twistedE6Datum 2 f) G ψ)
    (i₀ : Fin (Exceptional.twistedE6Datum 2 f).rank) (hi₀ : i₀.val < 2) {X Y : Subgroup G}
    (hX : X ∈ R)
    (hXψ : (X : Set G) = Set.range (ψ (Pi.single i₀ 1)))
    (hYψ : (Y : Set G) = Set.range (ψ (-Pi.single i₀ 1))) (hXY : Opposite X Y) :
    NSLFrame G R :=
  have : Fact (1 ≤ f) := ⟨hf⟩
  have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  have hθ := Exceptional.frobQ_frobQ 2 f hf
  h.nslFrame (CurtisTits.curtisTitsConclusion_twistedE6 2 f hadm)
    (leviConePresented_twistedE6 2 f hf)
    (TwistedE6.twistedDatum_isCTGroupDatum _ hθ (TwistedE6.iSup_twistedDatum_rootGroup _ hθ))
    (TwistedE6.twistedDatum_steinbergExtras _ hθ) rfl (NSLType.twistedE6Datum _ _ i₀ hi₀)
    (fun _ hγ => isPGroup_rootGroup_twistedE6Datum _ hγ)
    (fun hC => absurd hC cartan_F4_ne_cartanC) hX hXψ hYψ hXY

@[expose] def F4Frame (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ ψ : ∀ γ, (Adjoint.f4Datum (GaloisField 2 f)).rootGroup γ → G,
    IsCTFrame (Adjoint.f4Datum (GaloisField 2 f)) G ψ

@[expose] def TwistedE6Frame (G : Type) [Group G] (f : ℕ) : Prop :=
  ∃ ψ : ∀ γ, (Exceptional.twistedE6Datum 2 f).rootGroup γ → G,
    IsCTFrame (Exceptional.twistedE6Datum 2 f) G ψ

theorem nonSimplyLacedOutcome_of_F4Frame {G : Type} [Group G] (hZ : Subgroup.center G = ⊥)
    {f : ℕ} (hf : 1 ≤ f) (hG : F4Frame G f) : NonSimplyLacedOutcome G := by
  obtain ⟨ψ, hψ⟩ := hG
  have hadm : StatedLieAdmissible .F4 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  exact .inr (.inr (.inr (.inl ⟨f, hf, .F4, by decide,
    hψ.lieModel (CurtisTits.curtisTitsConclusion_f4 2 f hadm) (leviConePresented_f4 _) hZ⟩)))

theorem nonSimplyLacedOutcome_of_twistedE6Frame {G : Type} [Group G]
    (hZ : Subgroup.center G = ⊥) {f : ℕ} (hf : 1 ≤ f) (hG : TwistedE6Frame G f) :
    NonSimplyLacedOutcome G := by
  obtain ⟨ψ, hψ⟩ := hG
  have hadm : StatedLieAdmissible .twistedE6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  exact .inr (.inr (.inr (.inl ⟨f, hf, .twistedE6, by decide,
    hψ.lieModel (CurtisTits.curtisTitsConclusion_twistedE6 2 f hadm)
      (leviConePresented_twistedE6 2 f hf) hZ⟩)))

@[expose] def CaseMFrameInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), Hyp G R → ∀ A ∈ R,
    IsCoatom (Subgroup.normalizer (A : Set G)) → sigmaSet R A ≠ lambdaSet R A →
      IsSigmaMaximal R (centralGroup R A) → ∀ A₀ ∈ omegaSet R A,
        Nat.card (leviComps R A A₀) = 1 →
          (∀ X ∈ leviSet R A A₀, ∀ Y ∈ leviSet R A A₀, ¬ Special R X Y) →
            ∃ f, 1 ≤ f ∧ Nat.card A = 2 ^ f ∧ (F4Frame G f ∨ TwistedE6Frame G f) ∧
              NSLFrame G R

theorem caseMStep_of_frameInput (hF : CaseMFrameInput) : CaseMStep := by
  intro G _ R h _ A hA hcoat hAne hmax A₀ hA₀ h1 hdeg
  obtain ⟨f, hf, -, hG | hG, hN⟩ := hF G R h A hA hcoat hAne hmax A₀ hA₀ h1 hdeg
  · exact Output.of_nonSimplyLaced (nonSimplyLacedOutcome_of_F4Frame h.center hf hG) (.inr hN)
  · exact Output.of_nonSimplyLaced (nonSimplyLacedOutcome_of_twistedE6Frame h.center hf hG)
      (.inr hN)

end CFSG.Timmesfeld.ARS
