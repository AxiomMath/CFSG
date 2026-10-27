module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6EnnModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Inn
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner937TwE6Center
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwE6ThreeSC

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Exceptional

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tw3m_congr_conj {S T : Type} [Group S] [Group T] (e : S ≃* T) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

private theorem tw3m_not_three_dvd_add_one {n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) :
    ¬ 3 ∣ 2 ^ n + 1 := by
  intro h
  have hsub : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
    have := Nat.one_le_two_pow (n := n)
    omega
  have hd : 3 ∣ 2 := by
    have := Nat.dvd_sub h h3
    rwa [hsub] at this
  norm_num at hd

private def tw3m_ModelAt
    (n : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ₀ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup 3 4 R I L' ψ₀ A →
      ∃ (Kf : Type) (_ : Field Kf) (_ : Finite Kf) (σ : Kf ≃+* Kf),
        Nat.card Kf = (2 ^ n) ^ 2 ∧ (∀ c, σ c = c ^ 2 ^ n) ∧
        ∃ (e : L' ≃* ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom))
          (E : Subgroup ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom)),
          IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E ∧
          (∀ g : ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom),
            (∀ b ∈ E, g * b = b * g) → g ^ 3 = 1 → g ∈ E) ∧
          A.map (MulAut.congr e).toMonoidHom =
            E.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom) →*
              MulAut ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom)) ∧
          Subgroup.center L' = ⊥

private theorem tw3m_modelAt_recipe
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : ¬ 3 ∣ 2 ^ n + 1) :
    tw3m_ModelAt n (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  classical
  intro L' _ _ ψ₀ A hA
  obtain ⟨hψ0, hker0, hperf0, hAe, hAI, hr, -, hsc⟩ := hA
  haveI : Finite (TwE6Delta.RecipeR K n) := TwE6Delta.finite_recipeR hK
  obtain ⟨hker1, hZL⟩ := ggTwE6_ker_center_recipe (n := n) hn hK h3 ψ₀ hψ0 hker0 hperf0
  have hψ₀inj : Function.Injective ψ₀ := (MonoidHom.ker_eq_bot_iff ψ₀).1 hker1
  have hInn : TwE6Delta.RecipeI K n ⊆
      Set.range (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)) :=
    TwE6Delta.recipeI_subset_inn_of_not_dvd (n := n) (by omega) hK h3
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hE₀ab, hcardE₀, hE₀A, hscE₀⟩ :=
    exists_innerModel_recipe_twE6 (p := 3) (n := n) (K := K) Nat.prime_three (by omega) hK
      (fun φ hφ _ => hInn hφ)
      (TwE6Delta.ggCenterPrime_three_twE6 (by omega) hK h3)
      ψ₀ hψ0 hker0 hperf0 hAe hAI hsc
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ (2 ^ n) := fun c => iterateFrobeniusEquiv_def K 2 n c
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (n := n) (by omega) hK σ.toRingHom hσ
  set E₀ : Subgroup (TwE6Delta.RecipeR K n) := A.comap Λ with hE₀
  let E : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := E₀.map e.toMonoidHom
  have hEab : IsElemAbelian 3 E := hE₀ab.map e.toMonoidHom
  have hcardE : Nat.card E = Nat.card A := by
    rw [Subgroup.card_map_of_injective e.injective, hcardE₀]
  have hscE : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (∀ b ∈ E, g * b = b * g) → g ^ 3 = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨g₀, rfl⟩ : ∃ g₀, e g₀ = g := ⟨e.symm g, e.apply_symm_apply g⟩
    refine Subgroup.mem_map_of_mem e.toMonoidHom (hscE₀ g₀ (fun b hb => ?_) ?_)
    · have h1 := hg (e b) (Subgroup.mem_map_of_mem e.toMonoidHom hb)
      exact e.injective (by rw [map_mul, map_mul]; exact h1)
    · exact e.injective (by rw [map_pow, hgp, map_one])
  let ψ : L' →* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := e.toMonoidHom.comp ψ₀
  have hψbij : Function.Bijective ψ := e.bijective.comp ⟨hψ₀inj, hψ0⟩
  let eL : L' ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    MulEquiv.ofBijective ψ hψbij
  have heL : ∀ x, eL x = e (ψ₀ x) := fun x => rfl
  have hcomp : (MulAut.congr eL).toMonoidHom.comp Λ =
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).comp e.toMonoidHom := by
    refine MonoidHom.ext fun r => MulEquiv.ext fun l' => ?_
    obtain ⟨l, rfl⟩ := eL.surjective l'
    change eL (Λ r (eL.symm (eL l))) = e r * eL l * (e r)⁻¹
    rw [MulEquiv.symm_apply_apply]
    simp only [heL, hΛmap, map_mul, map_inv]
  have hAE : A.map (MulAut.congr eL).toMonoidHom =
      E.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
    calc A.map (MulAut.congr eL).toMonoidHom
        = ((A.comap Λ).map Λ).map (MulAut.congr eL).toMonoidHom := by rw [hE₀A]
      _ = (A.comap Λ).map ((MulAut.congr eL).toMonoidHom.comp Λ) := Subgroup.map_map _ _ _
      _ = (A.comap Λ).map ((MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
            MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).comp e.toMonoidHom) := by
            rw [hcomp]
      _ = E.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
            MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
          (Subgroup.map_map _ _ _).symm
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσ, eL, E, hEab, by rw [hcardE]; exact hr,
    hscE, hAE, hZL⟩

private theorem tw3m_model_of_innerDiag
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hI : GGInnerDiagOn Bs X) {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ∣ 2 ^ n - 1)
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hX : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥X ⧸ Subgroup.center ↥X))
    (hcard : commutator ↥X = ⊤ → ∀ {R : Type} [Group R]
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* R) (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      GGTorusLift 3 4 R → 3 ^ 4 ≤ Nat.card ↥(ggGamma X hN).range) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (Kf : Type) (_ : Field Kf) (_ : Finite Kf)
      (σ : Kf ≃+* Kf) (_ : Nat.card Kf = (2 ^ n) ^ 2) (_ : ∀ c, σ c = c ^ 2 ^ n)
      (e : ↥X ≃* ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom))
      (E : Subgroup ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom)),
      Subgroup.center ↥X = ⊥ ∧ IsElemAbelian 3 E ∧ 3 ^ 4 ≤ Nat.card E ∧
      (∀ g : ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom),
        (∀ c ∈ E, g * c = c * g) → g ^ 3 = 1 → g ∈ E) ∧
      (ggGamma X hN).range.map (MulAut.congr e).toMonoidHom =
        E.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom) →*
          MulAut ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom)) := by
  classical
  have h3p : ¬ 3 ∣ 2 ^ n + 1 := tw3m_not_three_dvd_add_one h3
  have hmark := ggInnerDiagOn_relabel hRig hI hΛ hX
  have hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab = ⟨.twE6, 0, n⟩ →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        GGTorusLift 3 4 R ∧ tw3m_ModelAt n R I) := by
    intro lab hlab hlabeq
    subst hlabeq
    refine nbrC_labelAll_guard ?_
    have h1 : LargeEvenLabelAll (⟨.twE6, 0, n⟩ : LargeEvenLabel)
        (fun R _ _ _ => GGTorusLift 3 4 R) :=
      largeEvenLabelAll_torusLift_twE6Dvd Nat.prime_three (by norm_num) hlab ⟨rfl, h3⟩
    have h2 : LargeEvenLabelAll (⟨.twE6, 0, n⟩ : LargeEvenLabel)
        (fun R _ I _ => tw3m_ModelAt n R I) :=
      TwE6Delta.labelAll rfl fun K _ _ hK => tw3m_modelAt_recipe hn hK h3p
    exact largeEvenLabelAll_and h1 h2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => lab = (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (P' := fun R _ I _ => GGTorusLift 3 4 R ∧ tw3m_ModelAt n R I) hall
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, Fm, -, -, θ, ⟨-, hBsN, h3I⟩, hlift, hModel⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  have hr := hcard hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hXc θ hBsN hBsI hr
    (le_trans (by norm_num : 3 ^ 3 ≤ 3 ^ 4) hr)
  obtain ⟨Kf, _, _, σ, hK, hσ, e, E, hEab, h4E, hsc, hAE, hZ⟩ := hModel X (ggQuotHom θ) _ hTB
  exact ⟨hBsN, Kf, inferInstance, inferInstance, σ, hK, hσ, e, E, hZ, hEab, h4E, hsc, hAE⟩
private theorem tw3m_field_iso
    {Kf : Type} [Field Kf] [Finite Kf] {n : ℕ} (hn : 1 ≤ n)
    (hKc : Nat.card Kf = (2 ^ n) ^ 2) (σe : Kf ≃+* Kf) (hσe : ∀ c, σe c = c ^ 2 ^ n) :
    ∃ τ : GaloisField 2 (2 * n) ≃+* Kf,
      τ.toRingHom.comp (frobQ 2 n) = σe.toRingHom.comp τ.toRingHom ∧
      τ.symm.toRingHom.comp σe.toRingHom = (frobQ 2 n).comp τ.symm.toRingHom := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite (GaloisField 2 (2 * n))
  haveI : Fintype Kf := Fintype.ofFinite Kf
  have hFcard : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn
  have hcardτ : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card Kf := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hFcard, hKc]
  let τ : GaloisField 2 (2 * n) ≃+* Kf := FiniteField.ringEquivOfCardEq hcardτ
  have hτ : τ.toRingHom.comp (frobQ 2 n) = σe.toRingHom.comp τ.toRingHom := by
    ext c
    show τ (frobQ 2 n c) = σe (τ c)
    rw [frobQ_apply, map_pow]
    exact (hσe (τ c)).symm
  have hτ' : τ.symm.toRingHom.comp σe.toRingHom =
      (frobQ 2 n).comp τ.symm.toRingHom := by
    ext c
    show τ.symm (σe c) = frobQ 2 n (τ.symm c)
    rw [hσe, map_pow, frobQ_apply]
  exact ⟨τ, hτ, hτ'⟩

private theorem tw3m_commutator_graph_eq
    {Kf : Type} [Field Kf] [Finite Kf] {n : ℕ} (hn : 1 ≤ n)
    (hKc : Nat.card Kf = (2 ^ n) ^ 2) (σ : Kf →+* Kf) (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    ⁅twistedFixedGroup .E6 Kf σ, twistedFixedGroup .E6 Kf σ⁆ =
      graphFixedRootGroup TwistTag.E6 Kf σ :=
  (finite_fixed_root_group_perfect .E6 Nat.prime_two hn Kf hKc σ hσ).2.2.1

private theorem tw3m_nonempty_equiv
    {Kf : Type} [Field Kf] [Finite Kf] {n : ℕ} (hn : 1 ≤ n)
    (hKc : Nat.card Kf = (2 ^ n) ^ 2) (σe : Kf ≃+* Kf) (hσe : ∀ c, σe c = c ^ 2 ^ n) :
    Nonempty (↥(graphFixedRootGroup TwistTag.E6 Kf σe.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n)) (frobQ 2 n))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcard : Nat.card (GaloisField 2 (2 * n)) = (2 ^ n) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn
  obtain ⟨τ, hτ, hτ'⟩ := tw3m_field_iso hn hKc σe hσe
  have hΓK := tw3m_commutator_graph_eq hn hKc σe.toRingHom hσe
  have hΓF := tw3m_commutator_graph_eq hn hFcard (frobQ 2 n) (fun c => frobQ_apply 2 n c)
  exact ⟨(MulEquiv.subgroupCongr hΓK.symm).trans
    ((MpStdTwE6.derivedEquiv τ hτ hτ' .E6).symm.trans (MulEquiv.subgroupCongr hΓF))⟩

private theorem tw3m_transport_props
    {R1 R2 : Type} [Group R1] [Group R2]
    (φ : R1 ≃* R2) (E0 : Subgroup R1) (hEab : IsElemAbelian 3 E0)
    (h4E : 3 ^ 4 ≤ Nat.card E0)
    (hsc : ∀ g : R1, (∀ b ∈ E0, g * b = b * g) → g ^ 3 = 1 → g ∈ E0) :
    IsElemAbelian 3 (E0.map φ.toMonoidHom) ∧ 3 ^ 4 ≤ Nat.card (E0.map φ.toMonoidHom) ∧
      (∀ g : R2, g ∈ Subgroup.centralizer (E0.map φ.toMonoidHom : Set R2) → g ^ 3 = 1 →
        g ∈ E0.map φ.toMonoidHom) := by
  refine ⟨hEab.map φ.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective]
    exact h4E
  · intro g hg hg3
    obtain ⟨g0, rfl⟩ := φ.surjective g
    refine Subgroup.mem_map_of_mem φ.toMonoidHom (hsc g0 (fun b hb => ?_) ?_)
    · have h1 := (Subgroup.mem_centralizer_iff.mp hg) (φ b)
        (Subgroup.mem_map_of_mem φ.toMonoidHom hb)
      exact φ.injective (by rw [map_mul, map_mul]; exact h1.symm)
    · exact φ.injective (by rw [map_pow, hg3, map_one])

private theorem tw3m_frame_eq
    {n : ℕ} (hn : 1 ≤ n) (h3p : ¬ 3 ∣ 2 ^ n + 1)
    {ζ : (GaloisField 2 (2 * n))ˣ} (hζ : ζ ^ 3 = 1)
    (hζσ : frobQ 2 n (ζ : GaloisField 2 (2 * n)) = ζ) :
    ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ =
      ExcFrames.twE6ThreeFrameHom (f := n) (by omega) h3p ζ hζ := by
  refine MonoidHom.ext fun s => Subtype.ext ?_
  rfl

private theorem tw3m_conj_to_frame
    {n : ℕ} (hn : 1 ≤ n) (h3p : ¬ 3 ∣ 2 ^ n + 1)
    {ζ : (GaloisField 2 (2 * n))ˣ} (hζ : ζ ^ 3 = 1)
    (hζσ : frobQ 2 n (ζ : GaloisField 2 (2 * n)) = ζ) (hζo : orderOf ζ = 3)
    {E : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n)) (frobQ 2 n))}
    (hEab : IsElemAbelian 3 E) (h4E : 3 ^ 4 ≤ Nat.card E)
    (hscE : ∀ g ∈ Subgroup.centralizer (E : Set _), g ^ 3 = 1 → g ∈ E) :
    ∃ c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n)) (frobQ 2 n)),
      E.map (MulAut.conj c⁻¹).toMonoidHom =
        (ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ).range := by
  obtain ⟨c, hc⟩ := ExcFrames.twistedE6ThreeSCReference_holds (f := n) (by omega) h3p hζo
    hζ hEab h4E hscE
  refine ⟨c, ?_⟩
  have hframe : (ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ).range =
      (ExcFrames.twE6ThreeFrameHom (f := n) (by omega) h3p ζ hζ).range := by
    rw [tw3m_frame_eq hn h3p hζ hζσ]
  rw [hframe, hc, Subgroup.map_map]
  have hcc : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
      MonoidHom.id _ := by
    refine MonoidHom.ext fun x => ?_
    show MulAut.conj c⁻¹ (MulAut.conj c x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group
  rw [hcc, Subgroup.map_id]

private theorem tw3m_map_conj_map
    {R1 R2 : Type} [Group R1] [Group R2]
    (φ : R1 ≃* R2) (E0 : Subgroup R1) :
    (E0.map (MulAut.conj : R1 →* MulAut R1)).map (MulAut.congr φ).toMonoidHom =
      (E0.map φ.toMonoidHom).map (MulAut.conj : R2 →* MulAut R2) := by
  have hmm : (MulAut.congr φ).toMonoidHom.comp (MulAut.conj : R1 →* MulAut R1) =
      (MulAut.conj : R2 →* MulAut R2).comp φ.toMonoidHom :=
    MonoidHom.ext fun x => tw3m_congr_conj φ x
  rw [Subgroup.map_map, hmm, Subgroup.map_map]

private theorem tw3m_congr_map_conj
    {Kg R1 R2 : Type} [Group Kg] [Group R1] [Group R2]
    (Γ : Subgroup (MulAut Kg)) (e0 : Kg ≃* R1) (φ : R1 ≃* R2) (E0 : Subgroup R1)
    (hAE0 : Γ.map (MulAut.congr e0).toMonoidHom =
      E0.map (MulAut.conj : R1 →* MulAut R1)) :
    Γ.map (MulAut.congr (e0.trans φ)).toMonoidHom =
      (E0.map φ.toMonoidHom).map (MulAut.conj : R2 →* MulAut R2) := by
  have hcomp : MulAut.congr (e0.trans φ) = (MulAut.congr e0).trans (MulAut.congr φ) :=
      by
    apply MulEquiv.ext
    intro x
    apply MulEquiv.ext
    intro y
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hhom : ((MulAut.congr e0).trans (MulAut.congr φ)).toMonoidHom =
      (MulAut.congr φ).toMonoidHom.comp (MulAut.congr e0).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, hhom, ← Subgroup.map_map, hAE0]
  exact tw3m_map_conj_map φ E0

private theorem tw3m_congr_assemble
    {Kg R : Type} [Group Kg] [Group R]
    (Γ : Subgroup (MulAut Kg)) (e1 : Kg ≃* R) (E : Subgroup R) (c : R)
    (A : Subgroup R)
    (h1 : Γ.map (MulAut.congr e1).toMonoidHom = E.map (MulAut.conj : R →* MulAut R))
    (h2 : E.map (MulAut.conj c⁻¹).toMonoidHom = A) :
    Γ.map (MulAut.congr (e1.trans (MulAut.conj c⁻¹))).toMonoidHom =
      A.map (MulAut.conj : R →* MulAut R) := by
  have hcomp : MulAut.congr (e1.trans (MulAut.conj c⁻¹)) =
      (MulAut.congr e1).trans (MulAut.congr (MulAut.conj c⁻¹)) := by
    apply MulEquiv.ext
    intro x
    apply MulEquiv.ext
    intro y
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hhom : ((MulAut.congr e1).trans (MulAut.congr (MulAut.conj c⁻¹))).toMonoidHom =
      (MulAut.congr (MulAut.conj c⁻¹)).toMonoidHom.comp (MulAut.congr e1).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, hhom, ← Subgroup.map_map, h1, Subgroup.map_map, ← h2, Subgroup.map_map]
  exact congrArg (fun h => E.map h)
    (MonoidHom.ext fun x => tw3m_congr_conj (MulAut.conj c⁻¹) x)

theorem ggTwE6Split_model_K_three
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.twE6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (h3 : 3 ∣ 2 ^ n - 1) :
    ∃ (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (F : Type) (_ : Field F) (_ : Finite F)
      (σ : F →+* F) (_ : Nat.card F = (2 ^ n) ^ 2) (_ : ∀ c, σ c = c ^ 2 ^ n)
      (ζ : Fˣ) (hζ : ζ ^ 3 = 1) (hζσ : σ (ζ : F) = ζ)
      (e : ↥K ≃* ↥(graphFixedRootGroup TwistTag.E6 F σ)),
      Subgroup.center ↥K = ⊥ ∧ orderOf ζ = 3 ∧
      (ggGamma K hN).range.map (MulAut.congr e).toMonoidHom =
        (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range.map
          (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 F σ) →*
            MulAut ↥(graphFixedRootGroup TwistTag.E6 F σ)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hBs, -, -, -⟩ := hH.1.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  have hn : 2 ≤ n := by
    have hn1 : 1 ≤ n := hΛ.1
    by_contra h
    have : n = 1 := by omega
    subst this
    norm_num at h3
  have h3p : ¬ 3 ∣ 2 ^ n + 1 := tw3m_not_three_dvd_add_one h3
  have hcard : commutator ↥K = ⊤ → ∀ {R : Type} [Group R]
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      GGTorusLift 3 4 R → 3 ^ 4 ≤ Nat.card ↥(ggGamma K hN).range :=
    fun hXc {R} _ θ hN hlift =>
      pow_le_card_range_ggGamma_bstar_of_torusLift hH.1 hnb hXc θ hN hlift
  obtain ⟨hN, Kf, hFieldKf, hFinKf, σe, hKc, hσe, e0, E0, hZK, hEab0, h4E0, hsc0, hAE0⟩ :=
    tw3m_model_of_innerDiag hRig hBs hSC (hH.2.2.1.2 y K hnb) hn h3 hΛ hK hcard
  letI : Field Kf := hFieldKf
  letI : Finite Kf := hFinKf
  obtain ⟨φ⟩ := tw3m_nonempty_equiv (n := n) (by omega) hKc σe hσe
  let E := E0.map φ.toMonoidHom
  obtain ⟨hEab, h4E, hscE⟩ := tw3m_transport_props φ E0 hEab0 h4E0 hsc0
  obtain ⟨ζ, hζ, ι₀, hζo, hinj, happly, hmem, hlast⟩ :=
    ExcFrames.exists_threeFrame (f := n) (by omega) h3p
  have hζσ : frobQ 2 n (ζ : GaloisField 2 (2 * n)) = ζ := by
    rw [frobQ_apply]
    exact congrArg Units.val (ExcFrames.zeta_pow_frobQ_eq_self hζ h3p)
  obtain ⟨c, hc⟩ := tw3m_conj_to_frame (n := n) (by omega) h3p hζ hζσ hζo hEab h4E hscE
  let e1 := e0.trans φ
  have hAE1 : (ggGamma K hN).range.map (MulAut.congr e1).toMonoidHom =
      E.map (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n))
        (frobQ 2 n)) →* MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n))
          (frobQ 2 n))) :=
    tw3m_congr_map_conj ((ggGamma K hN).range) e0 φ E0 hAE0
  refine ⟨hN, GaloisField 2 (2 * n), inferInstance, inferInstance, frobQ 2 n, ?_, ?_, ζ, hζ,
    hζσ, e1.trans (MulAut.conj c⁻¹), hZK, hζo, ?_⟩
  · exact CFSG.LieType.Universal.card_galoisField_two_mul 2 n (by omega)
  · exact fun c => frobQ_apply 2 n c
  · exact tw3m_congr_assemble ((ggGamma K hN).range) e1 E c
      (ExcFrames.twE6SplitFrameHom (frobQ 2 n) ζ hζ hζσ).range hAE1 hc

end CFSG.StandardType

end
