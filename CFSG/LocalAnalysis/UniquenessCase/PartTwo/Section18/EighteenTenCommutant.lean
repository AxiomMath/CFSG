module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.Background.HSp4Model
public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base11
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat
public import CFSG.Quasithin.Background.JonesParshallG2Derived
public import CFSG.Quasithin.Background.P3G2Zorn
public import CFSG.Quasithin.Vol2.KGNatCoord
public import CFSG.Quasithin.Vol2.Ch11G2Q8Comm
public import CFSG.ClassicalGroups.Orthogonal.EichlerCentralizerScalar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CentOmegaMinusFour
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CentNatural
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch10SecQ34CA
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecBFacts
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base10
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base3
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base4
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base19
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base20
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base21
public import CFSG.Quasithin.Vol2.Ch11SecCFacts
public import CFSG.Quasithin.Vol2.Ch11SecCFacts2
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.KGNatSL2
public import CFSG.Sporadic.Schreier.J4SSylow
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8
open scoped Matrix

variable {W : Type} [CommGroup W] [Finite W]

theorem hasScalarCommutant_statedOmegaMinus2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.Quasithin.H.HasScalarCommutant (StatedOmega (StatedQuadMinus 2 K b c)) := by
  classical
  intro g hg
  have hcomm_eichler : ∀ (u w x : (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2) → K),
      g (eichler (quadMinus (4 / 2) K b c) u w x) =
        eichler (quadMinus (4 / 2) K b c) u w (g x) := by
    intro u w x
    obtain ⟨A, hA, hAapp⟩ :=
      exists_mem_statedOmega_quadMinus_eichler (m := 4 / 2) (b := b) (c := c)
        (by norm_num) hirr u w
    have h := hg (⟨A, hA⟩ : ↥(StatedOmega (StatedQuadMinus 2 K b c))) hA x
    rw [hAapp x, hAapp (g x)] at h
    exact h
  let P : HypPair (quadMinus (4 / 2) K b c) := minusPair K b c (0 : Fin (4 / 2 - 1))
  have hPe : P.e = Pi.single (Sum.inl (0 : Fin (4 / 2 - 1))) 1 := rfl
  have hPf : P.f = Pi.single (Sum.inr (Sum.inl (0 : Fin (4 / 2 - 1)))) 1 := rfl
  have hw₀ : (Pi.single (Sum.inr (Sum.inr 0)) 1 :
      Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) ∈ P.perp :=
    single_inr_inr_mem_perp (i0 := 0) P hPe hPf 0
  have hQw₀ : quadMinus (4 / 2) K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) ≠ 0 := by
    rw [quadMinus_single_u]
    exact one_ne_zero
  obtain ⟨μ, hμ⟩ := exists_eq_smul_of_commute_eichler
    (Q := quadMinus (4 / 2) K b c)
    (nondegenerate_polarBilin_quadMinus_of_finite (4 / 2) K hirr) P
    ⟨_, hw₀, hQw₀⟩ g
    (fun w _ x => hcomm_eichler P.e w x) (fun w _ x => hcomm_eichler P.f w x)
  exact ⟨μ, hμ⟩

theorem commutant_section_of_matrix {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [Finite K]
    {H : Subgroup (MulAut W)} {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {π : ↥Γ →* ↥H}
    {β : W →* Multiplicative (ι → K)} (hβs : Function.Surjective β)
    {Z : Subgroup W} (hβk : ∀ w : W, β w = 1 ↔ w ∈ Z)
    (hβe : ∀ (γ : ↥Γ) (w : W),
      β (((π γ : ↥H) : MulAut W) w) = natAct Γ γ (β w))
    (HSC : CFSG.Quasithin.H.HasScalarCommutant Γ)
    {c : MulAut W} (hcZ : ∀ z ∈ Z, c z ∈ Z)
    (hc : ∀ x ∈ H, c * x = x * c)
    (hcopK : Nat.Coprime (orderOf c) (Nat.card K - 1)) :
    ∀ w : W, c w * w⁻¹ ∈ Z := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hker : β.ker ≤ (β.comp c.toMonoidHom).ker := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    have hwZ : w ∈ Z := (hβk w).1 hw
    exact (hβk (c w)).2 (hcZ w hwZ)
  let ψ : Multiplicative (ι → K) →* Multiplicative (ι → K) :=
    β.liftOfSurjective hβs ⟨β.comp c.toMonoidHom, hker⟩
  have hψ : ∀ w : W, ψ (β w) = β (c w) := fun w =>
    β.liftOfRightInverse_comp_apply _ _ ⟨β.comp c.toMonoidHom, hker⟩ w
  let g : (ι → K) →+ (ι → K) :=
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (ψ (Multiplicative.ofAdd v)))
      (fun a b => by simp [ofAdd_add, map_mul])
  have hgapp : ∀ v : ι → K,
      g v = Multiplicative.toAdd (ψ (Multiplicative.ofAdd v)) := fun _ => rfl
  have hg : ∀ γ ∈ Γ, ∀ v : ι → K,
      g (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v) =
        ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ g v := by
    intro γ hγ v
    let γ' : ↥Γ := ⟨γ, hγ⟩
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd v)
    have hstep : β (((π γ' : ↥H) : MulAut W) w) =
        Multiplicative.ofAdd (((γ : Matrix.GeneralLinearGroup ι K) :
          Matrix ι ι K) *ᵥ v) := by
      rw [hβe γ' w, hw]
      rfl
    have hcπ : c * (π γ' : MulAut W) = (π γ' : MulAut W) * c := hc (π γ') (π γ').2
    have h4 : c (((π γ' : ↥H) : MulAut W) w) =
        ((π γ' : ↥H) : MulAut W) (c w) := by
      have := congrArg (fun m : MulAut W => m w) hcπ
      simpa [MulAut.mul_apply] using this
    calc g (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ v)
        = Multiplicative.toAdd (ψ (β (((π γ' : ↥H) : MulAut W) w))) := by
          rw [hstep]
          rfl
      _ = Multiplicative.toAdd (β (c (((π γ' : ↥H) : MulAut W) w))) := by rw [hψ]
      _ = Multiplicative.toAdd (β (((π γ' : ↥H) : MulAut W) (c w))) := by rw [h4]
      _ = Multiplicative.toAdd (natAct Γ γ' (β (c w))) := by rw [hβe γ' (c w)]
      _ = Multiplicative.toAdd (natAct Γ γ' (ψ (β w))) := by rw [hψ w]
      _ = ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
            Multiplicative.toAdd (ψ (β w)) := rfl
      _ = ((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ g v := by
          rw [hgapp, ← hw]
  obtain ⟨a, ha⟩ := HSC g (fun γ hγ => hg γ hγ)
  have hscale : ∀ w : W, β (c w) =
      Multiplicative.ofAdd (a • Multiplicative.toAdd (β w)) := by
    intro w
    have h2 : ψ (β w) = Multiplicative.ofAdd (a • Multiplicative.toAdd (β w)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_ofAdd]
      have hgv := hgapp (Multiplicative.toAdd (β w))
      simp only [ofAdd_toAdd] at hgv
      rw [← hgv]
      exact ha _
    rw [← hψ w, h2]
  have ha0 : a ≠ 0 := by
    intro ha0
    obtain ⟨i⟩ := ‹Nonempty ι›
    let v₀ : ι → K := Pi.single i 1
    have hv₀ : v₀ ≠ 0 := by
      intro h
      have := congrFun h i
      simp [v₀] at this
    obtain ⟨w₀, hw₀⟩ := hβs (Multiplicative.ofAdd v₀)
    have hc0 : β (c w₀) = 1 := by
      rw [hscale w₀, ha0, zero_smul, ofAdd_zero]
    have hcZ0 : c w₀ ∈ Z := (hβk (c w₀)).1 hc0
    have hcZ' : ∀ z ∈ Z, c⁻¹ z ∈ Z := by
      intro z hz
      have hle : Z.map c.toMonoidHom ≤ Z := by
        rintro _ ⟨y, hy, rfl⟩
        exact hcZ y hy
      have heq : Z.map c.toMonoidHom = Z := by
        refine Subgroup.eq_of_le_of_card_ge hle ?_
        rw [Subgroup.card_map_of_injective c.injective]
      have hz' : z ∈ Z.map c.toMonoidHom := heq.ge hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz'
      have : c⁻¹ z = y := by rw [← hyz]; simp
      rw [this]
      exact hy
    have hwZ : w₀ ∈ Z := by
      have h := hcZ' (c w₀) hcZ0
      have hc_inv : c⁻¹ (c w₀) = w₀ := by simp
      rwa [hc_inv] at h
    have h1 : β w₀ = 1 := (hβk w₀).2 hwZ
    have h2 : Multiplicative.ofAdd v₀ = 1 := by rw [← hw₀]; exact h1
    have h3 : v₀ = 0 := by simpa using congrArg Multiplicative.toAdd h2
    exact hv₀ h3
  have hpow : ∀ k : ℕ, ∀ w : W, β ((c ^ k) w) =
      Multiplicative.ofAdd ((a ^ k) • Multiplicative.toAdd (β w)) := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        rw [pow_succ', MulAut.mul_apply, hscale, ih, toAdd_ofAdd, smul_smul, pow_succ']
  have haord : a ^ orderOf c = 1 := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    let v₀ : ι → K := Pi.single i 1
    obtain ⟨w₀, hw₀⟩ := hβs (Multiplicative.ofAdd v₀)
    have h := hpow (orderOf c) w₀
    rw [pow_orderOf_eq_one, MulAut.one_apply, hw₀] at h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd] at h'
    have := congrFun h' i
    simpa [v₀] using this.symm
  have haK : a ^ (Nat.card K - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [← Nat.card_eq_fintype_card] at h
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ orderOf c := orderOf_dvd_of_pow_eq_one haord
    have h2 : orderOf a ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one haK
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopK h1 h2)
  intro w
  have h1 : β (c w) = β w := by rw [hscale w, ha1, one_smul]; simp
  have h2 : β (c w * w⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  exact (hβk (c w * w⁻¹)).1 h2

theorem commutant_section_of_coord {K M : Type} [Field K] [Finite K] [AddCommGroup M]
    [Module K M]
    [Nontrivial M] {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)}
    {π : Γ →* ↥H} {ρ : Γ → M →+ M} {Z : Subgroup W}
    {f : W → M} (hfadd : ∀ a b : W, f (a * b) = f a + f b)
    (hfs : Function.Surjective f) (hfk : ∀ w : W, f w = 0 ↔ w ∈ Z)
    (hfe : ∀ (γ : Γ) (w : W), f (((π γ : ↥H) : MulAut W) w) = ρ γ (f w))
    (HSC : ∀ g : M →+ M, (∀ γ : Γ, g.comp (ρ γ) = (ρ γ).comp g) →
      ∃ a : K, ∀ v, g v = a • v)
    {c : MulAut W} (hcZ : ∀ z ∈ Z, c z ∈ Z)
    (hc : ∀ x ∈ H, c * x = x * c)
    (hcopK : Nat.Coprime (orderOf c) (Nat.card K - 1)) :
    ∀ w : W, c w * w⁻¹ ∈ Z := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hf1 : f 1 = 0 := by
    have h := hfadd 1 1
    rw [mul_one] at h
    have h1 : f 1 + f 1 = f 1 + 0 := by simpa using h.symm
    exact add_left_cancel h1
  have hfinv : ∀ w : W, f w⁻¹ = -f w := by
    intro w
    have h := hfadd w w⁻¹
    rw [mul_inv_cancel, hf1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  let pre : M → W := fun m => Classical.choose (hfs m)
  have hpre : ∀ m : M, f (pre m) = m := fun m => Classical.choose_spec (hfs m)
  have hgwd : ∀ (m : M) (w : W), f w = m → f (c (pre m)) = f (c w) := by
    intro m w hw
    have hzw : w * (pre m)⁻¹ ∈ Z := by
      rw [← hfk, hfadd, hfinv, hw, hpre m]
      exact add_neg_cancel m
    have h0 : f (c (w * (pre m)⁻¹)) = 0 := (hfk _).2 (hcZ _ hzw)
    rw [map_mul, map_inv, hfadd, hfinv] at h0
    have h0' : f (c w) - f (c (pre m)) = 0 := by
      rw [sub_eq_add_neg]
      exact h0
    exact (sub_eq_zero.mp h0').symm
  let gfun : M → M := fun m => f (c (pre m))
  have hgfun : ∀ (m : M) (w : W), f w = m → gfun m = f (c w) := fun m w hw => hgwd m w hw
  have hgadd : ∀ m₁ m₂ : M, gfun (m₁ + m₂) = gfun m₁ + gfun m₂ := by
    intro m₁ m₂
    have h1 := hgfun (m₁ + m₂) (pre m₁ * pre m₂) (by rw [hfadd, hpre, hpre])
    have h2 : f (c (pre m₁ * pre m₂)) = gfun m₁ + gfun m₂ := by
      simp only [gfun, map_mul, hfadd]
    rw [h1, h2]
  let g : M →+ M := AddMonoidHom.mk' gfun hgadd
  have hgm : ∀ m : M, g m = f (c (pre m)) := fun _ => rfl
  have hcomm : ∀ γ : Γ, g.comp (ρ γ) = (ρ γ).comp g := by
    intro γ
    ext m
    have h2 : g (ρ γ m) = f (c (((π γ : ↥H) : MulAut W) (pre m))) := by
      change gfun (ρ γ m) = f (c (((π γ : ↥H) : MulAut W) (pre m)))
      exact hgfun (ρ γ m) (((π γ : ↥H) : MulAut W) (pre m)) (by rw [hfe, hpre])
    show g (ρ γ m) = ρ γ (g m)
    rw [h2]
    have hcπ : c * (π γ : MulAut W) = (π γ : MulAut W) * c := hc (π γ) (π γ).2
    have h4 : c (((π γ : ↥H) : MulAut W) (pre m)) =
        ((π γ : ↥H) : MulAut W) (c (pre m)) := by
      have := congrArg (fun q : MulAut W => q (pre m)) hcπ
      simpa [MulAut.mul_apply] using this
    rw [h4, hfe]
    rfl
  obtain ⟨a, ha⟩ := HSC g hcomm
  have hscale : ∀ w : W, f (c w) = a • f w := by
    intro w
    rw [show f (c w) = g (f w) from (hgfun (f w) w rfl).symm, ha]
  have hcZ' : ∀ z ∈ Z, c⁻¹ z ∈ Z := by
    intro z hz
    have hle : Z.map c.toMonoidHom ≤ Z := by
      rintro _ ⟨y, hy, rfl⟩
      exact hcZ y hy
    have heq : Z.map c.toMonoidHom = Z := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective c.injective]
    have hz' : z ∈ Z.map c.toMonoidHom := heq.ge hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz'
    have : c⁻¹ z = y := by rw [← hyz]; simp
    rw [this]
    exact hy
  have ha0 : a ≠ 0 := by
    intro ha0
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    obtain ⟨w, hw⟩ := hfs m
    have hz : c w ∈ Z := (hfk (c w)).1 (by rw [hscale, ha0, zero_smul])
    have h := hcZ' (c w) hz
    have hc_inv : c⁻¹ (c w) = w := by simp
    rw [hc_inv] at h
    have h0 : f w = 0 := (hfk w).2 h
    rw [hw] at h0
    exact hm h0
  have hpow : ∀ (k : ℕ) (w : W), f ((c ^ k) w) = (a ^ k) • f w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        rw [pow_succ', MulAut.mul_apply, hscale, ih, smul_smul, pow_succ']
  have haord : a ^ orderOf c = 1 := by
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    obtain ⟨w, hw⟩ := hfs m
    have h := hpow (orderOf c) w
    rw [pow_orderOf_eq_one, MulAut.one_apply, hw] at h
    have h' : a ^ orderOf c • m = (1 : K) • m := by rw [← h]; simp
    exact smul_left_injective K hm h'
  have haK : a ^ (Nat.card K - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [← Nat.card_eq_fintype_card] at h
  have ha1 : a = 1 := by
    have h1 : orderOf a ∣ orderOf c := orderOf_dvd_of_pow_eq_one haord
    have h2 : orderOf a ∣ Nat.card K - 1 := orderOf_dvd_of_pow_eq_one haK
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopK h1 h2)
  intro w
  have h1 : f (c w) = f w := by rw [hscale w, ha1, one_smul]
  have h2 : f (c w * w⁻¹) = 0 := by rw [hfadd, hfinv, h1, add_neg_cancel]
  exact (hfk _).1 h2

theorem k_18_10_commutant :
    ∀ {W : Type} [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut W)) (f : ℕ),
        (NatSpn H ⊤ (CFSG.Quasithin.fixV H) 4 f ∨
          CFSG.Quasithin.G2Natural H ⊤ (CFSG.Quasithin.fixV H) f ∨
          CFSG.Quasithin.BinaryNaturalSL H ⊤ (CFSG.Quasithin.fixV H) 2 f ∨
          (Even f ∧ NatOmegaMinus H ⊤ (CFSG.Quasithin.fixV H) 4 (f / 2))) →
        ∀ c : MulAut W, (∀ x ∈ H, c * x = x * c) → Nat.Coprime (orderOf c) (2 ^ f - 1) →
          ∀ w : W, c w * w⁻¹ ∈ CFSG.Quasithin.fixV H := by
  intro W _ _ hW H f hcase c hc hcop w
  classical
  set Z : Subgroup W := CFSG.Quasithin.fixV H with hZdef
  have hcZ : ∀ z ∈ Z, c z ∈ Z := by
    intro z hz
    rw [hZdef, mem_fixV] at hz ⊢
    intro x hx
    have hcomm := congrArg (fun m : MulAut W => m z) (hc x hx)
    simpa [MulAut.mul_apply, hz x hx] using hcomm.symm
  rcases hcase with hsp | hg2 | hsl | hom
  ·
    obtain ⟨hEven, hrest⟩ := hsp
    obtain ⟨K, hKf, hKfin, hrest⟩ := hrest
    obtain ⟨hKcard, hR⟩ := hrest
    letI := hKf
    letI := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨π, hπ⟩ := hR
    have hNat : CFSG.Quasithin.SzN15.NatReal H ⊤ Z (StatedSp (4 / 2) K) π :=
      CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    obtain ⟨β, hβs, hβk, hβe⟩ := hNat.exists_β
    let β' : W →* Multiplicative (Fin 2 ⊕ Fin 2 → K) :=
      β.comp (Subgroup.topEquiv.symm.toMonoidHom)
    have hβ's : Function.Surjective β' := hβs.comp Subgroup.topEquiv.symm.surjective
    have hβ'k : ∀ v : W, β' v = 1 ↔ v ∈ Z := fun v => hβk ⟨v, trivial⟩
    have hβ'e : ∀ (γ : ↥(StatedSp (4 / 2) K)) (v : W),
        β' (((π γ : ↥H) : MulAut W) v) = natAct (StatedSp (4 / 2) K) γ (β' v) :=
      fun γ v => hβe γ ⟨v, trivial⟩ trivial
    exact commutant_section_of_matrix hβ's hβ'k hβ'e
      (CFSG.Quasithin.H.Sp4.hasScalarCommutant_statedSp (K := K)) hcZ hc
      (by rw [hKcard]; exact hcop) w
  ·
    obtain ⟨K, hKf, hKfin, hrest⟩ := hg2
    obtain ⟨hKcard, hR⟩ := hrest
    letI := hKf
    letI := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard)
    have hG2le : CFSG.Open.quasithinG2 K ≤ CFSG.Quasithin.Explicit.cayleyGroup K := by
      rw [CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup]
    obtain ⟨π, hπ⟩ := hR
    let LM := linModelZorn (F := K) (CFSG.Open.quasithinG2 K) hG2le
    obtain ⟨f, hfaddU, hfkU, hfsU, hfeU⟩ := exists_coord LM hπ
    have hfadd : ∀ a b : W, f (a * b) = f a + f b :=
      fun a b => hfaddU a trivial b trivial
    have hfk : ∀ v : W, f v = 0 ↔ v ∈ Z := fun v => hfkU v trivial
    have hfs : Function.Surjective f := fun m => by
      obtain ⟨u, -, hu⟩ := hfsU m
      exact ⟨u, hu⟩
    have hfe : ∀ (γ : ↥(CFSG.Open.quasithinG2 K)) (v : W),
        f (((π γ : ↥H) : MulAut W) v) = (LM.lin γ).toAddMonoidHom (f v) := by
      intro γ v
      exact hfeU γ v trivial
    haveI : Nontrivial (Ix3 → K) := by
      refine ⟨⟨0, Pi.single (Sum.inl 0) 1, ?_⟩⟩
      intro h
      have := congrFun h (Sum.inl 0)
      simp at this
    refine commutant_section_of_coord (K := K) (M := Ix3 → K)
      (Γ := ↥(CFSG.Open.quasithinG2 K)) (π := π) (Z := Z) (f := f)
      (ρ := fun γ : ↥(CFSG.Open.quasithinG2 K) => (LM.lin γ).toAddMonoidHom)
      hfadd hfs hfk hfe ?_ hcZ hc (by rw [hKcard]; exact hcop) w
    intro g hg
    refine commutant_cayley g (fun γc x => ?_)
    let γ : ↥(CFSG.Open.quasithinG2 K) := ⟨γc.1, by
      rw [CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup]
      exact γc.2⟩
    have h := congrArg (fun q : (Ix3 → K) →+ (Ix3 → K) => q x) (hg γ)
    have hlin : ∀ x : Ix3 → K, LM.lin γ x = g2Act γc x := fun x => rfl
    simpa [AddMonoidHom.comp_apply, hlin, γ] using h
  ·
    obtain ⟨K, hKf, hKfin, hrest⟩ := hsl
    obtain ⟨hKcard, hR⟩ := hrest
    letI := hKf
    letI := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨π, hπ⟩ := hR
    have hNat : CFSG.Quasithin.SzN15.NatReal H ⊤ Z (StatedSL 2 K) π :=
      CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    obtain ⟨β, hβs, hβk, hβe⟩ := hNat.exists_β
    let β' : W →* Multiplicative (Fin 2 → K) :=
      β.comp (Subgroup.topEquiv.symm.toMonoidHom)
    have hβ's : Function.Surjective β' := hβs.comp Subgroup.topEquiv.symm.surjective
    have hβ'k : ∀ v : W, β' v = 1 ↔ v ∈ Z := fun v => hβk ⟨v, trivial⟩
    have hβ'e : ∀ (γ : ↥(StatedSL 2 K)) (v : W),
        β' (((π γ : ↥H) : MulAut W) v) = natAct (StatedSL 2 K) γ (β' v) :=
      fun γ v => hβe γ ⟨v, trivial⟩ trivial
    exact commutant_section_of_matrix hβ's hβ'k hβ'e
      (CFSG.Quasithin.H.hasScalarCommutant_statedSL (K := K) (d := 2) le_rfl) hcZ hc
      (by rw [hKcard]; exact hcop) w
  ·
    obtain ⟨hev, hrest⟩ := hom
    obtain ⟨hEven, hrest⟩ := hrest
    obtain ⟨K, hKf, hKfin, b, c₀, hrest⟩ := hrest
    obtain ⟨hKcard, hrest⟩ := hrest
    obtain ⟨hirr, hR⟩ := hrest
    letI := hKf
    letI := hKfin
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f / 2) (by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard)
    obtain ⟨π, hπ⟩ := hR
    have hNat : CFSG.Quasithin.SzN15.NatReal H ⊤ Z
        (StatedOmega (StatedQuadMinus (4 / 2) K b c₀)) π :=
      CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
    obtain ⟨β, hβs, hβk, hβe⟩ := hNat.exists_β
    let β' : W →* Multiplicative (Fin (4 / 2 - 1) ⊕ Fin (4 / 2 - 1) ⊕ Fin 2 → K) :=
      β.comp (Subgroup.topEquiv.symm.toMonoidHom)
    have hβ's : Function.Surjective β' := hβs.comp Subgroup.topEquiv.symm.surjective
    have hβ'k : ∀ v : W, β' v = 1 ↔ v ∈ Z := fun v => hβk ⟨v, trivial⟩
    have hβ'e : ∀ (γ : ↥(StatedOmega (StatedQuadMinus (4 / 2) K b c₀))) (v : W),
        β' (((π γ : ↥H) : MulAut W) v) =
          natAct (StatedOmega (StatedQuadMinus (4 / 2) K b c₀)) γ (β' v) :=
      fun γ v => hβe γ ⟨v, trivial⟩ trivial
    have hcopK : Nat.Coprime (orderOf c) (Nat.card K - 1) := by
      rw [hKcard]
      refine hcop.coprime_dvd_right ?_
      exact Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨2, by
        obtain ⟨m, hm⟩ := hev
        omega⟩
    exact commutant_section_of_matrix hβ's hβ'k hβ'e
      (hasScalarCommutant_statedOmegaMinus2 hirr) hcZ hc hcopK w

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
