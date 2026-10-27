module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523
public import CFSG.Quasithin.Vol2.Ch6NatRho
public import CFSG.Quasithin.H13.VolIAltCoverUniversal
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
  (even_SL2_full_automorphism_semilinear_model)

variable {G : Type} [Group G]

section Transport

variable {L W V : Subgroup G} {n : ℕ}

theorem congr_conjAct_eq {f : ↥W ≃* ↥V} {g : G} (hgW : g ∈ Subgroup.normalizer (W : Set G))
    (hgV : g ∈ Subgroup.normalizer (V : Set G))
    (hf : ∀ w : ↥W, ((f (conjAct W ⟨g, hgW⟩ w) : ↥V) : G) = g * f w * g⁻¹) :
    MulAut.congr f (conjAct W ⟨g, hgW⟩) = conjAct V ⟨g, hgV⟩ := by
  ext v
  obtain ⟨w, rfl⟩ := f.surjective v
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hf, conjAct_apply_coe]

theorem IsNatModCh5.of_mulEquiv (hW : IsNatModCh5 L W n)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV : IsMulCommutative ↥V) (f : ↥W ≃* ↥V)
    (hf : ∀ (l : G) (hl : l ∈ L) (w : ↥W),
      ((f (conjAct W ⟨l, hW.1 hl⟩ w) : ↥V) : G) = l * f w * l⁻¹) :
    IsNatModCh5 L V n := by
  obtain ⟨hc, K, _, _, π, E, hK, hπs, hE⟩ := hW.exists_equiv
  have hmap : ∀ φ ∈ autOn L W, MulAut.congr f φ ∈ autOn L V := by
    intro φ hφ
    obtain ⟨g, hgL, rfl⟩ := mem_autOn_iff.mp hφ
    have hgV : (g : G) ∈ Subgroup.normalizer (V : Set G) := hLV hgL
    have h1 : MulAut.congr f (conjAct W g) = conjAct V ⟨g, hgV⟩ :=
      congr_conjAct_eq g.2 hgV (hf g hgL)
    rw [h1]
    exact mem_autOn_iff.mpr ⟨⟨g, hgV⟩, hgL, rfl⟩
  let ι : ↥(autOn L W) →* ↥(autOn L V) :=
    { toFun := fun φ => ⟨MulAut.congr f φ, hmap φ φ.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun φ ψ => Subtype.ext
        (map_mul (MulAut.congr f) (φ : MulAut ↥W) (ψ : MulAut ↥W)) }
  have hιs : Function.Surjective ι := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hgL, rfl⟩ := mem_autOn_iff.mp hψ
    have hgW : (g : G) ∈ Subgroup.normalizer (W : Set G) := hW.1 hgL
    refine ⟨⟨conjAct W ⟨g, hgW⟩, mem_autOn_iff.mpr ⟨⟨g, hgW⟩, hgL, rfl⟩⟩, Subtype.ext ?_⟩
    exact congr_conjAct_eq hgW g.2 (hf g hgL)
  let π' := ι.comp π
  have hπ's : Function.Surjective π' := hιs.comp hπs
  let Φ : ↥V ≃* ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K))) :=
    f.symm.trans (E.trans Subgroup.topEquiv.symm)
  have hΦ : ∀ γ v, (Φ (((π' γ : ↥(autOn L V)) : MulAut ↥V) v) :
      Multiplicative (Fin 2 → K)) = (FFModel.nat (Assembly.LowTwoRank.StatedSL 2 K)).act γ
        ((Φ v : ↥(⊤ : Subgroup (Multiplicative (Fin 2 → K)))) : Multiplicative (Fin 2 → K)) := by
    intro γ v
    show E (f.symm (MulAut.congr f (π γ : MulAut ↥W) v)) =
      natAct (Assembly.LowTwoRank.StatedSL 2 K) γ (E (f.symm v))
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    unfold natAct
    rw [← hE γ (f.symm v), ofAdd_toAdd]
  exact ⟨hLV, hV, K, inferInstance, inferInstance, hK,
    VolI.realizes_of_mulEquiv rfl π' hπ's Φ hΦ⟩

end Transport

section Iso

variable [Finite G] {L W₁ W₂ : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem NatL2Data.conj_of_equiv {V : Subgroup G} (D : NatL2Data L V n)
    (φ : (Fin 2 → D.K) ≃+ (Fin 2 → D.K))
    (hφ : ∀ (ℓ : ↥L) (x : Fin 2 → D.K),
      φ (((D.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) D.K) :
          Matrix (Fin 2) (Fin 2) D.K).mulVec x) =
        ((D.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) D.K) : Matrix (Fin 2) (Fin 2) D.K).mulVec
          (φ x)) :
    ∃ ψ : ↥V ≃* ↥V, (∀ v, Multiplicative.toAdd (D.E (ψ v)) = φ (Multiplicative.toAdd (D.E v))) ∧
      ∀ (l : G) (hl : l ∈ L) (v : ↥V),
        ((ψ (conjAct V ⟨l, D.le_normalizer hl⟩ v) : ↥V) : G) = l * ψ v * l⁻¹ := by
  let ψ : ↥V ≃* ↥V := D.E.trans (φ.toMultiplicative.trans D.E.symm)
  have hψ : ∀ v, Multiplicative.toAdd (D.E (ψ v)) = φ (Multiplicative.toAdd (D.E v)) := by
    intro v
    show Multiplicative.toAdd (D.E (D.E.symm (φ.toMultiplicative (D.E v)))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  refine ⟨ψ, hψ, fun l hl v => ?_⟩
  have h1 : D.E (ψ (conjAct V ⟨l, D.le_normalizer hl⟩ v)) =
      D.E (conjAct V ⟨l, D.le_normalizer hl⟩ (ψ v)) := by
    apply Multiplicative.toAdd.injective
    rw [hψ, D.toAdd_E_conj, D.toAdd_E_conj, D.conj_eq_rho ⟨l, hl⟩, D.conj_eq_rho ⟨l, hl⟩, hψ]
    exact hφ ⟨l, hl⟩ _
  rw [D.E.injective h1, conjAct_apply_coe]

omit [Finite G] in
theorem exists_equivariant_mulEquiv (hW₁ : IsNatModCh5 L W₁ n) (hW₂ : IsNatModCh5 L W₂ n)
    (hn : 1 ≤ n)
    (hker : L ⊓ Subgroup.centralizer (W₁ : Set G) = L ⊓ Subgroup.centralizer (W₂ : Set G)) :
    ∃ ψ : ↥W₁ ≃* ↥W₂, ∀ (l : G) (hl : l ∈ L) (w : ↥W₁),
      ((ψ (conjAct W₁ ⟨l, hW₁.1 hl⟩ w) : ↥W₂) : G) = l * ψ w * l⁻¹ := by
  let D₁ := hW₁.data
  let D₂ := hW₂.data
  set K := D₂.K
  obtain ⟨τ⟩ : Nonempty (D₁.K ≃+* K) := by
    have hcard : Nat.card D₁.K = Nat.card K := by rw [D₁.card, D₂.card]
    have := Fintype.ofFinite D₁.K
    have := Fintype.ofFinite K
    exact ⟨FiniteField.ringEquivOfCardEq (by simpa [Nat.card_eq_fintype_card] using hcard)⟩
  let τv : (Fin 2 → D₁.K) ≃+ (Fin 2 → K) := AddEquiv.piCongrRight fun _ => τ.toAddEquiv
  let ρ₁ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K :=
    (Matrix.SpecialLinearGroup.map τ.toRingHom).comp D₁.rho
  have hρ₁ : ∀ (ℓ : ↥L) (x : Fin 2 → D₁.K),
      τv (((D₁.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) D₁.K) :
        Matrix (Fin 2) (Fin 2) D₁.K).mulVec x) =
        ((ρ₁ ℓ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
          (τv x) := by
    intro ℓ x
    funext i
    exact RingHom.map_mulVec τ.toRingHom _ x i
  have hs₁ : Function.Surjective ρ₁ := by
    intro A
    obtain ⟨ℓ, hℓ⟩ := D₁.rho_surjective (Matrix.SpecialLinearGroup.map τ.symm.toRingHom A)
    refine ⟨ℓ, ?_⟩
    show Matrix.SpecialLinearGroup.map τ.toRingHom (D₁.rho ℓ) = A
    rw [hℓ]
    ext i j
    simp
  have hk : ρ₁.ker = D₂.rho.ker := by
    ext ℓ
    have h1 : ℓ ∈ ρ₁.ker ↔ ℓ ∈ D₁.rho.ker := by
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
      constructor
      · intro h
        have h2 := congrArg (Matrix.SpecialLinearGroup.map τ.symm.toRingHom) h
        rw [map_one] at h2
        rw [← h2]
        ext i j
        simp
      · intro h
        rw [h, map_one]
    rw [h1, D₁.mem_ker_rho_iff, D₂.mem_ker_rho_iff]
    have := congrArg (fun X : Subgroup G => (ℓ : G) ∈ X) hker
    simpa [ℓ.2] using this
  let θ : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ₁ hs₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective D₂.rho D₂.rho_surjective))
  have hθ : ∀ ℓ : ↥L, θ (ρ₁ ℓ) = D₂.rho ℓ := by
    intro ℓ
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective ρ₁ hs₁).symm (ρ₁ ℓ) =
        (QuotientGroup.mk ℓ : ↥L ⧸ ρ₁.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.quotientKerEquivOfSurjective D₂.rho D₂.rho_surjective)
      ((QuotientGroup.quotientMulEquivOfEq hk)
        ((QuotientGroup.quotientKerEquivOfSurjective ρ₁ hs₁).symm (ρ₁ ℓ))) = _
    rw [h1]
    rfl
  obtain ⟨⟨h, σ⟩, hhσ, -⟩ :=
    (even_SL2_full_automorphism_semilinear_model hn D₂.card).2.2.2.2 θ
  let σv : (Fin 2 → K) ≃+ (Fin 2 → K) := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  let hv : (Fin 2 → K) ≃+ (Fin 2 → K) := (Matrix.SpecialLinearGroup.toLin' h).toAddEquiv
  have hvv : ∀ y : Fin 2 → K, hv y = (h : Matrix (Fin 2) (Fin 2) K).mulVec y := fun y => by
    simp [hv, Matrix.SpecialLinearGroup.toLin'_apply]
  let φ : (Fin 2 → K) ≃+ (Fin 2 → K) := σv.trans hv
  have hφ : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (x : Fin 2 → K),
      φ ((g : Matrix (Fin 2) (Fin 2) K).mulVec x) =
        ((θ g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec (φ x) := by
    intro g x
    have h1 : σv ((g : Matrix (Fin 2) (Fin 2) K).mulVec x) =
        ((Matrix.SpecialLinearGroup.map σ.toRingHom g : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).mulVec (σv x) := by
      funext i
      exact RingHom.map_mulVec σ.toRingHom _ x i
    have h2 : θ g * h = h * Matrix.SpecialLinearGroup.map σ.toRingHom g := by
      rw [hhσ g]
      group
    show hv (σv ((g : Matrix (Fin 2) (Fin 2) K).mulVec x)) =
      ((θ g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec
        (hv (σv x))
    rw [hvv, hvv, h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, h2]
  let ψ : ↥W₁ ≃* ↥W₂ :=
    D₁.E.trans ((τv.trans φ).toMultiplicative.trans D₂.E.symm)
  have hψ : ∀ w, Multiplicative.toAdd (D₂.E (ψ w)) = φ (τv (Multiplicative.toAdd (D₁.E w))) := by
    intro w
    show Multiplicative.toAdd (D₂.E (D₂.E.symm ((τv.trans φ).toMultiplicative (D₁.E w)))) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  refine ⟨ψ, fun l hl w => ?_⟩
  have h1 : D₂.E (ψ (conjAct W₁ ⟨l, hW₁.1 hl⟩ w)) =
      D₂.E (conjAct W₂ ⟨l, hW₂.1 hl⟩ (ψ w)) := by
    apply Multiplicative.toAdd.injective
    rw [hψ, D₁.toAdd_E_conj, D₂.toAdd_E_conj, D₁.conj_eq_rho ⟨l, hl⟩,
      D₂.conj_eq_rho ⟨l, hl⟩, hψ, hρ₁, hφ, hθ]
  rw [D₂.E.injective h1, conjAct_apply_coe]

omit [Finite G] in
theorem NatL2Data.exists_scalar {V : Subgroup G} (D : NatL2Data L V n) {c : D.K} (hc : c ≠ 0) :
    ∃ ψ : ↥V ≃* ↥V, (∀ v, Multiplicative.toAdd (D.E (ψ v)) = c • Multiplicative.toAdd (D.E v)) ∧
      ∀ (l : G) (hl : l ∈ L) (v : ↥V),
        ((ψ (conjAct V ⟨l, D.le_normalizer hl⟩ v) : ↥V) : G) = l * ψ v * l⁻¹ := by
  let φ : (Fin 2 → D.K) ≃+ (Fin 2 → D.K) :=
    (LinearEquiv.smulOfNeZero D.K (Fin 2 → D.K) c hc).toAddEquiv
  obtain ⟨ψ, hψ, hψL⟩ := D.conj_of_equiv φ fun ℓ x => by
    show c • ((D.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) D.K) :
      Matrix (Fin 2) (Fin 2) D.K).mulVec x = ((D.rho ℓ : Matrix.SpecialLinearGroup (Fin 2) D.K) :
        Matrix (Fin 2) (Fin 2) D.K).mulVec (c • x)
    rw [Matrix.mulVec_smul]
  exact ⟨ψ, hψ, hψL⟩

end Iso

section Sum

variable [Finite G] {L V W₁ W₂ : Subgroup G}

theorem isNatModCh5_graph {n : ℕ} (hW₁ : IsNatModCh5 L W₁ n) (hW₂ : IsNatModCh5 L W₂ n)
    (hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a) (hdisj : W₁ ⊓ W₂ = ⊥) (ψ : ↥W₁ ≃* ↥W₂)
    (hψ : ∀ (l : G) (hl : l ∈ L) (w : ↥W₁),
      ((ψ (conjAct W₁ ⟨l, hW₁.1 hl⟩ w) : ↥W₂) : G) = l * ψ w * l⁻¹) :
    ∃ V₁ : Subgroup G, (∀ w : ↥W₁, (w : G) * ψ w ∈ V₁) ∧ V₁ ≤ W₁ ⊔ W₂ ∧ IsNatModCh5 L V₁ n := by
  have hc1 : ∀ a b : ↥W₁, ((ψ a : ↥W₂) : G) * b = b * ψ a := fun a b =>
    (hcomm b b.2 (ψ a) (ψ a).2).symm
  let g : ↥W₁ →* G :=
    { toFun := fun w => (w : G) * ψ w
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul, map_mul]
        calc (a : G) * b * (ψ a * ψ b) = a * (b * ψ a) * ψ b := by group
          _ = a * (ψ a * b) * ψ b := by rw [hc1]
          _ = a * ψ a * (b * ψ b) := by group }
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (w : G) = ((ψ w : ↥W₂) : G)⁻¹ := eq_inv_of_mul_eq_one_left hw
    have h2 : (w : G) ∈ W₁ ⊓ W₂ := ⟨w.2, by rw [h1]; exact W₂.inv_mem (ψ w).2⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  set V₁ := g.range with hV₁
  refine ⟨V₁, fun w => ⟨w, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨w, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left w.2) (Subgroup.mem_sup_right (ψ w).2)
  have hW₁c : ∀ a b : ↥W₁, (a : G) * b = b * a := fun a b => by
    obtain ⟨_, hc, -⟩ := hW₁
    exact congrArg Subtype.val (hc.is_comm.comm a b)
  have hW₂c : ∀ a b : ↥W₂, (a : G) * b = b * a := fun a b => by
    obtain ⟨_, hc, -⟩ := hW₂
    exact congrArg Subtype.val (hc.is_comm.comm a b)
  have hV₁c : IsMulCommutative ↥V₁ := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hb]
    show (a : G) * ψ a * (b * ψ b) = b * ψ b * (a * ψ a)
    calc (a : G) * ψ a * (b * ψ b) = a * (ψ a * b) * ψ b := by group
      _ = a * (b * ψ a) * ψ b := by rw [hc1]
      _ = (a * b) * (ψ a * ψ b) := by group
      _ = b * a * (ψ b * ψ a) := by rw [hW₁c a b, hW₂c (ψ a) (ψ b)]
      _ = b * (a * ψ b) * ψ a := by group
      _ = b * (ψ b * a) * ψ a := by rw [hc1 b a]
      _ = b * ψ b * (a * ψ a) := by group
  have hgL : ∀ (l : G) (hl : l ∈ L) (w : ↥W₁),
      g (conjAct W₁ ⟨l, hW₁.1 hl⟩ w) = l * g w * l⁻¹ := by
    intro l hl w
    show ((conjAct W₁ ⟨l, hW₁.1 hl⟩ w : ↥W₁) : G) * ψ (conjAct W₁ ⟨l, hW₁.1 hl⟩ w) =
      l * ((w : G) * ψ w) * l⁻¹
    rw [conjAct_apply_coe, hψ l hl w]
    group
  have hLV₁ : L ≤ Subgroup.normalizer (V₁ : Set G) := by
    intro l hl
    refine mem_normalizer_of_forall_conj_mem' fun x hx => ?_
    obtain ⟨w, rfl⟩ := hx
    rw [← hgL l hl w]
    exact ⟨_, rfl⟩
  let f : ↥W₁ ≃* ↥V₁ := MonoidHom.ofInjective hg
  refine hW₁.of_mulEquiv hLV₁ hV₁c f fun l hl w => ?_
  show g (conjAct W₁ ⟨l, hW₁.1 hl⟩ w) = l * g w * l⁻¹
  exact hgL l hl w

theorem isIrrPlusBase_of_isNatModCh5 {n : ℕ} {W : Subgroup G} (hW : IsNatModCh5 L W n)
    (hWV : W ≤ V) : IsIrrPlusBase L V W := by
  have hC := hW.inf_centralizer_eq_bot
  have hne : W ≠ ⊥ := by
    intro hb
    apply hW.not_le_centralizer
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [hb] at hw
    rw [Subgroup.mem_bot.mp hw, one_mul, mul_one]
  refine ⟨hWV, hne, hW.1, hW.commutator_eq, ?_, fun J hJ1 hJ2 hJ3 => ?_⟩
  · rw [hC]
    exact bot_lt_iff_ne_bot.mpr hne
  · rw [hC]
    exact hW.irreducible J hJ2 hJ3

end Sum

theorem l4NatSumFact : L4NatSumFact := by
  intro G _ _ L V S v hsum habel hker hS hv hvS
  obtain ⟨W₁, W₂, hLW₁, hLW₂, hdisj, hsup, hW₁, hW₂⟩ := hsum
  have hW₁V : W₁ ≤ V := hsup ▸ le_sup_left
  have hW₂V : W₂ ≤ V := hsup ▸ le_sup_right
  have hcomm : ∀ a ∈ W₁, ∀ b ∈ W₂, a * b = b * a := fun a ha b hb =>
    habel a (hW₁V ha) b (hW₂V hb)
  have hW₂N : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := by
    intro b hb
    refine mem_normalizer_of_forall_conj_mem' fun a ha => ?_
    rw [← hcomm a ha b hb, mul_inv_cancel_right]
    exact ha
  have hvV : v ∈ ((W₁ ⊔ W₂ : Subgroup G) : Set G) := hsup ▸ hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W₁ W₂ hW₂N] at hvV
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hvV
  beta_reduce at hv hvS ⊢
  have hfix : ∀ s ∈ S, s * w₁ * s⁻¹ = w₁ ∧ s * w₂ * s⁻¹ = w₂ := by
    intro s hs
    have hsL := hS.1 hs
    have h1 : s * w₁ * s⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp (hLW₁ hsL) w₁).mp hw₁
    have h2 : s * w₂ * s⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp (hLW₂ hsL) w₂).mp hw₂
    have hv' : (s * w₁ * s⁻¹) * (s * w₂ * s⁻¹) = w₁ * w₂ := by
      have := Subgroup.mem_centralizer_iff.mp hvS s hs
      calc (s * w₁ * s⁻¹) * (s * w₂ * s⁻¹) = s * (w₁ * w₂) * s⁻¹ := by group
        _ = w₁ * w₂ := by rw [this]; group
    have h3 : w₁⁻¹ * (s * w₁ * s⁻¹) ∈ W₁ ⊓ W₂ := by
      refine ⟨W₁.mul_mem (W₁.inv_mem hw₁) h1, ?_⟩
      have e : w₁⁻¹ * (s * w₁ * s⁻¹) = w₂ * (s * w₂ * s⁻¹)⁻¹ := by
        calc w₁⁻¹ * (s * w₁ * s⁻¹) =
            w₁⁻¹ * ((s * w₁ * s⁻¹) * (s * w₂ * s⁻¹)) * (s * w₂ * s⁻¹)⁻¹ := by group
          _ = w₁⁻¹ * (w₁ * w₂) * (s * w₂ * s⁻¹)⁻¹ := by rw [hv']
          _ = w₂ * (s * w₂ * s⁻¹)⁻¹ := by group
      rw [e]
      exact W₂.mul_mem hw₂ (W₂.inv_mem h2)
    rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at h3
    refine ⟨h3.symm, ?_⟩
    calc s * w₂ * s⁻¹ = (s * w₁ * s⁻¹)⁻¹ * ((s * w₁ * s⁻¹) * (s * w₂ * s⁻¹)) := by group
      _ = w₁⁻¹ * (w₁ * w₂) := by rw [hv', ← h3]
      _ = w₂ := by group
  by_cases h₂ : w₂ = 1
  · refine ⟨W₁, by rw [h₂, mul_one]; exact hw₁, hW₁, isIrrPlusBase_of_isNatModCh5 hW₁ hW₁V⟩
  by_cases h₁ : w₁ = 1
  · refine ⟨W₂, by rw [h₁, one_mul]; exact hw₂, hW₂, isIrrPlusBase_of_isNatModCh5 hW₂ hW₂V⟩
  have hk₁ : L ⊓ Subgroup.centralizer (W₁ : Set G) = L ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (le_inf inf_le_left (hker W₁ hW₁V hW₁))
      (inf_le_inf_left _ (Subgroup.centralizer_le hW₁V))
  have hk₂ : L ⊓ Subgroup.centralizer (W₂ : Set G) = L ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm (le_inf inf_le_left (hker W₂ hW₂V hW₂))
      (inf_le_inf_left _ (Subgroup.centralizer_le hW₂V))
  obtain ⟨ψ₀, hψ₀⟩ := exists_equivariant_mulEquiv hW₁ hW₂ (by norm_num) (hk₁.trans hk₂.symm)
  have hψ₀' : ∀ (l : G) (hl : l ∈ L) (w : ↥W₁),
      ψ₀ (conjAct W₁ ⟨l, hW₁.1 hl⟩ w) = conjAct W₂ ⟨l, hW₂.1 hl⟩ (ψ₀ w) := by
    intro l hl w
    apply Subtype.ext
    rw [hψ₀ l hl w, conjAct_apply_coe]
  let D₂ := hW₂.data
  have : CharP D₂.K 2 :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.char_two_of_card D₂.card
  set x₁ := Multiplicative.toAdd (D₂.E (ψ₀ ⟨w₁, hw₁⟩)) with hx₁
  set x₂ := Multiplicative.toAdd (D₂.E ⟨w₂, hw₂⟩) with hx₂
  have hx₁0 : x₁ ≠ 0 := by
    intro h0
    apply h₁
    have h1 : D₂.E (ψ₀ ⟨w₁, hw₁⟩) = 1 := Multiplicative.toAdd.injective (by rw [← hx₁, h0]; rfl)
    have h2 : ψ₀ ⟨w₁, hw₁⟩ = 1 := by rwa [MulEquiv.map_eq_one_iff] at h1
    rw [MulEquiv.map_eq_one_iff] at h2
    exact congrArg Subtype.val h2
  have hx₂0 : x₂ ≠ 0 := by
    intro h0
    apply h₂
    have h1 : D₂.E ⟨w₂, hw₂⟩ = 1 := Multiplicative.toAdd.injective (by rw [← hx₂, h0]; rfl)
    rw [MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  set P := (S.subgroupOf L).map D₂.rho with hP
  have hPfix : ∀ y : ↥W₂, (∀ s ∈ S, s * (y : G) * s⁻¹ = y) →
      ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) D₂.K).mulVec (Multiplicative.toAdd (D₂.E y)) =
        Multiplicative.toAdd (D₂.E y) := by
    intro y hy A hA
    obtain ⟨ℓ, hℓ', rfl⟩ := hA
    have hℓ : (ℓ : G) ∈ S := hℓ'
    rw [← D₂.conj_eq_rho, ← D₂.toAdd_E_conj]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    exact hy _ hℓ
  have hPx₁ : ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) D₂.K).mulVec x₁ = x₁ := by
    refine hPfix _ fun s hs => ?_
    have hsL := hS.1 hs
    have h1 := hψ₀ s hsL ⟨w₁, hw₁⟩
    have h2 : conjAct W₁ ⟨s, hW₁.1 hsL⟩ ⟨w₁, hw₁⟩ = ⟨w₁, hw₁⟩ := by
      apply Subtype.ext
      rw [conjAct_apply_coe]
      exact (hfix s hs).1
    rw [h2] at h1
    exact h1.symm
  have hPx₂ : ∀ A ∈ P, (A : Matrix (Fin 2) (Fin 2) D₂.K).mulVec x₂ = x₂ :=
    hPfix _ fun s hs => (hfix s hs).2
  have hP1 : P ≠ ⊥ := by
    intro hb
    have hsyl := isSylowTwoOf_map_hom' hS D₂.rho
    rw [MonoidHom.range_eq_top_of_surjective _ D₂.rho_surjective, ← hP, hb] at hsyl
    apply hsyl.2.2
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot, Subgroup.card_top,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), D₂.card]
    norm_num
  obtain ⟨c, hc⟩ := fixed_eq_line P hP1 hx₁0 hPx₁ hPx₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hx₂0 hc
  obtain ⟨σc, hσc, hσcL⟩ := D₂.exists_scalar hc0
  let ψ : ↥W₁ ≃* ↥W₂ := ψ₀.trans σc
  have hψw : ψ ⟨w₁, hw₁⟩ = ⟨w₂, hw₂⟩ := by
    apply D₂.E.injective
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (D₂.E (σc (ψ₀ ⟨w₁, hw₁⟩))) = x₂
    rw [hσc, ← hx₁, hc]
  have hψL : ∀ (l : G) (hl : l ∈ L) (w : ↥W₁),
      ((ψ (conjAct W₁ ⟨l, hW₁.1 hl⟩ w) : ↥W₂) : G) = l * ψ w * l⁻¹ := by
    intro l hl w
    show ((σc (ψ₀ (conjAct W₁ ⟨l, hW₁.1 hl⟩ w)) : ↥W₂) : G) = l * σc (ψ₀ w) * l⁻¹
    rw [hψ₀' l hl w]
    exact hσcL l hl (ψ₀ w)
  obtain ⟨V₁, hV₁mem, hV₁le, hV₁⟩ := isNatModCh5_graph hW₁ hW₂ hcomm hdisj ψ hψL
  refine ⟨V₁, ?_, hV₁, isIrrPlusBase_of_isNatModCh5 hV₁ (hV₁le.trans hsup.le)⟩
  have := hV₁mem ⟨w₁, hw₁⟩
  rwa [hψw] at this

end CFSG.Quasithin.H13
