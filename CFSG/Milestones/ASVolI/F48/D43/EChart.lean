module

public import CFSG.Milestones.ASVolI.F48.D43.EPar
public import CFSG.Milestones.ASVolI.F48.Rest.U52eChart
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldTriality

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Aut


theorem burnsideF48dE_card_mulAut {H : Type} [Group H] [Finite H]
    (hH : ChF.IsGenLie H .D4tw 3 1) : Nat.card (MulAut H) ≤ 3 * Nat.card H := by
  obtain ⟨-, -, K, _, _, hK, σ, hσ, ⟨ψ⟩⟩ := hH
  have hσb : Function.Bijective σ :=
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
    ⟨RingEquiv.ofBijective σ hσb, RingHom.ext fun _ => rfl⟩
  obtain ⟨Θ, hker, hcard, ⟨χ⟩⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.triality_normalForm_data
      (ℓ := 3) (f := 1) Nat.prime_three le_rfl K (by rw [hK]; rfl) σ' fun c => hσ c
  let e : H ≃* graphFixedRootGroup TwistTag.D4 K σ'.toRingHom := ψ.trans χ
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) := Finite.of_equiv H e.toEquiv
  haveI : Finite (MulAut (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) :=
    Finite.of_injective (fun f : MulAut (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) =>
      (f : graphFixedRootGroup TwistTag.D4 K σ'.toRingHom →
        graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) DFunLike.coe_injective
  haveI : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have h1 : Nat.card (MulAut (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) =
      Nat.card Θ.ker * Nat.card Θ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Θ).toEquiv, mul_comm]
  have h2 : Nat.card Θ.ker ≤ Nat.card (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) := by
    rw [hker]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective MulAut.conj)
  have h3 : Nat.card Θ.range ≤ 3 := by
    have := Subgroup.card_le_card_group Θ.range
    rw [hcard] at this
    simpa using this
  calc Nat.card (MulAut H) = Nat.card (MulAut (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom)) :=
        Nat.card_congr (MulAut.congr e).toEquiv
    _ = Nat.card Θ.ker * Nat.card Θ.range := h1
    _ ≤ Nat.card (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) * 3 := Nat.mul_le_mul h2 h3
    _ = 3 * Nat.card H := by rw [mul_comm, Nat.card_congr e.toEquiv]

end Aut

section Norm


theorem burnsideF48dE_comm_eq_one (hM : burnsideF48d_ModelFacts) {c : Equiv.Perm (Fin 26572)}
    (hc : ∀ g ∈ burnsideF48d_X, c * g = g * c) : c = 1 := by
  have key : ∀ g ∈ burnsideF48d_X, c (g 0) = g (c 0) := by
    intro g hg
    have := congrArg (fun h : Equiv.Perm (Fin 26572) => h 0) (hc g hg)
    simpa only [Equiv.Perm.mul_apply] using this
  have h0 : c 0 = 0 := by
    refine hM.fix_P1 _ fun z hz => ?_
    have h1 := key _ z.2
    rw [(hM.mem_P1 z).1 hz] at h1
    exact h1.symm
  refine Equiv.ext fun p => ?_
  obtain ⟨z, hz⟩ := hM.trans p
  rw [← hz, key _ z.2, h0]
  rfl

theorem burnsideF48dE_centralizer (hM : burnsideF48d_ModelFacts) :
    Subgroup.centralizer ((burnsideF48dE_Xs : Subgroup ↥burnsideF48dE_Xh) :
      Set ↥burnsideF48dE_Xh) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine burnsideF48dE_comm_eq_one hM fun g hg => ?_
  have := Subgroup.mem_centralizer_iff.1 hc ⟨g, burnsideF48dE_X_le hg⟩
    (show (⟨g, burnsideF48dE_X_le hg⟩ : ↥burnsideF48dE_Xh) ∈ burnsideF48dE_Xs from hg)
  exact (congrArg Subtype.val this).symm

theorem burnsideF48dE_conj_apply (g z : Equiv.Perm (Fin 26572)) (p : Fin 26572) :
    (g * z * g⁻¹) (g p) = g (z p) := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, burnsideF48dE_inv_apply_self]

theorem burnsideF48dE_fix0_of_norm (hM : burnsideF48d_ModelFacts) {g : Equiv.Perm (Fin 26572)}
    (hg : ∀ z : ↥burnsideF48d_X, z ∈ burnsideF48d_P1 →
      ((g⁻¹ * (z : Equiv.Perm (Fin 26572)) * g) 0 = 0)) : g 0 = 0 := by
  refine hM.fix_P1 _ fun z hz => ?_
  have h1 := hg z hz
  have e : (z : Equiv.Perm (Fin 26572)) (g 0) = g ((g⁻¹ * (z : Equiv.Perm (Fin 26572)) * g) 0) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply g g⁻¹, mul_inv_cancel,
      Equiv.Perm.one_apply]
  rw [e, h1]

theorem burnsideF48dE_line_of_norm (hM : burnsideF48d_ModelFacts) {g : Equiv.Perm (Fin 26572)}
    (hg : ∀ z : ↥burnsideF48d_X, z ∈ burnsideF48d_P2 →
      g⁻¹ * (z : Equiv.Perm (Fin 26572)) * g ∈ burnsideF48dE_setStab burnsideF48d_line) :
    ∀ p ∈ burnsideF48d_line, g p ∈ burnsideF48d_line := by
  have himg : burnsideF48d_line.image g = burnsideF48d_line := by
    refine hM.inv_P2 _ (Finset.Nonempty.image ⟨0, by decide⟩ _)
      (by rw [Finset.card_image_of_injective _ g.injective]; decide) fun z hz q hq => ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    have h1 := hg z hz p hp
    have e : (z : Equiv.Perm (Fin 26572)) (g p) =
        g ((g⁻¹ * (z : Equiv.Perm (Fin 26572)) * g) p) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply g g⁻¹, mul_inv_cancel,
        Equiv.Perm.one_apply]
    rw [e]
    exact Finset.mem_image_of_mem _ h1
  intro p hp
  rw [← himg]
  exact Finset.mem_image_of_mem _ hp

theorem burnsideF48dE_self_P1 (hM : burnsideF48d_ModelFacts) : ∀ g : ↥burnsideF48d_X,
    (∀ x, x ∈ burnsideF48d_P1 ↔ g * x * g⁻¹ ∈ burnsideF48d_P1) → g ∈ burnsideF48d_P1 := by
  intro g hg
  rw [hM.mem_P1]
  refine burnsideF48dE_fix0_of_norm hM fun z hz => ?_
  have h2 := (hg (g⁻¹ * z * g)).2 (by simpa [mul_assoc] using hz)
  exact (hM.mem_P1 _).1 h2

theorem burnsideF48dE_self_P2 (hM : burnsideF48d_ModelFacts) : ∀ g : ↥burnsideF48d_X,
    (∀ x, x ∈ burnsideF48d_P2 ↔ g * x * g⁻¹ ∈ burnsideF48d_P2) → g ∈ burnsideF48d_P2 := by
  intro g hg
  rw [hM.mem_P2]
  refine burnsideF48dE_line_of_norm hM fun z hz => ?_
  have h2 := (hg (g⁻¹ * z * g)).2 (by simpa [mul_assoc] using hz)
  exact (hM.mem_P2 _).1 h2

theorem burnsideF48dE_X_conj_iff (hM : burnsideF48d_ModelFacts) (g z : ↥burnsideF48dE_Xh) :
    (z : Equiv.Perm (Fin 26572)) ∈ burnsideF48d_X ↔
      ((g * z * g⁻¹ : ↥burnsideF48dE_Xh) : Equiv.Perm (Fin 26572)) ∈ burnsideF48d_X := by
  haveI := burnsideF48dE_normal hM
  constructor
  · intro h
    exact (burnsideF48dE_normal hM).conj_mem z (show z ∈ burnsideF48dE_Xs from h) g
  · intro h
    have h' := (burnsideF48dE_normal hM).conj_mem _ (show g * z * g⁻¹ ∈ burnsideF48dE_Xs from h) g⁻¹
    have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rw [e] at h'
    exact h'

theorem burnsideF48dE_normalizer_P1 (hM : burnsideF48d_ModelFacts) :
    Subgroup.normalizer ((burnsideF48d_P1.map burnsideF48dE_ι : Subgroup ↥burnsideF48dE_Xh) :
      Set ↥burnsideF48dE_Xh) = burnsideF48dE_P1 := by
  ext g
  rw [Subgroup.mem_normalizer_iff, burnsideF48dE_mem_P1 hM]
  constructor
  · intro hg
    refine burnsideF48dE_fix0_of_norm hM fun z hz => ?_
    have h1 : burnsideF48dE_ι z ∈ burnsideF48d_P1.map burnsideF48dE_ι := ⟨z, hz, rfl⟩
    have h2 := (hg (g⁻¹ * burnsideF48dE_ι z * g)).2 (by simpa [mul_assoc] using h1)
    obtain ⟨hX, hP⟩ := (burnsideF48dE_mem_map_ι _).1 h2
    exact (hM.mem_P1 _).1 hP
  · intro hg z
    rw [burnsideF48dE_mem_map_ι, burnsideF48dE_mem_map_ι]
    have hfix : (z : Equiv.Perm (Fin 26572)) 0 = 0 ↔
        ((g * z * g⁻¹ : ↥burnsideF48dE_Xh) : Equiv.Perm (Fin 26572)) 0 = 0 := by
      have e := burnsideF48dE_conj_apply (g : Equiv.Perm (Fin 26572)) z 0
      rw [hg] at e
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [e]
      constructor
      · intro h
        rw [h, hg]
      · intro h
        exact (g : Equiv.Perm (Fin 26572)).injective (h.trans hg.symm)
    constructor
    · rintro ⟨hX, hP⟩
      exact ⟨(burnsideF48dE_X_conj_iff hM g z).1 hX,
        (hM.mem_P1 _).2 (hfix.1 ((hM.mem_P1 _).1 hP))⟩
    · rintro ⟨hX, hP⟩
      exact ⟨(burnsideF48dE_X_conj_iff hM g z).2 hX,
        (hM.mem_P1 _).2 (hfix.2 ((hM.mem_P1 _).1 hP))⟩

theorem burnsideF48dE_normalizer_P2 (hM : burnsideF48d_ModelFacts) :
    Subgroup.normalizer ((burnsideF48d_P2.map burnsideF48dE_ι : Subgroup ↥burnsideF48dE_Xh) :
      Set ↥burnsideF48dE_Xh) = burnsideF48dE_P2 := by
  ext g
  rw [Subgroup.mem_normalizer_iff, burnsideF48dE_mem_P2 hM]
  constructor
  · intro hg
    refine burnsideF48dE_line_of_norm hM fun z hz => ?_
    have h1 : burnsideF48dE_ι z ∈ burnsideF48d_P2.map burnsideF48dE_ι := ⟨z, hz, rfl⟩
    have h2 := (hg (g⁻¹ * burnsideF48dE_ι z * g)).2 (by simpa [mul_assoc] using h1)
    obtain ⟨hX, hP⟩ := (burnsideF48dE_mem_map_ι _).1 h2
    exact (hM.mem_P2 _).1 hP
  · intro hg z
    rw [burnsideF48dE_mem_map_ι, burnsideF48dE_mem_map_ι]
    have hgS : (g : Equiv.Perm (Fin 26572)) ∈ burnsideF48dE_setStab burnsideF48d_line := hg
    have hline : (z : Equiv.Perm (Fin 26572)) ∈ burnsideF48dE_setStab burnsideF48d_line ↔
        ((g * z * g⁻¹ : ↥burnsideF48dE_Xh) : Equiv.Perm (Fin 26572)) ∈
          burnsideF48dE_setStab burnsideF48d_line := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · intro h
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgS h) (Subgroup.inv_mem _ hgS)
      · intro h
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgS) h) hgS
        rwa [show (g : Equiv.Perm (Fin 26572))⁻¹ * ((g : Equiv.Perm (Fin 26572)) *
          (z : Equiv.Perm (Fin 26572)) * (g : Equiv.Perm (Fin 26572))⁻¹) *
            (g : Equiv.Perm (Fin 26572)) = z by group] at this
    constructor
    · rintro ⟨hX, hP⟩
      exact ⟨(burnsideF48dE_X_conj_iff hM g z).1 hX,
        (hM.mem_P2 _).2 (hline.1 ((hM.mem_P2 _).1 hP))⟩
    · rintro ⟨hX, hP⟩
      exact ⟨(burnsideF48dE_X_conj_iff hM g z).2 hX,
        (hM.mem_P2 _).2 (hline.2 ((hM.mem_P2 _).1 hP))⟩

end Norm

section Chart


theorem burnsideF48dE_card_E (hM : burnsideF48d_ModelFacts) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .D4tw 3 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤)
    (ε' : ↥burnsideF48dE_Xs ≃* ↥Gp) :
    Nat.card (MulAut ↥Gp) = Nat.card ↥burnsideF48dE_Xh ∧
      Nat.card ↥burnsideF48dE_Xh = Nat.card E := by
  haveI : Finite E := hyp.finite
  haveI := hyp.normal
  haveI := burnsideF48dE_normal hM
  have hcGp : Nat.card ↥Gp = 20560831566912 := by
    rw [← Nat.card_congr ε'.toEquiv, burnsideF48dE_card_Xs hM]
  haveI : Finite (MulAut ↥Gp) :=
    Finite.of_injective (fun f : MulAut ↥Gp => (f : ↥Gp → ↥Gp)) DFunLike.coe_injective
  have hle : Nat.card (MulAut ↥Gp) ≤ Nat.card ↥burnsideF48dE_Xh := by
    rw [burnsideF48dE_card_Xh hM]
    have := burnsideF48dE_card_mulAut hyp.model
    omega
  have hge : Nat.card ↥burnsideF48dE_Xh ≤ Nat.card (MulAut ↥Gp) := by
    have hρX := burnsideF4d_rho_injective (Gp := burnsideF48dE_Xs) (burnsideF48dE_centralizer hM)
    exact Nat.card_le_card_of_injective _ ((MulAut.congr ε').injective.comp hρX)
  have hAut : Nat.card (MulAut ↥Gp) = Nat.card ↥burnsideF48dE_Xh := le_antisymm hle hge
  refine ⟨hAut, ?_⟩
  have hρE := burnsideF4d_rho_injective (Gp := Gp) hyp.centralizer_trivial
  have hdvd : Nat.card E ∣ Nat.card (MulAut ↥Gp) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hρE).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hAut, burnsideF48dE_card_Xh hM] at hdvd
  have h2 := Subgroup.card_mul_index Gp
  have hi : Gp.index ≠ 1 := fun h => hGp (Subgroup.index_eq_one.1 h)
  rw [hcGp] at h2
  rw [← h2] at hdvd ⊢
  rw [burnsideF48dE_card_Xh hM]
  have h3 : Gp.index ∣ 3 := by
    have : 20560831566912 * Gp.index ∣ 20560831566912 * 3 := by
      rw [show (20560831566912 : ℕ) * 3 = 61682494700736 by norm_num]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have h4 : Gp.index = 3 := ((Nat.dvd_prime Nat.prime_three).1 h3).resolve_left hi
  rw [h4]

theorem burnsideF48dE_chart (hM : burnsideF48d_ModelFacts) {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 .D4tw 3 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
    ∃ θ : ↥burnsideF48dE_Xh ≃* E,
      M₁ ⊓ M₂ = (burnsideF48dE_P1 ⊓ burnsideF48dE_P2).map θ.toMonoidHom ∧
      ((M₁ = burnsideF48dE_P1.map θ.toMonoidHom ∧ M₂ = burnsideF48dE_P2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48dE_P2.map θ.toMonoidHom ∧ M₂ = burnsideF48dE_P1.map θ.toMonoidHom)) ∧
      burnsideF48dE_Xs.map θ.toMonoidHom = Gp := by
  haveI : Finite E := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := burnsideF48dE_normal hM
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := hM.equiv_X ↥Gp hyp.model
  obtain ⟨ε, hεB, hε⟩ := burnsideF48t_identify ε₀ hM.sylow hM.B_eq hM.P1_ne_P2 hM.P1_max
    hM.P2_max hP
  let ε' : ↥burnsideF48dE_Xs ≃* ↥Gp :=
    (Subgroup.subgroupOfEquivOfLe burnsideF48dE_X_le).trans ε
  obtain ⟨hAut, hcE⟩ := burnsideF48dE_card_E hM hyp hGp ε'
  obtain ⟨θ₀, hθ₀⟩ := burnsideF48t_ext_equiv ε' (burnsideF48dE_centralizer hM)
    hyp.centralizer_trivial hAut.le hcE.le
  have hθι : ∀ x : ↥burnsideF48d_X, θ₀ (burnsideF48dE_ι x) = ((ε x : ↥Gp) : E) := by
    intro x
    exact hθ₀ ⟨burnsideF48dE_ι x, x.2⟩
  have himg : ∀ Q : Subgroup ↥burnsideF48d_X,
      (Q.map burnsideF48dE_ι).map θ₀.toMonoidHom = burnsideF48_img ε Q := by
    intro Q
    ext y
    rw [burnsideF48_mem_img_iff]
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hθι x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨burnsideF48dE_ι x, ⟨x, hx, rfl⟩, hθι x⟩
  have hXs : burnsideF48dE_Xs = (⊤ : Subgroup ↥burnsideF48d_X).map burnsideF48dE_ι := by
    ext z
    rw [burnsideF48dE_mem_map_ι]
    exact ⟨fun h => ⟨h, Subgroup.mem_top _⟩, fun ⟨h, _⟩ => h⟩
  have hXGp : burnsideF48dE_Xs.map θ₀.toMonoidHom = Gp := by
    rw [hXs, himg]
    ext y
    rw [burnsideF48_mem_img_iff]
    exact ⟨fun ⟨x, _, hx⟩ => hx ▸ (ε x).2, fun hy => ⟨ε.symm ⟨y, hy⟩, Subgroup.mem_top _, by simp⟩⟩
  have hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h := hyp.split
  have hpar : ∀ (Q : Subgroup ↥burnsideF48d_X) (Qhat : Subgroup ↥burnsideF48dE_Xh)
      (M : Subgroup E),
      (∀ g : ↥burnsideF48d_X, (∀ x, x ∈ Q ↔ g * x * g⁻¹ ∈ Q) → g ∈ Q) →
      Subgroup.normalizer ((Q.map burnsideF48dE_ι : Subgroup ↥burnsideF48dE_Xh) :
        Set ↥burnsideF48dE_Xh) = Qhat →
      burnsideF48_img ε Q = Gp ⊓ M → M₁ ⊓ M₂ ≤ M → M = Qhat.map θ₀.toMonoidHom := by
    intro Q Qhat M hself hN hQM hMle
    have h1 := burnsideF48s_autc_eq_normalizer ε hQM hself hsplit hMle
    rw [← hN, Subgroup.map_equiv_normalizer_eq, himg, hQM, ← h1]
  refine ⟨θ₀, ?_, ?_, hXGp⟩
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Subgroup.map_inf _ _ _ θ₀.injective,
        ← hpar _ _ M₁ (burnsideF48dE_self_P1 hM) (burnsideF48dE_normalizer_P1 hM) h1 inf_le_left,
        ← hpar _ _ M₂ (burnsideF48dE_self_P2 hM) (burnsideF48dE_normalizer_P2 hM) h2 inf_le_right]
    · rw [Subgroup.map_inf _ _ _ θ₀.injective,
        ← hpar _ _ M₂ (burnsideF48dE_self_P1 hM) (burnsideF48dE_normalizer_P1 hM) h1 inf_le_right,
        ← hpar _ _ M₁ (burnsideF48dE_self_P2 hM) (burnsideF48dE_normalizer_P2 hM) h2 inf_le_left,
        inf_comm]
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hpar _ _ M₁ (burnsideF48dE_self_P1 hM) (burnsideF48dE_normalizer_P1 hM) h1
        inf_le_left, hpar _ _ M₂ (burnsideF48dE_self_P2 hM) (burnsideF48dE_normalizer_P2 hM) h2
        inf_le_right⟩
    · exact Or.inr ⟨hpar _ _ M₁ (burnsideF48dE_self_P2 hM) (burnsideF48dE_normalizer_P2 hM) h2
        inf_le_left, hpar _ _ M₂ (burnsideF48dE_self_P1 hM) (burnsideF48dE_normalizer_P1 hM) h1
        inf_le_right⟩

end Chart

end CFSG.ASVolI
