module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eFacts
public import CFSG.Milestones.ASVolI.F48.Rest.U52Model2
public import CFSG.Milestones.ASVolI.F48.Small.AutChartCore
public import CFSG.Milestones.ASVolI.F431.BF436U5A
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieFld

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

section Ext

theorem burnsideF48t_ext_equiv {D E : Type} [Group D] [Group E] [Finite D] [Finite E]
    {X : Subgroup D} {Gp : Subgroup E} [X.Normal] [Gp.Normal] (ε : ↥X ≃* ↥Gp)
    (hcX : Subgroup.centralizer (X : Set D) = ⊥) (hcE : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hAut : Nat.card (MulAut ↥Gp) ≤ Nat.card D) (hDE : Nat.card D ≤ Nat.card E) :
    ∃ θ : D ≃* E, ∀ x : ↥X, θ (x : D) = (ε x : E) := by
  have hρE := burnsideF4d_rho_injective (Gp := Gp) hcE
  have hρX := burnsideF4d_rho_injective (Gp := X) hcX
  let ρD : D →* MulAut ↥Gp := (MulAut.congr ε).toMonoidHom.comp (burnsideF4d_rho X)
  have hρD : Function.Injective ρD := (MulAut.congr ε).injective.comp hρX
  haveI : Finite (MulAut ↥Gp) :=
    Finite.of_injective (fun f : MulAut ↥Gp => (f : ↥Gp → ↥Gp)) DFunLike.coe_injective
  have hEb : Function.Bijective (burnsideF4d_rho Gp) :=
    hρE.bijective_of_nat_card_le (hAut.trans hDE)
  have hDb : Function.Bijective ρD := hρD.bijective_of_nat_card_le hAut
  refine ⟨(MulEquiv.ofBijective ρD hDb).trans (MulEquiv.ofBijective _ hEb).symm, fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
  refine MulEquiv.ext fun y => Subtype.ext ?_
  rw [MulEquiv.ofBijective_apply, MulEquiv.ofBijective_apply, burnsideF4d_rho_apply]
  have hx : (burnsideF4d_rho X (x : D)) (ε.symm y) = x * ε.symm y * x⁻¹ := by
    apply Subtype.ext
    rw [burnsideF4d_rho_apply]
    simp
  show ((ε ((burnsideF4d_rho X (x : D)) (ε.symm y)) : ↥Gp) : E) = _
  rw [hx, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  simp

end Ext

theorem burnsideF48t_u52e_card_mulAut {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4g .U5 2 1 Gp M₁ M₂) : Nat.card (MulAut ↥Gp) ≤ 2 * Nat.card ↥Gp := by
  haveI : Finite E := hyp.finite
  obtain ⟨K, fK, h, Ψ, -, -⟩ := burnsideF4m_U5_chart hyp
  haveI : Finite (hypPSU h 2 1) := Finite.of_equiv _ Ψ.symm.toEquiv
  have hc1 : Nat.card (MulAut ↥Gp) = Nat.card (MulAut (hypPSU h 2 1)) :=
    Nat.card_congr (MulAut.congr Ψ.symm).toEquiv
  have hc2 : Nat.card ↥Gp = Nat.card (hypPSU h 2 1) := Nat.card_congr Ψ.symm.toEquiv
  rw [hc1, hc2]
  let Φ : hypPSU h 2 1 × Bool → MulAut (hypPSU h 2 1) := fun p =>
    MulAut.conj p.1 *
      (if p.2 then CFSG.Quasithin.H13.Sec53F.Unit.fieldP h (CFSG.Quasithin.H13.F431.Un.OL5.bar5 h)
        else 1)
  have hΦ : Function.Surjective Φ := by
    intro α
    obtain ⟨g, σ, hα⟩ := burnsideF4m_u5_normalForm h α
    by_cases hσ : σ = 1
    · refine ⟨(hypProj h 2 1 g, false), ?_⟩
      rw [hα, hσ, map_one, mul_one]
      simp only [Φ, Bool.false_eq_true, if_false, mul_one]
      rfl
    · have hb := CFSG.Quasithin.H13.F431.Un.OL5.fld5_eq_bar h (burnsideF4m_ringEquiv_sq h σ) hσ
      refine ⟨(hypProj h 2 1 g, true), ?_⟩
      rw [hα, hb]
      simp only [Φ, if_true]
      rfl
  have hle := Nat.card_le_card_of_surjective Φ hΦ
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hle
  linarith

section Norm


theorem burnsideF48t_u52e_pA_of_norm {g : Equiv.Perm (Fin 462)}
    (hg : ∀ z ∈ burnsideF48t_u52P1', g⁻¹ * z * g ∈ burnsideF48t_u52P1') :
    g burnsideF48t_u52pA = burnsideF48t_u52pA := by
  have hfix : ∀ z ∈ burnsideF48t_u52P1', z (g burnsideF48t_u52pA) = g burnsideF48t_u52pA := by
    intro z hz
    have h1 := hg z hz
    rw [burnsideF48t_u52_P1'_eq] at h1
    have h2 := MulAction.mem_stabilizer_iff.1 h1.2
    have e : z (g burnsideF48t_u52pA) = g ((g⁻¹ * z * g) burnsideF48t_u52pA) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply g g⁻¹, mul_inv_cancel,
        Equiv.Perm.one_apply]
    rw [Equiv.Perm.smul_def] at h2
    rw [e]
    exact congrArg g h2
  have hS0 : ∀ s ∈ burnsideF48t_u52S0', s ∈ burnsideF48t_u52P1' := by
    intro s hs
    rw [burnsideF48t_u52_P1'_eq]
    exact ⟨burnsideF48t_u52_S0'_le_X hs, MulAction.mem_stabilizer_iff.2 (burnsideF48t_u52_S0'_fix hs).1⟩
  have hσ := burnsideF48t_u52_σ_fix
  by_contra hne
  by_cases hB : g burnsideF48t_u52pA = burnsideF48t_u52pB
  · have := hfix _ (burnsideF48t_u52_σ_mem_P1' (i := 2) (by norm_num))
    rw [hB] at this
    exact hσ.2.2.2.2.2.2.2 this
  · obtain ⟨s, hs, hsx⟩ := burnsideF48t_u52_S0'_moves hne hB
    exact hsx (hfix s (hS0 s hs))

theorem burnsideF48t_u52e_pB_of_norm {g : Equiv.Perm (Fin 462)}
    (hg : ∀ z ∈ burnsideF48t_u52P2', g⁻¹ * z * g ∈ burnsideF48t_u52P2') :
    g burnsideF48t_u52pB = burnsideF48t_u52pB := by
  have hfix : ∀ z ∈ burnsideF48t_u52P2', z (g burnsideF48t_u52pB) = g burnsideF48t_u52pB := by
    intro z hz
    have h1 := hg z hz
    rw [burnsideF48t_u52_P2'_eq] at h1
    have h2 := MulAction.mem_stabilizer_iff.1 h1.2
    have e : z (g burnsideF48t_u52pB) = g ((g⁻¹ * z * g) burnsideF48t_u52pB) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply g g⁻¹, mul_inv_cancel,
        Equiv.Perm.one_apply]
    rw [Equiv.Perm.smul_def] at h2
    rw [e]
    exact congrArg g h2
  have hS0 : ∀ s ∈ burnsideF48t_u52S0', s ∈ burnsideF48t_u52P2' := by
    intro s hs
    rw [burnsideF48t_u52_P2'_eq]
    exact ⟨burnsideF48t_u52_S0'_le_X hs, MulAction.mem_stabilizer_iff.2 (burnsideF48t_u52_S0'_fix hs).2⟩
  have hσ := burnsideF48t_u52_σ_fix
  by_contra hne
  by_cases hA : g burnsideF48t_u52pB = burnsideF48t_u52pA
  · have := hfix _ (burnsideF48t_u52_σ_mem_P2' (i := 3) (Or.inr (Or.inr rfl)))
    rw [hA] at this
    exact hσ.2.2.2.2.2.2.1 this
  · obtain ⟨s, hs, hsx⟩ := burnsideF48t_u52_S0'_moves hA hne
    exact hsx (hfix s (hS0 s hs))

theorem burnsideF48t_u52e_self_P1 : ∀ g : ↥burnsideF48t_u52X,
    (∀ x, x ∈ burnsideF48t_u52P1 ↔ g * x * g⁻¹ ∈ burnsideF48t_u52P1) → g ∈ burnsideF48t_u52P1 := by
  intro g hg
  rw [burnsideF48t_u52_mem_P1_iff]
  refine burnsideF48t_u52e_pA_of_norm fun z hz => ?_
  have hzX := burnsideF48t_u52_P1'_le_X hz
  have h1 : (⟨z, hzX⟩ : ↥burnsideF48t_u52X) ∈ burnsideF48t_u52P1 :=
    (burnsideF48t_u52_mem_P1 _).2 hz
  have h2 := (hg (g⁻¹ * ⟨z, hzX⟩ * g)).2 (by simpa [mul_assoc] using h1)
  exact (burnsideF48t_u52_mem_P1 _).1 h2

theorem burnsideF48t_u52e_self_P2 : ∀ g : ↥burnsideF48t_u52X,
    (∀ x, x ∈ burnsideF48t_u52P2 ↔ g * x * g⁻¹ ∈ burnsideF48t_u52P2) → g ∈ burnsideF48t_u52P2 := by
  intro g hg
  rw [burnsideF48t_u52_mem_P2_iff]
  refine burnsideF48t_u52e_pB_of_norm fun z hz => ?_
  have hzX := burnsideF48t_u52_P2'_le_X hz
  have h1 : (⟨z, hzX⟩ : ↥burnsideF48t_u52X) ∈ burnsideF48t_u52P2 :=
    (burnsideF48t_u52_mem_P2 _).2 hz
  have h2 := (hg (g⁻¹ * ⟨z, hzX⟩ * g)).2 (by simpa [mul_assoc] using h1)
  exact (burnsideF48t_u52_mem_P2 _).1 h2


noncomputable abbrev burnsideF48t_u52eι : ↥burnsideF48t_u52X →* ↥burnsideF48t_u52Xh :=
  Subgroup.inclusion burnsideF48t_u52e_X_le

theorem burnsideF48t_u52e_mem_map_ι {Q : Subgroup ↥burnsideF48t_u52X} (z : ↥burnsideF48t_u52Xh) :
    z ∈ Q.map burnsideF48t_u52eι ↔ ∃ h : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X,
      (⟨z, h⟩ : ↥burnsideF48t_u52X) ∈ Q := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨h, hz⟩
    exact ⟨_, hz, rfl⟩

theorem burnsideF48t_u52e_normalizer_P1 :
    Subgroup.normalizer ((burnsideF48t_u52P1.map burnsideF48t_u52eι : Subgroup ↥burnsideF48t_u52Xh) :
      Set ↥burnsideF48t_u52Xh) = burnsideF48t_u52eP1 := by
  ext g
  rw [Subgroup.mem_normalizer_iff, burnsideF48t_u52e_mem_P1]
  constructor
  · intro hg
    refine burnsideF48t_u52e_pA_of_norm fun z hz => ?_
    have hzX := burnsideF48t_u52_P1'_le_X hz
    have h1 : (⟨z, burnsideF48t_u52e_X_le hzX⟩ : ↥burnsideF48t_u52Xh) ∈
        burnsideF48t_u52P1.map burnsideF48t_u52eι :=
      (burnsideF48t_u52e_mem_map_ι _).2 ⟨hzX, (burnsideF48t_u52_mem_P1 _).2 hz⟩
    have h2 := (hg (g⁻¹ * ⟨z, burnsideF48t_u52e_X_le hzX⟩ * g)).2 (by simpa [mul_assoc] using h1)
    obtain ⟨hX, hP⟩ := (burnsideF48t_u52e_mem_map_ι _).1 h2
    exact (burnsideF48t_u52_mem_P1 _).1 hP
  · intro hg z
    haveI := burnsideF48t_u52e_normal
    rw [burnsideF48t_u52e_mem_map_ι, burnsideF48t_u52e_mem_map_ι]
    have hXiff : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X ↔
        ((g * z * g⁻¹ : ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X := by
      constructor
      · intro h
        exact burnsideF48t_u52e_normal.conj_mem z (show z ∈ burnsideF48t_u52eXs from h) g
      · intro h
        have h' := burnsideF48t_u52e_normal.conj_mem _
          (show g * z * g⁻¹ ∈ burnsideF48t_u52eXs from h) g⁻¹
        have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
        rw [e] at h'
        exact h'
    have hfix : (z : Equiv.Perm (Fin 462)) burnsideF48t_u52pA = burnsideF48t_u52pA ↔
        ((g * z * g⁻¹ : ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) burnsideF48t_u52pA =
          burnsideF48t_u52pA := by
      have hgi : (g : Equiv.Perm (Fin 462))⁻¹ burnsideF48t_u52pA = burnsideF48t_u52pA := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hg.symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hgi]
      constructor
      · intro h
        rw [h, hg]
      · intro h
        have := congrArg (fun o => (g : Equiv.Perm (Fin 462))⁻¹ o) h
        simpa [hgi] using this
    constructor
    · rintro ⟨hX, hP⟩
      exact ⟨hXiff.1 hX, (burnsideF48t_u52_mem_P1_iff _).2
        (hfix.1 ((burnsideF48t_u52_mem_P1_iff _).1 hP))⟩
    · rintro ⟨hX, hP⟩
      exact ⟨hXiff.2 hX, (burnsideF48t_u52_mem_P1_iff _).2
        (hfix.2 ((burnsideF48t_u52_mem_P1_iff _).1 hP))⟩

theorem burnsideF48t_u52e_normalizer_P2 :
    Subgroup.normalizer ((burnsideF48t_u52P2.map burnsideF48t_u52eι : Subgroup ↥burnsideF48t_u52Xh) :
      Set ↥burnsideF48t_u52Xh) = burnsideF48t_u52eP2 := by
  ext g
  rw [Subgroup.mem_normalizer_iff, burnsideF48t_u52e_mem_P2]
  constructor
  · intro hg
    refine burnsideF48t_u52e_pB_of_norm fun z hz => ?_
    have hzX := burnsideF48t_u52_P2'_le_X hz
    have h1 : (⟨z, burnsideF48t_u52e_X_le hzX⟩ : ↥burnsideF48t_u52Xh) ∈
        burnsideF48t_u52P2.map burnsideF48t_u52eι :=
      (burnsideF48t_u52e_mem_map_ι _).2 ⟨hzX, (burnsideF48t_u52_mem_P2 _).2 hz⟩
    have h2 := (hg (g⁻¹ * ⟨z, burnsideF48t_u52e_X_le hzX⟩ * g)).2 (by simpa [mul_assoc] using h1)
    obtain ⟨hX, hP⟩ := (burnsideF48t_u52e_mem_map_ι _).1 h2
    exact (burnsideF48t_u52_mem_P2 _).1 hP
  · intro hg z
    rw [burnsideF48t_u52e_mem_map_ι, burnsideF48t_u52e_mem_map_ι]
    have hXiff : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X ↔
        ((g * z * g⁻¹ : ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52X := by
      constructor
      · intro h
        exact burnsideF48t_u52e_normal.conj_mem z (show z ∈ burnsideF48t_u52eXs from h) g
      · intro h
        have h' := burnsideF48t_u52e_normal.conj_mem _
          (show g * z * g⁻¹ ∈ burnsideF48t_u52eXs from h) g⁻¹
        have e : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
        rw [e] at h'
        exact h'
    have hfix : (z : Equiv.Perm (Fin 462)) burnsideF48t_u52pB = burnsideF48t_u52pB ↔
        ((g * z * g⁻¹ : ↥burnsideF48t_u52Xh) : Equiv.Perm (Fin 462)) burnsideF48t_u52pB =
          burnsideF48t_u52pB := by
      have hgi : (g : Equiv.Perm (Fin 462))⁻¹ burnsideF48t_u52pB = burnsideF48t_u52pB := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact hg.symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hgi]
      constructor
      · intro h
        rw [h, hg]
      · intro h
        have := congrArg (fun o => (g : Equiv.Perm (Fin 462))⁻¹ o) h
        simpa [hgi] using this
    constructor
    · rintro ⟨hX, hP⟩
      exact ⟨hXiff.1 hX, (burnsideF48t_u52_mem_P2_iff _).2
        (hfix.1 ((burnsideF48t_u52_mem_P2_iff _).1 hP))⟩
    · rintro ⟨hX, hP⟩
      exact ⟨hXiff.2 hX, (burnsideF48t_u52_mem_P2_iff _).2
        (hfix.2 ((burnsideF48t_u52_mem_P2_iff _).1 hP))⟩

theorem burnsideF48t_u52e_centralizer :
    Subgroup.centralizer ((burnsideF48t_u52eXs : Subgroup ↥burnsideF48t_u52Xh) :
      Set ↥burnsideF48t_u52Xh) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine burnsideF48t_u52e_comm_eq_one fun g hg => ?_
  have := Subgroup.mem_centralizer_iff.1 hc ⟨g, burnsideF48t_u52e_X_le hg⟩
    (show (⟨g, burnsideF48t_u52e_X_le hg⟩ : ↥burnsideF48t_u52Xh) ∈ burnsideF48t_u52eXs from hg)
  exact (congrArg Subtype.val this).symm

end Norm

section Chart


theorem burnsideF48t_u52e_chart {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 1 Gp M₁ M₂) (hGp : Gp ≠ ⊤) :
    ∃ θ : ↥burnsideF48t_u52Xh ≃* E,
      M₁ ⊓ M₂ = (burnsideF48t_u52eP1 ⊓ burnsideF48t_u52eP2).map θ.toMonoidHom ∧
      ((M₁ = burnsideF48t_u52eP1.map θ.toMonoidHom ∧ M₂ = burnsideF48t_u52eP2.map θ.toMonoidHom) ∨
        (M₁ = burnsideF48t_u52eP2.map θ.toMonoidHom ∧
          M₂ = burnsideF48t_u52eP1.map θ.toMonoidHom)) ∧
      burnsideF48t_u52eXs.map θ.toMonoidHom = Gp := by
  haveI : Finite E := hyp.finite
  haveI := hyp.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := burnsideF48t_u52e_normal
  have hP := burnsideF48_parabolics_of_compat ChF.nativeChartCompatibility hyp
  obtain ⟨ε₀⟩ := burnsideF48t_u52_equiv_X' hyp.model
  obtain ⟨ε, hεB, hε⟩ := burnsideF48t_identify ε₀ burnsideF48t_u52_sylow burnsideF48t_u52_B_eq
    burnsideF48t_u52_P1_ne_P2 burnsideF48t_u52_P1_max burnsideF48t_u52_P2_max hP
  have hcGp : Nat.card ↥Gp = 13685760 := by
    rw [← Nat.card_congr ε.toEquiv, burnsideF48t_u52_card_X]
  have hAut : Nat.card (MulAut ↥Gp) ≤ Nat.card ↥burnsideF48t_u52Xh := by
    have := burnsideF48t_u52e_card_mulAut hyp.toHypF_4_4g
    rw [burnsideF48t_u52e_card_Xh]
    omega
  have hcE : Nat.card ↥burnsideF48t_u52Xh ≤ Nat.card E := by
    have h2 := Subgroup.card_mul_index Gp
    have hi : Gp.index ≠ 1 := fun h => hGp (Subgroup.index_eq_one.1 h)
    have hi0 : Gp.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [burnsideF48t_u52e_card_Xh, ← h2, hcGp]
    have h3 : 2 ≤ Gp.index := by omega
    have := Nat.mul_le_mul_left 13685760 h3
    omega
  let ε' : ↥burnsideF48t_u52eXs ≃* ↥Gp :=
    (Subgroup.subgroupOfEquivOfLe burnsideF48t_u52e_X_le).trans ε
  obtain ⟨θ₀, hθ₀⟩ := burnsideF48t_ext_equiv ε' burnsideF48t_u52e_centralizer
    hyp.centralizer_trivial hAut hcE
  have hθι : ∀ x : ↥burnsideF48t_u52X, θ₀ (burnsideF48t_u52eι x) = ((ε x : ↥Gp) : E) := by
    intro x
    have := hθ₀ ⟨burnsideF48t_u52eι x, x.2⟩
    exact this
  have himg : ∀ Q : Subgroup ↥burnsideF48t_u52X,
      (Q.map burnsideF48t_u52eι).map θ₀.toMonoidHom = burnsideF48_img ε Q := by
    intro Q
    ext y
    rw [burnsideF48_mem_img_iff]
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (hθι x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨burnsideF48t_u52eι x, ⟨x, hx, rfl⟩, hθι x⟩
  have hXs : burnsideF48t_u52eXs = (⊤ : Subgroup ↥burnsideF48t_u52X).map burnsideF48t_u52eι := by
    ext z
    rw [burnsideF48t_u52e_mem_map_ι]
    exact ⟨fun h => ⟨h, Subgroup.mem_top _⟩, fun ⟨h, _⟩ => h⟩
  have hXGp : burnsideF48t_u52eXs.map θ₀.toMonoidHom = Gp := by
    rw [hXs, himg]
    ext y
    rw [burnsideF48_mem_img_iff]
    exact ⟨fun ⟨x, _, hx⟩ => hx ▸ (ε x).2, fun hy => ⟨ε.symm ⟨y, hy⟩, Subgroup.mem_top _, by simp⟩⟩
  have hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h := hyp.split
  have hpar : ∀ (Q : Subgroup ↥burnsideF48t_u52X) (Qhat : Subgroup ↥burnsideF48t_u52Xh)
      (M : Subgroup E),
      (∀ g : ↥burnsideF48t_u52X, (∀ x, x ∈ Q ↔ g * x * g⁻¹ ∈ Q) → g ∈ Q) →
      Subgroup.normalizer ((Q.map burnsideF48t_u52eι : Subgroup ↥burnsideF48t_u52Xh) :
        Set ↥burnsideF48t_u52Xh) = Qhat →
      burnsideF48_img ε Q = Gp ⊓ M → M₁ ⊓ M₂ ≤ M → M = Qhat.map θ₀.toMonoidHom := by
    intro Q Qhat M hself hN hQM hMle
    have h1 := burnsideF48s_autc_eq_normalizer ε hQM hself hsplit hMle
    rw [← hN, Subgroup.map_equiv_normalizer_eq, himg, hQM, ← h1]
  refine ⟨θ₀, ?_, ?_, hXGp⟩
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [Subgroup.map_inf _ _ _ θ₀.injective,
        ← hpar _ _ M₁ burnsideF48t_u52e_self_P1 burnsideF48t_u52e_normalizer_P1 h1 inf_le_left,
        ← hpar _ _ M₂ burnsideF48t_u52e_self_P2 burnsideF48t_u52e_normalizer_P2 h2 inf_le_right]
    · rw [Subgroup.map_inf _ _ _ θ₀.injective,
        ← hpar _ _ M₂ burnsideF48t_u52e_self_P1 burnsideF48t_u52e_normalizer_P1 h1 inf_le_right,
        ← hpar _ _ M₁ burnsideF48t_u52e_self_P2 burnsideF48t_u52e_normalizer_P2 h2 inf_le_left,
        inf_comm]
  · rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hpar _ _ M₁ burnsideF48t_u52e_self_P1 burnsideF48t_u52e_normalizer_P1 h1
        inf_le_left, hpar _ _ M₂ burnsideF48t_u52e_self_P2 burnsideF48t_u52e_normalizer_P2 h2
        inf_le_right⟩
    · exact Or.inr ⟨hpar _ _ M₁ burnsideF48t_u52e_self_P2 burnsideF48t_u52e_normalizer_P2 h2
        inf_le_left, hpar _ _ M₂ burnsideF48t_u52e_self_P1 burnsideF48t_u52e_normalizer_P1 h1
        inf_le_right⟩

end Chart

end CFSG.ASVolI
