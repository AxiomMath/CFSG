module

public import CFSG.Quasithin.Vol2.Ch11SecAKDh
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.C10KH

open CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit Matrix

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem finite_ringAut : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)

@[expose] def gComp (hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K) (t : K) :
    ↥⁅quasithinG2 K, quasithinG2 K⁆ :=
  ⟨(g2A (compSL t) : ↥(cayleyGroup K)), by rw [hc]; exact (g2A (compSL t)).2⟩

omit [Finite K] in
theorem center_g2D_eq_bot (hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K) {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) : Subgroup.center ↥⁅quasithinG2 K, quasithinG2 K⁆ = ⊥ := by
  have h := Subgroup.map_center_eq (MulEquiv.subgroupCongr hc)
  rw [CFSG.Quasithin.A318Excl.center_cayleyGroup_eq_bot hc0 hc1] at h
  rw [eq_bot_iff]
  intro z hz
  have hz' : MulEquiv.subgroupCongr hc z ∈ (⊥ : Subgroup ↥(cayleyGroup K)) :=
    h ▸ Subgroup.mem_map_of_mem _ hz
  rw [Subgroup.mem_bot] at hz' ⊢
  exact (MulEquiv.subgroupCongr hc).injective (hz'.trans (map_one _).symm)

omit [Finite K] in
theorem eq_of_conj_mul_zeta (hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K) {c₀ : K}
    (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {c c' : ↥⁅quasithinG2 K, quasithinG2 K⁆} {σ τ : K ≃+* K}
    (h : MulAut.conj c * CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv σ =
      MulAut.conj c' * CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv τ) : c = c' ∧ σ = τ := by
  have hστ : σ = τ := by
    refine RingEquiv.ext fun t => ?_
    have h1 := congrArg (fun α : MulAut ↥⁅quasithinG2 K, quasithinG2 K⁆ =>
      trO ((α (gComp hc t) : ↥⁅quasithinG2 K, quasithinG2 K⁆) :
        quasithinZorn K ≃ₗ[K] quasithinZorn K)) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      trO_conj] at h1
    rw [CFSG.Quasithin.H13.VolI.coe_g2DerivedFieldEquiv,
      CFSG.Quasithin.H13.VolI.coe_g2DerivedFieldEquiv] at h1
    change trO (zornConj σ ((g2A (compSL t) : ↥(cayleyGroup K)) :
        quasithinZorn K ≃ₗ[K] quasithinZorn K)) =
      trO (zornConj τ ((g2A (compSL t) : ↥(cayleyGroup K)) :
        quasithinZorn K ≃ₗ[K] quasithinZorn K)) at h1
    rwa [zornConj_g2A_comp, zornConj_g2A_comp, trO_g2A_comp, trO_g2A_comp] at h1
  subst hστ
  refine ⟨?_, rfl⟩
  have h2 : MulAut.conj c = MulAut.conj c' := mul_right_cancel h
  have hz : c'⁻¹ * c ∈ Subgroup.center ↥⁅quasithinG2 K, quasithinG2 K⁆ := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 := congrArg (fun α : MulAut ↥⁅quasithinG2 K, quasithinG2 K⁆ => α g) h2
    simp only [MulAut.conj_apply] at h3
    calc g * (c'⁻¹ * c) = c'⁻¹ * (c' * g * c'⁻¹) * c := by group
      _ = c'⁻¹ * (c * g * c⁻¹) * c := by rw [h3]
      _ = c'⁻¹ * c * g := by group
  rw [center_g2D_eq_bot hc hc0 hc1, Subgroup.mem_bot, inv_mul_eq_one] at hz
  exact hz.symm

end G2

section Card

variable {K : Type} [Field K] [Finite K] [CharP K 2]


open CFSG.Blueprint.Chevalley in
theorem card_mulAut_g2_le {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K) :
    Nat.card (MulAut ↥⁅quasithinG2 K, quasithinG2 K⁆) ≤
      Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ * Nat.card (K ≃+* K) := by
  have : Finite (K ≃+* K) := finite_ringAut
  obtain ⟨e₁⟩ := B42G2Id.nonempty_cayleyGroup_mulEquiv_adjointQuotient hK hn
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let ψ : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥(adjointGroup .G2 K) :=
    (MulEquiv.subgroupCongr hc).trans (e₁.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
  have : Finite ↥(adjointGroup .G2 K) := Finite.of_equiv _ ψ.toEquiv
  have hnf := (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
    hn K hK).1
  let F : MulAut ↥(adjointGroup .G2 K) → ↥(adjointGroup .G2 K) × (K ≃+* K) :=
    fun α => (hnf α).exists.choose
  have key : ∀ (γ : MulAut ↥(adjointGroup .G2 K)) (h : ↥(adjointGroup .G2 K)),
      ((γ h : ↥(adjointGroup .G2 K)) : ModGL .G2 K) = ((F γ).1 : ModGL .G2 K) *
        Units.map (entrywiseHom (F γ).2.toRingHom) (h : ModGL .G2 K) *
          ((F γ).1 : ModGL .G2 K)⁻¹ :=
    fun γ h => (hnf γ).exists.choose_spec h
  have hF : Function.Injective F := by
    intro α β hαβ
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [key α h, key β h, hαβ]
  calc Nat.card (MulAut ↥⁅quasithinG2 K, quasithinG2 K⁆)
      = Nat.card (MulAut ↥(adjointGroup .G2 K)) := Nat.card_congr (MulAut.congr ψ).toEquiv
    _ ≤ Nat.card (↥(adjointGroup .G2 K) × (K ≃+* K)) := Nat.card_le_card_of_injective F hF
    _ = Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ * Nat.card (K ≃+* K) := by
      rw [Nat.card_prod, Nat.card_congr ψ.toEquiv]

theorem indM_g2_eq_top {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    indM (g2QA K) = ⊤ := by
  have : Finite (K ≃+* K) := finite_ringAut
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨c₀, hc0, hc1⟩ := Vol2.KGNat.exists_ne_zero_ne_one (K := K) (by rw [hK]; omega)
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = cayleyGroup K := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      cayley_commutator_eq hc0 hc1]
  have : Finite (MulAut ↥⁅quasithinG2 K, quasithinG2 K⁆) := MulEquiv.finite_left
  refine Subgroup.eq_top_of_le_card _ ((card_mulAut_g2_le hn hK hc).trans ?_)
  let F : ↥⁅quasithinG2 K, quasithinG2 K⁆ × (K ≃+* K) → ↥(indM (g2QA K)) := fun p =>
    ⟨MulAut.conj p.1 * CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv p.2,
      mul_mem (conj_mem_indM _ _) (zeta_mem_indM _)⟩
  have hF : Function.Injective F := by
    rintro ⟨c, σ⟩ ⟨c', τ⟩ h
    obtain ⟨h1, h2⟩ := eq_of_conj_mul_zeta hc hc0 hc1 (congrArg Subtype.val h)
    exact Prod.ext h1 h2
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective F hF

end Card

end CFSG.Quasithin.Vol2.Ch11.SecA.C10KH
