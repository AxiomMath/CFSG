module

public import CFSG.RankThree.GF2n.Smith81.S81QCoreChar
public import CFSG.RankThree.GF2n.Smith81.S81QCoreModel
public import CFSG.RankThree.GF2n.Smith81.S81QTwist
public import CFSG.RankThree.GF2n.Smith81.S81VRankOneCore
public import CFSG.RankThree.GF2n.Smith81.S81VIsoGen

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.S81V


section Twist

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem eAut0Congr_mem_rootRad0_iff (σ : K ≃+* K) (u : ↥(EAut0 K)) :
    ((eAut0Congr σ u : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ∈ rootRad0 K ↔
      (u : W K ≃ₗ[K] W K) ∈ rootRad0 K := by
  have h := map_rootRad0 σ
  have h2 : eAut0Congr σ u ∈ ((rootRad0 K).subgroupOf (EAut0 K)).map (eAut0Congr σ).toMonoidHom ↔
      u ∈ (rootRad0 K).subgroupOf (EAut0 K) :=
    Subgroup.mem_map_iff_mem (f := (eAut0Congr σ).toMonoidHom) (eAut0Congr σ).injective
  rw [h] at h2
  exact h2

theorem eAut0Congr_xt (σ : K ≃+* K) (t : K) : eAut0Congr σ (xt t) = xt (σ t) := by
  have h1 : xt t = ⟨vAut0 K (xuWUnit alphaA2_mem_Perp t),
      vAut0_xuWUnit_mem_EAut0 alphaA2_mem_Perp t⟩ := Subtype.ext (coe_xt t)
  have h2 : xt (σ t) = ⟨vAut0 K (xuWUnit alphaA2_mem_Perp (σ t)),
      vAut0_xuWUnit_mem_EAut0 alphaA2_mem_Perp (σ t)⟩ := Subtype.ext (coe_xt (σ t))
  exact (congrArg (eAut0Congr σ) h1).trans ((eAut0Congr_xuWUnit σ alphaA2_mem_Perp t).trans h2.symm)

theorem eAut0Congr_s (σ : K ≃+* K) : eAut0Congr σ (d6RootDatum K).s = (d6RootDatum K).s := by
  apply Subtype.ext
  rw [coe_eAut0Congr]
  apply LinearEquiv.toLinearMap_injective
  refine (Finsupp.basisSingleOne : Module.Basis Idx0 K (W K)).ext fun a => ?_
  rw [Finsupp.coe_basisSingleOne]
  have h1 : (wMap σ).symm (Finsupp.single a (1 : K)) = Finsupp.single a 1 := by
    rw [wMap_symm_eq, wMap_single, map_one]
  change conjAut σ ((((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K)) (Finsupp.single a 1) =
    (((d6RootDatum K).s : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (Finsupp.single a 1)
  rw [conjAut_apply, h1, d6_s_apply_single, wMap_single, map_one]

variable {X : Type} [AddCommGroup X] [Module K X]

theorem fix0_comp_equiv (Θ : ↥(EAut0 K) ≃* ↥(EAut0 K))
    (hΘ : ∀ u : ↥(EAut0 K), ((Θ u : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ∈ rootRad0 K ↔
      (u : W K ≃ₗ[K] W K) ∈ rootRad0 K) (A : ↥(EAut0 K) →* (X ≃ₗ[K] X)) :
    fix0 (A.comp Θ.toMonoidHom) = fix0 A := by
  ext v
  rw [mem_fix0, mem_fix0]
  constructor
  · intro h u hu
    have h1 := h (Θ.symm u) (by
      rw [← hΘ, MulEquiv.apply_symm_apply]
      exact hu)
    simpa using h1
  · intro h u hu
    exact h _ ((hΘ u).2 hu)

end Twist

section Main

variable {K : Type} [Field K] [CharP K 2] [Finite K] {X : Type} [AddCommGroup X] [Module K X]

set_option maxRecDepth 20000 in
theorem core_main_E4 (hq : 4 ≤ Nat.card K) (hChar : E4StabChar K)
    (hX : Module.finrank K X = 32) (A : ↥(EAut0 K) →* (X ≃ₗ[K] X)) (β : X →ₗ[K] X →ₗ[K] K)
    (hβalt : ∀ v, β v v = 0) (hβA : ∀ g u w, β (A g u) (A g w) = β u w)
    (hline : Module.finrank K (fix0 A) = 1)
    (hspan : ⨆ g : ↥(EAut0 K), (fix0 A).map (A g : X →ₗ[K] X) = ⊤)
    (hV1 : Module.finrank K (V1_0 A β) ≤ 16) :
    ∃ (σ : K ≃+* K) (ψ : X ≃ₗ[K] W K),
      (∀ (g : ↥(EAut0 K)) (v : X),
        ψ (A g v) = ((eAut0Congr σ g : ↥(EAut0 K)) : W K ≃ₗ[K] W K) (ψ v)) ∧
        (fix0 A).map (ψ : X →ₗ[K] W K) = Submodule.span K {p0 K} := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hKn⟩ := FiniteField.card K 2
  have hKcard : Fintype.card K = 2 ^ (n : ℕ) := hKn
  have hq' : 4 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hf2 : 2 ≤ (n : ℕ) := by
    by_contra h
    have : (n : ℕ) ≤ 1 := by omega
    have h1 : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  haveI : FiniteDimensional K X := Module.finite_of_finrank_pos (by omega)
  set R := d6RootDatum K with hR
  set D := R.toRankOne A with hD
  have hfix_ne : fix0 A ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hline
    omega
  obtain ⟨v₀, hv₀, hne⟩ : ∃ v₀ ∈ fix0 A, v₀ ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hfix_ne
  have hfix : D.fix = fix0 A := toRankOne_fix_eq0 A
  obtain ⟨k, hk⟩ := D.exists_char (by rw [hfix]; exact hline) (by rw [hfix]; exact hv₀) hne
  have hsv : A R.s v₀ ∉ fix0 A := sv_D6 A hline hspan (by omega) hv₀ hne
  have hSetup : D.Setup v₀ k :=
    { fix1 := by rw [hfix]; exact hline
      mem := by rw [hfix]; exact hv₀
      ne0 := hne
      sv := by rw [hfix]; exact hsv
      char := hk }
  have hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w := fun n u w => hβA (R.u n) u w
  have hβa : ∀ (g : R.P) u w, β (D.a g u) (D.a g w) = β u w :=
    fun g u w => hβA (g : ↥(EAut0 K)) u w
  have hN15 : Module.finrank K D.N = 15 := d6_finrank_N
  have hV1' : Module.finrank K (D.V1 β) ≤ Module.finrank K D.N + 1 := by
    rw [toRankOne_V1_eq0 A β, hN15]
    omega
  have hbraid := R.toRankOne_braid A
  obtain ⟨i, hR1, -, hchar⟩ :=
    RankOneData.rankOne_normalized hKcard hf2 hSetup hβalt hβρ hβa hV1' hbraid
  let φ : K ≃+* K := iterateFrobeniusEquiv K 2 i
  have hφ : ∀ t : K, φ t = t ^ 2 ^ i := fun t => rfl
  let σ' : K ≃+* K := φ.symm
  have hσ'φ : ∀ t : K, (σ' t) ^ 2 ^ i = t := fun t => by
    rw [← hφ]
    exact φ.apply_symm_apply t
  let Θ : ↥(EAut0 K) ≃* ↥(EAut0 K) := (eAut0Congr φ).symm
  have hΘxt : ∀ t : K, Θ (xt t) = xt (σ' t) := by
    intro t
    apply (eAut0Congr φ).injective
    show eAut0Congr φ ((eAut0Congr φ).symm (xt t)) = _
    rw [MulEquiv.apply_symm_apply, eAut0Congr_xt, φ.apply_symm_apply]
  have hΘs : Θ R.s = R.s := by
    apply (eAut0Congr φ).injective
    show eAut0Congr φ ((eAut0Congr φ).symm R.s) = _
    rw [MulEquiv.apply_symm_apply, eAut0Congr_s]
  have hΘd : ∀ c : Kˣ, Θ (d0Hom K c) = d0Hom K (Units.map (σ' : K →* K) c) := by
    intro c
    apply (eAut0Congr φ).injective
    show eAut0Congr φ ((eAut0Congr φ).symm (d0Hom K c)) = _
    rw [MulEquiv.apply_symm_apply, eAut0Congr_d0Hom]
    congr 1
    ext
    simp [σ']
  have hΘrad : ∀ u : ↥(EAut0 K), ((Θ u : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ∈ rootRad0 K ↔
      (u : W K ≃ₗ[K] W K) ∈ rootRad0 K := by
    intro u
    have h := eAut0Congr_mem_rootRad0_iff φ (Θ u)
    rw [show eAut0Congr φ (Θ u) = u from MulEquiv.apply_symm_apply _ _] at h
    exact h.symm
  let AV : ↥(EAut0 K) →* (X ≃ₗ[K] X) := A.comp Θ.toMonoidHom
  have hAVfix : fix0 AV = fix0 A := fix0_comp_equiv Θ hΘrad A
  have hlineV : Module.finrank K (fix0 AV) = 1 := by rw [hAVfix]; exact hline
  have hv₀V : v₀ ∈ fix0 AV := by rw [hAVfix]; exact hv₀
  have hR1V : ∀ t : K, AV (xt t) (AV R.s v₀) = AV R.s v₀ + t • v₀ := by
    intro t
    have h1 := hR1 (σ' t)
    rw [hσ'φ] at h1
    show A (Θ (xt t)) (A (Θ R.s) v₀) = A (Θ R.s) v₀ + t • v₀
    rw [hΘxt, hΘs]
    exact h1
  have hd : ∀ c : Kˣ, AV (d0Hom K c) v₀ = (c : K) • v₀ := by
    intro c
    have h1 := hchar (Units.map (σ' : K →* K) c)
    have h2 : AV (d0Hom K c) v₀ = A (d0Hom K (Units.map (σ' : K →* K) c)) v₀ := by
      show A (Θ (d0Hom K c)) v₀ = _
      rw [hΘd]
    rw [h2]
    have h3 : D.a (D.d (Units.map (σ' : K →* K) c)) v₀ =
        A (d0Hom K (Units.map (σ' : K →* K) c)) v₀ := by
      show A (((R.d (Units.map (σ' : K →* K) c) : R.P) : ↥(EAut0 K))) v₀ = _
      rw [d6_d_eq_d0Hom]
    rw [← h3, h1]
    congr 1
    exact hσ'φ (c : K)
  have hhom : ∀ g g' : ↥(EAut0 K), ptW0 g = ptW0 g' →
      ∃ c : K, c ≠ 0 ∧ (g : W K ≃ₗ[K] W K) (p0 K) = c • (g' : W K ≃ₗ[K] W K) (p0 K) ∧
        AV g v₀ = c • AV g' v₀ := by
    intro g g' h
    have hmem : (g : W K ≃ₗ[K] W K) (p0 K) ∈ K ∙ (g' : W K ≃ₗ[K] W K) (p0 K) := by
      have := congrArg Subtype.val h
      rw [ptW0_val, ptW0_val] at this
      rw [← this]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact p0_ne_zero ((LinearEquiv.map_eq_zero_iff _).1 hc.symm)
    refine ⟨c, hc0, hc.symm, ?_⟩
    exact hhom_E4 hChar AV hlineV hv₀V hne hd hc0 hc.symm
  have hfixspan : fix0 A = Submodule.span K {v₀} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hv₀
    · rw [hline, finrank_span_singleton hne]
  have hspanV : Submodule.span K (Set.range fun g : ↥(EAut0 K) => AV g v₀) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup_le fun h => ?_
    rw [hfixspan, Submodule.map_span, Set.image_singleton]
    refine Submodule.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨eAut0Congr φ h, ?_⟩
    show A (Θ (eAut0Congr φ h)) v₀ = x
    rw [show Θ (eAut0Congr φ h) = h from MulEquiv.symm_apply_apply _ _]
    exact hx.symm
  have hR1M : ∀ t : K, ((EAut0 K).subtype (xt t)) (((EAut0 K).subtype R.s) (p0 K)) =
      ((EAut0 K).subtype R.s) (p0 K) + t • p0 K := fun t => xt_sp0 t
  have hPi : (PiW K).card ≤ Module.finrank K X := by
    rw [hX]
    exact card_PiW_le
  have hdim : Module.finrank K X ≤ Module.finrank K (W K) := by
    rw [hX, finrank_W32]
  obtain ⟨ψ, hψ, hψv⟩ := iso_of_generation (K := K) (Γ := ↥(EAut0 K)) (M := W K) (V := X)
    (EAut0 K).subtype AV (p0 K) v₀ (Pt := ↥(ptsW K)) ptW0 ColW (PiW K) R.s (fun t => xt t)
    hhom hline_E4 hR1M hR1V ptW0_surjective hGen_E4 hPi hspanV spanW_top0 hdim
  refine ⟨φ, ψ, fun g v => ?_, ?_⟩
  · have h := hψ (eAut0Congr φ g) v
    have hAV : AV (eAut0Congr φ g) = A g := by
      show A (Θ (eAut0Congr φ g)) = A g
      rw [show Θ (eAut0Congr φ g) = g from MulEquiv.symm_apply_apply _ _]
    rw [hAV] at h
    exact h
  · rw [hfixspan, Submodule.map_span, Set.image_singleton]
    exact congrArg (fun v : W K => Submodule.span K {v}) hψv

end Main

end CFSG.RankThree.GF2n.Smith81.D6Spin
