module

public import CFSG.RankThree.GF2n.Smith81.S81ZCoreChar
public import CFSG.RankThree.GF2n.Smith81.S81ZCoreModel
public import CFSG.RankThree.GF2n.Smith81.S81ZTrRD
public import CFSG.RankThree.GF2n.Smith81.S81VRankOneCore
public import CFSG.RankThree.GF2n.Smith81.S81VIsoGen

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81V CFSG.RankThree.GF2n.Smith81.S81Z.Tr


section Aux

variable {K : Type} [Field K] [CharP K 2]

theorem twistGp_symm_twistGp (σ : K ≃+* K) (g : Gp K) : twistGp σ.symm (twistGp σ g) = g :=
  Subtype.ext (twistUnits_symm_twistUnits σ g.1)

theorem twistGp_twistGp_symm (σ : K ≃+* K) (g : Gp K) : twistGp σ (twistGp σ.symm g) = g :=
  Subtype.ext (twistUnits_twistUnits_symm σ g.1)

theorem twistGp_mem_UA_iff (σ : K ≃+* K) (g : Gp K) : twistGp σ g ∈ UA K a7 ↔ g ∈ UA K a7 := by
  have h := twistGp_UA σ
  have h2 : twistGp σ g ∈ (UA K a7).map (twistGp σ).toMonoidHom ↔ g ∈ UA K a7 :=
    Subgroup.mem_map_iff_mem (f := (twistGp σ).toMonoidHom) (twistGp σ).injective
  rwa [h] at h2

variable {X : Type} [AddCommGroup X] [Module K X]

theorem fix7_twist (σ : K ≃+* K) (A : Gp K →* (X ≃ₗ[K] X)) :
    fix7 (A.comp (twistGp σ).toMonoidHom) = fix7 A := by
  ext v
  rw [mem_fix7, mem_fix7]
  constructor
  · intro h u hu
    have := h (twistGp σ.symm u) ((twistGp_mem_UA_iff σ.symm u).2 hu)
    simpa [twistGp_twistGp_symm] using this
  · intro h u hu
    exact h _ ((twistGp_mem_UA_iff σ u).2 hu)

theorem toRankOne_X (A : Gp K →* (X ≃ₗ[K] X)) (t : K) :
    ((rootDatumE7 K).toRankOne A).X t = A (xE alpha7 t) := by
  show A (uN (t • (n1N : NU K))) = _
  congr 1
  have : t • (n1N : NU K) = Pi.single (⟨alpha7, alpha7_mem⟩ : ↥(Phi a7)) t := by
    funext δ
    by_cases h : δ = (⟨alpha7, alpha7_mem⟩ : ↥(Phi a7))
    · subst h
      simp [n1N]
    · simp [n1N, Pi.single_apply, h]
  rw [this, uN_single]

end Aux

section Main

variable {K : Type} [Field K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X]

set_option maxRecDepth 20000 in
theorem core_main_E5 [Finite K] (hq : 4 ≤ Nat.card K) (hChar : E5StabChar K)
    (hX : Module.finrank K X = 56) (A : Gp K →* (X ≃ₗ[K] X)) (β : X →ₗ[K] X →ₗ[K] K)
    (hβalt : ∀ v, β v v = 0) (hβA : ∀ g u w, β (A g u) (A g w) = β u w)
    (hline : Module.finrank K (fix7 A) = 1)
    (hspan : ⨆ g : Gp K, (fix7 A).map (A g : X →ₗ[K] X) = ⊤)
    (hV1 : Module.finrank K (V17 A β) ≤ 28) :
    ∃ (σ : K ≃+* K) (ψ : X ≃ₗ[K] V K),
      (∀ (g : Gp K) (v : X), ψ (A g v) = endoE (twistGp σ g) (ψ v)) ∧
        (fix7 A).map (ψ : X →ₗ[K] V K) = Submodule.span K {(w0 : V K)} := by
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
  set R := rootDatumE7 K with hR
  set D := R.toRankOne A with hD
  have hfix_ne : fix7 A ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hline
    omega
  obtain ⟨v₀, hv₀, hne⟩ : ∃ v₀ ∈ fix7 A, v₀ ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hfix_ne
  have hfix : D.fix = fix7 A := toRankOne_fix_eq A
  obtain ⟨k, hk⟩ := D.exists_char (by rw [hfix]; exact hline) (by rw [hfix]; exact hv₀) hne
  have hsv : A (sN K) v₀ ∉ fix7 A := sv_E7 A hline hspan (by omega) hv₀ hne
  have hSetup : D.Setup v₀ k :=
    { fix1 := by rw [hfix]; exact hline
      mem := by rw [hfix]; exact hv₀
      ne0 := hne
      sv := by rw [hfix]; exact hsv
      char := hk }
  have hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w := fun n u w => hβA (R.u n) u w
  have hβa : ∀ (g : R.P) u w, β (D.a g u) (D.a g w) = β u w :=
    fun g u w => hβA (g : Gp K) u w
  have hN27 : Module.finrank K D.N = 27 := by
    show Module.finrank K (NU K) = 27
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    exact phi7_card
  have hV1' : Module.finrank K (D.V1 β) ≤ Module.finrank K D.N + 1 := by
    rw [toRankOne_V1_eq A β, hN27]
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
  let AV : Gp K →* (X ≃ₗ[K] X) := A.comp (twistGp σ').toMonoidHom
  have hAVfix : fix7 AV = fix7 A := fix7_twist σ' A
  have hlineV : Module.finrank K (fix7 AV) = 1 := by rw [hAVfix]; exact hline
  have hv₀V : v₀ ∈ fix7 AV := by rw [hAVfix]; exact hv₀
  have hR1V : ∀ t : K, AV (xE alpha7 t) (AV (sN K) v₀) = AV (sN K) v₀ + t • v₀ := by
    intro t
    have h1 := hR1 (σ' t)
    rw [hσ'φ, toRankOne_X] at h1
    show A (twistGp σ' (xE alpha7 t)) (A (twistGp σ' (sN K)) v₀) = A (twistGp σ' (sN K)) v₀ + t • v₀
    rw [twistGp_xE, twistGp_sN]
    exact h1
  have hd : ∀ c : Kˣ, AV (e7Data_valid.hm K nodeA c) v₀ = (c : K) • v₀ := by
    intro c
    have h1 := hchar (Units.map (σ' : K →* K) c)
    have h2 : AV (e7Data_valid.hm K nodeA c) v₀ = A (e7Data_valid.hm K nodeA (Units.map (σ' : K →* K) c)) v₀ := by
      show A (twistGp σ' (e7Data_valid.hm K nodeA c)) v₀ = _
      rw [twistGp_hm]
    rw [h2]
    have h3 : D.a (D.d (Units.map (σ' : K →* K) c)) v₀ =
        A (e7Data_valid.hm K nodeA (Units.map (σ' : K →* K) c)) v₀ := rfl
    rw [← h3, h1]
    congr 1
    exact hσ'φ (c : K)
  have hhom : ∀ g g' : Gp K, ptE g = ptE g' →
      ∃ c : K, c ≠ 0 ∧ ιV K g (w0 : V K) = c • ιV K g' (w0 : V K) ∧ AV g v₀ = c • AV g' v₀ := by
    intro g g' h
    have hmem : endoE g (w0 : V K) ∈ K ∙ endoE g' (w0 : V K) := by
      have := congrArg Subtype.val h
      rw [ptE_val, ptE_val] at this
      rw [← this]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      have h0 : endoE g (w0 : V K) = 0 := hc.symm
      apply w0_ne_zero (K := K)
      have := endoE_inv_endoE g (w0 : V K)
      rw [h0, map_zero] at this
      exact this.symm
    refine ⟨c, hc0, hc.symm, ?_⟩
    exact hhom_E5 hChar AV hlineV hv₀V hne hd hc0 hc.symm
  have hfixspan : fix7 A = Submodule.span K {v₀} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hv₀
    · rw [hline, finrank_span_singleton hne]
  have hspanV : Submodule.span K (Set.range fun g : Gp K => AV g v₀) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup_le fun h => ?_
    rw [hfixspan, Submodule.map_span, Set.image_singleton]
    refine Submodule.span_mono ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    refine ⟨twistGp σ'.symm h, ?_⟩
    show A (twistGp σ' (twistGp σ'.symm h)) v₀ = x
    rw [twistGp_twistGp_symm]
    exact hx.symm
  have hR1M : ∀ t : K, ιV K (xE alpha7 t) (ιV K (sN K) (w0 : V K)) =
      ιV K (sN K) (w0 : V K) + t • (w0 : V K) := fun t => endoE_xE_alpha7_sw0 t
  have hspanM : Submodule.span K (Set.range fun g : Gp K => ιV K g (w0 : V K)) = ⊤ := spanM_top
  have hPi : (PiE K).card ≤ Module.finrank K X := by
    rw [hX]
    exact card_PiE_le
  have hdim : Module.finrank K X ≤ Module.finrank K (V K) := by
    rw [hX, finrank_V56]
  obtain ⟨ψ, hψ, hψv⟩ := iso_of_generation (K := K) (Γ := Gp K) (M := V K) (V := X)
    (ιV K) AV (w0 : V K) v₀ (Pt := ↥(ptsE K)) ptE ColE (PiE K) (sN K) (fun t => xE alpha7 t)
    hhom hline_E7 hR1M hR1V ptE_surjective hGen_E7 hPi hspanV hspanM hdim
  refine ⟨φ, ψ, fun g v => ?_, ?_⟩
  · have h := hψ (twistGp φ g) v
    have hAV : AV (twistGp φ g) = A g := by
      show A (twistGp σ' (twistGp φ g)) = A g
      rw [show σ' = φ.symm from rfl, twistGp_symm_twistGp]
    rw [hAV] at h
    exact h
  · rw [hfixspan, Submodule.map_span, Set.image_singleton]
    exact congrArg (fun v : V K => Submodule.span K {v}) hψv

end Main

end CFSG.RankThree.GF2n.Smith81.S81Z
