module

public import CFSG.RankThree.GF2n.Stroth80.Sec717RepInputs
public import CFSG.RankThree.GF2n.Stroth80.Sec717RepLinAlg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

namespace Sec717RepInputs

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {B : LinearMap.BilinForm K E} {Qf : E → K} {φ : X →* (E ≃ₗ[K] E)}
  {V L Nb Rb : Subgroup X} {T : Submodule K E}

theorem quad (I : Sec717RepInputs B Qf φ V L Nb Rb T) :
    ∀ s ∈ L, ∀ u ∈ L, ∀ w, opm (φ s) (opm (φ u) w) = 0 := by
  intro s hs u hu w
  apply I.layer.nondeg.1
  intro e
  have hiso := I.layer.isom s (opm (φ u) w) e
  have h1 : B (opm (φ s) (opm (φ u) w)) e =
      -(B (opm (φ u) w) (opm (φ s) e) + B (opm (φ s) (opm (φ u) w)) (opm (φ s) e)) := by
    simp only [opm_apply, map_sub, LinearMap.sub_apply] at hiso ⊢
    rw [← hiso]
    ring
  rw [h1, I.quadIso u hu s hs, I.quadIso s hs s hs, add_zero, neg_zero]

theorem isLayerCorner_of_mapsTo (I : Sec717RepInputs B Qf φ V L Nb Rb T) {n : X}
    (h : ∀ e, opm (φ n) e ∈ T) : IsLayerCorner T (B.orthogonal T) (opm (φ n)) := by
  have hrange : LinearMap.range (opm (φ n)) ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact h x
  have hker : B.orthogonal T ≤ LinearMap.ker (opm (φ n)) := by
    rw [ker_opm_eq_orthogonal_range B I.layer.nondeg I.layer.refl (φ n) (I.layer.isom n)]
    exact LinearMap.BilinForm.orthogonal_le hrange
  exact ⟨h, fun x hx => hker hx⟩

theorem opm_inv_of_sq {g : E ≃ₗ[K] E} (hg : ∀ v, opm g (opm g v) = 0) (v : E) :
    opm g⁻¹ v = -opm g v := by
  have h1 : g (v - opm g v) = v := by
    have e : opm g (opm g v) = g (opm g v) - opm g v := opm_apply g _
    rw [hg v] at e
    have e2 : g (opm g v) = opm g v := (sub_eq_zero.mp e.symm)
    rw [map_sub, e2, opm_apply]
    abel
  have h2 : g⁻¹ v = v - opm g v := by
    rw [← h1, linearEquiv_inv_apply_apply]
    rw [h1]
  rw [opm_apply, h2]
  abel

theorem transvection (I : Sec717RepInputs B Qf φ V L Nb Rb T) :
    ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
      ∀ a ∈ V, ∀ b ∈ V, ∀ x ∈ L, ⁅g * a * g⁻¹, ⁅x, g * b * g⁻¹⁆⁆ ∈ V := by
  intro g hR _ a ha b hb x hx
  by_cases ha1 : a = 1
  · subst ha1
    have e : g * 1 * g⁻¹ = 1 := by group
    rw [e, commutatorElement_one_left]
    exact V.one_mem
  obtain ⟨β, hβ⟩ := (I.root_conj g ha ha1).1 b hb
  have hΨΨ : ∀ v, opm (φ (g * a * g⁻¹)) (opm (φ (g * a * g⁻¹)) v) = 0 := I.opm_conj_sq g ha
  set ya := g * a * g⁻¹ with hya
  set yb := g * b * g⁻¹ with hyb
  set Ψ := opm (φ ya) with hΨ
  have hyaR : ya ∈ Rb := hR a ha
  have hybR : yb ∈ Rb := hR b hb
  have hxN : x ∈ Nb := I.LN hx
  set D := opm (φ x) with hD
  have hDlow := I.layer.Nb_low x hxN
  have hya_apply : ∀ v, φ ya v = v + Ψ v := fun v => by
    rw [hΨ, opm_apply]
    abel
  have hya_inv : ∀ v, φ ya⁻¹ v = v - Ψ v := fun v => by
    have h := opm_inv_of_sq (g := φ ya) hΨΨ v
    rw [opm_apply, ← map_inv] at h
    calc φ ya⁻¹ v = (φ ya⁻¹ v - v) + v := by abel
      _ = v - Ψ v := by rw [h]; abel
  have hβ' : ∀ v, opm (φ yb) v = β • Ψ v := fun v => by
    have h := LinearMap.congr_fun hβ v
    rwa [LinearMap.smul_apply] at h
  have hyb_apply : ∀ v, φ yb v = v + β • Ψ v := fun v => by
    have h := hβ' v
    rw [opm_apply] at h
    calc φ yb v = (φ yb v - v) + v := by abel
      _ = v + β • Ψ v := by rw [h]; abel
  have hyb_inv : ∀ v, φ yb⁻¹ v = v - β • Ψ v := fun v => by
    have hsq : ∀ w, opm (φ yb) (opm (φ yb) w) = 0 := I.opm_conj_sq g hb
    have h := opm_inv_of_sq (g := φ yb) hsq v
    rw [opm_apply, ← map_inv, hβ'] at h
    calc φ yb⁻¹ v = (φ yb⁻¹ v - v) + v := by abel
      _ = v - β • Ψ v := by rw [h]; abel
  let Δ : E →ₗ[K] E := β • (D ∘ₗ Ψ - Ψ ∘ₗ D) + (β * β) • (Ψ ∘ₗ D ∘ₗ Ψ)
  have hΔ : ∀ e, Δ e = β • (D (Ψ e) - Ψ (D e)) + (β * β) • Ψ (D (Ψ e)) := fun e => rfl
  have hℓL : ⁅x, yb⁆ ∈ L := by
    rw [commutatorElement_def]
    have e : x * yb * x⁻¹ * yb⁻¹ = x * (yb * x⁻¹ * yb⁻¹) := by group
    rw [e]
    exact L.mul_mem hx (I.Rb_normL yb hybR _ (L.inv_mem hx))
  have hℓN : ⁅x, yb⁆ ∈ Nb := I.LN hℓL
  have hℓ : ∀ e, opm (φ ⁅x, yb⁆) e - Δ e ∈ T := by
    intro e
    have hm : yb * x⁻¹ * yb⁻¹ ∈ Nb := I.Rb_normN yb hybR _ (Nb.inv_mem hxN)
    have e1 : ⁅x, yb⁆ = x * (yb * x⁻¹ * yb⁻¹) := by
      rw [commutatorElement_def]
      group
    have h1 : opm (φ (x * (yb * x⁻¹ * yb⁻¹))) e =
        D e + opm (φ (yb * x⁻¹ * yb⁻¹)) e + D (opm (φ (yb * x⁻¹ * yb⁻¹)) e) := by
      rw [map_mul, opm_mul_apply_layer]
    have h2 : opm (φ (yb * x⁻¹ * yb⁻¹)) e + φ yb (D (φ yb⁻¹ e)) =
        φ yb (D (D (φ yb⁻¹ e))) := by
      rw [opm_conj φ, map_inv, opm_inv_apply_of_lowering hDlow, map_add, map_neg]
      abel
    have t1 : D (opm (φ (yb * x⁻¹ * yb⁻¹)) e) ∈ T :=
      hDlow.mid _ ((I.layer.Nb_low _ hm).top e)
    have t2 : φ yb (D (D (φ yb⁻¹ e))) ∈ T :=
      I.layer.Rb_T yb hybR _ (hDlow.mid _ (hDlow.top _))
    have key : D e - φ yb (D (φ yb⁻¹ e)) = Δ e := by
      rw [hyb_inv, hyb_apply, hΔ]
      simp only [map_sub, map_smul, map_add, hΨΨ, smul_zero, sub_zero, add_zero]
      module
    have e2 : opm (φ ⁅x, yb⁆) e - Δ e =
        (opm (φ (yb * x⁻¹ * yb⁻¹)) e + φ yb (D (φ yb⁻¹ e))) +
          D (opm (φ (yb * x⁻¹ * yb⁻¹)) e) := by
      rw [e1, h1, ← key]
      abel
    rw [e2, h2]
    exact T.add_mem t2 t1
  set ℓ := ⁅x, yb⁆ with hℓdef
  have hwL : ⁅ya, ℓ⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem (I.Rb_normL ya hyaR ℓ hℓL) (L.inv_mem hℓL)
  have hm₁ : ya * ℓ * ya⁻¹ ∈ Nb := I.Rb_normN ya hyaR ℓ hℓN
  have hcorner : ∀ e, opm (φ ⁅ya, ℓ⁆) e ∈ T := by
    intro e
    have e1 : ⁅ya, ℓ⁆ = (ya * ℓ * ya⁻¹) * ℓ⁻¹ := by
      rw [commutatorElement_def]
    have h1 : opm (φ ((ya * ℓ * ya⁻¹) * ℓ⁻¹)) e = opm (φ (ya * ℓ * ya⁻¹)) e + opm (φ ℓ⁻¹) e +
        opm (φ (ya * ℓ * ya⁻¹)) (opm (φ ℓ⁻¹) e) := by
      rw [map_mul, opm_mul_apply_layer]
    have hℓlow := I.layer.Nb_low ℓ hℓN
    have t4 : opm (φ (ya * ℓ * ya⁻¹)) (opm (φ ℓ⁻¹) e) ∈ T :=
      (I.layer.Nb_low _ hm₁).mid _ ((I.layer.Nb_low _ (Nb.inv_mem hℓN)).top e)
    have t5 : opm (φ ℓ⁻¹) e + opm (φ ℓ) e ∈ T := by
      rw [map_inv, opm_inv_apply_of_lowering hℓlow]
      have : -opm (φ ℓ) e + opm (φ ℓ) (opm (φ ℓ) e) + opm (φ ℓ) e =
          opm (φ ℓ) (opm (φ ℓ) e) := by abel
      rw [this]
      exact hℓlow.mid _ (hℓlow.top e)
    have t6 : φ ya (opm (φ ℓ) (φ ya⁻¹ e)) - φ ya (Δ (φ ya⁻¹ e)) ∈ T := by
      rw [← map_sub]
      exact I.layer.Rb_T ya hyaR _ (hℓ _)
    have t7 := hℓ e
    have key2 : φ ya (Δ (φ ya⁻¹ e)) - Δ e = ((2 : K) * β) • Ψ (D (Ψ e)) := by
      rw [hya_inv, hya_apply]
      simp only [hΔ, map_sub, map_smul, map_add, hΨΨ, smul_zero, sub_zero, add_zero, map_zero]
      module
    rw [I.char2, zero_mul, zero_smul] at key2
    have e2 : opm (φ ⁅ya, ℓ⁆) e =
        (φ ya (opm (φ ℓ) (φ ya⁻¹ e)) - φ ya (Δ (φ ya⁻¹ e))) + (opm (φ ℓ⁻¹) e + opm (φ ℓ) e) -
          (opm (φ ℓ) e - Δ e) + opm (φ (ya * ℓ * ya⁻¹)) (opm (φ ℓ⁻¹) e) +
            (φ ya (Δ (φ ya⁻¹ e)) - Δ e) := by
      rw [e1, h1, opm_conj φ]
      abel
    rw [e2, key2, add_zero]
    exact T.add_mem (T.sub_mem (T.add_mem t6 t5) t7) t4
  exact I.layer.corner_mem _ (I.LN hwL) (I.isLayerCorner_of_mapsTo hcorner)

theorem B_opm_self_eq_zero (I : Sec717RepInputs B Qf φ V L Nb Rb T) (g : X) {a : X}
    (ha : a ∈ V) (ha1 : a ≠ 1) (e : E) : B e (opm (φ (g * a * g⁻¹)) e) = 0 := by
  have hc : ∀ c : K, c ^ 2 * Qf (opm (φ (g * a * g⁻¹)) e) +
      c * B e (opm (φ (g * a * g⁻¹)) e) = 0 := by
    intro c
    obtain ⟨a', _, ha'⟩ := (I.root_conj g ha ha1).2 c
    have h1 := I.Qf_isom (g * a' * g⁻¹) e
    have h2 : φ (g * a' * g⁻¹) e = e + c • opm (φ (g * a * g⁻¹)) e := by
      have h := LinearMap.congr_fun ha' e
      rw [LinearMap.smul_apply, opm_apply] at h
      rw [← h]
      abel
    rw [h2, I.Qf_add, I.Qf_smul, map_smul, smul_eq_mul] at h1
    linear_combination h1
  obtain ⟨c₀, hc₀, hc₁⟩ := I.exists_ne
  have h1 := hc 1
  have h2 := hc c₀
  simp only [one_pow, one_mul] at h1
  have h3 : c₀ * (c₀ - 1) * Qf (opm (φ (g * a * g⁻¹)) e) = 0 := by
    linear_combination h2 - c₀ * h1
  have hne : c₀ * (c₀ - 1) ≠ 0 := mul_ne_zero hc₀ (sub_ne_zero.mpr hc₁)
  have hQ : Qf (opm (φ (g * a * g⁻¹)) e) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hne
    · exact h
  linear_combination h1 - hQ

theorem conj_ranks (I : Sec717RepInputs B Qf φ V L Nb Rb T) {g : X}
    (hR : ∀ a ∈ V, g * a * g⁻¹ ∈ Rb) (hN : ¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) {a : X} (ha : a ∈ V)
    (ha1 : a ≠ 1) :
    Module.finrank K ↥(T.map (opm (φ (g * a * g⁻¹)))) = 2 ∧
      Module.finrank K ↥((B.orthogonal T).map (opm (φ (g * a * g⁻¹)))) = 4 := by
  set y := g * a * g⁻¹ with hy
  set f := opm (φ y) with hf
  set P := B.orthogonal T with hP
  have hyR : y ∈ Rb := hR a ha
  have hyN : y ∉ Nb := I.conj_not_mem_Nb hR hN ha ha1
  have hrange : LinearMap.range f = T.map ((φ g : E ≃ₗ[K] E) : E →ₗ[K] E) := by
    rw [hf, hy, opm_conj_eq, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
      Submodule.map_top, I.layer.range_V a ha ha1]
  have hrank : Module.finrank K ↥(LinearMap.range f) = 6 := by
    rw [hrange, LinearEquiv.finrank_map_eq, I.layer.finrank_T]
  have hker : LinearMap.ker f = B.orthogonal (LinearMap.range f) :=
    ker_opm_eq_orthogonal_range B I.layer.nondeg I.layer.refl (φ y) (I.layer.isom y)
  have hfT : ∀ t ∈ T, f t ∈ T := fun t ht => by
    rw [hf, opm_apply]
    exact T.sub_mem (I.layer.Rb_T y hyR t ht) ht
  have hfP : ∀ p ∈ P, f p ∈ P := fun p hp => by
    rw [hf, opm_apply]
    exact P.sub_mem (I.layer.Rb_P y hyR p hp) hp
  set r := Module.finrank K ↥(T.map f) with hr
  have hr_even : Even r := I.evenT y hyR
  have hr_pos : 0 < r := by
    rw [hr, Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact I.conj_moves_T hR hN ha ha1
  have hTf := finrank_range_inf_orthogonal_add B I.layer.nondeg I.layer.refl (φ y) hker T
  rw [← hf, hrank, ← hP] at hTf
  have hPf_le : Module.finrank K ↥(P.map f) ≤ Module.finrank K ↥(LinearMap.range f ⊓ P) := by
    apply Submodule.finrank_mono
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨p, rfl⟩, hfP p hp⟩
  set N := P ⊓ T.comap f with hN'
  have hNP : N ≤ P := inf_le_left
  have hBf : ∀ e, B e (f e) = 0 := I.B_opm_self_eq_zero g ha ha1
  have hsymm : ∀ u v, B u (f v) = B v (f u) := by
    intro u v
    have h := hBf (u + v)
    simp only [map_add, LinearMap.add_apply, hBf u, hBf v, zero_add, add_zero] at h
    have h2 : B u (f v) = -B v (f u) := by linear_combination h
    rw [h2, neg_eq_iff_add_eq_zero, ← two_mul, I.char2, zero_mul]
  have hs_even : Even (Module.finrank K P - Module.finrank K N) := by
    refine even_finrank_sub_of_alt (B.compl₂ f) P N hNP (fun u _ => hBf u)
      (fun u _ v _ => hsymm u v) fun v hv => ?_
    constructor
    · rintro ⟨-, hvT⟩ u hu
      have hvT' : f v ∈ T := hvT
      exact I.layer.refl _ _ ((LinearMap.BilinForm.mem_orthogonal_iff.mp hu) _ hvT')
    · intro h
      refine ⟨hv, ?_⟩
      show f v ∈ T
      have : f v ∈ B.orthogonal P := LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => h u hu
      rwa [hP, LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl] at this
  have hs_pos : Module.finrank K N < Module.finrank K P := by
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne hNP fun h => I.not_mapsTo_T hyR hyN fun p hp => ?_
    have hpN : p ∈ N := h ▸ hp
    exact hpN.2
  have hP1 := CFSG.HardMathSupport.Timmesfeld.DFour.finrank_map_add_finrank_inf_ker f P
  have hN1 := CFSG.HardMathSupport.Timmesfeld.DFour.finrank_map_add_finrank_inf_ker f N
  have hNker : N ⊓ LinearMap.ker f = P ⊓ LinearMap.ker f := by
    apply le_antisymm
    · exact inf_le_inf_right _ hNP
    · rintro x ⟨hxP, hxk⟩
      refine ⟨⟨hxP, ?_⟩, hxk⟩
      show f x ∈ T
      rw [LinearMap.mem_ker.mp hxk]
      exact T.zero_mem
  rw [hNker] at hN1
  have hTN : T ≤ N := fun t ht => ⟨I.layer.T_le ht, hfT t ht⟩
  have hNmap : r ≤ Module.finrank K ↥(N.map f) := Submodule.finrank_mono (Submodule.map_mono hTN)
  have hNle := Submodule.finrank_mono hNP
  obtain ⟨k, hk⟩ := hr_even
  obtain ⟨j, hj⟩ := hs_even
  refine ⟨by omega, by omega⟩

theorem image_dim (I : Sec717RepInputs B Qf φ V L Nb Rb T) {Tt : X → Submodule K E}
    (hTt : ∀ g a : X, a ∈ V → a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g) :
    ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
      2 ≤ Module.finrank K ↥((Tt g).map (B.orthogonal (Tt 1)).mkQ) := by
  intro g hR hN
  obtain ⟨a, ha, ha1⟩ := I.layer.V_ne
  have hT1 : Tt 1 = T := by
    rw [I.Tt_eq_map hTt 1, map_one]
    exact Submodule.map_id T
  rw [hT1, ← hTt g a ha ha1]
  have hker : LinearMap.ker (opm (φ (g * a * g⁻¹))) =
      B.orthogonal (LinearMap.range (opm (φ (g * a * g⁻¹)))) :=
    ker_opm_eq_orthogonal_range B I.layer.nondeg I.layer.refl _ (I.layer.isom _)
  have h1 := finrank_range_inf_orthogonal_add B I.layer.nondeg I.layer.refl _ hker T
  have h2 := finrank_map_mkQ_add_finrank_inf (LinearMap.range (opm (φ (g * a * g⁻¹))))
    (B.orthogonal T)
  have h3 := (I.conj_ranks hR hN ha ha1).1
  omega

theorem pair_dim (I : Sec717RepInputs B Qf φ V L Nb Rb T) {Tt : X → Submodule K E}
    (hTt : ∀ g a : X, a ∈ V → a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g) :
    ∀ g₁ g₂ : X,
      (∀ a ∈ V, ∀ b ∈ V, (g₁ * a * g₁⁻¹) * (g₂ * b * g₂⁻¹) = (g₂ * b * g₂⁻¹) * (g₁ * a * g₁⁻¹)) →
      (∀ b ∈ V, g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ ∈ Rb) →
      (¬ ∀ b ∈ V, g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ ∈ Nb) →
        Module.finrank K ↥(Tt g₁ ⊓ Tt g₂) = 2 := by
  intro g₁ g₂ _ hR hN
  set h := g₁⁻¹ * g₂ with hh
  have hconj : ∀ b, g₁⁻¹ * (g₂ * b * g₂⁻¹) * g₁ = h * b * h⁻¹ := fun b => by rw [hh]; group
  have hR' : ∀ b ∈ V, h * b * h⁻¹ ∈ Rb := fun b hb => hconj b ▸ hR b hb
  have hN' : ¬ ∀ b ∈ V, h * b * h⁻¹ ∈ Nb := fun hall => hN fun b hb => (hconj b).symm ▸ hall b hb
  obtain ⟨a, ha, ha1⟩ := I.layer.V_ne
  have hg₂ : g₂ = g₁ * h := by rw [hh]; group
  have hTt₂ : Tt g₂ = (Tt h).map ((φ g₁ : E ≃ₗ[K] E) : E →ₗ[K] E) := by
    rw [I.Tt_eq_map hTt g₂, I.Tt_eq_map hTt h, hg₂, ← Submodule.map_comp]
    congr 1
    ext v
    simp [map_mul, LinearEquiv.mul_apply]
  have hinf : Tt g₁ ⊓ Tt g₂ = (T ⊓ Tt h).map ((φ g₁ : E ≃ₗ[K] E) : E →ₗ[K] E) := by
    rw [hTt₂, I.Tt_eq_map hTt g₁, Submodule.map_inf _ (φ g₁).injective]
  rw [hinf, LinearEquiv.finrank_map_eq, ← hTt h a ha ha1]
  have hker : LinearMap.ker (opm (φ (h * a * h⁻¹))) =
      B.orthogonal (LinearMap.range (opm (φ (h * a * h⁻¹)))) :=
    ker_opm_eq_orthogonal_range B I.layer.nondeg I.layer.refl _ (I.layer.isom _)
  have h1 := finrank_range_inf_orthogonal_add B I.layer.nondeg I.layer.refl _ hker
    (B.orthogonal T)
  rw [LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl] at h1
  have hrange : Module.finrank K ↥(LinearMap.range (opm (φ (h * a * h⁻¹)))) = 6 := by
    rw [opm_conj_eq, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
      Submodule.map_top, I.layer.range_V a ha ha1, LinearEquiv.finrank_map_eq, I.layer.finrank_T]
  have h2 := (I.conj_ranks hR' hN' ha ha1).2
  rw [inf_comm]
  omega

theorem no_isotropic (I : Sec717RepInputs B Qf φ V L Nb Rb T) {Tt : X → Submodule K E}
    (hTt : ∀ g a : X, a ∈ V → a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g) :
    ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ Rb) → (¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) →
      ∀ Lm : Submodule K E, Tt 1 ≤ Lm → Lm ≤ B.orthogonal (Tt 1) →
        (∀ r ∈ Rb, ∀ w ∈ Lm, φ r w ∈ Lm) → (∀ x ∈ Lm, ∀ y ∈ Lm, B x y = 0) →
        ∀ a ∈ V, a ≠ 1 → ¬ ((B.orthogonal (Tt 1)).map (opm (φ (g * a * g⁻¹))) ≤ Lm) := by
  have hT1 : Tt 1 = T := by
    rw [I.Tt_eq_map hTt 1, map_one]
    exact Submodule.map_id T
  rw [hT1]
  intro g hR hN Lm hTLm hLmP hLmR hLmiso a ha ha1 hsub
  have hyR : g * a * g⁻¹ ∈ Rb := hR a ha
  have hyN : g * a * g⁻¹ ∉ Nb := I.conj_not_mem_Nb hR hN ha ha1
  obtain ⟨S, hS, hNS, hSR, hSn⟩ := I.exists_normal_of_mapsTo Lm hTLm hLmR
  have hyS : g * a * g⁻¹ ∈ S :=
    (hS _).mpr ⟨hyR, fun p hp => hsub (Submodule.mem_map_of_mem hp)⟩
  have hSeq : S = Rb := by
    rcases I.simple S hNS hSR hSn with h | h
    · exact absurd (h ▸ hyS) hyN
    · exact h
  have hperp : B.orthogonal Lm ≤ T := by
    intro p' hp'
    have hp'P : p' ∈ B.orthogonal T := LinearMap.BilinForm.orthogonal_le hTLm hp'
    refine I.cfix p' hp'P fun r hr => ?_
    have hmem : opm (φ r) p' ∈ B.orthogonal (B.orthogonal T) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro p hp
      have hp1 : opm (φ r⁻¹) p ∈ Lm := ((hS _).mp (hSeq ▸ Rb.inv_mem hr)).2 p hp
      have h1 : B (opm (φ r⁻¹) p) p' = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hp') _ hp1
      have e : B p (opm (φ r) p') = B (opm (φ r⁻¹) p) p' := by
        have hiso := I.layer.isom r (φ r⁻¹ p) p'
        rw [phi_apply_inv_apply] at hiso
        simp only [opm_apply, map_sub, LinearMap.sub_apply]
        rw [hiso]
      rw [e, h1]
    rwa [LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl] at hmem
  have hPLm : B.orthogonal T ≤ Lm := by
    have h := LinearMap.BilinForm.orthogonal_le (B := B) hperp
    rwa [LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl] at h
  have hPT : B.orthogonal T ≤ T := by
    intro p hp
    have : p ∈ B.orthogonal (B.orthogonal T) :=
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => hLmiso u (hPLm hu) p (hPLm hp)
    rwa [LinearMap.BilinForm.orthogonal_orthogonal I.layer.nondeg I.layer.refl] at this
  have h1 := Submodule.finrank_mono hPT
  rw [I.layer.finrank_P, I.layer.finrank_T] at h1
  omega

end Sec717RepInputs

end CFSG.RankThree.GF2n.Stroth80
