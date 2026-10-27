module

public import CFSG.RankThree.GF2n.Stroth80.Sec717Layers

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

structure Sec717RepInputs {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [Group X]
    (B : LinearMap.BilinForm K E) (Qf : E → K) (φ : X →* (E ≃ₗ[K] E))
    (V L Nb Rb : Subgroup X) (T : Submodule K E) : Prop where
  layer : Sec717LayerData B φ V Nb Rb T
  char2 : (2 : K) = 0
  exists_ne : ∃ c : K, c ≠ 0 ∧ c ≠ 1
  Qf_add : ∀ e f, Qf (e + f) = Qf e + Qf f + B e f
  Qf_smul : ∀ (c : K) e, Qf (c • e) = c ^ 2 * Qf e
  Qf_isom : ∀ x e, Qf (φ x e) = Qf e
  VL : V ≤ L
  LN : L ≤ Nb
  NR : Nb ≤ Rb
  Rb_cent : ∀ r ∈ Rb, ∀ a ∈ V, r * a = a * r
  Rb_normL : ∀ r ∈ Rb, ∀ l ∈ L, r * l * r⁻¹ ∈ L
  Rb_normN : ∀ r ∈ Rb, ∀ n ∈ Nb, r * n * r⁻¹ ∈ Nb
  Nb_comm : ∀ a ∈ Nb, ∀ b ∈ Nb, ⁅a, b⁆ ∈ V
  L_comm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a
  V_sq : ∀ a ∈ V, a * a = 1
  root : ∀ a₀ ∈ V, a₀ ≠ 1 → (∀ a ∈ V, ∃ c : K, opm (φ a) = c • opm (φ a₀)) ∧
    ∀ c : K, ∃ a ∈ V, opm (φ a) = c • opm (φ a₀)
  cfix : ∀ w ∈ B.orthogonal T, (∀ r ∈ Rb, opm (φ r) w ∈ T) → w ∈ T
  evenT : ∀ r ∈ Rb, Even (Module.finrank K ↥(T.map (opm (φ r))))
  irrT : ∀ U : Submodule K E, U ≤ T → (∀ r ∈ Rb, ∀ w ∈ U, φ r w ∈ U) → U = ⊥ ∨ U = T
  simple : ∀ S : Subgroup X, Nb ≤ S → S ≤ Rb → (∀ r ∈ Rb, ∀ s ∈ S, r * s * r⁻¹ ∈ S) →
    S = Nb ∨ S = Rb
  invL : ∀ A : Subgroup X, V ≤ A → A ≤ L → (∀ r ∈ Rb, ∀ a ∈ A, r * a * r⁻¹ ∈ A) →
    A = V ∨ A = L
  CNL : ∀ n ∈ Nb, (∀ l ∈ L, n * l = l * n) → n ∈ L
  L_ne_V : ∃ l ∈ L, l ∉ V
  Nb_ne_L : ∃ z ∈ Nb, z ∉ L
  quadIso : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ x y, B (opm (φ l₁) x) (opm (φ l₂) y) = 0
  kL : ∀ l ∈ L, ∀ c : K, ∃ l' ∈ L, opm (φ l') = c • opm (φ l)
  two : ∀ k ∈ normalizer (V : Set X), (∀ a ∈ V, k * a = a * k) →
    IsPGroup 2 (zpowers k) → k ∈ Rb

namespace Sec717RepInputs

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {B : LinearMap.BilinForm K E} {Qf : E → K} {φ : X →* (E ≃ₗ[K] E)}
  {V L Nb Rb : Subgroup X} {T : Submodule K E}

theorem eq_of_opm_eq (I : Sec717RepInputs B Qf φ V L Nb Rb T) {a b : X}
    (h : opm (φ a) = opm (φ b)) : a = b := by
  apply I.layer.inj
  ext x
  have hx := LinearMap.congr_fun h x
  rw [opm_apply, opm_apply] at hx
  exact sub_left_injective hx

theorem opm_conj_eq (g a : X) :
    opm (φ (g * a * g⁻¹)) = (φ g : E →ₗ[K] E) ∘ₗ opm (φ a) ∘ₗ (φ g⁻¹ : E →ₗ[K] E) := by
  ext x
  exact opm_conj φ g a x

theorem opm_ne_zero (I : Sec717RepInputs B Qf φ V L Nb Rb T) {a : X} (ha : a ∈ V)
    (ha1 : a ≠ 1) : opm (φ a) ≠ 0 := by
  intro h
  apply ha1
  apply I.eq_of_opm_eq
  rw [h, map_one]
  ext x
  simp [opm_apply]

theorem root_conj (I : Sec717RepInputs B Qf φ V L Nb Rb T) (g : X) {a₀ : X} (ha₀ : a₀ ∈ V)
    (ha₀1 : a₀ ≠ 1) :
    (∀ a ∈ V, ∃ c : K, opm (φ (g * a * g⁻¹)) = c • opm (φ (g * a₀ * g⁻¹))) ∧
      ∀ c : K, ∃ a ∈ V, opm (φ (g * a * g⁻¹)) = c • opm (φ (g * a₀ * g⁻¹)) := by
  obtain ⟨h1, h2⟩ := I.root a₀ ha₀ ha₀1
  refine ⟨fun a ha => ?_, fun c => ?_⟩
  · obtain ⟨c, hc⟩ := h1 a ha
    refine ⟨c, ?_⟩
    rw [opm_conj_eq, opm_conj_eq, hc]
    ext x
    simp
  · obtain ⟨a, ha, hc⟩ := h2 c
    refine ⟨a, ha, ?_⟩
    rw [opm_conj_eq, opm_conj_eq, hc]
    ext x
    simp

theorem opm_V_sq (I : Sec717RepInputs B Qf φ V L Nb Rb T) {a : X} (ha : a ∈ V) (x : E) :
    opm (φ a) (opm (φ a) x) = 0 :=
  (I.layer.V_corner a ha).apply_lowering
    ((I.layer.V_corner a ha).isLayerLowering I.layer.T_le) x

theorem opm_conj_sq (I : Sec717RepInputs B Qf φ V L Nb Rb T) (g : X) {a : X} (ha : a ∈ V)
    (x : E) : opm (φ (g * a * g⁻¹)) (opm (φ (g * a * g⁻¹)) x) = 0 := by
  rw [opm_conj φ, opm_conj φ, phi_inv_apply_phi, I.opm_V_sq ha, map_zero]

theorem Tt_eq_map (I : Sec717RepInputs B Qf φ V L Nb Rb T) {Tt : X → Submodule K E}
    (hTt : ∀ g a : X, a ∈ V → a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g)
    (g : X) : Tt g = T.map ((φ g : E ≃ₗ[K] E) : E →ₗ[K] E) := by
  obtain ⟨a₀, ha₀, ha₀1⟩ := I.layer.V_ne
  rw [← hTt g a₀ ha₀ ha₀1, ← I.layer.range_V a₀ ha₀ ha₀1, opm_conj_eq, LinearMap.range_comp,
    LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]

theorem conj_not_mem_Nb (I : Sec717RepInputs B Qf φ V L Nb Rb T) {g : X}
    (hR : ∀ a ∈ V, g * a * g⁻¹ ∈ Rb) (hN : ¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) {a : X} (ha : a ∈ V)
    (ha1 : a ≠ 1) : g * a * g⁻¹ ∉ Nb := by
  intro haN
  apply hN
  intro b hb
  obtain ⟨c, hc⟩ := (I.root_conj g ha ha1).1 b hb
  refine I.layer.Rb_fix _ (hR b hb) fun w hw => ?_
  have h0 : opm (φ (g * a * g⁻¹)) w = 0 := (I.layer.Nb_low _ haN).bot w hw
  have h1 : opm (φ (g * b * g⁻¹)) w = 0 := by
    rw [hc, LinearMap.smul_apply, h0, smul_zero]
  rw [opm_apply, sub_eq_zero] at h1
  exact h1

theorem conj_moves_T (I : Sec717RepInputs B Qf φ V L Nb Rb T) {g : X}
    (hR : ∀ a ∈ V, g * a * g⁻¹ ∈ Rb) (hN : ¬ ∀ a ∈ V, g * a * g⁻¹ ∈ Nb) {a : X} (ha : a ∈ V)
    (ha1 : a ≠ 1) : T.map (opm (φ (g * a * g⁻¹))) ≠ ⊥ := by
  intro h
  apply I.conj_not_mem_Nb hR hN ha ha1
  refine I.layer.Rb_fix _ (hR a ha) fun w hw => ?_
  have hmem : opm (φ (g * a * g⁻¹)) w ∈ T.map (opm (φ (g * a * g⁻¹))) :=
    Submodule.mem_map_of_mem hw
  rw [h, Submodule.mem_bot, opm_apply, sub_eq_zero] at hmem
  exact hmem

theorem Rb_P_inv (I : Sec717RepInputs B Qf φ V L Nb Rb T) {r : X} (hr : r ∈ Rb) :
    ∀ w ∈ B.orthogonal T, φ r⁻¹ w ∈ B.orthogonal T :=
  I.layer.Rb_P r⁻¹ (Rb.inv_mem hr)

theorem exists_normal_of_mapsTo (I : Sec717RepInputs B Qf φ V L Nb Rb T) (U : Submodule K E)
    (hTU : T ≤ U) (hU : ∀ r ∈ Rb, ∀ w ∈ U, φ r w ∈ U) :
    ∃ S : Subgroup X, (∀ z, z ∈ S ↔ z ∈ Rb ∧ ∀ p ∈ B.orthogonal T, opm (φ z) p ∈ U) ∧
      Nb ≤ S ∧ S ≤ Rb ∧ ∀ r ∈ Rb, ∀ s ∈ S, r * s * r⁻¹ ∈ S := by
  refine ⟨{ carrier := {z | z ∈ Rb ∧ ∀ p ∈ B.orthogonal T, opm (φ z) p ∈ U}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun z => Iff.rfl, ?_, fun z hz => hz.1, ?_⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Rb.mul_mem ha hb, fun p hp => ?_⟩
    have e : opm (φ (a * b)) p = opm (φ a) (φ b p) + opm (φ b) p := by
      simp only [opm_apply, map_mul, LinearEquiv.mul_apply]
      abel
    rw [e]
    exact U.add_mem (ha' _ (I.layer.Rb_P b hb p hp)) (hb' p hp)
  · refine ⟨Rb.one_mem, fun p _ => ?_⟩
    simp [opm_apply]
  · rintro a ⟨ha, ha'⟩
    refine ⟨Rb.inv_mem ha, fun p hp => ?_⟩
    have e : opm (φ a⁻¹) p = -(φ a⁻¹ (opm (φ a) p)) := by
      simp only [opm_apply, map_sub, map_inv]
      rw [show (φ a)⁻¹ (φ a p) = p from linearEquiv_inv_apply_apply (φ a) p]
      abel
    rw [e]
    exact U.neg_mem (by simpa using hU a⁻¹ (Rb.inv_mem ha) _ (ha' p hp))
  · intro n hn
    refine ⟨I.NR hn, fun p hp => hTU ((I.layer.Nb_low n hn).mid p hp)⟩
  · rintro r hr s ⟨hs, hs'⟩
    refine ⟨Rb.mul_mem (Rb.mul_mem hr hs) (Rb.inv_mem hr), fun p hp => ?_⟩
    rw [opm_conj φ]
    exact hU r hr _ (hs' _ (I.Rb_P_inv hr p hp))

theorem not_mapsTo_T (I : Sec717RepInputs B Qf φ V L Nb Rb T) {y : X} (hyR : y ∈ Rb)
    (hyN : y ∉ Nb) : ¬ ∀ p ∈ B.orthogonal T, opm (φ y) p ∈ T := by
  intro hy
  obtain ⟨S, hS, hNS, hSR, hSn⟩ := I.exists_normal_of_mapsTo T le_rfl I.layer.Rb_T
  rcases I.simple S hNS hSR hSn with h | h
  · exact hyN (h ▸ (hS y).mpr ⟨hyR, hy⟩)
  · have hPT : B.orthogonal T ≤ T := fun p hp =>
      I.cfix p hp fun r hr => ((hS r).mp (h ▸ hr)).2 p hp
    have h1 := Submodule.finrank_mono hPT
    rw [I.layer.finrank_P, I.layer.finrank_T] at h1
    omega

end Sec717RepInputs

end CFSG.RankThree.GF2n.Stroth80
