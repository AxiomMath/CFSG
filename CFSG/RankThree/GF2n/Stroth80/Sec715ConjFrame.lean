module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrameAPI

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup
open scoped commutatorElement

structure Sec715Frame {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [Group X]
    (φ : X →* (E ≃ₗ[K] E)) (V L Nb Rb : Subgroup X) (Tt : X → Submodule K E) : Prop where
  V_le_L : V ≤ L
  V_le_Nb : V ≤ Nb
  L_le_Rb : L ≤ Rb
  Nb_le_Rb : Nb ≤ Rb
  Nb_normal : ∀ r ∈ Rb, ∀ n ∈ Nb, r * n * r⁻¹ ∈ Nb
  L_comm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a
  Nb_norm_L : ∀ n ∈ Nb, ∀ l ∈ L, n * l * n⁻¹ ∈ L
  L_le_conj_Rb : ∀ g : X, (∀ a ∈ V, g * a * g⁻¹ ∈ L) → ∀ l ∈ L, g⁻¹ * l * g ∈ Rb
  Tt_range : ∀ (g : X), ∀ a ∈ V, a ≠ 1 → LinearMap.range (opm (φ (g * a * g⁻¹))) = Tt g
  Nb_fixes : ∀ n ∈ Nb, ∀ w ∈ Tt 1, φ n w = w
  Rb_fix_Nb : ∀ r ∈ Rb, (∀ w ∈ Tt 1, φ r w = w) → r ∈ Nb


namespace Sec715Frame

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X} {Tt : X → Submodule K E}

theorem map_opm_eq (F : Sec715Frame φ V L Nb Rb Tt) {g : X}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * (g * b * g⁻¹) = (g * b * g⁻¹) * a) {a b : X} (ha : a ∈ V)
    (ha1 : a ≠ 1) (hb : b ∈ V) (hb1 : b ≠ 1) :
    (Tt 1).map (opm (φ (g * b * g⁻¹))) = (Tt g).map (opm (φ a)) := by
  have h1 : LinearMap.range (opm (φ a)) = Tt 1 := by
    have := F.Tt_range 1 a ha ha1
    simpa using this
  have h2 : LinearMap.range (opm (φ (g * b * g⁻¹))) = Tt g := F.Tt_range g b hb hb1
  have hc : opm (φ (g * b * g⁻¹)) ∘ₗ opm (φ a) = opm (φ a) ∘ₗ opm (φ (g * b * g⁻¹)) :=
    LinearMap.ext fun x => (opm_comm_of_comm (by rw [← map_mul, ← map_mul, hcomm a ha b hb]) x).symm
  rw [← h1, ← h2, ← LinearMap.range_comp, ← LinearMap.range_comp, hc]

theorem conj_mem_Nb (F : Sec715Frame φ V L Nb Rb Tt) {g : X}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * (g * b * g⁻¹) = (g * b * g⁻¹) * a)
    (hR : ∀ b ∈ V, g * b * g⁻¹ ∈ Rb) {b₀ : X} (hb₀ : b₀ ∈ V) (hb₀1 : b₀ ≠ 1)
    (hb₀N : g * b₀ * g⁻¹ ∈ Nb) : ∀ b ∈ V, g * b * g⁻¹ ∈ Nb := by
  intro b hb
  by_cases hb1 : b = 1
  · subst hb1
    simpa using Nb.one_mem
  have h0 : (Tt 1).map (opm (φ (g * b₀ * g⁻¹))) = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
    rw [opm_apply, F.Nb_fixes _ hb₀N u hu, sub_self]
  have hsame : (Tt 1).map (opm (φ (g * b * g⁻¹))) = ⊥ := by
    rw [F.map_opm_eq hcomm hb₀ hb₀1 hb hb1, ← F.map_opm_eq hcomm hb₀ hb₀1 hb₀ hb₀1, h0]
  refine F.Rb_fix_Nb _ (hR b hb) fun w hw => ?_
  have hmem : opm (φ (g * b * g⁻¹)) w ∈ (Tt 1).map (opm (φ (g * b * g⁻¹))) :=
    Submodule.mem_map_of_mem hw
  rw [hsame, Submodule.mem_bot, opm_apply, sub_eq_zero] at hmem
  exact hmem

theorem comm_conj_of_le_L (F : Sec715Frame φ V L Nb Rb Tt) {h : X}
    (hL : ∀ a ∈ V, h * a * h⁻¹ ∈ L) :
    ∀ a ∈ V, ∀ b ∈ V, a * (h * b * h⁻¹) = (h * b * h⁻¹) * a := fun a ha b hb =>
  F.L_comm a (F.V_le_L ha) _ (hL b hb)

theorem eq_one_of_conj_mem_Nb (F : Sec715Frame φ V L Nb Rb Tt) {h : X}
    (hL : ∀ a ∈ V, h * a * h⁻¹ ∈ L) (hout : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb) {b : X} (hb : b ∈ V)
    (hbN : h * b * h⁻¹ ∈ Nb) : b = 1 := by
  by_contra hb1
  exact hout (F.conj_mem_Nb (F.comm_conj_of_le_L hL) (fun a ha => F.L_le_Rb (hL a ha)) hb hb1 hbN)

theorem exists_conj_le_Nb (F : Sec715Frame φ V L Nb Rb Tt) {h : X}
    (hL : ∀ a ∈ V, h * a * h⁻¹ ∈ L) (hout : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb) {n : X} (hn : n ∈ Nb)
    (hnc : ¬ ∀ a ∈ V, n * (h * a * h⁻¹) = (h * a * h⁻¹) * n) {b₀ : X} (hb₀ : b₀ ∈ V)
    (hb₀1 : b₀ ≠ 1) (hcN : h⁻¹ * ⁅n, h * b₀ * h⁻¹⁆ * h ∈ Nb) :
    (∀ a ∈ V, (h⁻¹ * n * h) * a * (h⁻¹ * n * h)⁻¹ ∈ Nb) ∧
      h⁻¹ * n * h ∉ normalizer (V : Set X) := by
  set m := h⁻¹ * n * h with hm
  have hconj : ∀ a, m * a * m⁻¹ = h⁻¹ * (n * (h * a * h⁻¹) * n⁻¹) * h := fun a => by
    rw [hm]
    group
  have hnL : ∀ a ∈ V, n * (h * a * h⁻¹) * n⁻¹ ∈ L := fun a ha => F.Nb_norm_L n hn _ (hL a ha)
  have hmR : ∀ a ∈ V, m * a * m⁻¹ ∈ Rb := fun a ha => by
    rw [hconj]
    exact F.L_le_conj_Rb h hL _ (hnL a ha)
  have hmc : ∀ a ∈ V, ∀ b ∈ V, a * (m * b * m⁻¹) = (m * b * m⁻¹) * a := by
    intro a ha b hb
    have h1 := F.L_comm _ (hL a ha) _ (hnL b hb)
    rw [hconj]
    have e : h⁻¹ * (h * a * h⁻¹) * h = a := by group
    calc a * (h⁻¹ * (n * (h * b * h⁻¹) * n⁻¹) * h)
        = h⁻¹ * ((h * a * h⁻¹) * (n * (h * b * h⁻¹) * n⁻¹)) * h := by group
      _ = h⁻¹ * ((n * (h * b * h⁻¹) * n⁻¹) * (h * a * h⁻¹)) * h := by rw [h1]
      _ = (h⁻¹ * (n * (h * b * h⁻¹) * n⁻¹) * h) * a := by group
  have hb₀N : m * b₀ * m⁻¹ ∈ Nb := by
    have e : m * b₀ * m⁻¹ = (h⁻¹ * ⁅n, h * b₀ * h⁻¹⁆ * h) * b₀ := by
      rw [hm, commutatorElement_def]
      group
    rw [e]
    exact Nb.mul_mem hcN (F.V_le_Nb hb₀)
  refine ⟨F.conj_mem_Nb hmc hmR hb₀ hb₀1 hb₀N, fun hmV => hnc fun a ha => ?_⟩
  have hmV' : m * a * m⁻¹ ∈ V := (mem_normalizer_iff.mp hmV a).mp ha
  have hx : h * a * h⁻¹ ∈ Rb := F.L_le_Rb (hL a ha)
  have hcomm_mem : ⁅n, h * a * h⁻¹⁆ ∈ Nb := by
    rw [commutatorElement_def]
    have h1 : (h * a * h⁻¹) * n⁻¹ * (h * a * h⁻¹)⁻¹ ∈ Nb := F.Nb_normal _ hx _ (Nb.inv_mem hn)
    have e : n * (h * a * h⁻¹) * n⁻¹ * (h * a * h⁻¹)⁻¹ =
        n * ((h * a * h⁻¹) * n⁻¹ * (h * a * h⁻¹)⁻¹) := by group
    rw [e]
    exact Nb.mul_mem hn h1
  set c := (m * a * m⁻¹) * a⁻¹ with hcdef
  have hcV : c ∈ V := V.mul_mem hmV' (V.inv_mem ha)
  have hce : ⁅n, h * a * h⁻¹⁆ = h * c * h⁻¹ := by
    rw [hcdef, hm, commutatorElement_def]
    group
  have hc1 : c = 1 := F.eq_one_of_conj_mem_Nb hL hout hcV (hce ▸ hcomm_mem)
  have h1 : ⁅n, h * a * h⁻¹⁆ = 1 := by rw [hce, hc1]; group
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end Sec715Frame

end CFSG.RankThree.GF2n.Stroth80
