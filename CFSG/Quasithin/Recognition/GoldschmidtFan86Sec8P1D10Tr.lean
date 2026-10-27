module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Ord
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem mem_nbrStab_smul_iff (F : FanTree Γ G) (g h : G) (a : V) :
    h ∈ nbrStab Γ G (g • a) ↔ g⁻¹ * h * g ∈ nbrStab Γ G a := by
  rw [mem_nbrStab, mem_nbrStab]
  constructor
  · intro H w hw
    have h1 := H (g • w) ((F.adj_smul g a w).2 hw)
    calc (g⁻¹ * h * g) • w = g⁻¹ • (h • (g • w)) := by simp [mul_smul]
      _ = w := by rw [h1, inv_smul_smul]
  · intro H w hw
    have h1 := H (g⁻¹ • w) (by
      have := (F.adj_smul g⁻¹ (g • a) w).2 hw
      rwa [inv_smul_smul] at this)
    have h2 : g⁻¹ • (h • w) = g⁻¹ • w := by
      calc g⁻¹ • (h • w) = g⁻¹ • (h • (g • (g⁻¹ • w))) := by rw [smul_inv_smul]
        _ = (g⁻¹ * h * g) • (g⁻¹ • w) := by simp [mul_smul]
        _ = g⁻¹ • w := h1
    exact MulAction.injective g⁻¹ h2

theorem mem_gcirc_smul_iff (F : FanTree Γ G) (g h : G) (a β : V) :
    h ∈ Gcirc Γ G (g • a) (g • β) ↔ g⁻¹ * h * g ∈ Gcirc Γ G a β := by
  have hst : ∀ x : V, h ∈ MulAction.stabilizer G (g • x) ↔
      g⁻¹ * h * g ∈ MulAction.stabilizer G x := fun x => by
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro H
      calc (g⁻¹ * h * g) • x = g⁻¹ • (h • (g • x)) := by simp [mul_smul]
        _ = x := by rw [H, inv_smul_smul]
    · intro H
      have : g⁻¹ • (h • (g • x)) = g⁻¹ • (g • x) := by
        rw [inv_smul_smul]
        calc g⁻¹ • (h • (g • x)) = (g⁻¹ * h * g) • x := by simp [mul_smul]
          _ = x := H
      exact MulAction.injective g⁻¹ this
  have hsq : g⁻¹ * (h * h) * g = (g⁻¹ * h * g) * (g⁻¹ * h * g) := by group
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨(hst a).1 h1, (hst β).1 h2⟩, ?_⟩
    rw [← hsq]
    exact (mem_nbrStab_smul_iff F g (h * h) a).1 h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨(hst a).2 h1, (hst β).2 h2⟩, ?_⟩
    rw [mem_nbrStab_smul_iff F g (h * h) a, hsq]
    exact h3

theorem IsZ2Pair.smul (F : FanTree Γ G) (g : G) {lam a β δ δ' : V} {k : ℕ}
    (hz : IsZ2Pair Γ G lam a β δ δ' k) :
    IsZ2Pair Γ G (g • lam) (g • a) (g • β) (g • δ) (g • δ') k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hz
  refine ⟨?_, (F.adj_smul g _ _).2 h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_smul F]; exact h1
  · rw [dist_smul F, dist_smul F]; exact h3
  · rw [dist_smul F]; exact h4
  · rw [dist_smul F]; exact h5
  · rw [dist_smul F]; exact h6
  · rw [dist_smul F]; exact h7
  · rintro ⟨h, hh, hδ⟩
    apply h8
    refine ⟨g⁻¹ * h * g, (mem_gcirc_smul_iff F g h a β).1 hh, ?_⟩
    calc (g⁻¹ * h * g) • δ = g⁻¹ • (h • (g • δ)) := by simp [mul_smul]
      _ = δ' := by rw [hδ, inv_smul_smul]

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

open Fin.NatCast in
theorem isZ2Pair_translate (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hY : D.IsYPair δ')
    (i : Fin 5) :
    IsZ2Pair Γ G α (D.alpha i) (D.beta i) (D.delta i) ((D.x ^ i.val)⁻¹ • δ') 2 := by
  have h1 := IsZ2Pair.smul F (D.x ^ i.val)⁻¹ hY
  have hα : (D.x ^ i.val)⁻¹ • α = α :=
    MulAction.mem_stabilizer_iff.1 (inv_mem (pow_mem (D.x_mem_stabilizer F h) _))
  have hi : ((i.val : ℕ) : Fin 5) = i := Fin.cast_val_eq_self i
  have e : ∀ {m : ℕ}, m ≤ 4 → (D.x ^ i.val)⁻¹ • (D.P 0).vert m = (D.P i).vert m := fun {m} hm => by
    rw [D.x_pow_inv_smul_vert F h i.val 0 hm, hi, zero_add]
  rw [hα] at h1
  exact (show (D.x ^ i.val)⁻¹ • D.alpha 0 = D.alpha i from e (by norm_num)) ▸
    (show (D.x ^ i.val)⁻¹ • D.beta 0 = D.beta i from e (by norm_num)) ▸
    (show (D.x ^ i.val)⁻¹ • D.delta 0 = D.delta i from e (by norm_num)) ▸ h1

open Fin.NatCast in
theorem y_eq (F : FanTree Γ G) (h : Fan71c F L) {δ' : V} (hv : valence Γ δ' = 5) (i : Fin 5) :
    D.y δ' i = L.z (D.delta i) * L.z ((D.x ^ i.val)⁻¹ • δ') := by
  have hi : ((i.val : ℕ) : Fin 5) = i := Fin.cast_val_eq_self i
  have hδ : (D.x ^ i.val)⁻¹ • D.delta 0 = D.delta i := by
    have := D.x_pow_inv_smul_vert F h i.val 0 (m := 4) (by norm_num)
    rw [hi, zero_add] at this
    exact this
  have h1 : L.z (D.delta i) = (D.x ^ i.val)⁻¹ * L.z (D.delta 0) * D.x ^ i.val := by
    rw [← hδ, L.z_inv_smul _ (D.valence_delta F 0)]
  rw [h1, L.z_inv_smul _ hv]
  show (D.x ^ i.val)⁻¹ * (L.z (D.delta 0) * L.z δ') * D.x ^ i.val = _
  group

end D10Set

end CFSG.Quasithin.Fan86
