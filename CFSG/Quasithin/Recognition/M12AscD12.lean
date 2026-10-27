module

public import CFSG.Quasithin.Recognition.M12AscD11
public import CFSG.Quasithin.Recognition.M12AscD10
public import CFSG.Quasithin.Recognition.M12AscD9

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

@[expose] def bv : Perm (Fin 6) := x6 * (x16 * x16)

@[expose] def Fw (d : Perm (Fin 6)) : Perm (Fin 6) :=
  fAct x6 bv (swap 0 1 * d * (swap 0 1)⁻¹)

theorem basis_bv : (x6, bv) ∈ basisList := by decide +kernel

theorem Fv_mem : ∀ d ∈ D6l, fAct x6 bv d ∈ D6l := by decide +kernel

theorem Fv_inv : ∀ d ∈ D6l, fAct x6 bv (fAct x6 bv d) = d := by decide +kernel

theorem Fw_mem : ∀ d ∈ D6l, Fw d ∈ D6l := by decide +kernel

theorem Fw_cube : ∀ d ∈ D6l, Fw (Fw (Fw d)) = d := by decide +kernel

theorem swap01_mem : ∀ d ∈ D6l, swap 0 1 * d * (swap 0 1)⁻¹ ∈ D6l := by decide +kernel

namespace AscCox

variable {m : AscModel z} (c : AscCox m)

theorem exists_centralizing_b
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z)
    (h27 : 27 ∣ Nat.card G) {y : G} (h : OuterData c y) {g : G}
    (hg : g ∈ Subgroup.normalizer (c.D : Set G)) :
    ∃ v ∈ Subgroup.normalizer (c.D : Set G), v * (c.u' * z) = (c.u' * z) * v ∧
      ∀ d ∈ c.D, v * d * v⁻¹ = g * d * g⁻¹ := by
  have ht := c.frattini_mem hyp h27 h hg
  set t := g * (c.u' * z) * g⁻¹ * (c.u' * z)⁻¹ with htdef
  have hDN : c.D ≤ Subgroup.normalizer (c.D : Set G) := Subgroup.le_normalizer
  have ht3 := c.pow3_D ht
  have hbt : (c.u' * z) * t * (c.u' * z)⁻¹ = t⁻¹ := c.b_inverts_D ht
  have hgb : g * (c.u' * z) = t * (c.u' * z) * g := by
    rw [htdef]
    group
  refine ⟨t * g, (Subgroup.normalizer (c.D : Set G)).mul_mem (hDN ht) hg, ?_, ?_⟩
  · have htt : t * t = t⁻¹ := by
      calc t * t = (t * t * t) * t⁻¹ := by group
        _ = t⁻¹ := by rw [ht3, one_mul]
    have hbt' : (c.u' * z) * t = t⁻¹ * (c.u' * z) := by
      calc (c.u' * z) * t = ((c.u' * z) * t * (c.u' * z)⁻¹) * (c.u' * z) := by group
        _ = t⁻¹ * (c.u' * z) := by rw [hbt]
    calc t * g * (c.u' * z) = t * (g * (c.u' * z)) := by group
      _ = t * (t * (c.u' * z) * g) := by rw [hgb]
      _ = (t * t) * (c.u' * z) * g := by group
      _ = t⁻¹ * (c.u' * z) * g := by rw [htt]
      _ = ((c.u' * z) * t) * g := by rw [hbt']
      _ = (c.u' * z) * (t * g) := by group
  · intro d hd
    have hgd : g * d * g⁻¹ ∈ c.D := (Subgroup.mem_normalizer_iff.1 hg d).1 hd
    have hcomm := c.D_comm ht hgd
    calc t * g * d * (t * g)⁻¹ = t * (g * d * g⁻¹) * t⁻¹ := by group
      _ = (g * d * g⁻¹) * t * t⁻¹ := by rw [hcomm]
      _ = g * d * g⁻¹ := by group

theorem conj_pow_of_act {w : G} {F : Perm (Fin 6) → Perm (Fin 6)}
    (hF : ∀ d ∈ D6l, w * c.ρ d * w⁻¹ = c.ρ (F d)) (hmem : ∀ d ∈ D6l, F d ∈ D6l) (n : ℕ) :
    ∀ d ∈ D6l, w ^ n * c.ρ d * (w ^ n)⁻¹ = c.ρ (F^[n] d) := by
  induction n with
  | zero => intro d _; simp
  | succ n ih =>
    intro d hd
    have hF' : F^[n] d ∈ D6l := by
      clear ih
      induction n with
      | zero => exact hd
      | succ n ihn =>
        rw [Function.iterate_succ_apply']
        exact hmem _ ihn
    calc w ^ (n + 1) * c.ρ d * (w ^ (n + 1))⁻¹
        = w * (w ^ n * c.ρ d * (w ^ n)⁻¹) * w⁻¹ := by group
      _ = w * c.ρ (F^[n] d) * w⁻¹ := by rw [ih d hd]
      _ = c.ρ (F (F^[n] d)) := hF _ hF'
      _ = c.ρ (F^[n + 1] d) := by rw [Function.iterate_succ_apply']

theorem comm_of_act
    {g : G} (h : ∀ d ∈ D6l, g * c.ρ d * g⁻¹ = c.ρ d) :
    ∀ d ∈ c.D, g * d = d * g := by
  intro d hd
  obtain ⟨d₀, hd₀, rfl⟩ := (mem_D c).1 hd
  have := h d₀ hd₀
  calc g * c.ρ d₀ = (g * c.ρ d₀ * g⁻¹) * g := by group
    _ = c.ρ d₀ * g := by rw [this]

structure VData (v : G) : Prop where
  mem_N : v ∈ Subgroup.normalizer (c.D : Set G)
  comm_b : v * (c.u' * z) = (c.u' * z) * v
  act_x : v * c.ρ x6 * v⁻¹ = c.ρ x6
  act_x1 : v * c.ρ x16 * v⁻¹ = c.ρ bv
  sq : v * v = 1
  vz : (v * z) ^ 3 = 1

theorem exists_v
    [Finite G] [IsSimpleGroup G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G)
    {y : G} (h : OuterData c y) : ∃ v : G, VData c v := by
  obtain ⟨g, hgN, hgx, hgx1⟩ := c.exists_lift hyp h27 h basis_bv
  obtain ⟨v, hvN, hvb, hvact⟩ := c.exists_centralizing_b hyp h27 h hgN
  have hva : v * c.ρ x6 * v⁻¹ = c.ρ x6 := by
    calc v * c.ρ x6 * v⁻¹ = v * m.ψ mX * v⁻¹ := by rw [c.rho_x6]
      _ = g * m.ψ mX * g⁻¹ := hvact _ c.x_mem_D
      _ = c.ρ x6 := hgx
  have hvb' : v * c.ρ x16 * v⁻¹ = c.ρ bv := by
    calc v * c.ρ x16 * v⁻¹ = v * c.x1 * v⁻¹ := by rw [c.rho_x16]
      _ = g * c.x1 * g⁻¹ := hvact _ c.x1_mem_D
      _ = c.ρ bv := hgx1
  refine ⟨v, hvN, hvb, hva, hvb', ?_, ?_⟩
  ·
    have hF : ∀ d ∈ D6l, v * c.ρ d * v⁻¹ = c.ρ (fAct x6 bv d) := fun d hd =>
      c.conj_fAct hva hvb' hd
    have h2 := c.conj_pow_of_act hF Fv_mem 2
    have hact : ∀ d ∈ D6l, (v * v) * c.ρ d * (v * v)⁻¹ = c.ρ d := by
      intro d hd
      have := h2 d hd
      rw [pow_two] at this
      rw [this]
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
      rw [Fv_inv d hd]
    have hvvD : v * v ∈ c.D :=
      c.centralizer_D_le hyp h27 h ((mem_C c).2 (c.comm_of_act (by
        intro d hd
        have := hact d hd
        calc (v * v) * c.ρ d * (v * v)⁻¹ = c.ρ d := this)))
    have hvvb : (c.u' * z) * (v * v) = (v * v) * (c.u' * z) := by
      calc (c.u' * z) * (v * v) = ((c.u' * z) * v) * v := by group
        _ = (v * (c.u' * z)) * v := by rw [hvb]
        _ = v * ((c.u' * z) * v) := by group
        _ = v * (v * (c.u' * z)) := by rw [hvb]
        _ = (v * v) * (c.u' * z) := by group
    exact c.eq_one_of_comm_b hvvD hvvb
  ·
    have hz : ∀ d ∈ D6l, z * c.ρ d * z⁻¹ = c.ρ (swap 0 1 * d * (swap 0 1)⁻¹) := by
      intro d _
      have : c.ρ (swap 0 1) * c.ρ d * (c.ρ (swap 0 1))⁻¹ =
          c.ρ (swap 0 1 * d * (swap 0 1)⁻¹) := by rw [map_mul, map_mul, map_inv]
      rwa [c.ρ_z] at this
    have hF : ∀ d ∈ D6l, (v * z) * c.ρ d * (v * z)⁻¹ = c.ρ (Fw d) := by
      intro d hd
      have hd' := swap01_mem d hd
      calc (v * z) * c.ρ d * (v * z)⁻¹ = v * (z * c.ρ d * z⁻¹) * v⁻¹ := by group
        _ = v * c.ρ (swap 0 1 * d * (swap 0 1)⁻¹) * v⁻¹ := by rw [hz d hd]
        _ = c.ρ (Fw d) := c.conj_fAct hva hvb' hd'
    have h3 := c.conj_pow_of_act hF Fw_mem 3
    have hact : ∀ d ∈ D6l, (v * z) ^ 3 * c.ρ d * ((v * z) ^ 3)⁻¹ = c.ρ d := by
      intro d hd
      rw [h3 d hd]
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
      rw [Fw_cube d hd]
    have hD : (v * z) ^ 3 ∈ c.D :=
      c.centralizer_D_le hyp h27 h ((mem_C c).2 (c.comm_of_act hact))
    have hbz : (c.u' * z) * (v * z) = (v * z) * (c.u' * z) := by
      have hzb := c.b_comm_z
      calc (c.u' * z) * (v * z) = ((c.u' * z) * v) * z := by group
        _ = (v * (c.u' * z)) * z := by rw [hvb]
        _ = v * ((c.u' * z) * z) := by group
        _ = v * (z * (c.u' * z)) := by rw [hzb]
        _ = (v * z) * (c.u' * z) := by group
    have hcomm : (c.u' * z) * (v * z) ^ 3 = (v * z) ^ 3 * (c.u' * z) :=
      ((Commute.pow_right (show Commute (c.u' * z) (v * z) from hbz) 3)).eq
    exact c.eq_one_of_comm_b hD hcomm

end AscCox

end CFSG.Quasithin
