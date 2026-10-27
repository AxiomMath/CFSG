module

public import CFSG.Sporadic.Co1Patterson.GlueFiber

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open scoped commutatorElement

variable {n : ℕ} {L : Type} [Group L] {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H H' : Type} [Group H] [Group H'] {S : ExtraspecialTypeSystem n L act qf bil H}
  {S' : ExtraspecialTypeSystem n L act qf bil H'}

open Glue

theorem exists_translation (hb : Nondeg bil) (d : H × H' → ZMod 2)
    (hd : ∀ f₁ ∈ F S S', ∀ f₂ ∈ F S S', d (f₁ * f₂) = d f₁ + d f₂)
    (h1 : d (S.z, 1) = 0) (h2 : d (1, S'.z) = 0) :
    ∃ p : H', S'.φ p = 1 ∧ ∀ f ∈ F S S', d f = bil (S'.vec p) (S.vec f.1) := by
  classical
  have hd1 : d 1 = 0 := by
    have h := hd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at h
    linear_combination (-1 : ZMod 2) * h
  have hex : ∀ v, ∃ f ∈ F S S', S.vec f.1 = v := by
    intro v
    obtain ⟨a, ha, hav⟩ := S.vec_surj v
    obtain ⟨b, hb, hbv⟩ := S'.vec_surj v
    exact ⟨(a, b), ⟨ha, hb, hav.trans hbv.symm⟩, hav⟩
  have hker : ∀ f ∈ F S S', S.vec f.1 = 0 → d f = 0 := by
    intro f hf h0
    obtain ⟨a, b⟩ := f
    obtain ⟨hf1, hf2, hf3⟩ := hf
    simp only at hf1 hf2 hf3 h0
    have hb0 : S'.vec b = 0 := hf3 ▸ h0
    rcases (S.vec_eq_zero a hf1).1 h0 with rfl | rfl <;>
      rcases (S'.vec_eq_zero b hf2).1 hb0 with rfl | rfl
    · exact hd1
    · exact h2
    · exact h1
    · have := hd _ z1_mem_F _ one_z_mem_F
      rw [h1, h2, Prod.mk_mul_mk, mul_one, one_mul] at this
      simpa using this
  have hdep : ∀ f₁ ∈ F S S', ∀ f₂ ∈ F S S', S.vec f₁.1 = S.vec f₂.1 → d f₁ = d f₂ := by
    intro f₁ h₁ f₂ h₂ hv
    have hm : f₁⁻¹ * f₂ ∈ F S S' := mul_mem (inv_mem h₁) h₂
    have h0 : S.vec (f₁⁻¹ * f₂).1 = 0 := by
      have := S.vec_mul f₁.1⁻¹ f₂.1 (by simpa using (inv_mem h₁).1) h₂.1
      simp only [Prod.fst_mul, Prod.fst_inv]
      rw [this, S.vec_inv h₁.1, hv]
      exact vec_add_self _
    have := hd f₁ h₁ _ hm
    rw [mul_inv_cancel_left, hker _ hm h0, add_zero] at this
    exact this.symm
  let D : (Fin n → ZMod 2) → ZMod 2 := fun v => d (Classical.choose (hex v))
  have hD : ∀ f ∈ F S S', D (S.vec f.1) = d f := fun f hf =>
    hdep _ (Classical.choose_spec (hex _)).1 f hf (Classical.choose_spec (hex _)).2
  have hDadd : ∀ u v, D (u + v) = D u + D v := by
    intro u v
    obtain ⟨fu, hfu, hu⟩ := hex u
    obtain ⟨fv, hfv, hv⟩ := hex v
    have huv : S.vec (fu * fv).1 = u + v := by
      simp only [Prod.fst_mul]
      rw [S.vec_mul _ _ hfu.1 hfv.1, hu, hv]
    have hDu : D u = d fu := by rw [← hu]; exact hD fu hfu
    have hDv : D v = d fv := by rw [← hv]; exact hD fv hfv
    rw [← huv, hD _ (mul_mem hfu hfv), hd _ hfu _ hfv, ← hDu, ← hDv]
  obtain ⟨a, ha⟩ := hb.exists_eq D hDadd
  obtain ⟨p, hp, hpa⟩ := S'.vec_surj a
  exact ⟨p, hp, fun f hf => by rw [← hD f hf, ha, hpa]⟩

namespace Glue

variable (G : Glue S S')

@[expose] def P : Subgroup (H × H') := P0 S S' ⊓ Subgroup.normalizer (G.Δ : Set (H × H'))

theorem mem_P {g : H × H'} :
    g ∈ G.P ↔ g ∈ P0 S S' ∧ ∀ h, h ∈ G.Δ ↔ g * h * g⁻¹ ∈ G.Δ := Iff.rfl

theorem P_le_P0 : G.P ≤ P0 S S' := inf_le_left

theorem conj_mem_Δ {g h : H × H'} (hg : g ∈ G.P) (hh : h ∈ G.Δ) : g * h * g⁻¹ ∈ G.Δ :=
  ((G.mem_P.1 hg).2 h).1 hh

theorem Δ_le_P : G.Δ ≤ G.P := fun _ hg => ⟨F_le_P0 hg.1, Subgroup.le_normalizer hg⟩

theorem mem_P_of_conj [Finite H] [Finite H'] {g : H × H'} (hg : g ∈ P0 S S')
    (h : ∀ x ∈ G.Δ, g * x * g⁻¹ ∈ G.Δ) : g ∈ G.P :=
  ⟨hg, Subgroup.mem_normalizer_fintype h⟩

theorem z1_mem_P : (S.z, (1 : H')) ∈ G.P := by
  refine ⟨S.φ_z.trans (map_one S'.φ).symm, Subgroup.mem_set_normalizer_iff.2 fun h => ?_⟩
  rw [z1_comm h, mul_inv_cancel_right]

theorem one_z_mem_P : ((1 : H), S'.z) ∈ G.P := by
  have e : ((1 : H), S'.z) = (S.z, (1 : H')) * (S.z, S'.z) := by simp [S.z_mul_self]
  rw [e]
  exact mul_mem G.z1_mem_P (G.Δ_le_P G.zz_mem_Δ)

theorem m_conj_one {p : H'} (hp : S'.φ p = 1) {f : H × H'} (hf : f ∈ F S S') :
    ((1 : H), p) * f * ((1 : H), p)⁻¹ ∈ F S S' ∧
      G.m (((1 : H), p) * f * ((1 : H), p)⁻¹) = G.m f + bil (S'.vec p) (S.vec f.1) := by
  refine ⟨conj_mem_F ?_ hf, ?_⟩
  · show S.φ 1 = S'.φ p
    rw [map_one, hp]
  obtain ⟨a, b⟩ := f
  obtain ⟨h1, h2, h3⟩ := hf
  simp only at h1 h2 h3 ⊢
  have e : ((1 : H), p) * (a, b) * ((1 : H), p)⁻¹ = (a, p * b * p⁻¹) := by simp
  rw [e]
  rcases S'.comm_cases hp h2 with h | h
  · have e2 : p * b * p⁻¹ = b := by
      rw [commutatorElement_eq_one_iff_mul_comm.1 h, mul_inv_cancel_right]
    rw [e2, h3, (S'.commElt_eq_one_iff hp h2).1 h, add_zero]
  · have e2 : (a, p * b * p⁻¹) = (1, S'.z) * (a, b) := by
      have : p * b * p⁻¹ = S'.z * b := by
        calc p * b * p⁻¹ = (p * b * p⁻¹ * b⁻¹) * b := by group
          _ = S'.z * b := by
            rw [commutatorElement_def] at h
            rw [h]
      simp [this]
    rw [e2, G.m_mul _ one_z_mem_F _ ⟨h1, h2, h3⟩, G.m_one_z, h3,
      (S'.commElt_eq_z_iff hp h2).1 h, add_comm]

theorem exists_mem_P (hb : Nondeg bil) [Finite H] [Finite H'] (x : H) :
    ∃ y : H', (x, y) ∈ G.P := by
  obtain ⟨y0, hy0⟩ := S'.φ_surj (S.φ x)
  have hg : ((x, y0) : H × H') ∈ P0 S S' := hy0.symm
  set g : H × H' := (x, y0) with hg_def
  have hconj : ∀ f ∈ F S S', g⁻¹ * f * g ∈ F S S' := by
    intro f hf
    have := conj_mem_F (inv_mem hg) hf
    simpa using this
  let d : H × H' → ZMod 2 := fun f => G.m (g⁻¹ * f * g) + G.m f
  have hd : ∀ f₁ ∈ F S S', ∀ f₂ ∈ F S S', d (f₁ * f₂) = d f₁ + d f₂ := by
    intro f₁ h₁ f₂ h₂
    have e : g⁻¹ * (f₁ * f₂) * g = (g⁻¹ * f₁ * g) * (g⁻¹ * f₂ * g) := by group
    simp only [d]
    rw [e, G.m_mul _ (hconj f₁ h₁) _ (hconj f₂ h₂), G.m_mul f₁ h₁ f₂ h₂]
    ring
  have hcentral : ∀ c : H × H', (∀ h, c * h = h * c) → d c = 0 := by
    intro c hc
    have : g⁻¹ * c * g = c := by
      have := conj_central hc g⁻¹
      simpa using this
    simp only [d]
    rw [this]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨p, hp, hdp⟩ := exists_translation hb d hd (hcentral _ z1_comm)
    (hcentral _ one_z_comm)
  refine ⟨p * y0, ?_⟩
  have hgg : ((x, p * y0) : H × H') = ((1 : H), p) * g := by simp [hg_def]
  rw [hgg]
  have h1p : ((1 : H), p) ∈ P0 S S' := by
    show S.φ 1 = S'.φ p
    rw [map_one, hp]
  refine G.mem_P_of_conj (mul_mem h1p hg) fun x hx => ?_
  have hxF := hx.1
  have hf₁ : g * x * g⁻¹ ∈ F S S' := conj_mem_F hg hxF
  obtain ⟨hF2, hm2⟩ := G.m_conj_one hp hf₁
  have e : ((1 : H), p) * g * x * (((1 : H), p) * g)⁻¹ =
      ((1 : H), p) * (g * x * g⁻¹) * ((1 : H), p)⁻¹ := by group
  rw [e]
  refine ⟨hF2, ?_⟩
  rw [hm2, ← hdp _ hf₁]
  simp only [d]
  have e3 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e3, hx.2, zero_add]
  exact CharTwo.add_self_eq_zero _

theorem eq_of_mem_P_one {y : H'} (h : ((1 : H), y) ∈ G.P) : y = 1 ∨ y = S'.z := by
  have hy : S'.φ y = 1 := by
    have : S.φ 1 = S'.φ y := G.P_le_P0 h
    rw [map_one] at this
    exact this.symm
  refine S'.center_eq y hy fun q hq => ?_
  obtain ⟨a, ha⟩ := G.exists_mem_Δ_snd hq
  have h1 := G.conj_mem_Δ h ha
  have h2 := mul_mem (inv_mem ha) h1
  have e : ((a, q) : H × H')⁻¹ * (((1 : H), y) * (a, q) * ((1 : H), y)⁻¹) =
      (1, q⁻¹ * (y * q * y⁻¹)) := by simp [mul_assoc]
  rw [e] at h2
  have h3 := G.eq_one_of_one_mem_Δ h2
  have h4 : y * q * y⁻¹ = q := by
    rw [inv_mul_eq_one] at h3
    exact h3.symm
  calc q * y = y * q * y⁻¹ * y := by rw [h4]
    _ = y * q := by rw [mul_assoc, inv_mul_cancel, mul_one]

theorem mem_F_of_mem_P {g : H × H'} (hg : g ∈ G.P) (h1 : S.φ g.1 = 1) : g ∈ F S S' := by
  obtain ⟨a, b⟩ := g
  simp only at h1
  obtain ⟨c, hc⟩ := G.exists_mem_Δ_fst h1
  have hcP : ((a, c) : H × H') ∈ G.P := G.Δ_le_P hc
  have h2 : ((a, c) : H × H')⁻¹ * (a, b) ∈ G.P := mul_mem (inv_mem hcP) hg
  have e : ((a, c) : H × H')⁻¹ * (a, b) = (1, c⁻¹ * b) := by simp
  rw [e] at h2
  have hb : S'.φ b = 1 := by
    have : S.φ a = S'.φ b := G.P_le_P0 hg
    rw [← this, h1]
  have hcb : S'.φ (c⁻¹ * b) = 1 := by
    have : S.φ 1 = S'.φ (c⁻¹ * b) := G.P_le_P0 h2
    rw [map_one] at this
    exact this.symm
  have hzero : S'.vec (c⁻¹ * b) = 0 := (S'.vec_eq_zero _ hcb).2 (G.eq_of_mem_P_one h2)
  have hcF := G.Δ_le_F hc
  refine ⟨h1, hb, ?_⟩
  have h5 := S'.vec_mul c (c⁻¹ * b) hcF.2.1 hcb
  rw [mul_inv_cancel_left, hzero, add_zero] at h5
  show S.vec a = S'.vec b
  rw [h5]
  exact hcF.2.2

theorem swap_mem_F {g : H' × H} : g.swap ∈ F S S' ↔ g ∈ F S' S := by
  rw [mem_F, mem_F]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3.symm⟩⟩

@[expose] def swap : Glue S' S where
  m g := G.m g.swap
  m_mul a ha b hb := by
    rw [Prod.swap_mul]
    exact G.m_mul _ (swap_mem_F.2 ha) _ (swap_mem_F.2 hb)
  m_z1 := G.m_one_z
  m_zz := G.m_zz

theorem mem_swap_Δ {g : H' × H} : g ∈ G.swap.Δ ↔ g.swap ∈ G.Δ := by
  rw [mem_Δ, mem_Δ, ← swap_mem_F]
  rfl

theorem mem_swap_P {g : H' × H} : g ∈ G.swap.P ↔ g.swap ∈ G.P := by
  rw [mem_P, mem_P, mem_P0, mem_P0]
  refine and_congr eq_comm ⟨fun h k => ?_, fun h k => ?_⟩
  · have := h k.swap
    rw [mem_swap_Δ, mem_swap_Δ, Prod.swap_swap] at this
    rw [this, Prod.swap_mul, Prod.swap_mul, Prod.swap_inv, Prod.swap_swap]
  · rw [mem_swap_Δ, mem_swap_Δ, h k.swap, Prod.swap_mul, Prod.swap_mul, Prod.swap_inv]

theorem exists_mem_P_snd (hb : Nondeg bil) [Finite H] [Finite H'] (y : H') :
    ∃ x : H, (x, y) ∈ G.P := by
  obtain ⟨x, hx⟩ := G.swap.exists_mem_P hb y
  exact ⟨x, G.mem_swap_P.1 hx⟩

theorem eq_of_mem_P_snd_one {x : H} (h : (x, (1 : H')) ∈ G.P) : x = 1 ∨ x = S.z := by
  have hx : S.φ x = 1 := by
    have : S.φ x = S'.φ 1 := G.P_le_P0 h
    rw [this, map_one]
  obtain ⟨-, -, h3⟩ := G.mem_F_of_mem_P h hx
  exact (S.vec_eq_zero x hx).1 (h3.trans S'.vec_one)

end Glue

end CFSG.Sporadic.Co1Patterson
