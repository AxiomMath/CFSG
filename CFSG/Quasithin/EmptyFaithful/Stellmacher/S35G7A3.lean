module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7A1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.G7.A

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem plane_core (M : Model 5) (π : M.W →* orth.W)
    (hπ : ∀ (σ : Perm (Fin 5)) (m : M.W), π (M.act σ m) = orth.act σ (π m))
    (s : orth.W →* M.W) (hs : ∀ σ w, s (orth.act σ w) = M.act σ (s w)) (hπs : ∀ w, π (s w) = w)
    (hker : ∀ m, π m = 1 → ∀ σ, M.act σ m = m)
    (U : Subgroup M.W) (hU : IsInvSub M S5Syl U) (hinj : ∀ u ∈ U, π u = 1 → u = 1)
    (hcard : Nat.card U = 4)
    (hgen : Subgroup.closure {m : M.W | ∃ σ : Perm (Fin 5), ∃ u ∈ U, m = M.act σ u} = ⊤)
    (f : M.W →* orth.W)
    (H1 : ∀ σ : Perm (Fin 5), ∀ u ∈ U, ∃ u' ∈ U, f (M.act σ u) = orth.act σ (π u'))
    (H2 : ∃ σ0 : Perm (Fin 5), ∀ u ∈ U, f (M.act σ0 u) = 1) : f = 1 := by
  have hdec : ∀ m, m = (m * (s (π m))⁻¹) * s (π m) := fun m => by simp
  have hcfix : ∀ m σ, M.act σ (m * (s (π m))⁻¹) = m * (s (π m))⁻¹ := fun m σ =>
    hker _ (by rw [map_mul, map_inv, hπs, mul_inv_cancel]) σ
  have hPi : U.map π = P0 := by
    apply P0_eq_of_card
    · rintro b hb _ ⟨u, hu, rfl⟩
      exact ⟨M.act b u, hU b hb u hu, hπ b u⟩
    · have hinj' : Function.Injective (π.comp U.subtype) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        exact Subtype.ext (hinj x x.2 hx)
      have e1 : U.map π = (π.comp U.subtype).range := by
        ext w; simp [MonoidHom.mem_range]
      rw [e1, ← hcard]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  have hmem : ∀ u ∈ U, π u ∈ P0 := fun u hu => hPi ▸ ⟨u, hu, rfl⟩
  obtain ⟨ux, hux, hπux⟩ : ∃ u ∈ U, π u = ep 0 2 := by
    have := ep_zero_two_mem
    rw [← hPi] at this
    obtain ⟨u, hu, h⟩ := this
    exact ⟨u, hu, h⟩
  obtain ⟨d, hd, hdx⟩ := exists_swap_plane
  have hu4U : M.act d ux * ux⁻¹ ∈ U := U.mul_mem (hU d hd ux hux) (U.inv_mem hux)
  have hu4 : M.act d ux * ux⁻¹ = s (vp 4) := by
    have hc := hcfix ux d
    rw [hπux] at hc
    have e1 : ux = (ux * (s (ep 0 2))⁻¹) * s (ep 0 2) := by simp
    generalize ux * (s (ep 0 2))⁻¹ = c at hc e1
    calc M.act d ux * ux⁻¹ = M.act d (c * s (ep 0 2)) * (c * s (ep 0 2))⁻¹ := by rw [← e1]
      _ = M.act d (s (ep 0 2)) * (s (ep 0 2))⁻¹ := by
          rw [map_mul, hc]; simp [mul_assoc, mul_comm, mul_left_comm]
      _ = s (vp 4) := by rw [← hdx, map_mul, map_inv, hs]
  set fO : orth.W →* orth.W := f.comp s with hfO
  have hq : ∀ q, fO (vp q) = 1 ∨ fO (vp q) = vp q := by
    intro q
    apply eq_of_forall_mem_mp_fix
    intro σ hσ
    obtain ⟨u', hu', h'⟩ := H1 σ _ hu4U
    have : fO (vp q) = f (M.act σ (M.act d ux * ux⁻¹)) := by
      rw [hu4, ← hs, act_vp, hσ]; rfl
    rw [this, h']
    exact mem_mp.mpr (by rw [act_inv_act]; exact hmem u' hu')
  obtain ⟨σ0, hσ0⟩ := H2
  have h0 : fO (vp (σ0 4)) = 1 := by
    have : fO (vp (σ0 4)) = f (M.act σ0 (M.act d ux * ux⁻¹)) := by
      rw [hu4, ← hs, act_vp]; rfl
    rw [this]; exact hσ0 _ hu4U
  have hall : ∀ q, fO (vp q) = 1 := by
    refine fun q => eq_one_of_prod_eq_one (fun q => fO (vp q)) hq ?_ h0 q
    simp only [← map_mul, vp_prod, map_one]
  have hfO : ∀ w, fO w = 1 := by
    have h1 : Subgroup.closure (Set.range vp) ≤ fO.ker :=
      (Subgroup.closure_le _).mpr (by rintro _ ⟨p, rfl⟩; exact hall p)
    rw [closure_vp] at h1
    exact fun w => h1 (Subgroup.mem_top w)
  have e1 : ∀ σ, ∀ u, f (M.act σ u) = f (u * (s (π u))⁻¹) := by
    intro σ u
    calc f (M.act σ u) = f (M.act σ ((u * (s (π u))⁻¹) * s (π u))) :=
          congrArg (fun x => f (M.act σ x)) (hdec u)
      _ = f ((u * (s (π u))⁻¹) * s (orth.act σ (π u))) := by rw [map_mul, hcfix, ← hs]
      _ = f (u * (s (π u))⁻¹) := by
          rw [map_mul]; change _ * fO _ = _; rw [hfO, mul_one]
  have hz : ∀ σ, ∀ u ∈ U, f (M.act σ u) = 1 := by
    intro σ u hu
    rw [e1 σ u]
    apply eq_one_of_forall_mem_mp
    intro τ
    obtain ⟨u', hu', h'⟩ := H1 τ u hu
    rw [← e1 τ u, h']
    exact mem_mp.mpr (by rw [act_inv_act]; exact hmem u' hu')
  have h2 : Subgroup.closure {m : M.W | ∃ σ : Perm (Fin 5), ∃ u ∈ U, m = M.act σ u} ≤ f.ker :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨σ, u, hu, rfl⟩; exact hz σ u hu)
  rw [hgen] at h2
  exact MonoidHom.ext fun m => h2 (Subgroup.mem_top m)

end CFSG.Quasithin.F53.Stellmacher.S35.G7.A
