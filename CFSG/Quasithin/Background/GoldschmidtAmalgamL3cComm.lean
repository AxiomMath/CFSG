module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cFix

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem commutator_mem_of_closure {S : Set D} {Z : Subgroup D}
    (hZ : ∀ s ∈ Subgroup.closure S, ∀ w ∈ Z, s * w = w * s)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Z) {g h : D}
    (hg : g ∈ Subgroup.closure S) (hh : h ∈ Subgroup.closure S) :
    g * h * g⁻¹ * h⁻¹ ∈ Z := by
  have step1 : ∀ s ∈ S, ∀ h ∈ Subgroup.closure S, s * h * s⁻¹ * h⁻¹ ∈ Z := by
    intro s hs h hh
    induction hh using Subgroup.closure_induction with
    | mem t ht => exact hS s hs t ht
    | one => simp
    | mul t t' ht ht' iht iht' =>
      have e : s * (t * t') * s⁻¹ * (t * t')⁻¹ =
          (s * t * s⁻¹ * t⁻¹) * (t * (s * t' * s⁻¹ * t'⁻¹) * t⁻¹) := by group
      have hc : t * (s * t' * s⁻¹ * t'⁻¹) * t⁻¹ = s * t' * s⁻¹ * t'⁻¹ := by
        rw [hZ t ht _ iht']; group
      rw [e, hc]
      exact Z.mul_mem iht iht'
    | inv t ht iht =>
      have e : s * t⁻¹ * s⁻¹ * t⁻¹⁻¹ = (t⁻¹ * (s * t * s⁻¹ * t⁻¹) * t)⁻¹ := by group
      have hc : t⁻¹ * (s * t * s⁻¹ * t⁻¹) * t = s * t * s⁻¹ * t⁻¹ := by
        have := hZ t⁻¹ (Subgroup.inv_mem _ ht) _ iht
        calc t⁻¹ * (s * t * s⁻¹ * t⁻¹) * t = (t⁻¹ * (s * t * s⁻¹ * t⁻¹)) * t := rfl
          _ = ((s * t * s⁻¹ * t⁻¹) * t⁻¹) * t := by rw [this]
          _ = s * t * s⁻¹ * t⁻¹ := by group
      rw [e, hc]
      exact Z.inv_mem iht
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact step1 s hs h hh
  | one => simp
  | mul s s' hs hs' ihs ihs' =>
    have e : s * s' * h * (s * s')⁻¹ * h⁻¹ =
        (s * (s' * h * s'⁻¹ * h⁻¹) * s⁻¹) * (s * h * s⁻¹ * h⁻¹) := by group
    have hc : s * (s' * h * s'⁻¹ * h⁻¹) * s⁻¹ = s' * h * s'⁻¹ * h⁻¹ := by
      rw [hZ s hs _ ihs']; group
    rw [e, hc]
    exact Z.mul_mem ihs' ihs
  | inv s hs ihs =>
    have e : s⁻¹ * h * s⁻¹⁻¹ * h⁻¹ = s⁻¹ * (h * s * h⁻¹ * s⁻¹) * s := by group
    have e' : h * s * h⁻¹ * s⁻¹ = (s * h * s⁻¹ * h⁻¹)⁻¹ := by group
    have hc : s⁻¹ * (h * s * h⁻¹ * s⁻¹) * s = h * s * h⁻¹ * s⁻¹ := by
      rw [e']
      have := hZ s⁻¹ (Subgroup.inv_mem _ hs) _ (Z.inv_mem ihs)
      calc s⁻¹ * (s * h * s⁻¹ * h⁻¹)⁻¹ * s = (s⁻¹ * (s * h * s⁻¹ * h⁻¹)⁻¹) * s := rfl
        _ = ((s * h * s⁻¹ * h⁻¹)⁻¹ * s⁻¹) * s := by rw [this]
        _ = (s * h * s⁻¹ * h⁻¹)⁻¹ := by group
    rw [e, hc, e']
    exact Z.inv_mem ihs

section Comm

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.comm_q₀_q₁_mem (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64)
    {q₀ : ↥(pCoreOf 2 B)} (h₀ : psi g q₀ = (zel z, zel z)) :
    (q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ ∈ Subgroup.zpowers z := by
  have hzz := g.zel_mul_zel
  have hzi : (zel z)⁻¹ = zel z := inv_eq_of_mul_eq_one_right hzz
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have h₂ : psi g (g.xc (g.xc q₀)) = (zel z, 1) := by rw [rot, h₁]; simp
  have hq : psi g (q₀ * g.xc q₀) = psi g (g.xc (g.xc q₀)) := by
    rw [map_mul, h₀, h₁, h₂]; simp [hzz]
  obtain ⟨u, hu⟩ : ∃ u : ↥(pCoreOf 2 B), u = (q₀ * g.xc q₀)⁻¹ * g.xc (g.xc q₀) := ⟨_, rfl⟩
  have hu_ker : u ∈ (psi g).ker := by
    rw [MonoidHom.mem_ker, hu, map_mul, map_inv, hq]; simp
  have hu_U : (u : D) ∈ conjClosure V B :=
    (g.U_eq_K hU hT).ge ((g.mem_ker_psi hU u).mp hu_ker)
  have hd_ker : (q₀ * g.xc q₀ * q₀⁻¹ * (g.xc q₀)⁻¹ : ↥(pCoreOf 2 B)) ∈ (psi g).ker := by
    rw [MonoidHom.mem_ker]
    simp [map_mul, map_inv, h₀, h₁, hzz, hzi]
  have hd_U : (q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ ∈ conjClosure V B :=
    (g.U_eq_K hU hT).ge ((g.mem_ker_psi hU _).mp hd_ker)
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : D, p₀ = (q₀ : D) := ⟨_, rfl⟩
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : D, p₁ = x * p₀ * x⁻¹ := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂⟩ : ∃ p₂ : D, p₂ = x * p₁ * x⁻¹ := ⟨_, rfl⟩
  have hxc₀ : (g.xc q₀ : D) = p₁ := by rw [hp₁, hp₀]; rfl
  have hxc₁ : (g.xc (g.xc q₀) : D) = p₂ := by
    rw [hp₂, ← hxc₀]; rfl
  rw [hxc₀, ← hp₀]
  rw [hxc₀, ← hp₀] at hd_U
  have hp₁B : p₁ ∈ B := by
    rw [← hxc₀]; exact pCoreOf_le 2 B (g.xc q₀).2
  have hp₀B : p₀ ∈ B := by rw [hp₀]; exact pCoreOf_le 2 B q₀.2
  have hp₁Q : p₁ ∈ pCoreOf 2 B := by rw [← hxc₀]; exact (g.xc q₀).2
  have hq2 : p₂ = p₀ * p₁ * (u : D) := by
    have h := congrArg (fun w : ↥(pCoreOf 2 B) => (w : D)) hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hxc₀, hxc₁, ← hp₀] at h
    rw [h]; group
  obtain ⟨d, hd⟩ : ∃ d : D, d = p₀ * p₁ * p₀⁻¹ * p₁⁻¹ := ⟨_, rfl⟩
  rw [← hd] at hd_U ⊢
  have hw : p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹ ∈ Subgroup.zpowers z := by
    have h1 := g.hyp.commutator_mem (u : D) hu_U p₁ hp₁Q
    have e : p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹ = ((u : D) * p₁ * (u : D)⁻¹ * p₁⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ h1
  have hxd : x * d * x⁻¹ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d := by
    have e1 : x * d * x⁻¹ = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ := by
      rw [hd, hp₂, hp₁]; group
    have e2 : p₁ * p₂ * p₁⁻¹ * p₂⁻¹ =
        p₁ * p₀ * (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * p₁⁻¹ * p₀⁻¹ := by
      rw [hq2]; group
    have hcen : (p₁ * p₀) * (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) =
        (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * (p₁ * p₀) :=
      zpowers_comm_B g.hyp (B.mul_mem hp₁B hp₀B) hw
    have hdinv : d⁻¹ = d := by
      have := g.hyp.abelian.2 d hd_U
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_right this
    calc x * d * x⁻¹ = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ := e1
      _ = (p₁ * p₀) * (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * p₁⁻¹ * p₀⁻¹ := e2
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * (p₁ * p₀) * p₁⁻¹ * p₀⁻¹ := by rw [hcen]
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * (p₁ * p₀ * p₁⁻¹ * p₀⁻¹) := by group
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d⁻¹ := by rw [hd]; group
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d := by rw [hdinv]
  have hfix : x * d * x⁻¹ = d := by
    refine conj_eq_of_cube g.hyp g.x_mem g.x_cube ?_
    rw [hxd]
    have : (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d * d⁻¹ = p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹ := by
      group
    rw [this]; exact hw
  have hmem : d ∈ conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) := by
    refine ⟨hd_U, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc y * d = (y * d * y⁻¹) * y := by group
      _ = d * y := by rw [hfix]
  rw [g.U_inf_centralizer_x hU] at hmem
  exact hmem

end Comm

end GoldAmL3c

end F6

end CFSG.Quasithin
