module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cAutN
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cComm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

section NB

variable [Finite D] {x a a₁ a₂ : D} {N : Subgroup D} (g : Gen3 A B z V x a a₁ a₂)
  (d : NData B V x N)

include g d

theorem NData.comm_q₀_q₁_mem (hU : Nat.card (conjClosure V B) = 8)
    {q₀ : ↥(pCoreOf 2 B)} (hq₀N : (q₀ : D) ∈ N) (h₀ : psi g q₀ = (zel z, zel z)) :
    (q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ ∈ Subgroup.zpowers z := by
  have hzz := g.zel_mul_zel
  have hzi : (zel z)⁻¹ = zel z := inv_eq_of_mul_eq_one_right hzz
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have h₂ : psi g (g.xc (g.xc q₀)) = (zel z, 1) := by rw [rot, h₁]; simp
  have hq₁N : ((g.xc q₀ : ↥(pCoreOf 2 B)) : D) ∈ N := d.xc_mem g hq₀N
  have hq₂N : ((g.xc (g.xc q₀) : ↥(pCoreOf 2 B)) : D) ∈ N := d.xc_mem g hq₁N
  have hq : psi g (q₀ * g.xc q₀) = psi g (g.xc (g.xc q₀)) := by
    rw [map_mul, h₀, h₁, h₂]; simp [hzz]
  obtain ⟨u, hu⟩ : ∃ u : ↥(pCoreOf 2 B), u = (q₀ * g.xc q₀)⁻¹ * g.xc (g.xc q₀) := ⟨_, rfl⟩
  have hu_ker : psi g u = 1 := by
    rw [hu, map_mul, map_inv, hq]; simp
  have hu_N : (u : D) ∈ N := by
    rw [hu]; exact N.mul_mem (N.inv_mem (N.mul_mem hq₀N hq₁N)) hq₂N
  have hu_U : (u : D) ∈ conjClosure V B := d.mem_U_of_psi_eq_one g hU hu_N hu_ker
  have hd_ker : psi g (q₀ * g.xc q₀ * q₀⁻¹ * (g.xc q₀)⁻¹) = 1 := by
    simp [map_mul, map_inv, h₀, h₁, hzz, hzi]
  have hd_N : ((q₀ * g.xc q₀ * q₀⁻¹ * (g.xc q₀)⁻¹ : ↥(pCoreOf 2 B)) : D) ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem hq₀N hq₁N) (N.inv_mem hq₀N)) (N.inv_mem hq₁N)
  have hd_U : (q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ ∈ conjClosure V B :=
    d.mem_U_of_psi_eq_one g hU hd_N hd_ker
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
  obtain ⟨d', hd'⟩ : ∃ d' : D, d' = p₀ * p₁ * p₀⁻¹ * p₁⁻¹ := ⟨_, rfl⟩
  rw [← hd'] at hd_U ⊢
  have hw : p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹ ∈ Subgroup.zpowers z := by
    have h1 := g.hyp.commutator_mem (u : D) hu_U p₁ hp₁Q
    have e : p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹ = ((u : D) * p₁ * (u : D)⁻¹ * p₁⁻¹)⁻¹ := by group
    rw [e]; exact Subgroup.inv_mem _ h1
  have hxd : x * d' * x⁻¹ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d' := by
    have e1 : x * d' * x⁻¹ = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ := by
      rw [hd', hp₂, hp₁]; group
    have e2 : p₁ * p₂ * p₁⁻¹ * p₂⁻¹ =
        p₁ * p₀ * (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * p₁⁻¹ * p₀⁻¹ := by
      rw [hq2]; group
    have hcen : (p₁ * p₀) * (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) =
        (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * (p₁ * p₀) :=
      zpowers_comm_B g.hyp (B.mul_mem hp₁B hp₀B) hw
    have hdinv : d'⁻¹ = d' := by
      have := g.hyp.abelian.2 d' hd_U
      rw [pow_two] at this
      exact inv_eq_of_mul_eq_one_right this
    calc x * d' * x⁻¹ = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ := e1
      _ = (p₁ * p₀) * (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * p₁⁻¹ * p₀⁻¹ := e2
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * (p₁ * p₀) * p₁⁻¹ * p₀⁻¹ := by rw [hcen]
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * (p₁ * p₀ * p₁⁻¹ * p₀⁻¹) := by group
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d'⁻¹ := by rw [hd']; group
      _ = (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d' := by rw [hdinv]
  have hfix : x * d' * x⁻¹ = d' := by
    refine conj_eq_of_cube g.hyp g.x_mem g.x_cube ?_
    rw [hxd]
    have : (p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹) * d' * d'⁻¹ = p₁ * (u : D) * p₁⁻¹ * (u : D)⁻¹ := by
      group
    rw [this]; exact hw
  have hmem : d' ∈ conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) := by
    refine ⟨hd_U, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc y * d' = (y * d' * y⁻¹) * y := by group
      _ = d' * y := by rw [hfix]
  rw [g.U_inf_centralizer_x hU] at hmem
  exact hmem

theorem NData.mem_closure (hU : Nat.card (conjClosure V B) = 8) {q₀ : ↥(pCoreOf 2 B)}
    (hq₀N : (q₀ : D) ∈ N) (h₀ : psi g q₀ = (zel z, zel z)) {q : D} (hq : q ∈ N) :
    q ∈ Subgroup.closure ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) := by
  have hqQ : q ∈ pCoreOf 2 B := d.le_QB hq
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have hq01 : psi g (q₀ * g.xc q₀) = (zel z, 1) := by rw [map_mul, h₀, h₁]; simp [hzz]
  have hq₁N : ((g.xc q₀ : ↥(pCoreOf 2 B)) : D) ∈ N := d.xc_mem g hq₀N
  have hsub : ∀ w ∈ conjClosure V B,
      w ∈ Subgroup.closure ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) :=
    fun w hw => Subgroup.subset_closure (Or.inl hw)
  have hq₀ : (q₀ : D) ∈ Subgroup.closure
      ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) :=
    Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hq₁ : (g.xc q₀ : D) ∈ Subgroup.closure
      ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) :=
    Subgroup.subset_closure (Or.inr (Or.inr rfl))
  have key : ∀ p : ↥(pCoreOf 2 B), (p : D) ∈ Subgroup.closure
      ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) → (p : D) ∈ N →
      psi g p = psi g ⟨q, hqQ⟩ → q ∈ Subgroup.closure
        ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) := by
    intro p hp hpN hpq
    have hker : psi g (p⁻¹ * ⟨q, hqQ⟩) = 1 := by
      rw [map_mul, map_inv, hpq]; simp
    have hN' : ((p⁻¹ * ⟨q, hqQ⟩ : ↥(pCoreOf 2 B)) : D) ∈ N :=
      N.mul_mem (N.inv_mem hpN) hq
    have hU' : ((p⁻¹ * ⟨q, hqQ⟩ : ↥(pCoreOf 2 B)) : D) ∈ conjClosure V B :=
      d.mem_U_of_psi_eq_one g hU hN' hker
    have e : q = (p : D) * ((p⁻¹ * ⟨q, hqQ⟩ : ↥(pCoreOf 2 B)) : D) := by
      simp [Subgroup.coe_mul]
    rw [e]
    exact Subgroup.mul_mem _ hp (hsub _ hU')
  rcases hp : psi g ⟨q, hqQ⟩ with ⟨e₀, e₁⟩
  rcases g.zpowers_elem_cases e₀ with rfl | rfl <;> rcases g.zpowers_elem_cases e₁ with rfl | rfl
  · exact key 1 (Subgroup.one_mem _) N.one_mem (by rw [map_one, hp]; rfl)
  · exact key (g.xc q₀) hq₁ hq₁N (by rw [h₁, hp])
  · exact key (q₀ * g.xc q₀) (Subgroup.mul_mem _ hq₀ hq₁) (N.mul_mem hq₀N hq₁N)
      (by rw [hq01, hp])
  · exact key q₀ hq₀ hq₀N (by rw [h₀, hp])

theorem NData.comm_mem (hU : Nat.card (conjClosure V B) = 8) {q₀ : ↥(pCoreOf 2 B)}
    (hq₀N : (q₀ : D) ∈ N) (h₀ : psi g q₀ = (zel z, zel z)) {p q : D} (hp : p ∈ N)
    (hq : q ∈ N) : p * q * p⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  have hq₁N : ((g.xc q₀ : ↥(pCoreOf 2 B)) : D) ∈ N := d.xc_mem g hq₀N
  have hSB : Subgroup.closure ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) ≤ N := by
    rw [Subgroup.closure_le]
    rintro w (hw | hw | hw)
    · exact d.U_le hw
    · rw [hw]; exact hq₀N
    · rw [Set.mem_singleton_iff.mp hw]; exact hq₁N
  have hcomm01 := d.comm_q₀_q₁_mem g hU hq₀N h₀
  refine commutator_mem_of_closure (S := (conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)})
    (Z := Subgroup.zpowers z) ?_ ?_ (d.mem_closure g hU hq₀N h₀ hp) (d.mem_closure g hU hq₀N h₀ hq)
  · intro s hs w hw
    exact zpowers_comm_B g.hyp (pCoreOf_le 2 B (d.le_QB (hSB hs))) hw
  · have hUq : ∀ u ∈ conjClosure V B, ∀ r ∈ N,
        u * r * u⁻¹ * r⁻¹ ∈ Subgroup.zpowers z := fun u hu r hr =>
      g.hyp.commutator_mem u hu r (d.le_QB hr)
    have hqU : ∀ r ∈ N, ∀ u ∈ conjClosure V B,
        r * u * r⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
      intro r hr u hu
      have e : r * u * r⁻¹ * u⁻¹ = (u * r * u⁻¹ * r⁻¹)⁻¹ := by group
      rw [e]; exact Subgroup.inv_mem _ (hUq u hu r hr)
    rintro s (hs | hs | hs) t (ht | ht | ht)
    · have : s * t * s⁻¹ * t⁻¹ = 1 := by
        rw [g.U_comm hs ht]; group
      rw [this]; exact Subgroup.one_mem _
    · rw [ht]; exact hUq s hs _ hq₀N
    · rw [Set.mem_singleton_iff.mp ht]; exact hUq s hs _ hq₁N
    · rw [hs]; exact hqU _ hq₀N t ht
    · rw [hs, ht]
      have : (q₀ : D) * q₀ * (q₀ : D)⁻¹ * (q₀ : D)⁻¹ = 1 := by group
      rw [this]; exact Subgroup.one_mem _
    · rw [hs, Set.mem_singleton_iff.mp ht]; exact hcomm01
    · rw [Set.mem_singleton_iff.mp hs]; exact hqU _ hq₁N t ht
    · rw [Set.mem_singleton_iff.mp hs, ht]
      have e : (g.xc q₀ : D) * q₀ * (g.xc q₀ : D)⁻¹ * (q₀ : D)⁻¹ =
          ((q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹)⁻¹ := by group
      rw [e]; exact Subgroup.inv_mem _ hcomm01
    · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht]
      have : (g.xc q₀ : D) * g.xc q₀ * (g.xc q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ = 1 := by group
      rw [this]; exact Subgroup.one_mem _

end NB

end GoldAmL3c

end F6

end CFSG.Quasithin
