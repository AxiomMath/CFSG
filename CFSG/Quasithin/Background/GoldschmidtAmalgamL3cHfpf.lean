module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cComm

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem perm_three_order_three_cases : ∀ σ τ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 3 = 1 → τ ≠ 1 →
    τ ^ 3 = 1 → σ = τ ∨ σ = τ⁻¹ := by
  decide +kernel

section Hfpf

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.mem_closure_QB (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) {q₀ : ↥(pCoreOf 2 B)} (h₀ : psi g q₀ = (zel z, zel z))
    {q : D} (hq : q ∈ pCoreOf 2 B) :
    q ∈ Subgroup.closure ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) := by
  have hzz := g.zel_mul_zel
  have rot := g.psi_xc hU
  have h₁ : psi g (g.xc q₀) = (1, zel z) := by rw [rot, h₀]; simp [hzz]
  have hq01 : psi g (q₀ * g.xc q₀) = (zel z, 1) := by rw [map_mul, h₀, h₁]; simp [hzz]
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
      ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) →
      psi g p = psi g ⟨q, hq⟩ → q ∈ Subgroup.closure
        ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) := by
    intro p hp hpq
    have hker : p⁻¹ * ⟨q, hq⟩ ∈ (psi g).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpq]; simp
    have hU' : ((p⁻¹ * ⟨q, hq⟩ : ↥(pCoreOf 2 B)) : D) ∈ conjClosure V B :=
      (g.U_eq_K hU hT).ge ((g.mem_ker_psi hU _).mp hker)
    have e : q = (p : D) * ((p⁻¹ * ⟨q, hq⟩ : ↥(pCoreOf 2 B)) : D) := by
      simp [Subgroup.coe_mul]
    rw [e]
    exact Subgroup.mul_mem _ hp (hsub _ hU')
  rcases hp : psi g ⟨q, hq⟩ with ⟨e₀, e₁⟩
  rcases g.zpowers_elem_cases e₀ with rfl | rfl <;> rcases g.zpowers_elem_cases e₁ with rfl | rfl
  · exact key 1 (Subgroup.one_mem _) (by rw [map_one, hp]; rfl)
  · exact key (g.xc q₀) hq₁ (by rw [h₁, hp])
  · exact key (q₀ * g.xc q₀) (Subgroup.mul_mem _ hq₀ hq₁) (by rw [hq01, hp])
  · exact key q₀ hq₀ (by rw [h₀, hp])

theorem Gen3.comm_QB_mem (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64)
    {p q : D} (hp : p ∈ pCoreOf 2 B) (hq : q ∈ pCoreOf 2 B) :
    p * q * p⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨q₀, h₀⟩ := g.exists_q₀ hU hT
  have hq₀Q : (q₀ : D) ∈ pCoreOf 2 B := q₀.2
  have hq₁Q : (g.xc q₀ : D) ∈ pCoreOf 2 B := (g.xc q₀).2
  have hSB : Subgroup.closure ((conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)}) ≤
      pCoreOf 2 B := by
    rw [Subgroup.closure_le]
    rintro w (hw | hw | hw)
    · exact g.U_le_QB hw
    · rw [hw]; exact hq₀Q
    · rw [Set.mem_singleton_iff.mp hw]; exact hq₁Q
  have hcomm01 := g.comm_q₀_q₁_mem hU hT h₀
  refine commutator_mem_of_closure (S := (conjClosure V B : Set D) ∪ {(q₀ : D), (g.xc q₀ : D)})
    (Z := Subgroup.zpowers z) ?_ ?_ (g.mem_closure_QB hU hT h₀ hp) (g.mem_closure_QB hU hT h₀ hq)
  · intro s hs w hw
    exact zpowers_comm_B g.hyp (pCoreOf_le 2 B (hSB hs)) hw
  · have hUq : ∀ u ∈ conjClosure V B, ∀ r ∈ pCoreOf 2 B,
        u * r * u⁻¹ * r⁻¹ ∈ Subgroup.zpowers z := fun u hu r hr =>
      g.hyp.commutator_mem u hu r hr
    have hqU : ∀ r ∈ pCoreOf 2 B, ∀ u ∈ conjClosure V B,
        r * u * r⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := by
      intro r hr u hu
      have e : r * u * r⁻¹ * u⁻¹ = (u * r * u⁻¹ * r⁻¹)⁻¹ := by group
      rw [e]; exact Subgroup.inv_mem _ (hUq u hu r hr)
    rintro s (hs | hs | hs) t (ht | ht | ht)
    · have : s * t * s⁻¹ * t⁻¹ = 1 := by
        rw [g.U_comm hs ht]; group
      rw [this]; exact Subgroup.one_mem _
    · rw [ht]; exact hUq s hs _ hq₀Q
    · rw [Set.mem_singleton_iff.mp ht]; exact hUq s hs _ hq₁Q
    · rw [hs]; exact hqU _ hq₀Q t ht
    · rw [hs, ht]
      have : (q₀ : D) * q₀ * (q₀ : D)⁻¹ * (q₀ : D)⁻¹ = 1 := by group
      rw [this]; exact Subgroup.one_mem _
    · rw [hs, Set.mem_singleton_iff.mp ht]; exact hcomm01
    · rw [Set.mem_singleton_iff.mp hs]; exact hqU _ hq₁Q t ht
    · rw [Set.mem_singleton_iff.mp hs, ht]
      have e : (g.xc q₀ : D) * q₀ * (g.xc q₀ : D)⁻¹ * (q₀ : D)⁻¹ =
          ((q₀ : D) * (g.xc q₀ : D) * (q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹)⁻¹ := by group
      rw [e]; exact Subgroup.inv_mem _ hcomm01
    · rw [Set.mem_singleton_iff.mp hs, Set.mem_singleton_iff.mp ht]
      have : (g.xc q₀ : D) * g.xc q₀ * (g.xc q₀ : D)⁻¹ * (g.xc q₀ : D)⁻¹ = 1 := by group
      rw [this]; exact Subgroup.one_mem _

theorem Gen3.hfpf (hU : Nat.card (conjClosure V B) = 8) (hT : Nat.card ↥(A ⊓ B) = 64) :
    ∀ y ∈ B, y ≠ 1 → y ^ 3 = 1 → ∀ q ∈ pCoreOf 2 B, y * q * y⁻¹ = q →
      ∀ v ∈ pCoreOf 2 B, q * v = v * q := by
  intro y hyB hy1 hy3 q hq hyq v hv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy3' : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyT : y ∉ A ⊓ B := g.hyp.gold.vertex_right.not_mem_of_orderOf hy3'
  have hyQ : y ∉ pCoreOf 2 B := fun h => hyT (g.hyp.gold.pCoreOf_right_le h)
  have hxT := g.x_not
  have hxQ : x ∉ pCoreOf 2 B := fun h => hxT (g.hyp.gold.pCoreOf_right_le h)
  obtain ⟨π, -, hπk⟩ := g.hyp.gold.vertex_right.exists_hom
  have hpy3 : (π ⟨y, hyB⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyB⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hpx3 : (π ⟨x, g.x_mem⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, g.x_mem⟩ : ↥B) ^ 3 = 1 := Subtype.ext (by simpa [pow_three'] using g.x_cube)
    rw [this, map_one]
  have hpy1 : π ⟨y, hyB⟩ ≠ 1 := fun h => hyQ ((hπk _).mp h)
  have hpx1 : π ⟨x, g.x_mem⟩ ≠ 1 := fun h => hxQ ((hπk _).mp h)
  have hvB : v ∈ B := pCoreOf_le 2 B hv
  have hxinvB : x⁻¹ ∈ B := B.inv_mem g.x_mem
  have hq' : ∀ {c : D} (hcB : c ∈ B), π ⟨c, hcB⟩ = 1 → c ∈ pCoreOf 2 B := fun {c} hcB h =>
    (hπk ⟨c, hcB⟩).mp h
  suffices hqz : q ∈ Subgroup.zpowers z from (zpowers_comm_B g.hyp hvB hqz).symm
  rcases perm_three_order_three_cases _ _ hpy1 hpy3 hpx1 hpx3 with e | e
  ·
    have hq'Q : y * x⁻¹ ∈ pCoreOf 2 B := by
      refine hq' (B.mul_mem hyB hxinvB) ?_
      have : (⟨y * x⁻¹, B.mul_mem hyB hxinvB⟩ : ↥B) = ⟨y, hyB⟩ * ⟨x, g.x_mem⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, e]; simp
    have hcomm := g.comm_QB_mem hU hT (Subgroup.inv_mem _ hq'Q) hq
    have hxq : x * q * x⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      have e1 : (y * x⁻¹) * (x * q * x⁻¹) * (y * x⁻¹)⁻¹ = q := by
        calc (y * x⁻¹) * (x * q * x⁻¹) * (y * x⁻¹)⁻¹ = y * q * y⁻¹ := by group
          _ = q := hyq
      have e2 : x * q * x⁻¹ = (y * x⁻¹)⁻¹ * q * (y * x⁻¹) := by
        calc x * q * x⁻¹ = (y * x⁻¹)⁻¹ * ((y * x⁻¹) * (x * q * x⁻¹) * (y * x⁻¹)⁻¹) *
            (y * x⁻¹) := by group
          _ = (y * x⁻¹)⁻¹ * q * (y * x⁻¹) := by rw [e1]
      rw [e2]
      have e3 : (y * x⁻¹)⁻¹ * q * (y * x⁻¹) * q⁻¹ = (y * x⁻¹)⁻¹ * q * ((y * x⁻¹)⁻¹)⁻¹ * q⁻¹ := by
        rw [inv_inv]
      rw [e3]; exact hcomm
    have hfix := conj_eq_of_cube g.hyp g.x_mem g.x_cube hxq
    exact g.fixed_mem_zpowers hU hT hq hfix
  ·
    have hq'Q : y * x ∈ pCoreOf 2 B := by
      refine hq' (B.mul_mem hyB g.x_mem) ?_
      have : (⟨y * x, B.mul_mem hyB g.x_mem⟩ : ↥B) = ⟨y, hyB⟩ * ⟨x, g.x_mem⟩ := rfl
      rw [this, map_mul, e]
      have : (π ⟨x, g.x_mem⟩)⁻¹ * π ⟨x, g.x_mem⟩ = 1 := inv_mul_cancel _
      exact this
    have hcomm := g.comm_QB_mem hU hT (Subgroup.inv_mem _ hq'Q) hq
    have hxq : x⁻¹ * q * x⁻¹⁻¹ * q⁻¹ ∈ Subgroup.zpowers z := by
      have e1 : (y * x) * (x⁻¹ * q * x⁻¹⁻¹) * (y * x)⁻¹ = q := by
        calc (y * x) * (x⁻¹ * q * x⁻¹⁻¹) * (y * x)⁻¹ = y * q * y⁻¹ := by group
          _ = q := hyq
      have e2 : x⁻¹ * q * x⁻¹⁻¹ = (y * x)⁻¹ * q * (y * x) := by
        calc x⁻¹ * q * x⁻¹⁻¹ = (y * x)⁻¹ * ((y * x) * (x⁻¹ * q * x⁻¹⁻¹) * (y * x)⁻¹) *
            (y * x) := by group
          _ = (y * x)⁻¹ * q * (y * x) := by rw [e1]
      rw [e2]
      have e3 : (y * x)⁻¹ * q * (y * x) * q⁻¹ = (y * x)⁻¹ * q * ((y * x)⁻¹)⁻¹ * q⁻¹ := by
        rw [inv_inv]
      rw [e3]; exact hcomm
    have hx3' : x⁻¹ * x⁻¹ * x⁻¹ = 1 := by
      calc x⁻¹ * x⁻¹ * x⁻¹ = (x * x * x)⁻¹ := by group
        _ = 1 := by rw [g.x_cube]; simp
    have hfix' := conj_eq_of_cube g.hyp hxinvB hx3' hxq
    have hfix : x * q * x⁻¹ = q := by
      have : x * (x⁻¹ * q * x⁻¹⁻¹) * x⁻¹ = x * q * x⁻¹ := by
        rw [hfix']
      calc x * q * x⁻¹ = x * (x⁻¹ * q * x⁻¹⁻¹) * x⁻¹ := this.symm
        _ = q := by group
    exact g.fixed_mem_zpowers hU hT hq hfix

end Hfpf

end GoldAmL3c

end F6

end CFSG.Quasithin
