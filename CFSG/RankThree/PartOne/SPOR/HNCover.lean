module

public import CFSG.RankThree.PartOne.SPOR.PlanesGeneric

public section

namespace CFSG.RankThree.PartOne.SPOR

open Subgroup

variable {A : Type} [Group A]

theorem exists_conj_into_sylow {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {P Q : Subgroup M} (hSyl : ∃ S : Sylow p P, (S : Subgroup P) = Q.subgroupOf P) {y : M}
    (hyP : y ∈ P) (hord : orderOf y = p) : ∃ g : M, g ∈ P ∧ g⁻¹ * y * g ∈ Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S₀, hS₀⟩ := hSyl
  have hpgrp : IsPGroup p (zpowers (⟨y, hyP⟩ : P)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord, pow_one])
  obtain ⟨S, hS⟩ := hpgrp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S
  have hyS : (⟨y, hyP⟩ : P) ∈ (S : Subgroup P) := hS (Subgroup.mem_zpowers _)
  have hy'Q : (g : M)⁻¹ * y * (g : M) ∈ Q := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hyS
    rw [hS₀, Subgroup.mem_subgroupOf] at hyS
    simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hyS
  exact ⟨g, g.2, hy'Q⟩

theorem witness_transport {p : ℕ} {r : MulAut A} {m : A} (hm : r m = m) {x y : A}
    (hxy : centralizer ({y} : Set A) = centralizer ({m * x * m⁻¹} : Set A))
    (hw : ∃ l : List A, (∀ g ∈ l, g * x = x * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod)) :
    ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod) := by
  obtain ⟨l, hl, hord'⟩ := hw
  have hconj : MulAut.conj m⁻¹ * r * MulAut.conj m = r := by
    have h := aut_mul_conj_comm_of_fixed hm
    calc MulAut.conj m⁻¹ * r * MulAut.conj m = MulAut.conj m⁻¹ * (r * MulAut.conj m) := by group
      _ = MulAut.conj m⁻¹ * (MulAut.conj m * r) := by rw [h]
      _ = r := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  refine ⟨l.map (fun d => m * d * m⁻¹), ?_, ?_⟩
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
    have hdc : (m * d * m⁻¹) ∈ centralizer ({m * x * m⁻¹} : Set A) := by
      rw [mem_centralizer_singleton_iff]
      calc (m * d * m⁻¹) * (m * x * m⁻¹) = m * (d * x) * m⁻¹ := by group
        _ = m * (x * d) * m⁻¹ := by rw [hl d hd]
        _ = (m * x * m⁻¹) * (m * d * m⁻¹) := by group
    rw [← hxy, mem_centralizer_singleton_iff] at hdc
    exact hdc
  · set Ψ : MulAut (MulAut A) := MulAut.conj (MulAut.conj m) with hΨ
    have hconj' : (MulAut.conj m)⁻¹ * r * MulAut.conj m = r := by
      simpa [map_inv] using hconj
    have step : ∀ d : A, MulAut.conj (m * d * m⁻¹) * r * (MulAut.conj (m * d * m⁻¹))⁻¹ =
        Ψ (MulAut.conj d * r * (MulAut.conj d)⁻¹) := fun d => by
      rw [hΨ, MulAut.conj_apply]
      simp only [map_mul, map_inv]
      calc MulAut.conj m * MulAut.conj d * (MulAut.conj m)⁻¹ * r *
            (MulAut.conj m * MulAut.conj d * (MulAut.conj m)⁻¹)⁻¹
          = MulAut.conj m * MulAut.conj d * ((MulAut.conj m)⁻¹ * r * MulAut.conj m) *
              (MulAut.conj d)⁻¹ * (MulAut.conj m)⁻¹ := by group
        _ = MulAut.conj m * MulAut.conj d * r * (MulAut.conj d)⁻¹ * (MulAut.conj m)⁻¹ := by
            rw [hconj']
        _ = MulAut.conj m * (MulAut.conj d * r * (MulAut.conj d)⁻¹) * (MulAut.conj m)⁻¹ := by group
    have key : ((l.map fun d => m * d * m⁻¹).map
        fun h => MulAut.conj h * r * (MulAut.conj h)⁻¹).prod =
        Ψ ((l.map fun d => MulAut.conj d * r * (MulAut.conj d)⁻¹).prod) := by
      rw [map_list_prod, List.map_map, List.map_map]
      congr 1
      apply List.map_congr_left
      intro d _
      exact step d
    rw [key, MulEquiv.orderOf_eq]
    exact hord'

theorem cover_of_lines_conj [Finite A] {p : ℕ} (hp : p.Prime) (r : MulAut A) {Q : Subgroup A}
    (hSyl : ∃ S : Sylow p (fixSub r), (S : Subgroup (fixSub r)) = Q.subgroupOf (fixSub r))
    {κ : Type*} (xs : κ → A)
    (hcov : ∀ z ∈ Q, orderOf z = p →
      ∃ i, ∃ g : A, r g = g ∧ zpowers z = zpowers (g * xs i * g⁻¹))
    (hwit : ∀ i, ∃ l : List A, (∀ g ∈ l, g * xs i = xs i * g) ∧
      p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod)) :
    ∀ y : A, r y = y → orderOf y = p →
      ∃ l : List A, (∀ g ∈ l, g * y = y * g) ∧
        p ∣ orderOf ((l.map fun g => MulAut.conj g * r * (MulAut.conj g)⁻¹).prod) := by
  intro y hy hord
  obtain ⟨g₁, hg₁P, hz⟩ := exists_conj_into_sylow hp hSyl (mem_fixSub.2 hy) hord
  have hg₁ : r g₁ = g₁ := mem_fixSub.1 hg₁P
  have hzord : orderOf (g₁⁻¹ * y * g₁) = p := by
    have := orderOf_injective (MulAut.conj g₁⁻¹).toMonoidHom (MulAut.conj g₁⁻¹).injective y
    rw [hord] at this
    rw [← this]
    simp [mul_assoc]
  obtain ⟨i, g₂, hg₂, hzp⟩ := hcov _ hz hzord
  refine witness_transport (m := g₁ * g₂) (x := xs i) ?_ ?_ (hwit i)
  · rw [map_mul, hg₁, hg₂]
  · have h1 : centralizer ({g₁⁻¹ * y * g₁} : Set A) = centralizer ({g₂ * xs i * g₂⁻¹} : Set A) := by
      rw [CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
        CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers
          (g₂ * xs i * g₂⁻¹), hzp]
    ext u
    simp only [mem_centralizer_singleton_iff]
    have e1 : u * y = y * u ↔ (g₁⁻¹ * u * g₁) * (g₁⁻¹ * y * g₁) =
        (g₁⁻¹ * y * g₁) * (g₁⁻¹ * u * g₁) := by
      constructor
      · intro h
        calc (g₁⁻¹ * u * g₁) * (g₁⁻¹ * y * g₁) = g₁⁻¹ * (u * y) * g₁ := by group
          _ = g₁⁻¹ * (y * u) * g₁ := by rw [h]
          _ = (g₁⁻¹ * y * g₁) * (g₁⁻¹ * u * g₁) := by group
      · intro h
        have h' : g₁⁻¹ * (u * y) * g₁ = g₁⁻¹ * (y * u) * g₁ := by
          calc g₁⁻¹ * (u * y) * g₁ = (g₁⁻¹ * u * g₁) * (g₁⁻¹ * y * g₁) := by group
            _ = (g₁⁻¹ * y * g₁) * (g₁⁻¹ * u * g₁) := h
            _ = g₁⁻¹ * (y * u) * g₁ := by group
        simpa using h'
    have e2 : u * (g₁ * g₂ * xs i * (g₁ * g₂)⁻¹) = (g₁ * g₂ * xs i * (g₁ * g₂)⁻¹) * u ↔
        (g₁⁻¹ * u * g₁) * (g₂ * xs i * g₂⁻¹) = (g₂ * xs i * g₂⁻¹) * (g₁⁻¹ * u * g₁) := by
      constructor
      · intro h
        calc (g₁⁻¹ * u * g₁) * (g₂ * xs i * g₂⁻¹)
            = g₁⁻¹ * (u * (g₁ * g₂ * xs i * (g₁ * g₂)⁻¹)) * g₁ := by group
          _ = g₁⁻¹ * ((g₁ * g₂ * xs i * (g₁ * g₂)⁻¹) * u) * g₁ := by rw [h]
          _ = (g₂ * xs i * g₂⁻¹) * (g₁⁻¹ * u * g₁) := by group
      · intro h
        have h' : g₁⁻¹ * (u * (g₁ * g₂ * xs i * (g₁ * g₂)⁻¹)) * g₁ =
            g₁⁻¹ * ((g₁ * g₂ * xs i * (g₁ * g₂)⁻¹) * u) * g₁ := by
          calc g₁⁻¹ * (u * (g₁ * g₂ * xs i * (g₁ * g₂)⁻¹)) * g₁
              = (g₁⁻¹ * u * g₁) * (g₂ * xs i * g₂⁻¹) := by group
            _ = (g₂ * xs i * g₂⁻¹) * (g₁⁻¹ * u * g₁) := h
            _ = g₁⁻¹ * ((g₁ * g₂ * xs i * (g₁ * g₂)⁻¹) * u) * g₁ := by group
        simpa using h'
    have e3 : (g₁⁻¹ * u * g₁) * (g₁⁻¹ * y * g₁) = (g₁⁻¹ * y * g₁) * (g₁⁻¹ * u * g₁) ↔
        (g₁⁻¹ * u * g₁) * (g₂ * xs i * g₂⁻¹) = (g₂ * xs i * g₂⁻¹) * (g₁⁻¹ * u * g₁) := by
      have hu : (g₁⁻¹ * u * g₁) ∈ centralizer ({g₁⁻¹ * y * g₁} : Set A) ↔
          (g₁⁻¹ * u * g₁) ∈ centralizer ({g₂ * xs i * g₂⁻¹} : Set A) := by rw [h1]
      simpa only [mem_centralizer_singleton_iff, eq_comm] using hu
    rw [e1, e3, ← e2]

end CFSG.RankThree.PartOne.SPOR
