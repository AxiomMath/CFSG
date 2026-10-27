module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureNontrivialTwoCoreSection

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore

open CFSG.SolvableHall
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem exists_normalizer_mul_of_hall {H C M W : Subgroup G} (hMC : M ≤ C) (hWC : W ≤ C)
    (hCH : C ≤ H) (hCn : ∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C)
    (hMn : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) (hMWC : M ⊔ W = C) (hinf : M ⊓ W = ⊥)
    (hMsolv : Group.IsSolvable M) (hcop : Nat.Coprime (Nat.card M) (Nat.card W))
    {h : G} (hh : h ∈ H) :
    ∃ n ∈ H ⊓ Subgroup.normalizer (W : Set G), ∃ m ∈ M, h = n * m := by
  classical
  have hWH : W ≤ H := hWC.trans hCH
  have hWN : W ≤ Subgroup.normalizer (M : Set G) :=
    le_normalizer_of_forall_conj_mem fun w hw m hm => hMn w (hWH hw) m hm
  have hMW : ∀ c ∈ C, ∃ m ∈ M, ∃ w ∈ W, m * w = c := by
    intro c hc
    have hc' : c ∈ ((M ⊔ W : Subgroup G) : Set G) := by rw [hMWC]; exact hc
    rw [Subgroup.coe_mul_of_right_le_normalizer_left M W hWN] at hc'
    obtain ⟨m, hm, w, hw, rfl⟩ := hc'
    exact ⟨m, hm, w, hw, rfl⟩
  set N : Subgroup C := M.subgroupOf C with hNdef
  have hNn : N.Normal := ⟨fun n hn c => by
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hMn c (hCH c.2) n hn⟩
  have hNsolv : Group.IsSolvable N :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hMC).symm.toMonoidHom)
      (MulEquiv.surjective _)
  set W' : Subgroup C := W.subgroupOf C with hW'def
  have hNW : (N : Set C) * (W' : Set C) = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨m, hm, w, hw, hmw⟩ := hMW c c.2
    exact Set.mem_mul.mpr ⟨⟨m, hMC hm⟩, hm, ⟨w, hWC hw⟩, hw, Subtype.ext hmw⟩
  have hNW' : N ⊓ W' = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcM, hcW⟩
    have hc : (c : G) ∈ M ⊓ W := ⟨hcM, hcW⟩
    rw [hinf, Subgroup.mem_bot] at hc
    exact (Subgroup.mem_bot).mpr (Subtype.ext hc)
  have hcompl : Subgroup.IsComplement' N W' :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hNW') hNW
  have hNcard : Nat.card N = Nat.card M := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMC).toEquiv
  have hW'card : Nat.card W' = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
  have hNidx : N.index = Nat.card W := by
    have h1 := hcompl.card_mul_card
    have h2 := N.card_mul_index
    rw [← hW'card]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
  have hcop' : Nat.Coprime (Nat.card N) N.index := by rwa [hNcard, hNidx]
  set Wh : Subgroup G := W.map (MulAut.conj h⁻¹).toMonoidHom with hWhdef
  have hmemWh : ∀ x, x ∈ Wh ↔ h * x * h⁻¹ ∈ W := by
    intro x
    rw [hWhdef, Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have heq : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
      rw [heq]
      exact hw
    · intro hx
      refine ⟨h * x * h⁻¹, hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  have hWhC : Wh ≤ C := by
    intro x hx
    have h1 := hCn h⁻¹ (H.inv_mem hh) _ (hWC ((hmemWh x).mp hx))
    have heq : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [heq] at h1
  set Wh' : Subgroup C := Wh.subgroupOf C with hWh'def
  have hNWh : (N : Set C) * (Wh' : Set C) = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨m, hm, w, hw, hmw⟩ := hMW _ (hCn h hh c c.2)
    have hm' : h⁻¹ * m * h⁻¹⁻¹ ∈ M := hMn h⁻¹ (H.inv_mem hh) m hm
    have hw' : h⁻¹ * w * h⁻¹⁻¹ ∈ Wh := by
      rw [hmemWh]
      have heq : h * (h⁻¹ * w * h⁻¹⁻¹) * h⁻¹ = w := by group
      rw [heq]
      exact hw
    refine Set.mem_mul.mpr ⟨⟨_, hMC hm'⟩, hm', ⟨_, hWhC hw'⟩, hw', Subtype.ext ?_⟩
    change h⁻¹ * m * h⁻¹⁻¹ * (h⁻¹ * w * h⁻¹⁻¹) = c
    calc h⁻¹ * m * h⁻¹⁻¹ * (h⁻¹ * w * h⁻¹⁻¹) = h⁻¹ * (m * w) * h := by group
      _ = c := by rw [hmw]; group
  have hNWh' : N ⊓ Wh' = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcM, hcW⟩
    have hcW' : h * c * h⁻¹ ∈ W := (hmemWh c).mp hcW
    have hcM' : h * c * h⁻¹ ∈ M := hMn h hh c hcM
    have hc : h * c * h⁻¹ ∈ M ⊓ W := ⟨hcM', hcW'⟩
    rw [hinf, Subgroup.mem_bot] at hc
    exact (Subgroup.mem_bot).mpr (Subtype.ext (by
      rw [OneMemClass.coe_one]
      calc (c : G) = h⁻¹ * (h * c * h⁻¹) * h := by group
        _ = 1 := by rw [hc]; group))
  have := hNn
  obtain ⟨n, hnN, hconj⟩ :=
    solvable_normal_hall_complement_conjugacy N hNsolv hcop' hNW hNWh hNW' hNWh'
  have hnM : (n : G) ∈ M := hnN
  refine ⟨h * (n : G)⁻¹, Subgroup.mem_inf.mpr ⟨H.mul_mem hh (H.inv_mem (hCH n.2)), ?_⟩, n, hnM,
    by group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : MulAut.conj n⁻¹ (⟨x, hWC hx⟩ : C) ∈ Wh' := by
      rw [hconj]
      exact Subgroup.mem_map_of_mem _ hx
    have h2 : ((MulAut.conj n⁻¹ (⟨x, hWC hx⟩ : C) : C) : G) ∈ Wh := h1
    rw [hmemWh] at h2
    have heq : h * ((MulAut.conj n⁻¹ (⟨x, hWC hx⟩ : C) : C) : G) * h⁻¹ =
        h * (n : G)⁻¹ * x * (h * (n : G)⁻¹)⁻¹ := by
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rwa [heq] at h2
  · intro hx
    set w := h * (n : G)⁻¹ * x * (h * (n : G)⁻¹)⁻¹ with hwdef
    have hwh : h⁻¹ * w * h ∈ Wh := by
      rw [hmemWh]
      have heq : h * (h⁻¹ * w * h) * h⁻¹ = w := by group
      rw [heq]
      exact hx
    have hwhC : h⁻¹ * w * h ∈ C := hWhC hwh
    have h1 : (⟨h⁻¹ * w * h, hwhC⟩ : C) ∈ Wh' := hwh
    rw [hconj, Subgroup.mem_map] at h1
    obtain ⟨w', hw', hw'eq⟩ := h1
    have h2 := congrArg Subtype.val hw'eq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, inv_inv] at h2
    have hxw : x = (w' : G) := by
      have heq : (w' : G) = (n : G) * (h⁻¹ * w * h) * (n : G)⁻¹ := by
        rw [← h2]
        group
      rw [heq, hwdef]
      group
    rw [hxw]
    exact hw'

end CFSG.ShultStronglyClosedTI.LinearChain.NontrivialTwoCore
