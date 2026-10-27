module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Geo1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1D10Dist
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalChar
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Parts
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt3
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Stmt4

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem FanTree.card_stabilizer_eq_five_mul (F : FanTree Γ G) {α β : V} (h : pval Γ α = 5)
    (hαβ : Γ.Adj α β) :
    Nat.card (MulAction.stabilizer G α) =
      5 * Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
  have hcard : Nat.card (MulAction.orbit (MulAction.stabilizer G α) β) = 5 := by
    rw [F.orbit_stabilizer_eq_neighborSet hαβ]
    exact h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MulAction.stabilizer (MulAction.stabilizer G α) β)
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (MulAction.stabilizer G α) β),
    hcard] at h1
  rw [h1]
  congr 1
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : G), g.1.2, MulAction.mem_stabilizer_iff.1 g.2⟩
      invFun := fun g => ⟨⟨(g : G), g.2.1⟩, MulAction.mem_stabilizer_iff.2
        (MulAction.mem_stabilizer_iff.1 g.2.2)⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

variable {L : ZLab Γ G}

namespace D10Set

variable {α : V} (D : D10Set L α)

theorem card_nbrStab (F : FanTree Γ G) (h71c : Fan71c F L) (h65 : Fan65 F) :
    Nat.card (nbrStab Γ G α) = 2 ^ 8 * Nat.card D.calpha := by
  have hrel := h65.1 α D.val D.x (D.x_mem_stabilizer F h71c) (D.orderOf_x F)
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer ({D.x} : Set G)) (nbrStab Γ G α)
  rw [hrel] at h1
  have e : Subgroup.centralizer ({D.x} : Set G) ⊓ nbrStab Γ G α = D.calpha := by
    unfold calpha
    exact inf_comm _ _
  rw [e] at h1
  exact h1.symm

theorem relIndex_edge_eq_four (F : FanTree Γ G) (h71c : Fan71c F L) (h86b : Fan86b F L) :
    (nbrStab Γ G α).relIndex
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G (D.beta 0)) = 4 := by
  have hva : Γ.Adj α (D.beta 0) := D.adj_start_beta 0
  obtain ⟨φ, hker, hidx, hdvd, -⟩ := F.exists_edge_char hva
  obtain ⟨⟨w, hw⟩, hact⟩ := h86b α D
  obtain ⟨hwfix, -, -, -⟩ := id hw
  have hv5 : pval Γ α = 5 := D.val
  have hwα : w ∈ MulAction.stabilizer G α := by
    have := (Arc.mem_stab G).1 hwfix 0 (by norm_num)
    rw [D.start 0] at this
    exact this
  have hwβ : w ∈ MulAction.stabilizer G (D.beta 0) :=
    (Arc.mem_stab G).1 hwfix 1 (by norm_num)
  let e : ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G (D.beta 0)) := ⟨w, hwα, hwβ⟩
  have hnot : w ^ 2 ∉ nbrStab Γ G α := by
    intro hK
    have h1 : w⁻¹ • D.beta 1 = D.beta 2 := hact w hw 1 1 (by norm_num)
    have h2 : w⁻¹ • D.beta 2 = D.beta 4 := hact w hw 2 1 (by norm_num)
    have h3 : (w ^ 2)⁻¹ • D.beta 1 = D.beta 1 :=
      mem_nbrStab.1 (inv_mem hK) (D.beta 1) (D.adj_start_beta 1)
    have h4 : (w ^ 2)⁻¹ • D.beta 1 = D.beta 4 := by
      rw [show (w ^ 2)⁻¹ = w⁻¹ * w⁻¹ by group, mul_smul, h1, h2]
    rw [h3] at h4
    exact absurd (D.beta_injective F h71c h4) (by decide)
  have hφ : φ e ^ 2 ≠ 1 := by
    intro h1
    apply hnot
    have h2 : φ (e ^ 2) = 1 := by rw [map_pow]; exact h1
    have := (hker (e ^ 2)).2 h2
    simpa [e] using this
  have hmem : φ e ∈ φ.range := ⟨e, rfl⟩
  have hd1 : orderOf (φ e) ∣ Nat.card φ.range := Subgroup.orderOf_dvd_natCard φ.range hmem
  have hd2 : Nat.card φ.range ∣ 4 := by
    have := hdvd
    rwa [show pval Γ α - 1 = 4 by omega] at this
  have hd : orderOf (φ e) ∣ 2 ^ 2 := by simpa using hd1.trans hd2
  obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have h4 : orderOf (φ e) = 4 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · have h1 : orderOf (φ e) = 1 := by simpa using hord
      exact absurd (by rw [orderOf_eq_one_iff.1 h1]; simp) hφ
    · have h2 : orderOf (φ e) = 2 := by simpa using hord
      exact absurd (by rw [← h2]; exact pow_orderOf_eq_one (φ e)) hφ
    · simpa using hord
  have h5 : 4 ∣ Nat.card φ.range := by
    have := hd1
    rwa [h4] at this
  rw [hidx]
  exact Nat.dvd_antisymm hd2 h5

theorem card_stabilizer (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L)
    (h65 : Fan65 F) :
    Nat.card (MulAction.stabilizer G α) = 5 * 2 ^ 10 * Nat.card D.calpha := by
  have h71c : Fan71c F L := h7.2.2.1
  have h86b := h8.fan86.2.1
  have hva : Γ.Adj α (D.beta 0) := D.adj_start_beta 0
  have h1 := F.card_stabilizer_eq_five_mul D.val hva
  have h2 := Subgroup.relIndex_mul_card (nbrStab Γ G α)
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G (D.beta 0))
  rw [D.relIndex_edge_eq_four F h71c h86b, inf_eq_left.2 (F.nbrStab_le_edge α hva)] at h2
  rw [h1, ← h2, D.card_nbrStab F h71c h65]
  ring

theorem card_calpha (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L)
    (h512 : Fan512 F L) :
    Nat.card D.calpha = 2 ∨ Nat.card D.calpha = 4 := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨-, hle⟩ := h8.fan84a α D
  have hz : L.z α ∈ D.calpha := D.z_mem_calpha F h71c h512
  have hfin : Finite ↥D.calpha := by
    have := F.loc_finite α
    have hle' : D.calpha ≤ MulAction.stabilizer G α := inf_le_left.trans (F.nbrStab_le_stabilizer α)
    exact Finite.of_injective (Subgroup.inclusion hle') (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card D.calpha := Nat.card_pos
  have hord : orderOf (L.z α) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ (L.z_ne_one D.val)
    rw [pow_two]
    exact L.z_mul_self D.val
  have hd : 2 ∣ Nat.card D.calpha := hord ▸ Subgroup.orderOf_dvd_natCard D.calpha hz
  omega

theorem card_stabilizer_cases (F : FanTree Γ G) (h7 : Fan7 F L) (h8 : Fan8Parts F L)
    (h65 : Fan65 F) (h512 : Fan512 F L) :
    (Nat.card D.calpha = 2 ∧ Nat.card (MulAction.stabilizer G α) = 5 * 2 ^ 11) ∨
      (Nat.card D.calpha = 4 ∧ Nat.card (MulAction.stabilizer G α) = 5 * 2 ^ 12) := by
  have h := D.card_stabilizer F h7 h8 h65
  rcases D.card_calpha F h7 h8 h512 with h2 | h4
  · left
    exact ⟨h2, by rw [h, h2]; norm_num⟩
  · right
    exact ⟨h4, by rw [h, h4]; norm_num⟩

end D10Set

end CFSG.Quasithin.Fan86
