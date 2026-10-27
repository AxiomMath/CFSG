module

public import CFSG.Quasithin.EmptyFaithful.S153YGD0

public section

namespace CFSG.Quasithin.YG.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace GCfg

variable {H S L : Subgroup G} (C : GCfg H S L)
include C

theorem card_Q : Nat.card ↥(pCoreOf 2 H) = 16 * Nat.card ↥(blockD S L) := by
  have h := B2F.card_sup_mul_card_inf_of_commute
    (fun u hu d hd => C.U_comm_D hu hd : ∀ u ∈ C.U, ∀ d ∈ blockD S L, u * d = d * u)
  rw [C.U_inf_D, Subgroup.card_bot, C.card_U] at h
  rw [C.Q_eq]
  omega

theorem S_inf_centralizer : S ⊓ Subgroup.centralizer (C.U : Set G) = pCoreOf 2 H := by
  refine le_antisymm (fun y hy => ?_) (le_inf C.hQS fun y hy => ?_)
  · rw [← C.hQ]
    exact ⟨C.hSH hy.1, hy.2⟩
  · exact Subgroup.mem_centralizer_iff.2 fun u hu => (C.Q_comm_U hy hu).symm

theorem card_S : Nat.card ↥S = 8 * (16 * Nat.card ↥(blockD S L)) := by
  have h := C.P.card_im_mul (A := S) le_rfl
  rw [C.hS, Dstd_card, C.S_inf_centralizer, C.card_Q] at h
  exact h.symm

end GCfg

namespace GMate

variable {H S L M₀ : Subgroup G} {x : G} (C : GCfg H S L) (m : GMate H S M₀ x)
include C m

theorem Dx_le_B : conjR (blockD S L) x ≤ baum S := by
  have := C5.conjSubgroup_mono (m.D_le_B C) x
  rwa [C5.conjSubgroup_eq_self (normalizer_le_normalizer_baum S m.xN)] at this

theorem Dx_comm_U {d' u : G} (hd' : d' ∈ conjR (blockD S L) x) (hu : u ∈ C.U) :
    d' * u = u * d' := by
  have hd : x * d' * x⁻¹ ∈ blockD S L := mem_conjSubgroup_iff.1 hd'
  have hv : x * u * x⁻¹ ∈ conjR C.U x := by
    rw [C56.conjR_eq, mem_conjSubgroup_iff]
    have e : x * (x * u * x⁻¹) * x⁻¹ = (x * x) * u * (x * x)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (C.P.hSU m.xx) u).1 hu
  have h := m.D_comm_V C hd hv
  have e : x * d' * x⁻¹ * (x * u * x⁻¹) = x * (d' * u) * x⁻¹ := by group
  have e' : x * u * x⁻¹ * (x * d' * x⁻¹) = x * (u * d') * x⁻¹ := by group
  rw [e, e'] at h
  exact mul_left_cancel (mul_right_cancel h)

omit m in
theorem Dx_comm_V {d' v : G} (hd' : d' ∈ conjR (blockD S L) x) (hv : v ∈ conjR C.U x) :
    d' * v = v * d' := by
  have hd : x * d' * x⁻¹ ∈ blockD S L := mem_conjSubgroup_iff.1 hd'
  have hu : x * v * x⁻¹ ∈ C.U := mem_conjSubgroup_iff.1 hv
  have h := C.U_comm_D hu hd
  have e : x * v * x⁻¹ * (x * d' * x⁻¹) = x * (v * d') * x⁻¹ := by group
  have e' : x * d' * x⁻¹ * (x * v * x⁻¹) = x * (d' * v) * x⁻¹ := by group
  rw [e, e'] at h
  exact (mul_left_cancel (mul_right_cancel h)).symm

theorem Dx_le_D_sup_W : conjR (blockD S L) x ≤ blockD S L ⊔ (C.U ⊓ conjR C.U x) := by
  intro d' hd'
  have hB : d' ∈ baum S := m.Dx_le_B C hd'
  rw [m.B_eq C] at hB
  have hN : conjR C.U x ≤ conjR C.U x := le_rfl
  have hDU : blockD S L ⊔ C.U ≤ Subgroup.normalizer (conjR C.U x : Set G) :=
    sup_le (fun d hd => m.S_le_N_V C hd.1) (fun u hu => m.S_le_N_V C (C.hUS hu))
  have hB' : d' ∈ ((blockD S L ⊔ C.U : Subgroup G) : Set G) * ((conjR C.U x : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (blockD S L ⊔ C.U) (conjR C.U x) hDU]
    exact hB
  obtain ⟨a, ha, v, hv, hdeq⟩ := hB'
  have hdeq' : d' = a * v := hdeq.symm
  subst hdeq'
  obtain ⟨d₀, hd₀, u, hu, rfl⟩ := C5.mem_sup_of_commute
    (fun d hd u hu => (C.U_comm_D hu hd).symm : ∀ d ∈ blockD S L, ∀ u ∈ C.U, d * u = u * d) ha
  set w : G := u * v with hw
  have hd₀U : ∀ u' ∈ C.U, d₀ * u' = u' * d₀ := fun u' hu' => (C.U_comm_D hu' hd₀).symm
  have hd₀V : ∀ v' ∈ conjR C.U x, d₀ * v' = v' * d₀ := fun v' hv' => m.D_comm_V C hd₀ hv'
  have hwU : ∀ u' ∈ C.U, w * u' = u' * w := by
    intro u' hu'
    have h1 := Dx_comm_U C m hd' hu'
    have h2 := hd₀U u' hu'
    have e : d₀ * u * v * u' = d₀ * (u * v * u') := by group
    have e' : u' * (d₀ * u * v) = d₀ * (u' * (u * v)) := by
      calc u' * (d₀ * u * v) = (u' * d₀) * (u * v) := by group
        _ = (d₀ * u') * (u * v) := by rw [h2]
        _ = d₀ * (u' * (u * v)) := by group
    rw [e, e'] at h1
    exact mul_left_cancel h1
  have hwV : ∀ v' ∈ conjR C.U x, w * v' = v' * w := by
    intro v' hv'
    have h1 := Dx_comm_V C hd' hv'
    have h2 := hd₀V v' hv'
    have e : d₀ * u * v * v' = d₀ * (u * v * v') := by group
    have e' : v' * (d₀ * u * v) = d₀ * (v' * (u * v)) := by
      calc v' * (d₀ * u * v) = (v' * d₀) * (u * v) := by group
        _ = (d₀ * v') * (u * v) := by rw [h2]
        _ = d₀ * (v' * (u * v)) := by group
    rw [e, e'] at h1
    exact mul_left_cancel h1
  have hvU : v ∈ C.U ⊓ conjR C.U x := by
    have hvc : v ∈ conjR C.U x ⊓ Subgroup.centralizer (C.U : Set G) := by
      refine ⟨hv, Subgroup.mem_centralizer_iff.2 fun u' hu' => ?_⟩
      have h1 := hwU u' hu'
      have h2 : u * u' = u' * u := B2F.isElemAbelian_comm C.hU hu hu'
      have e : u * v * u' = u * (v * u') := by group
      have e' : u' * (u * v) = (u' * u) * v := by group
      rw [hw, e, e', ← h2, mul_assoc] at h1
      exact (mul_left_cancel h1).symm
    rw [(m.cent_U_V C).2.1]
    exact hvc
  have hwW : w ∈ C.U ⊓ conjR C.U x := by
    have hwU' : w ∈ C.U := mul_mem hu hvU.1
    have hwc : w ∈ C.U ⊓ Subgroup.centralizer (conjR C.U x : Set G) :=
      ⟨hwU', Subgroup.mem_centralizer_iff.2 fun v' hv' => (hwV v' hv').symm⟩
    rw [(m.cent_U_V C).1] at hwc
    exact hwc
  have e : d₀ * u * v = d₀ * w := by rw [hw]; group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hd₀) (Subgroup.mem_sup_right hwW)

theorem card_blockD_le_four : Nat.card ↥(blockD S L) ≤ 4 := by
  set D := blockD S L with hD
  set D' := conjR D x with hD'
  set W := C.U ⊓ conjR C.U x with hW
  have hW4 : Nat.card ↥W = 4 := (m.cent_U_V C).2.2
  have hDe : IsElemAbelian 2 D := m.D_elem C
  have hDW : ∀ a ∈ D, ∀ b ∈ W, a * b = b * a := fun a ha b hb => (C.U_comm_D hb.1 ha).symm
  have hDW0 : D ⊓ W = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun y hy => ?_
    have : y ∈ C.U ⊓ D := ⟨hy.2.1, hy.1⟩
    rw [C.U_inf_D] at this
    exact this
  have hDD' : ∀ a ∈ D, ∀ b ∈ D', a * b = b * a := by
    intro a ha b hb
    obtain ⟨d₀, hd₀, w, hw, rfl⟩ := C5.mem_sup_of_commute hDW (m.Dx_le_D_sup_W C hb)
    have h1 : a * d₀ = d₀ * a := B2F.isElemAbelian_comm hDe ha hd₀
    calc a * (d₀ * w) = (a * d₀) * w := by group
      _ = (d₀ * a) * w := by rw [h1]
      _ = d₀ * (a * w) := by group
      _ = d₀ * (w * a) := by rw [hDW a ha w hw]
      _ = d₀ * w * a := by group
  have h1 := B2F.card_sup_mul_card_inf_of_commute hDD'
  rw [m.D_inf_conj C, Subgroup.card_bot, mul_one] at h1
  have h2 := B2F.card_sup_mul_card_inf_of_commute hDW
  rw [hDW0, Subgroup.card_bot, mul_one, hW4] at h2
  have h3 : Nat.card ↥(D ⊔ D') ≤ Nat.card ↥(D ⊔ W) :=
    Subgroup.card_le_of_le (sup_le le_sup_left (m.Dx_le_D_sup_W C))
  have h4 : Nat.card ↥D' = Nat.card ↥D := C5.card_conjSubgroup D x
  have hpos : 0 < Nat.card ↥D := Nat.card_pos
  rw [h1, h2, h4] at h3
  nlinarith

theorem card_S_le : Nat.card ↥S ≤ 2 ^ 9 := by
  rw [C.card_S]
  have := m.card_blockD_le_four C
  omega

end GMate

end CFSG.Quasithin.YG.AppD
