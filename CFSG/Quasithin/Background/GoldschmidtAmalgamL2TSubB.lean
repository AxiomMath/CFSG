module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSubA
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2SQA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL2S

open scoped Pointwise

namespace F6

namespace GoldAmL2T

variable {D : Type*} [Group D]

@[expose] def evenSub (H : Subgroup D) (π : ↥H →* Equiv.Perm (Fin 3)) : Subgroup D :=
  ((alternatingGroup (Fin 3)).comap π).map H.subtype

theorem mem_evenSub {H : Subgroup D} {π : ↥H →* Equiv.Perm (Fin 3)} {x : D} (hx : x ∈ H) :
    x ∈ evenSub H π ↔ π ⟨x, hx⟩ ∈ alternatingGroup (Fin 3) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem card_evenSub {H : Subgroup D} {π : ↥H →* Equiv.Perm (Fin 3)}
    (hπ : Function.Surjective π) : 2 * Nat.card ↥(evenSub H π) = Nat.card ↥H := by
  have h1 : ((alternatingGroup (Fin 3)).comap π).index = 2 := by
    rw [Subgroup.index_comap_of_surjective (alternatingGroup (Fin 3)) hπ]
    exact alternatingGroup.index_eq_two
  have h2 := Subgroup.card_mul_index ((alternatingGroup (Fin 3)).comap π)
  rw [h1] at h2
  have h3 : Nat.card ↥(evenSub H π) = Nat.card ↥((alternatingGroup (Fin 3)).comap π) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [h3]
  omega

theorem sign_eq_one_of_cube {H : Subgroup D} {π : ↥H →* Equiv.Perm (Fin 3)} {x : ↥H}
    (hx : x ^ 3 = 1) : Equiv.Perm.sign (π x) = 1 := by
  apply units_eq_one_of_pow_three
  rw [← map_pow, ← map_pow, hx, map_one, map_one]

namespace SubData

variable [Finite D] {H T N W : Subgroup D} {w : D} (d : SubData H T N W w)

include d

theorem M_le_evenSub {π : ↥H →* Equiv.Perm (Fin 3)}
    (hπk : ∀ x : ↥H, π x = 1 ↔ (x : D) ∈ pCoreOf 2 H) :
    N ⊔ Subgroup.zpowers w ≤ evenSub H π := by
  refine sup_le (fun n hn => ?_) (Subgroup.zpowers_le.mpr ?_)
  · rw [mem_evenSub (d.N_le_H hn)]
    rw [(hπk ⟨n, d.N_le_H hn⟩).mpr (d.N_le hn)]
    exact Subgroup.one_mem _
  · rw [mem_evenSub d.w_mem, Equiv.Perm.mem_alternatingGroup]
    refine sign_eq_one_of_cube (π := π) ?_
    exact Subtype.ext (by simpa [pow_three'] using d.w_cube)

theorem relIndex_M_evenSub {π : ↥H →* Equiv.Perm (Fin 3)} (hπ : Function.Surjective π)
    (hπk : ∀ x : ↥H, π x = 1 ↔ (x : D) ∈ pCoreOf 2 H) :
    (N ⊔ Subgroup.zpowers w).relIndex (evenSub H π) = 2 := by
  have h1 := card_eq_relIndex_mul (d.M_le_evenSub hπk)
  have h2 := card_evenSub hπ
  rw [d.card_H] at h2
  rw [d.card_M] at h1
  have hpos : 0 < 3 * Nat.card ↥N := by have := Nat.card_pos (α := ↥N); omega
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  linarith

theorem conj_w_mem_M {π : ↥H →* Equiv.Perm (Fin 3)} (hπ : Function.Surjective π)
    (hπk : ∀ x : ↥H, π x = 1 ↔ (x : D) ∈ pCoreOf 2 H) {g : D} (hg : g ∈ H) :
    g * w * g⁻¹ ∈ N ⊔ Subgroup.zpowers w := by
  have hhH : g * w * g⁻¹ ∈ H := H.mul_mem (H.mul_mem hg d.w_mem) (H.inv_mem hg)
  have hh3 : (g * w * g⁻¹) * (g * w * g⁻¹) * (g * w * g⁻¹) = 1 := by
    calc (g * w * g⁻¹) * (g * w * g⁻¹) * (g * w * g⁻¹) = g * (w * w * w) * g⁻¹ := by group
      _ = 1 := by rw [d.w_cube]; group
  have hcube : (⟨g * w * g⁻¹, hhH⟩ : ↥H) ^ 3 = 1 :=
    Subtype.ext (by simpa [pow_three'] using hh3)
  have hmem : g * w * g⁻¹ ∈ evenSub H π :=
    (mem_evenSub hhH).mpr (Equiv.Perm.mem_alternatingGroup.mpr (sign_eq_one_of_cube hcube))
  have hsq : (g * w * g⁻¹) * (g * w * g⁻¹) ∈ N ⊔ Subgroup.zpowers w :=
    sq_mem_of_relIndex_two (d.relIndex_M_evenSub hπ hπk) hmem
  have hmain : ((g * w * g⁻¹) * (g * w * g⁻¹)) * ((g * w * g⁻¹) * (g * w * g⁻¹)) ∈
      N ⊔ Subgroup.zpowers w := (N ⊔ Subgroup.zpowers w).mul_mem hsq hsq
  have e : ((g * w * g⁻¹) * (g * w * g⁻¹)) * ((g * w * g⁻¹) * (g * w * g⁻¹)) = g * w * g⁻¹ := by
    calc ((g * w * g⁻¹) * (g * w * g⁻¹)) * ((g * w * g⁻¹) * (g * w * g⁻¹))
        = (g * w * g⁻¹) * ((g * w * g⁻¹) * (g * w * g⁻¹) * (g * w * g⁻¹)) := by group
      _ = g * w * g⁻¹ := by rw [hh3, mul_one]
  rwa [e] at hmain

theorem M_normal : H ≤ Subgroup.normalizer ((N ⊔ Subgroup.zpowers w : Subgroup D) : Set D) := by
  obtain ⟨π, hπ, hπk⟩ := d.vertex.exists_hom
  refine le_normalizer_of_conj_mem fun g hg m hm => ?_
  have hle : N ⊔ Subgroup.zpowers w ≤
      (N ⊔ Subgroup.zpowers w).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun n hn => ?_) (Subgroup.zpowers_le.mpr ?_)
    · show (MulAut.conj g) n ∈ N ⊔ Subgroup.zpowers w
      rw [MulAut.conj_apply]
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (d.N_norm hg) n).mp hn)
    · show (MulAut.conj g) w ∈ N ⊔ Subgroup.zpowers w
      rw [MulAut.conj_apply]
      exact d.conj_w_mem_M hπ hπk hg
  exact hle hm

theorem M_le_H : N ⊔ Subgroup.zpowers w ≤ H :=
  sup_le d.N_le_H (Subgroup.zpowers_le.mpr d.w_mem)

theorem W_norm_M :
    W ≤ Subgroup.normalizer ((N ⊔ Subgroup.zpowers w : Subgroup D) : Set D) :=
  d.W_le_H.trans d.M_normal

theorem H'_le_H : (N ⊔ Subgroup.zpowers w) ⊔ W ≤ H := sup_le d.M_le_H d.W_le_H

theorem W_inf_M : W ⊓ (N ⊔ Subgroup.zpowers w) = W ⊓ N := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, d.M_inf_T_le ⟨hx.2, d.W_le hx.1⟩⟩
  · exact inf_le_inf_left W le_sup_left

end SubData

end GoldAmL2T

end F6

end CFSG.Quasithin
