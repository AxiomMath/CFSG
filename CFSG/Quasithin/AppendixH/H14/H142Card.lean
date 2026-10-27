module

public import CFSG.Quasithin.AppendixH.H14.H142Arr
public import CFSG.Quasithin.AppendixH.H14.H142M23Data
public import CFSG.Quasithin.AppendixH.H14.H142StdDefs

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.ASVolI CFSG.ASVolI.ChH CFSG.Quasithin.H.Mathieu
open scoped Pointwise

theorem card_M23g (a : Fin 24) : Nat.card ↥(M23g a) = 10200960 := by
  obtain ⟨b, hb⟩ := exists_ne a
  obtain ⟨τ, hτ, hτ0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two a b hb.symm
  have hmap : mog23.map (MulAut.conj τ).toMonoidHom = M23g a := by
    refine map_conj_eq_of_iff τ hτ mog23 (M23g a) (fun x => x a = a) (fun h => h 0 = 0)
      (fun x => mem_M23g_iff a x) (fun h => ?_) (fun h => ?_)
    · show h ∈ M24g ⊓ stab 0 ↔ _
      rw [Subgroup.mem_inf, mem_stab_iff]
    · have e : τ⁻¹ a = 0 := by rw [← hτ0, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
      show (τ * h * τ⁻¹) a = a ↔ h 0 = 0
      simp only [Equiv.Perm.mul_apply, e]
      rw [← hτ0, EmbeddingLike.apply_eq_iff_eq]
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj τ).injective, card_mog23]

theorem gens23_mem : ∀ a ∈ gens23, ∃ σ ∈ M23g 8, HasArr σ a := by
  intro a ha
  obtain ⟨h1, h2⟩ := gens23_ok a ha
  exact ⟨permOfArrD a, mem_M23g_of_arr (hasArr_permOfArrD h1) h1 8 h2, hasArr_permOfArrD h1⟩

theorem card_MQ_le : Nat.card ↥(M23g 8 ⊓ MulAction.stabilizer S24 stdQ) ≤ 5760 := by
  have hsub : M23g 8 ⊓ MulAction.stabilizer S24 stdQ ≤
      M23g 8 ⊓ MulAction.stabilizer S24 (maskSetOf 1067264) := by
    intro g hg
    rw [Subgroup.mem_inf] at hg ⊢
    refine ⟨hg.1, ?_⟩
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← stdB_eq, smul_stdB_of_stdQ hg.2]
  have hle := Subgroup.card_le_of_le hsub
  have hbound := card_inf_stabilizer_mul_le (G := M23g 8) (m₀ := 1067264) (L := bfsB)
    gens23_mem bfsB_ok bfsB_nodup bfsB_lt
  rw [bfsB_length, card_M23g 8] at hbound
  have h2 : Nat.card ↥(M23g 8 ⊓ MulAction.stabilizer S24 stdQ) * 1771 ≤ 10200960 :=
    (Nat.mul_le_mul_right 1771 hle).trans hbound
  rw [show 10200960 = (5760 : ℕ) * 1771 by norm_num] at h2
  exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

theorem card_MH_le : Nat.card ↥(M23g 8 ⊓ MulAction.stabilizer S24 stdH) ≤ 40320 := by
  have hsub : M23g 8 ⊓ MulAction.stabilizer S24 stdH ≤
      M23g 8 ⊓ MulAction.stabilizer S24 (maskSetOf 9857280) := by
    intro g hg
    rw [Subgroup.mem_inf] at hg ⊢
    refine ⟨hg.1, ?_⟩
    have h8 : g 8 = 8 := ((CFSG.ASVolI.mem_M23g_iff 8 g).1 hg.1).2
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← stdO_eq, smul_stdO_of_stdH h8 hg.2]
  have hle := Subgroup.card_le_of_le hsub
  have hbound := card_inf_stabilizer_mul_le (G := M23g 8) (m₀ := 9857280) (L := bfsO)
    gens23_mem bfsO_ok bfsO_nodup bfsO_lt
  rw [bfsO_length, card_M23g 8] at hbound
  have h2 : Nat.card ↥(M23g 8 ⊓ MulAction.stabilizer S24 stdH) * 253 ≤ 10200960 :=
    (Nat.mul_le_mul_right 253 hle).trans hbound
  rw [show 10200960 = (40320 : ℕ) * 253 by norm_num] at h2
  exact Nat.le_of_mul_le_mul_right h2 (by norm_num)

end CFSG.Quasithin.AppendixH.H14
