module

public import CFSG.LocalAnalysis.StandardType.FF81.ConstructYRoot
import CFSG.ClassicalInvolution.WeakCT.Blocks
import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT (blockSL blockSL2 blockSL_comp blockSL_comm
  blockSL2_injective iSup_range_blockSL2)
open scoped MatrixGroups

theorem centralizer_inf_range_eq_map {H G : Type*} [Group H] [Group G] {f : H →* G}
    (hf : Function.Injective f) (x : H) :
    Subgroup.centralizer ({f x} : Set G) ⊓ f.range =
      (Subgroup.centralizer ({x} : Set H)).map f := by
  ext g
  constructor
  · rintro ⟨hg, ⟨y, rfl⟩⟩
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr (hf ?_), rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ⟨y, rfl⟩⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hy]

theorem range_blockSL_two_eq_iSup (F : Type) [Field F] (k : ℕ) :
    (blockSL F (k + 2 + 1) (k + 1) 2 (by omega)).range =
      ⨆ j : Fin k, (blockSL2 F (k + 2) ⟨(j : ℕ) + 2, by omega⟩).range := by
  rw [MonoidHom.range_eq_map, ← iSup_range_blockSL2 (K := F) k, Subgroup.map_iSup]
  refine iSup_congr fun j => ?_
  rw [← MonoidHom.range_comp]
  have hc : (blockSL F (k + 2 + 1) (k + 1) 2 (by omega)).comp (blockSL2 F k j) =
      blockSL2 F (k + 2) ⟨2 + (j : ℕ), by omega⟩ := blockSL_comp _ _
  rw [hc, show (⟨2 + (j : ℕ), by omega⟩ : Fin (k + 2)) = ⟨(j : ℕ) + 2, by omega⟩ from
    Fin.ext (Nat.add_comm _ _)]

private theorem sl2_eq_rho_or_inv :
    ∀ A : SL(2, ZMod 2), A ^ 3 = 1 → A ≠ 1 →
      (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1] ∨
        ((A⁻¹ : SL(2, ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1] := by
  decide +kernel

theorem eq_or_eq_inv_of_mem_map_blockSL2 {G : Type} [Group G] {m : ℕ}
    {ψ : SL(m + 1, ZMod 2) →* G} (hinj : Function.Injective ψ) {ρ : SL(2, ZMod 2)}
    (hρ : (ρ : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1]) (i : Fin m) {b : G}
    (hb : orderOf b = 3) (hbK : b ∈ (blockSL2 (ZMod 2) m i).range.map ψ) :
    b = ψ (blockSL2 (ZMod 2) m i ρ) ∨ b = (ψ (blockSL2 (ZMod 2) m i ρ))⁻¹ := by
  obtain ⟨_, ⟨A, rfl⟩, hA⟩ := hbK
  have hA3 : orderOf A = 3 := by
    have h := orderOf_injective (ψ.comp (blockSL2 (ZMod 2) m i))
      (hinj.comp (blockSL2_injective m i)) A
    rw [MonoidHom.comp_apply, hA, hb] at h
    exact h.symm
  have hA1 : A ^ 3 = 1 := hA3 ▸ pow_orderOf_eq_one A
  have hA0 : A ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hA3
    exact absurd hA3 (by decide)
  rcases sl2_eq_rho_or_inv A hA1 hA0 with h | h
  · left
    rw [← hA, show A = ρ from Subtype.ext (h.trans hρ.symm)]
  · right
    rw [← hA, ← show A⁻¹ = ρ from Subtype.ext (h.trans hρ.symm), map_inv, map_inv, inv_inv]

variable {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G} {K : ℕ → Subgroup G}
  {t : G}

theorem FrameSystem.cen_b_of_commute_of_tOne (hF : FrameSystem n b L K t) (hn : 3 ≤ n)
    (hb : orderOf b = 3) (h1n : ∀ a ∈ K 1, ∀ c ∈ K n, a * c = c * a) {ρ : SL(2, ZMod 2)}
    (hρ : (ρ : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 1])
    (hmat : ∀ g : SL(n + 2 + 1, ZMod 2),
      g * blockSL2 (ZMod 2) (n + 2) 0 ρ = blockSL2 (ZMod 2) (n + 2) 0 ρ * g →
        ∃ a : ℕ, ∃ B : SL(n + 2 - 1, ZMod 2),
          g = blockSL2 (ZMod 2) (n + 2) 0 ρ ^ a *
            blockSL (ZMod 2) (n + 2 + 1) (n + 2 - 1) 2 (by omega) B) :
    Subgroup.centralizer ({b} : Set G) ⊓ (⨆ i : Fin (n + 2), K (i : ℕ)) =
      Subgroup.zpowers b ⊔ L := by
  obtain ⟨ψ, hinj, hrange, hblk⟩ := hF.exists_marking_join hn h1n
  have hbK : b ∈ K 0 := by
    rw [hF.K0]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  rw [← hblk ⟨0, by omega⟩] at hbK
  have hb' := eq_or_eq_inv_of_mem_map_blockSL2 hinj hρ ⟨0, by omega⟩ hb hbK
  rw [show (⟨0, by omega⟩ : Fin (n + 2)) = 0 from Fin.ext (by simp)] at hb'
  set t₁ : SL(n + 2 + 1, ZMod 2) := blockSL2 (ZMod 2) (n + 2) 0 ρ with ht₁
  have hCb : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({ψ t₁} : Set G) := by
    rcases hb' with h | h
    · rw [h]
    · ext g
      rw [h, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      exact Commute.inv_right_iff
  have hZb : Subgroup.zpowers b = Subgroup.zpowers (ψ t₁) := by
    rcases hb' with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]
  have hJ : ∀ B : SL(n + 1, ZMod 2),
      blockSL (ZMod 2) (n + 2 + 1) (n + 1) 2 (by omega) B * t₁ =
        t₁ * blockSL (ZMod 2) (n + 2 + 1) (n + 1) 2 (by omega) B := fun B =>
    blockSL_comm _ _ (Or.inr (by simp)) B ρ
  have hCt : Subgroup.centralizer ({t₁} : Set SL(n + 2 + 1, ZMod 2)) =
      Subgroup.zpowers t₁ ⊔ (blockSL (ZMod 2) (n + 2 + 1) (n + 1) 2 (by omega)).range := by
    refine le_antisymm (fun g hg => ?_) (sup_le ?_ ?_)
    · obtain ⟨a, B, rfl⟩ := hmat g (Subgroup.mem_centralizer_singleton_iff.mp hg)
      exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers t₁) a) ⟨B, rfl⟩
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    · rintro _ ⟨B, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hJ B)
  have hJL : (blockSL (ZMod 2) (n + 2 + 1) (n + 1) 2 (by omega)).range.map ψ = L := by
    rw [range_blockSL_two_eq_iSup, Subgroup.map_iSup, ← hF.sysL.2.1]
    exact iSup_congr fun j => hblk ⟨(j : ℕ) + 2, by omega⟩
  rw [hCb, hZb, ← hrange, centralizer_inf_range_eq_map hinj, hCt, Subgroup.map_sup,
    MonoidHom.map_zpowers, hJL]

end CFSG.StandardType.FF81
