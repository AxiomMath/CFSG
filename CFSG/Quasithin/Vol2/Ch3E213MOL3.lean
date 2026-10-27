module

public import CFSG.Quasithin.Vol2.Ch3E213MOL2
public import CFSG.Quasithin.Vol2.Ch3E213MOS12

public section

namespace CFSG.Quasithin.Ch3E213M.OL

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.GLS.IVK CFSG.GH74.GLS B6 E2P
open scoped commutatorElement

theorem isSimpleGroup_of_L3U3 {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (h : IsPSU 3 p 1 Y ∨ IsPSL 3 p 1 Y) : IsSimpleGroup Y := by
  have : Fact p.Prime := ⟨hp⟩
  rcases h with h | h
  · obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := h
    have h1 := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p 1 hcard 3 le_rfl
      (by intro h; simp at h; omega)
    exact e.isSimpleGroup
  · obtain ⟨-, F, _, _, -, ⟨e⟩⟩ := h
    obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3)
      (by norm_num) (Or.inl le_rfl)
    have h1 :=
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.isSimpleGroup
    exact e.isSimpleGroup

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

theorem nonab_star (hS : Setting H T M V K) [Nontrivial ↥(E2.star M H K)] :
    ∃ a b : ↥(E2.star M H K), a * b ≠ b * a := by
  by_contra hcon
  have hc : ∀ a b : ↥(E2.star M H K), a * b = b * a :=
    fun a b => not_not.mp fun h => hcon ⟨a, b, h⟩
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hperf : ⁅K, K⁆ = K := hS.mem_cComp.2.1
  have hKJ : K ≤ kerIn M H := by
    rw [← hperf, Subgroup.commutator_le]
    intro a ha b hb
    have hsa : starMap M H ⟨a, hKH ha⟩ ∈ E2.star M H K := ⟨⟨a, hKH ha⟩, ha, rfl⟩
    have hsb : starMap M H ⟨b, hKH hb⟩ ∈ E2.star M H K := ⟨⟨b, hKH hb⟩, hb, rfl⟩
    have h1 : starMap M H ⟨a, hKH ha⟩ * starMap M H ⟨b, hKH hb⟩ =
        starMap M H ⟨b, hKH hb⟩ * starMap M H ⟨a, hKH ha⟩ :=
      congrArg Subtype.val (hc ⟨_, hsa⟩ ⟨_, hsb⟩)
    have h2 : starMap M H ⁅(⟨a, hKH ha⟩ : ↥H), ⟨b, hKH hb⟩⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have h3 : ⁅(⟨a, hKH ha⟩ : ↥H), ⟨b, hKH hb⟩⁆ ∈ (kerIn M H).subgroupOf H := by
      rw [← ker_starMap]
      exact h2
    exact Subgroup.mem_subgroupOf.mp h3
  have hstar : E2.star M H K = ⊥ := by
    rw [star_def, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_starMap]
    exact Subgroup.mem_subgroupOf.mpr (hKJ (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥(E2.star M H K))
  apply ha
  have h1 : (a : E2.StarQuot M H) ∈ (⊥ : Subgroup (E2.StarQuot M H)) := hstar ▸ a.2
  exact Subtype.ext (Subgroup.mem_bot.mp h1)

theorem false_of_ge5 (hA : KFactL3U3OuterInv)
    (hS : Setting H T M V K) (hC2 : Case2 H T M K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : (p % 4 = 1 ∧ IsPSU 3 p 1 ↥(E2.star M H K)) ∨
      (p % 4 = 3 ∧ IsPSL 3 p 1 ↥(E2.star M H K)))
    (hMK : E2.star M H (M ⊓ K) =
      E2.star M H K ⊓ Subgroup.centralizer (zStar H T M K : Set (E2.StarQuot M H))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup ↥(E2.star M H K) := isSimpleGroup_of_L3U3 hp (by omega)
    (hK.imp (fun h => h.2) (fun h => h.2))
  have hnab := nonab_star hS
  have hX := OS.asHyp_star hS hC2 hsimp (center_eq_bot_of_simple hnab) hnab
  have hMH : M ≤ H := hS.hyp.minParabolic.maximal.1.le
  have hsq : ∀ x ∈ E2.star M H V, x * x = 1 :=
    OS.star_sq fun v hv => by rw [← pow_two]; exact hS.hyp.elem.2 v hv
  have hV4 : 4 ≤ Nat.card (E2.star M H V) := hS.four_le.trans (OS.relIndex_le_card_star hS.hyp)
  have hVM := OS.star_le_pCoreOf hMH hS.hyp.le_pCoreOf
  have hKH : K ≤ H := le_of_mem_cComp hS.mem_cComp
  have hTK : E2.star M H (T ⊓ K) = E2.star M H T ⊓ E2.star M H K :=
    star_inf_T hS.hyp.minParabolic.isSylow hS.mem_cComp.2.2.1 hKH
  have hMK' : E2.star M H M ⊓ E2.star M H K = E2.star M H K ⊓
      Subgroup.centralizer (zOf (E2.star M H T ⊓ E2.star M H K) : Set (E2.StarQuot M H)) := by
    rw [← star_inf_M, hMK, ← hTK]
    rfl
  exact false_of_asHyp hA hX hp hp5 hK hMK' hsq hV4 hVM

end CFSG.Quasithin.Ch3E213M.OL
