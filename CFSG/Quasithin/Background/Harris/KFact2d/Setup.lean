module

public import CFSG.Quasithin.Background.Harris.KFact2d.Defs
public import CFSG.Quasithin.Vol2.Ch3E213MOL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRes2L3Cases
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3TwoC

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin E2P
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nonab_star_of_perfect {M H K : Subgroup G} (hKH : K ≤ H) (hperf : ⁅K, K⁆ = K)
    [Nontrivial ↥(E2.star M H K)] : ∃ a b : ↥(E2.star M H K), a * b ≠ b * a := by
  by_contra hcon
  have hc : ∀ a b : ↥(E2.star M H K), a * b = b * a :=
    fun a b => not_not.mp fun h => hcon ⟨a, b, h⟩
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

theorem exists_case2dStar {T N K K0 : Subgroup G} (hmp : MinParabolic K T N) (hK0 : K0 ∈ cComp K)
    (hKK0 : K = K0 ⊔ T) (hc : CFSG.Quasithin.Gap6R2.E22Case2d K T N K0) :
    ∃ p : ℕ, Case2dStar (E2.star N K K0) (E2.star N K T) (E2.star N K N) p := by
  have hc' := hc
  unfold CFSG.Quasithin.Gap6R2.E22Case2d at hc'
  dsimp only at hc'
  obtain ⟨hTn, hker, p, hp, hp2, hcases, hMK⟩ := hc'
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hsimp : IsSimpleGroup ↥(E2.star N K K0) := by
    refine CFSG.Quasithin.Ch3E213M.OL.isSimpleGroup_of_L3U3 hp hp3 ?_
    rcases hcases with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hKH : K0 ≤ K := le_of_mem_cComp hK0
  haveI : Nontrivial ↥(E2.star N K K0) := hsimp.toNontrivial
  have hnab := nonab_star_of_perfect (M := N) hKH hK0.2.1
  have hZ : Subgroup.center ↥(E2.star N K K0) = ⊥ :=
    CFSG.Quasithin.Ch3E213M.OL.center_eq_bot_of_simple hnab
  have hC2 : Ch3E213M.Case2 K T N K0 := ⟨hTn, hker⟩
  have hX := E217R3.asHyp_star' hmp hK0 hKK0 hC2 hsimp hZ hnab
  have hTK : E2.star N K (T ⊓ K0) = E2.star N K T ⊓ E2.star N K K0 :=
    star_inf_T hmp.isSylow hK0.2.2.1 hKH
  have hMK' : E2.star N K N ⊓ E2.star N K K0 = E2.star N K K0 ⊓
      Subgroup.centralizer (zOf (E2.star N K T ⊓ E2.star N K K0) : Set (E2.StarQuot N K)) := by
    rw [← star_inf_M, hMK, ← hTK]
    rfl
  exact ⟨p, hX, hp, hp2, hcases, hMK'⟩

end CFSG.Quasithin.Background.Harris.KFact2d
