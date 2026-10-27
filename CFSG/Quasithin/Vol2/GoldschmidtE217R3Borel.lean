module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Defs
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3TwoC
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Rigid
public import CFSG.Quasithin.EmptyFaithful.S146yBorel
public import CFSG.Quasithin.Vol2.Ch3E213MOL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M E2P
open scoped commutatorElement

namespace E217R3

@[expose] def R3Pkg2bOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting2 H T M V K →
    (T ⊓ Subgroup.centralizer (V : Set G)).relIndex T < 8 → Case2 H T M K →
    (IsPSL 3 2 1 ↥(E2.star M H K) ∨ IsAlt 6 ↥(E2.star M H K)) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → False

theorem isSimpleGroup_of_isBenderOf {n : ℕ} {Y : Type} [Group Y] [Finite Y]
    (h : E2.IsBenderOf n Y) : IsSimpleGroup Y := by
  obtain ⟨hn, h | h | h⟩ := h
  · exact RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (A5.C25.fusionIsBenderGroup_of_isPSL h)
  · exact RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (A5.C25.fusionIsBenderGroup_of_isSz h)
  · exact RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (K1.fusionIsBenderGroup_of_stated_psu_three hn h)

section Single

variable {X : Type} [Group X] [Finite X]

theorem false_of_borelRigid_asHyp {K T M B : Subgroup X} (hX : E2P.ASHyp K T M)
    (hrig : BorelRigid ↥K) (hB : E2.IsBorelIn K B) (hBM : B ≤ M) {v : X} (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hvM : ∀ m ∈ M, m * v = v * m) : False := by
  obtain ⟨S, hS, rfl⟩ := hB
  have hvL : v ∈ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hX.normal]
    exact Subgroup.mem_top v
  have hcen := centralizes_of_borelRigid hrig hS hv2 hvL
    (fun b hb => (hvM b (hBM hb)).symm)
  have hvC : v ∈ Subgroup.centralizer (K : Set X) :=
    Subgroup.mem_centralizer_iff.2 fun k hk => (hcen k hk).symm
  rw [hX.cent, Subgroup.mem_bot] at hvC
  exact hv1 hvC

end Single

variable {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}

omit [Finite G] in
theorem nonab_star' (hKc : K ∈ cComp H) [Nontrivial ↥(E2.star M H K)] :
    ∃ a b : ↥(E2.star M H K), a * b ≠ b * a := by
  by_contra hcon
  have hc : ∀ a b : ↥(E2.star M H K), a * b = b * a :=
    fun a b => not_not.mp fun h => hcon ⟨a, b, h⟩
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hperf : ⁅K, K⁆ = K := hKc.2.1
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


theorem false_of_single_borel (hS : Setting2 H T M V K) (hC2 : Case2 H T M K)
    (hsimp : IsSimpleGroup ↥(E2.star M H K)) (hrig : BorelRigid ↥(E2.star M H K))
    (hB : E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))) : False := by
  have hmp := hS.toHyp2.hyp.minParabolic
  have hnab := nonab_star' (M := M) hS.mem_cComp
  have hX := asHyp_star' hmp hS.mem_cComp hS.eq_sup hC2 hsimp
    (OL.center_eq_bot_of_simple hnab) hnab
  obtain ⟨v, hv2, hv1, -, hvM, -⟩ := exists_vbar hS.toHyp2
  have hBM : E2.star M H (M ⊓ K) ≤ E2.star M H M :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left)
  exact false_of_borelRigid_asHyp hX hrig hB hBM hv2 hv1 hvM

theorem r3Pkg2a : R3Pkg2a := by
  intro G _ _ H T M V K hS hlt hC2 n hBend hB
  exact false_of_single_borel hS hC2 (isSimpleGroup_of_isBenderOf hBend)
    (borelRigid_of_family (Or.inl hBend)) hB

theorem r3Pkg2b_of_one (p1 : R3Pkg2bOne) : R3Pkg2b := by
  intro G _ _ H T M V K hS hlt hC2 n hn hK hD hB
  by_cases hn1 : n = 1
  · subst hn1
    refine p1 G H T M V K hS hlt hC2 ?_ hD hB
    rcases hK with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [E2.IsSp4Prime] using h)
  · have hn2 : 2 ≤ n := by omega
    rcases hK with h | h
    · exact false_of_single_borel hS hC2 (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n h).2
        (borelRigid_of_family (Or.inr ⟨hn2, Or.inl h⟩)) hB
    · have h' : IsPSp4 2 n ↥(E2.star M H K) := by simpa [E2.IsSp4Prime, hn1] using h
      exact false_of_single_borel hS hC2
        (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n h')
        (borelRigid_of_family (Or.inr ⟨hn2, Or.inr h⟩)) hB

end E217R3

end CFSG.Quasithin
