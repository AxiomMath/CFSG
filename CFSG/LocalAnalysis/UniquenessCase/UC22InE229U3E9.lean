module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Uni
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

theorem uc22ine229u3e9_two_le_pRank {W : Type} [Group W] [Finite W] {n : ℕ} (hW : IsU3 W n)
    (h3 : 3 ∣ 2 ^ n + 1) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup W) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hW
  obtain ⟨A, hA, hAc⟩ := CFSG.QuasithinUnique.Id2519.HasElemAb.of_mulEquiv e.symm
    (CFSG.Quasithin.SBd19F.hasElemAb_nine_psu_three (K := K) Nat.one_le_two_pow hK h3)
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hA (by rw [hAc]; norm_num)

theorem uc22ine229u3e9_exists_elemAbelian_sq {H W : Type} [Group H] [Finite H] [Group W] [Finite W]
    (f : H →* W) (hf : Function.Surjective f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup W)) :
    ∃ E : Subgroup H, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p H) := inferInstance
  have h1 := (CFSG.SectionRank.pRank_sylow (P.mapSurjective hf)).1
  have h2 : ((P.mapSurjective hf : Sylow p W) : Subgroup W) = (P : Subgroup H).map f := rfl
  have hnc : ¬ IsCyclic (P : Subgroup H) := fun hc => by
    have hc' : IsCyclic ((P : Subgroup H).map f) :=
      isCyclic_of_surjective (f.subgroupMap P) (f.subgroupMap_surjective P)
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hp hc'
    rw [h2] at h1
    omega
  obtain ⟨E, -, hE, hEc⟩ := uc22p22u_exists_elemAbelian_sq hp hp2 P.2 hnc
  exact ⟨E, hE, hEc⟩

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229u3e9_exists_E {Y : Subgroup G} {n : ℕ} (hX : IsSU3 (Bar2 Y) n)
    (h3 : 3 ∣ 2 ^ n + 1) (hZ : Nat.card (center (Bar2 Y)) ∣ 3) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = 3) :
    ∃ E X' : Subgroup G, X ≤ E ∧ E ≤ Y ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ X' ≤ E ∧
      Nat.card X' = 3 ∧
      ∀ x : ↥Y, (x : G) ∈ X' → (QuotientGroup.mk x : Bar2 Y) ∈ center (Bar2 Y) → x = 1 := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  let π : ↥Y →* Bar2 Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hXs : Nat.card (X.subgroupOf Y) = 3 := by
    rw [← hXc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv
  obtain ⟨E₀, hE₀, hE₀c⟩ := uc22ine229u3e9_exists_elemAbelian_sq
    ((QuotientGroup.mk' (center (Bar2 Y))).comp π)
    ((QuotientGroup.mk'_surjective _).comp hπs) hp3 (by norm_num)
    (uc22ine229u3e9_two_le_pRank hX.2 h3)
  have hY2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) :=
    CFSG.SectionRank.le_pRank hp3.one_lt le_top hE₀ hE₀c
  obtain ⟨B, hXB⟩ := (IsPGroup.of_card (n := 1) (by rw [pow_one, hXs]) :
    IsPGroup 3 (X.subgroupOf Y)).exists_le_sylow
  have hB2 : 2 ≤ CFSG.Open.pRank 3 (B : Subgroup ↥Y) := by
    rw [(CFSG.SectionRank.pRank_sylow B).1]
    exact hY2
  obtain ⟨E₁, hXE₁, -, hE₁, hE₁c⟩ :=
    CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime B.2 hB2 hXB hXs
  have hdisj : Disjoint E₁ π.ker := by
    rw [Subgroup.disjoint_def]
    intro x hx hxk
    exact UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup hp3 (by norm_num) hE₁.isPGroup hker
      hx hxk
  obtain ⟨x₀, hx₀, hx₀Z⟩ : ∃ x₀ ∈ E₁, π x₀ ∉ center (Bar2 Y) := by
    by_contra h
    push Not at h
    have hle : E₁.map π ≤ center (Bar2 Y) := by
      rintro _ ⟨x, hx, rfl⟩
      exact h x hx
    have h9 := (Subgroup.card_dvd_of_le hle).trans hZ
    rw [UC6S846.card_map_of_disjoint_ker π E₁ hdisj, hE₁c] at h9
    norm_num at h9
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀Z (by rw [h, map_one]; exact Subgroup.one_mem _)
  have hx₀3 : x₀ ^ 3 = 1 := hE₁.2 x₀ hx₀
  have hX'₁ : Nat.card (Subgroup.zpowers x₀) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx₀3 hx₀1]
  have hX'₁E : Subgroup.zpowers x₀ ≤ E₁ := Subgroup.zpowers_le.2 hx₀
  refine ⟨E₁.map Y.subtype, (Subgroup.zpowers x₀).map Y.subtype, ?_, Subgroup.map_subtype_le _,
    hE₁.map Y.subtype, ?_, Subgroup.map_mono hX'₁E, ?_, ?_⟩
  · have := Subgroup.map_mono (f := Y.subtype) hXE₁
    rwa [Subgroup.map_subgroupOf_eq_of_le hXY] at this
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hE₁c]
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hX'₁]
  · rintro x ⟨z, hz, hzx⟩ hxZ
    have hzx' : z = x := Subtype.ext hzx
    rw [← hzx'] at hxZ ⊢
    by_contra hz1
    have hz3 : z ^ 3 = 1 := hE₁.2 z (hX'₁E hz)
    have hzc : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    have heq : Subgroup.zpowers z = Subgroup.zpowers x₀ :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz) (hX'₁.trans hzc.symm).le
    have hx₀z : x₀ ∈ Subgroup.zpowers z := by
      rw [heq]
      exact Subgroup.mem_zpowers x₀
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx₀z
    apply hx₀Z
    rw [← hm, map_zpow]
    exact zpow_mem hxZ m

end CFSG.LocalAnalysis.UniquenessCase.UC22
