module

public import CFSG.RankThree.PartOne.K159.InnLayerData
public import CFSG.RankThree.PartOne.S12.Sec1511Tools
public import CFSG.RankThree.PartOne.S12.Sec1514Simple

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K

section Center

variable {G : Type} [Group G]

theorem not_dvd_card_inf_centralizer_of_simple [Finite G] {p : ℕ} (hp3 : 3 < p) {I : Subgroup G}
    [IsSimpleGroup ↥I] (heven : Even (Nat.card ↥I)) :
    ¬ p ∣ Nat.card ↥(I ⊓ Subgroup.centralizer (I : Set G)) := by
  classical
  by_cases hcomm : ∀ x ∈ I, ∀ y ∈ I, x * y = y * x
  · have : IsMulCommutative ↥I := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    have hprime : (Nat.card ↥I).Prime := (Group.is_simple_iff_prime_card.1 inferInstance)
    have h2 : Nat.card ↥I = 2 := (Nat.Prime.even_iff hprime).1 heven
    intro hdvd
    have h1 : Nat.card ↥(I ⊓ Subgroup.centralizer (I : Set G)) ∣ Nat.card ↥I :=
      Subgroup.card_dvd_of_le inf_le_left
    have h3 := hdvd.trans h1
    rw [h2] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · push Not at hcomm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcomm
    set Z : Subgroup G := I ⊓ Subgroup.centralizer (I : Set G) with hZ
    have hnorm : (Z.subgroupOf I).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hn' : (n : G) ∈ Subgroup.centralizer (I : Set G) := (Subgroup.mem_subgroupOf.1 hn).2
      have h1 : (g : G) * (n : G) = (n : G) * (g : G) := Subgroup.mem_centralizer_iff.1 hn' g g.2
      have h2 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by rw [h1]; group
      refine Subgroup.mem_subgroupOf.2 ?_
      show (g * n * g⁻¹ : I).1 ∈ Z
      have : (g * n * g⁻¹ : I).1 = (n : G) := by simpa using h2
      rw [this]
      exact Subgroup.mem_subgroupOf.1 hn
    have hbot : Z = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Z.subgroupOf I) with h | h
      · rw [Subgroup.eq_bot_iff_forall]
        intro z hz
        have hzI : z ∈ I := hz.1
        have : (⟨z, hzI⟩ : ↥I) ∈ Z.subgroupOf I := Subgroup.mem_subgroupOf.2 hz
        rw [h] at this
        exact congrArg Subtype.val (Subgroup.mem_bot.1 this)
      · exfalso
        have hall : ∀ a ∈ I, a ∈ Subgroup.centralizer (I : Set G) := by
          intro a ha
          have : (⟨a, ha⟩ : ↥I) ∈ Z.subgroupOf I := by rw [h]; trivial
          exact (Subgroup.mem_subgroupOf.1 this).2
        exact hxy (Subgroup.mem_centralizer_iff.1 (hall y hy) x hx)
    rw [hbot, Subgroup.card_bot]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

end Center

section Rows

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_center_lieGenerated {p : ℕ} {A E : Subgroup G} (hp3 : 3 < p)
    (hout : Outcome152 p E A (lieGenerated p E)) (hEA : E = A) :
    ¬ p ∣ Nat.card ↥(lieGenerated p E ⊓ Subgroup.centralizer (lieGenerated p E : Set G)) := by
  obtain ⟨r, hr1, hr4, hrow⟩ := lieRow_of_outcome hout hEA
  have : IsSimpleGroup ↥(lieGenerated p E) := isSimpleGroup_of_lieRow hr1 hr4 hrow
  have heven : Even (Nat.card ↥(lieGenerated p E)) := by
    rcases hout with h | h | h | h | h
    · obtain ⟨-, -, -, -, -, -, he⟩ := h
      exact he
    · obtain ⟨-, -, -, -, -, -, he⟩ := h
      exact he
    · obtain ⟨-, -, -, -, -, -, he⟩ := h
      exact he
    · obtain ⟨-, -, -, -, -, -, he⟩ := h
      exact he
    · obtain ⟨-, -, -, -, -, -, hne, -⟩ := h
      exact absurd hEA hne
  exact not_dvd_card_inf_centralizer_of_simple hp3 heven

@[expose] def KFPerfNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) → E = A →
    ∀ Z : Subgroup G, Group.IsPerfect ↥Z → Z ≤ lieNormalizer p E →
      Z ≤ lieGenerated p E ⊔ Subgroup.centralizer (lieGenerated p E : Set G)

@[expose] def KFCompLayer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) → E = A →
    ∀ e ∈ E, e ≠ 1 → ∀ Q : Subgroup G,
      Q ≤ lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G) →
      IsComponent (Q.subgroupOf (lieGenerated p E ⊓ Subgroup.centralizer ({e} : Set G))) →
      Q ≤ thetaLayer p e

theorem kfInnLayerData_of_facts (hS13 : Sec13Avail) (h1 : LayerRowOne) (h2 : LayerRowTwo)
    (h3 : LayerRowThree) (h4 : LayerRowFour) (_h5 : LayerRowFive) (hEI : Sec1511.KFEI)
    (hPerf : KFPerfNormalizer) (hComp : KFCompLayer) : KFInnLayerData := by
  intro G _ _ p A c L E h15 hF hout hEA
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    subst hEA
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne rfl
  exact ⟨layerData_of_rows hS13 h1 h2 h3 h4 G p A c L E h15 hF hout hEA,
    hEI G p A c L E h15 hF hout hnot5, not_dvd_center_lieGenerated h15.h12.three_lt hout hEA,
    hPerf G p A c L E h15 hF hout hEA, hComp G p A c L E h15 hF hout hEA⟩

theorem kfInnLayer_of_rows (hS13 : Sec13Avail) (h1 : LayerRowOne) (h2 : LayerRowTwo)
    (h3 : LayerRowThree) (h4 : LayerRowFour) (h5 : LayerRowFive) (hEI : Sec1511.KFEI)
    (hPerf : KFPerfNormalizer) (hComp : KFCompLayer) : KFInnLayer :=
  kfInnLayer_of_data (kfInnLayerData_of_facts hS13 h1 h2 h3 h4 h5 hEI hPerf hComp)

end Rows

end CFSG.RankThree.PartOne.K159
