module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67TI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667

variable {M V W₁ W₂ : Subgroup G} {g : G}

theorem le_centralizer_of_eq_zpowers (h : Cfg1667 M V W₁ W₂) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    V ⊔ conjSubgroup V g ≤ centralizer ({z} : Set G) := by
  have hzmem : z ∈ V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) := by
    rw [hz]
    exact Subgroup.mem_zpowers z
  have hzV : z ∈ V := hzmem.1.1
  have hzVg : z ∈ conjSubgroup V g := hzmem.2.1
  refine sup_le ?_ ?_
  · intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp ((h.elemAbelian.1).is_comm.comm ⟨v, hv⟩ ⟨z, hzV⟩)
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp
      (((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1).is_comm.comm ⟨x, hx⟩ ⟨z, hzVg⟩)

theorem not_centralizer_le (h : Cfg1667 M V W₁ W₂) (hg : InCalO 1 M ⊥ V g) {z : G}
    (hz : V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) :
    ¬ centralizer ({z} : Set G) ≤ M := by
  intro hle
  have hle' : conjSubgroup V g ≤ centralizer ({z} : Set G) :=
    le_sup_right.trans (h.le_centralizer_of_eq_zpowers hz)
  exact hg.1.1 (hle'.trans hle)

end Cfg1667

private theorem normalizer_conjSubgroup_le_of_le {W T : Subgroup G} {m : G}
    (h : Subgroup.normalizer (W : Set G) ≤ T) (hm : m ∈ T) :
    Subgroup.normalizer (conjSubgroup W m : Set G) ≤ T := by
  intro n hn
  have hnm : m * n * m⁻¹ ∈ Subgroup.normalizer (W : Set G) := by
    have h1 : conjSubgroup W (m * n) = conjSubgroup W m := by
      rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hn]
    have hconj : conjSubgroup W (m * n * m⁻¹) = W := by
      calc conjSubgroup W (m * n * m⁻¹)
          = conjSubgroup (conjSubgroup W (m * n)) m⁻¹ :=
            (conjSubgroup_conjSubgroup W (m * n) m⁻¹).symm
        _ = conjSubgroup (conjSubgroup W m) m⁻¹ := by rw [h1]
        _ = conjSubgroup W (m * m⁻¹) := conjSubgroup_conjSubgroup W m m⁻¹
        _ = conjSubgroup W 1 := by rw [mul_inv_cancel]
        _ = W := conjSubgroup_one W
    exact conjSubgroup_eq_iff_mem_normalizer.mp hconj
  have hn_eq : n = m⁻¹ * (m * n * m⁻¹) * m := by group
  rw [hn_eq]
  exact T.mul_mem (T.mul_mem (T.inv_mem hm) (h hnm)) hm

theorem s1667_exists_sylow (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h129 : R129_1 D) (h159 : R15_9Small D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) {z : G} (hzV : z ∈ V) :
    ∃ S : Subgroup G, V ≤ S ∧ S ≤ D.M ∧
      CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : V ≤ centralizer ({z} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext_iff.mp ((hV.1).is_comm.comm ⟨v, hv⟩ ⟨z, hzV⟩)
  obtain ⟨P, hP⟩ :=
    CFSG.ABGLocalTools.exists_isSylowOf 2 (D.M ⊓ centralizer ({z} : Set G))
  have hPle : P ≤ D.M ⊓ centralizer ({z} : Set G) := hP.le
  have hPM : P ≤ D.M := hPle.trans inf_le_left
  have hPC : P ≤ centralizer ({z} : Set G) := hPle.trans inf_le_right
  have hPpg : IsPGroup 2 P := hP.isPGroup
  have hT : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  obtain ⟨m, hmM, hPm⟩ := E3.exists_le_conj_of_isSylowIn hT hPM hPpg
  let T' : Subgroup G := conjSubgroup D.T m
  have hT' : IsSylowIn 2 T' D.M := by
    have hnorm : m⁻¹ ∈ Subgroup.normalizer (D.M : Set G) :=
      Subgroup.le_normalizer (D.M.inv_mem hmM)
    have h := Ch1Sec3.isSylowIn_map_conj (p := 2) hT (g := m⁻¹) hnorm
    simpa only [T', conjSubgroup] using h
  have hT'M : T' ≤ D.M := hT'.le
  have hVT : V ≤ D.T := s15_13A_le_T hS.setting.hyp16.hyp125
  have hVVT' : V ≤ T' := by
    have hconjV : conjSubgroup V m = V :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (by
        rw [Hyp125.normalizer_eq hS.setting.hyp16.hyp125]; exact hmM)
    calc V = conjSubgroup V m := hconjV.symm
      _ ≤ conjSubgroup D.T m := E3.conjSubgroup_mono_left m hVT
      _ = T' := rfl
  have hWT' : E3.wClos V 0 T' ≤ T' := E3.wClos_le 0 T'
  have hWC : E3.wClos V 0 T' ≤ centralizer ({z} : Set G) :=
    (E3.wClos_mono hT'M).trans
      ((h159 V₀ V L hs.2 hS.setting.hyp16.small hS.ne_bot).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV)))
  let Q : Subgroup G := T' ⊓ centralizer ({z} : Set G)
  have hQpg : IsPGroup 2 Q := hT'.isPGroup.to_inf_left
  have hPQ : P ≤ Q := le_inf hPm hPC
  have hQK : Q ≤ D.M ⊓ centralizer ({z} : Set G) :=
    le_inf (inf_le_left.trans hT'M) inf_le_right
  have hQeq : Q = P := hP.eq_of_le hPQ hQK hQpg
  have hVP : V ≤ P := by
    rw [← hQeq]
    exact le_inf hVVT' hC
  have hWP : E3.wClos V 0 T' ≤ P := by
    rw [← hQeq]
    exact le_inf hWT' hWC
  have hnorm : Subgroup.normalizer (P : Set G) ≤ D.M := by
    refine (E3.e3_15_normalizer (i := 0) hT' hPM hPpg hWP).trans ?_
    have hwconj : E3.wClos V 0 T' = conjSubgroup (E3.wClos V 0 D.T) m :=
      E3.wClos_conj D.T m
    rw [hwconj]
    exact normalizer_conjSubgroup_le_of_le
      (sixteen_sixtyThree D hSg h129 h61 h159 V₀ V L hV hS ⟨Or.inr hs.1, hs.2⟩).2 hmM
  have hN : Subgroup.normalizer (P : Set G) ⊓ centralizer ({z} : Set G) ≤ D.M :=
    fun _ hx => hnorm hx.1
  exact ⟨P, hVP, hPM,
    CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hP hN⟩

theorem s1667_pRank_centralizer (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {z : G} (hzV : z ∈ V)
    (hz : orderOf z = 2) (hnot : ¬ centralizer ({z} : Set G) ≤ D.M) :
    CFSG.Open.pRank 3 (centralizer ({z} : Set G)) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    sixteen_sixtyEight_k D hSg h1219 V₀ V L hV hS hs
  have h3sig : 3 ∈ D.sig := by
    rw [hs.1.2.2.2]
    exact Set.mem_singleton 3
  obtain ⟨c, hcM, hcV, hcord⟩ := s1667_exists_orderOf_three D hSg h1217 hS hs h0
  have hcC : c ∈ centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV) hcV
  have hle : Subgroup.zpowers c ≤ D.M ⊓ centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hcM, hcC⟩
  have hEea : IsElemAbelian 3 (Subgroup.zpowers c) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    have hxord : orderOf x ∣ orderOf c := orderOf_dvd_of_mem_zpowers hx
    rw [hcord] at hxord
    exact orderOf_dvd_iff_pow_eq_one.mp hxord
  have hcard : Nat.card (Subgroup.zpowers c) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hcord, pow_one]
  have h3 : 1 ≤ CFSG.Open.pRank 3 (D.M ⊓ centralizer ({z} : Set G)) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hle hEea hcard
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hz2 : ∃ n : ℕ, z ^ (2 ^ n) = 1 := by
    refine ⟨1, ?_⟩
    rw [pow_one, ← hz]
    exact pow_orderOf_eq_one z
  exact pRank_three_centralizer D h61 h3sig hse hz1 hz2 hnot h3

theorem s1667_isStronglyPEmbedded (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {z : G} (hzV : z ∈ V)
    (hnot : ¬ centralizer ({z} : Set G) ≤ D.M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3
      ((centralizer ({z} : Set G) ⊓ D.M).subgroupOf (centralizer ({z} : Set G))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hse : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    sixteen_sixtyEight_k D hSg h1219 V₀ V L hV hS hs
  obtain ⟨c, hcM, hcV, hcord⟩ := s1667_exists_orderOf_three D hSg h1217 hS hs h0
  have hcC : c ∈ centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzV) hcV
  have hle : Subgroup.zpowers c ≤ centralizer ({z} : Set G) ⊓ D.M :=
    Subgroup.zpowers_le.mpr ⟨hcC, hcM⟩
  have hdvd : 3 ∣ Nat.card (centralizer ({z} : Set G) ⊓ D.M : Subgroup G) := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hcord] at h
  exact hse.subgroupOf hnot hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
