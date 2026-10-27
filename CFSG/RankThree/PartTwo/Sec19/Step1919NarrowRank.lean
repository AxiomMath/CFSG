module

import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Step1919NarrowRank

variable {X : Type} [Group X]

theorem card_sup_zpowers_of_orderOf [Finite X] (Y : Subgroup X) {y : X} (hy : orderOf y = 3)
    (hyY : y ∉ Y) (hcomm : ∀ z ∈ Y, z * y = y * z) :
    Nat.card (Y ⊔ Subgroup.zpowers y : Subgroup X) = Nat.card Y * 3 := by
  have hYN : Y ≤ Subgroup.normalizer (Subgroup.zpowers y : Set X) := fun z hz =>
    Sec12.mem_normalizer_zpowers_of_commute (hcomm z hz)
  have h1 := Sec6.card_sup_mul_card_inf hYN
  have hinf : Y ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card (Y ⊓ Subgroup.zpowers y : Subgroup X) ∣ 3 := by
      rw [← hy, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      have heq : Y ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, Nat.card_zpowers, hy])
      have hy' : y ∈ Y ⊓ Subgroup.zpowers y := by
        rw [heq]
        exact Subgroup.mem_zpowers y
      exact hyY hy'.1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hy] at h1
  exact h1

theorem orderOf_eq_three {y : X} {Y : Subgroup X} (hy3 : y ^ 3 = 1) (hyY : y ∉ Y) :
    orderOf y = 3 :=
  orderOf_eq_prime hy3 fun h => hyY (h ▸ Y.one_mem)

variable {G : Type} [Group G] [Finite G]

theorem four_le_localRank_of_chain {M : Subgroup G} (hQ : CFSG.Open.pCoreOf 2 M ≠ ⊥)
    {v₁ v₂ v₃ v₄ : M ⧸ CFSG.pCore 2 M}
    (hc12 : v₁ * v₂ = v₂ * v₁) (hc13 : v₁ * v₃ = v₃ * v₁) (hc14 : v₁ * v₄ = v₄ * v₁)
    (hc23 : v₂ * v₃ = v₃ * v₂) (hc24 : v₂ * v₄ = v₄ * v₂) (hc34 : v₃ * v₄ = v₄ * v₃)
    (h₁ : v₁ ^ 3 = 1) (h₂ : v₂ ^ 3 = 1) (h₃ : v₃ ^ 3 = 1) (h₄ : v₄ ^ 3 = 1)
    (hn₁ : v₁ ≠ 1) (hn₂ : v₂ ∉ Subgroup.zpowers v₁)
    (hn₃ : v₃ ∉ Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂)
    (hn₄ : v₄ ∉ Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ ⊔ Subgroup.zpowers v₃) :
    4 ≤ CFSG.Assembly.RankThreeEven.localRank 3 G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 M) with hπ
  have hN2 : IsPGroup 2 (CFSG.pCore 2 M) := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pCore 2 M) := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  set V₁ := Subgroup.zpowers v₁ with hV₁
  set V₂ := V₁ ⊔ Subgroup.zpowers v₂ with hV₂
  set V₃ := V₂ ⊔ Subgroup.zpowers v₃ with hV₃
  set V := V₃ ⊔ Subgroup.zpowers v₄ with hV
  have hV₁c : Nat.card V₁ = 3 := by
    rw [hV₁, Nat.card_zpowers]
    exact orderOf_eq_prime h₁ hn₁
  have hcen : ∀ {Y : Subgroup (M ⧸ CFSG.pCore 2 M)} {b : M ⧸ CFSG.pCore 2 M},
      Y ≤ Subgroup.centralizer {b} → ∀ z ∈ Y, z * b = b * z := by
    intro Y b hY z hzY
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hY hzY))
  have hV₁v₂ : V₁ ≤ Subgroup.centralizer {v₂} :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc12)
  have hV₂v₃ : V₂ ≤ Subgroup.centralizer {v₃} :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc13))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc23))
  have hV₃v₄ : V₃ ≤ Subgroup.centralizer {v₄} :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      hc14)) (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
        hc24))) (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          hc34))
  have hV₂c : Nat.card V₂ = 9 := by
    rw [hV₂, card_sup_zpowers_of_orderOf V₁ (orderOf_eq_three h₂ hn₂) hn₂ (hcen hV₁v₂), hV₁c]
  have hV₃c : Nat.card V₃ = 27 := by
    rw [hV₃, card_sup_zpowers_of_orderOf V₂ (orderOf_eq_three h₃ hn₃) hn₃ (hcen hV₂v₃), hV₂c]
  have hVc : Nat.card V = 81 := by
    rw [hV, card_sup_zpowers_of_orderOf V₃ (orderOf_eq_three h₄ hn₄) hn₄ (hcen hV₃v₄), hV₃c]
  set S : Set (M ⧸ CFSG.pCore 2 M) := {v₁, v₂, v₃, v₄} with hS
  have hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first | rfl | assumption | exact Eq.symm (by assumption)
  have hVS : V ≤ Subgroup.centralizer S := by
    have hmem : ∀ a ∈ S, a ∈ Subgroup.centralizer S := fun a ha =>
      Subgroup.mem_centralizer_iff.mpr fun b hb => hSc b hb a ha
    have h1 : v₁ ∈ S := by simp [hS]
    have h2 : v₂ ∈ S := by simp [hS]
    have h3 : v₃ ∈ S := by simp [hS]
    have h4 : v₄ ∈ S := by simp [hS]
    exact sup_le (sup_le (sup_le (Subgroup.zpowers_le.mpr (hmem _ h1))
      (Subgroup.zpowers_le.mpr (hmem _ h2))) (Subgroup.zpowers_le.mpr (hmem _ h3)))
      (Subgroup.zpowers_le.mpr (hmem _ h4))
  have hVsub : (V : Set (M ⧸ CFSG.pCore 2 M)) ⊆ Subgroup.closure S := by
    have h1 : v₁ ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
    have h2 : v₂ ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
    have h3 : v₃ ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
    have h4 : v₄ ∈ Subgroup.closure S := Subgroup.subset_closure (by simp [hS])
    exact sup_le (sup_le (sup_le (Subgroup.zpowers_le.mpr h1) (Subgroup.zpowers_le.mpr h2))
      (Subgroup.zpowers_le.mpr h3)) (Subgroup.zpowers_le.mpr h4)
  have hclV : Subgroup.closure S ≤ V := by
    rw [Subgroup.closure_le]
    intro a ha
    simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers _)))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers _)))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have hSa : S ⊆ Subgroup.centralizer {a} := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hVS ha) s hs)
    have hVa : V ≤ Subgroup.centralizer {a} :=
      (le_of_le_of_eq (Subgroup.closure_le _ |>.mpr hSa) rfl).trans' (fun x hx => hVsub hx)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hVa hb)).symm
  have hVe : ∀ v ∈ V, v ^ 3 = 1 := by
    intro v hv
    have hv' : v ∈ Subgroup.closure S := hVsub hv
    induction hv' using Subgroup.closure_induction with
    | mem a ha =>
      simp only [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      rw [Commute.mul_pow (hVcomm a (hclV ha) b (hclV hb)) 3, iha (hclV ha), ihb (hclV hb),
        one_mul]
    | inv a ha iha => rw [inv_pow, iha (hclV ha), inv_one]
  have hV3 : IsPGroup 3 V := fun v => ⟨1, Subtype.ext (by simpa using hVe v v.2)⟩
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
  obtain ⟨R, hR3, ⟨eR⟩⟩ := RankThreeCoreUniqueness.Helpers.coprime_kernel_lifts_pSubgroup 3
    Nat.prime_three π (QuotientGroup.mk'_surjective (CFSG.pCore 2 M)) hker V hV3
  have hRcomm : ∀ a b : R, a * b = b * a := fun a b => eR.injective (by
    rw [map_mul, map_mul]
    exact Subtype.ext (hVcomm _ (eR a).2 _ (eR b).2))
  have hRe : ∀ a : R, a ^ 3 = 1 := fun a => eR.injective (by
    rw [map_pow, map_one]
    exact Subtype.ext (hVe _ (eR a).2))
  set X₄ := R.map M.subtype with hX₄
  have hX₄card : Nat.card X₄ = 3 ^ 4 := by
    rw [hX₄, Subgroup.card_map_of_injective M.subtype_injective, Nat.card_congr eR.toEquiv, hVc]
    norm_num
  have hX₄mem : ∀ a ∈ X₄, ∃ a' : R, ((a' : M) : G) = a := by
    rintro _ ⟨a', ha', rfl⟩
    exact ⟨⟨a', ha'⟩, rfl⟩
  have hX₄c : IsMulCommutative X₄ := ⟨⟨fun a b => Subtype.ext (by
    obtain ⟨a', ha'⟩ := hX₄mem a a.2
    obtain ⟨b', hb'⟩ := hX₄mem b b.2
    change (a : G) * b = b * a
    rw [← ha', ← hb']
    exact congrArg (fun z : R => ((z : M) : G)) (hRcomm a' b'))⟩⟩
  have hX₄e : ∀ a ∈ X₄, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨a', ha'⟩ := hX₄mem a ha
    rw [← ha']
    exact congrArg (fun z : R => ((z : M) : G)) (hRe a')
  have hX₄N : X₄ ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.map_subtype_le _).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  exact Theta.le_localRank_of_le_normalizer (by norm_num) hQ
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hX₄c hX₄e hX₄card hX₄N

end Step1919NarrowRank

end CFSG.RankThree.PartTwo.Sec19
