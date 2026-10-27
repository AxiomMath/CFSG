module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem exists_elemAbelian_central (h : Hyp141 D L₁ L₂ X) {P : Subgroup G} (hP : IsPGroup 3 P)
    (hXP : X ≤ P) (hP₁ : P ≤ normalizer (L₁ : Set G)) (hP₂ : P ≤ normalizer (L₂ : Set G))
    (hY : F08.CentOverO2 P (L₁ ⊔ L₂) ≠ ⊥) :
    ∃ E : Subgroup G, E ≤ P ⊓ centralizer (P : Set G) ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ e ∈ E, ∀ l ∈ L₂, e * l * e⁻¹ * l⁻¹ ∈ pCoreOf 2 L₂ := by
  let Y : Subgroup G := F08.CentOverO2 P (L₁ ⊔ L₂)
  let X₁ : Subgroup G := X ⊓ L₁
  haveI : IsMulCommutative X := (isElemAbelian_X h).1
  have hYP : Y ≤ P := fun y hy => (mem_centOverO2_iff.mp hy).1
  have hY3 : IsPGroup 3 Y := hP.to_le hYP
  have hYX : Y ≤ centralizer (X : Set G) := centOverO2_le_centralizer h hP hXP
  have hXY : Disjoint X Y := disjoint_centOverO2 h hP hXP
  have hXcent : X ≤ centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨x₀, hx₀, hy⟩ := exists_mul_mem_centOverO2 h hP hXP hP₁ hP₂ hp
    have hxx₀ : x * x₀ = x₀ * x := by
      simpa using congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : X) (⟨x₀, hx₀⟩ : X))
    have hxy : x * (x₀⁻¹ * p) = (x₀⁻¹ * p) * x :=
      (Subgroup.mem_centralizer_iff.mp (hYX hy)) x hx
    have hp_eq : p = x₀ * (x₀⁻¹ * p) := by group
    rw [hp_eq]
    calc (x₀ * (x₀⁻¹ * p)) * x = x₀ * ((x₀⁻¹ * p) * x) := by group
      _ = x₀ * (x * (x₀⁻¹ * p)) := by rw [← hxy]
      _ = (x₀ * x) * (x₀⁻¹ * p) := by group
      _ = (x * x₀) * (x₀⁻¹ * p) := by rw [← hxx₀]
      _ = x * (x₀ * (x₀⁻¹ * p)) := by group
  haveI hYnt : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).2 hY
  haveI hZnt : Nontrivial ↥(Subgroup.center Y) :=
    IsPGroup.center_nontrivial (p := 3) (hG := hY3)
  have h3dvd : 3 ∣ Nat.card ↥(Subgroup.center Y) := by
    rcases IsPGroup.card_eq_or_dvd (p := 3) (G := ↥(Subgroup.center Y))
      (hG := hY3.to_subgroup (Subgroup.center Y)) with h1 | h2
    · exact absurd h1 (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr hZnt))
    · exact h2
  obtain ⟨c, hc_order⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  let z : G := (c : Y)
  have hzY : z ∈ Y := (c : Y).2
  have hz_order : orderOf z = 3 := by
    show orderOf ((c : Y) : G) = 3
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc_order]
  have hz_center : ∀ y ∈ Y, z * y = y * z := by
    intro y hy
    have hc := (Subgroup.mem_center_iff.mp c.2) (⟨y, hy⟩ : Y)
    have hc' : y * ((c : Y) : G) = ((c : Y) : G) * y := by
      simpa using congrArg (Subtype.val : Y → G) hc
    exact hc'.symm
  have hz_centP : z ∈ centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    obtain ⟨x₀, hx₀, hy⟩ := exists_mul_mem_centOverO2 h hP hXP hP₁ hP₂ hp
    have hzx : x₀ * z = z * x₀ := (Subgroup.mem_centralizer_iff.mp (hYX hzY)) x₀ hx₀
    have hzy : z * (x₀⁻¹ * p) = (x₀⁻¹ * p) * z := hz_center _ hy
    have hp_eq : p = x₀ * (x₀⁻¹ * p) := by group
    rw [hp_eq]
    calc (x₀ * (x₀⁻¹ * p)) * z = x₀ * ((x₀⁻¹ * p) * z) := by group
      _ = x₀ * (z * (x₀⁻¹ * p)) := by rw [← hzy]
      _ = (x₀ * z) * (x₀⁻¹ * p) := by group
      _ = (z * x₀) * (x₀⁻¹ * p) := by rw [hzx]
      _ = z * (x₀ * (x₀⁻¹ * p)) := by group
  let E : Subgroup G := X₁ ⊔ Subgroup.zpowers z
  have hX₁P : X₁ ≤ P := inf_le_left.trans hXP
  have hX₁C : X₁ ≤ centralizer (P : Set G) := inf_le_left.trans hXcent
  have hzpY : Subgroup.zpowers z ≤ Y := Subgroup.zpowers_le.mpr hzY
  have hzpP : Subgroup.zpowers z ≤ P := Subgroup.zpowers_le.mpr (hYP hzY)
  have hzpC : Subgroup.zpowers z ≤ centralizer (P : Set G) := Subgroup.zpowers_le.mpr hz_centP
  have hE_P : E ≤ P := sup_le hX₁P hzpP
  have hE_C : E ≤ centralizer (P : Set G) := sup_le hX₁C hzpC
  have hX₁card : Nat.card X₁ = 3 := card_inf_left h
  have hzX : z ∈ centralizer (X : Set G) := hYX hzY
  have hzX₁ : z ∈ centralizer (X₁ : Set G) :=
    Subgroup.centralizer_le (show (X₁ : Set G) ⊆ (X : Set G) from inf_le_left) hzX
  have hzpN : Subgroup.zpowers z ≤ normalizer (X₁ : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (X₁ : Set G) hzX₁)
  have hdisj : X₁ ⊓ Subgroup.zpowers z = ⊥ :=
    le_bot_iff.mp ((inf_le_inf inf_le_left hzpY).trans (le_of_eq (disjoint_iff.mp hXY)))
  have hcard :=
    CFSG.GH74.Uniqueness.card_sup_mul_card_inf' (A := X₁) (C := Subgroup.zpowers z) hzpN
  rw [hdisj, Subgroup.card_bot, mul_one, hX₁card, Nat.card_zpowers z, hz_order] at hcard
  have hE_comm : IsMulCommutative E :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (hE_C.trans (Subgroup.centralizer_le (show (E : Set G) ⊆ (P : Set G) from hE_P)))
  refine ⟨E, le_inf hE_P hE_C, ⟨hE_comm, ?_⟩, ?_, ?_⟩
  · intro e he
    haveI : IsMulCommutative E := hE_comm
    have he' : e ∈ (X₁ : Set G) * (Subgroup.zpowers z : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left X₁ (Subgroup.zpowers z) hzpN]
      exact he
    rw [Set.mem_mul] at he'
    obtain ⟨a, ha, b, hb, hab⟩ := he'
    have ha3 : a ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hX₁card]
      exact Subgroup.orderOf_dvd_natCard X₁ ha
    have hb3 : b ^ 3 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← hz_order, ← Nat.card_zpowers z]
      exact Subgroup.orderOf_dvd_natCard (Subgroup.zpowers z) hb
    have hcomm : Commute a b := by
      have h := mul_comm' (⟨a, (le_sup_left : X₁ ≤ E) ha⟩ : E)
        (⟨b, (le_sup_right : Subgroup.zpowers z ≤ E) hb⟩ : E)
      exact congrArg Subtype.val h
    rw [← hab, Commute.mul_pow hcomm 3, ha3, hb3, mul_one]
  · change Nat.card ↥(X₁ ⊔ Subgroup.zpowers z) = 9
    rw [show X₁ ⊔ Subgroup.zpowers z = Subgroup.zpowers z ⊔ X₁ from sup_comm X₁ _]
    exact hcard.trans (by norm_num)
  · have hzT : z ∈ F08.CentOverO2 ⊤ L₂ := by
      rw [mem_centOverO2_iff]
      refine ⟨trivial, ?_⟩
      have hzL : ∀ l ∈ L₁ ⊔ L₂, z * l * z⁻¹ * l⁻¹ ∈ pCoreOf 2 (L₁ ⊔ L₂) :=
        (mem_centOverO2_iff.mp hzY).2
      have hz₁ : z ∈ normalizer (L₁ : Set G) := hP₁ (hYP hzY)
      have hz₂ : z ∈ normalizer (L₂ : Set G) := hP₂ (hYP hzY)
      exact ((acts_trivially_sup_iff h hz₁ hz₂).mp hzL).2
    have hE_T : E ≤ F08.CentOverO2 ⊤ L₂ := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [mem_centOverO2_iff]
        refine ⟨trivial, ?_⟩
        intro l hl
        rw [← commutatorElement_def]
        exact (Hyp141.commutator_le h
          (Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hx).2 hl)).2
      · exact Subgroup.zpowers_le.mpr hzT
    intro e he l hl
    exact (mem_centOverO2_iff.mp (hE_T he)).2 l hl

theorem normalizer_le_of_acts_trivially (h : Hyp141 D L₁ L₂ X) (h1422 : Thm1422 D)
    {L : Subgroup G} (hL : L ∈ ({L₁, L₂} : Set (Subgroup G))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {W : Subgroup G} (hW : IsPGroup p W) (hW1 : W ≠ ⊥)
    (hWn : W ≤ normalizer (L : Set G))
    (hWc : ∀ w ∈ W, ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : normalizer (W : Set G) ≤ D.M := by
  let K : Subgroup G := L ⊓ centralizer (W : Set G)
  let N : Subgroup G := normalizer (W : Set G)
  have hLK : L = K ⊔ pCoreOf 2 L := eq_sup_centralizer_of_acts_trivially hp hp2 hW hWn hWc
  have hcal : calNOf K = {D.M} := h1422 L₁ L₂ X h L hL K (show K ≤ L from inf_le_left) hLK
  have hKN : K ≤ N := inf_le_right.trans (Subgroup.centralizer_le_normalizer (W : Set G))
  have hNtop : N ≠ ⊤ := by
    intro hNt
    have hNt' : normalizer (W : Set G) = ⊤ := hNt
    have hWnormal : W.Normal := Subgroup.normalizer_eq_top_iff.mp hNt'
    haveI : W.Normal := hWnormal
    haveI : IsSimpleGroup G := D.standing.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with hbot | htop
    · exact hW1 hbot
    · exfalso
      have htopPG : IsPGroup p (⊤ : Subgroup G) := htop ▸ hW
      have hPG : IsPGroup p G := htopPG.of_equiv Subgroup.topEquiv
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : Group.IsNilpotent G := IsPGroup.isNilpotent hPG
      obtain ⟨a, b, hab⟩ := D.standing.nonab
      exact hab (mul_comm a b)
  rcases eq_top_or_exists_le_coatom N with hNt | ⟨A, hA, hNA⟩
  · exact absurd hNt hNtop
  · have hA_mem : A ∈ calNOf K := ⟨hA, hKN.trans hNA⟩
    have hA_eq : A = D.M := by
      rw [hcal] at hA_mem
      exact Set.mem_singleton_iff.mp hA_mem
    exact hNA.trans (le_of_eq hA_eq)

theorem gamma_le (h : Hyp141 D L₁ L₂ X) (h1422 : Thm1422 D) {P E : Subgroup G}
    (hP : IsPGroup 3 P) (hEP : E ≤ P) (hP₂ : P ≤ normalizer (L₂ : Set G))
    (hEc : ∀ e ∈ E, ∀ l ∈ L₂, e * l * e⁻¹ * l⁻¹ ∈ pCoreOf 2 L₂) :
    rankThreeGamma 1 3 E ≤ D.M := by
  show GLBCore 3 1 E ≤ D.M
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall fun Q hQE hQ => ?_
  have hQ1 : Q ≠ ⊥ := by
    intro hbot
    obtain ⟨E', hE'Q, -, hE'card⟩ :=
      CFSG.SectionRank.exists_pRank (p := 3) (show 1 < 3 by norm_num) Q
    rw [hbot] at hE'Q
    have hE'bot : E' = ⊥ := le_bot_iff.mp hE'Q
    have h1 : Nat.card E' = 1 := by rw [hE'bot, Subgroup.card_bot]
    rw [hE'card] at h1
    have h3le : 3 ≤ 3 ^ Open.pRank 3 Q := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ Open.pRank 3 Q := Nat.pow_le_pow_right (by norm_num) hQ
    rw [h1] at h3le
    omega
  exact normalizer_le_of_acts_trivially h h1422 (L := L₂) (by simp) Nat.prime_three (by norm_num)
    (hP.to_le (hQE.trans hEP)) hQ1 (hQE.trans (hEP.trans hP₂))
    (fun w hw l hl => hEc w (hQE hw) l hl)

end Hyp141

@[expose] def Thm143 (D : Data G) : Prop :=
  ∀ L₁ L₂ X : Subgroup G, Hyp141 D L₁ L₂ X →
    IsStronglyPEmbedded 3 D.M ∨ L₁ ⊔ L₂ = Opp 3 D.M

theorem thm143 {D : Data G} (h82 : F08.R82 D) (h614 : UC6.R6_14 D) (hSg : UC6S846.SigmaStd D)
    (h1422 : Thm1422 D) : Thm143 D := by
  intro L₁ L₂ X h
  by_cases hs : IsStronglyPEmbedded 3 D.M
  · exact Or.inl hs
  · refine Or.inr ?_
    by_contra hne
    have hperm : PermutesPair D.M L₁ L₂ := h.permutesPair h82 hs
    obtain ⟨P, hP, hXP⟩ := h.exists_isSylowOf_ge
    have hP3 : IsPGroup 3 P := hP.isPGroup
    have hPn : P ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) :=
      h.le_normalizer_of_isPGroup hperm Nat.prime_three (by norm_num) hP3 hP.le
    have hP₁ : P ≤ normalizer (L₁ : Set G) := hPn.trans inf_le_left
    have hP₂ : P ≤ normalizer (L₂ : Set G) := hPn.trans inf_le_right
    have hY : F08.CentOverO2 P (L₁ ⊔ L₂) ≠ ⊥ := by
      intro hYbot
      exact hne (h.opp_three_eq hperm hP hXP hP₁ hP₂ hYbot)
    obtain ⟨E, hEP, hEel, hEcard, hEtriv⟩ :=
      h.exists_elemAbelian_central hP3 hXP hP₁ hP₂ hY
    have hΓ : rankThreeGamma 1 3 E ≤ D.M :=
      h.gamma_le h1422 hP3 (hEP.trans inf_le_left) hP₂ hEtriv
    exact hs (h614 (h.sig_subset_sig1 hSg) 3 Nat.prime_three (by norm_num) h.three_notMem_sig
      P hP E hEP hEel (by rw [hEcard]; norm_num) hΓ)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
