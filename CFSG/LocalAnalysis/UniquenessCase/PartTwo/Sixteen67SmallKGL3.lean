module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGAt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGCite
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGCom
import CFSG.Quasithin.Vol2.Ch11SecOE7F
import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Orders
import CFSG.Walter.PSL2Facts.Even
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1OddL3Inputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem s1667_kg_u3even_orderOf_le {D : Type} [Group D] {f : ℕ} (hf : 2 ≤ f)
    (hD : LieModel D .PSU 3 2 f) (α : MulAut D) (hα : α ^ 2 = 1)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) {y : D} (hy : α y = y) :
    orderOf y ≤ 2 ^ f + 1 := by
  have hα1 : α ≠ 1 := by
    intro h
    apply hαout
    rw [h]
    exact Subgroup.one_mem _
  have hα2 : orderOf α = 2 := orderOf_eq_prime hα hα1
  obtain ⟨k, hFk, hFin, hchar, j, hk, hjinj, hfix, -⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.fixed_iff_mem_range_of_outer hf
      (hD.statedClassicalModel (by decide)) α hα2 hαout
  obtain ⟨m, rfl⟩ := (hfix y).mp hy
  rw [orderOf_injective j hjinj m]
  let e := CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := k)
  calc orderOf m = orderOf (e.symm m) := (MulEquiv.orderOf_eq e.symm m).symm
    _ ≤ Nat.card k + 1 :=
      CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le k _
    _ = 2 ^ f + 1 := by rw [hk]

theorem s1667_kg_outer_involution_orderOf_le (hC2 : K67OuterInvL3U3) {J : Type} [Group J]
    [Finite J] {p f : ℕ} (hq : 4 ≤ p ^ f)
    (h : (p ^ f % 3 = 2 ∧ LieModel J .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel J .PSU 3 p f))
    (α : MulAut J) (hα : α ^ 2 = 1) (hαout : α ∉ (MulAut.conj : J →* MulAut J).range) {y : J}
    (hy : α y = y) : orderOf y ≤ p ^ f + 1 := by
  rcases h with ⟨h2, hL⟩ | ⟨h1, hU⟩
  · exact hC2 J p f (Or.inl ⟨h2, hL⟩) α hα hαout y hy
  · by_cases hp2 : p = 2
    · subst hp2
      have hf : 2 ≤ f := by
        by_contra hlt
        have hf1 : f ≤ 1 := by omega
        have h21 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hf1
        omega
      exact s1667_kg_u3even_orderOf_le hf hU α hα hαout hy
    · exact hC2 J p f (Or.inr ⟨hp2, h1, hU⟩) α hα hαout y hy

theorem s1667_kg_l3u3_centralizer {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q)
    (hC1 : K67CentL3U3) {p f : ℕ}
    (h : (p ^ f % 3 = 2 ∧ LieModel ↥J .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel ↥J .PSU 3 p f))
    {x : Q} (hx : x ∈ J) (hx3 : orderOf x = 3) :
    IsCyclic ↥(J ⊓ centralizer ({x} : Set Q)) ∧
      Nat.card ↥(J ⊓ centralizer ({x} : Set Q)) = (p ^ f) ^ 2 - 1 := by
  let x' : ↥J := ⟨x, hx⟩
  have hx'3 : orderOf x' = 3 := (Subgroup.orderOf_coe x').symm.trans hx3
  obtain ⟨hcyc, hcard⟩ := hC1 ↥J p f h x' hx'3
  have hTJ : J ⊓ centralizer ({x} : Set Q) ≤ J := inf_le_left
  have heq : (J ⊓ centralizer ({x} : Set Q)).subgroupOf J = centralizer ({x'} : Set ↥J) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun hh => Subtype.ext hh.2, fun hh => ⟨y.2, congrArg Subtype.val hh⟩⟩
  constructor
  · have hcyc' : IsCyclic ↥((J ⊓ centralizer ({x} : Set Q)).subgroupOf J) := by
      rw [heq]
      exact hcyc
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTJ).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTJ).surjective
  · rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv, heq]
    exact hcard

theorem k67_l3u3_elemAbelian_le {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) (hC1 : K67CentL3U3) (hC2 : K67OuterInvL3U3) {p f : ℕ}
    (hq : 4 ≤ p ^ f)
    (h : (p ^ f % 3 = 2 ∧ LieModel ↥J .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel ↥J .PSU 3 p f))
    {x : Q} (hx : x ∈ J) (hx3 : orderOf x = 3) {B : Subgroup Q} (hB : IsElemAbelian 2 B)
    (hBx : B ≤ centralizer ({x} : Set Q))
    (hBn : ∀ t ∈ J ⊓ centralizer ({x} : Set Q), t ∈ normalizer (B : Set Q)) : B ≤ J := by
  haveI := hJ
  obtain ⟨hcyc, hcard⟩ := s1667_kg_l3u3_centralizer J hC1 h hx hx3
  obtain ⟨g, hgT, hgen⟩ := s1667_kg_exists_generator hcyc
  have hgJ : g ∈ J := (Subgroup.mem_inf.mp hgT).1
  have hgx : g ∈ centralizer ({x} : Set Q) := (Subgroup.mem_inf.mp hgT).2
  have hzT : zpowers g = J ⊓ centralizer ({x} : Set Q) :=
    le_antisymm (Subgroup.zpowers_le.mpr hgT) (fun t ht => hgen t ht)
  have hord : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [← Nat.card_zpowers, hzT]
    exact hcard
  intro b hb
  by_contra hbJ
  have hb2 : b ^ 2 = 1 := hB.2 b hb
  let α : MulAut ↥J := MulAut.conjNormal b
  have hα2 : α ^ 2 = 1 := by
    have hpow : (MulAut.conjNormal (b ^ 2) : MulAut ↥J) = (MulAut.conjNormal b : MulAut ↥J) ^ 2 :=
      map_pow _ _ _
    rw [← hpow, hb2, map_one]
  have hαout : α ∉ (MulAut.conj : ↥J →* MulAut ↥J).range := fun hmem =>
    hbJ ((s1667_kg_mem_iff_conjNormal_mem_range J hC b).mpr hmem)
  have hc : g ^ 2 * b = b * g ^ 2 :=
    s1667_kg_sq_comm_of_cyclic J hgJ hgx (fun t ht => hgen t ht) hB hBx (hBn g hgT) hb
  let y : ↥J := ⟨g ^ 2, J.pow_mem hgJ 2⟩
  have hαy : α y = y := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply b y]
    show b * g ^ 2 * b⁻¹ = g ^ 2
    rw [← hc]
    exact mul_inv_cancel_right (g ^ 2) b
  have hle : orderOf y ≤ p ^ f + 1 :=
    s1667_kg_outer_involution_orderOf_le hC2 hq h α hα2 hαout hαy
  have hyord : orderOf y = orderOf (g ^ 2) := (Subgroup.orderOf_coe y).symm
  rw [hyord, orderOf_pow' g (by norm_num : (2 : ℕ) ≠ 0), hord] at hle
  have hd2 : Nat.gcd ((p ^ f) ^ 2 - 1) 2 ≤ 2 := Nat.gcd_le_right _ (by norm_num)
  have hdpos : 0 < Nat.gcd ((p ^ f) ^ 2 - 1) 2 := Nat.gcd_pos_of_pos_right _ (by norm_num)
  have hq4 : (p ^ f + 2) * 2 + 1 ≤ (p ^ f) ^ 2 := by
    generalize p ^ f = q at hq ⊢
    nlinarith
  have hdiv : p ^ f + 2 ≤ ((p ^ f) ^ 2 - 1) / Nat.gcd ((p ^ f) ^ 2 - 1) 2 := by
    rw [Nat.le_div_iff_mul_le hdpos]
    calc (p ^ f + 2) * Nat.gcd ((p ^ f) ^ 2 - 1) 2 ≤ (p ^ f + 2) * 2 :=
          Nat.mul_le_mul_left _ hd2
      _ ≤ (p ^ f) ^ 2 - 1 := by omega
  omega

theorem k67BPrimeOneAt_l3u3 {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) (hC1 : K67CentL3U3) (hC2 : K67OuterInvL3U3) {p f : ℕ}
    (hq : 4 ≤ p ^ f)
    (h : (p ^ f % 3 = 2 ∧ LieModel ↥J .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel ↥J .PSU 3 p f)) :
    K67BPrimeOneAt Q J := by
  intro x hxJ hx3 A hA hAx hAn h4
  exfalso
  have hAJ : A ≤ J := k67_l3u3_elemAbelian_le J hJ hC hC1 hC2 hq h hxJ hx3 hA hAx hAn
  have hAT : A ≤ J ⊓ centralizer ({x} : Set Q) := le_inf hAJ hAx
  have hcyc := (s1667_kg_l3u3_centralizer J hC1 h hxJ hx3).1
  have h2 := s1667_kg_card_le_two_of_le_cyclic hcyc hAT hA
  omega

theorem k67CaseIIIAt_l3u3 {Q : Type} [Group Q] [Finite Q] (J : Subgroup Q) (hJ : J.Normal)
    (hC : centralizer (J : Set Q) = ⊥) (hC1 : K67CentL3U3) (hC2 : K67OuterInvL3U3) {p f : ℕ}
    (hq : 4 ≤ p ^ f)
    (h : (p ^ f % 3 = 2 ∧ LieModel ↥J .PSL 3 p f) ∨ (p ^ f % 3 = 1 ∧ LieModel ↥J .PSU 3 p f)) :
    K67CaseIIIAt Q J := by
  intro x hxJ hx3 E hE hE4 hEJ hEx W hW hW1 hWx hWE hN
  have hTn : ∀ t ∈ J ⊓ centralizer ({x} : Set Q), t ∈ normalizer (W : Set Q) := fun t ht =>
    (hN t (s1667_kg_mem_normalizer_zpowers_of_mem_centralizer (Subgroup.mem_inf.mp ht).2)).2
  have hWJ : W ≤ J := k67_l3u3_elemAbelian_le J hJ hC hC1 hC2 hq h hxJ hx3 hW hWx hTn
  obtain ⟨-, hcard⟩ := s1667_kg_l3u3_centralizer J hC1 h hxJ hx3
  obtain ⟨w, hwW, hw1⟩ : ∃ w ∈ W, w ≠ 1 := by
    obtain ⟨⟨w, hw⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW1
    exact ⟨w, hw, fun h1 => hne (Subtype.ext h1)⟩
  have hw2 : w ^ 2 = 1 := hW.2 w hwW
  have hord : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  by_cases hq2 : Even (p ^ f)
  · have hwT : w ∈ J ⊓ centralizer ({x} : Set Q) := ⟨hWJ hwW, hWx hwW⟩
    have hdvd : 2 ∣ Nat.card ↥(J ⊓ centralizer ({x} : Set Q)) := by
      have := Subgroup.orderOf_dvd_natCard _ hwT
      rwa [hord] at this
    rw [hcard] at hdvd
    have hev : Even ((p ^ f) ^ 2) := Nat.even_pow.mpr ⟨hq2, by norm_num⟩
    have hmod : (p ^ f) ^ 2 % 2 = 0 := Nat.even_iff.mp hev
    have hpos : 0 < (p ^ f) ^ 2 := pow_pos (by omega) 2
    omega
  · have hp2 : p ≠ 2 := by
      intro hp
      subst hp
      apply hq2
      refine Nat.even_pow.mpr ⟨even_two, ?_⟩
      intro hf0
      rw [hf0] at hq
      norm_num at hq
    have hS : CFSG.Open.StatedClassicalModel ↥J .PSL 3 p f ∨
        CFSG.Open.StatedClassicalModel ↥J .PSU 3 p f := by
      rcases h with ⟨-, hL⟩ | ⟨-, hU⟩
      · exact Or.inl (hL.statedClassicalModel (by decide))
      · exact Or.inr (hU.statedClassicalModel (by decide))
    have hEW : E ⊓ W = ⊥ := by
      rw [eq_bot_iff, ← hEx]
      exact inf_le_inf_left E hWx
    have hcomm : ∀ a ∈ E, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp (hWE hb)) a ha
    obtain ⟨hEWab, hEWcard⟩ := s1667_kg_elemAbelian_sup_card_gt hE hE4 hW hW1 hcomm hEW
    have hEWJ : E ⊔ W ≤ J := sup_le hEJ hWJ
    have hel : IsElemAbelian 2 ((E ⊔ W).subgroupOf J) := hEWab.comap J.subtype_injective
    have hle := CFSG.RankThree.PartTwo.Sec15.Sylow155R1.res1OddL3_card_elemAbelian_le_four hp2 hS
      ((E ⊔ W).subgroupOf J) (fun a ha b hb => hel.comm ha hb) hel.2
    have hcardeq : Nat.card ↥((E ⊔ W).subgroupOf J) = Nat.card ↥(E ⊔ W) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEWJ).toEquiv
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
