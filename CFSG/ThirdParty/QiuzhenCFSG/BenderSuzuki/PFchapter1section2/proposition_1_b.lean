module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section2

open PFchapter1section1 PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 2, Proposition 1(b)
-/

private theorem proposition_1_b_exists_rank_two_subgroup_le_Q
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (h2rank : TwoRankAtLeastTwo G) :
    ∃ A : Subgroup G, A ≤ Q ∧ Nat.card A = 4 ∧ ∀ x : A, x ^ 2 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀card, hE₀sq⟩ := TwoRankAtLeastTwo.exists_subgroup h2rank
  have hE₀p : IsPGroup 2 E₀ := by
    refine IsPGroup.of_card (p := 2) (G := E₀) (n := 2) ?_
    norm_num [hE₀card]
  obtain ⟨T, hE₀T⟩ := IsPGroup.exists_le_sylow (G := G) (p := 2) hE₀p
  obtain ⟨S, hSQ⟩ := PFchapter1section1.proposition_1_c H D Q t hA1
  obtain ⟨g, hgTS⟩ := MulAction.exists_smul_eq G T S
  let A : Subgroup G := E₀.map (MulAut.conj g).toMonoidHom
  have hA_le_S : A ≤ (S : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyE, rfl⟩
    have hyT : y ∈ (T : Subgroup G) := hE₀T hyE
    rw [← hgTS, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) (T : Subgroup G) hyT
  have hAcard : Nat.card A = 4 := by
    have hcard_map :
        Nat.card A = Nat.card E₀ := by
      exact Subgroup.card_map_of_injective
        (K := E₀) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [hcard_map, hE₀card]
  have hAsq : ∀ x : A, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    rcases Subgroup.mem_map.mp x.property with ⟨y, hyE, hyx⟩
    have hy2 : y ^ 2 = (1 : G) := by
      exact congrArg Subtype.val (hE₀sq ⟨y, hyE⟩)
    rw [← hyx]
    simpa [pow_two] using congrArg (fun z : G => (MulAut.conj g) z) hy2
  exact ⟨A, hA_le_S.trans hSQ, hAcard, hAsq⟩

public theorem proposition_1_b_exists_two_distinct_nontrivial_of_card_four
    {A : Type*} [Group A] [Finite A] (hcard : Nat.card A = 4) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have htwo_lt : 2 < Fintype.card A := by
    omega
  rcases Fintype.two_lt_card_iff.mp htwo_lt with ⟨a, b, c, hab, hac, hbc⟩
  by_cases ha : a = 1
  · by_cases hb : b = 1
    · exact False.elim (hab (ha.trans hb.symm))
    · by_cases hc : c = 1
      · exact False.elim (hac (ha.trans hc.symm))
      · exact ⟨b, c, hb, hc, hbc⟩
  · by_cases hb : b = 1
    · by_cases hc : c = 1
      · exact False.elim (hbc (hb.trans hc.symm))
      · exact ⟨a, c, ha, hc, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

public theorem proposition_1_b_peterfalviKSet_nontrivial
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t) :
    ∃ x : G, x ∈ peterfalviKSet D t ∧ x ≠ 1 := by
  classical
  obtain ⟨A, hAQ, hAcard, hAsq⟩ :=
    proposition_1_b_exists_rank_two_subgroup_le_Q H D Q t hA.A1 hA.A3
  obtain ⟨a, b, ha_ne, hb_ne, hab⟩ :=
    proposition_1_b_exists_two_distinct_nontrivial_of_card_four hAcard
  let s : G := a
  let y : G := b
  have hsH : s ∈ H := hA.A1.Q_le_H (hAQ a.property)
  have hyH : y ∈ H := hA.A1.Q_le_H (hAQ b.property)
  have hsI : IsInvolution s := by
    constructor
    · intro hs_one
      exact ha_ne (Subtype.ext hs_one)
    · exact congrArg Subtype.val (hAsq a)
  have hyI : IsInvolution y := by
    constructor
    · intro hy_one
      exact hb_ne (Subtype.ext hy_one)
    · exact congrArg Subtype.val (hAsq b)
  rcases
      ((PFchapter1section1.proposition_3 H D Q t hA.A1).2
        s hsH hsI y).1 ⟨hyH, hyI⟩ with
    ⟨k, hkKset, hk_eq⟩
  refine ⟨k, hkKset, ?_⟩
  intro hk_one
  have hy_eq_s : y = s := by
    calc
      y = rightConjugateElem s k := hk_eq.symm
      _ = s := by simp [hk_one, rightConjugateElem]
  have hba : b = a := Subtype.ext hy_eq_s
  exact hab hba.symm

public theorem proposition_1_b_K_nontrivial
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    ∃ x : G, x ∈ K ∧ x ≠ 1 := by
  obtain ⟨x, hxK, hxne⟩ :=
    proposition_1_b_peterfalviKSet_nontrivial H D Q t hsec.hA
  exact ⟨x, (hsec.K_def x).mpr hxK, hxne⟩

public theorem proposition_1_b_of_hA
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA : HypothesisA G Ω H D Q t) :
    Group.IsNilpotent Q := by
  classical
  obtain ⟨x, hxK, hxne⟩ :=
    proposition_1_b_peterfalviKSet_nontrivial H D Q t hA
  let X : Subgroup G := Subgroup.zpowers x
  have hX_le_D : X ≤ D := by
    exact Subgroup.zpowers_le.mpr hxK.1
  have hX_norm_Q : X ≤ Subgroup.normalizer (Q : Set G) := by
    intro k hkX
    have hkH : k ∈ H := hA.A1.D_le_H (hX_le_D hkX)
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hqQ
      let qH : H := ⟨q, hA.A1.Q_le_H hqQ⟩
      let kH : H := ⟨k, hkH⟩
      have hqSub : qH ∈ Q.subgroupOf H := by
        simpa [qH, Subgroup.mem_subgroupOf] using hqQ
      have hconj := hA.A1.Q_normal_in_H.conj_mem qH hqSub kH
      simpa [qH, kH, Subgroup.mem_subgroupOf] using hconj
    · intro hqQ
      have hkInvH : k⁻¹ ∈ H := H.inv_mem hkH
      let qH : H := ⟨k * q * k⁻¹, hA.A1.Q_le_H hqQ⟩
      let kInvH : H := ⟨k⁻¹, hkInvH⟩
      have hqSub : qH ∈ Q.subgroupOf H := by
        simpa [qH, Subgroup.mem_subgroupOf] using hqQ
      have hconj := hA.A1.Q_normal_in_H.conj_mem qH hqSub kInvH
      change k⁻¹ * (k * q * k⁻¹) * (k⁻¹)⁻¹ ∈ Q at hconj
      simpa [mul_assoc] using hconj
  have hX_nontrivial : ∃ y : G, y ∈ X ∧ y ≠ 1 :=
    ⟨x, Subgroup.mem_zpowers x, hxne⟩
  have hfixed : ∀ y : G, y ∈ X → y ≠ 1 →
      Subgroup.centralizer ({y} : Set G) ⊓ Q = ⊥ := by
    intro y hyX hyne
    have hyanti : rightConjugateElem y t = y⁻¹ := by
      rcases Subgroup.mem_zpowers_iff.mp hyX with ⟨n, rfl⟩
      have hxanti := hxK.2
      change t⁻¹ * x * t = x⁻¹ at hxanti
      change t⁻¹ * x ^ n * t = (x ^ n)⁻¹
      calc
        t⁻¹ * x ^ n * t = (t⁻¹ * x * t) ^ n := by
          simpa using (conj_zpow (a := t⁻¹) (b := x) (i := n)).symm
        _ = (x⁻¹) ^ n := by rw [hxanti]
        _ = (x ^ n)⁻¹ := by simp
    exact proposition_1_a_of_mem_peterfalviKSet H D Q t hA.A1 y
      ⟨hX_le_D hyX, hyanti⟩ hyne
  exact External.huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
    Q X hX_norm_Q hX_nontrivial hfixed

public theorem proposition_1_b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q)) :
    Group.IsNilpotent Q := by
  exact proposition_1_b_of_hA H D Q t hsec.hA

end PFchapter1section2
end CFSG.BenderSuzuki
