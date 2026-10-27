module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat5
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CNat7
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223L3Orb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223W21
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_of_le' {A B : Subgroup G} (h : A ≤ B) (hB : IsElemAbelian 2 B) :
    IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hB h

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem exists_orderOf_three_K : ∃ y ∈ oTwoUpper H, orderOf y = 3 := by
  have hK9 : Nat.card ↥(oTwoUpper H) = Nat.card ↥(pCoreOf 2 (oTwoUpper H)) * 9 := by
    rw [card_eq_card_pCoreOf_mul_relIndex (oTwoUpper H), d.c.relIndex_K]
  have h3 : 3 ∣ Nat.card ↥(oTwoUpper H) := by
    rw [hK9]
    exact Dvd.dvd.mul_left (by norm_num) _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(oTwoUpper H)) 3 h3
  exact ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩

theorem K_le_oPrimeResidualOf : oTwoUpper H ≤ oPrimeResidualOf 3 (oTwoUpper H) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hxK : x ∈ oTwoUpper H := mem_oTwoUpper_of_odd hx.1 hx.2
  have h3 := d.c.pow_three_of_odd hxK hx.2
  by_cases h1 : x = 1
  · rw [h1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨hxK, 1, by rw [pow_one]; exact orderOf_eq_prime h3 h1⟩

theorem conjClosure_eq_kI
    (hc : conjClosure (oTwoUpper H) Mc ≤ Subgroup.centralizer (zSOf T Mc M B₀ : Set G))
    (hL4 : IsLnTwo 4 (OTwoQuot (kI T Mc M B₀))) :
    conjClosure (oTwoUpper H) Mc = kI T Mc M B₀ := by
  set Kc := conjClosure (oTwoUpper H) Mc with hKc
  have hb : Kc ≤ oPrimeResidualOf 3 Kc := conjClosure_le fun g hg x hx =>
    S15223.conj_mem_oPrimeResidualOf_of_le (fun y hy => mem_conjClosure hg hy)
      (d.K_le_oPrimeResidualOf hx)
  have hcI : Kc ≤ kI T Mc M B₀ :=
    hb.trans (Subgroup.closure_mono fun x hx => ⟨hc hx.1, hx.2⟩)
  have hQN : kI T Mc M B₀ ≤ Subgroup.normalizer (Kc : Set G) :=
    ((kI_le_centralizer T Mc M B₀).trans ((centralizer_zS_le_inf152 d.c.inputs).trans
      inf_le_left)).trans (le_normalizer_conjClosure (oTwoUpper H) Mc)
  have hNn : (Kc.subgroupOf (kI T Mc M B₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcI).2 hQN
  have hsimple := isSimple_quot_of_isLnTwo_four hL4
  obtain ⟨y, hyK, hy3⟩ := d.exists_orderOf_three_K
  have hyKc : y ∈ Kc := le_conjClosure _ Mc hyK
  have hyQ : y ∈ kI T Mc M B₀ := hcI hyKc
  refine le_antisymm hcI ((Subgroup.closure_le _).mpr fun x hx => ?_)
  obtain ⟨hxC, a, ha⟩ := hx
  have hxQ : x ∈ kI T Mc M B₀ := Subgroup.subset_closure ⟨hxC, a, ha⟩
  have hy3' : orderOf (⟨y, hyQ⟩ : ↥(kI T Mc M B₀)) = 3 :=
    (Subgroup.orderOf_coe (⟨y, hyQ⟩ : ↥(kI T Mc M B₀))).symm.trans hy3
  have hxa : orderOf (⟨x, hxQ⟩ : ↥(kI T Mc M B₀)) = 3 ^ a :=
    (Subgroup.orderOf_coe (⟨x, hxQ⟩ : ↥(kI T Mc M B₀))).symm.trans ha
  have h := mem_of_orderOf_pow_three (N := Kc.subgroupOf (kI T Mc M B₀)) (y := ⟨y, hyQ⟩)
    (Subgroup.mem_subgroupOf.2 hyKc) hy3' (x := ⟨x, hxQ⟩) (a := a) hxa
  exact Subgroup.mem_subgroupOf.1 h

theorem exists_Y1 (hF : ¬ X ≤ Mc) {n : ℕ} {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) (hn : 1 < n)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1) :
    ∃ Y₁ : Subgroup G, Y₁ = oTwoUpper Y₁ ∧ Y₁ ≤ M ⊓ I ∧
      sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₁ : Set G) ∧
      Nonempty (OTwoQuot (Y₁ ⊔ sOf152 T Mc M B₀) ≃* Equiv.Perm (Fin 3)) ∧ ¬ Y₁ ≤ Mc ⊓ I := by
  set S := sOf152 T Mc M B₀ with hS
  set P := parab (X ⊔ S) n W 1 with hP
  have hF' := d.facts15128 hF
  have hSyl : IsSylowTwoOf S P :=
    isSylowTwoOf_restrict d.sylow_sup (D.S_le_parab 1) (parab_le _ _ _ _)
  have hPeq : P = oTwoUpper P ⊔ S := eq_oTwoUpper_sup_of_isSylowTwoOf hSyl
  have hE : IsElemAbelian 2 (W 2) :=
    isElemAbelian_of_le' ((D.W_le 2 (by norm_num) (by have := D.three_le; omega)).trans
      (hF'.ULU)) d.isTwoReduced_W.1
  have hSMc : S ≤ Mc := S_le_T152.trans d.c.setting.qtfe.t_le_mc
  refine ⟨oTwoUpper P, (oTwoUpper_idem P).symm,
    (oTwoUpper_le P).trans (d.parab_le_NI hF D hn hZW),
    (D.S_le_parab 1).trans (le_normalizer_oTwoUpper P), ?_, fun h => ?_⟩
  · rw [← hPeq]
    exact oTwoQuot_parab_perm D hE
  · exact d.not_parab_le_Mc hF D hn hZW
      (hPeq.le.trans (sup_le h (le_inf hSMc (S_le_I152 d.c.inputs))))

theorem false_of_five
    (h21 : ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      Lemma15221ConclW T Mc M H H₁ H₂ B₀ I)
    (hF : ¬ X ≤ Mc) {W : ℕ → Subgroup G}
    (D : P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) 5 W)
    (hZW : zUOf1528 (zSOf T Mc M B₀) X = W 1)
    (hL4 : IsLnTwo 4 (OTwoQuot (kI T Mc M B₀))) : False := by
  obtain ⟨H₁, H₂, hpair⟩ := d.c.inputs.hN.pair
  have h21' := h21 H₁ H₂ hpair
  have hnot := d.not_irred_of_natural D
  have hone := h21'.one hnot
  have hKc : conjClosure (oTwoUpper H) Mc = kI T Mc M B₀ := d.conjClosure_eq_kI hone.2.2.1 hL4
  obtain ⟨Y₁, hY, hYN, hYS, hYQ, hYM⟩ := d.exists_Y1 hF D (by norm_num) hZW
  exact hnot (h21'.three (by rw [hKc]; exact hL4) d.c.concl ⟨Y₁, hY, hYN, hYS, hYQ, hYM⟩)

end CData

end C

end S15223P4

end CFSG.Quasithin
