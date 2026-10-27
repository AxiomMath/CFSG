module

public import CFSG.RankThree.PartTwo.Sec17.Item1723NRouteProofCore
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProof1724
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaS

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof1723N

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem para1725_at
    (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721) (h1723 : Item1723N)
    (h175 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item175 A c)
    (h : Sec17WQ G A c L Y₀ Y₁ S p P w Q)
    (htr : ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂) :
    ∃ (Y₁' S' P' : Subgroup G) (s : G), Sec17S G A c L Y₀ Y₁' S' p P' w Q s := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s₂, hs₂A, hs₂c, hs₂Aw⟩ :=
    h.toSec17W.exists_inverts_c_normalizes h415 h1715 h1721 h175
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  have hw3 : w ^ 3 = 1 := h.w_pow_three
  have hQ := h.mem_qStar_G
  obtain ⟨x, hx, hxQ⟩ := htr Q hQ _ (map_conj_mem_qStarTop hs₂A hQ)
  have hAwQ : A ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le h.le_normalizer_Q (Subgroup.zpowers_le.mpr h.w_normalizes_Q)
  have hwQs : w ∈ Subgroup.normalizer
      ((Q.map (MulAut.conj s₂).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    have hw : w ∈ (A ⊔ Subgroup.zpowers w).map (MulAut.conj s₂).toMonoidHom := by
      rw [Late.map_conj_eq_of_mem_normalizer hs₂Aw]
      exact (le_sup_right : Subgroup.zpowers w ≤ A ⊔ Subgroup.zpowers w) (Subgroup.mem_zpowers w)
    exact Subgroup.map_mono hAwQ hw
  have hwX : w ∈ Subgroup.normalizer ((xA A : Subgroup G) : Set G) := by
    have h1 : w ∈ Subgroup.normalizer
        ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
      refine mem_normalizer_of_map_conj_eq' ?_
      rw [map_conj_centralizer, Late.map_conj_eq_of_mem_normalizer hwA]
    exact normalizer_le_normalizer_pPrimeCoreOf 3 _ h1
  have hX3 : ¬ 3 ∣ Nat.card (xA A) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
  obtain ⟨y, hyX, hyw, hyQ⟩ := exists_commute_conj_eq hw3 hwX hX3 h.w_normalizes_Q hx
    (hxQ ▸ hwQs)
  set s₃ := y⁻¹ * s₂ with hs₃
  have hyA : y ∈ Subgroup.normalizer (A : Set G) := xA_le_normalizer A hyX
  have hyC : y ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hyX
  have hs₃A : s₃ ∈ Subgroup.normalizer (A : Set G) := mul_mem (inv_mem hyA) hs₂A
  have hs₃Q : s₃ ∈ Subgroup.normalizer (Q : Set G) :=
    inv_mul_mem_normalizer_of_map_conj_eq (hyQ.trans hxQ.symm)
  have hyc : y * c = c * y := (Subgroup.mem_centralizer_iff.mp hyC c h.c_mem).symm
  have hs₃c : s₃ * c * s₃⁻¹ = c⁻¹ := by
    have hyc' : y⁻¹ * c⁻¹ * y⁻¹⁻¹ = c⁻¹ := conj_inv_eq_of_commute hyc
    calc s₃ * c * s₃⁻¹ = y⁻¹ * (s₂ * c * s₂⁻¹) * y⁻¹⁻¹ := by rw [hs₃]; group
      _ = c⁻¹ := by rw [hs₂c, hyc']
  have hyAw : y⁻¹ ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) := by
    refine inv_mem (mem_normalizer_sup hyA ?_)
    refine mem_normalizer_of_map_conj_eq' ?_
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (y * w * y⁻¹) = _
    rw [hyw, mul_inv_cancel_right]
  have hs₃Aw : s₃ ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) :=
    mul_mem hyAw hs₂Aw
  obtain ⟨j, hj⟩ := exists_conj_eq_pow h1723 h.toSec17W hs₃A
  refine ⟨Y₁, S, P, (w ^ j)⁻¹ * s₃,
    { toSec17WQ := h
      s_mem_W := mul_mem (inv_mem (pow_mem hwA j)) hs₃A
      s_inverts_c := ?_
      s_normalizes_Aw := mul_mem (inv_mem (pow_mem (Subgroup.le_normalizer
        ((le_sup_right : Subgroup.zpowers w ≤ A ⊔ Subgroup.zpowers w)
          (Subgroup.mem_zpowers w))) j)) hs₃Aw
      s_normalizes_Q := mul_mem (inv_mem (pow_mem h.w_normalizes_Q j)) hs₃Q
      s_normalizes_y1 := inv_mul_mem_normalizer_of_map_conj_eq hj.symm }⟩
  have hwc : w ^ j * c = c * w ^ j := ((Commute.pow_right (show Commute c w from
    h.w_commute_c) j)).eq.symm
  have hwc' : (w ^ j)⁻¹ * c⁻¹ * (w ^ j)⁻¹⁻¹ = c⁻¹ := conj_inv_eq_of_commute hwc
  calc (w ^ j)⁻¹ * s₃ * c * ((w ^ j)⁻¹ * s₃)⁻¹ = (w ^ j)⁻¹ * (s₃ * c * s₃⁻¹) * (w ^ j)⁻¹⁻¹ := by
        group
    _ = c⁻¹ := by rw [hs₃c, hwc']

end Proof1723N

theorem para1725_of_1723N
    (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721) (h1723 : Item1723N)
    (h1724 : Item1724N)
    (h175 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item175 A c) :
    Para1725 := fun G _ _ A c L Y₀ Y₁ S p P w Q h =>
  Proof1723N.para1725_at h415 h1715 h1721 h1723 h175 h
    (h1724 G A c L Y₀ Y₁ S p P w Q h.toSec17W).1

end CFSG.RankThree.PartTwo.Sec17
