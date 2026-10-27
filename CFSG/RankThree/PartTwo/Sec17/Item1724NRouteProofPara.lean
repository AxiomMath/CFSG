module

public import CFSG.RankThree.PartTwo.Sec17.Item17ParaR
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
public import CFSG.RankThree.PartTwo.Sec17.Item1721StepsProof1724
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaW
public import CFSG.RankThree.PartTwo.Sec17.Item17Statements

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof1724N

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem para1724_at (h : Sec17W G A c L Y₀ Y₁ S p P w Q)
    (htr : ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂) :
    Sec4.autIn (Subgroup.normalizer (Q : Set G)) A = wStar A ∧
      ∃ w' : G, Sec17WQ G A c L Y₀ Y₁ S p P w' Q := by
  have hQ := h.mem_qStar_G
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  ·
    intro σ hσ
    obtain ⟨g, hgN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    exact Sec4.mem_autIn_iff.mpr ⟨g, hgN, Subgroup.mem_top g, rfl⟩
  ·
    intro σ hσ
    obtain ⟨g, hgN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    obtain ⟨x, hx, hQx⟩ := htr Q hQ _ (map_conj_mem_qStarTop hgN hQ)
    have hxg : x⁻¹ * g ∈ Subgroup.normalizer (A : Set G) :=
      mul_mem (inv_mem (xA_le_normalizer A hx)) hgN
    refine Sec4.mem_autIn_iff.mpr ⟨x⁻¹ * g, hxg,
      inv_mul_mem_normalizer_of_map_conj_eq hQx.symm, ?_⟩
    exact normalizerMonoidHom_inv_mul_eq hgN (pPrimeCoreOf_le 3 _ hx) hxg
  ·
    have hw3 := h.w_pow_three
    have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
    have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
    let f : scriptQPiStar A (lB A) ⊤ (piOf p) → scriptQPiStar A (lB A) ⊤ (piOf p) :=
      fun R => ⟨(R : Subgroup G).map (MulAut.conj w).toMonoidHom,
        map_conj_mem_qStarTop hwA R.2⟩
    have hf : ∀ R, f (f (f R)) = R := by
      intro R
      apply Subtype.ext
      change (((R : Subgroup G).map (MulAut.conj w).toMonoidHom).map
        (MulAut.conj w).toMonoidHom).map (MulAut.conj w).toMonoidHom = R
      rw [map_conj_map_conj, map_conj_map_conj, show w * w * w = 1 by
        rw [← hw3, pow_three, mul_assoc], map_conj_one]
    obtain ⟨R, hR⟩ := exists_fixed_of_cube_eq_id f hf (not_three_dvd_card_qStar htr hQ)
    have hRw : (R : Subgroup G).map (MulAut.conj w).toMonoidHom = R := congrArg Subtype.val hR
    obtain ⟨x, hx, hxR⟩ := htr Q hQ R R.2
    have hwN : w ∈ Subgroup.normalizer
        ((Q.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
      rw [← hxR]
      exact mem_normalizer_of_map_conj_eq' hRw
    have hxA : x ∈ Subgroup.normalizer (A : Set G) := xA_le_normalizer A hx
    have hxc : x ∈ Subgroup.centralizer ({c} : Set G) := xA_le_centralizer_of_mem h.c_mem hx
    have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
      Sec15R.centralizer_le_normalizer_L h.toSec15R
        (three_dvd_card_of_mem hwL h.orderOf_w) hxc
    have hconj : x⁻¹ * w * x = MulAut.conj x⁻¹ w := by
      rw [MulAut.conj_apply, inv_inv]
    refine ⟨x⁻¹ * w * x,
      { toSec17W :=
          { toSec17Y1 := h.toSec17Y1
            w_mem := Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hxA) hwA) hxA, ?_⟩
            w_not_mem := ?_
            orderOf_w := ?_
            le_Q := h.le_Q
            mem_qStar_G := hQ }
        w_normalizes_Q := conj_mem_normalizer_of_mem_normalizer_map hwN }⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxL) w).mp hwL
      rwa [inv_inv] at this
    · intro hmem
      apply h.w_not_mem
      have := (Subgroup.mem_normalizer_iff.mp hxA _).mp hmem
      have e : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
      rwa [e] at this
    · rw [hconj, MulEquiv.orderOf_eq, h.orderOf_w]

theorem para1726_at (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721)
    (h176 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item176 A (lB A) c L) {s : G}
    (h : Sec17S G A c L Y₀ Y₁ S p P w Q s)
    (htr : ∀ Q₁ ∈ scriptQPiStar A (lB A) ⊤ (piOf p), ∀ Q₂ ∈ scriptQPiStar A (lB A) ⊤ (piOf p),
      IsConjIn (xA A) Q₁ Q₂) :
    ∃ d r : G, Sec17Data G A c L Y₀ Y₁ S p P w Q s d r := by
  have : Fact p.Prime := ⟨h.p_prime⟩
  have hJ := h1721 G A c L Y₀ Y₁ S p P h.toSec17Y1
  obtain ⟨hΩ, -, -, -⟩ := h.hj_facts h1715 h415 hJ
  obtain ⟨d, r₀, hdAL, hd1, hd3c, hr₀, hr₀d⟩ := h.toSec17W.exists_d_r h1715 h1721 h415
  have hQ := h.mem_qStar_G
  have hr₀L : r₀ ∈ L := (Subgroup.mem_inf.mp hr₀).1
  have hr₀N : r₀ ∈ Subgroup.normalizer ((A ⊔ Subgroup.zpowers w : Subgroup G) : Set G) :=
    (Subgroup.mem_inf.mp hr₀).2
  have hr₀C : r₀ ∈ Subgroup.centralizer ({c} : Set G) := h.le_centralizer_c hr₀L
  have hr₀c : r₀ * c * r₀⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hr₀C, mul_inv_cancel_right]
  have hr₀H : r₀ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hr₀C
  have hAwQ : A ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le h.le_normalizer_Q (Subgroup.zpowers_le.mpr h.w_normalizes_Q)
  have hAQr : A ≤ Subgroup.normalizer
      ((Q.map (MulAut.conj r₀).toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    calc A ≤ A ⊔ Subgroup.zpowers w := le_sup_left
      _ = (A ⊔ Subgroup.zpowers w).map (MulAut.conj r₀).toMonoidHom :=
          (Late.map_conj_eq_of_mem_normalizer hr₀N).symm
      _ ≤ _ := Subgroup.map_mono hAwQ
  have hQr : Q.map (MulAut.conj r₀).toMonoidHom ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_map_mulEquiv (MulAut.conj r₀) hQ.prop.1.1.1.2.1, hAQr⟩
  have hQr' := (h176 G A c L h.toSec15R hΩ).2 Q hQ.prop.1.1 hJ d hdAL.1 hd1 hd3c r₀
    (Subgroup.mem_inf.mpr ⟨hr₀H, mem_normalizer_closure_pair hr₀c hr₀d⟩) hQr
  have hQrπ : Q.map (MulAut.conj r₀).toMonoidHom ∈ scriptQPi A (lB A) ⊤ (piOf p) :=
    ⟨⟨hQr', le_top⟩, isPiSubgroup_map_mulEquiv (MulAut.conj r₀) h.isPiSubgroup_Q⟩
  obtain ⟨Q'', hle, hQ''⟩ :=
    Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf p))) hQrπ
  obtain ⟨x, hx, hxQ⟩ := htr Q hQ Q'' hQ''
  have hcard : Nat.card Q'' ≤ Nat.card (Q.map (MulAut.conj r₀).toMonoidHom) := by
    rw [hxQ, Subgroup.card_map_of_injective (MulAut.conj x).injective,
      Subgroup.card_map_of_injective (MulAut.conj r₀).injective]
  have heq : Q.map (MulAut.conj r₀).toMonoidHom = Q.map (MulAut.conj x).toMonoidHom :=
    (Subgroup.eq_of_le_of_card_ge hle hcard).trans hxQ
  refine ⟨d, x⁻¹ * r₀,
    { toSec17S := h
      d_mem := hdAL
      d_ne_one := hd1
      d_threeCentral := hd3c
      r_normalizes_Q := inv_mul_mem_normalizer_of_map_conj_eq heq.symm
      r_origin := ⟨x, hx, ?_, ?_⟩ }⟩
  · rw [mul_inv_cancel_left]
    exact hr₀
  · rw [mul_inv_cancel_left]
    exact hr₀d

end Proof1724N

theorem para1724_ofN (h1724 : Item1724N) : Para1724 := fun G _ _ A c L Y₀ Y₁ S p P w Q h =>
  Proof1724N.para1724_at h (h1724 G A c L Y₀ Y₁ S p P w Q h).1

theorem para1726_ofN (h415 : Sec4.Item4_15) (h1715 : Item1715) (h1721 : Item1721)
    (h1724 : Item1724N)
    (h176 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item176 A (lB A) c L) :
    Para1726 := fun G _ _ A c L Y₀ Y₁ S p P w Q _ h =>
  Proof1724N.para1726_at h415 h1715 h1721 h176 h (h1724 G A c L Y₀ Y₁ S p P w Q h.toSec17W).1

end CFSG.RankThree.PartTwo.Sec17
