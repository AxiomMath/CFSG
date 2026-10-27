module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfRows
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_exists_order_seven_fpf
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig) :
    ∃ d : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian),
      d ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian ∧ orderOf d = 7 ∧
      (∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
          fixV (lBar ⊥ V h.hyp151.isElemAbelian L), d z = z → z = 1) := by
  let Z : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian) :=
    commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)
  obtain ⟨d, hdM, hd7, hdstab, hdnt⟩ :=
    s16h_sl28_seven_scalar_exists D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 h7
  refine ⟨d, hdM, hd7, ?_⟩
  have hZ2 : ∀ z : ↥Z, z ^ 2 = 1 := by
    intro z
    apply Subtype.ext
    simpa using s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian
      (z : Vtil ⊥ V h.hyp151.isElemAbelian)
  have hZpow : Nat.card ↥Z = 2 ^ rk ↥Z :=
    CFSG.Quasithin.card_eq_two_pow (s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian) Z
  have hZk : rk ↥Z ≤ 3 := by
    have hrow3 := s16fh_row_SL2_three (W := Vtil ⊥ V h.hyp151.isElemAbelian)
      (s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian) hrow
    obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hrow.2
    have hdim := s16fh_rk_of_realizes_nat (W := Vtil ⊥ V h.hyp151.isElemAbelian)
      (K := K) (d := 2) (a := 3) hKcard hreal
    have hrow3' : 3 * rk ↥Z ≤
        rk ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)) := hrow3
    omega
  have hZle : Nat.card ↥Z ≤ 8 := by
    rw [hZpow]
    calc 2 ^ rk ↥Z ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hZk
      _ = 8 := by norm_num
  let φ : MulAut ↥Z := CFSG.Quasithin.resAut Z ⟨d, hdstab⟩
  have hφapply : ∀ u : ↥Z, (φ u : Vtil ⊥ V h.hyp151.isElemAbelian) = d u := by
    intro u
    change ((CFSG.Quasithin.resHom Z ⟨d, hdstab⟩) u :
      Vtil ⊥ V h.hyp151.isElemAbelian) = d u
    exact CFSG.Quasithin.resHom_apply Z ⟨d, hdstab⟩ u
  have hg7 : (⟨d, hdstab⟩ : stabSub Z) ^ 7 = 1 := by
    apply Subtype.ext
    show d ^ 7 = 1
    rw [← hd7]
    exact pow_orderOf_eq_one d
  have hφpow : φ ^ 7 = 1 := by
    change (CFSG.Quasithin.resHom Z ⟨d, hdstab⟩) ^ 7 = 1
    rw [← map_pow, hg7, map_one]
  have hne1 : φ ≠ 1 := by
    intro hφ1
    apply hdnt
    rw [mem_centSub]
    intro z hz
    have h := congrArg (fun w : ↥Z => (w : Vtil ⊥ V h.hyp151.isElemAbelian))
      (congrArg (fun ψ : MulAut ↥Z => ψ ⟨z, hz⟩) hφ1)
    rw [hφapply] at h
    simpa using h
  have hφ7 : orderOf φ = 7 := by
    have hdvd : orderOf φ ∣ 7 := orderOf_dvd_of_pow_eq_one hφpow
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne1
    · exact h
  have hfpf := s16h_fpf_of_orderOf_seven_card_le_eight hZ2 hZle hφ7
  show ∀ z ∈ Z, d z = z → z = 1
  intro z hz hfix
  have hφz : φ ⟨z, hz⟩ = ⟨z, hz⟩ := by
    apply Subtype.ext
    show d z = z
    exact hfix
  simpa using congrArg Subtype.val (hfpf ⟨z, hz⟩ hφz)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
