module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8PBA2AAA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABFA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_involution_centralizes_seven
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
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {τ κ : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hτM : τ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hτN : τ ∉ Subgroup.normalizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _))
    (hτ2 : τ ^ 2 = 1)
    (hτZ : τ ∈ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (hκM : κ ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hκL : κ ∈ Subgroup.centralizer ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _))
    (hκB : κ ∈ Subgroup.centralizer
      ((barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) : Subgroup _) : Set _))
    (hκ7 : orderOf κ = 7) (hκW : κ ∉ centSub (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))) :
    τ * κ = κ * τ := by
  have hκK : κ ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian :=
    ⟨⟨hκM, hκL⟩, hκB⟩
  have hκ'K : τ * κ * τ⁻¹ ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian :=
    s16h_sl28_tau_conj_kbar_two D S h hs2 hcomp hxM hxn hτM hτN hτ2 κ hκK
  have hpow := (s16h_sl28_kbar_two_abelian_exp_seven D S hσ hJP h hs2 ht ht2 ht1 htr
    hW hcomp hthin hZ hbad hrow hZ4 h7 hxM hxn).1
  have hμK : (τ * κ * τ⁻¹) * κ⁻¹ ∈ s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian :=
    (s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian).mul_mem hκ'K
      ((s16h_sl28_kbar_two D V L x h.hyp151.isElemAbelian).inv_mem hκK)
  have hμkbar : (τ * κ * τ⁻¹) * κ⁻¹ ∈ kBar D.M ⊥ V h.hyp151.isElemAbelian L := by
    unfold kBar
    exact hμK.1
  have hκZinv : κ⁻¹ ∈ Subgroup.centralizer
      ((lBar ⊥ V h.hyp151.isElemAbelian L : Subgroup _) : Set _) :=
    (Subgroup.centralizer _).inv_mem hκL
  have hagree := s16h_sl28_kappa_prime_agrees_on_ZT D S h hxM hxn hκL hτZ
  have hμfixZ : ∀ z ∈ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L),
      ((τ * κ * τ⁻¹) * κ⁻¹) z = z := by
    intro z hz
    have hz' := s16h_sl28_centralizer_stabilizes_commSub_fixV hκZinv z hz
    calc ((τ * κ * τ⁻¹) * κ⁻¹) z = (τ * κ * τ⁻¹) (κ⁻¹ z) := rfl
      _ = κ (κ⁻¹ z) := hagree (κ⁻¹ z) hz'
      _ = z := κ.apply_symm_apply z
  have hμW1 : (τ * κ * τ⁻¹) * κ⁻¹ ∈ centSub
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)) := by
    by_contra hc
    by_cases hμ1 : (τ * κ * τ⁻¹) * κ⁻¹ = 1
    · rw [hμ1] at hc
      exact hc (Subgroup.one_mem _)
    · have hμ7 : orderOf ((τ * κ * τ⁻¹) * κ⁻¹) = 7 := by
        have hdvd : orderOf ((τ * κ * τ⁻¹) * κ⁻¹) ∣ 7 :=
          orderOf_dvd_of_pow_eq_one (hpow _ hμK)
        rcases (show Nat.Prime 7 by norm_num).eq_one_or_self_of_dvd _ hdvd with h1 | h7'
        · exact absurd (orderOf_eq_one_iff.mp h1) hμ1
        · exact h7'
      exact (s16h_sl28_seven_kbar_faithful_on_Z D S hσ hJP h hs2 ht ht2 ht1 htr hW
        hcomp hthin hZ hbad hrow hZ4 h7 hμkbar hμ7 hc) (mem_centSub.mpr hμfixZ)
  have hττ : τ * τ = 1 := by rw [← pow_two]; exact hτ2
  have hμinv : τ * ((τ * κ * τ⁻¹) * κ⁻¹) * τ⁻¹ =
      ((τ * κ * τ⁻¹) * κ⁻¹)⁻¹ := by
    have h1 : τ * (τ * κ * τ⁻¹) * τ⁻¹ = κ := by
      rw [show τ * (τ * κ * τ⁻¹) * τ⁻¹ = (τ * τ) * κ * (τ⁻¹ * τ⁻¹) by group]
      rw [hττ, one_mul, ← mul_inv_rev, hττ, inv_one, mul_one]
    rw [show τ * ((τ * κ * τ⁻¹) * κ⁻¹) * τ⁻¹
          = (τ * (τ * κ * τ⁻¹) * τ⁻¹) * (τ * κ⁻¹ * τ⁻¹) by group, h1]
    rw [show τ * κ⁻¹ * τ⁻¹ = (τ * κ * τ⁻¹)⁻¹ by group]
    group
  obtain ⟨hWmap₁, -⟩ := s16h_sl28_tau_swaps_wTil D S h hs2 hcomp hxM hxn hτM hτN hτ2
  have hμW2 : (τ * κ * τ⁻¹) * κ⁻¹ ∈ centSub
      (wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) := by
    rw [mem_centSub]
    intro w hw
    obtain ⟨u, huW1, rfl⟩ := Subgroup.mem_map.mp (hWmap₁.symm ▸ hw)
    have hu : ((τ * κ * τ⁻¹) * κ⁻¹) u = u := (mem_centSub.mp hμW1) u huW1
    have hminv : ((τ * κ * τ⁻¹) * κ⁻¹)⁻¹ (τ u) = τ u := by
      calc ((τ * κ * τ⁻¹) * κ⁻¹)⁻¹ (τ u)
          = (τ * ((τ * κ * τ⁻¹) * κ⁻¹) * τ⁻¹) (τ u) := by rw [hμinv]
        _ = τ (((τ * κ * τ⁻¹) * κ⁻¹) (τ⁻¹ (τ u))) := rfl
        _ = τ (((τ * κ * τ⁻¹) * κ⁻¹) u) :=
            by rw [show τ⁻¹ (τ u) = u from τ.symm_apply_apply u]
        _ = τ u := by rw [hu]
    have happly : ((τ * κ * τ⁻¹) * κ⁻¹) (τ u) = τ u := by
      rw [← congrArg ((τ * κ * τ⁻¹) * κ⁻¹) hminv]
      exact ((τ * κ * τ⁻¹) * κ⁻¹).apply_symm_apply (τ u)
    exact happly
  have hμeq1 : (τ * κ * τ⁻¹) * κ⁻¹ = 1 := by
    have hsup := s16h_sl28_wTil_sup_conj_eq_top D S h hs2 ht hW hcomp hxM hxn
    have hfix : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊔
        wTil ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) ≤
        fixV (Subgroup.zpowers ((τ * κ * τ⁻¹) * κ⁻¹)) :=
      sup_le (fun z hz => mem_fixV_zpowers_iff_apply.mpr ((mem_centSub.mp hμW1) z hz))
        (fun z hz => mem_fixV_zpowers_iff_apply.mpr ((mem_centSub.mp hμW2) z hz))
    have htop : (⊤ : Subgroup (Vtil ⊥ V h.hyp151.isElemAbelian)) ≤
        fixV (Subgroup.zpowers ((τ * κ * τ⁻¹) * κ⁻¹)) := by
      rw [← hsup]; exact hfix
    refine MulEquiv.ext fun v => ?_
    simpa using mem_fixV_zpowers_iff_apply.mp (htop (Subgroup.mem_top v))
  have hκ'eq : τ * κ * τ⁻¹ = κ := mul_inv_eq_one.mp hμeq1
  calc τ * κ = τ * κ * τ⁻¹ * τ := by group
    _ = κ * τ := by rw [hκ'eq]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
