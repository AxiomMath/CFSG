module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Base
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
import CFSG.GH74.Orders.LieType

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

private theorem w107_not_sq_dvd_u43 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
  intro h
  have hpdvd : p ∣ 2 ^ 7 * 3 ^ 6 * 5 * 7 := (dvd_pow_self p (by norm_num)).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h1 | h7
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h23 | h5
    · rcases (Nat.Prime.dvd_mul hp).1 h23 with h2 | h3
      · have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · have hp5' : p = 5 := le_antisymm (Nat.le_of_dvd (by norm_num) h5) hp5
      subst hp5'
      norm_num at h
  · have hp7 : p ≤ 7 := Nat.le_of_dvd (by norm_num) h7
    rcases (by omega : p = 5 ∨ p = 6 ∨ p = 7) with rfl | rfl | rfl
    · norm_num at h
    · norm_num at hp
    · norm_num at h

theorem w107_not_dvd_card_center {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    (h : LieModel (L ⧸ Subgroup.center L) .PSU 4 3 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Subgroup.center L) := by
  intro hpdvd
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsPerfect L := hq.1
  have hcardS : Nat.card (L ⧸ Subgroup.center L) = 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
    rw [CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1)
      (by norm_num) (by norm_num) h]
    decide
  let f : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hker : f.ker = Subgroup.center L := QuotientGroup.ker_mk' _
  have hcent : f.ker ≤ Subgroup.center L := le_of_eq hker
  have : Finite (L ⧸ Subgroup.center L) := Finite.of_surjective f hsurj
  obtain ⟨C⟩ : Nonempty (Sylow p f.ker) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow p (L ⧸ Subgroup.center L)) := inferInstance
  have hcyc : IsCyclic (Q : Subgroup (L ⧸ Subgroup.center L)) := by
    have hQcard : Nat.card (Q : Subgroup (L ⧸ Subgroup.center L)) =
        p ^ (Nat.card (L ⧸ Subgroup.center L)).factorization p := Q.card_eq_multiplicity
    rw [hcardS] at hQcard
    have hfac : (2 ^ 7 * 3 ^ 6 * 5 * 7).factorization p ≤ 1 := by
      by_contra hlt
      have h2 : 2 ≤ (2 ^ 7 * 3 ^ 6 * 5 * 7).factorization p :=
        Nat.succ_le_of_lt (not_le.1 hlt)
      exact w107_not_sq_dvd_u43 hp hp5
        ((hp.pow_dvd_iff_le_factorization (by norm_num)).mpr h2)
    refine isCyclic_of_card_dvd_prime (p := p) ?_
    rw [hQcard]
    simpa using (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mpr hfac
  have hCbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot
    f hsurj hcent C Q hcyc
  exact (Sylow.ne_bot_of_dvd_card C (by rw [hker]; exact hpdvd)) hCbot

theorem w107_card_center_eq_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L : Subgroup (MulAut W)} (hctx : Is135Context Y L)
    (hU : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1) (hZ : Subgroup.center ↥L ≠ ⊥)
    {t : MulAut W} (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (hcomm : ∀ z ∈ Subgroup.center ↥L, t * (z : MulAut W) = (z : MulAut W) * t) :
    Nat.card (Subgroup.center ↥L) = 3 := by
  let U : Subgroup W := commSub (⊤ : Subgroup W) (Subgroup.zpowers t)
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hfix : (⊤ : Subgroup W) ≤ fixV (Subgroup.zpowers t) := commSub_eq_bot_iff.mp hbot
    have ht1 : t = 1 := by
      ext w
      exact (mem_fixV.mp (hfix (Subgroup.mem_top w))) t (Subgroup.mem_zpowers t)
    rw [ht1, orderOf_one] at ht2
    norm_num at ht2
  have hcardU : Nat.card U ≤ 8 := by
    calc Nat.card U = 2 ^ rk U := card_eq_two_pow hW U
      _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (w107_rk_commSub_zpowers_le_three hm)
      _ = 8 := by norm_num
  have hstab : StableUnder ((Subgroup.center ↥L).map L.subtype) U := by
    refine stableUnder_commSub (H := (Subgroup.center ↥L).map L.subtype)
      (X := Subgroup.zpowers t) ?_ (fun _ _ _ _ => Subgroup.mem_top _)
    intro h hh x hx
    rw [Subgroup.mem_map] at hh
    obtain ⟨z, hz, rfl⟩ := hh
    have hcz : t * (z : MulAut W) = (z : MulAut W) * t := hcomm z hz
    have hconj : L.subtype z * t * (L.subtype z)⁻¹ = t := by
      change (z : MulAut W) * t * (z : MulAut W)⁻¹ = t
      rw [← hcz, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hconj]
    exact Subgroup.zpow_mem_zpowers t k
  obtain ⟨u, huU, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra h
    apply hUne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  let κ : ↥(Subgroup.center ↥L) →* MulAut W := L.subtype.comp (Subgroup.center ↥L).subtype
  let F : ↥(Subgroup.center ↥L) → ↥U := fun z =>
    ⟨κ z u, hstab (κ z) (Subgroup.mem_map.mpr ⟨(z : ↥L), z.2, rfl⟩) u huU⟩
  have hFne : ∀ z : ↥(Subgroup.center ↥L), F z ≠ 1 := by
    intro z hz1
    have hval : κ z u = 1 := congrArg Subtype.val hz1
    refine hu1 ?_
    calc u = (κ z)⁻¹ (κ z u) := (MulAut.inv_apply_self W (κ z) u).symm
      _ = (κ z)⁻¹ 1 := by rw [hval]
      _ = 1 := map_one _
  have hFinj : Function.Injective F := by
    intro z z' h
    have heq : κ z u = κ z' u := congrArg Subtype.val h
    by_contra hne
    have hw1 : (z'⁻¹ * z : ↥(Subgroup.center ↥L)) ≠ 1 := by
      intro h1
      apply hne
      have h2 := congrArg (fun w : ↥(Subgroup.center ↥L) => z' * w) h1
      simpa using h2
    have hw1' : (((z'⁻¹ * z : ↥(Subgroup.center ↥L)) : ↥L)) ≠ 1 := by
      intro h1
      exact hw1 (Subtype.ext h1)
    have hufix : u ∈ fixV (Subgroup.zpowers
        (((z'⁻¹ * z : ↥(Subgroup.center ↥L)) : ↥L) : MulAut W)) := by
      rw [mem_fixV_zpowers_iff]
      change κ (z'⁻¹ * z) u = u
      rw [map_mul, map_inv, MulAut.mul_apply, heq, MulAut.inv_apply_self]
    have hbot := w107_fixV_center_eq_bot hctx
      (z := ((z'⁻¹ * z : ↥(Subgroup.center ↥L)) : ↥L)) (z'⁻¹ * z).2 hw1'
    rw [hbot] at hufix
    exact hu1 (Subgroup.mem_bot.mp hufix)
  have hlt : Nat.card (Subgroup.center ↥L) < Nat.card U := by
    have : Fintype ↥(Subgroup.center ↥L) := Fintype.ofFinite _
    have : Fintype ↥U := Fintype.ofFinite _
    have hstrict := Fintype.card_lt_of_injective_of_notMem F hFinj
      (b := (⟨1, U.one_mem⟩ : ↥U)) (by rintro ⟨z, hz⟩; exact hFne z hz)
    simpa only [Nat.card_eq_fintype_card] using hstrict
  have hle7 : Nat.card (Subgroup.center ↥L) ≤ 7 := by omega
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := w135_odd_card_center hctx
  have hgt : 1 < Nat.card (Subgroup.center ↥L) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
  have hq : CFSG.IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hnot5 : ¬ 5 ∣ Nat.card (Subgroup.center ↥L) :=
    w107_not_dvd_card_center hq hU Nat.prime_five (by norm_num)
  have hnot7 : ¬ 7 ∣ Nat.card (Subgroup.center ↥L) :=
    w107_not_dvd_card_center hq hU Nat.prime_seven (by norm_num)
  obtain ⟨k, hk⟩ := hodd
  have hk13 : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk13 with rfl | rfl | rfl
  · omega
  · exfalso
    exact hnot5 (by rw [hk]; norm_num)
  · exfalso
    exact hnot7 (by rw [hk]; norm_num)

end CFSG.LocalAnalysis.WeakClosure81
