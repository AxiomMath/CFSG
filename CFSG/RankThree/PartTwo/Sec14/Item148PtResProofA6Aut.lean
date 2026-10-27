module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6Data
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltSixAut
import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148PtRes

open Equiv Equiv.Perm
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification

theorem cA_eq_vecPerm2 :
    Item148HJ.cA = Sec4.Item434AltPerm.vecPerm2 6 ![1, 0] := by
  decide

theorem cB_eq_vecPerm2 :
    Item148HJ.cB = Sec4.Item434AltPerm.vecPerm2 6 ![1, 1] := by
  decide

theorem vecPerm2_six_pow_three :
    ∀ w : Fin 2 → ZMod 3, Sec4.Item434AltPerm.vecPerm2 6 w ^ 3 = 1 := by
  decide +kernel

theorem pow_three_eq_one_of_commute_six {x g : Perm (Fin 6)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hg : sign g = 1) (hgx : g * x = x * g) : g ^ 3 = 1 := by
  obtain ⟨σ, hσ⟩ := Item148HJ.exists_conj_eq_rep hx3 hx1
  set g' := σ * g * σ⁻¹ with hg'def
  have hg' : sign g' = 1 := by
    rw [hg'def, Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, hg, mul_one, Int.units_mul_self]
  have hcomm : g' * (σ * x * σ⁻¹) = (σ * x * σ⁻¹) * g' := by
    rw [hg'def]
    calc σ * g * σ⁻¹ * (σ * x * σ⁻¹) = σ * (g * x) * σ⁻¹ := by group
      _ = σ * (x * g) * σ⁻¹ := by rw [hgx]
      _ = σ * x * σ⁻¹ * (σ * g * σ⁻¹) := by group
  have hg'3 : g' ^ 3 = 1 := by
    rcases hσ with h | h
    · rw [h, cA_eq_vecPerm2] at hcomm
      obtain ⟨w, hw⟩ := Sec4.Item434AltPerm.centralizer_vecPerm2_six ![1, 0] (by decide) g' hg'
        hcomm
      rw [← hw]
      exact vecPerm2_six_pow_three w
    · rw [h, cB_eq_vecPerm2] at hcomm
      obtain ⟨w, hw⟩ := Sec4.Item434AltPerm.centralizer_vecPerm2_six ![1, 1] (by decide) g' hg'
        hcomm
      rw [← hw]
      exact vecPerm2_six_pow_three w
  have hconj : g' ^ 3 = σ * g ^ 3 * σ⁻¹ := by
    rw [hg'def, conj_pow]
  rw [hconj] at hg'3
  have : g ^ 3 = σ⁻¹ * (σ * g ^ 3 * σ⁻¹) * σ := by group
  rw [this, hg'3, mul_one, inv_mul_cancel]

theorem card_perm_fin_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem two_dvd_card_outer_six : 2 ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := by
  have h1 : Nat.card (MulAut (alternatingGroup (Fin 6))) =
      Nat.card (Outer (alternatingGroup (Fin 6))) * 360 := by
    rw [← CatalogueSchreierAlternating.DegreeSix.inner_card]
    exact (inner (alternatingGroup (Fin 6))).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card (CFSG.Quasithin.SteinbergCB.conjPerm 6).range = 720 := by
    rw [← card_perm_fin_six]
    exact Nat.card_congr (MonoidHom.ofInjective
      (CFSG.Quasithin.SteinbergCB.conjPerm_injective (n := 6) (by norm_num))).toEquiv.symm
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  have h3 := Subgroup.card_subgroup_dvd_card (CFSG.Quasithin.SteinbergCB.conjPerm 6).range
  rw [h2, h1] at h3
  obtain ⟨k, hk⟩ := h3
  generalize Nat.card (Outer (alternatingGroup (Fin 6))) = n at hk ⊢
  exact ⟨k, by omega⟩

theorem mem_inner_of_pow_three {τ : MulAut (alternatingGroup (Fin 6))} (hτ : τ ^ 3 = 1) :
    τ ∈ inner (alternatingGroup (Fin 6)) := by
  have : Finite (MulAut (alternatingGroup (Fin 6))) := MulEquiv.finite_left
  set o : Outer (alternatingGroup (Fin 6)) := QuotientGroup.mk τ with ho
  have ho3 : o ^ 3 = 1 := by rw [ho, ← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
  have hdvd3 : orderOf o ∣ 3 := orderOf_dvd_of_pow_eq_one ho3
  have hdvdO : orderOf o ∣ Nat.card (Outer (alternatingGroup (Fin 6))) := orderOf_dvd_natCard o
  have hle := CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have h2 := two_dvd_card_outer_six
  have hpos : 0 < Nat.card (Outer (alternatingGroup (Fin 6))) := Nat.card_pos
  have hord : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact h
    · exfalso
      rw [h] at hdvdO
      obtain ⟨k, hk⟩ := hdvdO
      obtain ⟨m, hm⟩ := h2
      generalize Nat.card (Outer (alternatingGroup (Fin 6))) = n at hk hm hle hpos
      omega
  have ho1 : o = 1 := orderOf_eq_one_iff.mp hord
  rw [ho, QuotientGroup.eq_one_iff] at ho1
  exact ho1

theorem eq_one_of_fixed_alternating_six {τ : MulAut (alternatingGroup (Fin 6))}
    (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : alternatingGroup (Fin 6)} (hg : τ g = g) {k : ℕ}
    (hgk : g ^ k = 1) (hk3 : Nat.Coprime k 3) : g = 1 := by
  obtain ⟨h, rfl⟩ := mem_inner_of_pow_three hτ3
  have hinj := CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
  have hh3 : h ^ 3 = 1 := hinj (by rw [map_pow, hτ3, map_one])
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hτ1 (map_one _)
  have hgh : g * h = h * g := by
    have h1 : h * g * h⁻¹ = g := hg
    calc g * h = h * g * h⁻¹ * h := by rw [h1]
      _ = h * g := by group
  have hx3 : (h : Perm (Fin 6)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3, Subgroup.coe_one]
  have hx1 : (h : Perm (Fin 6)) ≠ 1 := fun he => hh1 (Subtype.ext he)
  have hgx : (g : Perm (Fin 6)) * h = h * g := congrArg Subtype.val hgh
  have hg3 : (g : Perm (Fin 6)) ^ 3 = 1 :=
    pow_three_eq_one_of_commute_six hx3 hx1 (mem_alternatingGroup.mp g.2) hgx
  have hg3' : g ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hg3, Subgroup.coe_one])
  have hd : orderOf g ∣ Nat.gcd k 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgk) (orderOf_dvd_of_pow_eq_one hg3')
  rw [hk3, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

theorem eq_one_of_fixed_tripleCover {T : Type*} [Group T] [Group.IsPerfect T]
    (hZ : Nat.card (Subgroup.center T) = 3)
    (e : T ⧸ Subgroup.center T ≃* alternatingGroup (Fin 6)) {σ : MulAut T} (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1) {t : T} (ht : σ t = t) {k : ℕ} (htk : t ^ k = 1) (hk3 : Nat.Coprime k 3) :
    t = 1 := by
  set σbar := PerfectAutomorphisms.centerQuotientHom T σ with hσbar
  set τ : MulAut (alternatingGroup (Fin 6)) := MulAut.congr e σbar with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, hσbar, ← map_pow, ← map_pow, hσ3, map_one, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h1
    apply hσ1
    have h2 : σbar = 1 := (MulAut.congr e).injective (h1.trans (map_one _).symm)
    exact PerfectAutomorphisms.centerQuotientHom_injective T (h2.trans (map_one _).symm)
  set x := e (QuotientGroup.mk' (Subgroup.center T) t) with hx
  have hxfix : τ x = x := by
    have h1 : τ x = e (σbar (QuotientGroup.mk' (Subgroup.center T) t)) := by
      rw [hτ, hx]
      simp [MulAut.congr_apply]
    rw [h1, hσbar]
    change e (PerfectAutomorphisms.onCenterQuotient σ _) = _
    rw [PerfectAutomorphisms.onCenterQuotient_apply_mk, ht]
  have hxk : x ^ k = 1 := by
    rw [hx, ← map_pow, ← map_pow, htk, map_one, map_one]
  have hx1 := eq_one_of_fixed_alternating_six hτ3 hτ1 hxfix hxk hk3
  have htZ : t ∈ Subgroup.center T := by
    have h1 : QuotientGroup.mk' (Subgroup.center T) t = 1 :=
      e.injective (hx1.trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff t).mp h1
  have : Finite (Subgroup.center T) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have ht3 : orderOf t ∣ 3 := by
    have h1 := Subgroup.orderOf_dvd_natCard (Subgroup.center T) htZ
    rwa [hZ] at h1
  have hd : orderOf t ∣ Nat.gcd k 3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one htk) ht3
  rw [hk3, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

end CFSG.RankThree.PartTwo.Sec14.Item148PtRes
