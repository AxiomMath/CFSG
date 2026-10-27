module

public import CFSG.LocalAnalysis.WeakClosure81.W16LU3OuterK
public import CFSG.LocalAnalysis.WeakClosure81.W16LU3OuterLift
public import CFSG.LocalAnalysis.WeakClosure81.W16LU3OuterDict

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.GH74.Uniqueness.Bender
open Subgroup

theorem psuThreeOuterInvolutionInput_holds :
    PSUThreeOuterInvolutionInput := by
  intro X _ _ n hperf hPSU hZ Y hY hYc α hα hαY hnot
  haveI hperfX : Group.IsPerfect X := ⟨hperf⟩
  have hX : IsU3Shape X n := ⟨hperf, hPSU, hZ⟩
  have hZodd : Odd (Nat.card (Subgroup.center X)) :=
    Odd.of_dvd_nat (by norm_num) hZ
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hB : BenderType (X ⧸ Subgroup.center X) n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.benderType_of_lieModel_PSU3 hPSU
  obtain ⟨Q, Qh, hQ1, hQh2, hQh3, hQC, hCN, hcentralizes, hliftαQ⟩ :=
    hX.exists_lift_data hY hYc
  let αbar : MulAut (X ⧸ Subgroup.center X) :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X α
  have hαbar_sq : αbar * αbar = 1 := by
    change CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X α *
      CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X α = 1
    rw [← map_mul, hα, map_one]
  have hαbar_fix : ∀ z ∈ rootCenter (Q : Subgroup (X ⧸ Subgroup.center X)), αbar z = z := by
    intro z hz
    rw [hQ1] at hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    rw [← hyz]
    change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
      ((QuotientGroup.mk' (Subgroup.center X)) y) =
        (QuotientGroup.mk' (Subgroup.center X)) y
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
      hαY y hy]
  rcases BenderType.unitary_involution_dichotomy hB Q αbar hαbar_sq hαbar_fix with
    ⟨r, hr, hrα⟩ | hodd
  · rw [hQ1] at hr
    obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp hr
    have hconj : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom X
        (MulAut.conj y) = αbar := by
      rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
      rw [hyr, hrα]
    have hinj := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X
    exact (hnot y hy (hinj hconj).symm).elim
  · obtain ⟨x, hxC, hxo, hx1⟩ :=
      BenderType.exists_odd_ne_one_centralizer_rootCenter hB Q
    obtain ⟨c, hc_eq⟩ := hπsurj x
    have hcK : π c ∈ Subgroup.centralizer
        (rootCenter (Q : Subgroup (X ⧸ Subgroup.center X)) :
          Set (X ⧸ Subgroup.center X)) := by
      rw [hc_eq]; exact hxC
    have hcC : c ∈ Subgroup.centralizer (Y : Set X) := hcentralizes c hcK
    have hco : Odd (orderOf c) := by
      have hxpow : c ^ orderOf x ∈ Subgroup.center X := by
        rw [← QuotientGroup.eq_one_iff (N := Subgroup.center X)]
        change QuotientGroup.mk' (Subgroup.center X) (c ^ orderOf x) = 1
        rw [map_pow, hc_eq, pow_orderOf_eq_one]
      have hpow : (c ^ orderOf x) ^ Nat.card (Subgroup.center X) = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp
          (Subgroup.orderOf_dvd_natCard (Subgroup.center X) hxpow)
      have hdvd : orderOf c ∣ orderOf x * Nat.card (Subgroup.center X) :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_mul]; exact hpow)
      exact Odd.of_dvd_nat (hxo.mul hZodd) hdvd
    have hcZ : c ∉ Subgroup.center X := by
      intro hc
      have hx1' : x = 1 := by
        rw [← hc_eq]
        exact (QuotientGroup.eq_one_iff (N := Subgroup.center X) c).mpr hc
      exact hx1 hx1'
    have hoddx : αbar x * x ∈ (Q : Subgroup (X ⧸ Subgroup.center X)) := hodd x hxC hxo
    rw [← hQh3] at hoddx
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hoddx
    have hqa : π q = π (α c * c) := by
      rw [hqeq, ← hc_eq]
      change CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
        ((QuotientGroup.mk' (Subgroup.center X)) c) *
          (QuotientGroup.mk' (Subgroup.center X)) c =
        (QuotientGroup.mk' (Subgroup.center X)) (α c * c)
      rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
        ← map_mul]
    obtain ⟨z, hz, hzq⟩ := (QuotientGroup.mk'_eq_mk' (Subgroup.center X)).mp hqa
    exact w16l_exists_odd_subgroup_inverted Y α hα hαY hQh2 hZodd hQC hCN (hliftαQ α hαY)
      hcC hco hcZ ⟨q, hq, z, hz, hzq.symm⟩

end CFSG.LocalAnalysis.WeakClosure81

end
