module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenData
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenModA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenModB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenModC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
import CFSG.Quasithin.Background.E6TwentyTwoA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaDefs
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem omSevenX_four_le_mParam_of_quot_aut {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal) (hF : Fstar Y = L)
    (hLq : CFSG.IsQuasisimple ↥L) (hO2 : O2Trivial L)
    (h : ∀ (t : MulAut W) (htY : t ∈ Y) (ht : orderOf t = 2)
      (σ : MulAut ↥L) (σ' : MulAut (↥L ⧸ center ↥L))
      (_hσ : ∀ l : ↥L, ((σ l : ↥L) : MulAut W) = t * l * t⁻¹)
      (_hσ' : ∀ l : ↥L, σ' (l : ↥L ⧸ center ↥L) = ((σ l : ↥L) : ↥L ⧸ center ↥L))
      (_hord : orderOf σ' = 2), 4 ≤ rkIdx (fixV (zpowers t))) :
    4 ≤ E3.mParam Y := by
  have hY : ∃ t ∈ Y, orderOf t = 2 := by
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2
      ((E6.two_dvd_card_of_isQuasisimple hLq).trans (Subgroup.card_dvd_of_le hLY))
    exact ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht⟩
  refine SevenFour.le_mParam_of_forall hY ?_
  intro t htY ht
  obtain ⟨σ, σ', hσ, hσ', hord⟩ := exists_quotAut_of_involution hLY hLn hF hLq hO2 htY ht
  exact h t htY ht σ σ' hσ hσ' hord

theorem omegaSevenCover_of_data (hD : OmegaSevenInvolData) : OmegaSevenCover := by
  intro W _ _ hW Y L hLY hLn hF hLq hO2 hmodel hZ3
  refine omSevenX_four_le_mParam_of_quot_aut hLY hLn hF hLq hO2 ?_
  intro t _htY ht σ σ' hσ hσ' hord
  classical
  obtain ⟨z0, hz0_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥L)) 3
      (by rw [hZ3])
  let z : ↥L := (z0 : ↥L)
  have hz_mem : z ∈ Subgroup.center ↥L := z0.2
  have hz3_order : orderOf z = 3 := (Subgroup.orderOf_coe z0).trans hz0_order
  let zA : MulAut W := (z : MulAut W)
  have hzA3 : orderOf zA = 3 := (Subgroup.orderOf_coe z).trans hz3_order
  have hzA3pow : zA ^ 3 = 1 := by
    rw [← hzA3]
    exact pow_orderOf_eq_one zA
  let U : Subgroup W := commSub ⊤ (Subgroup.zpowers zA)
  have hU16 : 16 ≤ rk ↥U :=
    sixteen_le_rk_commSub_center hW hLq hZ3 hz_mem hz3_order
      (three_pow_ten_dvd_card_of_model hmodel hZ3)
  have h_rk_le : rk ↥(commSub U (Subgroup.zpowers t)) ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    rw [rkIdx_fixV_zpowers, commV_eq_commSub]
    exact rk_mono (commSub_mono le_top le_rfl)
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hσz_mem : σ z ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := σ.surjective y
    calc σ y' * σ z = σ (y' * z) := (map_mul σ y' z).symm
      _ = σ (z * y') := by rw [Subgroup.mem_center_iff.mp hz_mem y']
      _ = σ z * σ y' := map_mul σ z y'
  have hσz_order : orderOf (σ z) = 3 := by
    rw [← hz3_order]
    exact MulEquiv.orderOf_eq σ z
  have hσz_eq : σ z = z ∨ σ z = z⁻¹ := by
    have hgen : Subgroup.zpowers z = center ↥L := by
      refine eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hz_mem) ?_
      simp [Nat.card_zpowers, hz3_order, hZ3]
    have hmem : σ z ∈ Subgroup.zpowers z := by
      rw [hgen]
      exact hσz_mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk3 : σ z = z ^ (k % (3 : ℤ)) := by
      calc σ z = z ^ k := hk.symm
        _ = z ^ (k % (3 : ℤ)) := by
          simp [← zpow_mod_orderOf z k, hz3_order]
    have hk_cases : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by
      have hk_nonneg : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
      have hk_lt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
      omega
    rcases hk_cases with hk0 | hk1 | hk2
    · exfalso
      have h : orderOf (σ z) = 1 := by rw [hk3, hk0]; simp
      omega
    · left
      rw [hk3, hk1]
      simp
    · right
      rw [hk3, hk2]
      have hz3pow : z ^ 3 = 1 := by rw [← hz3_order]; exact pow_orderOf_eq_one z
      have hz2 : z ^ (2 : ℤ) = z⁻¹ := by
        have h : z ^ (2 : ℤ) * z = 1 := by
          rw [← zpow_add_one]
          norm_num
          exact hz3pow
        exact eq_inv_of_mul_eq_one_left h
      rw [hz2]
  have hσz_fix : ((σ z : ↥L) : MulAut W) = t * zA * t⁻¹ := by
    simpa [zA] using hσ z
  rcases hσz_eq with hσz | hσz
  ·
    have htz : t * zA = zA * t := by
      have h := hσz_fix
      rw [hσz] at h
      have hz_eq : zA = t * zA * t⁻¹ := by simpa [zA] using h
      have ht_inv : t⁻¹ = t := by
        have h : t * t = 1 := by simpa [pow_two] using ht2
        exact inv_eq_of_mul_eq_one_right h
      calc t * zA = t * (t * zA * t⁻¹) := by
            conv_lhs => rw [hz_eq]
        _ = (t * t) * zA * t⁻¹ := by group
        _ = zA * t⁻¹ := by
          rw [show t * t = 1 by rw [← pow_two]; exact ht2]
          group
        _ = zA * t := by rw [ht_inv]
    have hperf : Group.IsPerfect ↥L := hLq.1
    have hker : (QuotientGroup.mk' (Subgroup.center ↥L)).ker = Subgroup.center ↥L :=
      QuotientGroup.ker_mk' (Subgroup.center ↥L)
    have hsurj : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥L)) :=
      QuotientGroup.mk'_surjective (Subgroup.center ↥L)
    have hker_le : (QuotientGroup.mk' (Subgroup.center ↥L)).ker ≤ Subgroup.center ↥L :=
      le_of_eq hker
    have hcomm_z : ∀ y : ↥L, ((y : MulAut W) * zA = zA * (y : MulAut W)) := by
      intro y
      have hy : (y : ↥L) * z = z * (y : ↥L) := Subgroup.mem_center_iff.mp hz_mem y
      simpa [zA, Subgroup.coe_mul] using congrArg (fun x : ↥L => ((x : MulAut W))) hy
    rcases hD (↥L ⧸ Subgroup.center ↥L) hmodel σ' hord with
        ⟨x, hx3, hxinv, hlc⟩ | ⟨g, τ, hτ, _hcomm, _hne, x, hx3, hxinv, hlc⟩
    ·
      obtain ⟨a, ha_x, hσa, ha_order⟩ :=
        exists_lift_inverted_of_center_three hz_mem hz3_order hZ3 hσz hσ' hx3 hxinv
      let aA : MulAut W := (a : MulAut W)
      have haA_pow3 : aA ^ 3 = 1 := by
        rw [← ha_order, ← Subgroup.orderOf_coe a]
        exact pow_orderOf_eq_one aA
      have hza : aA * zA = zA * aA := hcomm_z a
      obtain ⟨c, hca⟩ := hlc ↥L (QuotientGroup.mk' _) hsurj hker_le hperf
        (by rw [hker]; exact hZ3) a ha_x z (by rw [hker]; exact hz_mem)
      let cA : MulAut W := (c : MulAut W)
      have hcaA : cA * aA * cA⁻¹ = aA * zA := by
        have h := congrArg (fun x : ↥L => ((x : MulAut W))) hca
        simpa [aA, cA, zA, Subgroup.coe_mul, Subgroup.coe_inv] using h
      have hcz : cA * zA = zA * cA := hcomm_z c
      have hua : t * aA * t⁻¹ = aA⁻¹ := by
        have h := hσ a
        rw [hσa] at h
        simpa [aA, Subgroup.coe_inv] using h.symm
      have h3 := rk_commSub_le_three_mul_of_conjLift hW hzA3 haA_pow3 hza hcaA hcz htz hua
      have h6 : 6 ≤ rk ↥(commSub U (Subgroup.zpowers t)) := by
        dsimp [U] at hU16 ⊢
        omega
      omega
    ·
      obtain ⟨ĝ, hĝg⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) g
      let ĝA : MulAut W := (ĝ : MulAut W)
      have hĝA_z : ĝA * zA = zA * ĝA := by
        have hĝ_z : ĝ * z = z * ĝ := Subgroup.mem_center_iff.mp hz_mem ĝ
        simpa [ĝA, zA] using congrArg (fun x : ↥L => ((x : MulAut W))) hĝ_z
      let t' : MulAut W := ĝA * t * ĝA⁻¹
      let u : MulAut W := t * t'
      have ht'_z : t' * zA = zA * t' := by
        dsimp [t']
        calc ĝA * t * ĝA⁻¹ * zA = ĝA * t * (ĝA⁻¹ * zA) := by group
          _ = ĝA * t * (zA * ĝA⁻¹) := by
            rw [show ĝA⁻¹ * zA = zA * ĝA⁻¹ by
              exact (show Commute ĝA zA from hĝA_z).inv_left]
          _ = ĝA * (t * zA) * ĝA⁻¹ := by group
          _ = ĝA * (zA * t) * ĝA⁻¹ := by rw [htz]
          _ = (ĝA * zA) * t * ĝA⁻¹ := by group
          _ = (zA * ĝA) * t * ĝA⁻¹ := by rw [hĝA_z]
          _ = zA * (ĝA * t * ĝA⁻¹) := by group
      have hu_z : u * zA = zA * u := by
        dsimp [u]
        calc t * t' * zA = t * (t' * zA) := by group
          _ = t * (zA * t') := by rw [ht'_z]
          _ = (t * zA) * t' := by group
          _ = (zA * t) * t' := by rw [htz]
          _ = zA * (t * t') := by group
      let σu : MulAut ↥L := σ * MulAut.conj ĝ * σ * (MulAut.conj ĝ)⁻¹
      let σu' : MulAut (↥L ⧸ Subgroup.center ↥L) := σ' * τ
      have hσu_l : ∀ l : ↥L, ((σu l : ↥L) : MulAut W) = u * l * u⁻¹ := by
        intro l
        change ((σ (MulAut.conj ĝ (σ ((MulAut.conj ĝ)⁻¹ l))) : ↥L) : MulAut W) =
          u * (l : MulAut W) * u⁻¹
        rw [hσ (MulAut.conj ĝ (σ ((MulAut.conj ĝ)⁻¹ l)))]
        simp only [MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_mul,
          Subgroup.coe_inv]
        rw [hσ (ĝ⁻¹ * l * ĝ)]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        dsimp [u, t', ĝA]
        group
      have hσuz : σu z = z := by
        change σ (MulAut.conj ĝ (σ ((MulAut.conj ĝ)⁻¹ z))) = z
        rw [MulAut.conj_inv_apply]
        have h1 : ĝ⁻¹ * z * ĝ = z := by
          rw [Subgroup.mem_center_iff.mp hz_mem ĝ⁻¹]
          group
        rw [h1, hσz, MulAut.conj_apply]
        have h2 : ĝ * z * ĝ⁻¹ = z := by
          have hĝz : ĝ * z = z * ĝ := Subgroup.mem_center_iff.mp hz_mem ĝ
          rw [hĝz]
          group
        rw [h2, hσz]
      have hĝg' : (↑ĝ : ↥L ⧸ Subgroup.center ↥L) = g := by
        simpa using hĝg
      have hconj : ∀ l : ↥L, (MulAut.conj g) (l : ↥L ⧸ Subgroup.center ↥L) =
          ((MulAut.conj ĝ l : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by
        intro l
        rw [MulAut.conj_apply, MulAut.conj_apply, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, hĝg']
      have hconj_inv : ∀ l : ↥L, (MulAut.conj g)⁻¹ (l : ↥L ⧸ Subgroup.center ↥L) =
          (((MulAut.conj ĝ)⁻¹ l : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by
        intro l
        rw [MulAut.conj_inv_apply, MulAut.conj_inv_apply, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, hĝg']
      have hσu' : ∀ l : ↥L, σu' (l : ↥L ⧸ Subgroup.center ↥L) =
          ((σu l : ↥L) : ↥L ⧸ Subgroup.center ↥L) := by
        intro l
        dsimp [σu', σu]
        rw [hτ]
        simp only [MulAut.mul_apply]
        rw [hconj_inv, hσ', hconj, hσ']
        rfl
      obtain ⟨a, ha_x, hσa, ha_order⟩ :=
        exists_lift_inverted_of_center_three hz_mem hz3_order hZ3 hσuz hσu' hx3 hxinv
      let aA : MulAut W := (a : MulAut W)
      have haA_pow3 : aA ^ 3 = 1 := by
        rw [← ha_order, ← Subgroup.orderOf_coe a]
        exact pow_orderOf_eq_one aA
      have hza : aA * zA = zA * aA := hcomm_z a
      obtain ⟨c, hca⟩ := hlc ↥L (QuotientGroup.mk' _) hsurj hker_le hperf
        (by rw [hker]; exact hZ3) a ha_x z (by rw [hker]; exact hz_mem)
      let cA : MulAut W := (c : MulAut W)
      have hcaA : cA * aA * cA⁻¹ = aA * zA := by
        have h := congrArg (fun x : ↥L => ((x : MulAut W))) hca
        simpa [aA, cA, zA, Subgroup.coe_mul, Subgroup.coe_inv] using h
      have hcz : cA * zA = zA * cA := hcomm_z c
      have hua : u * aA * u⁻¹ = aA⁻¹ := by
        have h := hσu_l a
        rw [hσa] at h
        simpa [aA, Subgroup.coe_inv] using h.symm
      have h3u := rk_commSub_le_three_mul_of_conjLift hW hzA3 haA_pow3 hza hcaA hcz hu_z hua
      have hstab_t : ∀ w ∈ U, t w ∈ U := by
        intro w hw
        exact apply_mem_commSub_of_commute htz hw
      have hstab_t' : ∀ w ∈ U, t' w ∈ U := by
        intro w hw
        exact apply_mem_commSub_of_commute ht'_z hw
      have hstab_ĝA : ∀ w ∈ U, ĝA w ∈ U := by
        intro w hw
        exact apply_mem_commSub_of_commute hĝA_z hw
      have hstab_ĝA_inv : ∀ w ∈ U, ĝA⁻¹ w ∈ U := by
        intro w hw
        have hĝAinv_z : ĝA⁻¹ * zA = zA * ĝA⁻¹ := by
          have hcomm : Commute ĝA zA := hĝA_z
          exact hcomm.inv_left
        exact apply_mem_commSub_of_commute hĝAinv_z hw
      have hsup := commSub_zpowers_mul_le (U := U) (t := t) (t' := t') hstab_t hstab_t'
      have hsup_rk : rk ↥(commSub U (Subgroup.zpowers u)) ≤
          rk ↥(commSub U (Subgroup.zpowers t)) + rk ↥(commSub U (Subgroup.zpowers t')) := by
        have h := rk_mono hsup
        have h_eq := rk_sup_add_rk_inf (commSub U (Subgroup.zpowers t))
          (commSub U (Subgroup.zpowers t'))
        dsimp [u]
        omega
      have hconj_rk := rk_commSub_zpowers_conj_of_stable (U := U) (g := ĝA) (t := t)
        hstab_ĝA hstab_ĝA_inv
      have h3_le : 3 ≤ rk ↥(commSub U (Subgroup.zpowers t)) := by
        have h := h3u.trans (Nat.mul_le_mul_left 3 hsup_rk)
        rw [hconj_rk] at h
        change rk ↥(commSub ⊤ (Subgroup.zpowers zA)) ≤
          3 * (rk ↥(commSub (commSub ⊤ (Subgroup.zpowers zA)) (Subgroup.zpowers t)) +
            rk ↥(commSub (commSub ⊤ (Subgroup.zpowers zA)) (Subgroup.zpowers t))) at h
        change 16 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers zA)) at hU16
        change 3 ≤ rk ↥(commSub (commSub ⊤ (Subgroup.zpowers zA)) (Subgroup.zpowers t))
        omega
      have heven : Even (rk ↥(commSub U (Subgroup.zpowers t))) :=
        even_rk_commSub_of_commute hW hzA3 htz
      have h4 : 4 ≤ rk ↥(commSub U (Subgroup.zpowers t)) := by
        rcases heven with ⟨k, hk⟩
        omega
      exact le_trans h4 h_rk_le
  ·
    have htz : t * zA * t⁻¹ = zA⁻¹ := by
      rw [← hσz_fix, hσz]
      simp [zA]
    have hA := rk_commSub_le_two_mul_rkIdx_of_inverts hW hzA3 ht2 htz
    change 16 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers zA)) at hU16
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
