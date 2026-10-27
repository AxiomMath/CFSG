module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFResidue
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFL34Inner
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFL34Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFL34Mat
public import CFSG.GH74.Generic.S45.LOut
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldFourCover
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourConjugacy

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

theorem input15338FinalL34_native : Input15338FinalL34 := by
  intro L₂ _ _ hq h34 U hU4 hUel ⟨y, hyN, hy3, u₁, hu₁, hmove⟩ u hu hu1 M hMfix hM3 _ x hx3 _ hxM
  classical
  have : Group.IsPerfect L₂ := hq.1
  have hLie : CFSG.Blueprint.LieModel (L₂ ⧸ Subgroup.center L₂) .PSL 3 2 2 :=
    Or.inl ⟨by decide, h34⟩
  have hodd := CFSG.GH74.Generic.S45.odd_card_commutator_outer_L34 hLie
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hLie
  have hk : Nat.card k = 4 := by
    rw [hcard]
    norm_num
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hsq : ∀ w ∈ U, w * w = 1 := fun w hw => by rw [← sq]; exact hUel.2 w hw
  have hyN' : ∀ w ∈ U, y * w * y⁻¹ ∈ U := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hyN w).mp hw
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  obtain ⟨g, hug⟩ := exists_conj_eq_of_commutator hodd hU4 hsq hyN' hy3' hu₁ hmove u hu
  have hggc : g * g ∈ Subgroup.center L₂ := by
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have h := congrArg (fun φ : MulAut L₂ => φ z) (hsq u hu)
    simp only [MulAut.mul_apply, hug, MulAut.conj_apply, MulAut.one_apply] at h
    calc z * (g * g) = (g * (g * z * g⁻¹) * g⁻¹) * (g * g) := by rw [h]
      _ = (g * g) * z := by group
  have hgc : g ∉ Subgroup.center L₂ := fun hg => hu1 (by
    rw [hug]
    ext z
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← Subgroup.mem_center_iff.mp hg z]
    group)
  have hp2 : (QuotientGroup.mk' (Subgroup.center L₂) g) * (QuotientGroup.mk' (Subgroup.center L₂) g)
      = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hggc
  have hp1 : QuotientGroup.mk' (Subgroup.center L₂) g ≠ 1 := fun h =>
    hgc ((QuotientGroup.eq_one_iff g).mp h)
  have hep2 : e (QuotientGroup.mk' (Subgroup.center L₂) g) *
      e (QuotientGroup.mk' (Subgroup.center L₂) g) = 1 := by
    rw [← map_mul, hp2, map_one]
  have hep1 : e (QuotientGroup.mk' (Subgroup.center L₂) g) ≠ 1 := fun h =>
    hp1 (e.injective (h.trans (map_one e).symm))
  obtain ⟨c₀, hc₀⟩ := exists_conj_eq_wP_one _ hep2 hep1
  let e' : (L₂ ⧸ Subgroup.center L₂) ≃* projectiveSL 3 k :=
    e.trans (MulAut.conj (proj 3 k c₀))
  have he'g : e' (QuotientGroup.mk' (Subgroup.center L₂) g) = wP 1 := by
    change (MulAut.conj (proj 3 k c₀)) (e (QuotientGroup.mk' (Subgroup.center L₂) g)) = wP 1
    rw [MulAut.conj_apply]
    exact hc₀
  let U0 : Subgroup (L₂ ⧸ Subgroup.center L₂) := (projUnitriangular 3 k).comap e'.toMonoidHom
  let Z0 : Subgroup (L₂ ⧸ Subgroup.center L₂) := (wSub k).comap e'.toMonoidHom
  have hU0 : ∀ s, s ∈ U0 ↔ e' s ∈ projUnitriangular 3 k := fun s => Iff.rfl
  have hZ0 : ∀ s, s ∈ Z0 ↔ e' s ∈ wSub k := fun s => Iff.rfl
  have hc : ∀ s ∈ U0, s * (g : L₂ ⧸ Subgroup.center L₂) = (g : L₂ ⧸ Subgroup.center L₂) * s := by
    intro s hs
    apply e'.injective
    rw [map_mul, map_mul]
    have h1 : e' (g : L₂ ⧸ Subgroup.center L₂) = wP 1 := he'g
    rw [h1]
    exact wP_one_comm hs
  have hsq' : ∀ s ∈ U0, s * s ∈ Z0 := fun s hs => by
    rw [hZ0, map_mul]
    exact sq_mem_wSub hs
  have hZ : ∀ z ∈ Z0, ∃ a ∈ U0, ∃ b ∈ U0, z = a * b * a⁻¹ * b⁻¹ := by
    intro z hz
    obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := exists_comm_of_mem_wSub hz
    refine ⟨e'.symm a₀, ?_, e'.symm b₀, ?_, ?_⟩
    · rw [hU0, e'.apply_symm_apply]
      exact ha₀
    · rw [hU0, e'.apply_symm_apply]
      exact hb₀
    · have hab' : e' z = a₀ * b₀ * a₀⁻¹ * b₀⁻¹ := hab
      apply e'.injective
      rw [hab']
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hΩ : Nat.card {z : Subgroup.center L₂ // z * z = 1} ≤ 4 := by
    have h := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_center_sq_eq_one_le_four L₂ hLie
    have hequiv : {z : Subgroup.center L₂ // z * z = 1} ≃
        {z : (QuotientGroup.mk' (Subgroup.center L₂)).ker // z ^ 2 = 1} :=
      Equiv.subtypeEquiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _).symm).toEquiv
        (fun z => by simp [sq, Subtype.ext_iff])
    rw [Nat.card_congr hequiv]
    exact h
  have hU0card : Nat.card U0 = 64 := by
    rw [show U0 = (projUnitriangular 3 k).map e'.symm.toMonoidHom from
      Subgroup.comap_equiv_eq_map_symm e' _, Subgroup.card_map_of_injective e'.symm.injective,
      card_projUnitriangular_three hk]
    norm_num
  have hZ0card : Nat.card Z0 = 4 := by
    rw [show Z0 = (wSub k).map e'.symm.toMonoidHom from
      Subgroup.comap_equiv_eq_map_symm e' _, Subgroup.card_map_of_injective e'.symm.injective,
      card_wSub, hk]
  obtain ⟨d, hdU, hdZ, hdg⟩ := exists_fixed_lift_not_mem g hc hsq' hZ hΩ (by omega)
  have hfixu : ∀ z : L₂, z * g = g * z → z ∈ SBd18.fixedSub u := fun z hz => by
    rw [SBd18.mem_fixedSub, hug, MulAut.conj_apply, ← hz]
    group
  have hMc : M ≤ Subgroup.center L₂ := by
    intro m hm
    by_contra hmz
    have hmfix : g * m * g⁻¹ = m := by
      have h := SBd18.mem_fixedSub.mp (hMfix hm)
      rw [hug, MulAut.conj_apply] at h
      exact h
    have hmg : e' (QuotientGroup.mk' (Subgroup.center L₂) m) * wP 1 =
        wP 1 * e' (QuotientGroup.mk' (Subgroup.center L₂) m) := by
      rw [← he'g, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      have h1 : g * m = m * g := by rw [mul_inv_eq_iff_eq_mul] at hmfix; exact hmfix
      rw [h1]
    have hmb1 : e' (QuotientGroup.mk' (Subgroup.center L₂) m) ≠ 1 := fun h =>
      hmz ((QuotientGroup.eq_one_iff m).mp (e'.injective (h.trans (map_one e').symm)))
    obtain ⟨n, hn⟩ := hM3 ⟨m, hm⟩
    have hmn : e' (QuotientGroup.mk' (Subgroup.center L₂) m) ^ 3 ^ n = 1 := by
      have h1 : m ^ 3 ^ n = 1 := congrArg Subtype.val hn
      rw [← map_pow, ← map_pow, h1, map_one, map_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hmn)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hmb1 (orderOf_eq_one_iff.mp (by rw [hj]; rfl))
    have hne0 : orderOf (e' (QuotientGroup.mk' (Subgroup.center L₂) m)) ≠ 0 := by
      rw [hj]
      positivity
    have h3dvd : 3 ∣ orderOf (e' (QuotientGroup.mk' (Subgroup.center L₂) m)) := by
      rw [hj]
      exact dvd_pow_self 3 hj0
    have hord := orderOf_pow_orderOf_div hne0 h3dvd
    have hw2 : orderOf (wP 1 : projectiveSL 3 k) = 2 := by
      rw [← he'g]
      refine orderOf_eq_prime (by rw [sq, ← map_mul, hp2, map_one]) fun h => hp1 ?_
      exact e'.injective (h.trans (map_one e').symm)
    exact CFSG.RankThree.PartTwo.KFacts.L34.mul_ne_mul_of_orderOf hk hord hw2
      (((Commute.pow_left (hmg : Commute _ _) _)).eq)
  let Φx := PerfectAutomorphisms.centerQuotientHom L₂ x
  have hΦ : ∀ z : L₂, z ∈ SBd18.fixedSub u → Φx (z : L₂ ⧸ Subgroup.center L₂) =
      (z : L₂ ⧸ Subgroup.center L₂) := fun z hz => by
    rw [CentralCover.centerQuotientHom_apply_mk]
    have h := hMc (hxM z hz)
    have h1 := (QuotientGroup.eq_one_iff (x z * z⁻¹)).mpr h
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] at h1
    exact h1
  let α : MulAut (projectiveSL 3 k) := autTransfer e' Φx
  have hα3 : α ^ 3 = 1 := by
    have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    change autTransfer e' Φx ^ 3 = 1
    rw [← map_pow, show Φx ^ 3 = PerfectAutomorphisms.centerQuotientHom L₂ (x ^ 3) from
      (map_pow _ _ _).symm, hx3', map_one, map_one]
  have hαw : α (wP 1) = wP 1 := by
    rw [← he'g, autTransfer_apply, MulEquiv.symm_apply_apply]
    have := hΦ g (hfixu g rfl)
    exact congrArg e' this
  obtain ⟨A, hA, hAs, hnz⟩ := exists_lift_of_mem_not_mem (s := e' (d : L₂ ⧸ Subgroup.center L₂))
    hdU (fun h => hdZ h)
  have hαA : α (proj 3 k A) = proj 3 k A := by
    rw [hAs, autTransfer_apply, MulEquiv.symm_apply_apply]
    have := hΦ d (hfixu d hdg)
    exact congrArg e' this
  have hα1 : α = 1 := eq_one_of_fixes hk hα3 hαw hA hnz hαA
  have hΦx1 : Φx = 1 := autTransfer_injective e' (hα1.trans (map_one _).symm)
  have hx1 : x = 1 :=
    PerfectAutomorphisms.centerQuotientHom_injective L₂ (hΦx1.trans (map_one _).symm)
  rw [hx1, orderOf_one] at hx3
  omega

end CFSG.Quasithin.SBd19F
