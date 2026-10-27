module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveLayer
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCentralizes
public import CFSG.LocalAnalysis.StandardType.GGHalfFivePerm
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockEmbed
public import CFSG.LieType.SeitzGeneration.HyperIrrBlock

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

open scoped commutatorElement

private theorem zeta5_mem_halfTorus : zeta5 ∈ halfTorus 5 := by
  rw [zeta5]
  exact mul_mem (mul_mem (Subgroup.subset_closure ⟨0, by decide, rfl⟩)
    (Subgroup.subset_closure ⟨2, by decide, rfl⟩))
    (Subgroup.subset_closure ⟨4, by decide, rfl⟩)

private theorem omegaBlock_five_mem_halfTorus (k : Fin 5) (hk : k.val % 2 = 0) :
    omegaBlock 5 k ∈ halfTorus 5 :=
  Subgroup.subset_closure ⟨k, hk, rfl⟩

private theorem commutator_centralizer_eq_sl3four :
    ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
      Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆ = sl3four := by
  apply le_antisymm
  · have hderiv : ⁅(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)),
        (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4))⁆ ≤
        SpecialLinearGroup.toGL.range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact Commute.commutator_eq (Commute.all _ _)
    calc ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
          Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆
        = ⁅(resGL 3).range, (resGL 3).range⁆ := by rw [centralizer_zeta5]
      _ = Subgroup.map (resGL 3) ⁅(⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)),
            (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4))⁆ := by
          rw [MonoidHom.range_eq_map, Subgroup.map_commutator]
      _ ≤ Subgroup.map (resGL 3) SpecialLinearGroup.toGL.range := Subgroup.map_mono hderiv
      _ = sl3four := by rw [sl3four, resSL, MonoidHom.range_comp]
  · haveI : Group.IsPerfect ↥sl3four := isQuasisimple_sl3four.1
    calc sl3four = ⁅sl3four, sl3four⁆ := (Subgroup.commutator_eq_self (H := sl3four)).symm
      _ ≤ ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
            Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆ :=
          Subgroup.commutator_mono sl3four_le_centralizer sl3four_le_centralizer

private theorem omegaBlock_five_mem_centralizer (k : Fin 5) (hk : k.val % 2 = 0) :
    omegaBlock 5 k ∈ Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)) :=
  Subgroup.mem_centralizer_singleton_iff.mpr
    (halfTorus_comm (omegaBlock_five_mem_halfTorus k hk) zeta5_mem_halfTorus)

theorem map_sl3four_of_fix {α : MulAut (SpecialLinearGroup (Fin 6) F2)} (hα : α zeta5 = zeta5) :
    sl3four.map α.toMonoidHom = sl3four := by
  have hC : (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))).map
      α.toMonoidHom = Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      calc α y * zeta5 = α y * α zeta5 := by rw [hα]
        _ = α (y * zeta5) := (map_mul α y zeta5).symm
        _ = α (zeta5 * y) := by rw [hy]
        _ = α zeta5 * α y := map_mul α zeta5 y
        _ = zeta5 * α y := by rw [hα]
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      refine ⟨α.symm x, ?_, α.apply_symm_apply x⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply α.injective
      simp only [map_mul, MulEquiv.apply_symm_apply, hα]
      exact hx
  calc sl3four.map α.toMonoidHom
      = (⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
          Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆).map
            α.toMonoidHom := by rw [commutator_centralizer_eq_sl3four]
    _ = ⁅(Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))).map α.toMonoidHom,
          (Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))).map
            α.toMonoidHom⁆ :=
          Subgroup.map_commutator _ _ _
    _ = ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
          Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆ := by rw [hC]
    _ = sl3four := commutator_centralizer_eq_sl3four

theorem map_sl3four_of_mem_halfTorus {t : SpecialLinearGroup (Fin 6) F2} (ht : t ∈ halfTorus 5) :
    sl3four.map (MulAut.conj t).toMonoidHom = sl3four := by
  refine map_sl3four_of_fix (α := MulAut.conj t) ?_
  rw [MulAut.conj_apply, halfTorus_comm ht zeta5_mem_halfTorus]
  group

theorem omega_div_mem_sl3four :
    omegaBlock 5 0 * (omegaBlock 5 2)⁻¹ ∈ sl3four ∧ omegaBlock 5 2 * (omegaBlock 5 4)⁻¹ ∈ sl3four := by
  have hσmem : slPerm gf2_two (sigmaPerm 3) ∈ sl3four := slPerm_sigma_mem_sl3four
  have hτmem : slPerm gf2_two (tauPerm 3) ∈ sl3four := slPerm_tau_mem_sl3four
  have hconj0 : slPerm gf2_two (sigmaPerm 3) * omegaBlock 5 0 *
      (slPerm gf2_two (sigmaPerm 3))⁻¹ = omegaBlock 5 2 :=
    slPerm_conj_omegaBlock (π := sigmaPerm 3) (k := ⟨0, by omega⟩) (k' := ⟨2, by omega⟩)
      (by decide) (by decide)
  have hmem1 : omegaBlock 5 0 * (omegaBlock 5 2)⁻¹ ∈ sl3four := by
    have hmem : ⁅omegaBlock 5 0, slPerm gf2_two (sigmaPerm 3)⁆ ∈
        ⁅Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2)),
          Subgroup.centralizer ({zeta5} : Set (SpecialLinearGroup (Fin 6) F2))⁆ :=
      Subgroup.commutator_mem_commutator (omegaBlock_five_mem_centralizer 0 (by decide))
        (sl3four_le_centralizer hσmem)
    rw [commutator_centralizer_eq_sl3four] at hmem
    have heq : omegaBlock 5 0 * (omegaBlock 5 2)⁻¹ =
        ⁅omegaBlock 5 0, slPerm gf2_two (sigmaPerm 3)⁆ := by
      rw [← hconj0, commutatorElement_def]
      group
    rwa [heq]
  have hconj_tau0 : slPerm gf2_two (tauPerm 3) * omegaBlock 5 0 *
      (slPerm gf2_two (tauPerm 3))⁻¹ = omegaBlock 5 4 :=
    slPerm_conj_omegaBlock (π := tauPerm 3) (k := ⟨0, by omega⟩) (k' := ⟨4, by omega⟩)
      (by decide) (by decide)
  have hconj_tau2 : slPerm gf2_two (tauPerm 3) * omegaBlock 5 2 *
      (slPerm gf2_two (tauPerm 3))⁻¹ = omegaBlock 5 2 :=
    slPerm_conj_omegaBlock (π := tauPerm 3) (k := ⟨2, by omega⟩) (k' := ⟨2, by omega⟩)
      (by decide) (by decide)
  have hmem2 : omegaBlock 5 2 * (omegaBlock 5 4)⁻¹ ∈ sl3four := by
    have hconjmem : slPerm gf2_two (tauPerm 3) * (omegaBlock 5 0 * (omegaBlock 5 2)⁻¹) *
        (slPerm gf2_two (tauPerm 3))⁻¹ ∈ sl3four :=
      mul_mem (mul_mem hτmem hmem1) (inv_mem hτmem)
    have heq : slPerm gf2_two (tauPerm 3) * (omegaBlock 5 0 * (omegaBlock 5 2)⁻¹) *
        (slPerm gf2_two (tauPerm 3))⁻¹ = (omegaBlock 5 2 * (omegaBlock 5 4)⁻¹)⁻¹ := by
      calc slPerm gf2_two (tauPerm 3) * (omegaBlock 5 0 * (omegaBlock 5 2)⁻¹) *
            (slPerm gf2_two (tauPerm 3))⁻¹
          = (slPerm gf2_two (tauPerm 3) * omegaBlock 5 0 *
              (slPerm gf2_two (tauPerm 3))⁻¹) *
            (slPerm gf2_two (tauPerm 3) * omegaBlock 5 2 *
              (slPerm gf2_two (tauPerm 3))⁻¹)⁻¹ := by group
        _ = omegaBlock 5 4 * (omegaBlock 5 2)⁻¹ := by rw [hconj_tau0, hconj_tau2]
        _ = (omegaBlock 5 2 * (omegaBlock 5 4)⁻¹)⁻¹ := by group
    have : (omegaBlock 5 2 * (omegaBlock 5 4)⁻¹)⁻¹ ∈ sl3four := by
      rwa [← heq]
    simpa using inv_mem this
  exact ⟨hmem1, hmem2⟩

theorem normal_coprime_eq_bot {Q : Subgroup (SpecialLinearGroup (Fin 6) F2)} (hQ : Q ≤ sl3four)
    (hnorm : (Q.subgroupOf sl3four).Normal) (hcop : Nat.Coprime (Nat.card Q) 3) : Q = ⊥ := by
  classical
  let Q' : Subgroup ↥sl3four := Q.subgroupOf sl3four
  haveI hQ'normal : Q'.Normal := hnorm
  let N : Subgroup (SpecialLinearGroup (Fin 3) F4) := Q'.comap sl3fourEquiv.toMonoidHom
  haveI hNnormal : N.Normal := hnorm.comap sl3fourEquiv.toMonoidHom
  have hcardSL : Nat.card (SpecialLinearGroup (Fin 3) F4) = 60480 :=
    (Nat.card_congr sl3fourEquiv.toEquiv).trans card_sl3four
  have hcard_center : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F4)) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr sl3fourEquiv).toEquiv]
    exact card_center_sl3four
  have hcardQ' : Nat.card Q' = Nat.card Q := by
    have h := Subgroup.card_map_of_injective (K := Q') (f := sl3four.subtype)
      sl3four.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype Q sl3four, inf_eq_left.mpr hQ] at h
    exact h.symm
  have hmap : N.map sl3fourEquiv.toMonoidHom = Q' :=
    Subgroup.map_comap_eq_self_of_surjective sl3fourEquiv.surjective Q'
  have hcardN : Nat.card N = Nat.card Q' := by
    have h := Subgroup.card_map_of_injective (K := N) (f := sl3fourEquiv.toMonoidHom)
      sl3fourEquiv.injective
    rw [hmap] at h
    exact h.symm
  have hcardNQ : Nat.card N = Nat.card Q := by rw [hcardN, hcardQ']
  have hcop' : Nat.gcd (Nat.card Q) 3 = 1 := hcop
  by_cases hle : N ≤ Subgroup.center (SpecialLinearGroup (Fin 3) F4)
  · have hdvd : Nat.card N ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [hcard_center] at h
    have hne3 : Nat.card N ≠ 3 := by
      intro h3
      have h3dvd : 3 ∣ Nat.card Q := by rw [← hcardNQ, h3]
      have h2 : 3 ∣ Nat.gcd (Nat.card Q) 3 := Nat.dvd_gcd h3dvd (dvd_refl 3)
      rw [hcop'] at h2
      exact absurd h2 (by norm_num)
    have hNcard : Nat.card N = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exact absurd h hne3
    have hNbot : N = ⊥ := Subgroup.card_eq_one.mp hNcard
    have hQ'bot : Q' = ⊥ := by rw [← hmap, hNbot, Subgroup.map_bot]
    rw [Subgroup.eq_bot_iff_forall Q]
    intro q hq
    have hmem : (⟨q, hQ hq⟩ : ↥sl3four) ∈ Q' := (Subgroup.mem_subgroupOf).mpr hq
    rw [hQ'bot] at hmem
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hmem)
  · exfalso
    obtain ⟨a, haN, hac⟩ := Set.not_subset.1 hle
    have htop : N = ⊤ :=
      CFSG.LieType.SeitzGeneration.eq_top_of_normal_of_not_mem_center (F := F4) (p := 3)
        (by norm_num) (N := N) haN hac
    have hcardtop : Nat.card N = 60480 := by
      rw [htop]
      exact (Nat.card_congr (Subgroup.topEquiv :
        (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F4)) ≃*
          SpecialLinearGroup (Fin 3) F4).toEquiv).trans hcardSL
    have h3dvd : 3 ∣ Nat.card Q := by rw [← hcardNQ, hcardtop]; norm_num
    have h2 : 3 ∣ Nat.gcd (Nat.card Q) 3 := Nat.dvd_gcd h3dvd (dvd_refl 3)
    rw [hcop'] at h2
    exact absurd h2 (by norm_num)

theorem not_centralizes_of_mem_zpowers_omega4 {t : SpecialLinearGroup (Fin 6) F2}
    (ht : t ∈ Subgroup.zpowers (omegaBlock 5 4)) (ht1 : t ≠ 1) :
    ¬ ∀ s ∈ sl3four, t * s = s * t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  intro hcent
  have hτmem : slPerm gf2_two (tauPerm 3) ∈ sl3four := slPerm_tau_mem_sl3four
  have hcomm : omegaBlock 5 4 ^ k * slPerm gf2_two (tauPerm 3) =
      slPerm gf2_two (tauPerm 3) * omegaBlock 5 4 ^ k := hcent _ hτmem
  have hconj : slPerm gf2_two (tauPerm 3) * omegaBlock 5 4 *
      (slPerm gf2_two (tauPerm 3))⁻¹ = omegaBlock 5 0 :=
    slPerm_conj_omegaBlock (π := tauPerm 3) (k := ⟨4, by omega⟩) (k' := ⟨0, by omega⟩)
      (by decide) (by decide)
  have hconj_zpow : slPerm gf2_two (tauPerm 3) * omegaBlock 5 4 ^ k *
      (slPerm gf2_two (tauPerm 3))⁻¹ = omegaBlock 5 0 ^ k := by
    have h1 : slPerm gf2_two (tauPerm 3) * omegaBlock 5 4 ^ k *
        (slPerm gf2_two (tauPerm 3))⁻¹ =
        (MulAut.conj (slPerm gf2_two (tauPerm 3))) (omegaBlock 5 4 ^ k) := by
      rw [MulAut.conj_apply]
    rw [h1, map_zpow, MulAut.conj_apply, hconj]
  have heq : omegaBlock 5 0 ^ k = omegaBlock 5 4 ^ k := by
    have h2 : slPerm gf2_two (tauPerm 3) * omegaBlock 5 4 ^ k *
        (slPerm gf2_two (tauPerm 3))⁻¹ = omegaBlock 5 4 ^ k := by
      rw [← hcomm]; group
    rw [hconj_zpow] at h2
    exact h2
  have hdisj := disjoint_zpowers_omegaBlock_lower 3
  have hω4_mem : omegaBlock 5 4 ∈ (halfTorus 3).map (slLower2Hom 3) := by
    refine Subgroup.mem_map.mpr ⟨omegaBlock 3 ⟨2, by omega⟩, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨⟨2, by omega⟩, by decide, rfl⟩
    · rw [slLower2Hom_omegaBlock]
      exact congrArg (omegaBlock 5) (Fin.ext rfl)
  have hbot : omegaBlock 5 0 ^ k = 1 := by
    refine (Subgroup.disjoint_def.mp hdisj) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩) ?_
    rw [heq]
    exact (Subgroup.zpowers_le.mpr hω4_mem) (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  exact ht1 (heq ▸ hbot)

end CFSG.StandardType.GGHalf

end
