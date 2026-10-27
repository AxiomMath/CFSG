module

public import CFSG.RankThree.PartOne.KFOUT3.L12Ker
public import CFSG.RankThree.PartOne.KF.LayerTransfer
public import CFSG.RankThree.PartOne.KF.FratRows
public import CFSG.RankThree.PartOne.KF.SymCtxQuot
public import CFSG.RankThree.PartOne.KF.LayerFrame

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFOUT3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LocalCores

theorem kf1212LayerRow12 : KF1212LayerRow 12 := by
  intro G _ _ p A c L E ctx hmodel _ h4
  have h := ctx.hyp
  have hp5 : p = 5 := hmodel.1
  subst hp5
  have hcore := ctx.table_core
  obtain ⟨f, K, hKf, hKfin, hU, hf1, h5, h25, hmod, ε, hε, hAε⟩ := exists_r12plane hcore hmodel
  have hp : Nat.Prime 5 := Nat.prime_five
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have : CharP K 2 := hU.charP
  obtain ⟨z, hz⟩ := exists_isPrimitiveRoot hU Nat.prime_five h5
  have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
  let t : Kˣ := Units.mk0 z hz0
  have ht : t ^ 5 = 1 := Units.ext (by simpa [t] using hz.pow_eq_one)
  have ht1 : t ≠ 1 := fun h1 => hz.ne_one (by norm_num) (by simpa [t] using congrArg Units.val h1)
  set bM : ↥(unitarySU 2 f K 5) := bB hU h5 ht with hbM
  have hbMp := bB_pow_five hU h5 ht
  have hbmem : projU K f bM ∈ ((A ⊓ L).subgroupOf L).map ε := by
    rw [hAε]
    exact ⟨bM, bB_mem_piSU hU h5 ht, rfl⟩
  obtain ⟨x, hx, hxb⟩ := hbmem
  have hxA : (x : G) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
  have hxL : (x : G) ∈ L := x.2
  have hbb : ε ⟨(x : G), hxL⟩ = (MonoidHom.id _ : StatedProj (unitarySU 2 f K 5) →*
      StatedProj (unitarySU 2 f K 5)) (projU K f bM) := hxb
  have hb1 : (x : G) ≠ 1 := by
    intro h1
    have h2 : projU K f bM = 1 := by
      rw [← hxb]
      have : x = 1 := Subtype.ext h1
      rw [this, map_one]
    exact projU_bB_ne_one hU h5 ht ht1 h2
  have hKP := perfectResidual_centralizer_proj hU h5 ht ht1
  have hQ : IsQuasisimple ↥((suBlock12 hU).range) := by
    have := isQuasisimple_perfectResidual_centralizer_bB hU h5 ht ht1
    rwa [perfectResidual_centralizer_bB hU h5 ht ht1] at this
  have hq : IsCentralPQuot 5 (MonoidHom.id (StatedProj (unitarySU 2 f K 5))) :=
    SymCtx.isCentralPQuot_of_bijective _ Function.bijective_id 5
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    intro a ha
    have R := h.restr_of_generic ctx.generic
    obtain ⟨e, he, i, hei⟩ := R.exists_mul_zpow (h.A_le_E ha)
    have hciA : c ^ i ∈ A := A.zpow_mem h.c_mem i
    have heA : e ∈ A := by
      have : e = a * (c ^ i)⁻¹ := by rw [hei]; group
      rw [this]
      exact A.mul_mem ha (A.inv_mem hciA)
    rw [hei]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨heA, he.2⟩)
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i))
  obtain ⟨KL, hKLeq, hKLq, hKLz, hAK, htwo, ⟨eqv⟩⟩ := exists_layerCore_of_cover hp hp2
    (IsPGroup.of_card h.A_card) h.A_elem ctx.L_le_centralizer hA ε
    (MonoidHom.id (StatedProj (unitarySU 2 f K 5))) hε hq hxA hxL
    (bM := projU K f bM) (by rw [← map_pow, hbMp, map_one]) hbb
    (T₀ := (piSU f K).map (projU K f)) (U := (rad5 f K).map (projU K f))
    (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := hy
      rw [← map_pow, piSU_pow_five ha, map_one])
    (by rw [Subgroup.map_id]; exact hAε)
    (by
      rw [hKP]
      exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv (kerEquiv hU) hQ)
    (by
      rw [hKP, ← card_center_mulEquiv (kerEquiv hU)]
      exact not_dvd_card_center_range_suBlock12 hU h5)
    (by
      rw [hKP]
      exact card_proj_inf hU h5 hz)
    (by
      rw [hKP]
      exact Subgroup.map_mono (rad5_le_range hU))
    (isPGroup_rad5.of_surjective ((projU K f).subgroupMap (rad5 f K))
      ((projU K f).subgroupMap_surjective (rad5 f K)))
    (by
      rintro y ⟨a, ha, rfl⟩
      refine mem_normalizer_of_conj_mem (fun v hv => ?_) (fun v hv => ?_)
      · obtain ⟨w, hw, rfl⟩ := hv
        exact ⟨a * w * a⁻¹, piSU_conj_rad5 ha hw, by simp⟩
      · obtain ⟨w, hw, rfl⟩ := hv
        exact ⟨a⁻¹ * w * a, by simpa using piSU_conj_rad5 ((piSU f K).inv_mem ha) hw, by simp⟩)
    (by
      obtain ⟨u, hu, a, ha, hne⟩ := exists_not_commute hU h5 ht ht1
      exact ⟨projU K f u, ⟨u, hu, rfl⟩, projU K f a, ⟨a, ha, rfl⟩, hne⟩)
  refine ⟨(x : G), KL, ⟨⟨hxA, hxL, hb1⟩, hKLeq, hKLq, hKLz, hAK, htwo⟩, ?_⟩
  have hF : Nat.card K = (2 ^ f) ^ 2 := by rw [hU.card, ← pow_mul, mul_comm]
  have hf2 : 2 ≤ f := two_le_of_dvd_five h5
  have hnq : ((3 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h3
    have h2 : 2 ^ f = 2 ^ 1 := congrArg Prod.snd h3
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := f)
    hF (n := 3) le_rfl hnq).2
  refine ⟨f, hf1, h5, hmod, ⟨Nat.prime_two, hf1, le_rfl, hnq⟩, K, hKf, hKfin, hF, ?_⟩
  obtain ⟨e₁⟩ := exists_centerQuotient_mulEquiv
    ((MulEquiv.subgroupCongr hKP).trans (kerEquiv hU).symm)
  obtain ⟨e₂⟩ := exists_centerQuotient_mulEquiv (MonoidHom.ofInjective (suBlock12_injective hU)).symm
  exact ⟨eqv.trans (e₁.trans (e₂.trans (QuotientGroup.quotientMulEquivOfEq hZ)))⟩

end CFSG.RankThree.PartOne
