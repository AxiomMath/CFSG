module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Conf
public import CFSG.RankThree.PartTwo.Sec14.Ronan148BA6Swap
public import CFSG.RankThree.PartTwo.Sec14.Ronan148ANormalHJGen
public import CFSG.RankThree.PartTwo.Sec14.Ronan148AA6Transport
public import CFSG.RankThree.PartTwo.Sec14.Ronan148AA6Point

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS Main148 HJRes148

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_mem_zpowers_of_isLBConfig {A B Lb : Subgroup G} {b d : G} [Finite G]
    (hA : Late.IsE27 A) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    b ∉ Subgroup.zpowers d := by
  intro hbd
  obtain ⟨-, hdB, -, -, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hBle : B ≤ Subgroup.zpowers d := by
    rw [hc.1, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hbd
    · exact Subgroup.mem_zpowers g
  have h1 : Nat.card (Subgroup.zpowers d) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (hA.1.2 d hdA)
  have h2 : Nat.card B ≤ Nat.card (Subgroup.zpowers d) := Subgroup.card_le_of_le hBle
  have h3 : Nat.card B = 9 := by
    have := hB.2
    rw [hA.2] at this
    omega
  have h4 := Nat.le_of_dvd (by norm_num) h1
  omega

section Certificates



theorem step148NormalHJA6One2_of (hT : KTransport148) (hPQ : Step148A6PointQ) :
    Ronan148A.Step148NormalHJA6One2 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hXJ h12 y hy
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := hS.isE27
  obtain ⟨hbB, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hbA : b ∈ A := hB.1 hbB
  have hdA : d ∈ A := hB.1 hdB
  have hbd : b ∉ Subgroup.zpowers d := not_mem_zpowers_of_isLBConfig hA hB hc
  obtain ⟨η⟩ := hη
  have hYd6 : Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr η.symm hJ6
  obtain ⟨hYB6, hdYB, hbc⟩ := HJRes2.outer_facts hS hB hc hYB htype hle hYd hYBYd hAYd hYd6
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have hYBC : YB ≤ Y ⊓ Subgroup.centralizer (B : Set G) := le_of_mem_thetaComponentsIn hYB
  have hYBY : YB ≤ Y := hYBC.trans inf_le_left
  have hYBM : YB ≤ Y ⊔ A := hYBY.trans le_sup_left
  have hJcard : Nat.card ↥(img148 A Y J) = 1080 :=
    Sec19.Item19Res4Proof.card_eq_of_isTripleA6 hJ6
  have h3J' : 3 ∣ Nat.card ↥(img148 A Y J) := by rw [hJcard]; norm_num
  have h3J : 3 ∣ Nat.card J := h3J'.trans (card_img148_dvd hJM)
  have hJc : IsComponent (img148 A Y J) := Ronan148J.isComponent_img148_of_three_dvd hY.2 hJ h3J
  obtain ⟨-, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  set dα := alpha148 A Y d hdA with hdαdef
  have hdJ : dα ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hdA, hYdJ (hYBYd hdYB), rfl⟩
  have hdC : img148 A Y J ≤ Subgroup.centralizer {dα} :=
    HJRes2.le_centralizer_of_mem_sectionCentralizer hdA hdc
  have hdα1 : dα ≠ 1 := fun h1' => hd1 (alpha148_injective hA.1.2 hdA A.one_mem
    (h1'.trans ((alpha148_eq_mk' A.one_mem).trans
      (mk'_ker148_eq_one_iff.mpr (Subgroup.one_mem _))).symm))
  have hdZ : img148 A Y J ⊓
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      Subgroup.zpowers dα := by
    have hdZJ : dα ∈ img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      refine ⟨hdJ, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hdC hz))
    have hZ3 : Nat.card ↥(img148 A Y J ⊓
        Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) = 3 := by
      rw [← hJ6.1, ← Sec14.map_subtype_center_eq,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have hd3 : dα ^ 3 = 1 := by
      rw [hdαdef, ← alpha148_pow hdA 3]
      simp only [hA.1.2 d hdA]
      exact (alpha148_eq_mk' A.one_mem).trans (mk'_ker148_eq_one_iff.mpr (Subgroup.one_mem _))
    have hdo : orderOf dα = 3 := orderOf_eq_prime hd3 hdα1
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdZJ) ?_).symm
    rw [hZ3, Nat.card_zpowers, hdo]
  have hbJ := HJRes2.le_centralizer_of_theta hYdM heq hJθ hbA hbc.2
  have hBJ : img148 A Y B ≤
      Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hc.1]
    have hS' : ({b, d} : Set G) ⊆ (Y ⊔ A : Subgroup G) := by
      rintro g (rfl | rfl)
      · exact Subgroup.mem_sup_right hbA
      · exact Subgroup.mem_sup_right hdA
    refine Ronan148J.img148_closure_le_centralizer hS' fun g hg => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hg with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hbJ hz)
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hdC hz)
  have h3YB : 3 ∣ Nat.card YB := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥YB),
      HJRes2.card_of_isTripleCover_six hYB6]
    exact Dvd.dvd.mul_right (by norm_num) _
  have hYBα : img148 A Y YB = img148 A Y J := by
    refine Subgroup.eq_of_le_of_card_ge (heq ▸ img148_mono hYBYd) ?_
    have h1' := Ronan148J.card_theta_quot_le_card_img148 (A := A) (Y := Y) hYBM
      (isPerfect_of_mem_thetaComponentsIn hYB) (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB)
      h3YB
    rw [HJRes2.card_of_isTripleCover_six hYB6] at h1'
    rw [hJcard]
    exact h1'
  by_contra hN
  set x := QuotientGroup.mk' (ker148 A Y) (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ A)) with hx
  have hne : (img148 A Y J).map (MulAut.conj x).toMonoidHom ≠ img148 A Y J := by
    intro heq'
    apply hN
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact heq'
  set K := (img148 A Y J).map (MulAut.conj x).toMonoidHom with hK
  have hKc : IsComponent K := Res2LBal.isComponent_conj hJc x
  have eK : ↥(img148 A Y J) ≃* ↥K :=
    (img148 A Y J).equivMapOfInjective _ (MulAut.conj x).injective
  have hK6 : Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) :=
    KFacts.KS14.isTripleCover_congr eK hJ6
  have hKZ : K ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      img148 A Y J ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    Ronan148A.center_eq_of_tripleCover_A6148 hS hJc hJ6 x hne
  have hxY : x ∈ img148 A Y Y := mem_img148_iff.mpr ⟨y, Subgroup.mem_sup_left hy, hy, rfl⟩
  have hKY : K ≤ img148 A Y Y := by
    rintro _ ⟨z, hz, rfl⟩
    exact (img148 A Y Y).mul_mem ((img148 A Y Y).mul_mem hxY (img148_mono hJY hz))
      ((img148 A Y Y).inv_mem hxY)
  have hKx : K.map (MulAut.conj x).toMonoidHom = img148 A Y J := by
    rcases Ronan148A.map_conj_eq_or_of_tripleCover_A6148 hS hJc hJ6 x (x * x) with h | h | h
    · exact absurd h hne
    · rw [hK, Res2LBal.map_conj_map_conj]
      exact h
    · exfalso
      apply hne
      have h2 := congrArg (fun H : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) =>
        H.map (MulAut.conj x⁻¹).toMonoidHom) h
      simp only [Res2LBal.map_conj_map_conj, inv_mul_cancel, Res2LBal.map_conj_one,
        inv_mul_cancel_left] at h2
      exact h2.symm
  have hKx' : K.map (MulAut.conj x⁻¹).toMonoidHom = img148 A Y J := by
    rw [hK, Res2LBal.map_conj_map_conj, inv_mul_cancel, Res2LBal.map_conj_one]
  have hAK : img148 A Y A ≤ Subgroup.normalizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro a ha
    have haJ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAJα ha)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change K.map (MulAut.conj a).toMonoidHom = K
    rcases Ronan148A.map_conj_eq_or_of_tripleCover_A6148 hS hJc hJ6 x (a * x) with h | h | h
    · exact absurd h hne
    · exfalso
      apply hne
      have h2 : K.map (MulAut.conj a).toMonoidHom = img148 A Y J := by
        rw [hK, Res2LBal.map_conj_map_conj]
        exact h
      have h3 := congrArg (fun H : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y) =>
        H.map (MulAut.conj a⁻¹).toMonoidHom) h2
      have haJ' : (img148 A Y J).map (MulAut.conj a⁻¹).toMonoidHom = img148 A Y J :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp ((hAJα (inv_mem ha)))
      simp only [Res2LBal.map_conj_map_conj, inv_mul_cancel, Res2LBal.map_conj_one] at h3
      rw [h3, haJ']
    · rw [hK, Res2LBal.map_conj_map_conj]
      exact h.symm
  obtain ⟨hbK, hbC, hAeqK, hE₁9, hAeq⟩ := a6_config148 hS hY.2 hB hbB hdB hd1 hbd hJc hJ6 hKc hK6
    hne hAJα hAK hBJ hdZ hKZ
  set bα := alpha148 A Y b hbA with hbαdef
  have hdZK : dα ∈ K ⊓ Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hKZ, hdZ]; exact Subgroup.mem_zpowers dα
  have hbdα : bα ∉ Subgroup.zpowers dα := fun h => hbC ((Subgroup.zpowers_le.mpr hdZK.2) h)
  have hAE := img148_isE27 (Y := Y) hA
  have hA3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := hAE.1.2
  have hAab : ∀ u ∈ img148 A Y A, ∀ v ∈ img148 A Y A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAE.1.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hbαA : bα ∈ img148 A Y A := alpha148_mem_img148 hbA
  have hdαA : dα ∈ img148 A Y A := alpha148_mem_img148 hdA
  have hE9 : Nat.card ↥(Subgroup.zpowers bα ⊔ Subgroup.zpowers dα) = 9 := by
    have h9 := Ronan148J.card_zpowers_sup_zpowers_eq_nine (hAab _ hdαA _ hbαA) (hA3 _ hdαA) hdα1
      (hA3 _ hbαA) hbdα
    rwa [sup_comm (Subgroup.zpowers dα) (Subgroup.zpowers bα)] at h9
  have hEK : Subgroup.zpowers bα ⊔ Subgroup.zpowers dα ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr hbK) (Subgroup.zpowers_le.mpr hdZK.1)
  have hEx : (Subgroup.zpowers bα ⊔ Subgroup.zpowers dα).map (MulAut.conj x).toMonoidHom ≤
      img148 A Y YB := by
    rw [hYBα, ← hKx]
    exact Subgroup.map_mono hEK
  have hEx' : (Subgroup.zpowers bα ⊔ Subgroup.zpowers dα).map (MulAut.conj x⁻¹).toMonoidHom ≤
      img148 A Y YB := by
    rw [hYBα, ← hKx']
    exact Subgroup.map_mono hEK
  have hdx : (Subgroup.zpowers dα).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers dα := by
    have hxd : x * dα * x⁻¹ ∈ Subgroup.zpowers dα := by
      rw [← hdZ, ← hKZ]
      refine ⟨Res2LBal.conj_mem_map hdJ x, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      obtain ⟨j, hj, rfl⟩ := hz
      have hjd : j * dα = dα * j := Subgroup.mem_centralizer_singleton_iff.mp (hdC hj)
      simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      calc x * j * x⁻¹ * (x * dα * x⁻¹) = x * (j * dα) * x⁻¹ := by group
        _ = x * (dα * j) * x⁻¹ := by rw [hjd]
        _ = x * dα * x⁻¹ * (x * j * x⁻¹) := by group
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [MonoidHom.map_zpowers]
      exact Subgroup.zpowers_le.mpr hxd
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  obtain ⟨w, hwN, hwb⟩ := exists_normalizer_mem_inf148 hT hS hY hB hc hbA hdA hYBY hle hy hE9
    hEx hEx' hdx
  have hE₁YB : img148 A Y A ⊓ img148 A Y J ≤ img148 A Y YB := by
    rw [hYBα]; exact inf_le_right
  have hE₁3 : IsPGroup 3 ↥(img148 A Y A ⊓ img148 A Y J) :=
    IsPGroup.of_card (n := 2) (by rw [hE₁9]; norm_num)
  obtain ⟨w₁, hw₁N, hw₁⟩ := exists_normalizer_map_inf148 hT hS hB hc hbA hYBY hle hE₁YB hE₁3
    hE₁9 hAeq
  obtain ⟨ha, haE⟩ := hw₁ (w * b * w⁻¹) hwb
  have haΩ : Subgroup.zpowers (w₁ * (w * b * w⁻¹) * w₁⁻¹) ∈ omegaA A := by
    have e1 : Subgroup.zpowers (w₁ * (w * b * w⁻¹) * w₁⁻¹) =
        (Subgroup.zpowers b).map (MulAut.conj (w₁ * w)).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      congr 1
      simp only [MonoidHom.coe_coe, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group
    rw [e1, map_conj_mem_omegaA_iff (mul_mem hw₁N hwN)]
    exact hc.2.1
  have haK : alpha148 A Y (w₁ * (w * b * w⁻¹) * w₁⁻¹) ha ∈
      Subgroup.centralizer (K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    Res2LBal.mem_centralizer_of_mem_of_ne hKc hJc hne haE.2
  exact hPQ G A c L hS Y hY J hJ hAJ hJ6 hXJ K hKc hne hK6 hKY bα hbαA hbK hbC hAeqK _ ha haΩ
    haK

theorem step148NormalHJA6One3_of (hT : KTransport148) (hPQ : Step148A6PointQ) :
    Ronan148A.Step148NormalHJA6One3 := by
  intro G _ _ A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ
    Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hXJ h12 y hy _
  exact step148NormalHJA6One2_of hT hPQ G A c L hS Y hY hs ih hcases h1 B hB hnot YB hYB htype hΔ
    b d Lb hc hle J hJ hYBJ hAJ Yd hYd hYBYd hYdJ hAYd hYdt hdc heq hη hJ6 hXJ h12 y hy

theorem kTransport148_holds : KTransport148 :=
  fun _ _ _ _ _ _ hS _ hB _ _ _ hc _ hle _ hEY hE3 hE9 =>
    Ronan148A.exists_conj_eq_sup_of_le_yb148 hS hB hc hle hEY hE3 hE9

theorem step148NormalHJA6One3_holds (h142 : Concl142S14) : Ronan148A.Step148NormalHJA6One3 :=
  step148NormalHJA6One3_of kTransport148_holds (Ronan148A.step148A6PointQ_holds h142)

end Certificates

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
