module

public import CFSG.RankThree.GF2n.Smith81.S81E7Sl2
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourCentralizer
public import CFSG.RankThree.GF2n.Smith81.S81E7Cent

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_map_psi_iff (N : Subgroup ↥(adjointGroup .E7 K)) (x : ↥(e7Data_valid.minGroup K)) :
    (x : (Module.End K (V K))ˣ) ∈ (N.map (e7Psi K)).map (e7Data_valid.minGroup K).subtype ↔
      (e7Equiv (K := K)) x ∈ N := by
  constructor
  · intro h
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 h
    have hzx' : z = x := Subtype.ext hzx
    rw [← hzx']
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.1 hz
    rw [← haz]
    have hea : (e7Equiv (K := K)) (e7Psi K a) = a := (e7Equiv (K := K)).apply_symm_apply a
    rw [hea]
    exact ha
  · intro h
    exact Subgroup.mem_map.2 ⟨e7Psi K ((e7Equiv (K := K)) x), Subgroup.mem_map.2 ⟨(e7Equiv (K := K)) x, h, rfl⟩,
      congrArg Subtype.val ((e7Equiv (K := K)).symm_apply_apply x)⟩

theorem mem_Jgrp_iff_equiv (x : ↥(e7Data_valid.minGroup K)) :
    (x : (Module.End K (V K))ˣ) ∈ Jgrp K ↔
      (e7Equiv (K := K)) x ∈ (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) := by
  rw [Jgrp_eq_map]
  exact mem_map_psi_iff _ x

theorem mem_Lam_iff_equiv (x : ↥(e7Data_valid.minGroup K)) :
    (x : (Module.End K (V K))ˣ) ∈ Lam K ↔ (e7Equiv (K := K)) x ∈ EPilot.perpLevi .E7 K := by
  rw [Lam_eq_map]
  exact mem_map_psi_iff _ x

abbrev sl2W : Matrix.SpecialLinearGroup (Fin 2) K := CFSG.LieType.Chevalley.WSL

theorem sl2W_mul_vSL (e : K) :
    sl2W * CFSG.LieType.Chevalley.vSL e = CFSG.LieType.Chevalley.uSL (-e) * sl2W := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2W, Matrix.SpecialLinearGroup.coe_mul, CFSG.LieType.Chevalley.coe_uSL,
      CFSG.LieType.Chevalley.coe_vSL, CFSG.LieType.Chevalley.coe_WSL, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sl2W_mul_uSL (a : K) :
    sl2W * CFSG.LieType.Chevalley.uSL a = CFSG.LieType.Chevalley.vSL (-a) * sl2W := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2W, Matrix.SpecialLinearGroup.coe_mul, CFSG.LieType.Chevalley.coe_uSL,
      CFSG.LieType.Chevalley.coe_vSL, CFSG.LieType.Chevalley.coe_WSL, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem sl2W_mul_HSL (c : Kˣ) :
    sl2W * CFSG.LieType.Chevalley.HSL c = CFSG.LieType.Chevalley.HSL c⁻¹ * sl2W := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2W, Matrix.SpecialLinearGroup.coe_mul, CFSG.LieType.Chevalley.coe_HSL,
      CFSG.LieType.Chevalley.coe_WSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Diag_eq_HSL (c : Kˣ) : sl2Diag c = CFSG.LieType.Chevalley.HSL c := rfl

theorem jHom_mem_minGroup (m : Matrix.SpecialLinearGroup (Fin 2) K) :
    jHom m ∈ e7Data_valid.minGroup K :=
  Jgrp_le_E (by rw [Jgrp_eq_range]; exact MonoidHom.mem_range.2 ⟨m, rfl⟩)

def jHomMin : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(e7Data_valid.minGroup K) :=
  MonoidHom.mk' (fun m => ⟨jHom m, jHom_mem_minGroup m⟩) (fun a b => Subtype.ext (map_mul jHom a b))

def jHomAdj : Matrix.SpecialLinearGroup (Fin 2) K →* ModGL .E7 K :=
  (adjointGroup .E7 K).subtype.comp ((e7Equiv (K := K)).toMonoidHom.comp jHomMin)

def highRootSL2Hom : Matrix.SpecialLinearGroup (Fin 2) K →* ModGL .E7 K :=
  (CFSG.LieType.Chevalley.rootSL2 .E7 K theta).comp (MulAut.conj sl2W).toMonoidHom

theorem jHomAdj_slLower (e : K) :
    jHomAdj (MinData.Valid.slLower K e) = highRootSL2Hom (MinData.Valid.slLower K e) := by
  have hX : jHomMin (MinData.Valid.slLower K e) = e7Data_valid.xm K theta e :=
    Subtype.ext (xu_theta e).symm
  have hE : (e7Equiv (K := K)) (e7Data_valid.xm K theta e) = EPilot.pinnedElt .E7 theta e :=
    ((e7Equiv (K := K)).symm_apply_eq.1 (e7Psi_pinnedElt' isRoot_theta e)).symm
  have hG : highRootSL2Hom (MinData.Valid.slLower K e) =
      CFSG.LieType.Chevalley.rootSL2 .E7 K theta (CFSG.LieType.Chevalley.uSL (-e)) := by
    unfold highRootSL2Hom
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hv : MinData.Valid.slLower K e = CFSG.LieType.Chevalley.vSL e := rfl
    rw [hv, sl2W_mul_vSL e, mul_inv_cancel_right]
  have hU : CFSG.LieType.Chevalley.rootSL2 .E7 K theta (CFSG.LieType.Chevalley.uSL (-e)) =
      CFSG.Blueprint.Chevalley.pinnedX .E7 K theta (-e) :=
    CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo isRoot_theta (-e)
  rw [hG, hU, show -e = e from CharTwo.neg_eq e]
  show (adjointGroup .E7 K).subtype ((e7Equiv (K := K)) (jHomMin (MinData.Valid.slLower K e))) = _
  rw [hX, hE]
  rfl

theorem jHomAdj_slUpper (a : K) :
    jHomAdj (MinData.Valid.slUpper K a) = highRootSL2Hom (MinData.Valid.slUpper K a) := by
  have hX : jHomMin (MinData.Valid.slUpper K a) = e7Data_valid.xm K (-theta) a :=
    Subtype.ext (xu_neg_theta a).symm
  have hE : (e7Equiv (K := K)) (e7Data_valid.xm K (-theta) a) =
      EPilot.pinnedElt .E7 (-theta) a :=
    ((e7Equiv (K := K)).symm_apply_eq.1 (e7Psi_pinnedElt' (isRoot_neg isRoot_theta) a)).symm
  have hG : highRootSL2Hom (MinData.Valid.slUpper K a) =
      CFSG.LieType.Chevalley.rootSL2 .E7 K theta (CFSG.LieType.Chevalley.vSL (-a)) := by
    unfold highRootSL2Hom
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hv : MinData.Valid.slUpper K a = CFSG.LieType.Chevalley.uSL a := rfl
    rw [hv, sl2W_mul_uSL a, mul_inv_cancel_right]
  have hV : CFSG.LieType.Chevalley.rootSL2 .E7 K theta (CFSG.LieType.Chevalley.vSL (-a)) =
      CFSG.Blueprint.Chevalley.pinnedX .E7 K (-theta) (-a) :=
    CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo isRoot_theta (-a)
  rw [hG, hV, show -a = a from CharTwo.neg_eq a]
  show (adjointGroup .E7 K).subtype ((e7Equiv (K := K)) (jHomMin (MinData.Valid.slUpper K a))) = _
  rw [hX, hE]
  rfl

theorem jHomAdj_eq_highRootSL2Hom (m : Matrix.SpecialLinearGroup (Fin 2) K) : jHomAdj m = highRootSL2Hom m := by
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod m
  simp only [map_mul]
  rw [jHomAdj_slLower e, jHomAdj_slUpper a, jHomAdj_slLower b, jHomAdj_slUpper c]

theorem highRootSL2Hom_injective : Function.Injective (highRootSL2Hom (K := K)) := by
  intro x y hxy
  unfold highRootSL2Hom at hxy
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxy
  have h2 := CFSG.SeitzReduction.E6Pilot.rootSL2_highRoot_injective (τ := .E7) hxy
  exact mul_left_cancel (mul_right_cancel h2)

theorem jHomMin_injective : Function.Injective (jHomMin (K := K)) := by
  intro x y hxy
  have h1 : jHomAdj x = jHomAdj y := by
    simp only [jHomAdj, MonoidHom.comp_apply, hxy]
  exact highRootSL2Hom_injective ((jHomAdj_eq_highRootSL2Hom x).symm.trans (h1.trans (jHomAdj_eq_highRootSL2Hom y)))

theorem jHom_injective : Function.Injective (jHom (K := K)) := by
  intro x y hxy
  apply jHomMin_injective
  exact Subtype.ext hxy

theorem jHomAdj_HSL (c : Kˣ) :
    jHomAdj (CFSG.LieType.Chevalley.HSL c) = rootDiagUnit .E7 (EPilot.highDiag .E7 c⁻¹) := by
  rw [jHomAdj_eq_highRootSL2Hom]
  unfold highRootSL2Hom
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [sl2W_mul_HSL c, mul_inv_cancel_right]
  exact CFSG.SeitzReduction.E6Pilot.rootSL2_highRoot_HSL (Or.inr (Or.inl rfl)) c⁻¹

theorem exists_mul_of_mem_sup_of_commute {G : Type*} [Group G] {H N : Subgroup G}
    (hc : ∀ h ∈ H, ∀ n ∈ N, Commute h n) {x : G} (hx : x ∈ H ⊔ N) :
    ∃ h ∈ H, ∃ n ∈ N, h * n = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, N.one_mem, mul_one y⟩
    · exact ⟨1, H.one_mem, y, hy, one_mul y⟩
  · exact ⟨1, H.one_mem, 1, N.one_mem, mul_one 1⟩
  · rintro _ _ _ _ ⟨h₁, hh₁, n₁, hn₁, rfl⟩ ⟨h₂, hh₂, n₂, hn₂, rfl⟩
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, n₁ * n₂, N.mul_mem hn₁ hn₂, ?_⟩
    have hcomm : h₂ * n₁ = n₁ * h₂ := (hc h₂ hh₂ n₁ hn₁).eq
    calc h₁ * h₂ * (n₁ * n₂) = h₁ * (h₂ * n₁) * n₂ := by simp only [mul_assoc]
      _ = h₁ * (n₁ * h₂) * n₂ := by rw [hcomm]
      _ = h₁ * n₁ * (h₂ * n₂) := by simp only [mul_assoc]
  · rintro _ _ ⟨h, hh, n, hn, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, n⁻¹, N.inv_mem hn, ?_⟩
    rw [mul_inv_rev]
    exact (hc h hh n hn).inv_inv.eq

theorem commute_highTorusLine {s t : ModGL .E7 K} (hs : s ∈ EPilot.highTorusLine .E7 K)
    (ht : t ∈ EPilot.highTorusLine .E7 K) : Commute s t := by
  obtain ⟨c, rfl⟩ := EPilot.mem_highTorusLine.1 hs
  obtain ⟨d, rfl⟩ := EPilot.mem_highTorusLine.1 ht
  unfold Commute SemiconjBy
  rw [← CFSG.LieType.Chevalley.rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_mul,
    ← EPilot.highDiag_mul, ← EPilot.highDiag_mul,
    mul_comm]

theorem highTorusLine_le_highRootSL2_E7 :
    EPilot.highTorusLine .E7 K ≤ EPilot.highRootSL2 .E7 K := by
  intro t ht
  obtain ⟨c, rfl⟩ := EPilot.mem_highTorusLine.1 ht
  rw [← CFSG.SeitzReduction.E6Pilot.rootSL2_highRoot_HSL (Or.inr (Or.inl rfl)) c,
    ← CFSG.SeitzReduction.E6Pilot.range_rootSL2_highRoot]
  exact MonoidHom.mem_range.2 ⟨CFSG.LieType.Chevalley.HSL c, rfl⟩

theorem odd_orderOf_highTorusLine {f : ℕ} (hKc : Nat.card K = 2 ^ f)
    {t : ↥(adjointGroup .E7 K)}
    (ht : t ∈ (EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K)) :
    Odd (orderOf t) :=
  Odd.of_dvd_nat (CFSG.SeitzReduction.E7Pilot.odd_card_highTorusLine_E7 hKc)
    (Subgroup.orderOf_dvd_natCard _ ht)

theorem exists_card_eq_two_pow : ∃ f : ℕ, Nat.card K = 2 ^ f := by
  haveI := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem even_natCard_of_charP_two : Even (Nat.card K) := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact Nat.even_iff.2 ((FiniteField.even_card_iff_char_two (F := K)).1 (ringChar.eq K 2))

theorem centralizer_nonsplit_J_Lam (hq : 4 ≤ Nat.card K) {v : (Module.End K (V K))ˣ} (hvJ : v ∈ Jgrp K)
    (hordv : orderOf v = Nat.card K + 1)
    {e : (Module.End K (V K))ˣ} (he : e ∈ EGrp K) (hcomm : e * v = v * e) :
    ∃ j ∈ Jgrp K, ∃ l ∈ Lam K, e = j * l ∧ j * v = v * j ∧ Odd (orderOf j) := by
  have hev : Even (Nat.card K) := even_natCard_of_charP_two
  have hvE : v ∈ e7Data_valid.minGroup K := Jgrp_le_E hvJ
  obtain ⟨v', hv'⟩ : ∃ x : ↥(adjointGroup .E7 K), x = (e7Equiv (K := K)) ⟨v, hvE⟩ := ⟨_, rfl⟩
  obtain ⟨e', he'⟩ : ∃ x : ↥(adjointGroup .E7 K), x = (e7Equiv (K := K)) ⟨e, he⟩ := ⟨_, rfl⟩
  have hcomm' : e' * v' = v' * e' := by
    rw [hv', he', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hv'J : v' ∈ (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) := by
    rw [hv']
    exact (mem_Jgrp_iff_equiv ⟨v, hvE⟩).1 hvJ
  have hordv' : orderOf v' = Nat.card K + 1 := by
    rw [hv', ← hordv]
    have h1 := orderOf_injective (e7Equiv (K := K)).toMonoidHom (e7Equiv (K := K)).injective
      (⟨v, hvE⟩ : ↥(e7Data_valid.minGroup K))
    simp only [MulEquiv.coe_toMonoidHom] at h1
    rw [h1]
    exact Subgroup.orderOf_mk v hvE
  have hX : Nat.card (Subgroup.zpowers v') = Nat.card K + 1 := by
    rw [Nat.card_zpowers, hordv']
  have hXJ : Subgroup.zpowers v' ≤ (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) :=
    Subgroup.zpowers_le.2 hv'J
  have hcyc : IsCyclic (Subgroup.zpowers v') := Subgroup.isCyclic_zpowers _
  have hvc : Commute v' e' := hcomm'.symm
  have hc : e' ∈ Subgroup.centralizer
      ((Subgroup.zpowers v' : Subgroup ↥(adjointGroup .E7 K)) : Set ↥(adjointGroup .E7 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hvc.zpow_left k).eq
  obtain ⟨y, hyX, d, hd, hed⟩ :=
    CFSG.SeitzReduction.E7Pilot.exists_mul_of_mem_centralizer_nonsplit_E7 hq hXJ hX hcyc hc
  have hem : (⟨e, he⟩ : ↥(e7Data_valid.minGroup K)) =
      (e7Equiv (K := K)).symm y * (e7Equiv (K := K)).symm d := by
    have h1 : (⟨e, he⟩ : ↥(e7Data_valid.minGroup K)) = (e7Equiv (K := K)).symm e' := by
      rw [he']
      exact ((e7Equiv (K := K)).symm_apply_apply _).symm
    rw [h1, hed, map_mul]
  have hjy : y * v' = v' * y := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyX
    rw [← hk]
    exact ((Commute.refl v').zpow_left k).eq
  have hjv : (e7Equiv (K := K)).symm y * (⟨v, hvE⟩ : ↥(e7Data_valid.minGroup K)) =
      (⟨v, hvE⟩ : ↥(e7Data_valid.minGroup K)) * (e7Equiv (K := K)).symm y := by
    apply (e7Equiv (K := K)).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hv']
    exact hjy
  have hodd : Odd (Nat.card K + 1) := hev.add_one
  have hdiv : orderOf y ∣ Nat.card K + 1 := by
    rw [← hX]
    exact Subgroup.orderOf_dvd_natCard _ hyX
  have hjord : orderOf (((e7Equiv (K := K)).symm y : ↥(e7Data_valid.minGroup K)) :
      (Module.End K (V K))ˣ) = orderOf y := by
    rw [Subgroup.orderOf_coe]
    have h1 := orderOf_injective (e7Equiv (K := K)).toMonoidHom (e7Equiv (K := K)).injective
      ((e7Equiv (K := K)).symm y)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  refine ⟨((e7Equiv (K := K)).symm y : ↥(e7Data_valid.minGroup K)),
    (mem_Jgrp_iff_equiv _).2 (by rw [MulEquiv.apply_symm_apply]; exact hXJ hyX), 
    ((e7Equiv (K := K)).symm d : ↥(e7Data_valid.minGroup K)),
    (mem_Lam_iff_equiv _).2 (by rw [MulEquiv.apply_symm_apply]; exact hd), ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hem
  · exact congrArg Subtype.val hjv
  · rw [hjord]
    exact Odd.of_dvd_nat hodd hdiv

theorem centralizer_split_J_Lam (hq : 4 ≤ Nat.card K) {v : (Module.End K (V K))ˣ} (hvJ : v ∈ Jgrp K)
    (hordv : orderOf v = Nat.card K - 1)
    {e : (Module.End K (V K))ˣ} (he : e ∈ EGrp K) (hcomm : e * v = v * e) :
    ∃ j ∈ Jgrp K, ∃ l ∈ Lam K, e = j * l ∧ j * v = v * j ∧ Odd (orderOf j) := by
  obtain ⟨f, hKc⟩ := exists_card_eq_two_pow (K := K)
  rw [Jgrp_eq_range] at hvJ
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 hvJ
  have hmord : orderOf m = Nat.card K - 1 := by
    have h1 : orderOf (jHom m) = orderOf m := orderOf_injective jHom jHom_injective m
    rw [hm, hordv] at h1
    exact h1.symm
  obtain ⟨g, c, hcord, hgc⟩ := sl2_conj_diag hq hmord
  have hw : jHom g ∈ Jgrp K := by
    rw [Jgrp_eq_range]
    exact MonoidHom.mem_range.2 ⟨g, rfl⟩
  have hw' : jHom g ∈ e7Data_valid.minGroup K := jHom_mem_minGroup g
  have hwv : jHom g * v * (jHom g)⁻¹ = jHom (sl2Diag c) := by
    rw [← hm, ← hgc, map_mul, map_mul, map_inv]
  obtain ⟨vs, hvs⟩ : ∃ x : ↥(e7Data_valid.minGroup K),
      x = jHomMin (K := K) (sl2Diag c) := ⟨_, rfl⟩
  have hvsG : (vs : (Module.End K (V K))ˣ) = jHom (sl2Diag c) := by
    rw [hvs]
    rfl
  obtain ⟨s, hs⟩ : ∃ x : ↥(adjointGroup .E7 K), x =
      ⟨rootDiagUnit .E7 (EPilot.highDiag .E7 c⁻¹),
        CFSG.SeitzReduction.E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup
          (Or.inr (Or.inl rfl)) c⁻¹⟩ := ⟨_, rfl⟩
  have hsvs : (e7Equiv (K := K)) vs = s := by
    rw [hvs, hs]
    apply Subtype.ext
    have h := jHomAdj_HSL c
    simp only [jHomAdj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype] at h
    rw [sl2Diag_eq_HSL]
    exact h
  have hsT : s ∈ (EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) := by
    rw [hs, Subgroup.mem_subgroupOf]
    exact EPilot.rootDiagUnit_highDiag_mem_highTorusLine c⁻¹
  have hAT : Subgroup.zpowers s ≤ (EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K) :=
    Subgroup.zpowers_le.2 hsT
  have hcA : (⟨rootDiagUnit .E7 (EPilot.highDiag .E7 c⁻¹),
      CFSG.SeitzReduction.E6Pilot.rootDiagUnit_highDiag_mem_adjointGroup
        (Or.inr (Or.inl rfl)) c⁻¹⟩ : ↥(adjointGroup .E7 K)) ∈ Subgroup.zpowers s := by
    rw [← hs]
    exact Subgroup.mem_zpowers s
  have hc3 : 3 ≤ orderOf c⁻¹ := by
    rw [orderOf_inv, hcord]
    omega
  have hcen := CFSG.SeitzReduction.E7Pilot.centralizer_split_E7 hc3 hAT hcA
  obtain ⟨e1, he1⟩ : ∃ x : ↥(e7Data_valid.minGroup K),
      x = ⟨jHom g * e * (jHom g)⁻¹, mul_mem (mul_mem hw' he) (inv_mem hw')⟩ := ⟨_, rfl⟩
  have hGL : (jHom g * e * (jHom g)⁻¹) * jHom (sl2Diag c) =
      jHom (sl2Diag c) * (jHom g * e * (jHom g)⁻¹) := by
    rw [← hwv]
    calc (jHom g * e * (jHom g)⁻¹) * (jHom g * v * (jHom g)⁻¹)
        = jHom g * (e * v) * (jHom g)⁻¹ := by group
      _ = jHom g * (v * e) * (jHom g)⁻¹ := by rw [hcomm]
      _ = (jHom g * v * (jHom g)⁻¹) * (jHom g * e * (jHom g)⁻¹) := by group
  have hcomm1 : e1 * vs = vs * e1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he1, hvsG]
    exact hGL
  have hcommA : (e7Equiv (K := K)) e1 * s = s * (e7Equiv (K := K)) e1 := by
    rw [← hsvs, ← map_mul, ← map_mul, hcomm1]
  have hcen_mem : (e7Equiv (K := K)) e1 ∈ Subgroup.centralizer
      ((Subgroup.zpowers s : Subgroup ↥(adjointGroup .E7 K)) : Set ↥(adjointGroup .E7 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hcomm2 : Commute s ((e7Equiv (K := K)) e1) := hcommA.symm
    exact (hcomm2.zpow_left k).eq
  rw [hcen] at hcen_mem
  have hTD : ∀ h ∈ (EPilot.highTorusLine .E7 K).subgroupOf (adjointGroup .E7 K),
      ∀ n ∈ EPilot.perpLevi .E7 K, Commute h n := fun h hh n hn =>
    (Subgroup.mem_centralizer_iff.1
      (CFSG.SeitzReduction.E7Pilot.highTorusLine_le_centralizer_perpLevi_E7 (K := K) hh) n hn).symm
  obtain ⟨t, ht, d, hd, htd⟩ := exists_mul_of_mem_sup_of_commute hTD hcen_mem
  have htH : (t : ModGL .E7 K) ∈ EPilot.highTorusLine .E7 K := Subgroup.mem_subgroupOf.1 ht
  have hsH : (s : ModGL .E7 K) ∈ EPilot.highTorusLine .E7 K := Subgroup.mem_subgroupOf.1 hsT
  have htJ : t ∈ (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) :=
    Subgroup.mem_subgroupOf.2 (highTorusLine_le_highRootSL2_E7 htH)
  have hTS : t * s = s * t := Subtype.ext (commute_highTorusLine htH hsH).eq
  have hpre : (e7Equiv (K := K)).symm (e7Equiv (K := K) e1) = e1 :=
    (e7Equiv (K := K)).symm_apply_apply e1
  rw [← htd, map_mul] at hpre
  obtain ⟨J1, hJ1⟩ : ∃ x : (Module.End K (V K))ˣ,
      x = ((e7Equiv (K := K)).symm t : ↥(e7Data_valid.minGroup K)) := ⟨_, rfl⟩
  obtain ⟨L1, hL1⟩ : ∃ x : (Module.End K (V K))ˣ,
      x = ((e7Equiv (K := K)).symm d : ↥(e7Data_valid.minGroup K)) := ⟨_, rfl⟩
  have hl : L1 ∈ Lam K := by
    rw [hL1]
    exact (mem_Lam_iff_equiv _).2 (by rw [MulEquiv.apply_symm_apply]; exact hd)
  have hj1 : J1 ∈ Jgrp K := by
    rw [hJ1]
    exact (mem_Jgrp_iff_equiv _).2 (by rw [MulEquiv.apply_symm_apply]; exact htJ)
  have hwe : jHom g * e * (jHom g)⁻¹ = J1 * L1 := by
    have h1 : (e1 : (Module.End K (V K))ˣ) = J1 * L1 := by
      rw [← hpre, hJ1, hL1]
      rfl
    rw [he1] at h1
    exact h1
  have hLw : L1 * jHom g = jHom g * L1 := Lam_commute_J hl hw
  have hv_eq : v = (jHom g)⁻¹ * jHom (sl2Diag c) * jHom g := by
    rw [← hwv]
    group
  have hj1vs : (e7Equiv (K := K)).symm t * vs = vs * (e7Equiv (K := K)).symm t := by
    apply (e7Equiv (K := K)).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hsvs]
    exact hTS
  have hj1G : J1 * jHom (sl2Diag c) = jHom (sl2Diag c) * J1 := by
    rw [← hvsG, hJ1]
    exact congrArg Subtype.val hj1vs
  refine ⟨(jHom g)⁻¹ * J1 * jHom g, mul_mem (mul_mem (inv_mem hw) hj1) hw, L1, hl, ?_, ?_, ?_⟩
  · calc e = (jHom g)⁻¹ * (jHom g * e * (jHom g)⁻¹) * jHom g := by group
      _ = (jHom g)⁻¹ * (J1 * L1) * jHom g := by rw [hwe]
      _ = ((jHom g)⁻¹ * J1 * jHom g) * ((jHom g)⁻¹ * L1 * jHom g) := by group
      _ = ((jHom g)⁻¹ * J1 * jHom g) * L1 := by
          congr 1
          rw [mul_assoc, hLw, inv_mul_cancel_left]
  · calc ((jHom g)⁻¹ * J1 * jHom g) * v
        = (jHom g)⁻¹ * (J1 * jHom (sl2Diag c)) * jHom g := by rw [hv_eq]; group
      _ = (jHom g)⁻¹ * (jHom (sl2Diag c) * J1) * jHom g := by rw [hj1G]
      _ = v * ((jHom g)⁻¹ * J1 * jHom g) := by rw [hv_eq]; group
  · have hconj := orderOf_conj_eq_orderOf ((jHom g)⁻¹) J1
    rw [inv_inv] at hconj
    rw [hconj, hJ1]
    have h2 := orderOf_injective (e7Equiv (K := K)).toMonoidHom (e7Equiv (K := K)).injective
      ((e7Equiv (K := K)).symm t)
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h2
    rw [Subgroup.orderOf_coe, ← h2]
    exact odd_orderOf_highTorusLine hKc ht

theorem centralizer_le_J_Lam (hq : 4 ≤ Nat.card K) {v : (Module.End K (V K))ˣ} (hvJ : v ∈ Jgrp K)
    (hord : orderOf v = Nat.card K - 1 ∨ orderOf v = Nat.card K + 1)
    {e : (Module.End K (V K))ˣ} (he : e ∈ EGrp K) (hcomm : e * v = v * e) :
    ∃ j ∈ Jgrp K, ∃ l ∈ Lam K, e = j * l ∧ j * v = v * j ∧ Odd (orderOf j) := by
  rcases hord with h | h
  · exact centralizer_split_J_Lam hq hvJ h he hcomm
  · exact centralizer_nonsplit_J_Lam hq hvJ h he hcomm

end CFSG.RankThree.GF2n.Smith81.E7Model
