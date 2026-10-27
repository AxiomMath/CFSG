module

public import CFSG.Quasithin.SteinbergBSQTEInvolutionSylow
public import CFSG.LieType.SteinbergBROddLinearThreeInvolution
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup CFSG.Wreathed.OddLinearThreeCentralizerCore QTEInvolutionSylow

namespace QTEOddLinearThree

variable {F : Type*} [Field F]

theorem matrixAction_mul (g h : SL3 F) (v : Fin 3 → F) :
    matrixAction F (g * h) v = matrixAction F g (matrixAction F h v) := by
  change Matrix.SpecialLinearGroup.toLin' (g * h) v = _
  rw [map_mul]
  rfl

theorem matrixAction_one (v : Fin 3 → F) : matrixAction F 1 v = v := by
  change Matrix.SpecialLinearGroup.toLin' 1 v = v
  rw [map_one]
  rfl

theorem matrixAction_inv_apply (g : SL3 F) (v : Fin 3 → F) :
    matrixAction F g (matrixAction F g⁻¹ v) = v := by
  rw [← matrixAction_mul, mul_inv_cancel, matrixAction_one]

theorem matrixAction_apply_inv (g : SL3 F) (v : Fin 3 → F) :
    matrixAction F g⁻¹ (matrixAction F g v) = v := by
  rw [← matrixAction_mul, inv_mul_cancel, matrixAction_one]

@[expose] def preservingFixing (P Q : Submodule F (Fin 3 → F)) : Subgroup (SL3 F) where
  carrier := {g | (∀ v, matrixAction F g v ∈ P ↔ v ∈ P) ∧ ∀ v ∈ Q, matrixAction F g v = v}
  one_mem' := ⟨fun v => by rw [matrixAction_one], fun v _ => matrixAction_one v⟩
  mul_mem' := by
    rintro g h ⟨hgP, hgQ⟩ ⟨hhP, hhQ⟩
    exact ⟨fun v => by rw [matrixAction_mul, hgP, hhP],
      fun v hv => by rw [matrixAction_mul, hhQ v hv, hgQ v hv]⟩
  inv_mem' := by
    rintro g ⟨hgP, hgQ⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [← hgP, matrixAction_inv_apply]
    · calc matrixAction F g⁻¹ v = matrixAction F g⁻¹ (matrixAction F g v) := by rw [hgQ v hv]
        _ = v := matrixAction_apply_inv g v

variable [Finite F]

theorem preservingFixing_le_centralizer (hF : Odd (Nat.card F)) {z : SL3 F} (hz : orderOf z = 2) :
    preservingFixing (minusSpace (matrixAction F z).toLinearMap)
        (plusSpace (matrixAction F z).toLinearMap) ≤ centralizer ({z} : Set (SL3 F)) := by
  intro g hg
  obtain ⟨hgP, hgQ⟩ := hg
  have hcompl := involution_spaces_isCompl (two_ne_zero F hF) (matrixAction F z).toLinearMap
    (matrixAction_involutive F z hz)
  rw [mem_centralizer_singleton_iff]
  apply Matrix.SpecialLinearGroup.toLin'_injective
  refine LinearEquiv.ext fun v => ?_
  change matrixAction F (g * z) v = matrixAction F (z * g) v
  obtain ⟨x, hx, y, hy, rfl⟩ :=
    Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hzx : matrixAction F z x = -x := by
    have := Module.End.mem_eigenspace_iff.1 hx
    rw [neg_one_smul] at this
    exact this
  have hzy : matrixAction F z y = y := by
    have := Module.End.mem_eigenspace_iff.1 hy
    rw [one_smul] at this
    exact this
  have hgx : matrixAction F g x ∈ minusSpace (matrixAction F z).toLinearMap := (hgP x).2 hx
  have hzgx : matrixAction F z (matrixAction F g x) = -matrixAction F g x := by
    have := Module.End.mem_eigenspace_iff.1 hgx
    rw [neg_one_smul] at this
    exact this
  rw [matrixAction_mul, matrixAction_mul, map_add, map_add, hzx, hzy, map_add, map_neg,
    hgQ y hy, map_add, hzgx, hzy]

end QTEOddLinearThree

open QTEOddLinearThree

variable {F : Type*} [Field F] [Finite F]

theorem odd_linear_three_involution_and_Sylow_structure (hF : Odd (Nat.card F))
    (hq : 5 ≤ Nat.card F) (D : Subgroup (SL3 F)) [D.Normal]
    (hD : D ≤ CFSG.LinearGroups.scalarSubgroup 3 F) :
    (∀ T : Sylow 2 (SL3 F ⧸ D), IsCyclic (center (T : Subgroup (SL3 F ⧸ D))) ∧
      ∀ E : Subgroup (SL3 F ⧸ D), E ≤ T → IsElementaryAbelian 2 E → Nat.card E ≤ 4) ∧
    ∀ t : SL3 F ⧸ D, orderOf t = 2 →
      ∃ z : SL3 F, (orderOf z = 2 ∧ QuotientGroup.mk' D z = t) ∧
        (∀ w : SL3 F, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z) ∧
        Module.finrank F (minusSpace (matrixAction F z).toLinearMap) = 2 ∧
        Module.finrank F (plusSpace (matrixAction F z).toLinearMap) = 1 ∧
        (perfectResidual (centralizer ({t} : Set (SL3 F ⧸ D)))).map
            (centralizer ({t} : Set (SL3 F ⧸ D))).subtype =
          (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D) ∧
        Function.Injective ((QuotientGroup.mk' D).comp
          (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).subtype) ∧
        Nonempty (↥((preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D)) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F) ∧
        t ∈ (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D) ∧
        ∀ l ∈ (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D),
          l * t = t * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD' : D ≤ center (SL3 F) := hD.trans CFSG.LinearGroups.scalarSubgroup_eq_center.le
  have hq3 : 3 ≤ Nat.card F := by omega
  have hcenK : ∀ (z : SL3 F) (hz : orderOf z = 2) (t : SL3 F ⧸ D)
      (hzt : QuotientGroup.mk' D z = t),
      (targetQuotientCentralizer F hF D z hz t hzt).ker ≤ center _ := by
    intro z hz t hzt a ha
    rw [targetQuotientCentralizer_ker] at ha
    obtain ⟨c, -, -, rfl⟩ := (matrixQuotientCentralizer_mem_ker_iff hF hD' hz).1 ha
    refine mem_center_iff.2 fun g => LinearEquiv.ext fun v => ?_
    change g ((c : Fˣ) • v) = (c : Fˣ) • g v
    rw [Units.smul_def, Units.smul_def, map_smul]
  refine ⟨fun T => ?_, fun t ht => ?_⟩
  ·
    by_cases hT1 : Nat.card (T : Subgroup (SL3 F ⧸ D)) = 1
    · have : Subsingleton (T : Subgroup (SL3 F ⧸ D)) := (Nat.card_eq_one_iff_unique.1 hT1).1
      refine ⟨isCyclic_of_subsingleton, fun E hET _ => ?_⟩
      have := card_le_of_le hET
      omega
    have hnt : Nontrivial (T : Subgroup (SL3 F ⧸ D)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by have := Nat.card_pos (α := T); omega)
    have hZ2 : IsPGroup 2 (center (T : Subgroup (SL3 F ⧸ D))) :=
      T.isPGroup'.to_subgroup (center _)
    have hZnt := T.isPGroup'.center_nontrivial
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.2 hZnt).ne' hk
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := center (T : Subgroup (SL3 F ⧸ D))) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    have ht : orderOf ((x : T) : SL3 F ⧸ D) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hTt : (T : Subgroup (SL3 F ⧸ D)) ≤ centralizer ({((x : T) : SL3 F ⧸ D)} : Set _) :=
      fun s hs => mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_center_iff.1 x.2 ⟨s, hs⟩))
    obtain ⟨z, hz, hzt, -, hdm, -, -, -, -, hsurj, -, -⟩ :=
      odd_linear_three_involution_centralizer_core F hF hq3 D hD' _ ht
    have hodd : Odd (Nat.card (targetQuotientCentralizer F hF D z hz _ hzt).ker) := by
      rw [targetQuotientCentralizer_ker]
      exact matrixQuotientKernel_odd F hF D hD' z hz
    have := finite_linearEquiv (E := F) (W := minusSpace (matrixAction F z).toLinearMap)
    obtain ⟨hH1, hH2⟩ := linear_two_twoLocal hF hdm
    obtain ⟨h1, h2⟩ := sylow_transfer _ hsurj (hcenK z hz _ hzt) hodd hH1 hH2 T hTt
    refine ⟨h1, fun E hET hE => h2 E hET (fun a ha b hb => ?_) fun a ha => ?_⟩
    · exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · rw [← sq]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  ·
    obtain ⟨z, hz, hzt, huniq, hdm, hdp, -, -, hcoe, hsurj, hker, -⟩ :=
      odd_linear_three_involution_centralizer_core F hF hq3 D hD' t ht
    set φ := targetQuotientCentralizer F hF D z hz t hzt with hφ
    let SLk := (LinearEquiv.det : (minusSpace (matrixAction F z).toLinearMap ≃ₗ[F]
      minusSpace (matrixAction F z).toLinearMap) →* Fˣ).ker
    have hcompl := involution_spaces_isCompl (two_ne_zero F hF) (matrixAction F z).toLinearMap
      (matrixAction_involutive F z hz)
    obtain ⟨y₀, hy₀, hy₀0⟩ : ∃ y₀ ∈ plusSpace (matrixAction F z).toLinearMap, y₀ ≠ 0 :=
      Submodule.exists_mem_ne_zero_of_ne_bot fun h => by
        rw [h, finrank_bot] at hdp
        exact absurd hdp (by norm_num)
    have hinj : Function.Injective (φ.comp SLk.subtype) := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, ha⟩ h
      obtain ⟨c, hc3, -, rfl⟩ := (hker a).1 h
      have hc2 : c ^ 2 = 1 := (minus_scalar_det F hF z hz c).symm.trans ha
      have hc1 : c = 1 := by
        calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
          _ = 1 := by rw [hc3, hc2, inv_one, one_mul]
      subst hc1
      exact Subtype.ext (LinearEquiv.ext fun x => one_smul Fˣ x)
    have hJr : (φ.comp SLk.subtype).range = SLk.map φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    let b : Module.Basis (Fin 2) F (minusSpace (matrixAction F z).toLinearMap) :=
      Module.finBasisOfFinrankEq F _ hdm
    let eJ : SLk.map φ ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      ((MulEquiv.subgroupCongr hJr).symm.trans (MonoidHom.ofInjective hinj).symm).trans
        (CFSG.LieType.SteinbergBR.OddLinearThreeInv.slEquiv b)
    have hJn : (SLk.map φ).Normal := (MonoidHom.normal_ker _).map φ hsurj
    have h4 : ∃ s : Finset F, s.card = 4 := by
      have := Fintype.ofFinite F
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
      exact ⟨s, hs⟩
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect h4
    have hJperf : Group.IsPerfect (SLk.map φ) :=
      Group.IsPerfect.ofSurjective (f := eJ.symm.toMonoidHom) eJ.symm.surjective
    have hquot : Group.IsSolvable (centralizer ({t} : Set (SL3 F ⧸ D)) ⧸ SLk.map φ) := by
      refine Group.isSolvable_of_comm fun x y => ?_
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          obtain ⟨a, rfl⟩ := hsurj x
          obtain ⟨c, rfl⟩ := hsurj y
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          refine ⟨(a * c)⁻¹ * (c * a), ?_, by rw [map_mul, map_inv, map_mul, map_mul]⟩
          change LinearEquiv.det ((a * c)⁻¹ * (c * a)) = 1
          rw [map_mul, map_inv, map_mul, map_mul, mul_comm (LinearEquiv.det c), inv_mul_cancel]
    have hDinf : perfectResidual (centralizer ({t} : Set (SL3 F ⧸ D))) = SLk.map φ :=
      le_antisymm ((CFSG.perfect_residual_characterization.2.2.2.2.1 (SLk.map φ)).1 hquot)
        ((CFSG.perfect_residual_transport (MonoidHom.id _)).2.2 _ hJperf)
    have hblock : SLk.map ((centralizer ({z} : Set (SL3 F))).subtype.comp
        (matrixCentralizerEquiv F hF z hz).toMonoidHom) =
        preservingFixing (minusSpace (matrixAction F z).toLinearMap)
          (plusSpace (matrixAction F z).toLinearMap) := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        change (matrixCentralizerEquiv F hF z hz a : SL3 F) ∈ preservingFixing _ _
        have hdet : (a.det⁻¹ : Fˣ) = 1 := by
          rw [show a.det = 1 from ha, inv_one]
        have hcomm : ∀ v, (matrixAction F z).toLinearMap
            (matrixAction F (matrixCentralizerEquiv F hF z hz a : SL3 F) v) =
            matrixAction F (matrixCentralizerEquiv F hF z hz a : SL3 F)
              ((matrixAction F z).toLinearMap v) := by
          intro v
          have h := mem_centralizer_singleton_iff.1 (matrixCentralizerEquiv F hF z hz a).2
          change matrixAction F z (matrixAction F _ v) = matrixAction F _ (matrixAction F z v)
          rw [← matrixAction_mul, ← matrixAction_mul, h]
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · have hmap := commuting_map_eigenspace (matrixAction F z).toLinearMap
            (matrixAction F (matrixCentralizerEquiv F hF z hz a : SL3 F)) hcomm (-1)
          constructor
          · intro hv
            have hmem : matrixAction F (matrixCentralizerEquiv F hF z hz a : SL3 F) v ∈
                (Module.End.eigenspace (matrixAction F z).toLinearMap (-1)).map
                  (matrixAction F (matrixCentralizerEquiv F hF z hz a : SL3 F)).toLinearMap := by
              rw [hmap]
              exact hv
            obtain ⟨w, hw, hwv⟩ := hmem
            rw [← (matrixAction F _).injective hwv]
            exact hw
          · intro hv
            have := matrixCentralizerEquiv_minus F hF z hz a ⟨v, hv⟩
            rw [this]
            exact (a ⟨v, hv⟩).2
        · have := matrixCentralizerEquiv_plus F hF z hz a ⟨v, hv⟩
          rw [this, hdet, Units.val_one, one_smul]
      · intro g hg
        have hgC := preservingFixing_le_centralizer hF hz hg
        obtain ⟨a, ha⟩ := (matrixCentralizerEquiv F hF z hz).surjective ⟨g, hgC⟩
        refine ⟨a, ?_, by rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ha]; rfl⟩
        have hplus := matrixCentralizerEquiv_plus F hF z hz a ⟨y₀, hy₀⟩
        rw [ha] at hplus
        change matrixAction F g y₀ = _ at hplus
        rw [hg.2 y₀ hy₀] at hplus
        have h1 : ((a.det⁻¹ : Fˣ) : F) = 1 := by
          have h' : (1 : F) • y₀ = ((a.det⁻¹ : Fˣ) : F) • y₀ := by rw [one_smul]; exact hplus
          exact (smul_left_injective F hy₀0 h').symm
        change a.det = 1
        have h1' : (a.det⁻¹ : Fˣ) = 1 := Units.ext h1
        rw [inv_eq_one] at h1'
        exact h1'
    have hL : (SLk.map φ).map (centralizer ({t} : Set (SL3 F ⧸ D))).subtype =
        (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
          (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D) := by
      rw [← hblock, Subgroup.map_map, Subgroup.map_map]
      congr 1
    have hzB : z ∈ preservingFixing (minusSpace (matrixAction F z).toLinearMap)
        (plusSpace (matrixAction F z).toLinearMap) := by
      refine ⟨fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun v hv => ?_⟩
      · have h := Module.End.mem_eigenspace_iff.1 hv
        rw [neg_one_smul] at h
        change matrixAction F z (matrixAction F z v) = -matrixAction F z v at h
        rw [matrixAction_involutive F z hz v] at h
        rw [h]
        exact neg_mem hv
      · have h := Module.End.mem_eigenspace_iff.1 hv
        rw [neg_one_smul] at h
        change matrixAction F z v = -v at h
        rw [h]
        exact neg_mem hv
      · have h := Module.End.mem_eigenspace_iff.1 hv
        rw [one_smul] at h
        exact h
    refine ⟨z, ⟨hz, hzt⟩, huniq, hdm, hdp, by rw [hDinf, hL], ?_, ?_, ?_, ?_⟩
    ·
      rw [injective_iff_map_eq_one]
      rintro ⟨g, hg⟩ h
      have hgD : g ∈ D := (QuotientGroup.eq_one_iff g).1 h
      obtain ⟨c, -, hcg⟩ := CFSG.LinearGroups.mem_scalarSubgroup_iff.1 (hD hgD)
      have hfix := hg.2 y₀ hy₀
      have hcy : (c : F) • y₀ = y₀ := by
        have hgy : matrixAction F g y₀ = (c : F) • y₀ := by
          change Matrix.mulVec (g : Matrix (Fin 3) (Fin 3) F) y₀ = _
          rw [hcg]
          ext i
          simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
        rw [← hgy]
        exact hfix
      have hc1 : (c : F) = 1 := by
        have h' : (c : F) • y₀ = (1 : F) • y₀ := by rw [one_smul]; exact hcy
        exact smul_left_injective F hy₀0 h'
      apply Subtype.ext
      apply Subtype.ext
      change (g : Matrix (Fin 3) (Fin 3) F) = 1
      rw [hcg, hc1, map_one]
    · rw [← hL]
      exact ⟨(eJ.symm.trans (equivMapOfInjective _ _
        (centralizer ({t} : Set (SL3 F ⧸ D))).subtype_injective)).symm⟩
    · exact ⟨z, hzB, hzt⟩
    · intro l hl
      rw [← hL] at hl
      exact mem_centralizer_singleton_iff.1 (map_subtype_le _ hl)

end CFSG.Quasithin.SteinbergBS
