module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
import CFSG.Milestones.CL_LIT_Fischer_3T_existence_uniqueness
import CFSG.GroupTheory.ThreeTranspositions.NoLine
import all CFSG.Fischer.F4
public import CFSG.Fischer.Unitary

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Blueprint.Fischer

section Star

private def IsStar {Y : Type} [Group Y] (S : Set Y) : Prop :=
  ∃ c x y z : Y, c ∈ S ∧ x ∈ S ∧ y ∈ S ∧ z ∈ S ∧
    orderOf (c * x) = 3 ∧ orderOf (c * y) = 3 ∧ orderOf (c * z) = 3 ∧
    x * y = y * x ∧ x * z = z * x ∧ y * z = z * y ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z

private theorem IsStar.image {Y Y' : Type} [Group Y] [Group Y'] {S : Set Y} (h : IsStar S)
    (φ : Y ≃* Y') : IsStar (φ '' S) := by
  obtain ⟨c, x, y, z, hc, hx, hy, hz, o1, o2, o3, c12, c13, c23, n12, n13, n23⟩ := h
  refine ⟨φ c, φ x, φ y, φ z, ⟨c, hc, rfl⟩, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, MulEquiv.orderOf_eq, o1]
  · rw [← map_mul, MulEquiv.orderOf_eq, o2]
  · rw [← map_mul, MulEquiv.orderOf_eq, o3]
  · rw [← map_mul, ← map_mul, c12]
  · rw [← map_mul, ← map_mul, c13]
  · rw [← map_mul, ← map_mul, c23]
  · exact fun h => n12 (φ.injective h)
  · exact fun h => n13 (φ.injective h)
  · exact fun h => n23 (φ.injective h)

private theorem hasCoreStar_of_isStar {G Y : Type} [Group G] [Group Y] {t : G} (φ : G ≃* Y)
    (h : IsStar (φ '' {x | IsConj t x})) : HasCoreStar G t := by
  obtain ⟨_, _, _, _, ⟨c, hc, rfl⟩, ⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, ⟨z, hz, rfl⟩, o1, o2, o3,
    c12, c13, c23, n12, n13, n23⟩ := h
  refine hasCoreStar_of_center hc hx hy hz ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rwa [← map_mul, MulEquiv.orderOf_eq] at o1
  · rwa [← map_mul, MulEquiv.orderOf_eq] at o2
  · rwa [← map_mul, MulEquiv.orderOf_eq] at o3
  · exact φ.injective (by rw [map_mul, map_mul, c12])
  · exact φ.injective (by rw [map_mul, map_mul, c13])
  · exact φ.injective (by rw [map_mul, map_mul, c23])
  · exact fun h => n12 (by rw [h])
  · exact fun h => n13 (by rw [h])
  · exact fun h => n23 (by rw [h])

private theorem IsStar.of_localImages {X : Type} [Group X] {E : Set X} (hP : Pair X E) {e : X}
    (h : IsStar (LocalImages E e)) : IsStar E := by
  have : Finite X := hP.1
  obtain ⟨_, _, _, _, ⟨fc, hfc, rfl⟩, ⟨fx, hfx, rfl⟩, ⟨fy, hfy, rfl⟩, ⟨fz, hfz, rfl⟩, o1, o2, o3,
    c12, c13, c23, n12, n13, n23⟩ := h
  have hsq : ∀ f : LocalGroup E e, (f : X) ∈ LocalClass E e → (f : X) * f = 1 := by
    intro f hf
    have h2 := pow_orderOf_eq_one (f : X)
    rwa [hP.2.2.1 _ hf.1, pow_two] at h2
  have hle : ∀ f g : LocalGroup E e, (f : X) ∈ LocalClass E e → (g : X) ∈ LocalClass E e →
      orderOf ((f : X) * g) ∈ ({1, 2, 3} : Set ℕ) := fun f g hf hg =>
    hP.2.2.2.1 _ hf.1 _ hg.1
  have hord : ∀ f g : LocalGroup E e, (f : X) ∈ LocalClass E e → (g : X) ∈ LocalClass E e →
      orderOf ((QuotientGroup.mk f : LocalQuotient E e) * QuotientGroup.mk g) = 3 →
        orderOf ((f : X) * g) = 3 := by
    intro f g hf hg h3
    have hdvd : orderOf (QuotientGroup.mk' (Subgroup.center (LocalGroup E e)) (f * g)) ∣
        orderOf (f * g) := orderOf_map_dvd _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, h3, ← Subgroup.orderOf_coe,
      Subgroup.coe_mul] at hdvd
    rcases hle f g hf hg with h1 | h1 | h1
    · rw [h1] at hdvd
      norm_num at hdvd
    · rw [h1] at hdvd
      norm_num at hdvd
    · exact h1
  have hcomm : ∀ f g : LocalGroup E e, (f : X) ∈ LocalClass E e → (g : X) ∈ LocalClass E e →
      (QuotientGroup.mk f : LocalQuotient E e) * QuotientGroup.mk g =
        QuotientGroup.mk g * QuotientGroup.mk f →
      (QuotientGroup.mk f : LocalQuotient E e) ≠ QuotientGroup.mk g → (f : X) * g = g * f := by
    intro f g hf hg hfg hne
    have hle3 : orderOf ((f : X) * g) ≤ 3 := by
      rcases hle f g hf hg with h1 | h1 | h1 <;> rw [h1] <;> norm_num
    rcases CFSG.GroupTheory.ThreeTranspositions.commute_or_orderOf_mul_eq_three (hsq f hf)
      (hsq g hg) hle3 with h1 | h1
    · exact h1.eq
    · exfalso
      apply hne
      set a : LocalQuotient E e := QuotientGroup.mk f
      set b : LocalQuotient E e := QuotientGroup.mk g
      have haa : a * a = 1 := by
        rw [← QuotientGroup.mk_mul, show f * f = 1 from Subtype.ext (hsq f hf),
          QuotientGroup.mk_one]
      have hbb : b * b = 1 := by
        rw [← QuotientGroup.mk_mul, show g * g = 1 from Subtype.ext (hsq g hg),
          QuotientGroup.mk_one]
      have h3 : (a * b) ^ 3 = 1 := by
        have hfg3 : (f * g) ^ 3 = 1 := by
          rw [← h1, ← Subgroup.coe_mul, Subgroup.orderOf_coe]
          exact pow_orderOf_eq_one _
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hfg3, QuotientGroup.mk_one]
      have h2 : (a * b) ^ 2 = 1 := by
        rw [pow_two, mul_assoc, ← mul_assoc b, ← hfg, mul_assoc, hbb, mul_one, haa]
      have hab : a * b = 1 := by
        calc a * b = (a * b) ^ 3 * ((a * b) ^ 2)⁻¹ := by group
          _ = 1 := by rw [h3, h2, inv_one, mul_one]
      calc a = a * (b * b) := by rw [hbb, mul_one]
        _ = (a * b) * b := by group
        _ = b := by rw [hab, one_mul]
  refine ⟨fc, fx, fy, fz, hfc.1, hfx.1, hfy.1, hfz.1, hord fc fx hfc hfx o1,
    hord fc fy hfc hfy o2, hord fc fz hfc hfz o3, hcomm fx fy hfx hfy c12 n12,
    hcomm fx fz hfx hfz c13 n13, hcomm fy fz hfy hfz c23 n23, ?_, ?_, ?_⟩
  · exact fun h => n12 (congrArg QuotientGroup.mk (Subtype.ext h))
  · exact fun h => n13 (congrArg QuotientGroup.mk (Subtype.ext h))
  · exact fun h => n23 (congrArg QuotientGroup.mk (Subtype.ext h))

end Star

section Unitary

open CFSG.Fischer CFSG.Sporadic.Fi22

private def starW0 : W := ![1, 0, 1, 0, F4.ω, 1]
private def starW1 : W := ![1, 1, 0, 0, 0, 0]
private def starW2 : W := ![0, 0, 1, 1, 0, 0]
private def starW3 : W := ![0, 0, 0, 0, 1, 1]

private theorem iso0 : hermStd starW0 starW0 = 0 := by decide +kernel
private theorem iso1 : hermStd starW1 starW1 = 0 := by decide +kernel
private theorem iso2 : hermStd starW2 starW2 = 0 := by decide +kernel
private theorem iso3 : hermStd starW3 starW3 = 0 := by decide +kernel

private theorem ne0 : starW0 ≠ 0 := by decide +kernel
private theorem ne1 : starW1 ≠ 0 := by decide +kernel
private theorem ne2 : starW2 ≠ 0 := by decide +kernel
private theorem ne3 : starW3 ≠ 0 := by decide +kernel

private theorem comm12 : tvM starW1 * tvM starW2 = tvM starW2 * tvM starW1 := by decide +kernel
private theorem comm13 : tvM starW1 * tvM starW3 = tvM starW3 * tvM starW1 := by decide +kernel
private theorem comm23 : tvM starW2 * tvM starW3 = tvM starW3 * tvM starW2 := by decide +kernel

private theorem ncomm1 : tvM starW0 * tvM starW1 ≠ tvM starW1 * tvM starW0 := by decide +kernel
private theorem ncomm2 : tvM starW0 * tvM starW2 ≠ tvM starW2 * tvM starW0 := by decide +kernel
private theorem ncomm3 : tvM starW0 * tvM starW3 ≠ tvM starW3 * tvM starW0 := by decide +kernel

private theorem cube1 : (tvM starW0 * tvM starW1) ^ 3 = 1 := by decide +kernel
private theorem cube2 : (tvM starW0 * tvM starW2) ^ 3 = 1 := by decide +kernel
private theorem cube3 : (tvM starW0 * tvM starW3) ^ 3 = 1 := by decide +kernel

private theorem dist12 :
    tvM starW0 * (tvM starW1 * tvM starW2) ≠ tvM starW1 * tvM starW2 * tvM starW0 := by
  decide +kernel
private theorem dist13 :
    tvM starW0 * (tvM starW1 * tvM starW3) ≠ tvM starW1 * tvM starW3 * tvM starW0 := by
  decide +kernel
private theorem dist23 :
    tvM starW0 * (tvM starW2 * tvM starW3) ≠ tvM starW2 * tvM starW3 * tvM starW0 := by
  decide +kernel

private noncomputable def tvS (w : W) (hw : hermStd w w = 0) : SU0 :=
  ⟨tvGL w hw, tvGL_mem_SU0 hw⟩

private theorem tvS_val (w : W) (hw : hermStd w w = 0) :
    ((tvS w hw : SU0) : GL (Fin 6) F4).val = tvM w := rfl

private noncomputable def piS : SU0 →* PSU (1 : Matrix (Fin 6) (Fin 6) K) :=
  (QuotientGroup.mk' _).comp suEquiv.toMonoidHom

private theorem piS_tvS_mem {w : W} (hw0 : w ≠ 0) (hw : hermStd w w = 0) :
    piS (tvS w hw) ∈ Transvections 1 := by
  refine ⟨suEquiv (tvS w hw), rfl, ψV w, ψV_ne_zero hw0, ?_, ?_⟩
  · rw [hermitian_ψV_self, hw, map_zero]
  · intro x
    rw [suEquiv_val]
    exact ψGL_tv_mulVec _ hw x

private theorem SU0_ext {s s' : SU0} (h : ((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
    ((s' : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) : s = s' :=
  Subtype.ext (Units.ext h)

private theorem piS_ne_one {s y : SU0} (h : y * s ≠ s * y) : piS s ≠ 1 := by
  intro h1
  have hc : suEquiv s ∈ Subgroup.center (SU (1 : Matrix (Fin 6) (Fin 6) K)) :=
    (QuotientGroup.eq_one_iff _).1 h1
  apply h
  apply suEquiv.injective
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.1 hc (suEquiv y))

private theorem isStar_transvections_one :
    IsStar (Transvections (1 : Matrix (Fin 6) (Fin 6) K)) := by
  have hord : ∀ {w : W} (hw : hermStd w w = 0),
      (tvM starW0 * tvM w) ^ 3 = 1 → tvM starW0 * tvM w ≠ tvM w * tvM starW0 →
        orderOf (piS (tvS starW0 iso0) * piS (tvS w hw)) = 3 := by
    intro w hw h3 hn
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [← map_mul]
    refine orderOf_eq_prime ?_ (piS_ne_one (y := tvS starW0 iso0) fun h => hn ?_)
    · rw [← map_pow, show (tvS starW0 iso0 * tvS w hw) ^ 3 = 1 from SU0_ext (by
        rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_mul, Units.val_mul,
          tvS_val, tvS_val]
        exact h3), map_one]
    · have h' := congrArg (fun s : SU0 => ((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) h
      simp only [Subgroup.coe_mul, Units.val_mul, tvS_val] at h'
      have h2 : tvM starW0 * tvM starW0 = 1 := tvM_mul_self iso0
      calc tvM starW0 * tvM w = tvM starW0 * (tvM starW0 * (tvM starW0 * tvM w)) := by
            rw [← mul_assoc (tvM starW0), h2, one_mul]
        _ = tvM starW0 * (tvM starW0 * tvM w * tvM starW0) := by rw [h']
        _ = tvM w * tvM starW0 := by rw [← mul_assoc, ← mul_assoc, h2, one_mul]
  have hcomm : ∀ {w w' : W} (hw : hermStd w w = 0) (hw' : hermStd w' w' = 0),
      tvM w * tvM w' = tvM w' * tvM w → piS (tvS w hw) * piS (tvS w' hw') =
        piS (tvS w' hw') * piS (tvS w hw) := by
    intro w w' hw hw' h
    rw [← map_mul, ← map_mul, SU0_ext (s := tvS w hw * tvS w' hw') (s' := tvS w' hw' * tvS w hw)
      (by simp only [Subgroup.coe_mul, Units.val_mul, tvS_val]; exact h)]
  have hdist : ∀ {w w' : W} (hw : hermStd w w = 0) (hw' : hermStd w' w' = 0),
      tvM starW0 * (tvM w * tvM w') ≠ tvM w * tvM w' * tvM starW0 →
        piS (tvS w hw) ≠ piS (tvS w' hw') := by
    intro w w' hw hw' h heq
    have h1 : piS (tvS w hw * tvS w' hw') = 1 := by
      rw [map_mul, heq, ← map_mul, show tvS w' hw' * tvS w' hw' = 1 from SU0_ext (by
        simp only [Subgroup.coe_mul, Units.val_mul, tvS_val, Subgroup.coe_one, Units.val_one]
        exact tvM_mul_self hw'), map_one]
    refine piS_ne_one (y := tvS starW0 iso0) (fun h' => h ?_) h1
    have h'' := congrArg (fun s : SU0 => ((s : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) h'
    simpa only [Subgroup.coe_mul, Units.val_mul, tvS_val, mul_assoc] using h''
  exact ⟨_, _, _, _, piS_tvS_mem ne0 iso0, piS_tvS_mem ne1 iso1, piS_tvS_mem ne2 iso2,
    piS_tvS_mem ne3 iso3, hord iso1 cube1 ncomm1, hord iso2 cube2 ncomm2, hord iso3 cube3 ncomm3,
    hcomm iso1 iso2 comm12, hcomm iso1 iso3 comm13, hcomm iso2 iso3 comm23,
    hdist iso1 iso2 dist12, hdist iso1 iso3 dist13, hdist iso2 iso3 dist23⟩

private theorem isStar_transvections {H : Matrix (Fin 6) (Fin 6) K}
    (hH : IsNondegenerateHermitian H) : IsStar (Transvections H) := by
  obtain ⟨iso, himg⟩ := exists_psu_equiv hH
  rw [← himg]
  exact isStar_transvections_one.image iso

end Unitary

section Types

private theorem isStar_of_F22 {X : Type} [Group X] {E : Set X} (h : F22 X E) : IsStar E := by
  obtain ⟨hP, e, -, H, hH, iso, himg⟩ := h
  refine IsStar.of_localImages hP (e := e) ?_
  have h1 := (isStar_transvections hH).image iso.symm
  rw [← himg] at h1
  simpa only [Set.image_image, MulEquiv.symm_apply_apply, Set.image_id'] using h1

private theorem isStar_of_F23 {X : Type} [Group X] {E : Set X} (h : F23 X E) : IsStar E := by
  obtain ⟨hP, e, -, h22⟩ := h
  exact IsStar.of_localImages hP (isStar_of_F22 h22)

private theorem isStar_of_F24 {X : Type} [Group X] {E : Set X} (h : F24 X E) : IsStar E := by
  obtain ⟨hP, e, -, h23⟩ := h
  exact IsStar.of_localImages hP (isStar_of_F23 h23)

end Types

set_option linter.unusedVariables false in
theorem hasCoreStar_of_fi22
    {G : Type} [Group G] {t : G} (hP : Pair G {x | IsConj t x})
    (φ : G ≃* CFSG.Blueprint.NativeSporadic.Fi22) (hφ : Pair _ (φ '' {x | IsConj t x}))
    (hu : ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi22, Pair _ E → E = φ '' {x | IsConj t x}) :
    HasCoreStar G t := by
  obtain ⟨-, -, D₀, hT, -, -, -⟩ := CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full 0
  have h22 : F22 CFSG.Blueprint.NativeSporadic.Fi22 D₀ := hT
  rw [hu D₀ h22.1] at h22
  exact hasCoreStar_of_isStar (Y := CFSG.Blueprint.NativeSporadic.Fi22) φ (isStar_of_F22 h22)

set_option linter.unusedVariables false in
theorem hasCoreStar_of_fi23
    {G : Type} [Group G] {t : G} (hP : Pair G {x | IsConj t x})
    (φ : G ≃* CFSG.Blueprint.NativeSporadic.Fi23) (hφ : Pair _ (φ '' {x | IsConj t x}))
    (hu : ∀ E : Set CFSG.Blueprint.NativeSporadic.Fi23, Pair _ E → E = φ '' {x | IsConj t x}) :
    HasCoreStar G t := by
  obtain ⟨-, -, D₀, hT, -, -, -⟩ := CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full 1
  have h23 : F23 CFSG.Blueprint.NativeSporadic.Fi23 D₀ := hT
  rw [hu D₀ h23.1] at h23
  exact hasCoreStar_of_isStar (Y := CFSG.Blueprint.NativeSporadic.Fi23) φ (isStar_of_F23 h23)

set_option linter.unusedVariables false in
theorem hasCoreStar_of_fi24
    {G : Type} [Group G] {t : G} (hP : Pair G {x | IsConj t x})
    (φ : G ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime)
    (hφ : Pair _ (φ '' {x | IsConj t x}))
    (hu : ∀ E : Set (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime), Pair _ E →
      E = φ '' {x | IsConj t x}) :
    HasCoreStar G t := by
  obtain ⟨-, -, D₀, hT, -, -, -⟩ := CFSG.Milestones.cl_lit_fischer_3t_existence_uniqueness_full 2
  have h24 : F24 (MulAut CFSG.Blueprint.NativeSporadic.Fi24prime) D₀ := hT
  rw [hu D₀ h24.1] at h24
  exact hasCoreStar_of_isStar φ (isStar_of_F24 h24)

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
