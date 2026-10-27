module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47L3Inv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47L3Trans

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped MatrixGroups Matrix

theorem s16c1_G47_L3_iso {Y : Type} [Group Y] (h : IsL3Five Y) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 5 ∧ Nonempty (Y ≃* SL(3, F)) := by
  rcases h with ⟨-, -, F, hFf, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hcard' : Nat.card F = 5 := by simpa using hcard
    have hcube := s16c1_G47_cube_five hcard'
    let φ : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 F) :=
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 F)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)
    exact ⟨F, hFf, hFin, hcard',
      ⟨(e.trans φ.symm).trans (CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tr.projEquiv hcube).symm⟩⟩
  all_goals omega

theorem s16c1_G47_L3five_inv {Hs : Type} [Group Hs] [Finite Hs] {Ys Xs : Subgroup Hs}
    (hY : Ys.Normal) (hL3 : IsL3Five ↥Ys) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5) :
    ∃ t ∈ Xs, t * t = 1 ∧ t ≠ 1 ∧
      (∀ v : Hs, v * v = 1 → (∀ x ∈ Xs, v * x = x * v) →
        (∀ y ∈ Ys, v * y = y * v) ∨ ∀ y ∈ Ys, v * y * v⁻¹ = t * y * t⁻¹) ∧
      ∃ a ∈ Ys, ∃ b ∈ Ys, orderOf (a * t * a⁻¹ * (b * t * b⁻¹)) = 4 := by
  classical
  haveI : Ys.Normal := hY
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨ι⟩⟩ := s16c1_G47_L3_iso hL3
  letI : Field F := hFfield
  letI : Finite F := hFfin
  let Xs' : Subgroup SL(3, F) := (Xs.subgroupOf Ys).map ι.toMonoidHom
  have hXs' : IsSL2Prime ↥Xs' 5 :=
    s16c1_isSL2Prime_of_equiv hX
      ((Subgroup.subgroupOfEquivOfLe hXY).symm.trans
        (Subgroup.equivMapOfInjective (Xs.subgroupOf Ys) ι.toMonoidHom ι.injective))
  obtain ⟨t', ht'X, ht'2, ht'1, hinv⟩ := s16c1_G47_L3_inv hFcard hXs'
  obtain ⟨a', b', hord⟩ := s16c1_G47_L3_trans hFcard ht'2 ht'1
  let t : Hs := (ι.symm t' : ↥Ys)
  have htX : t ∈ Xs := by
    obtain ⟨y, hy, hyι⟩ := Subgroup.mem_map.mp ht'X
    have hyι' : ι y = t' := hyι
    have hy' : y = ι.symm t' := ι.injective (by rw [hyι']; simp)
    rw [hy'] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  have ht2 : t * t = 1 := by
    have h2 : ι.symm t' * ι.symm t' = 1 := by rw [← map_mul, ht'2, map_one]
    simpa [t] using congrArg (fun z : ↥Ys => (z : Hs)) h2
  have ht1 : t ≠ 1 := by
    intro h
    apply ht'1
    have hιsym : ι.symm t' = 1 := Subtype.ext (by simpa [t] using h)
    rw [← MulEquiv.apply_symm_apply ι t', hιsym, map_one]
  refine ⟨t, htX, ht2, ht1, ?_, ?_⟩
  · intro v hv2 hvX
    let φ : MulAut ↥Ys := MulAut.conjNormal (H := Ys) v
    have hφ2 : ∀ z : ↥Ys, φ (φ z) = z := by
      intro z
      have h : φ * φ = 1 := by
        show MulAut.conjNormal (H := Ys) v * MulAut.conjNormal (H := Ys) v = 1
        rw [← map_mul, hv2, map_one]
      rw [← MulAut.mul_apply, h, MulAut.one_apply]
    have hσ2 : ∀ y : SL(3, F), (MulAut.congr ι φ) ((MulAut.congr ι φ) y) = y := by
      intro y
      have h := hφ2 (ι.symm y)
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.apply_symm_apply, h]
    have hσX : ∀ x ∈ Xs', (MulAut.congr ι φ) x = x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hyXs : (y : Hs) ∈ Xs := Subgroup.mem_subgroupOf.mp hy
      have hφy : φ y = y := by
        apply Subtype.ext
        change v * (y : Hs) * v⁻¹ = (y : Hs)
        have hc := hvX (y : Hs) hyXs
        calc v * (y : Hs) * v⁻¹ = (y * v) * v⁻¹ := by rw [← hc]
          _ = y := by group
      show (MulAut.congr ι φ) (ι y) = ι y
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hφy]
    rcases hinv (MulAut.congr ι φ) hσ2 hσX with hσ1 | hσt
    · left
      intro y hy
      have hz : φ ⟨y, hy⟩ = ⟨y, hy⟩ := by
        have h := congrArg (fun f : MulAut SL(3, F) => f (ι ⟨y, hy⟩)) hσ1
        have h2 : ι (φ ⟨y, hy⟩) = ι ⟨y, hy⟩ := by
          simpa [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
            MulAut.one_apply] using h
        exact ι.injective h2
      have h' := congrArg (fun z : ↥Ys => (z : Hs)) hz
      change v * y * v⁻¹ = y at h'
      calc v * y = (v * y * v⁻¹) * v := by group
        _ = y * v := by rw [h']
    · right
      intro y hy
      have h := hσt (ι ⟨y, hy⟩)
      have hleft : (MulAut.congr ι φ) (ι ⟨y, hy⟩) = ι (φ ⟨y, hy⟩) := by
        simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      rw [hleft] at h
      have h2 : ι (φ ⟨y, hy⟩) = ι (ι.symm t' * ⟨y, hy⟩ * (ι.symm t')⁻¹) := by
        rw [h]
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      have hφ : φ ⟨y, hy⟩ = ι.symm t' * ⟨y, hy⟩ * (ι.symm t')⁻¹ := ι.injective h2
      have h' := congrArg (fun z : ↥Ys => (z : Hs)) hφ
      simpa [t, φ, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] using h'
  · let a : Hs := (ι.symm a' : ↥Ys)
    let b : Hs := (ι.symm b' : ↥Ys)
    refine ⟨a, (ι.symm a').2, b, (ι.symm b').2, ?_⟩
    let f : SL(3, F) →* Hs := Ys.subtype.comp ι.symm.toMonoidHom
    have hf : Function.Injective f := fun x y h => ι.symm.injective (Subtype.ext h)
    have hmap : f (a' * t' * a'⁻¹ * (b' * t' * b'⁻¹)) =
        a * t * a⁻¹ * (b * t * b⁻¹) := by
      simp only [f, a, b, t, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hmap, orderOf_injective f hf, hord]

theorem s16c1_G47_L3five_card_le {Hs : Type} [Group Hs] [Finite Hs] {Ys Xs Vs : Subgroup Hs}
    (hY : Ys.Normal) (hL3 : IsL3Five ↥Ys) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5)
    (hV2 : ∀ v ∈ Vs, v * v = 1) (hVX : ∀ v ∈ Vs, ∀ x ∈ Xs, v * x = x * v)
    (hVY : ∀ v ∈ Vs, (∀ y ∈ Ys, v * y = y * v) → v = 1) : Nat.card ↥Vs ≤ 2 := by
  classical
  obtain ⟨t, -, -, -, hconj, -⟩ := s16c1_G47_L3five_inv hY hL3 hXY hX
  have hdich : ∀ v : Hs, v ∈ Vs →
      (∀ y ∈ Ys, v * y = y * v) ∨ ∀ y ∈ Ys, v * y * v⁻¹ = t * y * t⁻¹ :=
    fun v hv => hconj v (hV2 v hv) (hVX v hv)
  have hconj_eq : ∀ u v : Hs, u ∈ Vs → v ∈ Vs →
      (∀ y ∈ Ys, u * y * u⁻¹ = t * y * t⁻¹) →
      (∀ y ∈ Ys, v * y * v⁻¹ = t * y * t⁻¹) → u = v := by
    intro u v hu hv hU hV
    have hmem : u⁻¹ * v ∈ Vs := Vs.mul_mem (Vs.inv_mem hu) hv
    have hcent : ∀ y ∈ Ys, (u⁻¹ * v) * y = y * (u⁻¹ * v) := by
      intro y hy
      calc (u⁻¹ * v) * y = u⁻¹ * (v * y * v⁻¹) * v := by group
        _ = u⁻¹ * (t * y * t⁻¹) * v := by rw [hV y hy]
        _ = u⁻¹ * (u * y * u⁻¹) * v := by rw [← hU y hy]
        _ = y * (u⁻¹ * v) := by group
    have h1 : u⁻¹ * v = 1 := hVY (u⁻¹ * v) hmem hcent
    calc u = u * 1 := by group
      _ = u * (u⁻¹ * v) := by rw [h1]
      _ = v := by group
  have hinj : Function.Injective (fun v : ↥Vs => decide ((v : Hs) = 1)) := by
    intro u v huv
    change decide ((u : Hs) = 1) = decide ((v : Hs) = 1) at huv
    by_cases hu : (u : Hs) = 1
    · have hv : (v : Hs) = 1 := by
        by_contra hv
        rw [decide_eq_true_iff.mpr hu, decide_eq_false_iff_not.mpr hv] at huv
        exact Bool.noConfusion huv
      exact Subtype.ext (hu.trans hv.symm)
    · have hv : (v : Hs) ≠ 1 := by
        intro hv
        rw [decide_eq_true_iff.mpr hv, decide_eq_false_iff_not.mpr hu] at huv
        exact Bool.noConfusion huv
      have hU : ∀ y ∈ Ys, (u : Hs) * y * u⁻¹ = t * y * t⁻¹ := by
        rcases hdich u u.2 with h | h
        · exact absurd (hVY u u.2 h) hu
        · exact h
      have hV : ∀ y ∈ Ys, (v : Hs) * y * v⁻¹ = t * y * t⁻¹ := by
        rcases hdich v v.2 with h | h
        · exact absurd (hVY v v.2 h) hv
        · exact h
      exact Subtype.ext (hconj_eq u v u.2 v.2 hU hV)
  calc Nat.card ↥Vs ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]

theorem s16c1_G47_L3five_transposition {Hs : Type} [Group Hs] [Finite Hs] {Ys Xs : Subgroup Hs}
    {v : Hs} (hY : Ys.Normal) (hL3 : IsL3Five ↥Ys) (hXY : Xs ≤ Ys) (hX : IsSL2Prime ↥Xs 5)
    (hv2 : v * v = 1) (hvX : ∀ x ∈ Xs, v * x = x * v)
    (hvY : ¬ ∀ y ∈ Ys, v * y = y * v) :
    ∃ a ∈ Ys, ∃ b ∈ Ys, orderOf (a * v * a⁻¹ * (b * v * b⁻¹)) = 4 := by
  obtain ⟨t, htX, ht2, -, hconj, a, ha, b, hb, hord⟩ := s16c1_G47_L3five_inv hY hL3 hXY hX
  have hConj : ∀ y ∈ Ys, v * y * v⁻¹ = t * y * t⁻¹ := by
    intro y hy
    rcases hconj v hv2 hvX with h | h
    · exact absurd h hvY
    · exact h y hy
  let c : Hs := t⁻¹ * v
  have hc2 : c * c = 1 := by
    change (t⁻¹ * v) * (t⁻¹ * v) = 1
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hvt : v * t⁻¹ = t⁻¹ * v := by rw [hti, hvX t htX]
    have h1 : t⁻¹ * t⁻¹ = 1 := by rw [hti, ht2]
    calc (t⁻¹ * v) * (t⁻¹ * v)
        = t⁻¹ * (v * t⁻¹) * v := by group
      _ = t⁻¹ * (t⁻¹ * v) * v := by rw [hvt]
      _ = (t⁻¹ * t⁻¹) * (v * v) := by group
      _ = 1 := by rw [h1, hv2, one_mul]
  have hcY : ∀ y ∈ Ys, c * y = y * c := by
    intro y hy
    change (t⁻¹ * v) * y = y * (t⁻¹ * v)
    calc (t⁻¹ * v) * y = t⁻¹ * (v * y * v⁻¹) * v := by group
      _ = t⁻¹ * (t * y * t⁻¹) * v := by rw [hConj y hy]
      _ = y * (t⁻¹ * v) := by group
  have hca : c * a⁻¹ = a⁻¹ * c := hcY a⁻¹ (Ys.inv_mem ha)
  have hcb : c * b⁻¹ = b⁻¹ * c := hcY b⁻¹ (Ys.inv_mem hb)
  have hcbt : c * (b * t * b⁻¹) = (b * t * b⁻¹) * c :=
    hcY (b * t * b⁻¹) (Ys.mul_mem (Ys.mul_mem hb (hXY htX)) (Ys.inv_mem hb))
  have hv_eq : v = t * c := by
    change v = t * (t⁻¹ * v)
    group
  refine ⟨a, ha, b, hb, ?_⟩
  have ha' : a * (t * c) * a⁻¹ = (a * t * a⁻¹) * c := by
    calc a * (t * c) * a⁻¹ = a * t * (c * a⁻¹) := by group
      _ = a * t * (a⁻¹ * c) := by rw [hca]
      _ = (a * t * a⁻¹) * c := by group
  have hb' : b * (t * c) * b⁻¹ = (b * t * b⁻¹) * c := by
    calc b * (t * c) * b⁻¹ = b * t * (c * b⁻¹) := by group
      _ = b * t * (b⁻¹ * c) := by rw [hcb]
      _ = (b * t * b⁻¹) * c := by group
  have hprod : a * v * a⁻¹ * (b * v * b⁻¹) = a * t * a⁻¹ * (b * t * b⁻¹) := by
    rw [hv_eq, ha', hb']
    calc (a * t * a⁻¹) * c * ((b * t * b⁻¹) * c)
        = (a * t * a⁻¹) * (c * (b * t * b⁻¹)) * c := by group
      _ = (a * t * a⁻¹) * ((b * t * b⁻¹) * c) * c := by rw [hcbt]
      _ = (a * t * a⁻¹) * (b * t * b⁻¹) * (c * c) := by group
      _ = a * t * a⁻¹ * (b * t * b⁻¹) := by rw [hc2, mul_one]
  rw [hprod]
  exact hord

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
