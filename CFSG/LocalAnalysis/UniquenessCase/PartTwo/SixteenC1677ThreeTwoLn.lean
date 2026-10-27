module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoLnA
public import CFSG.Quasithin.AppendixH.H9.GLAutomorphisms
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightRowCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Matrix
open CFSG.ASVolI.ChH
open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private noncomputable def s168e3_matAct {m : ℕ} (δ : GL (Fin m) (ZMod 2))
    (w : Multiplicative (Fin m → ZMod 2)) : Multiplicative (Fin m → ZMod 2) :=
  Multiplicative.ofAdd ((δ : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ Multiplicative.toAdd w)

private theorem s168e3_matAct_eq_natAct {m : ℕ} (Γ : Subgroup (GL (Fin m) (ZMod 2)))
    (g : ↥Γ) (w : Multiplicative (Fin m → ZMod 2)) :
    s168e3_matAct (g : GL (Fin m) (ZMod 2)) w = natAct Γ g w := by
  rw [s168e3_matAct, natAct]

theorem s168e3_ln_fix_order_of {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {m p : ℕ} (hm : 3 ≤ m)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      H (⊤ : Subgroup W) ⊥ 2)
    (hpair : ∀ u v : Fin m → ZMod 2,
      ∃ B : GL (Fin m) (ZMod 2), orderOf B = p ∧
        (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u ∧
        (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ v = v)
    (hdual : ∀ u w : Fin m → ZMod 2,
      ∃ B : GL (Fin m) (ZMod 2), orderOf B = p ∧
        (B : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u ∧
        ((B : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) *ᵥ w = w) :
    ∀ x : W, x ≠ 1 → ∃ b ∈ H, orderOf b = p ∧ b x = x := by
  obtain ⟨I, hZI, hind, hsup, hN⟩ := hsum
  have hsup' : (⨆ i : Fin 2, I i) = ⊤ := by simpa using hsup
  have hTop : StatedSL m (ZMod 2) = ⊤ :=
    le_antisymm le_top (fun x _ => FFC.mem_statedSL_zmod x)
  let ι : GL (Fin m) (ZMod 2) ≃* ↥(StatedSL m (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hTop).symm
  have hι : ∀ δ : GL (Fin m) (ZMod 2),
      ((ι δ : ↥(StatedSL m (ZMod 2))) : GL (Fin m) (ZMod 2)) = δ := fun _ => rfl
  obtain ⟨π₀, hπ₀⟩ := FFC.BinaryNaturalSL.exists_zmod (hN 0)
  obtain ⟨f₀, hfs₀, hfk₀, hfe₀⟩ := FFC.exists_natMap hπ₀
  obtain ⟨π₁, hπ₁⟩ := FFC.BinaryNaturalSL.exists_zmod (hN 1)
  obtain ⟨f₁, hfs₁, hfk₁, hfe₁⟩ := FFC.exists_natMap hπ₁
  have hfi₀ : Function.Injective f₀ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk₀ u).1 hu))
  have hfi₁ : Function.Injective f₁ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk₁ u).1 hu))
  let π₀' : GL (Fin m) (ZMod 2) →* ↥H := π₀.comp ι.toMonoidHom
  let π₁' : GL (Fin m) (ZMod 2) →* ↥H := π₁.comp ι.toMonoidHom
  have heq₀ : ∀ (δ : GL (Fin m) (ZMod 2)) (u : ↥(I 0))
      (hu : ((π₀' δ : ↥H) : MulAut W) (u : W) ∈ I 0),
      f₀ ⟨((π₀' δ : ↥H) : MulAut W) (u : W), hu⟩ = s168e3_matAct δ (f₀ u) := by
    intro δ u hu
    have hnat : natAct (StatedSL m (ZMod 2)) (ι δ) (f₀ u) = s168e3_matAct δ (f₀ u) := by
      rw [s168e3_matAct, natAct, hι δ]
    have h1 := hfe₀ (ι δ) u hu
    rwa [hnat] at h1
  have heq₁ : ∀ (δ : GL (Fin m) (ZMod 2)) (u : ↥(I 1))
      (hu : ((π₁' δ : ↥H) : MulAut W) (u : W) ∈ I 1),
      f₁ ⟨((π₁' δ : ↥H) : MulAut W) (u : W), hu⟩ = s168e3_matAct δ (f₁ u) := by
    intro δ u hu
    have hnat : natAct (StatedSL m (ZMod 2)) (ι δ) (f₁ u) = s168e3_matAct δ (f₁ u) := by
      rw [s168e3_matAct, natAct, hι δ]
    have h1 := hfe₁ (ι δ) u hu
    rwa [hnat] at h1
  have hinj₀ : Function.Injective π₀' := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    have hfix : ∀ w : Multiplicative (Fin m → ZMod 2), s168e3_matAct δ w = w := by
      intro w
      obtain ⟨u, rfl⟩ := hfs₀ w
      have hu : ((π₀' δ : ↥H) : MulAut W) (u : W) ∈ I 0 := hπ₀.2.2.2.1 (π₀' δ) u u.2
      have h1 := heq₀ δ u hu
      have h2 : ((π₀' δ : ↥H) : MulAut W) (u : W) = (u : W) := by rw [hδ]; rfl
      have h3 : (⟨((π₀' δ : ↥H) : MulAut W) (u : W), hu⟩ : ↥(I 0)) = u := Subtype.ext h2
      have h4 : f₀ u = s168e3_matAct δ (f₀ u) := (congrArg f₀ h3).symm.trans h1
      exact h4.symm
    have hιδ : ι δ = 1 := natAct_faithful (StatedSL m (ZMod 2)) (ι δ) (fun w => by
      rw [← s168e3_matAct_eq_natAct (StatedSL m (ZMod 2)) (ι δ) w, hι δ]
      rw [hfix w, mul_inv_cancel])
    exact ι.injective (by rw [hιδ, map_one])
  have hinj₁ : Function.Injective π₁' := by
    rw [injective_iff_map_eq_one]
    intro δ hδ
    have hfix : ∀ w : Multiplicative (Fin m → ZMod 2), s168e3_matAct δ w = w := by
      intro w
      obtain ⟨u, rfl⟩ := hfs₁ w
      have hu : ((π₁' δ : ↥H) : MulAut W) (u : W) ∈ I 1 := hπ₁.2.2.2.1 (π₁' δ) u u.2
      have h1 := heq₁ δ u hu
      have h2 : ((π₁' δ : ↥H) : MulAut W) (u : W) = (u : W) := by rw [hδ]; rfl
      have h3 : (⟨((π₁' δ : ↥H) : MulAut W) (u : W), hu⟩ : ↥(I 1)) = u := Subtype.ext h2
      have h4 : f₁ u = s168e3_matAct δ (f₁ u) := (congrArg f₁ h3).symm.trans h1
      exact h4.symm
    have hιδ : ι δ = 1 := natAct_faithful (StatedSL m (ZMod 2)) (ι δ) (fun w => by
      rw [← s168e3_matAct_eq_natAct (StatedSL m (ZMod 2)) (ι δ) w, hι δ]
      rw [hfix w, mul_inv_cancel])
    exact ι.injective (by rw [hιδ, map_one])
  have hsurj₀ : Function.Surjective π₀' := fun h => by
    obtain ⟨γ, hγ⟩ := hπ₀.1 h
    let γ' : ↥(StatedSL m (ZMod 2)) := γ
    have hγ' : π₀ γ' = h := hγ
    exact ⟨ι.symm γ', by
      show π₀ (ι (ι.symm γ')) = h
      rw [MulEquiv.apply_symm_apply]
      exact hγ'⟩
  have hsurj₁ : Function.Surjective π₁' := fun h => by
    obtain ⟨γ, hγ⟩ := hπ₁.1 h
    let γ' : ↥(StatedSL m (ZMod 2)) := γ
    have hγ' : π₁ γ' = h := hγ
    exact ⟨ι.symm γ', by
      show π₁ (ι (ι.symm γ')) = h
      rw [MulEquiv.apply_symm_apply]
      exact hγ'⟩
  let e₀ : GL (Fin m) (ZMod 2) ≃* ↥H := MulEquiv.ofBijective π₀' ⟨hinj₀, hsurj₀⟩
  let e₁ : GL (Fin m) (ZMod 2) ≃* ↥H := MulEquiv.ofBijective π₁' ⟨hinj₁, hsurj₁⟩
  have he₀ : ∀ δ, ((e₀ δ : ↥H) : MulAut W) = ((π₀' δ : ↥H) : MulAut W) := fun _ => rfl
  have he₁ : ∀ δ, ((e₁ δ : ↥H) : MulAut W) = ((π₁' δ : ↥H) : MulAut W) := fun _ => rfl
  let α : MulAut (GL (Fin m) (ZMod 2)) := e₁.trans e₀.symm
  have hα : ∀ γ, e₀ (α γ) = e₁ γ := fun γ => by
    show e₀ ((e₁.trans e₀.symm) γ) = e₁ γ
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  obtain ⟨B, hB⟩ := CFSG.ASVolI.ChH.exists_aut_form_GL_two (by omega : 3 ≤ m) α
  intro x hx
  have hx_sup : x ∈ I 0 ⊔ I 1 := by
    have hx' : x ∈ ⨆ i : Fin 2, I i := by rw [hsup']; trivial
    have hle : (⨆ i : Fin 2, I i) ≤ I 0 ⊔ I 1 := by
      apply iSup_le
      intro i
      fin_cases i
      · exact le_sup_left
      · exact le_sup_right
    exact hle hx'
  obtain ⟨a, ha, a', ha', haa'⟩ := Subgroup.mem_sup.1 hx_sup
  rw [← haa']
  let u : Fin m → ZMod 2 := Multiplicative.toAdd (f₀ ⟨a, ha⟩)
  let v : Fin m → ZMod 2 := Multiplicative.toAdd (f₁ ⟨a', ha'⟩)
  have hu_toAdd : Multiplicative.toAdd (f₀ ⟨a, ha⟩) = u := rfl
  have hv_toAdd : Multiplicative.toAdd (f₁ ⟨a', ha'⟩) = v := rfl
  have hof_u : Multiplicative.ofAdd u = f₀ ⟨a, ha⟩ := ofAdd_toAdd u
  have hof_v : Multiplicative.ofAdd v = f₁ ⟨a', ha'⟩ := ofAdd_toAdd v
  have hb_eq : ∀ γ, ((e₁ γ : ↥H) : MulAut W) = ((e₀ (α γ) : ↥H) : MulAut W) :=
    fun γ => by rw [hα γ]
  rcases hB with hInner | hDual
  · obtain ⟨γ, hγord, hγu, hγv⟩ := hpair (B⁻¹ *ᵥ u) v
    refine ⟨(e₁ γ : ↥H), (e₁ γ).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hγord
    · rw [map_mul]
      congr 1
      · have hu : ((π₀' (α γ) : ↥H) : MulAut W) (a : W) ∈ I 0 :=
          hπ₀.2.2.2.1 (π₀' (α γ)) a ha
        have h1 := heq₀ (α γ) ⟨a, ha⟩ hu
        have hmat : ((α γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u := by
          rw [hInner γ, show (((B * γ * B⁻¹ : GL (Fin m) (ZMod 2))) :
              Matrix (Fin m) (Fin m) (ZMod 2)) =
            (B : Matrix (Fin m) (Fin m) (ZMod 2)) * (γ : Matrix (Fin m) (Fin m) (ZMod 2)) *
              (B⁻¹ : Matrix (Fin m) (Fin m) (ZMod 2)) by
            rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
              Matrix.GeneralLinearGroup.coe_inv]]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγu, Matrix.mulVec_mulVec,
            ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
            mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
        have h2 : s168e3_matAct (α γ) (f₀ ⟨a, ha⟩) = f₀ ⟨a, ha⟩ := by
          rw [s168e3_matAct, hmat, hof_u]
        have h3 : f₀ ⟨((π₀' (α γ) : ↥H) : MulAut W) (a : W), hu⟩ = f₀ ⟨a, ha⟩ := by
          rw [h1, h2]
        have h4 : ((π₀' (α γ) : ↥H) : MulAut W) (a : W) = (a : W) := by
          have h5 : (⟨((π₀' (α γ) : ↥H) : MulAut W) (a : W), hu⟩ : ↥(I 0)) = ⟨a, ha⟩ :=
            hfi₀ h3
          exact congrArg Subtype.val h5
        rw [hb_eq γ, he₀ (α γ)]
        exact h4
      · have hu' : ((π₁' γ : ↥H) : MulAut W) (a' : W) ∈ I 1 :=
          hπ₁.2.2.2.1 (π₁' γ) a' ha'
        have h1 := heq₁ γ ⟨a', ha'⟩ hu'
        have h2 : s168e3_matAct γ (f₁ ⟨a', ha'⟩) = f₁ ⟨a', ha'⟩ := by
          rw [s168e3_matAct, hγv, hof_v]
        have h3 : f₁ ⟨((π₁' γ : ↥H) : MulAut W) (a' : W), hu'⟩ = f₁ ⟨a', ha'⟩ := by
          rw [h1, h2]
        have h4 : ((π₁' γ : ↥H) : MulAut W) (a' : W) = (a' : W) := by
          have h5 : (⟨((π₁' γ : ↥H) : MulAut W) (a' : W), hu'⟩ : ↥(I 1)) = ⟨a', ha'⟩ :=
            hfi₁ h3
          exact congrArg Subtype.val h5
        rw [he₁ γ]
        exact h4
  · obtain ⟨γ, hγord, hγv, hγw⟩ := hdual v (B⁻¹ *ᵥ u)
    refine ⟨(e₁ γ : ↥H), (e₁ γ).2, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hγord
    · rw [map_mul]
      congr 1
      · have hu : ((π₀' (α γ) : ↥H) : MulAut W) (a : W) ∈ I 0 :=
          hπ₀.2.2.2.1 (π₀' (α γ)) a ha
        have h1 := heq₀ (α γ) ⟨a, ha⟩ hu
        have hdualmat : (((dualGLn m γ : GL (Fin m) (ZMod 2)) :
            Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ (B⁻¹ *ᵥ u)) = B⁻¹ *ᵥ u := by
          calc ((dualGLn m γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ
                (B⁻¹ *ᵥ u)
              = ((dualGLn m γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ
                  ((γ : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ *ᵥ (B⁻¹ *ᵥ u)) := by rw [hγw]
            _ = (((dualGLn m γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *
                  (γ : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) *ᵥ (B⁻¹ *ᵥ u) := by
                  rw [Matrix.mulVec_mulVec]
            _ = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ (B⁻¹ *ᵥ u) := by
                  rw [show ((dualGLn m γ : GL (Fin m) (ZMod 2)) :
                      Matrix (Fin m) (Fin m) (ZMod 2)) *
                      (γ : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ = 1 by
                    rw [show ((dualGLn m γ : GL (Fin m) (ZMod 2)) :
                        Matrix (Fin m) (Fin m) (ZMod 2)) =
                        (((γ⁻¹ : GL (Fin m) (ZMod 2)) :
                          Matrix (Fin m) (Fin m) (ZMod 2))ᵀ) from rfl,
                      ← Matrix.transpose_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
                      Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one]]
            _ = B⁻¹ *ᵥ u := by rw [Matrix.one_mulVec]
        have hmat : ((α γ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ u = u := by
          rw [hDual γ, show (((B * dualGLn m γ * B⁻¹ : GL (Fin m) (ZMod 2))) :
              Matrix (Fin m) (Fin m) (ZMod 2)) =
            (B : Matrix (Fin m) (Fin m) (ZMod 2)) *
              (dualGLn m γ : Matrix (Fin m) (Fin m) (ZMod 2)) *
              (B⁻¹ : Matrix (Fin m) (Fin m) (ZMod 2)) by
            rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
              Matrix.GeneralLinearGroup.coe_inv]]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hdualmat, Matrix.mulVec_mulVec,
            ← Matrix.GeneralLinearGroup.coe_inv, ← Matrix.GeneralLinearGroup.coe_mul,
            mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
        have h2 : s168e3_matAct (α γ) (f₀ ⟨a, ha⟩) = f₀ ⟨a, ha⟩ := by
          rw [s168e3_matAct, hmat, hof_u]
        have h3 : f₀ ⟨((π₀' (α γ) : ↥H) : MulAut W) (a : W), hu⟩ = f₀ ⟨a, ha⟩ := by
          rw [h1, h2]
        have h4 : ((π₀' (α γ) : ↥H) : MulAut W) (a : W) = (a : W) := by
          have h5 : (⟨((π₀' (α γ) : ↥H) : MulAut W) (a : W), hu⟩ : ↥(I 0)) = ⟨a, ha⟩ :=
            hfi₀ h3
          exact congrArg Subtype.val h5
        rw [hb_eq γ, he₀ (α γ)]
        exact h4
      · have hu' : ((π₁' γ : ↥H) : MulAut W) (a' : W) ∈ I 1 :=
          hπ₁.2.2.2.1 (π₁' γ) a' ha'
        have h1 := heq₁ γ ⟨a', ha'⟩ hu'
        have h2 : s168e3_matAct γ (f₁ ⟨a', ha'⟩) = f₁ ⟨a', ha'⟩ := by
          rw [s168e3_matAct, hγv, hof_v]
        have h3 : f₁ ⟨((π₁' γ : ↥H) : MulAut W) (a' : W), hu'⟩ = f₁ ⟨a', ha'⟩ := by
          rw [h1, h2]
        have h4 : ((π₁' γ : ↥H) : MulAut W) (a' : W) = (a' : W) := by
          have h5 : (⟨((π₁' γ : ↥H) : MulAut W) (a' : W), hu'⟩ : ↥(I 1)) = ⟨a', ha'⟩ :=
            hfi₁ h3
          exact congrArg Subtype.val h5
        rw [he₁ γ]
        exact h4

theorem s168e3_ln_fix_order_three {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {m : ℕ} (hm4 : 4 ≤ m) (hm5 : m ≤ 5)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1) H (⊤ : Subgroup W) ⊥ 2) :
    ∀ x : W, x ≠ 1 → ∃ b ∈ H, orderOf b = 3 ∧ b x = x :=
  s168e3_ln_fix_order_of (p := 3) (by omega) hsum
    (fun u v => s168e3_ln_fix_two hm4 hm5 u v)
    (fun u w => s168e3_ln_fix_dual hm4 hm5 u w)

theorem s168e3_pointFix_of_star {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdiv : p ∣ Nat.card ↥(lBar V₀ V hV L))
    (hfix : ∀ x : vStar D.M V₀ V hV L, x ≠ 1 →
      ∃ b ∈ lStar D.M V₀ V hV L, orderOf b = p ∧ b x = x) :
    ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ Mbar D.M V₀ V hV, orderOf b = p ∧ b x = x := by
  intro x hx
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ, θ, hρs, hρe, hρk⟩ := s168e3_star c hs
  have hmono : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  by_cases hρx : ρ x = 1
  · have hxfix : x ∈ fixV (lBar V₀ V hV L) := by
      rw [← hρk, MonoidHom.mem_ker]; exact hρx
    obtain ⟨b₀, hb₀ord⟩ := exists_prime_orderOf_dvd_card' p hdiv
    exact ⟨(b₀ : MulAut (Vtil V₀ V hV)), hmono b₀.2,
      by rw [Subgroup.orderOf_coe]; exact hb₀ord,
      mem_fixV.1 hxfix b₀ b₀.2⟩
  · obtain ⟨bstar, hbstar, hbstarord, hbstarx⟩ := hfix (ρ x) hρx
    let b₀ : ↥(lBar V₀ V hV L) := θ.symm ⟨bstar, hbstar⟩
    have hθb₀ : θ b₀ = ⟨bstar, hbstar⟩ := MulEquiv.apply_symm_apply θ _
    have hb₀ord : orderOf b₀ = p := by
      have h1 : orderOf b₀ = orderOf (⟨bstar, hbstar⟩ : ↥(lStar D.M V₀ V hV L)) := by
        rw [← MulEquiv.orderOf_eq θ b₀, hθb₀]
      rw [h1, (Subgroup.orderOf_coe (⟨bstar, hbstar⟩ : ↥(lStar D.M V₀ V hV L))).symm]
      exact hbstarord
    have hρb : ρ ((b₀ : MulAut (Vtil V₀ V hV)) x) = ρ x := by
      rw [hρe b₀ x, hθb₀]
      exact hbstarx
    have hρk1 : ρ ((b₀ : MulAut (Vtil V₀ V hV)) x * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hρb, mul_inv_cancel]
    have hk : (b₀ : MulAut (Vtil V₀ V hV)) x * x⁻¹ ∈ fixV (lBar V₀ V hV L) := by
      rw [← hρk, MonoidHom.mem_ker]; exact hρk1
    let b : MulAut (Vtil V₀ V hV) := (b₀ : MulAut (Vtil V₀ V hV))
    have hborder : orderOf b = p := by
      rw [Subgroup.orderOf_coe]; exact hb₀ord
    have hodd : Odd (orderOf b) := by
      rw [hborder]; exact hp.odd_of_ne_two hp2
    have hpow : b ^ orderOf b = 1 := pow_orderOf_eq_one b
    have hZ : ∀ z ∈ fixV (lBar V₀ V hV L), b z = z :=
      fun z hz => mem_fixV.1 hz b₀ b₀.2
    have hmain : b x * x⁻¹ ∈ fixV (lBar V₀ V hV L) := hk
    have hbx : b x = x :=
      s16g_apply_eq_of_odd (s15_Infra_vtil_sq_eq_one V₀ V hV) hodd hpow hZ hmain
    exact ⟨b, hmono b₀.2, hborder, hbx⟩

theorem s168e3_two_ln_three_dvd_kbar {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (h3 : 3 ∈ D.sig) {m : ℕ} (hm4 : 4 ≤ m) (hm5 : m ≤ 5)
    (hLm : IsLn ↥(lBar V₀ V hV L) m 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z m 1)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    3 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
      (lStar D.M V₀ V hV L)) := by
  by_contra hK
  have hF : s16e_two_Fam D V₀ V L hV (fun H U Z => BinaryNaturalSL H U Z m 1) :=
    s16e_two_fam_ln D hV (by omega) hLm hsum
  obtain ⟨J₀, J₁, hJ₀, hJ₁, F⟩ :=
    s16e_two_cfg2 D c.std.hx c.std.h61 c.std.h127 c.std.h1214 hV c.setting c.ne hs hF
  have hcard : Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣
      Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
        (lStar D.M V₀ V hV L)) *
      Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) := s16e_two_card_dvd_mul_aut F
  have h27 : ¬ 27 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    intro h27
    have h27' : 27 ∣ Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
      rwa [c23_card_mbar_v1Sub_eq D c.std.h1217 c.setting.hyp151 hV]
    have h27'' : 27 ∣ Nat.card ↥(s16e_two_cent (Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
        (lStar D.M V₀ V hV L)) * Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) :=
      h27'.trans hcard
    have hcop : Nat.Coprime 27 (Nat.card ↥(s16e_two_cent
        (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L))) :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hK)
    have h27aut : 27 ∣ Nat.card (MulAut ↥(lStar D.M V₀ V hV L)) :=
      hcop.dvd_of_dvd_mul_left h27''
    obtain ⟨e⟩ := s16e_two_lStar_equiv D c.std.h1217 c.setting.hyp151 hV
    have h27bar : 27 ∣ Nat.card (MulAut ↥(lBar V₀ V hV L)) := by
      rwa [Nat.card_congr (MulAut.congr e).toEquiv] at h27aut
    exact s16e_two_ln_not_cube (by omega) hm5 hLm
      (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact h27bar)
  have htop : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  rw [htop] at hsum
  have h3dvd : 3 ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rcases s16e_two_ln_card_cases (by omega : 3 ≤ m) hm5 hLm with h | h | h <;>
      rw [h] <;> norm_num
  have hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ Mbar D.M V₀ V hV, orderOf b = 3 ∧ b x = x :=
    s168e3_pointFix_of_star c hs Nat.prime_three (by decide) h3dvd
      (s168e3_ln_fix_order_three hm4 hm5 hsum)
  exact s168e3_false_of_kernel c Nat.prime_three h3
    (s168e3_kernel_of_cube Nat.prime_three (Mbar D.M V₀ V hV)
      (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact h27) hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
