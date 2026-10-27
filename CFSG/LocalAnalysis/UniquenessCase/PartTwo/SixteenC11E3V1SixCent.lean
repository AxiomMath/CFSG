module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixHyp
public import CFSG.Quasithin.Background.HPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyEndAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W W' : Type} [CommGroup W] [Finite W] [CommGroup W'] [Finite W']
  {M L : Subgroup (MulAut W)} {L' : Subgroup (MulAut W')} {κ : W →* W'} {e : ↥L' →* ↥L}

private theorem s1611e3_eq_one_of_fixes {I₁ I₂ : Subgroup W'}
    (hsup : I₁ ⊔ I₂ = ⊤) {ψ : MulAut W'}
    (hψ : ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')))
    (hE₁ : Z391.EndUnitsTrivial L' I₁) (hE₂ : Z391.EndUnitsTrivial L' I₂)
    (hfix₁ : I₁.map ψ.toMonoidHom = I₁) (hfix₂ : I₂.map ψ.toMonoidHom = I₂) : ψ = 1 := by
  have hpt : ∀ (J : Subgroup W') (hJ : J.map ψ.toMonoidHom = J),
      Z391.EndUnitsTrivial L' J → ∀ x ∈ J, ψ x = x := by
    intro J hJ hE x hx
    let φ : ↥J ≃* ↥J :=
      (MulEquiv.subgroupMap ψ J).trans (MulEquiv.subgroupCongr hJ)
    have hφval : ∀ y : ↥J, ((φ y : ↥J) : W') = ψ y := fun y => rfl
    have hφeqv : ∀ (l : ↥L') (x y : ↥J), l • (x : W') = (y : W') →
        l • ((φ x : ↥J) : W') = ((φ y : ↥J) : W') := by
      intro l x y hxy
      show (l : MulAut W') (ψ x) = ψ y
      have hcomm : ψ * (l : MulAut W') = (l : MulAut W') * ψ :=
        (Subgroup.mem_centralizer_iff.1 hψ (l : MulAut W') l.2).symm
      have h1 := congrArg (fun f : MulAut W' => f x) hcomm
      simp only [MulAut.mul_apply] at h1
      have hxy' : (l : MulAut W') ((x : ↥J) : W') = ((y : ↥J) : W') := hxy
      calc (l : MulAut W') (ψ x) = ψ ((l : MulAut W') x) := h1.symm
        _ = ψ y := by rw [hxy']
    have hφ1 : φ = MulEquiv.refl _ := hE φ hφeqv
    have h2 : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      have := congrArg (fun ψ : ↥J ≃* ↥J => ψ ⟨x, hx⟩) hφ1
      simpa using this
    have h3 := congrArg (fun y : ↥J => (y : W')) h2
    rw [hφval ⟨x, hx⟩] at h3
    simpa using h3
  have h₀ : ∀ x ∈ I₁, ψ x = x := hpt I₁ hfix₁ hE₁
  have h₁ : ∀ x ∈ I₂, ψ x = x := hpt I₂ hfix₂ hE₂
  ext w
  have hw : w ∈ I₁ ⊔ I₂ := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul, h₀ a ha, h₁ b hb]
  rfl

theorem SixHyp.ker_eq (h : SixHyp M L L' κ e) : κ.ker = fixV L := by
  refine le_antisymm ?_ ?_
  · intro w hw
    exact h.ker w (MonoidHom.mem_ker.1 hw)
  · intro w hw
    rw [MonoidHom.mem_ker]
    have hfix : κ w ∈ fixV L' := by
      rw [mem_fixV]
      intro b hb
      rw [← h.equiv ⟨b, hb⟩ w]
      congr 1
      exact mem_fixV.1 hw (e ⟨b, hb⟩) (e ⟨b, hb⟩).2
    rw [h.fix, Subgroup.mem_bot] at hfix
    exact hfix

private theorem s1611e3_not_isoMod {I₁ I₂ : Subgroup W'}
    (hinf : I₁ ⊓ I₂ = ⊥) (hsup : I₁ ⊔ I₂ = ⊤)
    (h₁ : H.Pair.IsInv L' I₁) (h₂ : H.Pair.IsInv L' I₂)
    (hne : ∀ ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')), I₁.map ψ.toMonoidHom ≠ I₂) :
    ¬ H.Pair.IsoMod L' I₁ I₂ := by
  rintro ⟨e, he⟩
  let P : W' →* W' := H.Pair.proj hinf hsup
  have hPmem : ∀ w, P w ∈ I₁ := H.Pair.proj_mem hinf hsup
  have hPself : ∀ {a : W'}, a ∈ I₁ → P a = a := fun ha => H.Pair.proj_eq_self hinf hsup ha
  have hPidem : ∀ w, P (P w) = P w := fun w => hPself (hPmem w)
  let P₁ : W' →* ↥I₁ := P.codRestrict I₁ hPmem
  have hb₂ : ∀ w : W', w * (P w)⁻¹ ∈ I₂ := fun w => by
    rw [← H.Pair.proj_eq_one_iff hinf hsup]
    rw [map_mul, map_inv, hPidem w, mul_inv_cancel]
  let b₂ : W' →* ↥I₂ :=
    { toFun := fun w => ⟨w * (P w)⁻¹, hb₂ w⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show (x * y) * (P (x * y))⁻¹ = (x * (P x)⁻¹) * (y * (P y)⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl) }
  let β : W' →* W' := I₂.subtype.comp (e.toMonoidHom.comp P₁)
  let γ : W' →* W' := I₁.subtype.comp (e.symm.toMonoidHom.comp b₂)
  let ψ₀ : W' →* W' := β * γ
  have hψ₀ : ∀ w, ψ₀ w = β w * γ w := fun w => rfl
  have hPβ : ∀ w, P (β w) = 1 := fun w =>
    (H.Pair.proj_eq_one_iff hinf hsup).mpr (show β w ∈ I₂ from (e (P₁ w)).2)
  have hPγ : ∀ w, P (γ w) = γ w := fun w =>
    hPself (show γ w ∈ I₁ from (e.symm (b₂ w)).2)
  have hψ₀inv : ∀ w, ψ₀ (ψ₀ w) = w := fun w => by
    have h1 : P (ψ₀ w) = γ w := by rw [hψ₀ w, map_mul, hPβ w, hPγ w, one_mul]
    have h2 : b₂ (ψ₀ w) = e (P₁ w) := by
      apply Subtype.ext
      change ψ₀ w * (P (ψ₀ w))⁻¹ = (e (P₁ w) : W')
      rw [h1]
      change β w * γ w * (γ w)⁻¹ = (e (P₁ w) : W')
      rw [show β w = (e (P₁ w) : W') from rfl]
      group
    have h3 : γ (ψ₀ w) = P w := by
      change (e.symm (b₂ (ψ₀ w)) : W') = P w
      rw [h2]
      show (e.symm (e (P₁ w)) : W') = P w
      rw [MulEquiv.symm_apply_apply]
      rfl
    have h4 : β (ψ₀ w) = ((b₂ w : ↥I₂) : W') := by
      change (e (P₁ (ψ₀ w)) : W') = (b₂ w : W')
      have hP₁ : P₁ (ψ₀ w) = e.symm (b₂ w) := by
        apply Subtype.ext
        change P (ψ₀ w) = (e.symm (b₂ w) : W')
        rw [h1]
        rfl
      rw [hP₁, MulEquiv.apply_symm_apply]
    rw [hψ₀ (ψ₀ w), h4, h3]
    change ((b₂ w : ↥I₂) : W') * P w = w
    rw [show ((b₂ w : ↥I₂) : W') = w * (P w)⁻¹ from rfl]
    group
  have he_symm : ∀ (l : ↥L') (b : ↥I₂) (hb : (l : MulAut W') (b : W') ∈ I₂),
      (e.symm ⟨(l : MulAut W') (b : W'), hb⟩ : W') = (l : MulAut W') (e.symm b) := by
    intro l b hb
    have hb' : (l : MulAut W') ((e.symm b : ↥I₁) : W') ∈ I₁ := h₁ l l.2 _ (e.symm b).2
    have h2 : (e ⟨(l : MulAut W') ((e.symm b : ↥I₁) : W'), hb'⟩ : W') =
        (l : MulAut W') (b : W') := by
      have h := he l l.2 (e.symm b) hb'
      simpa using h
    have h3 : e ⟨(l : MulAut W') ((e.symm b : ↥I₁) : W'), hb'⟩ =
        ⟨(l : MulAut W') (b : W'), hb⟩ := Subtype.ext h2
    have h4 : e.symm ⟨(l : MulAut W') (b : W'), hb⟩ =
        ⟨(l : MulAut W') ((e.symm b : ↥I₁) : W'), hb'⟩ := by
      rw [← h3, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h4
  have hψ₀eqv : ∀ (l : ↥L') (w : W'),
      ψ₀ ((l : MulAut W') w) = (l : MulAut W') (ψ₀ w) := by
    intro l w
    have hPl : P ((l : MulAut W') w) = (l : MulAut W') (P w) :=
      H.Pair.proj_equivariant hinf hsup h₁ h₂ l.2 w
    have hb₂l : ((b₂ ((l : MulAut W') w) : ↥I₂) : W') =
        (l : MulAut W') ((b₂ w : ↥I₂) : W') := by
      show ((l : MulAut W') w) * (P ((l : MulAut W') w))⁻¹ =
        (l : MulAut W') (w * (P w)⁻¹)
      rw [hPl, map_mul, map_inv]
    have hβl : β ((l : MulAut W') w) = (l : MulAut W') (β w) := by
      change (e (P₁ ((l : MulAut W') w)) : W') = (l : MulAut W') (e (P₁ w) : W')
      have hP₁l : P₁ ((l : MulAut W') w) =
          ⟨(l : MulAut W') ((P₁ w : ↥I₁) : W'), h₁ l l.2 _ (P₁ w).2⟩ :=
        Subtype.ext hPl
      rw [hP₁l]
      exact he l l.2 (P₁ w) (h₁ l l.2 _ (P₁ w).2)
    have hγl : γ ((l : MulAut W') w) = (l : MulAut W') (γ w) := by
      change (e.symm (b₂ ((l : MulAut W') w)) : W') =
        (l : MulAut W') (e.symm (b₂ w) : W')
      have hb : (l : MulAut W') ((b₂ w : ↥I₂) : W') ∈ I₂ := h₂ l l.2 _ (b₂ w).2
      have h1' : b₂ ((l : MulAut W') w) =
          ⟨(l : MulAut W') ((b₂ w : ↥I₂) : W'), hb⟩ := Subtype.ext hb₂l
      rw [h1']
      exact he_symm l (b₂ w) hb
    rw [hψ₀ ((l : MulAut W') w), hψ₀ w, hβl, hγl, map_mul]
  have hinj : Function.Injective ψ₀ := fun a b hab => by
    have h := congrArg ψ₀ hab
    rwa [hψ₀inv a, hψ₀inv b] at h
  have hsurj : Function.Surjective ψ₀ := fun b => ⟨ψ₀ b, hψ₀inv b⟩
  let ψ : MulAut W' := MulEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩
  have hψc : ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    ext w
    show (l : MulAut W') (ψ₀ w) = ψ₀ ((l : MulAut W') w)
    exact (hψ₀eqv ⟨l, hl⟩ w).symm
  have hmap : I₁.map ψ.toMonoidHom = I₂ := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      change ψ₀ a ∈ I₂
      have hP₁a : P₁ a = ⟨a, ha⟩ := Subtype.ext (hPself ha)
      have hb : b₂ a = 1 := Subtype.ext (by
        show a * (P a)⁻¹ = 1
        rw [hPself ha, mul_inv_cancel])
      change (e (P₁ a) : W') * (e.symm (b₂ a) : W') ∈ I₂
      rw [hP₁a, hb]
      simpa using (e ⟨a, ha⟩).2
    · intro b hb
      refine Subgroup.mem_map.2 ⟨((e.symm ⟨b, hb⟩ : ↥I₁) : W'), (e.symm ⟨b, hb⟩).2, ?_⟩
      change ψ₀ ((e.symm ⟨b, hb⟩ : ↥I₁) : W') = b
      have hP₁a : P₁ ((e.symm ⟨b, hb⟩ : ↥I₁) : W') = e.symm ⟨b, hb⟩ :=
        Subtype.ext (hPself (e.symm ⟨b, hb⟩).2)
      have hb' : b₂ ((e.symm ⟨b, hb⟩ : ↥I₁) : W') = 1 := Subtype.ext (by
        show ((e.symm ⟨b, hb⟩ : ↥I₁) : W') * (P _)⁻¹ = 1
        rw [hPself (e.symm ⟨b, hb⟩).2, mul_inv_cancel])
      change (e (P₁ ((e.symm ⟨b, hb⟩ : ↥I₁) : W')) : W') *
        (e.symm (b₂ ((e.symm ⟨b, hb⟩ : ↥I₁) : W')) : W') = b
      rw [hP₁a, hb']
      simpa using congrArg Subtype.val (MulEquiv.apply_symm_apply e ⟨b, hb⟩)
  exact hne ψ hψc hmap

theorem SixHyp.cent'_eq_one (h : SixHyp M L L' κ e) :
    ∀ ψ ∈ Subgroup.centralizer (L' : Set (MulAut W')), ψ = 1 := by
  intro ψ hψ
  obtain ⟨I₁, I₂, hZ₁, hZ₂, hI₁Z, hI₂Z, hsupZ, hN₁, hN₂, hne⟩ := h.sum
  rw [bot_sup_eq] at hI₁Z hI₂Z hsupZ
  have hinf : I₁ ⊓ I₂ = ⊥ := le_bot_iff.1 hI₁Z
  have hsup : I₁ ⊔ I₂ = ⊤ := hsupZ
  have hIrr₁ : I₁ ∈ irrSet L' := s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₁
  have hIrr₂ : I₂ ∈ irrSet L' := s16c167_mem_irrSet_alt (n := 6) (by norm_num) hN₂
  have hfix₁ : I₁ ⊓ fixV L' = ⊥ := s16c167_cfg2_fix_alt (n := 6) (by norm_num) hN₁
  have hfix₂ : I₂ ⊓ fixV L' = ⊥ := s16c167_cfg2_fix_alt (n := 6) (by norm_num) hN₂
  have hIrrOn₁ : IsIrrOn L' I₁ ⊥ := hfix₁ ▸ hIrr₁.2
  have hIrrOn₂ : IsIrrOn L' I₂ ⊥ := hfix₂ ▸ hIrr₂.2
  have hInv₁ : H.Pair.IsInv L' I₁ := hIrrOn₁.2.1
  have hInv₂ : H.Pair.IsInv L' I₂ := hIrrOn₂.2.1
  have hIrr'₁ : H.Pair.IsIrr L' I₁ :=
    ⟨hIrrOn₁.1.ne', fun U hU hUi => hIrrOn₁.2.2.2 U hUi bot_le hU⟩
  have hIrr'₂ : H.Pair.IsIrr L' I₂ :=
    ⟨hIrrOn₂.1.ne', fun U hU hUi => hIrrOn₂.2.2.2 U hUi bot_le hU⟩
  have hniso : ¬ H.Pair.IsoMod L' I₁ I₂ := s1611e3_not_isoMod hinf hsup hInv₁ hInv₂ hne
  have hE₁ : Z391.EndUnitsTrivial L' I₁ := s16c167_endUnits_alt (n := 6) (by norm_num) hN₁
  have hE₂ : Z391.EndUnitsTrivial L' I₂ := s16c167_endUnits_alt (n := 6) (by norm_num) hN₂
  have hnorm : ψ ∈ Subgroup.normalizer (L' : Set (MulAut W')) :=
    Subgroup.centralizer_le_normalizer _ hψ
  have hcase₁ := H.Pair.map_eq_or_map_eq hinf hsup hInv₁ hInv₂ hIrr'₁ hIrr'₂ hniso hnorm
  have hfixψ₁ : I₁.map ψ.toMonoidHom = I₁ := by
    rcases hcase₁ with h' | h'
    · exact h'
    · exact absurd h' (hne ψ hψ)
  have hniso' : ¬ H.Pair.IsoMod L' I₂ I₁ := fun h' => hniso (H.Pair.IsoMod.symm hInv₂ h')
  have hinf' : I₂ ⊓ I₁ = ⊥ := by rw [inf_comm]; exact hinf
  have hsup' : I₂ ⊔ I₁ = ⊤ := by rw [sup_comm]; exact hsup
  have hcase₂ := H.Pair.map_eq_or_map_eq hinf' hsup' hInv₂ hInv₁ hIrr'₂ hIrr'₁ hniso' hnorm
  have hfixψ₂ : I₂.map ψ.toMonoidHom = I₂ := by
    rcases hcase₂ with h' | h'
    · exact h'
    · exfalso
      have hψinv : ψ⁻¹ ∈ Subgroup.centralizer (L' : Set (MulAut W')) :=
        (Subgroup.centralizer (L' : Set (MulAut W'))).inv_mem hψ
      apply hne ψ⁻¹ hψinv
      rw [← h']
      rw [Subgroup.map_map]
      have hcomp : ψ⁻¹.toMonoidHom.comp ψ.toMonoidHom = MonoidHom.id W' := by
        ext w; simp
      rw [hcomp, Subgroup.map_id]
  exact s1611e3_eq_one_of_fixes hsup hψ hE₁ hE₂ hfixψ₁ hfixψ₂

theorem SixHyp.cent_eq_one (h : SixHyp M L L' κ e) :
    ∀ ψ ∈ Subgroup.centralizer (L : Set (MulAut W)), ψ = 1 := by
  intro ψ hψ
  have hker : κ.ker = fixV L := SixHyp.ker_eq h
  have hfix_of_cent : ∀ χ ∈ Subgroup.centralizer (L : Set (MulAut W)),
      ∀ w ∈ fixV L, χ w ∈ fixV L := by
    intro χ hχ w hw
    rw [mem_fixV] at hw ⊢
    intro l hl
    have hcomm : (l : MulAut W) * χ = χ * (l : MulAut W) :=
      Subgroup.mem_centralizer_iff.1 hχ l hl
    have h1 := congrArg (fun f : MulAut W => f w) hcomm
    simp only [MulAut.mul_apply] at h1
    rw [h1, congrArg χ (hw l hl)]
  have hψfix := hfix_of_cent ψ hψ
  let g : W →* W' := κ.comp ψ.toMonoidHom
  have hg : κ.ker ≤ g.ker := by
    intro w hw
    have hw' : w ∈ fixV L := hker ▸ hw
    show κ (ψ w) = 1
    exact MonoidHom.mem_ker.1 (hker.symm ▸ hψfix w hw')
  let ψ' : W' →* W' := (κ.liftOfSurjective h.surj) ⟨g, hg⟩
  have hψ' : ∀ w, ψ' (κ w) = κ (ψ w) := fun w => by
    change ((κ.liftOfSurjective h.surj) ⟨g, hg⟩) (κ w) = g w
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  let g' : W →* W' := κ.comp ψ⁻¹.toMonoidHom
  have hg' : κ.ker ≤ g'.ker := by
    intro w hw
    have hw' : w ∈ fixV L := hker ▸ hw
    have hψinv : ψ⁻¹ ∈ Subgroup.centralizer (L : Set (MulAut W)) :=
      (Subgroup.centralizer (L : Set (MulAut W))).inv_mem hψ
    show κ (ψ⁻¹ w) = 1
    exact MonoidHom.mem_ker.1 (hker.symm ▸ hfix_of_cent ψ⁻¹ hψinv w hw')
  let φ' : W' →* W' := (κ.liftOfSurjective h.surj) ⟨g', hg'⟩
  have hφ' : ∀ w, φ' (κ w) = κ (ψ⁻¹ w) := fun w => by
    change ((κ.liftOfSurjective h.surj) ⟨g', hg'⟩) (κ w) = g' w
    rw [MonoidHom.liftOfRightInverse_comp_apply]
  have hcomp₁ : ∀ y, ψ' (φ' y) = y := by
    intro y
    obtain ⟨w, rfl⟩ := h.surj y
    rw [hφ' w, hψ' (ψ⁻¹ w), MulAut.apply_inv_self]
  have hcomp₂ : ∀ y, φ' (ψ' y) = y := by
    intro y
    obtain ⟨w, rfl⟩ := h.surj y
    rw [hψ' w, hφ' (ψ w), MulAut.inv_apply_self]
  have hinj : Function.Injective ψ' := fun a b hab => by
    have h1 := congrArg φ' hab
    rwa [hcomp₂ a, hcomp₂ b] at h1
  have hsurj : Function.Surjective ψ' := fun y => ⟨φ' y, hcomp₁ y⟩
  let ψA : MulAut W' := MulEquiv.ofBijective ψ' ⟨hinj, hsurj⟩
  have hψA : ∀ w, ψA (κ w) = κ (ψ w) := hψ'
  have hψAc : ψA ∈ Subgroup.centralizer (L' : Set (MulAut W')) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    ext y
    obtain ⟨w, rfl⟩ := h.surj y
    show (b : MulAut W') (ψA (κ w)) = ψA ((b : MulAut W') (κ w))
    rw [hψA w, ← h.equiv ⟨b, hb⟩ w, hψA ((e ⟨b, hb⟩ : MulAut W) w),
      ← h.equiv ⟨b, hb⟩ (ψ w)]
    congr 1
    exact congrArg (fun f : MulAut W => f w)
      (Subgroup.mem_centralizer_iff.1 hψ (e ⟨b, hb⟩) (e ⟨b, hb⟩).2)
  have hψA1 : ψA = 1 := SixHyp.cent'_eq_one h ψA hψAc
  let η : W →* W :=
    { toFun := fun w => ψ w * w⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        show ψ (x * y) * (x * y)⁻¹ = (ψ x * x⁻¹) * (ψ y * y⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hη : ∀ w, η w ∈ fixV L := by
    intro w
    have h1 : κ (η w) = 1 := by
      change κ (ψ w * w⁻¹) = 1
      rw [map_mul, map_inv, ← hψA w, hψA1]
      simp
    rw [← hker, MonoidHom.mem_ker]
    exact h1
  have hηgen : ∀ (l : MulAut W), l ∈ L → ∀ w : W, η (l w * w⁻¹) = 1 := by
    intro l hl w
    have hηl : η (l w) = η w := by
      have hcomm : l (ψ w) = ψ (l w) :=
        congrArg (fun f : MulAut W => f w)
          (Subgroup.mem_centralizer_iff.1 hψ l hl)
      have hfix := mem_fixV.1 (hη w) l hl
      show ψ (l w) * (l w)⁻¹ = ψ w * w⁻¹
      rw [← hcomm, ← map_inv, ← map_mul]
      exact hfix
    rw [map_mul, map_inv, hηl, mul_inv_cancel]
  have hηtriv : η = 1 := by
    rw [← MonoidHom.ker_eq_top_iff, eq_top_iff, ← h.comm]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨l, hl, w, rfl⟩
    exact hηgen l hl w
  ext w
  have h1 := DFunLike.congr_fun hηtriv w
  exact mul_inv_eq_one.1 h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
