module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreStarRefl

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open CFSG.Fischer.Classification

section Aux

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

private theorem mem_orthReflSet_iff {g : GL (Fin m) (ZMod 3)} :
    g ∈ orthReflSet 3 m f ↔ g ∈ F3.reflSet f :=
  exists_congr fun v => and_congr
    ⟨fun h => show f v v = 1 by rw [h]; decide,
      fun h => show f v v = -2 by rw [show f v v = 1 from h]; decide⟩ Iff.rfl

private theorem closure_orthReflSet :
    Subgroup.closure (orthReflSet 3 m f) = F3.reflGroup f :=
  congrArg Subgroup.closure (Set.ext fun _ => mem_orthReflSet_iff)

private theorem hasCoreStar_of_hom (hf : IsF3Form f) (hm : 5 ≤ m) {L : Type} [Group L] {t : L}
    (φ : ↥(F3.reflGroup f) →* L) (hker : φ.ker ≤ Subgroup.center ↥(F3.reflGroup f))
    {v₀ : Fin m → ZMod 3} (hv₀ : f v₀ v₀ = 1)
    (ht : φ ⟨F3.refl f v₀, F3.refl_mem_reflGroup v₀⟩ = t) : CoreStar.HasCoreStar L t := by
  obtain ⟨v, e₁, e₂, e₃, hv, h1, h2, h3, h12, h13, h23, hv1, hv2, hv3⟩ :=
    CoreStar.exists_reflStar_vectors hf.symm hf.nondeg hm
  let ρ : (Fin m → ZMod 3) → ↥(F3.reflGroup f) := fun u =>
    ⟨F3.refl f u, F3.refl_mem_reflGroup u⟩
  have hρ : ∀ u, ((ρ u : ↥(F3.reflGroup f)) : GL (Fin m) (ZMod 3)) = F3.refl f u := fun _ => rfl
  let g : (Fin m → ZMod 3) → L := fun u => φ (ρ u)
  have hgD : ∀ u, f u u = 1 → IsConj t (g u) := fun u hu => by
    obtain ⟨c, hc, hconj⟩ := F3.exists_conj_refl hf (by omega) hv₀ hu
    rw [← ht]
    refine isConj_iff.mpr ⟨φ ⟨c, hc⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hconj)
  have hgmul : ∀ u u', g u * g u' = φ (ρ u * ρ u') := fun u u' => (map_mul φ _ _).symm
  have hgsq : ∀ u, g u * g u = 1 := fun u => by
    rw [hgmul, show ρ u * ρ u = 1 from Subtype.ext (F3.refl_mul_self u), map_one]
  have hcomm : ∀ u u', f u u = 1 → f u' u' = 1 → f u u' = 0 → g u * g u' = g u' * g u := by
    intro u u' hu hu' h
    rw [hgmul, hgmul, show ρ u * ρ u' = ρ u' * ρ u from
      Subtype.ext ((F3.refl_commute_iff hf hu hu').2 (Or.inl h))]
  have hinj : ∀ u u', f u u = 1 → f u' u' = 1 → g u = g u' → u' = u ∨ u' = -u := by
    intro u u' hu hu' h
    have hk : (ρ u)⁻¹ * ρ u' ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      exact inv_mul_eq_one.mpr h
    rcases F3.coe_eq_of_mem_center hf (by omega) (hker hk) with h2 | h2
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hρ, hρ, inv_mul_eq_one] at h2
      exact (F3.refl_eq_refl_iff hu hu').mp h2
    · exfalso
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hρ, hρ, inv_mul_eq_iff_eq_mul, mul_neg_one] at h2
      exact F3.refl_ne_neg_refl (f := f) (by omega) u u' h2
  have hord : ∀ u u', f u u = 1 → f u' u' = 1 → f u u' ≠ 0 → u' ≠ u → u' ≠ -u →
      orderOf (g u * g u') = 3 := by
    intro u u' hu hu' h hne hne'
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [hgmul, ← map_pow, show (ρ u * ρ u') ^ 3 = 1 from
        Subtype.ext (by simpa [hρ] using F3.refl_mul_refl_pow_three hf hu hu' h), map_one]
    · have hgu' : g u' = g u := by
        rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right (hgsq u)]
      rcases hinj u u' hu hu' hgu'.symm with h2 | h2
      exacts [hne h2, hne' h2]
  have hsep : ∀ {a e : Fin m → ZMod 3}, f a e = 0 → f v e = 1 → a ≠ v ∧ a ≠ -v := by
    intro a e ha hve
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, hve] at ha
      exact one_ne_zero ha
    · rw [h, LinearMap.BilinForm.neg_left, hve] at ha
      exact absurd ha (by decide)
  have h21 : f e₂ e₁ = 0 := by rw [hf.symm]; exact h12
  have h31 : f e₃ e₁ = 0 := by rw [hf.symm]; exact h13
  obtain ⟨n1v, n1v'⟩ := hsep h12 hv2
  obtain ⟨n2v, n2v'⟩ := hsep h21 hv1
  obtain ⟨n3v, n3v'⟩ := hsep h31 hv1
  have hne : ∀ {a b : Fin m → ZMod 3}, f a a = 1 → f b b = 1 → f a b = 0 → g a ≠ g b := by
    intro a b ha hb hab h
    rcases hinj a b ha hb h with h' | h'
    · rw [h', ha] at hab
      exact one_ne_zero hab
    · rw [h', LinearMap.BilinForm.neg_right, ha] at hab
      exact absurd hab (by decide)
  exact CoreStar.hasCoreStar_of_center (hgD v hv) (hgD e₁ h1) (hgD e₂ h2) (hgD e₃ h3)
    (hord v e₁ hv h1 (by rw [hv1]; exact one_ne_zero) n1v n1v')
    (hord v e₂ hv h2 (by rw [hv2]; exact one_ne_zero) n2v n2v')
    (hord v e₃ hv h3 (by rw [hv3]; exact one_ne_zero) n3v n3v')
    (hcomm e₁ e₂ h1 h2 h12) (hcomm e₁ e₃ h1 h3 h13) (hcomm e₂ e₃ h2 h3 h23)
    (hne h1 h2 h12) (hne h1 h3 h13) (hne h2 h3 h23)

private theorem exists_eq_refl {r : ↥(Subgroup.closure (orthReflSet 3 m f))}
    (hr : (r : GL (Fin m) (ZMod 3)) ∈ orthReflSet 3 m f) :
    ∃ v₀, f v₀ v₀ = 1 ∧ (r : GL (Fin m) (ZMod 3)) = F3.refl f v₀ := by
  obtain ⟨v₀, hv₀, h⟩ := F3.mem_reflSet_iff.mp (mem_orthReflSet_iff.mp hr)
  exact ⟨v₀, hv₀, h.symm⟩

private theorem hasCoreStar_aux (hf : IsF3Form f) (hm : 5 ≤ m) {L : Type} [Group L] {D : Set L}
    {t : L} (ht : t ∈ D) (h : IsReflModel 3 m f L D ∨ IsReflQuotModel 3 m f L D) :
    CoreStar.HasCoreStar L t := by
  let ι : ↥(F3.reflGroup f) ≃* ↥(Subgroup.closure (orthReflSet 3 m f)) :=
    MulEquiv.subgroupCongr closure_orthReflSet.symm
  have hι : ∀ x, ((ι x : ↥(Subgroup.closure (orthReflSet 3 m f))) : GL (Fin m) (ZMod 3)) =
      (x : GL (Fin m) (ZMod 3)) := fun _ => rfl
  rcases h with ⟨e, he⟩ | ⟨e, he⟩
  ·
    obtain ⟨v₀, hv₀, hr⟩ := exists_eq_refl (he t ht)
    refine hasCoreStar_of_hom hf hm (e.symm.toMonoidHom.comp ι.toMonoidHom) (fun x hx => ?_) hv₀
      ?_
    · have hinj : Function.Injective (e.symm.toMonoidHom.comp ι.toMonoidHom) :=
        e.symm.injective.comp ι.injective
      have : x = 1 := hinj (by rw [map_one]; exact MonoidHom.mem_ker.mp hx)
      rw [this]
      exact Subgroup.one_mem _
    · have : ι ⟨F3.refl f v₀, F3.refl_mem_reflGroup v₀⟩ = e t :=
        Subtype.ext ((hι _).trans hr.symm)
      simp [this]
  ·
    obtain ⟨r, hr, her⟩ := he t ht
    obtain ⟨v₀, hv₀, hrv⟩ := exists_eq_refl hr
    let φ : ↥(F3.reflGroup f) →* L := e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' (Subgroup.center ↥(Subgroup.closure (orthReflSet 3 m f)))).comp
        ι.toMonoidHom)
    refine hasCoreStar_of_hom hf hm φ (fun x hx => ?_) hv₀ ?_
    · have hc : ι x ∈ Subgroup.center ↥(Subgroup.closure (orthReflSet 3 m f)) := by
        have h1 : QuotientGroup.mk' _ (ι x) = 1 := e.symm.injective (by
          rw [map_one]
          exact hx)
        exact (QuotientGroup.eq_one_iff (ι x)).mp h1
      refine Subgroup.mem_center_iff.mpr fun y => ι.injective ?_
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hc (ι y)
    · have : ι ⟨F3.refl f v₀, F3.refl_mem_reflGroup v₀⟩ = r :=
        Subtype.ext ((hι _).trans hrv.symm)
      simp [φ, this, ← her]

end Aux

theorem hasCoreStar_of_isReflModel_three {L : Type} [Group L] {D : Set L} {t : L} (ht : t ∈ D)
    {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (h : IsReflModel 3 6 f L D ∨ IsReflQuotModel 3 6 f L D) : CoreStar.HasCoreStar L t :=
  hasCoreStar_aux ⟨hsymm, hnd⟩ (by norm_num) ht h

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical
