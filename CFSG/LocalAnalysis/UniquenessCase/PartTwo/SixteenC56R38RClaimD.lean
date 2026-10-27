module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Model
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38B
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38ROrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma mem_normalizer_inf_centralizer_singleton {V : Subgroup G} {y f : G}
    (hfV : f ∈ Subgroup.normalizer (V : Set G))
    (hfC : f ∈ Subgroup.centralizer ({y} : Set G)) :
    f ∈ Subgroup.normalizer ((V ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    obtain ⟨hdV, hdC⟩ := Subgroup.mem_inf.1 hd
    exact Subgroup.mem_inf.2
      ⟨(Subgroup.mem_normalizer_iff.1 hfV d).1 hdV,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hfC hdC) (Subgroup.inv_mem _ hfC)⟩
  · intro hd
    obtain ⟨hdV, hdC⟩ := Subgroup.mem_inf.1 hd
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hfV d).2 hdV, ?_⟩
    have h1 : d = f⁻¹ * (f * d * f⁻¹) * f := by group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hfC) hdC) hfC

theorem r38_exists_involution_two_le_pRank_of_fixed_line {M N V₀ V F : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMV : M ≤ normalizer (V : Set G)) (hV₀ : Nat.card V₀ ≤ 4)
    (hFM : F ≤ M) (hF : IsElemAbelian 3 F) (hFcard : Nat.card F = 3 ^ 3) {y : G} (hyF : y ∈ F)
    (hys : y ∈ stabTil V₀ V) (hy3 : y ^ 3 = 1) (hCV : ∀ v ∈ V, y * v * y⁻¹ = v → v ∈ N)
    (S : OmegaModel (Vtil V₀ V hV)) (hK : Nat.card S.K = 4) {e : Vtil V₀ V hV} (he1 : e ≠ 1)
    (hfix : ∀ w : Vtil V₀ V hV, actTil V₀ V hV ⟨y, hys⟩ w = w ↔ ∃ c : S.K, w = S.smul c e) :
    ∃ v ∈ N, v ≠ 1 ∧ v ^ 2 = 1 ∧ 2 ≤ CFSG.Open.pRank 3 (M ⊓ centralizer ({v} : Set G)) := by
  classical
  let Dp : Subgroup G := V ⊓ Subgroup.centralizer ({y} : Set G)
  have hD : IsElemAbelian 2 Dp := hV.mono inf_le_left
  have hDn : F ≤ Subgroup.normalizer (Dp : Set G) := by
    intro f hf
    have hfC : f ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hF.comm hf hyF)
    exact mem_normalizer_inf_centralizer_singleton (hMV (hFM hf)) hfC
  have hDcard : Nat.card Dp ≤ 16 := by
    let Dp' : Subgroup (IntMod V hV) := Dp.subgroupOf V
    have hcard' : Nat.card Dp' = Nat.card Dp :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Dp ≤ V)).toEquiv
    let φ : Dp' →* Vtil V₀ V hV := (mkTil V₀ V hV).comp Dp'.subtype
    have hker : Nat.card φ.ker ≤ 4 := by
      have hmem : ∀ d : φ.ker, (d.1.1 : IntMod V hV).val ∈ V₀ := by
        intro d
        have hd1 : φ d.1 = 1 := d.2
        have h : mkTil V₀ V hV d.1.1 = mkTil V₀ V hV (1 : IntMod V hV) := by
          rw [map_one]
          exact hd1
        rw [mkTil_eq_iff] at h
        simpa using h
      let ψ : φ.ker → V₀ := fun d => ⟨(d.1.1 : IntMod V hV).val, hmem d⟩
      have hinj : Function.Injective ψ := by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        apply IntMod.val_injective
        exact congrArg (fun z : V₀ => (z : G)) hab
      calc Nat.card φ.ker ≤ Nat.card V₀ := Nat.card_le_card_of_injective ψ hinj
        _ ≤ 4 := hV₀
    have hrange : Nat.card φ.range ≤ 4 := by
      have hx : ∀ x : φ.range, ∃ c : S.K, (x : Vtil V₀ V hV) = S.smul c e := by
        intro x
        obtain ⟨d, hd⟩ := MonoidHom.mem_range.1 x.2
        have hstab : actStab V₀ V hV ⟨y, hys⟩ d.1 = d.1 := by
          apply IntMod.val_injective
          rw [actStab_apply_val]
          have hmem : (d.1 : IntMod V hV).val ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := d.2
          have hdy : (d.1 : IntMod V hV).val * y = y * (d.1 : IntMod V hV).val :=
            Subgroup.mem_centralizer_singleton_iff.1 hmem.2
          rw [← hdy, mul_assoc, mul_inv_cancel, mul_one]
        have hfixd : actTil V₀ V hV ⟨y, hys⟩ (mkTil V₀ V hV d.1) =
            mkTil V₀ V hV d.1 := by
          rw [actTil_mk, hstab]
        have hw : actTil V₀ V hV ⟨y, hys⟩ (φ d) = φ d := by
          change actTil V₀ V hV ⟨y, hys⟩ (mkTil V₀ V hV d.1) = mkTil V₀ V hV d.1
          exact hfixd
        obtain ⟨c, hc⟩ := (hfix (φ d)).1 hw
        exact ⟨c, by rw [← hd]; exact hc⟩
      let f : φ.range → S.K := fun x => Classical.choose (hx x)
      have hf : ∀ x : φ.range, (x : Vtil V₀ V hV) = S.smul (f x) e :=
        fun x => Classical.choose_spec (hx x)
      have hinj : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        rw [hf a, hf b, hab]
      calc Nat.card φ.range ≤ Nat.card S.K := Nat.card_le_card_of_injective f hinj
        _ = 4 := hK
    calc Nat.card Dp = Nat.card Dp' := hcard'.symm
      _ = Nat.card φ.ker * Nat.card φ.range := (Subgroup.card_ker_mul_card_range φ).symm
      _ ≤ 4 * 4 := Nat.mul_le_mul hker hrange
      _ = 16 := by norm_num
  have hD1 : Dp ≠ ⊥ := by
    have hefix : actTil V₀ V hV ⟨y, hys⟩ e = e :=
      (hfix e).2 ⟨1, (S.smul_one_eq e).symm⟩
    obtain ⟨v, hv_e, hv_fix⟩ :=
      exists_fixed_lift_of_pow_eq_one hV hys (show Odd 3 from ⟨1, by norm_num⟩) hy3 hefix
    have hvDp : v.val ∈ Dp :=
      ⟨IntMod.val_mem v, by
        change v.val ∈ Subgroup.centralizer ({y} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (mul_inv_eq_iff_eq_mul.mp hv_fix).symm⟩
    have hvne : v.val ≠ 1 := by
      intro h
      apply he1
      rw [← hv_e]
      have hv1 : v = 1 := IntMod.val_injective (by rw [h, IntMod.val_one])
      rw [hv1, map_one]
    intro hbot
    exact hvne (by rw [hbot] at hvDp; exact Subgroup.mem_bot.1 hvDp)
  obtain ⟨v, hvDp, hv1, hvrank⟩ :=
    exists_ne_one_two_le_pRank_of_card_le_sixteen hF hFcard hDn hD hD1 hDcard
  refine ⟨v, ?_, hv1, ?_, ?_⟩
  · exact hCV v hvDp.1 (by
      have hvC : v * y = y * v := Subgroup.mem_centralizer_singleton_iff.1 hvDp.2
      rw [← hvC, mul_assoc, mul_inv_cancel, mul_one])
  · exact hV.2 v hvDp.1
  · exact le_trans hvrank (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3)
      (inf_le_inf hFM le_rfl))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
