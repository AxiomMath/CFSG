module

import CFSG.RankThree.GF2n.Tim81.Sec6.RootImages
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.GroupTheory.MulAutInner
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCharacteristic
public import CFSG.RankThree.GF2n.Tim81.Sec7.S73BarIso

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n.Tim81.Sec7 (yOf rOf oOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

theorem IsSUImage.map_of_injective {K L : Type} [Group K] [Group L] {X : Subgroup K}
    {Δ : Set (Subgroup K)} {f m : ℕ} {hf : 1 ≤ f} {hm : 2 ≤ m} (hX : IsSUImage X Δ f m hf hm)
    (ψ : K →* L) (hψ : Function.Injective ψ) :
    IsSUImage (X.map ψ) ((fun U => U.map ψ) '' Δ) f m hf hm := by
  obtain ⟨Φ, hker, hrange, hclass⟩ := hX
  refine ⟨ψ.comp Φ, (MonoidHom.ker_comp_of_injective Φ ψ hψ).le.trans hker,
    by rw [MonoidHom.range_comp, hrange], fun U => ⟨?_, ?_⟩⟩
  · rintro ⟨W, hW, rfl⟩
    obtain ⟨x, rfl⟩ := (hclass W).mp hW
    exact ⟨x, Subgroup.map_map _ ψ Φ⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, (hclass _).mpr ⟨x, rfl⟩, Subgroup.map_map _ ψ Φ⟩

theorem mem_normalizer_yOf_of_conj_eq_inv {t : G} (ht : t * h * t⁻¹ = h⁻¹) :
    t ∈ Subgroup.normalizer (yOf h : Set G) := by
  have hz : conjSubgroup t (Subgroup.zpowers h) = Subgroup.zpowers h := by
    change (Subgroup.zpowers h).map (MulAut.conj t).toMonoidHom = _
    simp only [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ht,
      Subgroup.zpowers_inv]
  rw [yOf, ← conjSubgroup_eq_self_iff]
  change conjSubgroup t (Subgroup.centralizer (Subgroup.zpowers h : Set G)) =
    Subgroup.centralizer (Subgroup.zpowers h : Set G)
  rw [← CFSG.CGT.Timmesfeld75.centralizer_conjSubgroup_eq, hz]

theorem exists_mulAut_yBar_conj {t : G} (ht : t ∈ Subgroup.normalizer (yOf h : Set G)) :
    ∃ σ : MulAut (YBar h), ∀ (y : G) (hy : y ∈ yOf h) (hty : t * y * t⁻¹ ∈ yOf h),
      σ (QuotientGroup.mk (⟨y, hy⟩ : ↥(yOf h))) =
        QuotientGroup.mk (⟨t * y * t⁻¹, hty⟩ : ↥(yOf h)) := by
  let α : MulAut ↥(yOf h) := (yOf h).normalizerMonoidHom ⟨t, ht⟩
  have he : (pPrimeCore 2 ↥(yOf h)).map
      (α : ↥(yOf h) →* ↥(yOf h)) = pPrimeCore 2 ↥(yOf h) := by
    rw [← MulEquiv.toMonoidHom_eq_coe]
    exact pPrimeCore_map_iso 2 α
  exact ⟨QuotientGroup.congr _ _ α he, fun y hy hty => rfl⟩

namespace EpsIn

theorem comap_conj_le_pCore (hE : EpsIn M V h) {X₀ : Subgroup (YBar h)} [X₀.Normal]
    (hκ : Function.Injective (MulAut.conj : YBar h →* MulAut (YBar h))) :
    (inSubgroup (pCore 2) (X₀.map (MulAut.conj : YBar h →* MulAut (YBar h)) ⊓
        Subgroup.normalizer (((barY h V).map (MulAut.conj : YBar h →* MulAut (YBar h)) :
          Subgroup (MulAut (YBar h))) : Set (MulAut (YBar h))))).comap
      (MulAut.conj : YBar h →* MulAut (YBar h)) ≤ inSubgroup (pCore 2) (barY h (rOf M h)) := by
  obtain ⟨hQ2, hQS, -⟩ := inSubgroup_pCore_two (X₀.map
    (MulAut.conj : YBar h →* MulAut (YBar h)) ⊓
      Subgroup.normalizer (((barY h V).map (MulAut.conj : YBar h →* MulAut (YBar h)) :
        Subgroup (MulAut (YBar h))) : Set (MulAut (YBar h))))
  refine le_inSubgroup_pCore ?_ ?_ (hQ2.comap_of_injective _ hκ)
  · intro y hy
    have h1 := (hQS (Subgroup.mem_comap.mp hy)).2
    rw [← hE.normalizer_barY, ← conjSubgroup_eq_self_iff]
    apply Subgroup.map_injective hκ
    rw [CFSG.CGT.Timmesfeld75.map_conjSubgroup]
    exact conjSubgroup_eq_self_iff.mpr h1
  · intro r hr
    have h1 : MulAut.conj r ∈ Subgroup.normalizer
        ((X₀.map (MulAut.conj : YBar h →* MulAut (YBar h)) : Subgroup (MulAut (YBar h))) :
          Set (MulAut (YBar h))) := by
      rw [← conjSubgroup_eq_self_iff, ← CFSG.CGT.Timmesfeld75.map_conjSubgroup,
        conjSubgroup_eq_self_iff.mpr ((Subgroup.normalizer_eq_top X₀).ge (Subgroup.mem_top r))]
    have h2 : MulAut.conj r ∈ Subgroup.normalizer
        (((barY h V).map (MulAut.conj : YBar h →* MulAut (YBar h)) :
          Subgroup (MulAut (YBar h))) : Set (MulAut (YBar h))) := by
      rw [← conjSubgroup_eq_self_iff, ← CFSG.CGT.Timmesfeld75.map_conjSubgroup,
        conjSubgroup_eq_self_iff.mpr (hE.normalizer_barY.ge hr)]
    exact Subgroup.le_normalizer_comap (MulAut.conj : YBar h →* MulAut (YBar h))
      (Subgroup.mem_comap.mpr (mem_normalizer_map_subtype_of_characteristic
        (mem_normalizer_inf h1 (Subgroup.le_normalizer h2))
        (pCore 2 ↥(X₀.map (MulAut.conj : YBar h →* MulAut (YBar h)) ⊓ Subgroup.normalizer
          (((barY h V).map (MulAut.conj : YBar h →* MulAut (YBar h)) :
            Subgroup (MulAut (YBar h))) : Set (MulAut (YBar h)))))))

theorem mem_centralizer_of_forall_apply_eq (hE : EpsIn M V h) {X₀ : Subgroup (YBar h)}
    [X₀.Normal] (hκ : Function.Injective (MulAut.conj : YBar h →* MulAut (YBar h)))
    {σ : MulAut (YBar h)}
    (hσ : ∀ x ∈ inSubgroup (pCore 2) (barY h (rOf M h)), σ x = x) :
    σ ∈ Subgroup.centralizer ((inSubgroup (pCore 2)
      (X₀.map (MulAut.conj : YBar h →* MulAut (YBar h)) ⊓ Subgroup.normalizer
        (((barY h V).map (MulAut.conj : YBar h →* MulAut (YBar h)) :
          Subgroup (MulAut (YBar h))) : Set (MulAut (YBar h)))) :
      Subgroup (MulAut (YBar h))) : Set (MulAut (YBar h))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro τ hτ
  obtain ⟨-, hQS, -⟩ := inSubgroup_pCore_two (X₀.map
    (MulAut.conj : YBar h →* MulAut (YBar h)) ⊓
      Subgroup.normalizer (((barY h V).map (MulAut.conj : YBar h →* MulAut (YBar h)) :
        Subgroup (MulAut (YBar h))) : Set (MulAut (YBar h))))
  obtain ⟨y, -, rfl⟩ := (hQS hτ).1
  have hyO : y ∈ inSubgroup (pCore 2) (barY h (rOf M h)) :=
    hE.comap_conj_le_pCore (X₀ := X₀) hκ (Subgroup.mem_comap.mpr hτ)
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hσ y hyO]

theorem eq_one_of_commute_mk (hE : EpsIn M V h) {c : G} (hcY : c ∈ yOf h)
    (hcR : c ∉ rOf M h) {v : YBar h} (hv : v ∈ barY h V)
    (hvc : v * QuotientGroup.mk (⟨c, hcY⟩ : ↥(yOf h)) =
      QuotientGroup.mk (⟨c, hcY⟩ : ↥(yOf h)) * v) : v = 1 := by
  by_contra hv1
  have hvc' : v ∈ conjSubgroup (QuotientGroup.mk (⟨c, hcY⟩ : ↥(yOf h)) : YBar h)
      (barY h V) := by
    rw [mem_conjSubgroup, mul_assoc, hvc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hv
  have hne : barY h V ⊓
      conjSubgroup (QuotientGroup.mk (⟨c, hcY⟩ : ↥(yOf h)) : YBar h) (barY h V) ≠ ⊥ := by
    intro hbot
    exact hv1 (Subgroup.mem_bot.mp (hbot.le (Subgroup.mem_inf.mpr ⟨hv, hvc'⟩)))
  have hN := conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_isTI hE.isTI_barY hne)
  rw [hE.normalizer_barY] at hN
  exact hcR (hE.mem_rOf_of_bar_mem hcY hN)

theorem eq_one_of_forall_apply_eq (hE : EpsIn M V h) {P : Subgroup G}
    (hP : inSubgroup (pCore 2) (barY h (rOf M h)) = barY h P)
    {X₀ : Subgroup (YBar h)} (hX₀ : ∀ α : MulAut (YBar h), X₀.map α.toMonoidHom = X₀)
    (hC : Subgroup.centralizer (X₀ : Set (YBar h)) = ⊥) (hf : 1 ≤ f)
    (hn : 4 ≤ n) (hSU : IsSUImage X₀ (barRoots h V) f n hf (Nat.le_trans (Nat.le_add_left 2 2) hn))
    {c : G} (hcY : c ∈ yOf h) (hcR : c ∉ rOf M h) {σ : MulAut (YBar h)}
    (hσP : ∀ x ∈ barY h P, σ x = x)
    (hσc : σ (QuotientGroup.mk (⟨c, hcY⟩ : ↥(yOf h))) =
      QuotientGroup.mk ⟨c, hcY⟩) : σ = 1 := by
  have hZ : Subgroup.center (YBar h) = ⊥ :=
    eq_bot_iff.mpr (hC ▸ Subgroup.center_le_centralizer (X₀ : Set (YBar h)))
  have hκ := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  haveI : X₀.Characteristic := Subgroup.characteristic_iff_map_eq.mpr hX₀
  have hnorm : (X₀.map (MulAut.conj : YBar h →* MulAut (YBar h))).Normal := by
    have h := CFSG.ComponentClassification.CatalogueSchreierCharacteristic.innerSubgroup_normal X₀
    rwa [CFSG.ComponentClassification.CatalogueSchreierCharacteristic.innerSubgroup,
      MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hC' := CFSG.GroupTheory.centralizer_map_mulAut_conj_eq_bot hC
  have hSU' := hSU.map_of_injective MulAut.conj hκ
  have hT' : (barY h V).map (MulAut.conj : YBar h →* MulAut (YBar h)) ∈
      (fun U : Subgroup (YBar h) => U.map (MulAut.conj : YBar h →* MulAut (YBar h))) ''
        barRoots h V := ⟨barY h V, ⟨1, (conjSubgroup_one _).symm⟩, rfl⟩
  haveI := hnorm
  have hcen := hSU'.centralizer_pCore_le hn hT'
  have hσT := hcen (hE.mem_centralizer_of_forall_apply_eq (X₀ := X₀) hκ
    fun x hx => hσP x (hP.le hx))
  rw [hC', sup_bot_eq] at hσT
  obtain ⟨v, hv, rfl⟩ := hσT
  rw [MulAut.conj_apply] at hσc
  have hvc := mul_inv_eq_iff_eq_mul.mp hσc
  rw [hE.eq_one_of_commute_mk hcY hcR hv hvc, map_one]

end EpsIn

end CFSG.RankThree.GF2n.Tim81
