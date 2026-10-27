module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.EvenBN.GMSK.CatEvenBenderOuter
import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.NotF3
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418IndexTwo
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

omit [Finite X] in
theorem orderOf_conjNormal_eq_two [K.Normal] {z : X} (hz2 : orderOf z = 2)
    (hout : ∀ k ∈ K, ∃ x ∈ K, z * x * z⁻¹ ≠ k * x * k⁻¹) :
    orderOf (MulAut.conjNormal (H := K) z) = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at h
  set ψ := MulAut.conjNormal (H := K) z with hψ
  have hψ2 : ψ ^ 2 = 1 := by
    have h : MulAut.conjNormal (H := K) (z ^ 2) = (MulAut.conjNormal (H := K) z) ^ 2 :=
      map_pow _ _ _
    rw [pow_two, hzsq, map_one] at h
    exact h.symm
  have hψne : ψ ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hxne⟩ := hout 1 K.one_mem
    have hval : (ψ ⟨x, hx⟩).val = x := by
      have h2 : ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [h1]; rfl
      exact congrArg Subtype.val h2
    have hform : (ψ ⟨x, hx⟩).val = z * x * z⁻¹ := by
      simp [ψ, MulAut.conjNormal_apply]
    rw [hform] at hval
    exact hxne (by rw [hval]; group)
  exact @orderOf_eq_prime _ _ _ 2 hfact hψ2 hψne

omit [Finite X] in
theorem conjNormal_not_mem_range [K.Normal] {z : X}
    (hout : ∀ k ∈ K, ∃ x ∈ K, z * x * z⁻¹ ≠ k * x * k⁻¹) :
    MulAut.conjNormal (H := K) z ∉ (MulAut.conj : ↥K →* MulAut ↥K).range := by
  rintro ⟨k, hk⟩
  obtain ⟨x, hx, hxne⟩ := hout k k.2
  have hval : (MulAut.conjNormal (H := K) z ⟨x, hx⟩).val = (MulAut.conj k ⟨x, hx⟩).val := by
    rw [← hk]
  simp [MulAut.conjNormal_apply, MulAut.conj_apply] at hval
  exact hxne hval

omit [Finite X] in
theorem map_fixedSubgroup_conjNormal [K.Normal] (z : X) :
    (fixedSubgroup (MulAut.conjNormal (H := K) z)).map K.subtype =
      K ⊓ centralizer ({z} : Set X) := by
  ext y
  constructor
  · intro hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hx' : (MulAut.conjNormal (H := K) z) x = x := by
      simpa [fixedSubgroup] using hx
    have h := congrArg Subtype.val hx'
    simp [MulAut.conjNormal_apply] at h
    refine ⟨x.2, ?_⟩
    change x.val ∈ centralizer ({z} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x.val * z = (z * x.val * z⁻¹) * z := by rw [h]
      _ = z * x.val := by group
  · rintro ⟨hyK, hyC⟩
    refine Subgroup.mem_map.mpr ⟨⟨y, hyK⟩, ?_, rfl⟩
    change (MulAut.conjNormal (H := K) z) ⟨y, hyK⟩ = ⟨y, hyK⟩
    change y ∈ centralizer ({z} : Set X) at hyC
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC
    apply Subtype.ext
    simp [MulAut.conjNormal_apply]
    calc z * y * z⁻¹ = (y * z) * z⁻¹ := by rw [hyC.symm]
      _ = y := by group

namespace CoreSetup

theorem lieModel_psp_of_outer
    (h : CoreSetup X K L T Y n) (hev : CFSG.Blueprint.EvenLieType (↥K ⧸ center ↥K))
    (hL2 : CFSG.Open.pCoreOf 2 L = ⊥) {z : X} (hz2 : orderOf z = 2)
    (hcomp : CFSG.Open.IsComponentOf L (K ⊓ centralizer ({z} : Set X)))
    (hout : ∀ k ∈ K, ∃ x ∈ K, z * x * z⁻¹ ≠ k * x * k⁻¹) :
    CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .PSp 2 2 n := by
  classical
  have hNormal : K.Normal := h.normal
  have hKperf : Group.IsPerfect ↥K := (Group.isPerfect_def (G := ↥K)).mpr h.quasisimple.1
  let ψ : MulAut ↥K := (@MulAut.conjNormal X _ K hNormal) z
  have hψ_order : orderOf ψ = 2 := @orderOf_conjNormal_eq_two X _ K hNormal z hz2 hout
  have hψ_not_inner : ψ ∉ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    @conjNormal_not_mem_range X _ K hNormal z hout
  have hψ2 : ψ ^ 2 = 1 := by
    rw [← hψ_order]
    exact pow_orderOf_eq_one ψ
  have hmap : (fixedSubgroup ψ).map K.subtype = K ⊓ centralizer ({z} : Set X) :=
    @map_fixedSubgroup_conjNormal X _ K hNormal z
  let C : Subgroup X := centralizer ({z} : Set X)
  have hcomp' : CFSG.Open.IsComponentOf L (K ⊓ C) := hcomp
  have hLK : L ≤ K ⊓ C := hcomp'.1
  have hLC : L ≤ C := hLK.trans inf_le_right
  let e₁ : ↥(fixedSubgroup ψ) ≃* ↥((fixedSubgroup ψ).map K.subtype) :=
    Subgroup.equivMapOfInjective (fixedSubgroup ψ) K.subtype K.subtype_injective
  let e₂ : ↥((fixedSubgroup ψ).map K.subtype) ≃* ↥(K ⊓ C) :=
    MulEquiv.subgroupCongr hmap
  let e : ↥(fixedSubgroup ψ) ≃* ↥(K ⊓ C) := e₁.trans e₂
  let M : Subgroup ↥(fixedSubgroup ψ) := (L.subgroupOf K).subgroupOf (fixedSubgroup ψ)
  have hL_le_fixed : L.subgroupOf K ≤ fixedSubgroup ψ := by
    intro x hx
    change ψ x = x
    apply Subtype.ext
    have hxL : x.val ∈ L := hx
    have hxC : x.val ∈ C := hLC hxL
    change x.val ∈ centralizer ({z} : Set X) at hxC
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    simp [ψ, @MulAut.conjNormal_apply X _ K hNormal]
    calc z * x.val * z⁻¹ = (x.val * z) * z⁻¹ := by rw [hxC]
      _ = x.val := by group
  have hcomp_subgroup : CFSG.IsComponent (L.subgroupOf (K ⊓ C)) := by
    have hcomp_assembly : CFSG.Assembly.IsComponentOf L (K ⊓ C) :=
      CFSG.Assembly.isComponentOf_iff_open.mpr hcomp'
    exact (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLK).mp
      hcomp_assembly
  have hMmap : M.map e.toMonoidHom = L.subgroupOf (K ⊓ C) := by
    apply Subgroup.map_injective (f := (K ⊓ C).subtype) (K ⊓ C).subtype_injective
    rw [Subgroup.map_map]
    have hcomp_e : (K ⊓ C).subtype.comp e.toMonoidHom =
        K.subtype.comp (fixedSubgroup ψ).subtype := by
      ext x
      rfl
    rw [hcomp_e, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hL_le_fixed,
      Subgroup.map_subgroupOf_eq_of_le h.le, Subgroup.map_subgroupOf_eq_of_le hLK]
  have hM : CFSG.IsComponent M :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponent_map_iff e M).1
      (by rw [hMmap]; exact hcomp_subgroup)
  have hLcore : CFSG.pCore 2 ↥L = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp
      (by simpa [CFSG.Open.pCoreOf] using hL2)
  let eBar : Bar2 L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hLcore).trans QuotientGroup.quotientBot
  have hLsimpleBar : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h.sz
  have hSimpleL : IsSimpleGroup ↥L := eBar.symm.isSimpleGroup
  obtain ⟨a, b, hab⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h.sz
  have hNonabL : ∃ a b : ↥L, a * b ≠ b * a := by
    refine ⟨eBar a, eBar b, ?_⟩
    intro hba
    apply hab
    have h' : eBar (a * b) = eBar (b * a) := by rw [map_mul, map_mul, hba]
    exact eBar.injective h'
  have hLq : CFSG.IsQuasisimple ↥L :=
    (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ↥L _ hSimpleL hNonabL).1
  have hcenterL : Subgroup.center ↥L = ⊥ :=
    (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ↥L _ hSimpleL hNonabL).2
  let eML : ↥M ≃* ↥L :=
    (Subgroup.subgroupOfEquivOfLe hL_le_fixed).trans (Subgroup.subgroupOfEquivOfLe h.le)
  have hcenterM : Subgroup.center ↥M = ⊥ := by
    have h1 : (Subgroup.center ↥M).map eML.toMonoidHom = ⊥ := by
      rw [show (Subgroup.center ↥M).map eML.toMonoidHom = Subgroup.center ↥L from by
        exact Subgroup.map_center_eq eML, hcenterL]
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥M) (f := eML.toMonoidHom)
      eML.injective).mp h1
  let eMbar : (↥M ⧸ Subgroup.center ↥M) ≃* ↥M :=
    (QuotientGroup.quotientMulEquivOfEq hcenterM).trans QuotientGroup.quotientBot
  let eToBar2 : Bar2 L ≃* (↥M ⧸ Subgroup.center ↥M) :=
    eBar.trans (eML.symm.trans eMbar.symm)
  have hLieModelM : CFSG.Blueprint.LieModel (↥M ⧸ Subgroup.center ↥M) .twistedB2 0 2 n :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eToBar2 h.sz
  have hinv : (Subgroup.center ↥K).map ψ.toMonoidHom = Subgroup.center ↥K :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) ψ
  let σ : MulAut (↥K ⧸ Subgroup.center ↥K) :=
    CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient
      (Subgroup.center ↥K) ψ hinv
  obtain ⟨D, hD, ⟨eD⟩⟩ :=
    CFSG.EvenSporadicStandard.M12Std.Rbc.exists_isComponent_fixed_onQuotient
      (Subgroup.center ↥K) le_rfl ψ hinv hM
  have hLieModelD : CFSG.Blueprint.LieModel (↥D ⧸ Subgroup.center ↥D) .twistedB2 0 2 n :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hLieModelM
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    change σ (σ (QuotientGroup.mk' (Subgroup.center ↥K) y)) =
      QuotientGroup.mk' (Subgroup.center ↥K) y
    rw [CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient_mk,
      CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient_mk]
    rw [show ψ (ψ y) = y from by
      simpa [pow_two] using congrArg (fun f : MulAut ↥K => f y) hψ2]
  have hσ_eq : σ = CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient ψ := by
    ext x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
    rw [CFSG.ComponentClassification.CatalogueBFixedCentralQuotient.onQuotient_mk,
      CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  have hσne : σ ≠ 1 := by
    intro hσ1
    have hψ1 : ψ = 1 :=
      @CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp
        ↥K _ hKperf ψ (by
        rw [← hσ_eq]
        exact hσ1)
    exact hψ_not_inner (by
      rw [hψ1]
      exact MonoidHom.mem_range.mpr ⟨1, map_one _⟩)
  have hσ_not_inner : σ ∉ (MulAut.conj : (↥K ⧸ Subgroup.center ↥K) →*
      MulAut (↥K ⧸ Subgroup.center ↥K)).range := by
    rintro ⟨kbar, hkbar⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) kbar
    let τ : MulAut ↥K := (MulAut.conj k)⁻¹ * ψ
    have hconj : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient
        (MulAut.conj k) =
        MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥K) k) := by
      ext x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) x
      rw [CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk,
        MulAut.conj_apply, MulAut.conj_apply]
      simp [map_mul, map_inv]
    have hτ : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient τ = 1 := by
      have hconj' : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K
          (MulAut.conj k) =
          MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥K) k) := hconj
      have hψσ : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K ψ = σ :=
        hσ_eq.symm
      change CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K
        ((MulAut.conj k)⁻¹ * ψ) = 1
      rw [map_mul, map_inv, hconj', hψσ, hkbar, inv_mul_cancel]
    have hτ1 : τ = 1 :=
      @CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp
        ↥K _ hKperf τ hτ
    have hψ_eq : ψ = MulAut.conj k := by
      rw [show τ = (MulAut.conj k)⁻¹ * ψ from rfl] at hτ1
      exact (inv_mul_eq_one.mp hτ1).symm
    exact hψ_not_inner (MonoidHom.mem_range.mpr ⟨k, hψ_eq.symm⟩)
  have hσ_order : orderOf σ = 2 := by
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact @orderOf_eq_prime _ _ _ 2 hfact hσ2 hσne
  have hS_simple : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.quasisimple.2
  have hS_nonab : ∃ a b : (↥K ⧸ Subgroup.center ↥K), a * b ≠ b * a :=
    (CFSG.Quasithin.EmptyFaithfulMultiple.Insp15418.isQuasisimple_of_open h.quasisimple).2.2
  have hcat := CFSG.LocalAnalysis.EvenBN.GMSK.catSzEvenOuterList n
  exact hcat (↥K ⧸ Subgroup.center ↥K) hS_simple hS_nonab hev σ hσ_order hσ_not_inner
    D hD hLieModelD


end CoreSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
