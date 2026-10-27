module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.GroupTheory.OddCentralQuotient
public import Mathlib.Algebra.Group.Commutator

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

private theorem irgTG_mem_center_range_iff {K G : Type*} [Group K] [Group G] (φ : K →* G)
    (hperf : commutator K = ⊤) (hk : φ.ker ≤ Subgroup.center K) (x : K) :
    φ.rangeRestrict x ∈ Subgroup.center ↥φ.range ↔ x ∈ Subgroup.center K := by
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hmem : ∀ z : K, ⁅x, z⁆ ∈ Subgroup.center K := by
      intro z
      apply hk
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hcomm : Commute (φ.rangeRestrict x) (φ.rangeRestrict z) :=
        (Subgroup.mem_center_iff.mp hx (φ.rangeRestrict z)).symm
      have hmap : ⁅φ x, φ z⁆ =
          φ.range.subtype ⁅φ.rangeRestrict x, φ.rangeRestrict z⁆ := by
        rw [show φ x = φ.range.subtype (φ.rangeRestrict x) from rfl,
          show φ z = φ.range.subtype (φ.rangeRestrict z) from rfl, ← map_commutatorElement]
      rw [hmap, hcomm.commutator_eq, map_one]
    let f : K →* ↥(Subgroup.center K) :=
      { toFun := fun z => ⟨⁅x, z⁆, hmem z⟩
        map_one' := by
          apply Subtype.ext
          change ⁅x, 1⁆ = 1
          rw [commutatorElement_one_right]
        map_mul' := by
          intro z w
          apply Subtype.ext
          change ⁅x, z * w⁆ = ⁅x, z⁆ * ⁅x, w⁆
          rw [commutatorElement_mul_right_eq_mul_conj]
          have hcw : z * (⁅x, w⁆ * z⁻¹) = ⁅x, w⁆ := by
            rw [← mul_assoc, Subgroup.mem_center_iff.mp (hmem w) z, mul_assoc, mul_inv_cancel,
              mul_one]
          simp only [mul_assoc]
          rw [hcw] }
    haveI : IsMulCommutative ↥(Subgroup.center K) := Subgroup.center.isMulCommutative K
    have hfker : f.ker = ⊤ := by
      rw [eq_top_iff, ← hperf]
      exact Abelianization.commutator_subset_ker f
    have hy1 : f y = 1 := MonoidHom.mem_ker.mp (by rw [hfker]; trivial)
    have hcommy : ⁅x, y⁆ = 1 :=
      congrArg (fun t : ↥(Subgroup.center K) => (t : K)) hy1
    exact (commutatorElement_eq_one_iff_mul_comm.mp hcommy).symm
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp w.2
    have hw : w = φ.rangeRestrict z := by
      apply Subtype.ext
      exact hz.symm
    rw [hw]
    apply Subtype.ext
    show φ z * φ x = φ x * φ z
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]

private theorem irgTG_center_range_odd {K G : Type*} [Group K] [Group G] (φ : K →* G)
    (hperf : commutator K = ⊤) (hk : φ.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card (Subgroup.center K))) :
    Odd (Nat.card (Subgroup.center ↥φ.range)) := by
  have hcenter : Subgroup.center ↥φ.range = (Subgroup.center K).map φ.rangeRestrict := by
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp z.2
      have hEq : φ.rangeRestrict x = z := by
        apply Subtype.ext
        exact hx
      refine Subgroup.mem_map.mpr ⟨x, ?_, hEq⟩
      have hxcenter : φ.rangeRestrict x ∈ Subgroup.center ↥φ.range := by
        rwa [hEq]
      exact (irgTG_mem_center_range_iff φ hperf hk x).mp hxcenter
    · intro hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact (irgTG_mem_center_range_iff φ hperf hk x).mpr hx
  rw [hcenter]
  exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd (Subgroup.center K) φ.rangeRestrict)

private theorem irgTG_exists_aut {K G : Type*} [Group K] [Group G] (φ φ' : K →* G)
    (hr : φ'.range = φ.range) (hperf : commutator K = ⊤)
    (hk : φ.ker ≤ Subgroup.center K) (hk' : φ'.ker ≤ Subgroup.center K) :
    ∃ θ : MulAut (K ⧸ Subgroup.center K),
      ∀ x y : K, θ (QuotientGroup.mk' (Subgroup.center K) x) =
          QuotientGroup.mk' (Subgroup.center K) y →
        φ' x * (φ y)⁻¹ ∈ (Subgroup.center ↥φ.range).map φ.range.subtype := by
  let J : Subgroup G := φ.range
  let ψ : K →* J := φ.rangeRestrict
  let e : φ'.range ≃* J := MulEquiv.subgroupCongr hr
  let ψ' : K →* J := e.toMonoidHom.comp φ'.rangeRestrict
  let mkZ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let mkJ : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  let π : K →* J ⧸ Subgroup.center J := mkJ.comp ψ
  let π' : K →* J ⧸ Subgroup.center J := mkJ.comp ψ'
  have hψ : ∀ x : K, J.subtype (ψ x) = φ x := fun x => rfl
  have hψ' : ∀ x : K, J.subtype (ψ' x) = φ' x := fun x =>
    MulEquiv.subgroupCongr_apply hr (φ'.rangeRestrict x)
  have hπker : π.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (ψ x : J ⧸ Subgroup.center J) = 1 ↔ x ∈ Subgroup.center K
    rw [QuotientGroup.eq_one_iff]
    exact irgTG_mem_center_range_iff φ hperf hk x
  have hπ'ker : π'.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (ψ' x : J ⧸ Subgroup.center J) = 1 ↔ x ∈ Subgroup.center K
    rw [QuotientGroup.eq_one_iff]
    have hmem : ψ' x ∈ Subgroup.center J ↔ φ'.rangeRestrict x ∈ Subgroup.center ↥φ'.range := by
      constructor
      · intro h
        rw [Subgroup.mem_center_iff] at h ⊢
        intro w
        apply e.injective
        rw [map_mul, map_mul]
        exact h (e w)
      · intro h
        rw [Subgroup.mem_center_iff] at h ⊢
        intro g
        obtain ⟨w, rfl⟩ := e.surjective g
        rw [show ψ' x = e (φ'.rangeRestrict x) from rfl]
        rw [← map_mul, ← map_mul]
        exact congrArg e (h w)
    exact hmem.trans (irgTG_mem_center_range_iff φ' hperf hk' x)
  have hπsurj : Function.Surjective π := by
    intro y
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp j.2
    exact ⟨x, by
      show mkJ (ψ x) = mkJ j
      congr 1
      apply Subtype.ext
      change J.subtype (ψ x) = J.subtype j
      rw [hψ x]
      exact hx⟩
  let Φ : K ⧸ Subgroup.center K →* J ⧸ Subgroup.center J :=
    QuotientGroup.lift (Subgroup.center K) π (le_of_eq hπker.symm)
  have hΦmk : ∀ x : K, Φ (mkZ x) = π x := fun x => rfl
  have hΦinj : Function.Injective Φ := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) b
    have hab' : π x = π y := hab
    have h1 : π (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hab', mul_inv_cancel]
    have h2 : x * y⁻¹ ∈ Subgroup.center K := by
      rw [← hπker]
      exact MonoidHom.mem_ker.mpr h1
    change (x : K ⧸ Subgroup.center K) = (y : K ⧸ Subgroup.center K)
    rw [QuotientGroup.eq_iff_div_mem]
    simpa only [div_eq_mul_inv] using h2
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨x, hx⟩ := hπsurj y
    exact ⟨mkZ x, by rw [hΦmk x]; exact hx⟩
  let eπ : K ⧸ Subgroup.center K ≃* J ⧸ Subgroup.center J :=
    MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  let Φ' : K ⧸ Subgroup.center K →* J ⧸ Subgroup.center J :=
    QuotientGroup.lift (Subgroup.center K) π' (le_of_eq hπ'ker.symm)
  have hΦ'mk : ∀ x : K, Φ' (mkZ x) = π' x := fun x => rfl
  have hπ'surj : Function.Surjective π' := by
    intro w
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) w
    have hj' : (j : G) ∈ φ'.range := by rw [hr]; exact j.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hj'
    exact ⟨x, by
      show mkJ (ψ' x) = mkJ j
      congr 1
      apply Subtype.ext
      change J.subtype (ψ' x) = J.subtype j
      rw [hψ' x]
      exact hx⟩
  have hΦ'inj : Function.Injective Φ' := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) b
    have hab' : π' x = π' y := hab
    have h1 : π' (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hab', mul_inv_cancel]
    have h2 : x * y⁻¹ ∈ Subgroup.center K := by
      rw [← hπ'ker]
      exact MonoidHom.mem_ker.mpr h1
    change (x : K ⧸ Subgroup.center K) = (y : K ⧸ Subgroup.center K)
    rw [QuotientGroup.eq_iff_div_mem]
    simpa only [div_eq_mul_inv] using h2
  have hΦ'surj : Function.Surjective Φ' := by
    intro y
    obtain ⟨x, hx⟩ := hπ'surj y
    exact ⟨mkZ x, by rw [hΦ'mk x]; exact hx⟩
  let eπ' : K ⧸ Subgroup.center K ≃* J ⧸ Subgroup.center J :=
    MulEquiv.ofBijective Φ' ⟨hΦ'inj, hΦ'surj⟩
  have heπ : ∀ x : K, eπ (mkZ x) = π x := fun x => rfl
  have heπ' : ∀ x : K, eπ' (mkZ x) = π' x := fun x => rfl
  refine ⟨eπ'.trans eπ.symm, ?_⟩
  intro x y hxy
  have h1 : π' x = π y := by
    have h2 : eπ.symm (eπ' (mkZ x)) = mkZ y := by
      simpa only [MulEquiv.trans_apply] using hxy
    have h3 := (MulEquiv.symm_apply_eq eπ).mp h2
    rwa [heπ' x, heπ y] at h3
  have hz : ψ' x * (ψ y)⁻¹ ∈ Subgroup.center J := by
    have h4 : (ψ' x : J ⧸ Subgroup.center J) = (ψ y : J ⧸ Subgroup.center J) := h1
    rw [QuotientGroup.eq_iff_div_mem] at h4
    simpa only [div_eq_mul_inv] using h4
  rw [Subgroup.mem_map]
  exact ⟨ψ' x * (ψ y)⁻¹, hz, by rw [map_mul, map_inv, hψ' x, hψ y]⟩

theorem irg_transfer_gen
    {K : Type} [Group K] [Finite K] (D : UniversalRootDatum K)
    (hperf : commutator K = ⊤) (hodd : Odd (Nat.card (Subgroup.center K)))
    (P Q : (Fin D.rank → ℤ) → Prop)
    (hP2 : ∀ β, P β → IsPGroup 2 (D.rootGroup β) ∧ IsPGroup 2 (D.rootGroup (-β)))
    (hQ2 : ∀ β, Q β → IsPGroup 2 (D.rootGroup β) ∧ IsPGroup 2 (D.rootGroup (-β)))
    (hM : ∀ θ : MulAut (K ⧸ Subgroup.center K), ∀ β', P β' → ∀ u' : K,
      ∃ β, Q β ∧ ∃ u : K,
        (ggRootSub D (QuotientGroup.mk' (Subgroup.center K)) β' u').map θ.toMonoidHom =
          ggRootSub D (QuotientGroup.mk' (Subgroup.center K)) β u ∧
        (ggRootSub D (QuotientGroup.mk' (Subgroup.center K)) (-β') u').map θ.toMonoidHom =
          ggRootSub D (QuotientGroup.mk' (Subgroup.center K)) (-β) u)
    {G : Type} [Group G] (φ φ' : K →* G) (hr : φ'.range = φ.range)
    (hk : φ.ker ≤ Subgroup.center K) (hk' : φ'.ker ≤ Subgroup.center K)
    {β' : Fin D.rank → ℤ} (hP : P β') (u' : K) :
    ∃ β, Q β ∧ ∃ u : K, ggRootSub D φ' β' u' = ggRootSub D φ β u ∧
      ggRootSub D φ' (-β') u' = ggRootSub D φ (-β) u := by
  obtain ⟨θ, hθ⟩ := irgTG_exists_aut φ φ' hr hperf hk hk'
  let J : Subgroup G := φ.range
  let ψ : K →* J := φ.rangeRestrict
  let e : φ'.range ≃* J := MulEquiv.subgroupCongr hr
  let ψ' : K →* J := e.toMonoidHom.comp φ'.rangeRestrict
  let mkZ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hψ : ∀ x : K, J.subtype (ψ x) = φ x := fun x => rfl
  have hψ' : ∀ x : K, J.subtype (ψ' x) = φ' x := fun x =>
    MulEquiv.subgroupCongr_apply hr (φ'.rangeRestrict x)
  have hcomp : J.subtype.comp ψ = φ := MonoidHom.ext (fun x => hψ x)
  have hcomp' : J.subtype.comp ψ' = φ' := MonoidHom.ext (fun x => hψ' x)
  have hoddJ : Odd (Nat.card (Subgroup.center J)) := irgTG_center_range_odd φ hperf hk hodd
  have step : ∀ (Y' Y : Subgroup K), IsPGroup 2 (Y'.map ψ') → IsPGroup 2 (Y.map ψ) →
      (Y'.map mkZ).map θ.toMonoidHom = Y.map mkZ → Y'.map ψ' = Y.map ψ := by
    intro Y' Y hY'2 hY2 hq
    refine CFSG.GroupTheory.eq_of_sup_eq_of_le_center (le_refl (Subgroup.center J)) hoddJ
      hY'2 hY2 (le_antisymm ?_ ?_)
    · refine sup_le ?_ le_sup_right
      intro a ha
      rw [Subgroup.mem_map] at ha
      obtain ⟨x, hxY, rfl⟩ := ha
      have hmk : mkZ x ∈ Y'.map mkZ := Subgroup.mem_map.mpr ⟨x, hxY, rfl⟩
      have hmem : θ (mkZ x) ∈ Y.map mkZ := by
        rw [← hq]
        exact Subgroup.mem_map.mpr ⟨mkZ x, hmk, rfl⟩
      rw [Subgroup.mem_map] at hmem
      obtain ⟨y, hyY, hy⟩ := hmem
      have hz : ψ' x * (ψ y)⁻¹ ∈ Subgroup.center J := by
        have hzZ := hθ x y hy.symm
        rw [Subgroup.mem_map] at hzZ
        obtain ⟨z, hzc, hzz⟩ := hzZ
        have hEq : z = ψ' x * (ψ y)⁻¹ := by
          apply Subtype.ext
          change J.subtype z = J.subtype (ψ' x * (ψ y)⁻¹)
          rw [hzz, map_mul, map_inv, hψ' x, hψ y]
        exact hEq ▸ hzc
      have hyB : ψ y ∈ Y.map ψ := Subgroup.mem_map.mpr ⟨y, hyY, rfl⟩
      have haux : (ψ' x * (ψ y)⁻¹) * ψ y ∈ Subgroup.center J ⊔ Y.map ψ :=
        Subgroup.mul_mem_sup hz hyB
      rw [sup_comm] at haux
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using haux
    · refine sup_le ?_ le_sup_right
      intro b hb
      rw [Subgroup.mem_map] at hb
      obtain ⟨y, hyY, rfl⟩ := hb
      have hmem : mkZ y ∈ (Y'.map mkZ).map θ.toMonoidHom := by
        rw [hq]
        exact Subgroup.mem_map.mpr ⟨y, hyY, rfl⟩
      rw [Subgroup.mem_map] at hmem
      obtain ⟨z, hz, hzθ⟩ := hmem
      rw [Subgroup.mem_map] at hz
      obtain ⟨x, hxY, rfl⟩ := hz
      have hzJ : ψ' x * (ψ y)⁻¹ ∈ Subgroup.center J := by
        have hzZ := hθ x y hzθ
        rw [Subgroup.mem_map] at hzZ
        obtain ⟨z', hzc, hzz⟩ := hzZ
        have hEq : z' = ψ' x * (ψ y)⁻¹ := by
          apply Subtype.ext
          change J.subtype z' = J.subtype (ψ' x * (ψ y)⁻¹)
          rw [hzz, map_mul, map_inv, hψ' x, hψ y]
        exact hEq ▸ hzc
      have hzJ' : ψ y * (ψ' x)⁻¹ ∈ Subgroup.center J := by
        simpa only [mul_inv_rev, inv_inv] using (Subgroup.center J).inv_mem hzJ
      have hxA : ψ' x ∈ Y'.map ψ' := Subgroup.mem_map.mpr ⟨x, hxY, rfl⟩
      have haux : (ψ y * (ψ' x)⁻¹) * ψ' x ∈ Subgroup.center J ⊔ Y'.map ψ' :=
        Subgroup.mul_mem_sup hzJ' hxA
      rw [sup_comm] at haux
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using haux
  obtain ⟨β, hQ, u, hβ, hβm⟩ := hM θ β' hP u'
  refine ⟨β, hQ, u, ?_, ?_⟩
  · let Y' : Subgroup K := (D.rootGroup β').map (MulAut.conj u').toMonoidHom
    let Y : Subgroup K := (D.rootGroup β).map (MulAut.conj u).toMonoidHom
    have hY'2 : IsPGroup 2 (Y'.map ψ') :=
      IsPGroup.map (IsPGroup.map (hP2 β' hP).1 (MulAut.conj u').toMonoidHom) ψ'
    have hY2 : IsPGroup 2 (Y.map ψ) :=
      IsPGroup.map (IsPGroup.map (hQ2 β hQ).1 (MulAut.conj u).toMonoidHom) ψ
    have hq : (Y'.map mkZ).map θ.toMonoidHom = Y.map mkZ := by
      simpa only [ggRootSub, Y', Y] using hβ
    have hAB : Y'.map ψ' = Y.map ψ := step Y' Y hY'2 hY2 hq
    have hpos : (Y'.map ψ').map J.subtype = Y'.map φ' := by rw [Subgroup.map_map, hcomp']
    have hneg : (Y.map ψ).map J.subtype = Y.map φ := by rw [Subgroup.map_map, hcomp]
    calc ggRootSub D φ' β' u' = Y'.map φ' := rfl
      _ = (Y'.map ψ').map J.subtype := hpos.symm
      _ = (Y.map ψ).map J.subtype := by rw [hAB]
      _ = Y.map φ := hneg
      _ = ggRootSub D φ β u := rfl
  · let Y' : Subgroup K := (D.rootGroup (-β')).map (MulAut.conj u').toMonoidHom
    let Y : Subgroup K := (D.rootGroup (-β)).map (MulAut.conj u).toMonoidHom
    have hY'2 : IsPGroup 2 (Y'.map ψ') :=
      IsPGroup.map (IsPGroup.map (hP2 β' hP).2 (MulAut.conj u').toMonoidHom) ψ'
    have hY2 : IsPGroup 2 (Y.map ψ) :=
      IsPGroup.map (IsPGroup.map (hQ2 β hQ).2 (MulAut.conj u).toMonoidHom) ψ
    have hq : (Y'.map mkZ).map θ.toMonoidHom = Y.map mkZ := by
      simpa only [ggRootSub, Y', Y] using hβm
    have hAB : Y'.map ψ' = Y.map ψ := step Y' Y hY'2 hY2 hq
    have hpos : (Y'.map ψ').map J.subtype = Y'.map φ' := by rw [Subgroup.map_map, hcomp']
    have hneg : (Y.map ψ).map J.subtype = Y.map φ := by rw [Subgroup.map_map, hcomp]
    calc ggRootSub D φ' (-β') u' = Y'.map φ' := rfl
      _ = (Y'.map ψ').map J.subtype := hpos.symm
      _ = (Y.map ψ).map J.subtype := by rw [hAB]
      _ = Y.map φ := hneg
      _ = ggRootSub D φ (-β) u := rfl

end CFSG.StandardType.RCKRP
