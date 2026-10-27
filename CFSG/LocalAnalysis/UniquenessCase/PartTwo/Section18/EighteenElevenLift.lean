module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.UC2TenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b
public import CFSG.Permutation.FiveTransitive.CoprimeKernelPrimeLift
public import CFSG.GroupTheory.LiftConjPower
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.RankThreeUC
open CFSG.RankThreeEvenClassification.Helpers

variable {G : Type} [Group G] [Finite G]

theorem actTil_comp_inclusion_ker {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {X : Subgroup G} (hX : X ≤ stabTil V₀ V)
    (hXsub : CFSG.Open.IsSubnormal X D.M) (hsimple : IsSimpleGroup (Bar2 X))
    (hX1 : barSub V₀ V hV.isElemAbelian X ≠ ⊥) :
    ((actTil V₀ V hV.isElemAbelian).comp (Subgroup.inclusion hX)).ker =
      CFSG.pCore 2 ↥X := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxP : (x : G) ∈ pCoreOf 2 X :=
      mem_pCoreOf_of_actTil_eq_one hV hXsub hsimple hX1 x.2 (hX x.2) hx
    rw [← CFSG.openPCoreOf_subgroupOf 2 X]
    exact Subgroup.mem_subgroupOf.mpr hxP
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 X := by
      rw [← CFSG.openPCoreOf_subgroupOf 2 X] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    have hmem := actTil_mem_barSub V₀ V hV.isElemAbelian hxP (hX x.2)
    rw [TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV.isElemAbelian hXsub
      (barSub_pCoreOf_eq_bot_of_hyp125 hV), Subgroup.mem_bot] at hmem
    exact hmem

theorem exists_lift_prime_order {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {X : Subgroup G} (hX : X ≤ stabTil V₀ V)
    (hXsub : CFSG.Open.IsSubnormal X D.M) (hsimple : IsSimpleGroup (Bar2 X))
    (hX1 : barSub V₀ V hV.isElemAbelian X ≠ ⊥)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {ybar : MulAut (Vtil V₀ V hV.isElemAbelian)}
    (hy : ybar ∈ barSub V₀ V hV.isElemAbelian X) (hord : orderOf ybar = r) :
    ∃ g : ↥X, orderOf g = r ∧
      ∃ c : ℕ, actTil V₀ V hV.isElemAbelian ⟨(g : G), hX g.2⟩ = ybar ^ 2 ^ c := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  let φ : ↥X →* MulAut (Vtil V₀ V hV.isElemAbelian) :=
    (actTil V₀ V hV.isElemAbelian).comp (Subgroup.inclusion hX)
  have hker : IsPGroup 2 φ.ker := by
    rw [show φ.ker = CFSG.pCore 2 ↥X from
      actTil_comp_inclusion_ker hV hX hXsub hsimple hX1]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  have hrange : φ.range = barSub V₀ V hV.isElemAbelian X := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hy' : ybar ∈ φ.range := by rw [hrange]; exact hy
  let yR : ↥φ.range := ⟨ybar, hy'⟩
  have hyord : orderOf yR = r := by
    rw [← Subgroup.orderOf_coe yR]
    simpa [yR] using hord
  obtain ⟨g, hg, hgord⟩ :=
    CFSG.FiveTransitive.CoprimeKernelPrimeLift.exists_lift φ.rangeRestrict
      φ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict]) hr2 yR hyord
  refine ⟨g, hgord, 0, ?_⟩
  have hval : φ g = ybar := by
    have h1 := congrArg Subtype.val hg
    simpa [yR] using h1
  have hval' : actTil V₀ V hV.isElemAbelian ⟨(g : G), hX g.2⟩ = ybar := hval
  simpa using hval'

theorem exists_lift_conj_pow {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {X : Subgroup G} (hX : X ≤ stabTil V₀ V)
    (hXsub : CFSG.Open.IsSubnormal X D.M) (hsimple : IsSimpleGroup (Bar2 X))
    (hX1 : barSub V₀ V hV.isElemAbelian X ≠ ⊥)
    {b : ↥X} {r : ℕ} (hb : orderOf b = r) (hr : r.Prime) (hr2 : r ≠ 2)
    {xbar : MulAut (Vtil V₀ V hV.isElemAbelian)}
    (hxbar : xbar ∈ barSub V₀ V hV.isElemAbelian X) {m : ℤ}
    (hconj : xbar * actTil V₀ V hV.isElemAbelian ⟨(b : G), hX b.2⟩ * xbar⁻¹ =
      (actTil V₀ V hV.isElemAbelian ⟨(b : G), hX b.2⟩) ^ m) :
    ∃ x : ↥X, actTil V₀ V hV.isElemAbelian ⟨(x : G), hX x.2⟩ = xbar ∧
      x * b * x⁻¹ = b ^ m := by
  classical
  let φ : ↥X →* MulAut (Vtil V₀ V hV.isElemAbelian) :=
    (actTil V₀ V hV.isElemAbelian).comp (Subgroup.inclusion hX)
  have hker : IsPGroup 2 φ.ker := by
    rw [show φ.ker = CFSG.pCore 2 ↥X from
      actTil_comp_inclusion_ker hV hX hXsub hsimple hX1]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  have hrange : φ.range = barSub V₀ V hV.isElemAbelian X := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hxbar' : xbar ∈ φ.range := by rw [hrange]; exact hxbar
  let xR : ↥φ.range := ⟨xbar, hxbar'⟩
  have hconjR : xR * φ.rangeRestrict b * xR⁻¹ = (φ.rangeRestrict b) ^ m := by
    apply Subtype.ext
    change xbar * actTil V₀ V hV.isElemAbelian ⟨(b : G), hX b.2⟩ * xbar⁻¹ =
      (actTil V₀ V hV.isElemAbelian ⟨(b : G), hX b.2⟩) ^ m
    exact hconj
  obtain ⟨x, hx, hxconj⟩ := CFSG.GroupTheory.exists_lift_conj_zpow φ.rangeRestrict
    φ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict]) hb hr hr2 hconjR
  refine ⟨x, ?_, hxconj⟩
  have h1 := congrArg Subtype.val hx
  have h1' : actTil V₀ V hV.isElemAbelian ⟨(x : G), hX x.2⟩ = xbar := h1
  exact h1'

theorem exists_L2_section_of_lift {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {X : Subgroup G} (hX : X ≤ stabTil V₀ V)
    (hXsub : CFSG.Open.IsSubnormal X D.M) (hsimple : IsSimpleGroup (Bar2 X))
    (hX1 : barSub V₀ V hV.isElemAbelian X ≠ ⊥)
    {b : ↥X} {r n : ℕ} (hb : orderOf b = r) (hr : r.Prime) (hr2 : r ≠ 2)
    {Y : Subgroup (MulAut (Vtil V₀ V hV.isElemAbelian))}
    (hY : Y ≤ barSub V₀ V hV.isElemAbelian X ⊓
      Subgroup.centralizer
        ({actTil V₀ V hV.isElemAbelian ⟨(b : G), hX b.2⟩} :
          Set (MulAut (Vtil V₀ V hV.isElemAbelian))))
    (hL2 : IsL2 ↥Y n) :
    ∃ Yt : Subgroup G,
      Yt ≤ X ⊓ Subgroup.centralizer (Subgroup.zpowers (b : G) : Set G) ∧
        ∃ N₀ : Subgroup ↥Yt, ∃ _ : N₀.Normal, IsL2 (↥Yt ⧸ N₀) n := by
  classical
  let φ : ↥X →* MulAut (Vtil V₀ V hV.isElemAbelian) :=
    (actTil V₀ V hV.isElemAbelian).comp (Subgroup.inclusion hX)
  have hker : IsPGroup 2 φ.ker := by
    rw [show φ.ker = CFSG.pCore 2 ↥X from
      actTil_comp_inclusion_ker hV hX hXsub hsimple hX1]
    exact CFSG.pCore_isPGroup (p := 2) (G := ↥X)
  have hnotdvd : ¬ r ∣ Nat.card φ.ker := by
    intro hdiv
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥φ.ker)).mp hker
    rw [hk] at hdiv
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      (hr.dvd_of_dvd_pow hdiv))
  have hrange : φ.range = barSub V₀ V hV.isElemAbelian X := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hYle : Y ≤ φ.range := by rw [hrange]; exact fun y hy => (hY hy).1
  let Y' : Subgroup ↥φ.range := Y.subgroupOf φ.range
  have hL2' : IsL2 ↥Y' n := by
    have e : ↥Y' ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYle
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2
  have hzp : IsPGroup r (Subgroup.zpowers b) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hb, pow_one]
  let C : Subgroup ↥X := Subgroup.centralizer (Subgroup.zpowers b : Set ↥X)
  have hCmap : C.map φ.rangeRestrict =
      Subgroup.centralizer (Subgroup.zpowers (φ.rangeRestrict b) : Set ↥φ.range) := by
    change (Subgroup.centralizer (Subgroup.zpowers b : Set ↥X)).map φ.rangeRestrict =
      Subgroup.centralizer (Subgroup.zpowers (φ.rangeRestrict b) : Set ↥φ.range)
    rw [← MonoidHom.map_zpowers]
    exact centralizer_map_eq_of_pGroup_prime_complement_kernel r hr φ.rangeRestrict
      φ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict]) (Subgroup.zpowers b) hzp
  have hY'C : Y' ≤ Subgroup.centralizer
      (Subgroup.zpowers (φ.rangeRestrict b) : Set ↥φ.range) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hY hy).2
  let D : Subgroup ↥X := C ⊓ Y'.comap φ.rangeRestrict
  let ψD : ↥D →* ↥Y' :=
    (φ.rangeRestrict.comp D.subtype).codRestrict Y' (fun x => x.2.2)
  have hψD : Function.Surjective ψD := by
    intro y
    have hyC : (y : ↥φ.range) ∈ C.map φ.rangeRestrict := by
      rw [hCmap]
      exact hY'C y.2
    obtain ⟨c, hcC, hcψ⟩ := Subgroup.mem_map.mp hyC
    have hcY : c ∈ Y'.comap φ.rangeRestrict := by
      rw [Subgroup.mem_comap]
      rw [hcψ]
      exact y.2
    refine ⟨⟨c, ⟨hcC, hcY⟩⟩, ?_⟩
    apply Subtype.ext
    exact hcψ
  let N₀' : Subgroup ↥D := ψD.ker
  have hN₀' : N₀'.Normal := MonoidHom.normal_ker ψD
  let eD : ↥D ≃* ↥(D.map X.subtype) :=
    Subgroup.equivMapOfInjective D X.subtype X.subtype_injective
  let Yt : Subgroup G := D.map X.subtype
  let ψYt : ↥Yt →* ↥Y' := ψD.comp eD.symm.toMonoidHom
  have hψYt : Function.Surjective ψYt := hψD.comp eD.symm.surjective
  let N₀ : Subgroup ↥Yt := ψYt.ker
  have hN₀ : N₀.Normal := MonoidHom.normal_ker ψYt
  have hL2Yt : IsL2 (↥Yt ⧸ N₀) n := by
    have e : ↥Yt ⧸ N₀ ≃* ↥Y' :=
      QuotientGroup.quotientKerEquivOfSurjective ψYt hψYt
    exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2'
  refine ⟨Yt, ?_, N₀, hN₀, hL2Yt⟩
  refine le_inf (Subgroup.map_subtype_le D) ?_
  rintro y ⟨d, hd, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hdb : Commute ((d : ↥X) : G) ((b : ↥X) : G) :=
    (congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hd.1 b (Subgroup.mem_zpowers b))).symm
  exact (hdb.zpow_right k).eq.symm

theorem le_M_of_twoLocal_of_inverted (D : Data G) (h109 : Inputs1719.UC2_10_9 D)
    {s p : ℕ} {B K : Subgroup G} (hs : Odd s) (hp : p.Prime) (hdvd : p ∣ 2 ^ s - 1)
    (hB : B ≤ D.M ⊓ Subgroup.normalizer (D.T : Set G)) (hcard : Nat.card B = p)
    (hBU : B ∈ uniqueSet D.M) (hBK : B ≤ K) (hKM : K ≤ D.M)
    (hinv : UC22.F05.InvertedIn K B) {H : Subgroup G} (hH : IsTwoLocal H)
    (hKH : K ⊔ D.T ≤ H) : H ≤ D.M :=
  uc22p22p_le_of_uniqueMax
    (CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.uniqueMax_of_inverted_uc2_10_9
      h109 hs hp hdvd hB hcard (inU_iff_mem_uniqueSet.2 hBU) hBK hKM hinv) hH hKH

theorem invertedIn_sup_zpowers {b x : G} (hinv : x * b * x⁻¹ = b⁻¹) :
    UC22.F05.InvertedIn (Subgroup.zpowers b ⊔ Subgroup.zpowers x) (Subgroup.zpowers b) := by
  refine ⟨x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x), ?_⟩
  intro y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  calc x * b ^ k * x⁻¹ = (x * b * x⁻¹) ^ k := by rw [conj_zpow]
    _ = (b⁻¹) ^ k := by rw [hinv]
    _ = (b ^ k)⁻¹ := by rw [inv_zpow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
