module

public import CFSG.Quasithin.Vol2.Asc94.L52Hstruct
public import CFSG.LargeExtraspecial.S9FiveB
public import CFSG.Fischer.Classification.Defs
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6Four
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LargeExtraspecial.S9FourD
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin.A94.L52

open scoped commutatorElement

private theorem d8_transport {G : Type*} [Group G] (K : Subgroup G) (φ : ↥K ≃* DihedralGroup 4)
    (z : G) (hzK : z ∈ K) (hz1 : z ≠ 1) (hzc : ∀ g : G, g * z = z * g) :
    (∀ x ∈ K, x ^ 2 ∈ Subgroup.zpowers z) ∧
      (∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ Subgroup.zpowers z) ∧
      (∀ x ∈ K, (∀ y ∈ K, x * y = y * x) → x ∈ Subgroup.zpowers z) := by
  have hsq8 : ∀ g : DihedralGroup 4, g ^ 2 = 1 ∨ g ^ 2 = DihedralGroup.r 2 := by decide
  have hcomm8 : ∀ g h : DihedralGroup 4, ⁅g, h⁆ = 1 ∨ ⁅g, h⁆ = DihedralGroup.r 2 := by decide
  have hcent8 : ∀ g : DihedralGroup 4, (∀ h : DihedralGroup 4, g * h = h * g) →
      g = 1 ∨ g = DihedralGroup.r 2 := by decide
  have huniq8 : ∀ w : DihedralGroup 4, w ≠ 1 → (∀ h : DihedralGroup 4, w * h = h * w) →
      w = DihedralGroup.r 2 := by decide
  have hzK1 : (⟨z, hzK⟩ : ↥K) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hw : φ ⟨z, hzK⟩ = DihedralGroup.r 2 := by
    refine huniq8 _ (fun h1 => hzK1 (φ.injective (h1.trans (map_one φ).symm))) (fun h => ?_)
    obtain ⟨k, rfl⟩ := φ.surjective h
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hzc k.1).symm)
  have hkey : ∀ k : ↥K, (φ k = 1 ∨ φ k = DihedralGroup.r 2) → (k : G) ∈ Subgroup.zpowers z := by
    rintro k (hk | hk)
    · rw [φ.injective (hk.trans (map_one φ).symm)]
      exact Subgroup.one_mem _
    · rw [φ.injective (hk.trans hw.symm)]
      exact Subgroup.mem_zpowers z
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun x hx hxc => ?_⟩
  · have h := hkey ((⟨x, hx⟩ : ↥K) ^ 2) (by rw [map_pow]; exact hsq8 _)
    exact h
  · have h := hkey ⁅(⟨x, hx⟩ : ↥K), ⟨y, hy⟩⁆ (by rw [map_commutatorElement]; exact hcomm8 _ _)
    simpa [commutatorElement_def] using h
  · have hc : ∀ g : DihedralGroup 4, φ ⟨x, hx⟩ * g = g * φ ⟨x, hx⟩ := by
      intro g
      obtain ⟨k, rfl⟩ := φ.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext (hxc k.1 k.2))
    exact hkey ⟨x, hx⟩ (hcent8 _ hc)

private theorem he_comm_of_factor {P : Type*} [Group P] {d e x y : P} (hx : x = d * e)
    (hxy : x * y = y * x) (he : e * y = y * e) : d * y = y * d := by
  subst hx
  apply mul_right_cancel (b := e)
  calc d * y * e = d * (y * e) := mul_assoc _ _ _
    _ = d * (e * y) := by rw [he]
    _ = d * e * y := (mul_assoc _ _ _).symm
    _ = y * (d * e) := hxy
    _ = y * d * e := (mul_assoc _ _ _).symm

theorem isExtraspecialPGroup_of_cube_data {P : Type*} [Group P] [Finite P] {Q : Subgroup P}
    (hcard : Nat.card Q = 128) (D : Fin 3 → Subgroup P) (z : P) (hzord : orderOf z = 2)
    (hzcen : z ∈ Subgroup.center P) (hDQ : ∀ i, D i ≤ Q)
    (hD8 : ∀ i, Nonempty (↥(D i) ≃* DihedralGroup 4)) (hzD : ∀ i, z ∈ D i)
    (hDcomm : ∀ i j, i ≠ j → ∀ x ∈ D i, ∀ y ∈ D j, x * y = y * x)
    (hsup : (⨆ i, D i) = Q) : CFSG.IsExtraspecialPGroup 2 ↥Q := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hzord
    exact absurd hzord (by decide)
  have hzc : ∀ g : P, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hzcen g
  have hZcen : ∀ c ∈ Subgroup.zpowers z, ∀ g : P, g * c = c * g := fun c hc g =>
    Subgroup.mem_center_iff.mp (Subgroup.zpowers_le.mpr hzcen hc) g
  have hF : ∀ i, (∀ x ∈ D i, x ^ 2 ∈ Subgroup.zpowers z) ∧
      (∀ x ∈ D i, ∀ y ∈ D i, ⁅x, y⁆ ∈ Subgroup.zpowers z) ∧
      (∀ x ∈ D i, (∀ y ∈ D i, x * y = y * x) → x ∈ Subgroup.zpowers z) := fun i =>
    d8_transport (D i) (hD8 i).some z (hzD i) hz1 hzc
  have hsqD : ∀ i, ∀ x ∈ D i, x ^ 2 ∈ Subgroup.zpowers z := fun i => (hF i).1
  have hcomD : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, ⁅x, y⁆ ∈ Subgroup.zpowers z := fun i => (hF i).2.1
  have hcentD : ∀ i, ∀ x ∈ D i, (∀ y ∈ D i, x * y = y * x) → x ∈ Subgroup.zpowers z :=
    fun i => (hF i).2.2
  have hDQcomm : ∀ i, ∀ d ∈ D i, ∀ y ∈ Q, ⁅d, y⁆ ∈ Subgroup.zpowers z := by
    intro i d hd y hy
    have hy' : y ∈ ⨆ j, D j := by rw [hsup]; exact hy
    refine Subgroup.iSup_induction D (C := fun y => ⁅d, y⁆ ∈ Subgroup.zpowers z) hy' ?_ ?_ ?_
    · intro j y' hy'
      by_cases hij : i = j
      · rw [← hij] at hy'
        exact hcomD i d hd y' hy'
      · show ⁅d, y'⁆ ∈ Subgroup.zpowers z
        rw [commutatorElement_eq_one_iff_mul_comm.mpr (hDcomm i j hij d hd y' hy')]
        exact Subgroup.one_mem _
    · show ⁅d, (1 : P)⁆ ∈ Subgroup.zpowers z
      rw [commutatorElement_one_right]
      exact Subgroup.one_mem _
    · intro a b ha hb
      show ⁅d, a * b⁆ ∈ Subgroup.zpowers z
      have e : ⁅d, a * b⁆ = ⁅d, a⁆ * (a * ⁅d, b⁆ * a⁻¹) := by
        simp only [commutatorElement_def]
        group
      have e2 : a * ⁅d, b⁆ * a⁻¹ = ⁅d, b⁆ := by
        rw [hZcen _ hb a, mul_assoc, mul_inv_cancel, mul_one]
      rw [e, e2]
      exact mul_mem ha hb
  have hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Subgroup.zpowers z := by
    intro x hx
    have hx' : x ∈ ⨆ j, D j := by rw [hsup]; exact hx
    refine Subgroup.iSup_induction D (C := fun x => ∀ y ∈ Q, ⁅x, y⁆ ∈ Subgroup.zpowers z)
      hx' ?_ ?_ ?_
    · intro j d hd y hy
      exact hDQcomm j d hd y hy
    · intro y _
      show ⁅(1 : P), y⁆ ∈ Subgroup.zpowers z
      rw [commutatorElement_one_left]
      exact Subgroup.one_mem _
    · intro a b ha hb y hy
      show ⁅a * b, y⁆ ∈ Subgroup.zpowers z
      have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
        simp only [commutatorElement_def]
        group
      have e2 : a * ⁅b, y⁆ * a⁻¹ = ⁅b, y⁆ := by
        rw [hZcen _ (hb y hy) a, mul_assoc, mul_inv_cancel, mul_one]
      rw [e, e2]
      exact mul_mem (hb y hy) (ha y hy)
  have hQsq : ∀ x ∈ Q, x ^ 2 ∈ Subgroup.zpowers z := by
    intro x hx
    have hx' : x ∈ ⨆ j, D j := by rw [hsup]; exact hx
    have key := Subgroup.iSup_induction D (C := fun x => x ∈ Q ∧ x ^ 2 ∈ Subgroup.zpowers z) hx'
      (fun j d hd => ⟨hDQ j hd, hsqD j d hd⟩)
      ⟨Q.one_mem, by rw [one_pow]; exact Subgroup.one_mem _⟩
      (by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have hc : b⁻¹ * (a * a) = (a * a) * b⁻¹ := by
          have h := hZcen _ ha2 b⁻¹
          rwa [sq] at h
        have e : (a * b) ^ 2 = ⁅a, b⁆ * (a ^ 2 * b ^ 2) := by
          simp only [commutatorElement_def, sq]
          calc a * b * (a * b) = a * b * a⁻¹ * ((a * a) * b⁻¹) * (b * b) := by group
            _ = a * b * a⁻¹ * (b⁻¹ * (a * a)) * (b * b) := by rw [hc]
            _ = a * b * a⁻¹ * b⁻¹ * (a * a * (b * b)) := by simp only [mul_assoc]
        rw [e]
        exact mul_mem (hQcomm a ha b hb) (mul_mem ha2 hb2))
    exact key.2
  have hfact : ∀ x ∈ Q, ∃ d0 ∈ D 0, ∃ d1 ∈ D 1, ∃ d2 ∈ D 2, x = d0 * d1 * d2 := by
    intro x hx
    have hx' : x ∈ ⨆ j, D j := by rw [hsup]; exact hx
    refine Subgroup.iSup_induction D
      (C := fun x => ∃ d0 ∈ D 0, ∃ d1 ∈ D 1, ∃ d2 ∈ D 2, x = d0 * d1 * d2) hx' ?_ ?_ ?_
    · intro j d hd
      fin_cases j
      · exact ⟨d, hd, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
      · exact ⟨1, Subgroup.one_mem _, d, hd, 1, Subgroup.one_mem _, by simp⟩
      · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, d, hd, by simp⟩
    · exact ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
    · rintro a b ⟨a0, ha0, a1, ha1, a2, ha2, rfl⟩ ⟨b0, hb0, b1, hb1, b2, hb2, rfl⟩
      have h10 : a1 * b0 = b0 * a1 := hDcomm 1 0 (by decide) a1 ha1 b0 hb0
      have h20 : a2 * b0 = b0 * a2 := hDcomm 2 0 (by decide) a2 ha2 b0 hb0
      have h21 : a2 * b1 = b1 * a2 := hDcomm 2 1 (by decide) a2 ha2 b1 hb1
      refine ⟨a0 * b0, mul_mem ha0 hb0, a1 * b1, mul_mem ha1 hb1, a2 * b2, mul_mem ha2 hb2, ?_⟩
      calc a0 * a1 * a2 * (b0 * b1 * b2) = a0 * (a1 * (a2 * b0)) * b1 * b2 := by
            simp only [mul_assoc]
        _ = a0 * (a1 * (b0 * a2)) * b1 * b2 := by rw [h20]
        _ = a0 * ((a1 * b0) * a2) * b1 * b2 := by simp only [mul_assoc]
        _ = a0 * ((b0 * a1) * a2) * b1 * b2 := by rw [h10]
        _ = a0 * b0 * (a1 * (a2 * b1)) * b2 := by simp only [mul_assoc]
        _ = a0 * b0 * (a1 * (b1 * a2)) * b2 := by rw [h21]
        _ = a0 * b0 * (a1 * b1) * (a2 * b2) := by simp only [mul_assoc]
  have hQcent : ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x ∈ Subgroup.zpowers z := by
    intro x hx hxc
    obtain ⟨d0, hd0, d1, hd1, d2, hd2, rfl⟩ := hfact x hx
    have c0 : ∀ y ∈ D 0, d0 * y = y * d0 := by
      intro y hy
      have h1y : y * d1 = d1 * y := hDcomm 0 1 (by decide) y hy d1 hd1
      have h2y : y * d2 = d2 * y := hDcomm 0 2 (by decide) y hy d2 hd2
      have hye : d1 * d2 * y = y * (d1 * d2) := by
        rw [mul_assoc, ← h2y, ← mul_assoc, ← h1y, mul_assoc]
      exact he_comm_of_factor (mul_assoc d0 d1 d2) (hxc y (hDQ 0 hy)) hye
    have c1 : ∀ y ∈ D 1, d1 * y = y * d1 := by
      intro y hy
      have h0y : y * d0 = d0 * y := hDcomm 1 0 (by decide) y hy d0 hd0
      have h2y : y * d2 = d2 * y := hDcomm 1 2 (by decide) y hy d2 hd2
      have hye : d0 * d2 * y = y * (d0 * d2) := by
        rw [mul_assoc, ← h2y, ← mul_assoc, ← h0y, mul_assoc]
      have hx1 : d0 * d1 * d2 = d1 * (d0 * d2) := by
        rw [← mul_assoc, hDcomm 0 1 (by decide) d0 hd0 d1 hd1]
      exact he_comm_of_factor hx1 (hxc y (hDQ 1 hy)) hye
    have c2 : ∀ y ∈ D 2, d2 * y = y * d2 := by
      intro y hy
      have h0y : y * d0 = d0 * y := hDcomm 2 0 (by decide) y hy d0 hd0
      have h1y : y * d1 = d1 * y := hDcomm 2 1 (by decide) y hy d1 hd1
      have hye : d0 * d1 * y = y * (d0 * d1) := by
        rw [mul_assoc, ← h1y, ← mul_assoc, ← h0y, mul_assoc]
      have hx2 : d0 * d1 * d2 = d2 * (d0 * d1) := by
        rw [mul_assoc, hDcomm 1 2 (by decide) d1 hd1 d2 hd2, ← mul_assoc,
          hDcomm 0 2 (by decide) d0 hd0 d2 hd2, mul_assoc]
      exact he_comm_of_factor hx2 (hxc y (hDQ 2 hy)) hye
    exact mul_mem (mul_mem (hcentD 0 d0 hd0 c0) (hcentD 1 d1 hd1 c1)) (hcentD 2 d2 hd2 c2)
  have hP : IsPGroup 2 ↥Q := IsPGroup.of_card (n := 7) (hcard.trans (by norm_num))
  have hle : Subgroup.zpowers z ≤ Q := Subgroup.zpowers_le.mpr (hDQ 0 (hzD 0))
  have hZ : Nat.card ↥((Subgroup.zpowers z).subgroupOf Q) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hzord]
  have hZc : (Subgroup.zpowers z).subgroupOf Q ≤ Subgroup.center ↥Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hZcen _ hx _
  have hcomm' : ∀ x y : ↥Q, ⁅x, y⁆ ∈ (Subgroup.zpowers z).subgroupOf Q := by
    intro x y
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hQcomm x.1 x.2 y.1 y.2
  have hsq' : ∀ x : ↥Q, x ^ 2 ∈ (Subgroup.zpowers z).subgroupOf Q := by
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact hQsq x.1 x.2
  have hcent' : ∀ x : ↥Q, (∀ y : ↥Q, x * y = y * x) → x ∈ (Subgroup.zpowers z).subgroupOf Q := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hQcent x.1 x.2 (fun y hy => ?_)
    simpa using congrArg Subtype.val (hx ⟨y, hy⟩)
  have hnab : ∃ x : ↥Q, x ∉ (Subgroup.zpowers z).subgroupOf Q := by
    by_contra hcon
    push Not at hcon
    have htop : (Subgroup.zpowers z).subgroupOf Q = ⊤ := (Subgroup.eq_top_iff' _).mpr hcon
    rw [htop, Subgroup.card_top, hcard] at hZ
    norm_num at hZ
  exact CFSG.LargeExtraspecial.S9.isExtraspecialPGroup_of_center hP hZ hZc hcomm' hsq' hcent' hnab

theorem isExtraspecialPGroup_Qh : CFSG.IsExtraspecialPGroup 2 ↥Qh := by
  obtain ⟨D, z, hzord, hzc, hDQ, hD8, hzD, hDc, -, hsup⟩ := isD8CentralCube_Qh
  exact isExtraspecialPGroup_of_cube_data card_Qh D z hzord hzc hDQ hD8 hzD hDc hsup

theorem inf_centralizer_Qh : Qh ⊓ Subgroup.centralizer (Qh : Set Hc) = Subgroup.zpowers zt := by
  have hcen : Qh ⊓ Subgroup.centralizer (Qh : Set Hc) =
      (Subgroup.center ↥Qh).map Qh.subtype := by
    ext x
    constructor
    · rintro ⟨hxQ, hxc⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxc g.1 g.2
    · intro hx
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      refine Subgroup.mem_inf.mpr ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hk ⟨h, hh⟩)
  have hcard_c : Nat.card ↥(Qh ⊓ Subgroup.centralizer (Qh : Set Hc)) = 2 := by
    rw [hcen, ← Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.center ↥Qh) Qh.subtype
      (Subgroup.subtype_injective Qh)).toEquiv]
    exact isExtraspecialPGroup_Qh.2.2.2
  have hle : Subgroup.zpowers zt ≤ Qh ⊓ Subgroup.centralizer (Qh : Set Hc) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨U1_le_Qh zt_mem_U1,
      Subgroup.mem_centralizer_iff.mpr fun h _ => Subgroup.mem_center_iff.mp zt_central h⟩
  have hcardz : Nat.card ↥(Subgroup.zpowers zt) = 2 := by
    rw [Nat.card_zpowers, zt_order]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hcard_c, hcardz]))).symm

end CFSG.Quasithin.A94.L52
