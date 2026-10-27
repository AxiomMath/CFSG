module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenExt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4U5Delta
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixExcl
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
public import CFSG.LocalAnalysis.WeakClosure81.InFMulEquiv
public import CFSG.LocalAnalysis.WeakClosure81.InFSqPrimeTwoGroup
public import CFSG.GroupTheory.PCore.QuotMulAut
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.GroupTheory.SylowNormalElements
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveSylow
public import CFSG.Quasithin.Vol2.Ch4Sec3Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.Quasithin.Vol2.Ch9L34Gam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof
  (lieModel_eq_of_isChar2LieShape fieldExponent_eq_of_isChar2LieShape)

variable {G : Type} [Group G] [Finite G]

theorem bar2_mulEquiv_map_of_isPGroup_ker {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (π : X →* Y) (hker : IsPGroup 2 π.ker) (K : Subgroup X) :
    Nonempty (Bar2 K ≃* Bar2 (K.map π)) := by
  classical
  let ψ : ↥K →* ↥(K.map π) :=
    (π.comp K.subtype).codRestrict (K.map π)
      (fun x => Subgroup.mem_map_of_mem π x.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hψker : IsPGroup 2 ψ.ker := by
    have h1 : ψ.ker = π.ker.comap K.subtype := by
      ext x
      constructor
      · intro hx
        change (K.subtype x : X) ∈ π.ker
        have hx' : (ψ x : ↥(K.map π)) = 1 := hx
        have hx'' : (ψ x : Y) = 1 := congrArg Subtype.val hx'
        simpa [show (ψ x : Y) = π (x : X) from rfl] using hx''
      · intro hx
        change (ψ x : ↥(K.map π)) = 1
        exact Subtype.ext hx
    rw [h1]
    exact IsPGroup.comap_of_injective hker K.subtype K.subtype_injective
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker ψ hψ hψker

noncomputable def bar2TopMulEquiv {K : Subgroup G} :
    Bar2 (⊤ : Subgroup ↥K) ≃* Bar2 K :=
  QuotientGroup.congr (CFSG.pCore 2 ↥(⊤ : Subgroup ↥K)) (CFSG.pCore 2 ↥K)
    (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥K) ≃* ↥K)
    (CFSG.pCore_map_iso 2 (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥K) ≃* ↥K))

theorem nonempty_barImage_mulEquiv_quotient {X X₁ J : Subgroup G} (hJX : J ≤ X)
    (hJX₁ : J ≤ X₁)
    [hNX₁ : ((CFSG.Open.pCoreOf 2 X).subgroupOf X₁).Normal]
    [hNJ : ((CFSG.Open.pCoreOf 2 X).subgroupOf J).Normal] :
    Nonempty (↥(UC22.barImage X J) ≃*
      ↥((J.subgroupOf X₁).map (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 X).subgroupOf X₁)))) := by
  classical
  have hN₀ : CFSG.Open.pCoreOf 2 X = (CFSG.pCore 2 ↥X).map X.subtype := rfl
  let f₁ : ↥J →* Bar2 X := (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hJX)
  let f₂ : ↥J →* (↥X₁ ⧸ ((CFSG.Open.pCoreOf 2 X).subgroupOf X₁)) :=
    (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 X).subgroupOf X₁)).comp
      (Subgroup.inclusion hJX₁)
  have hker₁ : f₁.ker = (CFSG.Open.pCoreOf 2 X).subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) (Subgroup.inclusion hJX x) = 1 ↔
      (x : G) ∈ CFSG.Open.pCoreOf 2 X
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact Subgroup.mem_map_of_mem X.subtype hx
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have hyx' : y = Subgroup.inclusion hJX x := Subtype.ext hyx
      rwa [hyx'] at hy
  have hker₂ : f₂.ker = (CFSG.Open.pCoreOf 2 X).subgroupOf J := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 X).subgroupOf X₁))
        (Subgroup.inclusion hJX₁ x) = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 X
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hrange₁ : f₁.range = UC22.barImage X J := by
    rw [UC22.barImage]
    rw [show f₁.range = (J.subgroupOf X).map (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) from by
      rw [show f₁ = (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp (Subgroup.inclusion hJX) from rfl,
        MonoidHom.range_comp, Subgroup.inclusion_range]]
  have hrange₂ : f₂.range =
      (J.subgroupOf X₁).map (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 X).subgroupOf X₁)) := by
    rw [show f₂ = (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 X).subgroupOf X₁)).comp
      (Subgroup.inclusion hJX₁) from rfl, MonoidHom.range_comp, Subgroup.inclusion_range]
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hker₁).symm.trans
    ((QuotientGroup.quotientKerEquivRange f₁).trans
      (MulEquiv.subgroupCongr hrange₁))).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker₂).symm.trans
      ((QuotientGroup.quotientKerEquivRange f₂).trans (MulEquiv.subgroupCongr hrange₂)))⟩

theorem inFSq_X1_of_extension_clause {X T P₁ J₁ X₁ : Subgroup G} {P : Subgroup (Bar2 X)}
    {n : ℕ} (hP₁X : P₁ ≤ X) (hX₁ : X₁ = T ⊔ J₁) (hJ₁ : J₁ = Opp 2 P₁)
    (hTN₀ : T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G))
    (hTP : T ≤ Subgroup.normalizer (P₁ : Set G))
    (hTX₁ : T ≤ X₁) (hJX₁ : J₁ ≤ X₁) (hN₀P₁ : CFSG.Open.pCoreOf 2 X ≤ P₁)
    (hbP : UC22.barImage X P₁ = P)
    (hext : ∀ (E : Type) [Group E] [Finite E] (J_E : Subgroup E) [J_E.Normal],
      Nonempty (↥J_E ≃* ↥(Opp 2 P)) → IsPGroup 2 (E ⧸ J_E) → InFSq n (⊤ : Subgroup E))
    (hT2 : IsPGroup 2 T) :
    InFSq n X₁ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ : Subgroup G := CFSG.Open.pCoreOf 2 X with hN₀def
  have hN₀2 : IsPGroup 2 N₀ := by
    rw [hN₀def]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_isPGroup_pCoreOf X
  have hN₀J₁ : N₀ ≤ J₁ := by
    rw [hJ₁]
    exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two hN₀2 hN₀P₁
  have hN₀X₁ : N₀ ≤ X₁ := hN₀J₁.trans hJX₁
  have hJ₁P₁ : J₁ ≤ P₁ := by
    rw [hJ₁]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 2 P₁
  have hTJ₁ : T ≤ Subgroup.normalizer (J₁ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hPt : P₁.map (MulAut.conj t).toMonoidHom = P₁ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTP ht)
    rw [hJ₁]
    show (CFSG.RankThree.PartOne.pElementSubgroup 2 P₁).map (MulAut.conj t).toMonoidHom
      = CFSG.RankThree.PartOne.pElementSubgroup 2 P₁
    have hconj : CFSG.RankThree.PartOne.conjBy t P₁ = P₁ := hPt
    rw [show (CFSG.RankThree.PartOne.pElementSubgroup 2 P₁).map (MulAut.conj t).toMonoidHom
        = CFSG.RankThree.PartOne.pElementSubgroup 2 (CFSG.RankThree.PartOne.conjBy t P₁)
        from (CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy 2 t P₁).symm, hconj]
  have hN₀X : X ≤ Subgroup.normalizer (N₀ : Set G) := by
    rw [hN₀def]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hN₀norm : (N₀.subgroupOf X₁).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀X₁).mpr ?_
    rw [hX₁]
    exact sup_le hTN₀ (hJ₁P₁.trans (hP₁X.trans hN₀X))
  have hJ₁norm : (J₁.subgroupOf X₁).Normal := by
    rw [hX₁]
    exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hTJ₁
  let E := ↥X₁ ⧸ (N₀.subgroupOf X₁)
  let πE : ↥X₁ →* E := QuotientGroup.mk' (N₀.subgroupOf X₁)
  have hπE : Function.Surjective πE := QuotientGroup.mk'_surjective _
  have hkerE : IsPGroup 2 πE.ker := by
    have h1 : πE.ker = N₀.subgroupOf X₁ := QuotientGroup.ker_mk' _
    rw [h1]
    exact hN₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hN₀X₁).symm
  let J_E : Subgroup E := (J₁.subgroupOf X₁).map πE
  haveI hJEnorm : J_E.Normal := hJ₁norm.map πE hπE
  haveI hN₀J₁norm : ((CFSG.Open.pCoreOf 2 X).subgroupOf J₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀J₁).mpr (hJ₁P₁.trans (hP₁X.trans hN₀X))
  have hiso : Nonempty (↥J_E ≃* ↥(Opp 2 P)) := by
    obtain ⟨e1⟩ := nonempty_barImage_mulEquiv_quotient (X := X) (X₁ := X₁) (J := J₁)
      (hJ₁P₁.trans hP₁X) hJX₁
    have hbJ : UC22.barImage X J₁ = Opp 2 P := by
      rw [hJ₁, CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_opp (p := 2)
        Nat.prime_two hP₁X, hbP]
      rfl
    exact ⟨e1.symm.trans (MulEquiv.subgroupCongr hbJ)⟩
  have hEq2 : IsPGroup 2 (E ⧸ J_E) := by
    let g : ↥T →* (E ⧸ J_E) :=
      (QuotientGroup.mk' J_E).comp ((QuotientGroup.mk' (N₀.subgroupOf X₁)).comp
        (Subgroup.inclusion hTX₁))
    have hg : Function.Surjective g := by
      intro q
      obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective J_E q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N₀.subgroupOf X₁) e
      have hx : (x : G) ∈ (T : Set G) * (J₁ : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right T J₁ hTJ₁, ← hX₁]
        exact x.2
      obtain ⟨t, ht, j, hj, htj⟩ := hx
      have hjE : πE ⟨j, hJX₁ hj⟩ ∈ J_E :=
        Subgroup.mem_map_of_mem πE (Subgroup.mem_subgroupOf.mpr hj)
      have hq : (QuotientGroup.mk' J_E) (πE x) =
          (QuotientGroup.mk' J_E) (πE ⟨t, hTX₁ ht⟩) := by
        have h1 : πE x = πE ⟨t, hTX₁ ht⟩ * πE ⟨j, hJX₁ hj⟩ := by
          rw [← map_mul]
          exact congrArg πE (Subtype.ext htj.symm)
        have hb1 : (QuotientGroup.mk' J_E) (πE ⟨j, hJX₁ hj⟩) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hjE
        rw [h1, map_mul, hb1, mul_one]
      refine ⟨⟨t, ht⟩, ?_⟩
      show (QuotientGroup.mk' J_E) (πE ⟨t, hTX₁ ht⟩) = (QuotientGroup.mk' J_E) (πE x)
      exact hq.symm
    exact hT2.of_surjective g hg
  have hE : InFSq n (⊤ : Subgroup E) := hext E J_E hiso hEq2
  obtain ⟨e2a⟩ := bar2_mulEquiv_map_of_isPGroup_ker πE hkerE (⊤ : Subgroup ↥X₁)
  have hmap : (⊤ : Subgroup ↥X₁).map πE = ⊤ := Subgroup.map_top_of_surjective πE hπE
  have e2b : Bar2 ((⊤ : Subgroup ↥X₁).map πE) ≃* Bar2 (⊤ : Subgroup E) := hmap ▸ MulEquiv.refl _
  have e : Bar2 X₁ ≃* Bar2 (⊤ : Subgroup E) :=
    (bar2TopMulEquiv (K := X₁)).symm.trans (e2a.trans e2b)
  exact (inFSq_iff_bar2_inF_mulEquiv e n).2 hE

theorem barImage_map_pCoreQuotMulAut {M K : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (M : Set G)) (hKM : K ≤ M) :
    (UC22.barImage M K).map
        (CFSG.pCoreQuotMulAut ↥M (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom
      = UC22.barImage M (K.map (MulAut.conj t).toMonoidHom) := by
  classical
  have hconj : K.map (MulAut.conj t).toMonoidHom ≤ M := by
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.mem_normalizer_iff.mp ht k |>.1 (hKM hk)
  have hval : ∀ (m : ↥M) (hmM : t * (m : G) * t⁻¹ ∈ M),
      (CFSG.pCoreQuotMulAut ↥M (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom
          (uc22p21cPi M m) = uc22p21cPi M ⟨t * (m : G) * t⁻¹, hmM⟩ := by
    intro m hmM
    show (CFSG.pCoreQuotMulAut ↥M (Subgroup.normalizerMonoidHom M ⟨t, ht⟩))
        (QuotientGroup.mk m) = QuotientGroup.mk ⟨t * (m : G) * t⁻¹, hmM⟩
    rw [CFSG.pCoreQuotMulAut_mk]
    rfl
  ext q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, hmK, hm⟩ := (uc22p21c_mem_barImage).mp hy
    have hmemM : t * (m : G) * t⁻¹ ∈ M := Subgroup.mem_normalizer_iff.mp ht (m : G) |>.1 m.2
    rw [← hm, hval m hmemM]
    exact (uc22p21c_mem_barImage).mpr
      ⟨⟨t * (m : G) * t⁻¹, hmemM⟩, ⟨(m : G), hmK, (MulAut.conj_apply _ _).symm⟩, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨k, hkK, hkm⟩ := hm
    have hmM : t * k * t⁻¹ ∈ M := hconj ⟨k, hkK, rfl⟩
    have hkM : k ∈ M := hKM hkK
    refine ⟨uc22p21cPi M ⟨k, hkM⟩, (uc22p21c_mem_barImage).mpr ⟨⟨k, hkM⟩, hkK, rfl⟩, ?_⟩
    rw [hval ⟨k, hkM⟩ hmM]
    congr 1
    exact Subtype.ext hkm

theorem mem_normalizer_barPreimage {M : Subgroup G} {Y : Subgroup (Bar2 M)} {t : G}
    (ht : t ∈ Subgroup.normalizer (M : Set G))
    (hY : Y.map (CFSG.pCoreQuotMulAut ↥M (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom
      = Y) :
    t ∈ Subgroup.normalizer (UC22.barPreimage M Y : Set G) := by
  classical
  have hval : ∀ (u : G) (hu : u ∈ Subgroup.normalizer (M : Set G)) (x : ↥M)
      (huM : u * (x : G) * u⁻¹ ∈ M),
      (CFSG.pCoreQuotMulAut ↥M (Subgroup.normalizerMonoidHom M ⟨u, hu⟩)).toMonoidHom
          (uc22p21cPi M x) = uc22p21cPi M ⟨u * (x : G) * u⁻¹, huM⟩ := by
    intro u hu x huM
    show (CFSG.pCoreQuotMulAut ↥M (Subgroup.normalizerMonoidHom M ⟨u, hu⟩))
        (QuotientGroup.mk x) = QuotientGroup.mk ⟨u * (x : G) * u⁻¹, huM⟩
    rw [CFSG.pCoreQuotMulAut_mk]
    rfl
  have step : ∀ x ∈ M, (x ∈ UC22.barPreimage M Y ↔
      t * x * t⁻¹ ∈ UC22.barPreimage M Y) := by
    intro x hxM
    have hmemM : t * x * t⁻¹ ∈ M := Subgroup.mem_normalizer_iff.mp ht x |>.1 hxM
    have hxu : uc22p21cPi M ⟨t * x * t⁻¹, hmemM⟩ =
        (CFSG.pCoreQuotMulAut ↥M (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom
          (uc22p21cPi M ⟨x, hxM⟩) := (hval t ht ⟨x, hxM⟩ hmemM).symm
    constructor
    · intro hx
      obtain ⟨hxM', hxY⟩ := (uc22p21c_mem_barPreimage).mp hx
      have hyφ : (CFSG.pCoreQuotMulAut ↥M
          (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom (uc22p21cPi M ⟨x, hxM'⟩) ∈ Y := by
        have h1 : (CFSG.pCoreQuotMulAut ↥M
            (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom (uc22p21cPi M ⟨x, hxM'⟩) ∈
            Y.map (CFSG.pCoreQuotMulAut ↥M
              (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hxY
        rwa [hY] at h1
      have hy : uc22p21cPi M ⟨t * x * t⁻¹, hmemM⟩ ∈ Y := by
        rw [hxu]
        exact hyφ
      exact (uc22p21c_mem_barPreimage).mpr ⟨hmemM, hy⟩
    · intro hx
      obtain ⟨hxM', hxY⟩ := (uc22p21c_mem_barPreimage).mp hx
      have hy : uc22p21cPi M ⟨t * x * t⁻¹, hmemM⟩ ∈ Y := by
        rw [show (⟨t * x * t⁻¹, hmemM⟩ : ↥M) = ⟨t * x * t⁻¹, hxM'⟩ from Subtype.ext rfl]
        exact hxY
      refine (uc22p21c_mem_barPreimage).mpr ⟨hxM, ?_⟩
      have hyφ : (CFSG.pCoreQuotMulAut ↥M
          (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom (uc22p21cPi M ⟨x, hxM⟩) ∈
          Y.map (CFSG.pCoreQuotMulAut ↥M
            (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom := by
        rw [hY, ← hxu]
        exact hy
      exact (Subgroup.mem_map_iff_mem (f := (CFSG.pCoreQuotMulAut ↥M
        (Subgroup.normalizerMonoidHom M ⟨t, ht⟩)).toMonoidHom)
        (MulEquiv.injective _)).mp hyφ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (step x (uc22p21c_mem_barPreimage.mp hx).1).mp hx
  · intro hx
    have hxM : x ∈ M := by
      have h1 : t * x * t⁻¹ ∈ M := (uc22p21c_mem_barPreimage.mp hx).1
      have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) (t * x * t⁻¹) |>.1 h1
      rwa [show t⁻¹ * (t * ↑x * t⁻¹) * (t⁻¹)⁻¹ = ↑x from by group] at h2
    exact (step x hxM).mpr hx

theorem uniqueMax_iSup_of_noncyclic_of_le {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (D : Data G) (h61 : UC6.R6_1 D) (h : Hyp18 D V₀ V p L)
    {Δ : Set (Subgroup G)} (hΔM : (⨆ H ∈ Δ, H) ≤ D.M)
    (hM : D.M ∈ calMOf (⨆ H ∈ Δ, H))
    {A : Subgroup G} (hA : A ≤ ⨆ H ∈ Δ, H) (hAp : IsPGroup p A) (hAc : ¬ IsCyclic A) :
    UniqueMax D.M (⨆ H ∈ Δ, H) := by
  refine Set.Subset.antisymm (fun N hN => ?_) (fun N hN => ?_)
  · rw [Set.mem_singleton_iff]
    have hNM : N ≤ D.M :=
      le_of_noncyclic_of_isTwoLocal D h61 h.hp (hA.trans hΔM) hAp hAc hN.1.1
        (hA.trans hN.2)
    exact (hN.1.2 D.M D.maxLocal.1 hNM).symm
  · rw [Set.mem_singleton_iff] at hN
    subst N
    exact hM

theorem tPullbackData {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) {X : Subgroup G} (hX : X = UC22.conjClosure D.M L) :
    ∃ (Sbar : Subgroup (Bar2 X)) (φ : ↥D.T →* MulAut (Bar2 X))
      (R : Subgroup (MulAut (Bar2 X))),
      Sbar = UC22.barImage X (D.T ⊓ X) ∧
        IsSylowIn 2 (D.T ⊓ X) X ∧ IsSylowIn 2 Sbar ⊤ ∧ IsPGroup 2 R ∧
          (∀ r ∈ R, Sbar.map r.toMonoidHom = Sbar) ∧
            (∀ t : ↥D.T, φ t ∈ R) ∧
              (∀ (t : ↥D.T) (ht : (t : G) ∈ Subgroup.normalizer (X : Set G)),
                φ t = (CFSG.pCoreQuotMulAut ↥X)
                  ((Subgroup.normalizerMonoidHom X) ⟨t, ht⟩)) ∧
                D.T ≤ Subgroup.normalizer (X : Set G) ∧
                  D.T ≤ Subgroup.normalizer (D.T ⊓ X : Set G) ∧
                    IsPGroup 2 D.T := by
  classical
  have hXM : X ≤ D.M := hX.symm ▸ h.X_le_M
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hMnormX : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [hX]
    exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hTX : D.T ≤ Subgroup.normalizer (X : Set G) := hTM.trans hMnormX
  have hT2 : IsPGroup 2 D.T :=
    (WeakClosure81.isSylowOf_two_iff_isSylowIn.mp D.sylowG).2.1
  have hSylM : IsSylowIn 2 D.T D.M :=
    WeakClosure81.isSylowOf_two_iff_isSylowIn.mp D.sylowM
  have hSylS : IsSylowIn 2 (D.T ⊓ X) X := by
    have h := CFSG.isSylowTwoOf_inf_of_normal (S := D.T) (X := D.M) (N := X)
      (show CFSG.QuasithinUnique.IsSylowTwoOf D.T D.M from
        ⟨hSylM.1, hSylM.2.1, hSylM.2.2⟩) hXM hMnormX
    have h2 := h
    rw [inf_comm] at h2
    exact ⟨h2.1, h2.2.1, h2.2.2⟩
  have hSstab : D.T ≤ Subgroup.normalizer (D.T ⊓ X : Set G) := by
    have h := CFSG.GroupTheory.isSylowOf_le_normalizer_inf (p := 2) (M := D.M) (P := X) (R := D.T)
      hXM ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).mpr hMnormX) D.sylowM
    simpa [inf_comm] using h
  set Sbar : Subgroup (Bar2 X) := UC22.barImage X (D.T ⊓ X) with hSbardef
  have hSbarSyl : IsSylowIn 2 Sbar ⊤ := WeakClosure81.isSylowIn_barImage hSylS
  let ι : ↥D.T →* Subgroup.normalizer (X : Set G) :=
    { toFun := fun t => ⟨(t : G), hTX t.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  let φ : ↥D.T →* MulAut (Bar2 X) :=
    (CFSG.pCoreQuotMulAut ↥X).comp ((Subgroup.normalizerMonoidHom X).comp ι)
  let R : Subgroup (MulAut (Bar2 X)) := φ.range
  have hR2 : IsPGroup 2 R :=
    hT2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hRS : ∀ r ∈ R, Sbar.map r.toMonoidHom = Sbar := by
    rintro r ⟨t, rfl⟩
    have ht : (t : G) ∈ Subgroup.normalizer (X : Set G) := hTX t.2
    have hStab : (D.T ⊓ X).map (MulAut.conj (t : G)).toMonoidHom = D.T ⊓ X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSstab t.2)
    show (UC22.barImage X (D.T ⊓ X)).map (φ t).toMonoidHom = _
    rw [show φ t = CFSG.pCoreQuotMulAut ↥X
      (Subgroup.normalizerMonoidHom X ⟨(t : G), ht⟩) from rfl]
    rw [barImage_map_pCoreQuotMulAut ht (inf_le_right : D.T ⊓ X ≤ X), hStab]
  exact ⟨Sbar, φ, R, hSbardef, hSylS, hSbarSyl, hR2, hRS, fun t => ⟨t, rfl⟩,
    fun t ht => rfl, hTX, hSstab, hT2⟩

theorem u5_X1_data {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hK : Inputs1719.KU5Delta)
    (hKU3 : Inputs1719.K_U3IndexNormal)
    (hU5 : IsU5 (Bar2 (UC22.conjClosure D.M L)) 2) :
    ∃ (P : Subgroup (Bar2 (UC22.conjClosure D.M L))) (P₁ J₁ X₁ : Subgroup G),
      P₁ = UC22.barPreimage (UC22.conjClosure D.M L) P ∧ J₁ = Opp 2 P₁ ∧
        X₁ = D.T ⊔ J₁ ∧ InFSq 2 X₁ ∧ D.T ≤ X₁ ∧ X₁ ≤ D.M ∧
          IsU3 (Bar2 (Opp 2 P)) 2 := by
  classical
  set X := UC22.conjClosure D.M L with hXdef
  obtain ⟨Sbar, φ, R, -, -, hSbarSyl, hR2, hRS, hφrange, hφcanon, hTX, -, hT2⟩ :=
    tPullbackData h hXdef
  obtain ⟨P, -, hPR, hJperf, hJq, hJU3⟩ :=
    hK (Bar2 X) hU5 Sbar R hSbarSyl hR2 hRS
  have hext := fun (E : Type) [Group E] [Finite E] (J_E : Subgroup E) [J_E.Normal] =>
    inFSq_top_of_normal_mulEquiv_isU3 hKU3 hJperf hJq hJU3 E J_E
  set P₁ : Subgroup G := UC22.barPreimage X P with hP₁def
  set J₁ : Subgroup G := Opp 2 P₁ with hJ₁def
  set X₁ : Subgroup G := D.T ⊔ J₁ with hX₁def
  have hP₁X : P₁ ≤ X := uc22p21c_barPreimage_le X P
  have hbP : UC22.barImage X P₁ = P :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_barPreimage X P
  have hN₀P₁ : CFSG.Open.pCoreOf 2 X ≤ P₁ := UC22.pCoreOf_le_barPreimage X P
  have hTP : D.T ≤ Subgroup.normalizer (P₁ : Set G) := by
    intro t ht
    refine mem_normalizer_barPreimage (hTX ht) ?_
    rw [← hφcanon ⟨t, ht⟩ (hTX ht)]
    exact hPR _ (hφrange _)
  have hTN₀ : D.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    hTX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) X)
  have hJ₁P₁ : J₁ ≤ P₁ := by
    rw [hJ₁def]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 2 P₁
  have hJX₁ : J₁ ≤ X₁ := hX₁def ▸ le_sup_right
  have hTX₁ : D.T ≤ X₁ := hX₁def ▸ le_sup_left
  have hX₁M : X₁ ≤ D.M := hX₁def ▸ sup_le D.sylowM.le (hJ₁P₁.trans (hP₁X.trans h.X_le_M))
  have hF₁ : InFSq 2 X₁ :=
    inFSq_X1_of_extension_clause (X := X) (T := D.T) (P₁ := P₁) (J₁ := J₁) (X₁ := X₁)
      (P := P) hP₁X hX₁def hJ₁def hTN₀ hTP hTX₁ hJX₁ hN₀P₁ hbP hext hT2
  exact ⟨P, P₁, J₁, X₁, rfl, rfl, rfl, hF₁, hTX₁, hX₁M, hJU3⟩

theorem u5_noncyclic {D : Data G} {p : ℕ}
    {X : Subgroup G} {P : Subgroup (Bar2 X)}
    {P₁ J₁ X₁ : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP₁ : P₁ = UC22.barPreimage X P)
    (hJ₁ : J₁ = Opp 2 P₁) (hX₁ : X₁ = D.T ⊔ J₁)
    (hU3 : IsU3 (Bar2 (Opp 2 P)) 2) (hp5 : p = 5) :
    ∃ A : Subgroup G, A ≤ X₁ ∧ IsPGroup p A ∧ ¬ IsCyclic A ∧ p ∣ Nat.card X₁ := by
  classical
  have hP₁X : P₁ ≤ X := hP₁ ▸ uc22p21c_barPreimage_le X P
  have hbP : UC22.barImage X P₁ = P := hP₁ ▸
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_barPreimage X P
  have hN₀P₁ : CFSG.Open.pCoreOf 2 X ≤ P₁ :=
    hP₁ ▸ UC22.pCoreOf_le_barPreimage X P
  have hJ₁P₁ : J₁ ≤ P₁ := by
    rw [hJ₁]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 2 P₁
  haveI : Fact p.Prime := ⟨hp⟩
  have hbr5 : CFSG.pRank 5 ↥(⊤ : Subgroup (Bar2 (Opp 2 P))) =
      CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 (Opp 2 P))) :=
    (CFSG.SectionRank.pRank_eq_open_pRank_top 5
      ↥(⊤ : Subgroup (Bar2 (Opp 2 P)))).trans
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 5)
        (⊤ : Subgroup (Bar2 (Opp 2 P)))).symm
  have hpRank5 : CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 (Opp 2 P))) = 2 :=
    hbr5.symm.trans (Inputs1719.kU34Data_fiveRank (X := Bar2 (Opp 2 P)) hU3)
  have hpRankP : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 (Opp 2 P))) = 2 := by
    rw [hp5]
    exact hpRank5
  obtain ⟨E, -, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p)
      (H := (⊤ : Subgroup (Bar2 (Opp 2 P)))) (k := 2) (by rw [hpRankP])
  have hJ2 : IsPGroup 2 (CFSG.pCore 2 ↥(Opp 2 P)) := CFSG.pCore_isPGroup
  let ψ₁ : ↥(Opp 2 P) →* Bar2 (Opp 2 P) := QuotientGroup.mk' (CFSG.pCore 2 ↥(Opp 2 P))
  have hker₁ : ¬ p ∣ Nat.card ψ₁.ker := by
    rw [show ψ₁.ker = CFSG.pCore 2 ↥(Opp 2 P) from QuotientGroup.ker_mk' _]
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hJ2 hp hp2
  obtain ⟨EJ, hEJel, hEJmap, hEJcard⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ₁ hker₁
      (S := E) (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)
      hEel
  have hbJ : UC22.barImage X J₁ = Opp 2 P := by
    rw [hJ₁, CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_opp (p := 2)
      Nat.prime_two hP₁X, hbP]
    rfl
  let ψ₂ : ↥J₁ →* ↥(Opp 2 P) :=
    ((uc22p21cPi X).comp (Subgroup.inclusion (hJ₁P₁.trans hP₁X))).codRestrict
      (Opp 2 P) (fun z => by
        rw [← hbJ]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr z.2))
  have hψ₂ : Function.Surjective ψ₂ := by
    intro y
    have hy : (y : Bar2 X) ∈ UC22.barImage X J₁ := by
      rw [hbJ]
      exact y.2
    obtain ⟨z, hzJ, hzy⟩ := (uc22p21c_mem_barImage).mp hy
    refine ⟨⟨z, hzJ⟩, ?_⟩
    exact Subtype.ext hzy
  have hker₂ : ψ₂.ker = (CFSG.Open.pCoreOf 2 X).subgroupOf J₁ := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hval : (ψ₂ z : Bar2 X) = (uc22p21cPi X) (Subgroup.inclusion (hJ₁P₁.trans hP₁X) z) := rfl
    have hmem_iff : ((Subgroup.inclusion (hJ₁P₁.trans hP₁X) z : ↥X) : Bar2 X) = 1 ↔
        (Subgroup.inclusion (hJ₁P₁.trans hP₁X) z : ↥X) ∈ CFSG.pCore 2 ↥X :=
      QuotientGroup.eq_one_iff _
    rw [Subtype.ext_iff, hval]
    change ((Subgroup.inclusion (hJ₁P₁.trans hP₁X) z : ↥X) : Bar2 X) = 1 ↔
      (z : G) ∈ CFSG.Open.pCoreOf 2 X
    rw [hmem_iff]
    constructor
    · intro hz
      exact Subgroup.mem_map_of_mem X.subtype hz
    · intro hz
      obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
      have h2 : (⟨(z : G), Subgroup.map_subtype_le _ hz⟩ : ↥X) = y := Subtype.ext hyz.symm
      show (⟨(z : G), _⟩ : ↥X) ∈ CFSG.pCore 2 ↥X
      rw [h2]
      exact hy
  have hN₀J₁ : CFSG.Open.pCoreOf 2 X ≤ J₁ := by
    rw [hJ₁]
    exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_isPGroup_pCoreOf X) hN₀P₁
  have hker₂dvd : ¬ p ∣ Nat.card ψ₂.ker := by
    rw [hker₂]
    have hJ2' : IsPGroup 2 ((CFSG.Open.pCoreOf 2 X).subgroupOf J₁) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_isPGroup_pCoreOf X).of_equiv
        (Subgroup.subgroupOfEquivOfLe hN₀J₁).symm
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup hJ2' hp hp2
  obtain ⟨E₁, hE₁el, hE₁map, hE₁card⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range ψ₂ hker₂dvd
      (S := EJ) (by rw [MonoidHom.range_eq_top.mpr hψ₂]; exact le_top) hEJel
  let A : Subgroup G := E₁.map J₁.subtype
  have hAel : IsElemAbelian p A := hE₁el.map J₁.subtype
  have hAcard : Nat.card A = p ^ 2 := by
    rw [Subgroup.card_map_of_injective J₁.subtype_injective, hE₁card, hEJcard, hEcard]
  have hAX₁ : A ≤ X₁ := hX₁ ▸ (Subgroup.map_subtype_le E₁).trans le_sup_right
  have hpdvd : p ∣ Nat.card X₁ := by
    have h2 : p ∣ Nat.card A := hAcard ▸ dvd_pow_self p (by norm_num)
    exact h2.trans (Subgroup.card_dvd_of_le hAX₁)
  exact ⟨A, hAX₁, hAel.isPGroup, UC22.uc22p22u_not_isCyclic_of_card_sq hp hAel hAcard,
    hpdvd⟩

theorem u5_p_eq_five
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (hU5 : IsU5 (Bar2 (UC22.conjClosure D.M L)) 2) :
    p = 5 := by
  classical
  set X := UC22.conjClosure D.M L with hXdef
  have hsX : IsSimpleGroup (Bar2 X) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5
  have hXL : X = L := conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
  have hp : p.Prime := h.p_prime
  have hconcl : S17.Concl17_42 D L X p := h1742 L p h.hL.1 h.hp
  rcases hconcl with h1 | ⟨m, x, -, -, hne, -, -⟩ | ⟨m, hU5', hm2, -, hp5', -⟩ |
    ⟨m, hsp, hm1, -, hcong4, -, -⟩ | ⟨m, hU4', hm1, hcong5, -⟩
  · rcases h1 with hthin | ⟨m, hU3⟩ | hL3
    · exact absurd hthin (S17.not_thin8_of_isU5_bar2 hU5)
    · exact absurd (lieModel_eq_of_isChar2LieShape hU5 isChar2LieShape_PSU_five
        hU3).2.1 (by norm_num)
    · exact absurd (lieModel_eq_of_isChar2LieShape hU5 isChar2LieShape_PSU_five
        hL3).1 (by decide)
  · exact absurd hXL hne
  · exact hp5'
  · have hm : m = 2 := by
      rcases hsp with hsp | hg2
      · exact fieldExponent_eq_of_isChar2LieShape hU5 isChar2LieShape_PSU_five hsp
      · exact absurd (lieModel_eq_of_isChar2LieShape hU5 isChar2LieShape_PSU_five
          hg2).1 (by decide)
    have hcong : (2 : ℤ) ^ 2 ≡ -1 [ZMOD (p : ℤ)] := hm ▸ hcong4
    have h5 : (p : ℤ) ∣ 5 := by
      have h := hcong.symm.dvd
      norm_num at h
      exact h
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (Int.natCast_dvd_natCast.mp h5)
  · have hm : m = 2 :=
      fieldExponent_eq_of_isChar2LieShape hU5 isChar2LieShape_PSU_five hU4'
    have hcong : (2 : ℤ) ^ 2 ≡ -1 [ZMOD (p : ℤ)] := hm ▸ hcong5
    have h5 : (p : ℤ) ∣ 5 := by
      have h := hcong.symm.dvd
      norm_num at h
      exact h
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (Int.natCast_dvd_natCast.mp h5)

theorem r18_7b_U5
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (hSg : UC6S846.SigmaStd D) (h1742 : S17.R17_42At D V₀ V)
    (hK : Inputs1719.KU5Delta) (hKU3 : Inputs1719.K_U3IndexNormal) (hV₀ : V₀ ≠ ⊥)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    (hU5 : IsU5 (Bar2 (UC22.conjClosure D.M L)) 2) :
    R18_7bAt D V₀ V p L h := by
  classical
  set X := UC22.conjClosure D.M L with hXdef
  have hXL : X = L := by
    have hsX : IsSimpleGroup (Bar2 X) :=
      LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU5
    exact conjClosure_eq_self_of_isSimpleGroup_bar2 h.hL.1 hsX
  have hUL : IsU5 (Bar2 L) 2 := hXL ▸ hU5
  have hp5 : p = 5 := u5_p_eq_five h h1742 hU5
  have hnof : S17.nOf L = 2 :=
    S17.nOf_eq_of_isChar2LieShape hUL isChar2LieShape_PSU_five
  obtain ⟨P, P₁, J₁, X₁, hP₁, hJ₁, hX₁, hF₁, hTX₁, hX₁M, hU3⟩ :=
    u5_X1_data (D := D) h hK hKU3 hU5
  obtain ⟨A, hAX₁, hAp, hAc, hp₁⟩ :=
    u5_noncyclic (X := X) h.p_prime h.p_ne_two hP₁ hJ₁ hX₁ hU3 hp5
  have hΔ : ∀ H ∈ ({X₁} : Set (Subgroup G)), D.T ≤ H ∧ H ≤ D.M := by
    intro H hH
    rw [Set.mem_singleton_iff] at hH
    subst hH
    exact ⟨hTX₁, hX₁M⟩
  have hΔU : UniqueMax D.M (⨆ H ∈ ({X₁} : Set (Subgroup G)), H) := by
    have hsup : (⨆ H ∈ ({X₁} : Set (Subgroup G)), H) = X₁ := by simp
    have hΔM : (⨆ H ∈ ({X₁} : Set (Subgroup G)), H) ≤ D.M := hsup.le.trans hX₁M
    have hM : D.M ∈ calMOf (⨆ H ∈ ({X₁} : Set (Subgroup G)), H) := by
      rw [hsup]
      exact ⟨D.maxLocal, hX₁M⟩
    have hA : A ≤ (⨆ H ∈ ({X₁} : Set (Subgroup G)), H) := le_trans hAX₁ hsup.symm.le
    exact hsup.symm ▸ uniqueMax_iSup_of_noncyclic_of_le D h61 h hΔM hM hA hAp hAc
  have hΔp : ∀ H ∈ ({X₁} : Set (Subgroup G)), p ∣ Nat.card H := by
    intro H hH
    rw [Set.mem_singleton_iff] at hH
    subst hH
    exact hp₁
  have hΔn : fIndexMax ({X₁} : Set (Subgroup G)) ≤ (S17.nOf L : ℕ∞) := by
    rw [hnof]
    refine fIndexMax_le_iff.2 fun H hH => ?_
    rw [Set.mem_singleton_iff] at hH
    subst hH
    exact hF₁
  exact r18_7b_of_delta' D hx h61 h127 h1114 h162 hTor h1482 h126 hSg h hV₀ hX1
    hΔ hΔU hΔp hΔn

theorem u4_X1_data {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hK : Inputs1719.KU4Delta)
    (hKL2 : Inputs1719.K_L2SzAutRank)
    {n : ℕ} (hn : 2 ≤ n) (hU4 : IsU4 (Bar2 (UC22.conjClosure D.M L)) n)
    (hpq : p ∣ 2 ^ n + 1) :
    ∃ (P : Subgroup (Bar2 (UC22.conjClosure D.M L)))
      (Y₀ : Subgroup (Bar2 (UC22.conjClosure D.M L))) (P₁ J₁ X₁ N H : Subgroup G),
      P₁ = UC22.barPreimage (UC22.conjClosure D.M L) P ∧ J₁ = Opp 2 P₁ ∧
        X₁ = D.T ⊔ J₁ ∧ H = D.T ⊔ N ∧
          N ≤ UC22.conjClosure D.M L ∧
            Y₀ ≤ UC22.barImage (UC22.conjClosure D.M L) N ∧
              InFSq n X₁ ∧ D.T ≤ X₁ ∧ X₁ ≤ D.M ∧ D.T ≤ H ∧ H ≤ D.M ∧
                Nat.card ↥H = p * Nat.card ↥D.T ∧
                  p ∣ Nat.card ↥X₁ ∧ p ∣ Nat.card ↥H ∧
                    CFSG.Open.pCoreOf 2 (UC22.conjClosure D.M L) ≤ J₁ ∧
                      IsL2 (Bar2 (Opp 2 P)) n ∧ D.T ≤ Subgroup.normalizer (P₁ : Set G) ∧
                        D.T ⊓ UC22.conjClosure D.M L ≤ J₁ ∧
                          UC22.barImage (UC22.conjClosure D.M L) J₁ = Opp 2 P ∧
                      (∃ E : Subgroup (Bar2 (UC22.conjClosure D.M L)),
                        E ≤ Opp 2 P ⊔ Y₀ ∧ CFSG.Open.IsElemAbelian p E ∧
                          Nat.card E = p ^ 2) := by
  classical
  set X := UC22.conjClosure D.M L with hXdef
  obtain ⟨Sbar, φ, R, hSbar, hSylS, hSbarSyl, hR2, hRS, hφrange, hφcanon, hTX, -, hT2⟩ :=
    tPullbackData h hXdef
  obtain ⟨P, Y₀, hPmax, hPR, hJperf, hJU4, hY₀card, hY₀N, hSY₀R, E₀, hE₀le, hE₀el, hE₀card⟩ :=
    hK (Bar2 X) n hn hU4 Sbar R p hSbarSyl hR2 hRS h.p_prime hpq
  have hext := fun (E : Type) [Group E] [Finite E] (J_E : Subgroup E) [J_E.Normal] =>
    inFSq_top_of_normal_mulEquiv_isL2 hKL2 hJperf hJU4 E J_E
  set P₁ : Subgroup G := UC22.barPreimage X P with hP₁def
  set J₁ : Subgroup G := Opp 2 P₁ with hJ₁def
  set X₁ : Subgroup G := D.T ⊔ J₁ with hX₁def
  set N : Subgroup G := UC22.barPreimage X (Sbar ⊔ Y₀) with hNdef
  set H : Subgroup G := D.T ⊔ N with hHdef
  have hP₁X : P₁ ≤ X := uc22p21c_barPreimage_le X P
  have hbP : UC22.barImage X P₁ = P :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_barPreimage X P
  have hNX : N ≤ X := uc22p21c_barPreimage_le X (Sbar ⊔ Y₀)
  have hbN : UC22.barImage X N = Sbar ⊔ Y₀ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_barPreimage X (Sbar ⊔ Y₀)
  have hY₀bN : Y₀ ≤ UC22.barImage X N := by
    rw [hbN]
    exact le_sup_right
  have hN₀P₁ : CFSG.Open.pCoreOf 2 X ≤ P₁ := UC22.pCoreOf_le_barPreimage X P
  have hN₀J₁ : CFSG.Open.pCoreOf 2 X ≤ J₁ := by
    rw [hJ₁def]
    exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_isPGroup_pCoreOf X) hN₀P₁
  have hN₀N : CFSG.Open.pCoreOf 2 X ≤ N := UC22.pCoreOf_le_barPreimage X (Sbar ⊔ Y₀)
  have hTP : D.T ≤ Subgroup.normalizer (P₁ : Set G) := by
    intro t ht
    refine mem_normalizer_barPreimage (hTX ht) ?_
    rw [← hφcanon ⟨t, ht⟩ (hTX ht)]
    exact hPR _ (hφrange _)
  have hTN : D.T ≤ Subgroup.normalizer (N : Set G) := by
    intro t ht
    refine mem_normalizer_barPreimage (hTX ht) ?_
    rw [← hφcanon ⟨t, ht⟩ (hTX ht)]
    exact hSY₀R _ (hφrange _)
  have hTN₀ : D.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    hTX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) X)
  have hJ₁P₁ : J₁ ≤ P₁ := by
    rw [hJ₁def]
    exact CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 2 P₁
  have hJX₁ : J₁ ≤ X₁ := hX₁def ▸ le_sup_right
  have hTX₁ : D.T ≤ X₁ := hX₁def ▸ le_sup_left
  have hX₁M : X₁ ≤ D.M := hX₁def ▸ sup_le D.sylowM.le (hJ₁P₁.trans (hP₁X.trans h.X_le_M))
  have hTH : D.T ≤ H := hHdef ▸ le_sup_left
  have hHM : H ≤ D.M := hHdef ▸ sup_le D.sylowM.le (hNX.trans h.X_le_M)
  have hF₁ : InFSq n X₁ :=
    inFSq_X1_of_extension_clause (X := X) (T := D.T) (P₁ := P₁) (J₁ := J₁) (X₁ := X₁)
      (P := P) hP₁X hX₁def hJ₁def hTN₀ hTP hTX₁ hJX₁ hN₀P₁ hbP hext hT2
  have hN₀_le_T : CFSG.Open.pCoreOf 2 X ≤ D.T := by
    haveI : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
    have hle := (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).le_sylow_of_normal hSylS.toSylow
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    have hzX : z ∈ X := Subgroup.map_subtype_le _ hz
    have h2 : y = (⟨z, hzX⟩ : ↥X) := Subtype.ext hyz
    rw [h2] at hy
    have hyT : (⟨z, hzX⟩ : ↥X) ∈ D.T.subgroupOf X := by simpa using hle hy
    exact Subgroup.mem_subgroupOf.mp hyT
  have hTN_eq : D.T ⊓ N = D.T ⊓ X := by
    refine le_antisymm (fun x hx => ⟨hx.1, hNX hx.2⟩) ?_
    rintro x ⟨hxT, hxX⟩
    refine ⟨hxT, (uc22p21c_mem_barPreimage).mpr ⟨hxX, ?_⟩⟩
    rw [hSbar]
    exact Subgroup.mem_sup_left ((uc22p21c_mem_barImage).mpr
      ⟨⟨x, hxX⟩, ⟨hxT, hxX⟩, rfl⟩)
  have hpreS : UC22.barPreimage X Sbar = D.T ⊓ X := by
    rw [hSbar]
    exact UC22.barPreimage_barImage_of_pCoreOf_le inf_le_right
      (le_inf hN₀_le_T (Subgroup.map_subtype_le _))
  have hcardTX : Nat.card ↥(D.T ⊓ X) =
      Nat.card (CFSG.Open.pCoreOf 2 X) * Nat.card Sbar := by
    rw [← hpreS, UC22.uc22p22u_card_barPreimage X Sbar]
  haveI : Fact (Nat.Prime p) := ⟨h.p_prime⟩
  have hY₀p : IsPGroup p ↥Y₀ := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by simpa using hY₀card⟩
  have hdisj : Sbar ⊓ Y₀ = ⊥ :=
    (IsPGroup.disjoint_of_ne 2 p (Ne.symm h.p_ne_two) Sbar Y₀
      hSbarSyl.isPGroup hY₀p).eq_bot
  have hcardSY : Nat.card ↥(Sbar ⊔ Y₀) = Nat.card Sbar * p := by
    have h1 := CFSG.Quasithin.H13.Ch4.card_sup_mul_card_inf_of_le_normalizer
      (L := Sbar) (X := Y₀) hY₀N
    rw [hdisj, hY₀card] at h1
    simpa using h1
  have hcardN : Nat.card ↥N = p * Nat.card ↥(D.T ⊓ X) := by
    rw [hNdef, UC22.uc22p22u_card_barPreimage X (Sbar ⊔ Y₀), hcardSY, hcardTX]
    ring
  have hcardH : Nat.card ↥H = p * Nat.card ↥D.T := by
    have h1 := CFSG.Quasithin.H13.Ch4.card_sup_mul_card_inf_of_le_normalizer
      (L := N) (X := D.T) hTN
    rw [show N ⊓ D.T = D.T ⊓ X from by rw [inf_comm]; exact hTN_eq, hcardN] at h1
    have h2 : Nat.card ↥(D.T ⊔ N) * Nat.card ↥(D.T ⊓ X) =
        p * Nat.card ↥D.T * Nat.card ↥(D.T ⊓ X) := by
      rw [sup_comm]
      rw [h1]
      ring
    have h3 : Nat.card ↥(D.T ⊔ N) = p * Nat.card ↥D.T :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
    rwa [hHdef]
  have hbJ : UC22.barImage X J₁ = Opp 2 P := by
    rw [hJ₁def, CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_opp (p := 2)
      Nat.prime_two hP₁X, hbP]
    rfl
  have hpL2 : p ∣ Nat.card (Bar2 (Opp 2 P)) := by
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) hJU4)]
    have h1 : p ∣ (2 ^ n) ^ 2 - 1 := by
      have h2 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        have := Nat.sq_sub_sq (2 ^ n) 1
        simpa using this
      rw [h2]
      exact dvd_mul_of_dvd_left hpq _
    exact dvd_mul_of_dvd_right h1 _
  have hpJ : p ∣ Nat.card ↥(Opp 2 P) := by
    have h1 : Nat.card ↥(Opp 2 P) =
        Nat.card (Bar2 (Opp 2 P)) * Nat.card ↥(CFSG.pCore 2 ↥(Opp 2 P)) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(Opp 2 P))
    rw [h1]
    exact dvd_mul_of_dvd_left hpL2 _
  have hpre : UC22.barPreimage X (UC22.barImage X J₁) = J₁ :=
    UC22.barPreimage_barImage_of_pCoreOf_le (hJ₁P₁.trans hP₁X) hN₀J₁
  have hpJ₁ : p ∣ Nat.card ↥J₁ := by
    have h1 : Nat.card ↥J₁ = Nat.card (CFSG.Open.pCoreOf 2 X) * Nat.card ↥(Opp 2 P) := by
      rw [← hpre, UC22.uc22p22u_card_barPreimage X (UC22.barImage X J₁), hbJ]
    rw [h1]
    exact dvd_mul_of_dvd_right hpJ _
  have hp₁ : p ∣ Nat.card ↥X₁ := hpJ₁.trans (Subgroup.card_dvd_of_le hJX₁)
  have hdvdH : p ∣ Nat.card ↥H := by
    rw [hcardH]
    exact dvd_mul_right p _
  have hSP : Sbar ≤ P := (le_inf le_top Subgroup.le_normalizer).trans hPmax.2.1
  have hTXP₁ : D.T ⊓ X ≤ P₁ := by
    rw [← hpreS]
    intro x hx
    obtain ⟨hxX, hxS⟩ := uc22p21c_mem_barPreimage.mp hx
    exact uc22p21c_mem_barPreimage.mpr ⟨hxX, hSP hxS⟩
  have hTXJ : D.T ⊓ X ≤ J₁ := by
    rw [hJ₁def]
    exact CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_two (hT2.to_le inf_le_left) hTXP₁
  exact ⟨P, Y₀, P₁, J₁, X₁, N, H, rfl, rfl, rfl, rfl, hNX, hY₀bN, hF₁, hTX₁, hX₁M,
    hTH, hHM, hcardH, hp₁, hdvdH, hN₀J₁, hJU4, hTP, hTXJ, hbJ, ⟨E₀, hE₀le, hE₀el, hE₀card⟩⟩

theorem u4_H_inFSq {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    {H T : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hcardH : Nat.card ↥H = p * Nat.card ↥T) :
    InFSq n H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardTpos : 0 < Nat.card ↥T := Nat.card_pos
  have hidx : T.relIndex H = p := by
    have h1 := Subgroup.relIndex_mul_card T H
    rw [inf_of_le_left hTH] at h1
    have h2 : T.relIndex H * Nat.card ↥T = p * Nat.card ↥T := by rw [h1, hcardH]
    exact Nat.eq_of_mul_eq_mul_right hcardTpos h2
  have hTsyl : IsSylowIn 2 T H := by
    refine ⟨hTH, hT2, ?_⟩
    rw [hidx]
    intro h2dvd
    exact hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd).symm)
  have hTsylOf : CFSG.ABGLocalTools.IsSylowOf 2 T H :=
    WeakClosure81.isSylowOf_two_iff_isSylowIn.mpr hTsyl
  have hpdvd : p ∣ Nat.card ↥H := by
    rw [hcardH]
    exact dvd_mul_right p _
  obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) p hpdvd
  let A : Subgroup G := Subgroup.zpowers (g : G)
  have hAH : A ≤ H := by
    rintro x ⟨m, rfl⟩
    exact H.zpow_mem g.2 m
  have hAcard : Nat.card A = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hgord]
  have hAo : Odd (Nat.card A) := by
    rw [hAcard]
    exact hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hY : Nat.card ↥H = Nat.card A * 2 ^ k := by rw [hcardH, hAcard, hk]
  have hperm : Permutes A T := uc22p22r_permutes_of_hall hAH hAo hY hTsylOf
  have hinf : A ⊓ T = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hAcard, hk]
    exact Nat.Coprime.pow_right k (hp.odd_of_ne_two hp2).coprime_two_right
  have hcardAT : Nat.card ↥(A ⊔ T) = p * Nat.card ↥T := by
    rw [CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.card_sup_of_permutable hperm hinf, hAcard]
  have hATH : A ⊔ T = H :=
    Subgroup.eq_of_le_of_card_ge (sup_le hAH hTH) (by rw [hcardAT, hcardH])
  have h1 : InFSq 1 (A ⊔ T) :=
    inFSq_one_of_prime_mul_two_group A T p hp (hp.odd_of_ne_two hp2) hAcard hT2 hperm
  rw [hATH] at h1
  exact TwelveTwentyTwo.inFSq_mono (by omega) h1

noncomputable def bar2RestrictMap {X J₁ N : Subgroup G} (h : J₁ ⊔ N ≤ X) :
    ↥(J₁ ⊔ N) →* Bar2 X :=
  (uc22p21cPi X).comp (Subgroup.inclusion h)

theorem bar2RestrictMap_ker {X J₁ N : Subgroup G} (h : J₁ ⊔ N ≤ X) :
    (bar2RestrictMap h).ker = (CFSG.Open.pCoreOf 2 X).subgroupOf (J₁ ⊔ N) := by
  ext z
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hval : bar2RestrictMap h z = (uc22p21cPi X) (Subgroup.inclusion h z) := rfl
  have hmem_iff : ((Subgroup.inclusion h z : ↥X) : Bar2 X) = 1 ↔
      (Subgroup.inclusion h z : ↥X) ∈ CFSG.pCore 2 ↥X :=
    QuotientGroup.eq_one_iff _
  rw [hval]
  change ((Subgroup.inclusion h z : ↥X) : Bar2 X) = 1 ↔
    (z : G) ∈ CFSG.Open.pCoreOf 2 X
  rw [hmem_iff]
  constructor
  · intro hz
    exact Subgroup.mem_map_of_mem X.subtype hz
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    have h2 : (⟨(z : G), Subgroup.map_subtype_le _ hz⟩ : ↥X) = y := Subtype.ext hyz.symm
    show (⟨(z : G), _⟩ : ↥X) ∈ CFSG.pCore 2 ↥X
    rw [h2]
    exact hy

theorem bar2RestrictMap_range {X : Subgroup G} {P Y₀ : Subgroup (Bar2 X)}
    {P₁ J₁ N : Subgroup G} (h : J₁ ⊔ N ≤ X)
    (hP₁ : P₁ = UC22.barPreimage X P) (hJ₁ : J₁ = Opp 2 P₁)
    (hY₀N : Y₀ ≤ UC22.barImage X N) (hP₁X : P₁ ≤ X) :
    Opp 2 P ⊔ Y₀ ≤ (bar2RestrictMap h).range := by
  have hbP : UC22.barImage X P₁ = P := hP₁ ▸
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_barPreimage X P
  have hbJ : UC22.barImage X J₁ = Opp 2 P := by
    rw [hJ₁, CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_barImage_opp (p := 2)
      Nat.prime_two hP₁X, hbP]
    rfl
  have hJrange : Opp 2 P ≤ (bar2RestrictMap h).range := by
    intro j hj
    rw [← hbJ] at hj
    obtain ⟨x, hxJ, hxj⟩ := (uc22p21c_mem_barImage).mp hj
    exact ⟨⟨(x : G), Subgroup.mem_sup_left hxJ⟩, hxj⟩
  have hYrange : Y₀ ≤ (bar2RestrictMap h).range := by
    intro y hy
    obtain ⟨x, hxN, hxj⟩ := (uc22p21c_mem_barImage).mp (hY₀N hy)
    exact ⟨⟨(x : G), Subgroup.mem_sup_right hxN⟩, hxj⟩
  exact sup_le hJrange hYrange

theorem u4_noncyclic {p : ℕ}
    {X : Subgroup G} {P Y₀ : Subgroup (Bar2 X)}
    {P₁ J₁ N : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP₁ : P₁ = UC22.barPreimage X P) (hJ₁ : J₁ = Opp 2 P₁)
    (hY₀N : Y₀ ≤ UC22.barImage X N)
    (hP₁X : P₁ ≤ X) (hNX : N ≤ X) (hJ₁P₁ : J₁ ≤ P₁)
    (hN₀J₁ : CFSG.Open.pCoreOf 2 X ≤ J₁)
    {E : Subgroup (Bar2 X)} (hEle : E ≤ Opp 2 P ⊔ Y₀)
    (hEel : CFSG.Open.IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) :
    ∃ A' : Subgroup ↥(J₁ ⊔ N), CFSG.Open.IsElemAbelian p A' ∧ Nat.card A' = p ^ 2 := by
  classical
  have hJNX : J₁ ⊔ N ≤ X := sup_le (hJ₁P₁.trans hP₁X) hNX
  have hker : (bar2RestrictMap hJNX).ker = (CFSG.Open.pCoreOf 2 X).subgroupOf (J₁ ⊔ N) :=
    bar2RestrictMap_ker hJNX
  have hrange : Opp 2 P ⊔ Y₀ ≤ (bar2RestrictMap hJNX).range :=
    bar2RestrictMap_range hJNX hP₁ hJ₁ hY₀N hP₁X
  have hkerp : ¬ p ∣ Nat.card (bar2RestrictMap hJNX).ker := by
    rw [hker]
    have h2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 X).subgroupOf (J₁ ⊔ N)) :=
      (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_isPGroup_pCoreOf X).of_equiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_of_le_left hN₀J₁)).symm
    exact CFSG.GroupTheory.not_dvd_card_of_isPGroup h2 hp hp2
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A', hA'el, -, hA'card⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHigh.TwFive.exists_lift_of_le_range
      (bar2RestrictMap hJNX) hkerp (S := E) (hEle.trans hrange) hEel
  exact ⟨A', hA'el, hA'card.trans hEcard⟩

theorem u4_shape_data
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h1742 : S17.R17_42At D V₀ V)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    {n : ℕ} (hU4 : IsU4 (Bar2 (UC22.conjClosure D.M L)) n) :
    S17.nOf L = n ∧ 2 ≤ n ∧ p ∣ 2 ^ n + 1 := by
  classical
  have hsX : IsSimpleGroup (Bar2 (UC22.conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
  obtain ⟨e⟩ := barSubBar2Equiv_conjClosure_of_isSimpleGroup h.hyp125 h.hL.1 hsX hX1
  have hUsub : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) n :=
    LieModel.of_mulEquiv e hU4
  obtain ⟨-, hnof, hn1, hcong⟩ := isU4_barSub_cong h h1742 hUsub
  have h5 : (p : ℤ) ∣ 2 ^ n + 1 := by
    simpa using hcong.symm.dvd
  exact ⟨hnof, hn1, Int.natCast_dvd_natCast.mp h5⟩

theorem r18_7b_U4
    {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (hSg : UC6S846.SigmaStd D) (h1742 : S17.R17_42At D V₀ V)
    (hK : Inputs1719.KU4Delta) (hKL2 : Inputs1719.K_L2SzAutRank) (hV₀ : V₀ ≠ ⊥)
    (hX1 : barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥)
    {n : ℕ} (hU4 : IsU4 (Bar2 (UC22.conjClosure D.M L)) n) :
    R18_7bAt D V₀ V p L h := by
  classical
  set X := UC22.conjClosure D.M L with hXdef
  obtain ⟨hnof, hn, hpq⟩ := u4_shape_data h h1742 hX1 hU4
  obtain ⟨P, Y₀, P₁, J₁, X₁, N, H, hP₁, hJ₁, hX₁, hH, hNX, hY₀N, hF₁, hTX₁, hX₁M,
    hTH, hHM, hcardH, hp₁, hdvdH, hN₀J₁, -, -, -, -, ⟨E₀, hE₀le, hE₀el, hE₀card⟩⟩ :=
    u4_X1_data (D := D) h hK hKL2 hn hU4 hpq
  have hP₁X : P₁ ≤ X := hP₁ ▸ uc22p21c_barPreimage_le X P
  have hJ₁P₁ : J₁ ≤ P₁ := hJ₁ ▸ CFSG.LocalAnalysis.RankThreeUC.pElementSubgroup_le 2 P₁
  have hT2 : IsPGroup 2 D.T :=
    (WeakClosure81.isSylowOf_two_iff_isSylowIn.mp D.sylowG).2.1
  have hFH : InFSq n H := u4_H_inFSq h.p_prime h.p_ne_two hn hTH hT2 hcardH
  obtain ⟨A', hA'el, hA'card⟩ :=
    u4_noncyclic (X := X) (P := P) (Y₀ := Y₀) (P₁ := P₁) (J₁ := J₁) (N := N) (E := E₀)
      h.p_prime h.p_ne_two hP₁ hJ₁ hY₀N hP₁X hNX hJ₁P₁ hN₀J₁ hE₀le hE₀el hE₀card
  let A : Subgroup G := A'.map (J₁ ⊔ N).subtype
  have hAel : CFSG.Open.IsElemAbelian p A := hA'el.map (J₁ ⊔ N).subtype
  have hAcard : Nat.card A = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (J₁ ⊔ N).subtype_injective, hA'card]
  have hJX₁ : J₁ ≤ X₁ := hX₁ ▸ le_sup_right
  have hNH : N ≤ H := hH ▸ le_sup_right
  have hAX : A ≤ X₁ ⊔ H :=
    (Subgroup.map_subtype_le A').trans (sup_le_sup hJX₁ hNH)
  have hAc : ¬ IsCyclic A :=
    UC22.uc22p22u_not_isCyclic_of_card_sq h.p_prime hAel hAcard
  have hΔsup : (⨆ K ∈ ({X₁, H} : Set (Subgroup G)), K) = X₁ ⊔ H := by
    refine le_antisymm (iSup₂_le fun K hK => ?_) ?_
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
      rcases hK with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup₂_of_le X₁ (by simp) le_rfl)
        (le_iSup₂_of_le H (by simp) le_rfl)
  have hΔU : UniqueMax D.M (⨆ K ∈ ({X₁, H} : Set (Subgroup G)), K) := by
    have hΔM : (⨆ K ∈ ({X₁, H} : Set (Subgroup G)), K) ≤ D.M :=
      hΔsup.le.trans (sup_le hX₁M hHM)
    have hM : D.M ∈ calMOf (⨆ K ∈ ({X₁, H} : Set (Subgroup G)), K) := by
      rw [hΔsup]
      exact ⟨D.maxLocal, sup_le hX₁M hHM⟩
    have hAmem : A ≤ (⨆ K ∈ ({X₁, H} : Set (Subgroup G)), K) := le_trans hAX hΔsup.symm.le
    exact uniqueMax_iSup_of_noncyclic_of_le D h61 h hΔM hM hAmem hAel.isPGroup hAc
  have hΔ : ∀ K ∈ ({X₁, H} : Set (Subgroup G)), D.T ≤ K ∧ K ≤ D.M := by
    intro K hK
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl
    · exact ⟨hTX₁, hX₁M⟩
    · exact ⟨hTH, hHM⟩
  have hΔp : ∀ K ∈ ({X₁, H} : Set (Subgroup G)), p ∣ Nat.card K := by
    intro K hK
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl
    · exact hp₁
    · exact hdvdH
  have hΔn : fIndexMax ({X₁, H} : Set (Subgroup G)) ≤ (S17.nOf L : ℕ∞) := by
    rw [hnof]
    refine fIndexMax_le_iff.2 fun K hK => ?_
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl
    · exact hF₁
    · exact hFH
  exact r18_7b_of_delta' D hx h61 h127 h1114 h162 hTor h1482 h126 hSg h hV₀ hX1
    hΔ hΔU hΔp hΔn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
