module

public import CFSG.LocalAnalysis.SectionRank.Alternating
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
public import CFSG.HardMathSupport.Foote.E27.LieTwo.SylowNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s168e3_isElemAbelian_comap_of_injective {X Y : Type*} [Group X] [Group Y]
    {p : ℕ} {E : Subgroup Y} (hE : IsElemAbelian p E) (f : X →* Y)
    (hf : Function.Injective f) : IsElemAbelian p (E.comap f) := by
  haveI : IsMulCommutative E := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    change (a : X) * (b : X) = (b : X) * (a : X)
    refine hf ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' (⟨f a, a.2⟩ : E) ⟨f b, b.2⟩)
  · refine hf ?_
    rw [map_pow, hE.2 (f x) hx, map_one]

private theorem s168e3_mulAut_conj_smul_eq_map {A : Type*} [Group A] (a : A)
    (H : Subgroup A) : (MulAut.conj a) • H = H.map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem s168e3_four_le_pRank_of_alt_cover {M Y Z : Subgroup G} {n : ℕ} (hn9 : 9 ≤ n)
    (hYM : Y ≤ M) (hYN : (Y.subgroupOf M).Normal) (hZY : Z ≤ Y)
    (φ : ↥Y →* alternatingGroup (Fin n)) (hφ : Function.Surjective φ)
    (hker : φ.ker = Z.subgroupOf Y) (hZ2 : IsPGroup 2 ↥Z)
    {y : G} (hyM : y ∈ M) (hy3 : orderOf y = 3) (hyY : y ∉ Y)
    (hcomm : ∀ u ∈ Y, y * u * y⁻¹ * u⁻¹ ∈ Z) :
    4 ≤ CFSG.Open.pRank 3 M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let H : Subgroup G := Y ⊔ Subgroup.zpowers y
  have hYH : Y ≤ H := le_sup_left
  have hH_le_M : H ≤ M := sup_le hYM (Subgroup.zpowers_le.mpr hyM)
  have hyH : y ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hM_norm : M ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mp hYN
  have hYH_normal : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr (hH_le_M.trans hM_norm)
  letI : (Y.subgroupOf H).Normal := hYH_normal
  have hzy : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy3]; norm_num)
  have hzyH : IsPGroup 3 ((Subgroup.zpowers y).subgroupOf H) := hzy.comap_subtype (K := H)
  obtain ⟨S, hSle⟩ := hzyH.exists_le_sylow
  have hyS : (⟨y, hyH⟩ : ↥H) ∈ (S : Subgroup ↥H) :=
    hSle (show (⟨y, hyH⟩ : ↥H) ∈ (Subgroup.zpowers y).subgroupOf H from
      Subgroup.mem_zpowers y)
  obtain ⟨P, hP⟩ :=
    CFSG.HardMathSupport.Foote.E27.exists_sylow_subgroupOf_eq (Y.subgroupOf H) S
  let e : (Y.subgroupOf H) ≃* ↥Y := Subgroup.subgroupOfEquivOfLe hYH
  let ef : (Y.subgroupOf H) →* ↥Y := e.toMonoidHom
  have hef : Function.Surjective ef := e.surjective
  let PY : Sylow 3 ↥Y := Sylow.mapSurjective (f := ef) hef P
  have hPY_coe : (PY : Subgroup ↥Y) = (P : Subgroup (Y.subgroupOf H)).map ef :=
    Sylow.coe_mapSurjective (f := ef) (hf := hef) P
  let SG : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hSG_p : IsPGroup 3 SG := (S.2).map H.subtype
  have hSGZ : SG ⊓ Z = ⊥ := by
    have hd : Disjoint SG Z :=
      IsPGroup.disjoint_of_ne 3 2 (by norm_num) SG Z hSG_p hZ2
    exact disjoint_iff.mp hd
  have hPY_S : ∀ u : ↥PY, (((u : ↥Y) : G)) ∈ SG := by
    intro u
    have hu : (u : ↥Y) ∈ (P : Subgroup (Y.subgroupOf H)).map ef := by
      rw [← hPY_coe]
      exact u.2
    obtain ⟨a, haP, hae⟩ := Subgroup.mem_map.mp hu
    have haS : (a : ↥H) ∈ (S : Subgroup ↥H) := by
      rw [hP] at haP
      simpa only [Subgroup.mem_subgroupOf] using haP
    refine Subgroup.mem_map.mpr ⟨(a : ↥H), haS, ?_⟩
    change ((a : ↥H) : G) = ((u : ↥Y) : G)
    rw [← hae]
    rfl
  have hPY_comm : ∀ u : ↥PY, (((u : ↥Y) : G)) * y = y * (((u : ↥Y) : G)) := by
    intro u
    have hySG : y ∈ SG := Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, hyS, rfl⟩
    have huSG : ((u : ↥Y) : G) ∈ SG := hPY_S u
    have hmemZ : y * ((u : ↥Y) : G) * y⁻¹ * ((u : ↥Y) : G)⁻¹ ∈ Z :=
      hcomm _ (u : ↥Y).2
    have hmemSG : y * ((u : ↥Y) : G) * y⁻¹ * ((u : ↥Y) : G)⁻¹ ∈ SG :=
      SG.mul_mem (SG.mul_mem (SG.mul_mem hySG huSG) (SG.inv_mem hySG)) (SG.inv_mem huSG)
    have hone : y * ((u : ↥Y) : G) * y⁻¹ * ((u : ↥Y) : G)⁻¹ = 1 := by
      have hbot : y * ((u : ↥Y) : G) * y⁻¹ * ((u : ↥Y) : G)⁻¹ ∈ SG ⊓ Z :=
        ⟨hmemSG, hmemZ⟩
      rw [hSGZ] at hbot
      simpa using hbot
    have hconj : y * ((u : ↥Y) : G) * y⁻¹ = ((u : ↥Y) : G) :=
      mul_inv_eq_one.mp hone
    calc ((u : ↥Y) : G) * y = (y * ((u : ↥Y) : G) * y⁻¹) * y := by rw [hconj]
      _ = y * ((u : ↥Y) : G) := by group
  have h3alt : 3 ≤ pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
    CFSG.SectionRank.three_le_pRank_alternating hn9
  obtain ⟨E₀, -, hE₀ea, hE₀card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (H := ⊤) (k := 3) h3alt
  have hE₀pg : IsPGroup 3 E₀ := IsPGroup.of_card (n := 3) hE₀card
  obtain ⟨R₀, hE₀R₀⟩ := hE₀pg.exists_le_sylow
  let SY : Sylow 3 (alternatingGroup (Fin n)) := PY.mapSurjective hφ
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (M := alternatingGroup (Fin n)) R₀ SY
  have hSY_coe : (SY : Subgroup (alternatingGroup (Fin n))) =
      (PY : Subgroup ↥Y).map φ :=
    Sylow.coe_mapSurjective (f := φ) (hf := hφ) PY
  have hconjR : (R₀ : Subgroup (alternatingGroup (Fin n))).map
      (MulAut.conj a).toMonoidHom = (SY : Subgroup (alternatingGroup (Fin n))) := by
    rw [← s168e3_mulAut_conj_smul_eq_map a (R₀ : Subgroup (alternatingGroup (Fin n)))]
    rw [← Sylow.coe_subgroup_smul (g := a) (P := R₀), ha]
  let E₁ : Subgroup (alternatingGroup (Fin n)) :=
    E₀.map (MulAut.conj a).toMonoidHom
  have hE₁_le : E₁ ≤ (SY : Subgroup (alternatingGroup (Fin n))) := by
    show E₀.map (MulAut.conj a).toMonoidHom ≤ (SY : Subgroup (alternatingGroup (Fin n)))
    rw [← hconjR]
    exact Subgroup.map_mono hE₀R₀
  have hE₁ea : IsElemAbelian 3 E₁ :=
    CFSG.SectionRank.isElemAbelian_map hE₀ea (MulAut.conj a).toMonoidHom
  have hE₁card : Nat.card E₁ = 3 ^ 3 := by
    show Nat.card (E₀.map (MulAut.conj a).toMonoidHom) = 3 ^ 3
    rw [Subgroup.card_map_of_injective (K := E₀)
      (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective]
    exact hE₀card
  let g : ↥PY →* alternatingGroup (Fin n) :=
    φ.comp (PY : Subgroup ↥Y).subtype
  have hg_range : g.range = (SY : Subgroup (alternatingGroup (Fin n))) := by
    rw [hSY_coe]
    ext x
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(u : ↥Y), u.2, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  have hg_inj : Function.Injective g := by
    intro u v huv
    change φ (u : ↥Y) = φ (v : ↥Y) at huv
    have hker_mem : ((v : ↥Y)⁻¹ * (u : ↥Y)) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huv]
      exact inv_mul_cancel _
    rw [hker] at hker_mem
    have hmemZ : ((((v : ↥Y)⁻¹ * (u : ↥Y)) : ↥Y) : G) ∈ Z := hker_mem
    have hmemSG : ((((v : ↥Y)⁻¹ * (u : ↥Y)) : ↥Y) : G) ∈ SG := by
      have hu := hPY_S u
      have hv := hPY_S v
      simpa using SG.mul_mem (SG.inv_mem hv) hu
    have hone : ((((v : ↥Y)⁻¹ * (u : ↥Y)) : ↥Y) : G) = 1 := by
      have hbot : ((((v : ↥Y)⁻¹ * (u : ↥Y)) : ↥Y) : G) ∈ SG ⊓ Z := ⟨hmemSG, hmemZ⟩
      rw [hSGZ] at hbot
      simpa using hbot
    apply Subtype.ext
    apply Subtype.ext
    have h1 : (v : G)⁻¹ * (u : G) = 1 := by simpa using hone
    exact (inv_mul_eq_one.mp h1).symm
  have hE₁_range : E₁ ≤ g.range := by
    rw [hg_range]
    exact hE₁_le
  let EP : Subgroup ↥PY := E₁.comap g
  have hEP_map : EP.map g = E₁ := Subgroup.map_comap_eq_self hE₁_range
  have hEP_ea : IsElemAbelian 3 EP :=
    s168e3_isElemAbelian_comap_of_injective hE₁ea g hg_inj
  have hEP_card : Nat.card EP = 3 ^ 3 := by
    have h := Subgroup.card_map_of_injective (K := EP) (f := g) hg_inj
    rw [hEP_map, hE₁card] at h
    exact h.symm
  let EY : Subgroup ↥Y := EP.map (PY : Subgroup ↥Y).subtype
  have hEY_ea : IsElemAbelian 3 EY :=
    CFSG.SectionRank.isElemAbelian_map hEP_ea (PY : Subgroup ↥Y).subtype
  have hEY_card : Nat.card EY = 3 ^ 3 := by
    show Nat.card (EP.map (PY : Subgroup ↥Y).subtype) = 3 ^ 3
    rw [Subgroup.card_map_of_injective (K := EP) (f := (PY : Subgroup ↥Y).subtype)
      (Subgroup.subtype_injective (PY : Subgroup ↥Y))]
    exact hEP_card
  have hEY_le_PY : EY ≤ (PY : Subgroup ↥Y) := by
    show EP.map (PY : Subgroup ↥Y).subtype ≤ (PY : Subgroup ↥Y)
    exact Subgroup.map_subtype_le EP
  let E : Subgroup G := EY.map Y.subtype
  have hE_ea : IsElemAbelian 3 E := CFSG.SectionRank.isElemAbelian_map hEY_ea Y.subtype
  have hE_card : Nat.card E = 3 ^ 3 := by
    show Nat.card (EY.map Y.subtype) = 3 ^ 3
    rw [Subgroup.card_map_of_injective (K := EY) (f := Y.subtype)
      (Subgroup.subtype_injective Y)]
    exact hEY_card
  have hE_le_Y : E ≤ Y := by
    show EY.map Y.subtype ≤ Y
    exact Subgroup.map_subtype_le EY
  have hE_le_M : E ≤ M := hE_le_Y.trans hYM
  have hnot_y_E : y ∉ E := fun hyE => hyY (hE_le_Y hyE)
  let PG : Subgroup G := (PY : Subgroup ↥Y).map Y.subtype
  have hE_le_PG : E ≤ PG := by
    show EY.map Y.subtype ≤ (PY : Subgroup ↥Y).map Y.subtype
    exact Subgroup.map_mono hEY_le_PY
  have hcentral : y ∈ Subgroup.centralizer (E : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxPG : x ∈ PG := hE_le_PG hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxPG
    exact hPY_comm ⟨u, hu⟩
  have h_y3 : y ^ 3 = 1 := by simpa [hy3] using pow_orderOf_eq_one y
  have hmain : 3 + 1 ≤ CFSG.Open.pRank 3 M :=
    CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer (p := 3)
      Nat.prime_three (E := E) (H := M) (k := 3) hE_ea hE_card h_y3 hnot_y_E hcentral
      hE_le_M hyM
  simpa using hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
