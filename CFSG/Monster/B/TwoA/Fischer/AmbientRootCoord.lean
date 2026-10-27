module

public import CFSG.Monster.B.TwoA.Fischer.GramMinor
public import CFSG.Monster.B.TwoA.Fischer.AdjointIntertwinerCore
public import CFSG.Monster.B.TwoA.Fischer.CertSeed
public import CFSG.Monster.B.E6.FixedE6RootRank
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3068
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

theorem jGen_mem_J
    {k : ℕ} (hk : k < 13) : jGen k ∈ J := by
  rw [J_eq_closure_jGen]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem exists_toPerm_eq_jGen
    {k : ℕ} (hk : k < 12) :
    ∃ f₀ : F₀, MulAction.toPerm f₀ = jGen k := by
  by_cases h2 : k < 2
  · exact ⟨kF (genAB k), by simp only [jGen, h2, ↓reduceIte]⟩
  · exact ⟨wBasis (k - 2), by simp only [jGen, h2, hk, ↓reduceIte]⟩

theorem jGen_eq_wF
    {k : ℕ} (hk2 : 2 ≤ k) (hk : k < 12) :
    jGen k = MulAction.toPerm (wF (bW ⟨k - 2, by omega⟩)) := by
  have h := jGen_trans ⟨k - 2, by omega⟩
  rwa [show ((⟨k - 2, by omega⟩ : Fin 10) : ℕ) + 2 = k by simp only; omega] at h

theorem gramPt_eq_symm_decY
    {V : Type*} {Y : Set V} (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) {i : ℕ}
    (hi : i < 78) :
    gramPt Y Φ i = Φ.symm (decY (Cert.basisPt i)) := by
  rw [gramPt]
  congr 1
  apply ι_injective
  apply Fin.ext
  have h := Cert.ι_jWord_o hi
  rw [h, ι_decY (h ▸ (ι (Cert.jWord (Cert.labelWord i) o)).2)]

theorem tableAdMat_add (x x' : Fin 78 → ZMod 2) :
    Cert.adMat (x + x') = Cert.adMat x + Cert.adMat x' := by
  ext r c
  simp only [Cert.adMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem tableAdMat_smul (a : ZMod 2) (x : Fin 78 → ZMod 2) :
    Cert.adMat (a • x) = a • Cert.adMat x := by
  ext r c
  simp only [Cert.adMat, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem tableBracket_add_left (x x' y : Fin 78 → ZMod 2) :
    Cert.tableBracket (x + x') y = Cert.tableBracket x y + Cert.tableBracket x' y := by
  unfold Cert.tableBracket
  rw [tableAdMat_add, Matrix.add_mulVec]

theorem tableBracket_smul_left (a : ZMod 2) (x y : Fin 78 → ZMod 2) :
    Cert.tableBracket (a • x) y = a • Cert.tableBracket x y := by
  unfold Cert.tableBracket
  rw [tableAdMat_smul, Matrix.smul_mulVec]

def tableBil : (Fin 78 → ZMod 2) →ₗ[ZMod 2] (Fin 78 → ZMod 2) →ₗ[ZMod 2] (Fin 78 → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) Cert.tableBracket tableBracket_add_left tableBracket_smul_left
    (fun _ _ _ => Matrix.mulVec_add _ _ _) (fun _ _ _ => Matrix.mulVec_smul _ _ _)

theorem tableBil_apply (x y : Fin 78 → ZMod 2) : tableBil x y = Cert.tableBracket x y :=
  LinearMap.mk₂_apply _ _ x y

theorem gramForm_add_right (x y y' : Fin 78 → ZMod 2) :
    Cert.gramForm x (y + y') = Cert.gramForm x y + Cert.gramForm x y' := by
  unfold Cert.gramForm
  rw [Matrix.mulVec_add, dotProduct_add]

theorem gramForm_smul_right (a : ZMod 2) (x y : Fin 78 → ZMod 2) :
    Cert.gramForm x (a • y) = a • Cert.gramForm x y := by
  unfold Cert.gramForm
  rw [Matrix.mulVec_smul, dotProduct_smul]

def gramBil : (Fin 78 → ZMod 2) →ₗ[ZMod 2] (Fin 78 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.mk₂ (ZMod 2) Cert.gramForm (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) gramForm_add_right gramForm_smul_right

theorem gramBil_apply (x y : Fin 78 → ZMod 2) : gramBil x y = Cert.gramForm x y :=
  LinearMap.mk₂_apply _ _ x y

theorem gramForm_single (i j : Fin 78) :
    Cert.gramForm (Pi.single i 1) (Pi.single j 1) = rowsMatrix 78 Cert.gramRowArr i j := by
  rw [Cert.gramForm, single_dotProduct, one_mul, Matrix.mulVec_single_one, Matrix.col_apply]

@[expose] def actH
    {S V : Type*} [Group S] {lab : V → S} {Y : Set V}
    (ρ : sliceGroup lab Y →* stdGroup) : sliceGroup lab Y →* Equiv.Perm fixedL :=
  actStar.comp ((SemidirectProduct.inl : stdGroup →* GStar).comp ρ)

theorem actH_apply
    {S V : Type*} [Group S] {lab : V → S} {Y : Set V}
    (ρ : sliceGroup lab Y →* stdGroup) (h : sliceGroup lab Y) (u : fixedL) :
    actH ρ h u = actStar (SemidirectProduct.inl (ρ h)) u := rfl

theorem actH_eq_gL
    {S V : Type*} [Group S] {lab : V → S} {Y : Set V}
    (ρ : sliceGroup lab Y →* stdGroup) (h : sliceGroup lab Y) (u : fixedL) :
    actH ρ h u = gL (ρ h) u :=
  actStar_inl_eq_gL _ _

abbrev stabH
    {S V : Type*} [Group S] {lab : V → S} {Y : Set V}
    (ρ : sliceGroup lab Y →* stdGroup) (u : fixedL) : Subgroup (sliceGroup lab Y) :=
  (MulAction.stabilizer (Equiv.Perm fixedL) u).comap (actH ρ)

theorem mem_stabH
    {S V : Type*} [Group S] {lab : V → S} {Y : Set V}
    {ρ : sliceGroup lab Y →* stdGroup} {u : fixedL} {g : sliceGroup lab Y} :
    g ∈ stabH ρ u ↔ actH ρ g u = u := by
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

theorem finite_fixedL :
    Finite fixedL := Finite.of_equiv _ basisL.equivFun.toEquiv.symm

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)
  {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
include H hΦ

theorem exists_conjHom_eq
    {k : ℕ} (hk : k < 13) : ∃ g : sliceGroup lab Y, H.conjHom Φ g = jGen k :=
  MonoidHom.mem_range.1 ((H.range_conjHom hΦ).symm ▸ jGen_mem_J hk)

omit hΦ in
theorem phi_act (g : sliceGroup lab Y) (v : Y) (hv : act (g : S) v ∈ Y) :
    Φ ⟨act (g : S) v, hv⟩ = H.conjHom Φ g (Φ v) := by
  rw [H.conjHom_apply]
  rfl

theorem mem_setStab_of_conjHom_eq
    {k : ℕ} (hk : k < 12) {g : sliceGroup lab Y}
    (hg : H.conjHom Φ g = jGen k) : (g : S) ∈ setStab act lab Y C := by
  obtain ⟨f₀, hf₀⟩ := exists_toPerm_eq_jGen hk
  obtain ⟨f, rfl⟩ := H.alpha_surjective f₀
  have e : g = ⟨f, f.2.1⟩ := H.conjHom_injective Φ (by rw [hg, H.conjHom_setStab hΦ, hf₀])
  rw [e]
  exact f.2

theorem mem_ptStab_of_conjHom_eq
    {k : ℕ} (hk2 : 2 ≤ k) (hk : k < 12) {g : sliceGroup lab Y}
    (hg : H.conjHom Φ g = jGen k) : (g : S) ∈ ptStab act lab Y C := by
  set r : Subgroup.closure (lab '' C) :=
    Additive.toMul (φ.symm (bW ⟨k - 2, by omega⟩)) with hr
  have hrF : (r : S) ∈ setStab act lab Y C := H.mem_setStab r
  have hα : α ⟨r, hrF⟩ = wF (bW ⟨k - 2, by omega⟩) := by
    rw [H.alpha r ⟨r, hrF⟩ 1 (mul_one (r : S)).symm
      (by rw [OneMemClass.coe_one, map_one, Equiv.Perm.one_apply])]
    simp only [QuotientGroup.mk_one, map_one, kF, mul_one, hr, ofMul_toMul,
      LinearEquiv.apply_symm_apply]
  have e : g = ⟨r, hrF.1⟩ := H.conjHom_injective Φ (by
    rw [hg, show (⟨r, hrF.1⟩ : sliceGroup lab Y) = ⟨(⟨r, hrF⟩ : setStab act lab Y C), hrF.1⟩
      from rfl, H.conjHom_setStab hΦ, hα, jGen_eq_wF hk2 hk])
  rw [e, H.ptStab_eq]
  exact r.2

theorem setStab_mem_of_gen
    (K : Subgroup (sliceGroup lab Y))
    (hK : ∀ k < 12, ∀ g, H.conjHom Φ g = jGen k → g ∈ K) (f : setStab act lab Y C) :
    (⟨f, f.2.1⟩ : sliceGroup lab Y) ∈ K := by
  have hP : ∀ k < 12, jGen k ∈ K.map (H.conjHom Φ) := fun k hk => by
    obtain ⟨g, hg⟩ := H.exists_conjHom_eq hΦ (show k < 13 by omega)
    exact Subgroup.mem_map.2 ⟨g, hK k hk g hg, hg⟩
  have hF₀ : α f ∈ (K.map (H.conjHom Φ)).comap
      (MulAction.toPermHom F₀ CFSG.Monster.B.Fischer.Y) := by
    refine F₀_mem ?_ ?_ (fun t => ?_) (α f)
    · rw [Subgroup.mem_comap, MulAction.coe_toPermHom, ← jGen_zero]
      exact hP 0 (by norm_num)
    · rw [Subgroup.mem_comap, MulAction.coe_toPermHom, ← jGen_one]
      exact hP 1 (by norm_num)
    · rw [Subgroup.mem_comap, MulAction.coe_toPermHom, ← jGen_trans t]
      exact hP _ (by omega)
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hF₀)
  rw [MulAction.coe_toPermHom, ← H.conjHom_setStab hΦ f] at e
  rw [← H.conjHom_injective Φ e]
  exact hg

theorem ptStab_mem_of_gen
    (K : Subgroup (sliceGroup lab Y))
    (hK : ∀ k, 2 ≤ k → k < 12 → ∀ g, H.conjHom Φ g = jGen k → g ∈ K) (r : ptStab act lab Y C) :
    (⟨r, r.2.1⟩ : sliceGroup lab Y) ∈ K := by
  have hP : ∀ t : Fin 10, wF (bW t) ∈ (K.map (H.conjHom Φ)).comap
      (MulAction.toPermHom F₀ CFSG.Monster.B.Fischer.Y) := fun t => by
    obtain ⟨g, hg⟩ := H.exists_conjHom_eq hΦ (show (t : ℕ) + 2 < 13 by omega)
    rw [Subgroup.mem_comap, MulAction.coe_toPermHom, ← jGen_trans t]
    exact Subgroup.mem_map.2 ⟨g, hK _ (by omega) (by omega) g hg, hg⟩
  have hr : (r : S) ∈ Subgroup.closure (lab '' C) := by
    rw [← H.ptStab_eq]
    exact r.2
  set r' : Subgroup.closure (lab '' C) := ⟨r, hr⟩
  have hrF : (r : S) ∈ setStab act lab Y C := H.mem_setStab r'
  have hα : α ⟨r, hrF⟩ = wF (φ (Additive.ofMul r')) := by
    rw [H.alpha r' ⟨r, hrF⟩ 1 (mul_one (r : S)).symm
      (by rw [OneMemClass.coe_one, map_one, Equiv.Perm.one_apply])]
    simp only [QuotientGroup.mk_one, map_one, kF, mul_one]
  obtain ⟨g, hg, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (wF_mem hP (φ (Additive.ofMul r'))))
  rw [MulAction.coe_toPermHom, ← hα, ← H.conjHom_setStab hΦ ⟨r, hrF⟩] at e
  rw [show (⟨r, r.2.1⟩ : sliceGroup lab Y) = ⟨(⟨r, hrF⟩ : setStab act lab Y C), hrF.1⟩ from rfl,
    ← H.conjHom_injective Φ e]
  exact hg

theorem ncommInd_gramPt_gramPt
    (i k : Fin 78) :
    ncommInd lab (gramPt Y Φ i) (gramPt Y Φ k) = rowsMatrix 78 Cert.gramRowArr i k := by
  obtain ⟨ψ, hψ, -, hxT, -⟩ := H.canonical_identification hΦ
  rw [← ncommQuotForm_ncommVec]
  exact H.slice.ncommQuotForm_gramPt hψ H.mem.1 (H.phi_base hΦ) hxT i k

theorem ncommInd_gramPt_eq
    {i : ℕ} (hi : i < 78) (z : Y) :
    ncommInd lab (gramPt Y Φ i) z = if (Cert.ncRow i).testBit (ι (Φ z)) then 1 else 0 := by
  obtain ⟨ψ, hψ, -, hxT, -⟩ := H.canonical_identification hΦ
  exact H.slice.ncommInd_gramPt hψ H.mem.1 (H.phi_base hΦ) hxT hi z

theorem linearIndependent_ncommVec_gramPt :
    LinearIndependent (ZMod 2) fun i : Fin 78 => ncommVec lab Y (gramPt Y Φ i) := by
  obtain ⟨ψ, hψ, -, hxT, -⟩ := H.canonical_identification hΦ
  exact H.slice.linearIndependent_gramPt hψ H.mem.1 (H.phi_base hΦ) hxT

theorem phi_lab_gramPt
    {i : ℕ} (hi : i < 78) (v : Y) (hv : act (lab (gramPt Y Φ i)) v ∈ Y) :
    Φ ⟨act (lab (gramPt Y Φ i)) v, hv⟩ = Cert.jLabel (Cert.labelWord i) (Φ v) := by
  obtain ⟨ψ, hψ, -, hxT, -⟩ := H.canonical_identification hΦ
  rw [← H.slice.psi_lab_gramPt hψ H.mem.1 (H.phi_base hΦ) hxT hi]
  exact (hψ _ v _ rfl).symm

variable (Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL)

def gramBasis :
    Module.Basis (Fin 78) (ZMod 2) (NcommQuot lab Y) :=
  basisOfLinearIndependentOfCardEqFinrank (H.linearIndependent_ncommVec_gramPt hΦ)
    (by rw [Fintype.card_fin, Ψ.finrank_eq, finrank_fixedL])

theorem gramBasis_apply
    (i : Fin 78) : H.gramBasis hΦ Ψ i = ncommVec lab Y (gramPt Y Φ i) := by
  rw [gramBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

def coordEquiv :
    (Fin 78 → ZMod 2) ≃ₗ[ZMod 2] fixedL :=
  (H.gramBasis hΦ Ψ).equivFun.symm.trans Ψ

theorem coordEquiv_apply
    (c : Fin 78 → ZMod 2) :
    H.coordEquiv hΦ Ψ c = ∑ i, c i • Ψ (ncommVec lab Y (gramPt Y Φ i)) := by
  rw [coordEquiv, LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul, gramBasis_apply]

theorem coordEquiv_single
    (i : Fin 78) :
    H.coordEquiv hΦ Ψ (Pi.single i 1) = Ψ (ncommVec lab Y (gramPt Y Φ i)) := by
  rw [coordEquiv_apply, Finset.sum_eq_single i
    (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]

include Ψ in
theorem ncommVec_eq_sum
    (y : Y) :
    ncommVec lab Y y = ∑ i : Fin 78, toVecD 78 (Cert.labelCoord (ι (Φ y))) i •
      ncommVec lab Y (gramPt Y Φ i) := by
  set c := toVecD 78 (Cert.labelCoord (ι (Φ y))) with hc
  set w := (∑ i : Fin 78, c i • ncommVec lab Y (gramPt Y Φ i)) - ncommVec lab Y y with hw
  have hk : ∀ k : Fin 78, ncommQuotForm lab Y (ncommVec lab Y (gramPt Y Φ k)) w = 0 := by
    intro k
    have hcert := congrFun (Cert.fischer_label_coordinates_certificate.2 (Φ y)) k
    simp only [Matrix.mulVec, dotProduct] at hcert
    rw [hw, map_sub, map_sum]
    simp only [map_smul, smul_eq_mul, ncommQuotForm_ncommVec, H.ncommInd_gramPt_gramPt hΦ,
      H.ncommInd_gramPt_eq hΦ k.2]
    rw [← hcert, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hall : ∀ u, ncommQuotForm lab Y u w = 0 := by
    intro u
    rw [← (H.gramBasis hΦ Ψ).sum_repr u, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [map_smul, LinearMap.smul_apply, gramBasis_apply, hk, smul_zero]
  exact (sub_eq_zero.1 ((ncommQuotForm_nondegenerate lab Y).2 w hall)).symm

variable {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
  (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
  {Ψ} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)

include hΨ in
theorem adjVec_eq_coordEquiv
    (y : Y) :
    adjVec ρ y = H.coordEquiv hΦ Ψ (toVecD 78 (Cert.labelCoord (ι (Φ y)))) := by
  rw [← hΨ, coordEquiv_apply, H.ncommVec_eq_sum hΦ Ψ y, map_sum]
  simp only [map_smul]

include hΨ in
theorem coordEquiv_single_eq
    (i : Fin 78) :
    H.coordEquiv hΦ Ψ (Pi.single i 1) = adjVec ρ (gramPt Y Φ i) := by
  rw [coordEquiv_single, hΨ]

include hroot hΨ in
theorem gL_coordEquiv
    (g : sliceGroup lab Y) (M : Matrix (Fin 78) (Fin 78) (ZMod 2))
    (hM : ∀ i : Fin 78, M *ᵥ Pi.single i 1 =
      toVecD 78 (Cert.labelCoord (ι (H.conjHom Φ g (Φ (gramPt Y Φ i)))))) (c : Fin 78 → ZMod 2) :
    gL (ρ g) (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ (M *ᵥ c) := by
  have key : (gL (ρ g)).comp (H.coordEquiv hΦ Ψ).toLinearMap =
      (H.coordEquiv hΦ Ψ).toLinearMap.comp (Matrix.mulVecLin M) := by
    refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe,
      Matrix.mulVecLin_apply]
    have hmem : act (g : S) (gramPt Y Φ i) ∈ Y := H.slice.mapsTo _ g.2 _ (gramPt Y Φ i).2
    rw [H.coordEquiv_single_eq hΦ hΨ, ← H.slice.adjVec_act hroot g _ hmem,
      H.adjVec_eq_coordEquiv hΦ hΨ, hM i, H.phi_act g _ hmem]
  exact LinearMap.congr_fun key c

include hroot hΨ in
theorem gL_coordEquiv_fMat
    {k : ℕ} (hk : k < 12) {g : sliceGroup lab Y}
    (hg : H.conjHom Φ g = jGen k) (c : Fin 78 → ZMod 2) :
    gL (ρ g) (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ (Cert.fMat k *ᵥ c) :=
  H.gL_coordEquiv hΦ hroot hΨ g _ (fun i => by
    rw [hg]
    exact Cert.fischer_clique_fixed_certificate.1 k hk i _ (ι_gramPt Φ i.2)) c

include hroot hΨ in
theorem gL_coordEquiv_fourMat
    {k : ℕ} (hk : k < 4) {g : sliceGroup lab Y}
    (hg : H.conjHom Φ g = jGen (Cert.fourGen k)) (c : Fin 78 → ZMod 2) :
    gL (ρ g) (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ (Cert.fourMat k *ᵥ c) :=
  H.gL_coordEquiv hΦ hroot hΨ g _ (fun i => by
    rw [hg]
    exact Cert.fischer_seed_certificate.2.1 k hk i _ (ι_gramPt Φ i.2)) c

include hρ hroot hΨ in
theorem bracketL_adjVec_gramPt
    (i j : Fin 78) :
    bracketL (adjVec ρ (gramPt Y Φ i)) (adjVec ρ (gramPt Y Φ j)) =
      H.coordEquiv hΦ Ψ (toVecD 78 (Cert.bTable i j)) := by
  have hb := Cert.table_binding i.2 j.2 (Φ (gramPt Y Φ j)) (ι_gramPt Φ j.2)
  have hmem : act (lab (gramPt Y Φ i)) (gramPt Y Φ j) ∈ Y :=
    H.slice.mapsTo _ (lab_mem_sliceGroup (gramPt Y Φ i).2) _ (gramPt Y Φ j).2
  have hL := H.phi_lab_gramPt hΦ i.2 _ hmem
  rw [H.slice.bracketL_adjVec hρ hroot]
  by_cases hc : Commute (lab (gramPt Y Φ i)) (lab (gramPt Y Φ j))
  · rw [ncommProd_single_of_commute act lab Y hc, map_zero]
    have hfix : act (lab (gramPt Y Φ i)) (gramPt Y Φ j) = gramPt Y Φ j :=
      (H.slice.act_lab_eq_iff (gramPt Y Φ i).2 (gramPt Y Φ j).2).2 hc
    have h1 : Cert.jLabel (Cert.labelWord i) (Φ (gramPt Y Φ j)) = Φ (gramPt Y Φ j) := by
      rw [← hL]
      exact congrArg Φ (Subtype.ext hfix)
    rw [hb.1 h1, map_zero]
  · rw [ncommProd_single_of_not_commute act lab Y hc hmem, map_add, map_add, adjMap_single_one,
      adjMap_single_one, adjMap_single_one]
    have hne : Cert.jLabel (Cert.labelWord i) (Φ (gramPt Y Φ j)) ≠ Φ (gramPt Y Φ j) := by
      rw [← hL]
      intro h
      apply hc
      rw [← H.slice.act_lab_eq_iff (gramPt Y Φ i).2 (gramPt Y Φ j).2]
      exact congrArg Subtype.val (Φ.injective h)
    rw [hb.2 hne, map_add, map_add, H.adjVec_eq_coordEquiv hΦ hΨ (gramPt Y Φ i),
      H.adjVec_eq_coordEquiv hΦ hΨ (gramPt Y Φ j), H.adjVec_eq_coordEquiv hΦ hΨ ⟨_, hmem⟩,
      ι_gramPt Φ i.2, ι_gramPt Φ j.2, hL]

include hρ hroot hΨ in
theorem bracketL_coordEquiv
    (c d : Fin 78 → ZMod 2) :
    bracketL (H.coordEquiv hΦ Ψ c) (H.coordEquiv hΦ Ψ d) =
      H.coordEquiv hΦ Ψ (Cert.tableBracket c d) := by
  have key : bracketBil.compl₁₂ (H.coordEquiv hΦ Ψ).toLinearMap (H.coordEquiv hΦ Ψ).toLinearMap =
      tableBil.compr₂ (H.coordEquiv hΦ Ψ).toLinearMap := by
    refine LinearMap.ext_basis (Pi.basisFun (ZMod 2) (Fin 78)) (Pi.basisFun (ZMod 2) (Fin 78))
      fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, Pi.basisFun_apply,
      LinearEquiv.coe_coe, bracketBil_apply, tableBil_apply]
    rw [H.coordEquiv_single_eq hΦ hΨ, H.coordEquiv_single_eq hΦ hΨ,
      H.bracketL_adjVec_gramPt hΦ hρ hroot hΨ, Cert.tableBracket_single]
  exact LinearMap.congr_fun₂ key c d

include hρ hroot hΨ in
theorem formL_coordEquiv
    (c d : Fin 78 → ZMod 2) :
    formL (H.coordEquiv hΦ Ψ c) (H.coordEquiv hΦ Ψ d) = Cert.gramForm c d := by
  have key : formL.compl₁₂ (H.coordEquiv hΦ Ψ).toLinearMap (H.coordEquiv hΦ Ψ).toLinearMap =
      gramBil := by
    refine LinearMap.ext_basis (Pi.basisFun (ZMod 2) (Fin 78)) (Pi.basisFun (ZMod 2) (Fin 78))
      fun i j => ?_
    simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, LinearEquiv.coe_coe, gramBil_apply]
    rw [H.coordEquiv_single_eq hΦ hΨ, H.coordEquiv_single_eq hΦ hΨ,
      H.slice.formL_adjVec hρ hroot, H.ncommInd_gramPt_gramPt hΦ, gramForm_single]
  exact LinearMap.congr_fun₂ key c d

include hρ hroot hΨ in
theorem finrank_range_adL_coordEquiv
    (c : Fin 78 → ZMod 2) :
    Module.finrank (ZMod 2) (LinearMap.range (adL (H.coordEquiv hΦ Ψ c))) =
      (Cert.adMat c).rank := by
  have key : (adL (H.coordEquiv hΦ Ψ c)).comp (H.coordEquiv hΦ Ψ).toLinearMap =
      (H.coordEquiv hΦ Ψ).toLinearMap.comp (Cert.adMat c).mulVecLin := by
    refine LinearMap.ext fun d => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    exact H.bracketL_coordEquiv hΦ hρ hroot hΨ c d
  rw [Matrix.rank, ← LinearEquiv.finrank_map_eq (H.coordEquiv hΦ Ψ), ← LinearMap.range_comp,
    ← key, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

include hroot hΨ in
theorem fixed_setStab_iff
    (c : Fin 78 → ZMod 2) :
    (∀ f : setStab act lab Y C, actH ρ ⟨f, f.2.1⟩ (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ c) ↔
      ∀ k < 12, Cert.fMat k *ᵥ c = c := by
  constructor
  · intro h k hk
    obtain ⟨g, hg⟩ := H.exists_conjHom_eq hΦ (show k < 13 by omega)
    have h1 := h ⟨g, H.mem_setStab_of_conjHom_eq hΦ hk hg⟩
    rw [actH_eq_gL, show (⟨((⟨g, H.mem_setStab_of_conjHom_eq hΦ hk hg⟩ :
        setStab act lab Y C) : S), _⟩ : sliceGroup lab Y) = g from rfl,
      H.gL_coordEquiv_fMat hΦ hroot hΨ hk hg] at h1
    exact (H.coordEquiv hΦ Ψ).injective h1
  · intro h f
    refine mem_stabH.1 (H.setStab_mem_of_gen hΦ _ (fun k hk g hg => mem_stabH.2 ?_) f)
    rw [actH_eq_gL, H.gL_coordEquiv_fMat hΦ hroot hΨ hk hg, h k hk]

include hroot hΨ in
theorem fixed_ptStab_iff
    (c : Fin 78 → ZMod 2) :
    (∀ r : ptStab act lab Y C, actH ρ ⟨r, r.2.1⟩ (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ c) ↔
      ∀ k, 2 ≤ k → k < 12 → Cert.fMat k *ᵥ c = c := by
  constructor
  · intro h k hk2 hk
    obtain ⟨g, hg⟩ := H.exists_conjHom_eq hΦ (show k < 13 by omega)
    have h1 := h ⟨g, H.mem_ptStab_of_conjHom_eq hΦ hk2 hk hg⟩
    rw [actH_eq_gL, show (⟨((⟨g, H.mem_ptStab_of_conjHom_eq hΦ hk2 hk hg⟩ :
        ptStab act lab Y C) : S), _⟩ : sliceGroup lab Y) = g from rfl,
      H.gL_coordEquiv_fMat hΦ hroot hΨ hk hg] at h1
    exact (H.coordEquiv hΦ Ψ).injective h1
  · intro h r
    refine mem_stabH.1 (H.ptStab_mem_of_gen hΦ _ (fun k hk2 hk g hg => mem_stabH.2 ?_) r)
    rw [actH_eq_gL, H.gL_coordEquiv_fMat hΦ hroot hΨ hk hg, h k hk2 hk]

end FullIntertwinerHyp

end CFSG.Monster.B.TwoA.Fischer
