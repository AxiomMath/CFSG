module

public import CFSG.Quasithin.Background.SimsG4Defs
public import CFSG.Quasithin.Background.SimsG45Basis
public import CFSG.Quasithin.Vol2.Ch3E213MG41A
import CFSG.Quasithin.Background.SimsG45Transv
import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Vol2.Ch3E213MG41D2

public section

namespace CFSG.Quasithin.SimsG4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat)
open CFSG.Quasithin.Ch3E213M (natAct spBil subfieldSp subfieldSpEquiv)
open CFSG.Quasithin.Ch3E213M.G41 (trv act_trv conj_trv)

section Coordinates

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem spGroup_eq_isometryGroup (B : LinearMap.BilinForm F V) :
    spGroup B = CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryGroup B :=
  Subgroup.ext fun g =>
    (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.mem_isometryGroup_iff B g).symm

theorem exists_isSympBasis [CharP F 2] (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4) :
    ∃ b : Module.Basis (Fin 4) F V, IsSympBasis B b := by
  haveI : FiniteDimensional F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  have halt' : LinearMap.IsAlt B := halt
  have hnd' : B.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => halt'.eq_iff.mp (hy x)⟩
  have hsymm : ∀ x y, B y x = B x y := fun x y => by rw [← halt'.neg x y, CharTwo.neg_eq]
  obtain ⟨m, c, hm, h11, h22, h12⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      B halt' hnd'
  obtain rfl : m = 2 := by omega
  have h21 : ∀ i j, B (c (Sum.inr i)) (c (Sum.inl j)) = if j = i then 1 else 0 := fun i j => by
    rw [hsymm, h12]
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → V,
      e = ![c (Sum.inl 0), c (Sum.inl 1), c (Sum.inr 1), c (Sum.inr 0)] := ⟨_, rfl⟩
  have hgram : ∀ i j, B (e i) (e j) = if i.val + j.val = 3 then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he, h11, h22, h12, h21]
  have hli : LinearIndependent F e := SimsG45.linearIndependent_of_antidiag B hgram
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [hdim]), fun i j => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact hgram i j

@[expose] noncomputable def spCoord (B : LinearMap.BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : IsSympBasis B b) : spGroup B ≃* antiSp F :=
  (MulEquiv.subgroupCongr (spGroup_eq_isometryGroup B)).trans (SimsG45.isoAntiSp B b hb)

variable (B : LinearMap.BilinForm F V) (b : Module.Basis (Fin 4) F V)

theorem glMat_spCoord (hb : IsSympBasis B b) (g : spGroup B) :
    glMat (spCoord B b hb g : GL (Fin 4) F) =
      LinearMap.toMatrix b b ((g : V ≃ₗ[F] V) : V →ₗ[F] V) :=
  rfl

theorem natAct_spCoord (hb : IsSympBasis B b) (g : spGroup B) (x : V) :
    natAct (spCoord B b hb g) (b.equivFun x) = b.equivFun ((g : V ≃ₗ[F] V) x) :=
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_mulVec b g.1 x

theorem natAct_spCoord_symm (hb : IsSympBasis B b) (A : antiSp F) (x : V) :
    natAct A (b.equivFun x) = b.equivFun ((((spCoord B b hb).symm A : spGroup B) :
      V ≃ₗ[F] V) x) := by
  conv_lhs => rw [← (spCoord B b hb).apply_symm_apply A]
  exact natAct_spCoord B b hb _ x

theorem spBil_equivFun (hb : IsSympBasis B b) (x y : V) :
    spBil (b.equivFun x) (b.equivFun y) = B x y := by
  conv_rhs => rw [← Matrix.toBilin_toMatrix b B]
  rw [SimsG45.toMatrix_eq_minorJ B b hb, Matrix.toBilin_apply]
  exact Matrix.toBilin'_apply _ _ _

theorem spCoord_mem_subfieldSp_iff (hb : IsSympBasis B b) (F₀ : Subfield F) (g : spGroup B) :
    spCoord B b hb g ∈ subfieldSp F₀ ↔ (g : V ≃ₗ[F] V) ∈ subfieldSpOf b F₀ :=
  Iff.rfl

theorem isTransv_of_apply (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    {w : V} (hw : w ≠ 0) {c : F} (hc : c ≠ 0) (t : V ≃ₗ[F] V)
    (ht : ∀ x, t x = x + (c * B x w) • w) : IsTransv t := by
  have hsub : ∀ x, ((t : V →ₗ[F] V) - LinearMap.id : V →ₗ[F] V) x = (c * B x w) • w := fun x => by
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, ht, LinearMap.id_apply, add_sub_cancel_left]
  refine ⟨?_, ?_⟩
  · have hR : LinearMap.range ((t : V →ₗ[F] V) - LinearMap.id) = F ∙ w := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [hsub]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        obtain ⟨v, hv⟩ := SimsG45.exists_pair_eq_one B halt hnd hw
        refine LinearMap.mem_range.mpr ⟨c⁻¹ • v, ?_⟩
        rw [hsub, LinearMap.map_smul₂, smul_eq_mul, hv, mul_one, mul_inv_cancel₀ hc, one_smul]
    rw [hR, finrank_span_singleton hw]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hsub, hsub, LinearMap.map_smul₂, smul_eq_mul, halt w, mul_zero,
      mul_zero, zero_smul, LinearMap.zero_apply]

theorem spCoord_symm_trv_apply [CharP F 2] (hb : IsSympBasis B b) (v : Fin 4 → F) (c : F)
    (x : V) :
    (((spCoord B b hb).symm (trv v c) : spGroup B) : V ≃ₗ[F] V) x =
      x + (c * B x (b.equivFun.symm v)) • b.equivFun.symm v := by
  apply b.equivFun.injective
  rw [← natAct_spCoord_symm B b hb, act_trv, map_add, map_smul, LinearEquiv.apply_symm_apply,
    ← spBil_equivFun B b hb, LinearEquiv.apply_symm_apply]

end Coordinates

section Subfield

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem trv_mem_subfieldSp [CharP F 2] (F₀ : Subfield F) (v : Fin 4 → F₀) (c : F₀) :
    trv (fun i => (v i : F)) (c : F) ∈ subfieldSp F₀ := by
  rw [← Ch3E213M.range_subAntiSp, ← Ch3E213M.G41.subAntiSp_trv]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem exists_card_subfield [Finite F] [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    (F₀ : Subfield F) : ∃ k : ℕ, 0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k := by
  letI := Fintype.ofFinite F₀
  obtain ⟨k, -, hk⟩ := FiniteField.card F₀ 2
  have hk' : Nat.card F₀ = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
  have h := Module.natCard_eq_pow_finrank (K := F₀) (V := F)
  rw [hn, hk', ← pow_mul] at h
  exact ⟨k, k.pos, ⟨_, Nat.pow_right_injective le_rfl h⟩, hk'⟩

variable (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) (b : Module.Basis (Fin 4) F V)
  (F₀ : Subfield F)

theorem transvGen_eq_self_of_subfield [CharP F 2] (hb : IsSympBasis B b) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hG : ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) :
    transvGen G₀ = G₀ := by
  refine le_antisymm (transvGen_le G₀) fun g hg => ?_
  obtain ⟨hgSp, hgF⟩ := (hG g).mp hg
  let f : antiSp F →* (V ≃ₗ[F] V) := (spGroup B).subtype.comp (spCoord B b hb).symm.toMonoidHom
  have hf : f (spCoord B b hb ⟨g, hgSp⟩) = g := by simp [f]
  have hcl := Ch3E213M.G41.subfieldSp_le_closure F₀
    ((spCoord_mem_subfieldSp_iff B b hb F₀ ⟨g, hgSp⟩).mpr hgF)
  rw [← hf]
  have hmap := Subgroup.mem_map_of_mem f hcl
  rw [MonoidHom.map_closure] at hmap
  refine (Subgroup.closure_le _).mpr ?_ hmap
  rintro _ ⟨_, ⟨v, c, rfl⟩, rfl⟩
  by_cases hc : (c : F) = 0
  · rw [hc, Ch3E213M.G41.trv_zero, map_one]
    exact (transvGen G₀).one_mem
  by_cases hv : (fun i => (v i : F)) = 0
  · rw [hv, Ch3E213M.G41.trv_zero_left, map_one]
    exact (transvGen G₀).one_mem
  refine Subgroup.subset_closure ⟨(hG _).mpr ⟨((spCoord B b hb).symm _).2, ?_⟩, ?_⟩
  · change (((spCoord B b hb).symm (trv (fun i => (v i : F)) (c : F)) : spGroup B) :
      V ≃ₗ[F] V) ∈ subfieldSpOf b F₀
    rw [← spCoord_mem_subfieldSp_iff B b hb F₀, MulEquiv.apply_symm_apply]
    exact trv_mem_subfieldSp F₀ v c
  · refine isTransv_of_apply B halt hnd (w := b.equivFun.symm fun i => (v i : F)) ?_ hc _
      (spCoord_symm_trv_apply B b hb _ _)
    intro h0
    apply hv
    rw [← b.equivFun.apply_symm_apply fun i => (v i : F), h0, map_zero]

theorem nonempty_mulEquiv_symplectic [Finite F] [CharP F 2] (hb : IsSympBasis B b)
    (hG : ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) {k : ℕ} (hk : 0 < k)
    (hcard : Nat.card F₀ = 2 ^ k) :
    Nonempty (↥G₀ ≃* ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 k))) := by
  let f : antiSp F →* (V ≃ₗ[F] V) := (spGroup B).subtype.comp (spCoord B b hb).symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp (spCoord B b hb).symm.injective
  have hGmap : G₀ = (subfieldSp F₀).map f := by
    ext g
    rw [hG, Subgroup.mem_map]
    constructor
    · rintro ⟨hgSp, hgF⟩
      exact ⟨spCoord B b hb ⟨g, hgSp⟩, (spCoord_mem_subfieldSp_iff B b hb F₀ _).mpr hgF,
        by simp [f]⟩
    · rintro ⟨A, hA, rfl⟩
      refine ⟨((spCoord B b hb).symm A).2, ?_⟩
      change (((spCoord B b hb).symm A : spGroup B) : V ≃ₗ[F] V) ∈ subfieldSpOf b F₀
      rw [← spCoord_mem_subfieldSp_iff B b hb F₀, MulEquiv.apply_symm_apply]
      exact hA
  letI := Fintype.ofFinite F₀
  letI := Fintype.ofFinite (GaloisField 2 k)
  have hcardeq : Fintype.card F₀ = Fintype.card (GaloisField 2 k) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard, GaloisField.card 2 k hk.ne']
  let ρ : F₀ ≃+* GaloisField 2 k := FiniteField.ringEquivOfCardEq hcardeq
  exact ⟨(MulEquiv.subgroupCongr hGmap).trans <|
    (Subgroup.equivMapOfInjective _ f hf).symm.trans <|
    (subfieldSpEquiv F₀).symm.trans <|
    (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.antiSpEquiv F₀).trans <|
    (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic).trans <|
    (TauCeti.GLSymplectic.mulEquivSymplecticGroup (Fin 2) F₀).trans
    { toFun := fun A => ⟨(A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F₀).map ρ,
        SymplecticGroup.map_mem A.2 ρ⟩
      invFun := fun A => ⟨(A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (GaloisField 2 k)).map ρ.symm,
        SymplecticGroup.map_mem A.2 ρ.symm⟩
      left_inv := fun A => Subtype.ext (by ext i j; simp)
      right_inv := fun A => Subtype.ext (by ext i j; simp)
      map_mul' := fun A A' => Subtype.ext (by simp [Matrix.map_mul]) }⟩

end Subfield

theorem case1_of_subfield {F : Type} [Field F] [Finite F] [CharP F 2] (n : ℕ)
    (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F)
    (hb : IsSympBasis B b)
    (hG : ∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) :
    G41Case1 n B G₀ := by
  obtain ⟨k, hk, hkn, hcard⟩ := exists_card_subfield n hn F₀
  exact ⟨transvGen_eq_self_of_subfield B G₀ b F₀ hb halt hnd hG, b, F₀, k, hb, hk, hkn, hcard, hG,
    nonempty_mulEquiv_symplectic B G₀ b F₀ hb hG hk hcard⟩

end CFSG.Quasithin.SimsG4
