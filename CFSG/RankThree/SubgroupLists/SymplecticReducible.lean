module

public import CFSG.RankThree.SubgroupLists.CliffordPrime
public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Walter.W67.CentralExt
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Certificates.Certificate43
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.SubgroupLists

open Matrix
open scoped MatrixGroups

section Sections

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def sectionMap (A C : Submodule K (σ → K)) (g : GL σ K)
    (hC : ∀ c ∈ C, Matrix.toLin' (g : Matrix σ σ K) c ∈ C)
    (hA : ∀ a ∈ A, Matrix.toLin' (g : Matrix σ σ K) a ∈ A) :
    Module.End K (C ⧸ A.comap C.subtype) :=
  (A.comap C.subtype).mapQ (A.comap C.subtype) ((Matrix.toLin' (g : Matrix σ σ K)).restrict hC)
    (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.coe_restrict_apply] at hx ⊢
      exact hA _ hx)

theorem sectionMap_mk (A C : Submodule K (σ → K)) (g : GL σ K)
    (hC : ∀ c ∈ C, Matrix.toLin' (g : Matrix σ σ K) c ∈ C)
    (hA : ∀ a ∈ A, Matrix.toLin' (g : Matrix σ σ K) a ∈ A) (x : C) :
    sectionMap A C g hC hA (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨(g : Matrix σ σ K) *ᵥ (x : σ → K), by
        simpa [Matrix.toLin'_apply] using hC x x.2⟩ := by
  simp only [sectionMap, Submodule.mapQ_apply]
  rfl

noncomputable def sectionEnd (G : Subgroup (GL σ K)) {A C : Submodule K (σ → K)}
    (hA : IsInvariant G A) (hC : IsInvariant G C) :
    G →* Module.End K (C ⧸ A.comap C.subtype) where
  toFun g := sectionMap A C g (fun c hc => by simpa [Matrix.toLin'_apply] using hC g g.2 c hc)
    (fun a ha => by simpa [Matrix.toLin'_apply] using hA g g.2 a ha)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, sectionMap_mk,
      OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, Module.End.one_apply]
  map_mul' g h := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, sectionMap_mk,
      Subgroup.coe_mul, Module.End.mul_apply]
    congr 2
    rw [gl_mulVec_mul]

theorem sectionEnd_mk (G : Subgroup (GL σ K)) {A C : Submodule K (σ → K)}
    (hA : IsInvariant G A) (hC : IsInvariant G C) (g : G) (x : C) :
    sectionEnd G hA hC g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨((g : GL σ K) : Matrix σ σ K) *ᵥ (x : σ → K), hC g g.2 x x.2⟩ :=
  sectionMap_mk A C g (fun c hc => by simpa [Matrix.toLin'_apply] using hC g g.2 c hc)
    (fun a ha => by simpa [Matrix.toLin'_apply] using hA g g.2 a ha) x

theorem sectionEnd_eq_one_iff (G : Subgroup (GL σ K)) {A C : Submodule K (σ → K)}
    (hA : IsInvariant G A) (hC : IsInvariant G C) (g : G) :
    sectionEnd G hA hC g = 1 ↔
      ∀ c ∈ C, ((g : GL σ K) : Matrix σ σ K) *ᵥ c - c ∈ A := by
  constructor
  · intro h c hc
    have := congrArg (fun f => f (Submodule.Quotient.mk (⟨c, hc⟩ : C))) h
    simp only [sectionEnd_mk, Module.End.one_apply, Submodule.Quotient.eq] at this
    simpa using this
  · intro h
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, sectionEnd_mk,
      Module.End.one_apply]
    rw [Submodule.Quotient.eq]
    simpa using h x x.2

noncomputable def sectionRep (G : Subgroup (GL σ K)) {A C : Submodule K (σ → K)}
    (hA : IsInvariant G A) (hC : IsInvariant G C) {m : ℕ}
    (b : Module.Basis (Fin m) K (C ⧸ A.comap C.subtype)) : G →* GL (Fin m) K :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp (sectionEnd G hA hC).toHomUnits

theorem sectionRep_eq_one_iff (G : Subgroup (GL σ K)) {A C : Submodule K (σ → K)}
    (hA : IsInvariant G A) (hC : IsInvariant G C) {m : ℕ}
    (b : Module.Basis (Fin m) K (C ⧸ A.comap C.subtype)) (g : G) :
    sectionRep G hA hC b g = 1 ↔ ∀ c ∈ C, ((g : GL σ K) : Matrix σ σ K) *ᵥ c - c ∈ A := by
  rw [← sectionEnd_eq_one_iff G hA hC g]
  constructor
  · intro h
    have h' := congrArg Units.val h
    simp only [sectionRep, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      MulEquiv.coe_toMonoidHom, MonoidHom.coe_toHomUnits, Units.val_one] at h'
    exact (LinearMap.toMatrixAlgEquiv b).injective (by rw [map_one]; exact h')
  · intro h
    apply Units.ext
    simp only [sectionRep, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      MonoidHom.coe_toHomUnits, Units.val_one]
    rw [h]
    exact map_one (LinearMap.toMatrixAlgEquiv b)

end Sections

theorem pow_prime_sq_eq_one_of_unipotent {p : ℕ} [Fact p.Prime] {σ : Type*} [Fintype σ]
    [DecidableEq σ] [Nonempty σ] (g : GL σ (ZMod p))
    (h : ((g : Matrix σ σ (ZMod p)) - 1) ^ 4 = 0) : g ^ (p ^ 2) = 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h4 : 4 ≤ p ^ 2 := by nlinarith
  have hpow : ((g : Matrix σ σ (ZMod p)) - 1) ^ (p ^ 2) = 0 := by
    rw [← Nat.add_sub_cancel' h4, pow_add, h, zero_mul]
  rw [sub_pow_char_pow_of_commute p 2 (Commute.one_right _), one_pow, sub_eq_zero] at hpow
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hpow, Units.val_one]


section SymplecticForm

variable {K : Type} [Field K] {n : ℕ}

abbrev spGram (n : ℕ) (K : Type) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] noncomputable def spForm (n : ℕ) (K : Type) [Field K] :
    LinearMap.BilinForm K (Fin n ⊕ Fin n → K) :=
  Matrix.toBilin' (spGram n K)

theorem spForm_apply (x y : Fin n ⊕ Fin n → K) :
    spForm n K x y = ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  rw [spForm, Matrix.toBilin'_apply']
  simp [dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.one_apply, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]

theorem spForm_self (x : Fin n ⊕ Fin n → K) : spForm n K x x = 0 := by
  rw [spForm_apply]
  exact Finset.sum_eq_zero fun i _ => by ring

theorem spForm_isRefl : (spForm n K).IsRefl :=
  LinearMap.BilinForm.IsAlt.isRefl spForm_self

theorem spForm_separatingLeft : LinearMap.SeparatingLeft (spForm n K) := by
  intro x hx
  funext i
  rcases i with i | i
  · have h := hx (Pi.single (Sum.inr i) 1)
    rw [spForm_apply] at h
    simpa [Pi.single_apply] using h
  · have h := hx (Pi.single (Sum.inl i) 1)
    rw [spForm_apply] at h
    simpa [Pi.single_apply] using h

theorem spForm_nondegenerate : (spForm n K).Nondegenerate :=
  ⟨spForm_separatingLeft, fun y hy => spForm_separatingLeft y fun x => spForm_isRefl _ _ (hy x)⟩

theorem transpose_mul_spGram_mul {A : GL (Fin n ⊕ Fin n) K}
    (hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSp n K) :
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * spGram n K * A = spGram n K := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic] at hA
  exact (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mpr
    (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp hA)

theorem spForm_mulVec {A : GL (Fin n ⊕ Fin n) K}
    (hA : A ∈ CFSG.Assembly.LowTwoRank.StatedSp n K) (x y : Fin n ⊕ Fin n → K) :
    spForm n K ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ x)
      ((A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ y) = spForm n K x y := by
  rw [spForm, Matrix.toBilin'_apply', Matrix.toBilin'_apply', dotProduct_comm,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, transpose_mul_spGram_mul hA]

noncomputable abbrev orth (U : Submodule K (Fin n ⊕ Fin n → K)) :
    Submodule K (Fin n ⊕ Fin n → K) :=
  (spForm n K).orthogonal U

theorem mem_orth {U : Submodule K (Fin n ⊕ Fin n → K)} {v : Fin n ⊕ Fin n → K} :
    v ∈ orth U ↔ ∀ u ∈ U, spForm n K u v = 0 :=
  LinearMap.BilinForm.mem_orthogonal_iff

theorem finrank_orth (U : Submodule K (Fin n ⊕ Fin n → K)) :
    Module.finrank K (orth U) = 2 * n - Module.finrank K U := by
  rw [orth, LinearMap.BilinForm.finrank_orthogonal spForm_nondegenerate,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]

theorem orth_orth (U : Submodule K (Fin n ⊕ Fin n → K)) : orth (orth U) = U :=
  LinearMap.BilinForm.orthogonal_orthogonal spForm_nondegenerate spForm_isRefl U

theorem sup_orth_eq_top {U : Submodule K (Fin n ⊕ Fin n → K)} (h : U ⊓ orth U = ⊥) :
    U ⊔ orth U = ⊤ :=
  ((LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint spForm_isRefl).mpr
    (disjoint_iff.mpr h)).sup_eq_top

theorem isInvariant_orth {G : Subgroup (GL (Fin n ⊕ Fin n) K)}
    (hGS : G ≤ CFSG.Assembly.LowTwoRank.StatedSp n K) {U : Submodule K (Fin n ⊕ Fin n → K)}
    (hU : IsInvariant G U) : IsInvariant G (orth U) := by
  intro g hg v hv
  rw [mem_orth] at hv ⊢
  intro u hu
  have hu' : ((g⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix _ _ K) *ᵥ u ∈ U := hU _ (G.inv_mem hg) u hu
  rw [← gl_mulVec_inv_mulVec g u, spForm_mulVec (hGS hg)]
  exact hv _ hu'

end SymplecticForm


section Quasisimple

theorem quasisimple_gl2_of_unipotent_kernel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type*}
    [Group G] [Finite G] (hG : CFSG.IsQuasisimple G) (ρ : G →* GL (Fin 2) (ZMod p))
    (hker : ∀ g, ρ g = 1 → g ^ (p ^ 2) = 1) :
    Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) := by
  classical
  have hnt : Nontrivial G := CFSG.LocalCores.isQuasisimple_nontrivial hG
  obtain ⟨hperf, hsimple, a, b, hab⟩ := hG
  have hMp : IsPGroup p ρ.ker := fun g => ⟨2, Subtype.ext (hker g g.2)⟩
  have hMc : ρ.ker ≤ Subgroup.center G := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups ⟨hperf, hsimple, a, b, hab⟩
        ρ.normal_ker with h | h
    · exfalso
      have hGp : IsPGroup p G := fun g => ⟨2, hker g (by
        have : g ∈ ρ.ker := h ▸ Subgroup.mem_top g
        exact this)⟩
      have hQp : IsPGroup p (G ⧸ Subgroup.center G) := hGp.to_quotient _
      have : Nontrivial (G ⧸ Subgroup.center G) := ⟨⟨a * b, b * a, hab⟩⟩
      have hZ := hQp.center_nontrivial
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center (G ⧸ Subgroup.center G)) with h0 | h0
      · rw [h0] at hZ
        exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hZ
      · have ha : a ∈ Subgroup.center (G ⧸ Subgroup.center G) := h0 ▸ Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp ha b).symm
    · exact h
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPab : IsMulCommutative (P : Subgroup G) := by
    let f : (P : Subgroup G) →* (P : Subgroup G).map ρ := ρ.subgroupMap (P : Subgroup G)
    have hfker : f.ker ≤ Subgroup.center (P : Subgroup G) := by
      intro x hx
      have hx' : ρ x = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        simpa [f] using this
      have hxc : (x : G) ∈ Subgroup.center G := hMc hx'
      rw [Subgroup.mem_center_iff] at hxc ⊢
      intro y
      exact Subtype.ext (hxc y)
    have hHp : IsPGroup p ((P : Subgroup G).map ρ) := P.isPGroup'.map ρ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
    have hdvd : p ^ k ∣ Nat.card (GL (Fin 2) (ZMod p)) :=
      hk ▸ Subgroup.card_subgroup_dvd_card _
    have hk1 : k ≤ 1 := by
      by_contra hk2
      exact not_sq_dvd_card_GL_two (pow_dvd_pow p (by omega) |>.trans hdvd)
    have : IsCyclic ((P : Subgroup G).map ρ) := by
      interval_cases k
      · rw [pow_zero] at hk
        have : Subsingleton ((P : Subgroup G).map ρ) := (Nat.card_eq_one_iff_unique.mp hk).1
        exact isCyclic_of_subsingleton
      · rw [pow_one] at hk
        exact isCyclic_of_prime_card hk
    exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hfker
  have hM : ρ.ker = ⊥ := by
    have h := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup P hPab hMc hMp
    rwa [Group.IsPerfect.commutator_eq_top, inf_top_eq] at h
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hM
  let e : G ≃* ρ.range := MonoidHom.ofInjective hinj
  have : Group.IsPerfect ρ.range := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hne : ρ.range ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have : ρ x ∈ ρ.range := ⟨x, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx (hinj (by rw [this, map_one]))
  rcases perfect_gl2_mulEquiv hp2 ρ.range hne with h | h
  · obtain ⟨f⟩ := h
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨f⟩ := h
    exact Or.inr ⟨e.trans f⟩

theorem isInvariant_bot {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : Subgroup (GL σ K)) : IsInvariant G (⊥ : Submodule K (σ → K)) := by
  intro g _ w hw
  rw [Submodule.mem_bot] at hw ⊢
  rw [hw, Matrix.mulVec_zero]

theorem finrank_section_bot {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (C : Submodule K (σ → K)) :
    Module.finrank K (C ⧸ (⊥ : Submodule K (σ → K)).comap C.subtype) = Module.finrank K C := by
  have h := Submodule.finrank_quotient_add_finrank ((⊥ : Submodule K (σ → K)).comap C.subtype)
  have h0 : Module.finrank K ((⊥ : Submodule K (σ → K)).comap C.subtype) = 0 := by
    rw [Submodule.comap_bot, Submodule.ker_subtype, finrank_bot]
  rw [h0, add_zero] at h
  exact h

theorem sectionRep_bot_eq_one_iff {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : Subgroup (GL σ K)) {C : Submodule K (σ → K)} (hC : IsInvariant G C) {m : ℕ}
    (b : Module.Basis (Fin m) K (C ⧸ (⊥ : Submodule K (σ → K)).comap C.subtype)) (g : G) :
    sectionRep G (isInvariant_bot G) hC b g = 1 ↔
      ∀ c ∈ C, ((g : GL σ K) : Matrix σ σ K) *ᵥ c = c := by
  rw [sectionRep_eq_one_iff]
  simp [sub_eq_zero]

theorem sq_eq_one_of_mem_center_sl2 {F : Type*} [CommRing F] {x : SL(2, F)}
    (hx : x ∈ Subgroup.center SL(2, F)) : x ^ 2 = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, hr, map_one]
  rfl

theorem sq_eq_one_of_mem_center_of_mulEquiv {J : Type*} [Group J] {F : Type*} [CommRing F]
    (f : J ≃* SL(2, F)) {x : J} (hx : x ∈ Subgroup.center J) : x ^ 2 = 1 := by
  have hfc : f x ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := f.surjective y
    rw [← map_mul, ← map_mul, hx z]
  apply f.injective
  rw [map_pow, map_one]
  exact sq_eq_one_of_mem_center_sl2 hfc

theorem quasisimple_of_two_gl2_reps {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (hG : CFSG.IsQuasisimple G) (ρ₁ ρ₂ : G →* GL (Fin 2) (ZMod p))
    (hjoint : ∀ g : G, ρ₁ g = 1 → ρ₂ g = 1 → g = 1) :
    Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) := by
  classical
  have hperf : Group.IsPerfect G := hG.1
  have key : ∀ ρ : G →* GL (Fin 2) (ZMod p), Function.Injective ρ →
      Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) := fun ρ hρ =>
    quasisimple_gl2_of_unipotent_kernel hp2 hG ρ fun g hg => by
      rw [show g = 1 from hρ (hg.trans (map_one ρ).symm), one_pow]
  by_cases hk2 : ∀ g, ρ₂ g = 1
  · exact key ρ₁ fun a b hab => by
      have := hjoint (a * b⁻¹) (by rw [map_mul, map_inv, hab, mul_inv_cancel])
        (by rw [hk2])
      rwa [mul_inv_eq_one] at this
  by_cases hk1 : ∀ g, ρ₁ g = 1
  · exact key ρ₂ fun a b hab => by
      have := hjoint (a * b⁻¹) (by rw [hk1])
        (by rw [map_mul, map_inv, hab, mul_inv_cancel])
      rwa [mul_inv_eq_one] at this
  push Not at hk1 hk2
  have hNc : ρ₁.ker ≤ Subgroup.center G := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hG ρ₁.normal_ker with h | h
    · exfalso
      obtain ⟨g, hg⟩ := hk1
      exact hg (show g ∈ ρ₁.ker from h ▸ Subgroup.mem_top g)
    · exact h
  have hrange_ne : ∀ ρ : G →* GL (Fin 2) (ZMod p), (∃ g, ρ g ≠ 1) → ρ.range ≠ ⊥ := by
    rintro ρ ⟨g, hg⟩ h
    have : ρ g ∈ ρ.range := ⟨g, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact hg this
  have : Group.IsPerfect ρ₁.range := Group.IsPerfect.range ρ₁
  have : Group.IsPerfect ρ₂.range := Group.IsPerfect.range ρ₂
  have hN2 : ∀ n ∈ ρ₁.ker, n ^ 2 = 1 := by
    intro n hn
    have hcen : ρ₂.rangeRestrict n ∈ Subgroup.center ρ₂.range := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨_, g, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict]
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hNc hn) g)]
    have hsq : ρ₂.rangeRestrict n ^ 2 = 1 := by
      rcases perfect_gl2_mulEquiv hp2 ρ₂.range (hrange_ne ρ₂ hk2) with h | h
      · obtain ⟨f⟩ := h
        exact sq_eq_one_of_mem_center_of_mulEquiv f hcen
      · obtain ⟨f⟩ := h
        exact sq_eq_one_of_mem_center_of_mulEquiv f hcen
    have h2' : ρ₂ (n ^ 2) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val hsq
      rwa [SubgroupClass.coe_pow, MonoidHom.coe_rangeRestrict, OneMemClass.coe_one] at this
    exact hjoint _ (by rw [map_pow, (MonoidHom.mem_ker.mp hn), one_pow]) h2'
  have hsplit : ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 → (ρ₁.range ≃* SL(2, F)) →
      ρ₁.ker = ⊥ := by
    intro F _ _ hF e
    let π : G →* SL(2, F) := e.toMonoidHom.comp ρ₁.rangeRestrict
    have hπ : Function.Surjective π := e.surjective.comp ρ₁.rangeRestrict_surjective
    have hπker : ∀ g, π g = 1 ↔ ρ₁ g = 1 := by
      intro g
      simp only [π, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hcen : π.ker ≤ Subgroup.center G := fun g hg => hNc ((hπker g).mp hg)
    have h2grp : IsPGroup 2 π.ker := fun g => ⟨1, Subtype.ext (by
      rw [pow_one]
      exact hN2 g ((hπker g).mp g.2))⟩
    obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hF hπ hcen h2grp (MonoidHom.id _)
    have hβx : ∀ x, π (β x) = x := fun x => DFunLike.congr_fun hβ x
    have hc : ∀ g : G, (β (π g))⁻¹ * g ∈ Subgroup.center G := fun g =>
      hcen (by rw [MonoidHom.mem_ker, map_mul, map_inv, hβx, inv_mul_cancel])
    let φ : G →* G :=
      { toFun := fun g => (β (π g))⁻¹ * g
        map_one' := by simp
        map_mul' := fun g h => by
          have hcg := Subgroup.mem_center_iff.mp (hc g)
          simp only [map_mul]
          calc (β (π g) * β (π h))⁻¹ * (g * h) = (β (π h))⁻¹ * (((β (π g))⁻¹ * g) * h) := by
                group
            _ = ((β (π g))⁻¹ * g) * ((β (π h))⁻¹ * h) := by
                rw [← mul_assoc, hcg, mul_assoc] }
    have hφ : φ = 1 := perfect_hom_eq_one_of_commute hperf φ (by
      rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
      exact Subgroup.mem_center_iff.mp (hc h) _)
    rw [eq_bot_iff]
    intro n hn
    have h1 : φ n = 1 := by rw [hφ]; rfl
    have hπn : π n = 1 := (hπker n).mpr hn
    simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, hπn, map_one, inv_one, one_mul] at h1
    exact (Subgroup.mem_bot).mpr h1
  have hker : ρ₁.ker = ⊥ := by
    rcases perfect_gl2_mulEquiv hp2 ρ₁.range (hrange_ne ρ₁ hk1) with h | h
    · obtain ⟨e⟩ := h
      exact hsplit (ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2) e
    · obtain ⟨e⟩ := h
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact hsplit (ZMod 5) (by rw [ZMod.ringChar_zmod_n]; norm_num) e
  exact key ρ₁ ((MonoidHom.ker_eq_bot_iff ρ₁).mp hker)

theorem quasisimple_of_plane_decomposition {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {σ : Type*}
    [Fintype σ] [DecidableEq σ] {G : Subgroup (GL σ (ZMod p))} (hG : CFSG.IsQuasisimple G)
    {W W' : Submodule (ZMod p) (σ → ZMod p)} (hW : IsInvariant G W) (hW' : IsInvariant G W')
    (h2 : Module.finrank (ZMod p) W = 2) (h2' : Module.finrank (ZMod p) W' = 2)
    (hsup : W ⊔ W' = ⊤) :
    Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) := by
  classical
  let b₁ := Module.finBasisOfFinrankEq (ZMod p) _ ((finrank_section_bot W).trans h2)
  let b₂ := Module.finBasisOfFinrankEq (ZMod p) _ ((finrank_section_bot W').trans h2')
  have hρ₁ := sectionRep_bot_eq_one_iff G hW b₁
  have hρ₂ := sectionRep_bot_eq_one_iff G hW' b₂
  refine quasisimple_of_two_gl2_reps hp2 hG (sectionRep G (isInvariant_bot G) hW b₁)
    (sectionRep G (isInvariant_bot G) hW' b₂) fun g h1 h2 => ?_
  apply Subtype.ext
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hv : v ∈ W ⊔ W' := hsup ▸ Submodule.mem_top
  obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add, (hρ₁ g).mp h1 w hw, (hρ₂ g).mp h2 w' hw', OneMemClass.coe_one,
    Units.val_one, Matrix.one_mulVec]

end Quasisimple

section Reducible

local notation "V₄" => Fin 2 ⊕ Fin 2

open CFSG.Assembly.LowTwoRank

theorem gl_fin_one_comm {K : Type*} [CommRing K] (a b : GL (Fin 1) K) : a * b = b * a := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem eq_span_of_finrank_eq_one {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {U : Submodule K V} (h : Module.finrank K U = 1) :
    ∃ u ∈ U, U = K ∙ u := by
  have hU0 : U ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h
    exact zero_ne_one h
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  refine ⟨u, hu, ?_⟩
  symm
  apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)
  rw [h, finrank_span_singleton hu0]

theorem le_orth_of_finrank_eq_one {K : Type} [Field K] {n : ℕ}
    {U : Submodule K (Fin n ⊕ Fin n → K)} (h : Module.finrank K U = 1) : U ≤ orth U := by
  obtain ⟨u, -, rfl⟩ := eq_span_of_finrank_eq_one h
  intro x hx
  rw [mem_orth]
  intro y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp [spForm_self]

theorem mulVec_sq {p : ℕ} (M : Matrix V₄ V₄ (ZMod p))
    (v : V₄ → ZMod p) :
    (M ^ 2) *ᵥ v = M *ᵥ (M *ᵥ v) := by
  rw [pow_two, Matrix.mulVec_mulVec]

theorem mulVec_cube {p : ℕ} (M : Matrix V₄ V₄ (ZMod p))
    (v : V₄ → ZMod p) : (M ^ 3) *ᵥ v = M *ᵥ (M *ᵥ (M *ᵥ v)) := by
  rw [pow_three, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

variable {p : ℕ} [Fact p.Prime]

theorem sub_mem_orth_of_fix {G : Subgroup (GL V₄ (ZMod p))}
    (hGS : G ≤ StatedSp 2 (ZMod p)) {T : Submodule (ZMod p) (V₄ → ZMod p)} {g : G}
    (hg : ∀ t ∈ T, ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *ᵥ t = t)
    (v : V₄ → ZMod p) :
    ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *ᵥ v - v ∈ orth T := by
  rw [mem_orth]
  intro t ht
  rw [map_sub, sub_eq_zero]
  conv_lhs => rw [← hg t ht]
  exact spForm_mulVec (hGS g.2) t v

theorem pow_eq_one_of_unipotent_sub {G : Subgroup (GL V₄ (ZMod p))} {g : G}
    (h : (((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) - 1) ^ 4 = 0) :
    g ^ (p ^ 2) = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow]; exact pow_prime_sq_eq_one_of_unipotent _ h)

theorem quasisimple_reducible_sp4 (hp2 : p ≠ 2) {G : Subgroup (GL V₄ (ZMod p))}
    (hGS : G ≤ StatedSp 2 (ZMod p)) (hG : CFSG.IsQuasisimple G)
    {U : Submodule (ZMod p) (V₄ → ZMod p)} (hU : IsInvariant G U) (hU0 : U ≠ ⊥)
    (hUt : U ≠ ⊤) :
    Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) := by
  classical
  have hV : Module.finrank (ZMod p) (V₄ → ZMod p) = 4 := by simp
  have hperf : Group.IsPerfect G := hG.1
  have caseA : ∀ W, IsInvariant G W → Module.finrank (ZMod p) W = 2 → W ⊓ orth W = ⊥ →
      Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) :=
    fun W hW h2 hd => quasisimple_of_plane_decomposition hp2 hG hW (isInvariant_orth hGS hW) h2
      (by rw [finrank_orth, h2]) (sup_orth_eq_top hd)
  have caseB : ∀ T, IsInvariant G T → T ≠ ⊥ → T ≤ orth T →
      Nonempty (G ≃* SL(2, ZMod p)) ∨ Nonempty (G ≃* SL(2, ZMod 5)) := by
    intro T hT hT0 hTT
    have hfT := finrank_orth T
    have hle := Submodule.finrank_mono hTT
    have hpos : Module.finrank (ZMod p) T ≠ 0 := fun h => hT0 (Submodule.finrank_eq_zero.mp h)
    rcases (by omega : Module.finrank (ZMod p) T = 1 ∨ Module.finrank (ZMod p) T = 2) with
      h1 | h2
    ·
      let b₁ := Module.finBasisOfFinrankEq (ZMod p) _ ((finrank_section_bot T).trans h1)
      have hχ : sectionRep G (isInvariant_bot G) hT b₁ = 1 :=
        perfect_hom_eq_one_of_commute hperf _ fun a _ b _ => gl_fin_one_comm a b
      have hfix : ∀ g : G, ∀ t ∈ T,
          ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p)) *ᵥ t = t := fun g =>
        (sectionRep_bot_eq_one_iff G hT b₁ g).mp (by rw [hχ]; rfl)
      have hS : IsInvariant G (orth T) := isInvariant_orth hGS hT
      have hsec : Module.finrank (ZMod p) (orth T ⧸ T.comap (orth T).subtype) = 2 := by
        have h := Submodule.finrank_quotient_add_finrank (T.comap (orth T).subtype)
        rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hTT), h1, hfT, h1] at h
        omega
      let b₂ := Module.finBasisOfFinrankEq (ZMod p) _ hsec
      refine quasisimple_gl2_of_unipotent_kernel hp2 hG (sectionRep G hT hS b₂) fun g hg => ?_
      have hk := (sectionRep_eq_one_iff G hT hS b₂ g).mp hg
      apply pow_eq_one_of_unipotent_sub
      set gm : Matrix V₄ V₄ (ZMod p) := ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))
        with hgm
      set M := gm - 1 with hM
      have hMv : ∀ v, M *ᵥ v = gm *ᵥ v - v :=
        fun v => by rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec]
      have h3 : M ^ 3 = 0 := by
        rw [Matrix.ext_iff_mulVec]
        intro v
        rw [mulVec_cube, Matrix.zero_mulVec]
        have hv1 : M *ᵥ v ∈ orth T := by rw [hMv]; exact sub_mem_orth_of_fix hGS (hfix g) v
        have hv2 : M *ᵥ (M *ᵥ v) ∈ T := by rw [hMv]; exact hk _ hv1
        rw [hMv, hfix g _ hv2, sub_self]
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, h3, zero_mul]
    ·
      have hTeq : orth T = T :=
        (Submodule.eq_of_le_of_finrank_le hTT (by rw [hfT, h2])).symm
      let b := Module.finBasisOfFinrankEq (ZMod p) _ ((finrank_section_bot T).trans h2)
      refine quasisimple_gl2_of_unipotent_kernel hp2 hG (sectionRep G (isInvariant_bot G) hT b)
        fun g hg => ?_
      have hk := (sectionRep_bot_eq_one_iff G hT b g).mp hg
      apply pow_eq_one_of_unipotent_sub
      set gm : Matrix V₄ V₄ (ZMod p) := ((g : GL V₄ (ZMod p)) : Matrix V₄ V₄ (ZMod p))
        with hgm
      set M := gm - 1 with hM
      have hMv : ∀ v, M *ᵥ v = gm *ᵥ v - v :=
        fun v => by rw [hM, Matrix.sub_mulVec, Matrix.one_mulVec]
      have h2' : M ^ 2 = 0 := by
        rw [Matrix.ext_iff_mulVec]
        intro v
        rw [mulVec_sq, Matrix.zero_mulVec]
        have hv1 : M *ᵥ v ∈ T := by
          rw [hMv, ← hTeq]
          exact sub_mem_orth_of_fix hGS hk v
        rw [hMv, hk _ hv1, sub_self]
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, h2', zero_mul]
  by_cases hR : U ⊓ orth U = ⊥
  · have hpos : Module.finrank (ZMod p) U ≠ 0 := fun h => hU0 (Submodule.finrank_eq_zero.mp h)
    have hlt : Module.finrank (ZMod p) U < 4 := hV ▸ Submodule.finrank_lt hUt
    rcases (by omega : Module.finrank (ZMod p) U = 1 ∨ Module.finrank (ZMod p) U = 2 ∨
        Module.finrank (ZMod p) U = 3) with h1 | h2 | h3
    · exfalso
      exact hU0 (by rw [← inf_eq_left.mpr (le_orth_of_finrank_eq_one h1)]; exact hR)
    · exact caseA U hU h2 hR
    · exfalso
      have hW1 : Module.finrank (ZMod p) (orth U) = 1 := by rw [finrank_orth, h3]
      have hWle := le_orth_of_finrank_eq_one hW1
      rw [orth_orth] at hWle
      have hbot : orth U = ⊥ := by
        rw [← hR]
        exact le_antisymm (le_inf hWle le_rfl) inf_le_right
      rw [hbot, finrank_bot] at hW1
      exact zero_ne_one hW1
  · exact caseB (U ⊓ orth U) (isInvariant_inf hU (isInvariant_orth hGS hU)) hR fun x hx => by
      rw [mem_orth]
      intro y hy
      exact (mem_orth.mp hx.2) y hy.1

end Reducible

end CFSG.RankThree.SubgroupLists
