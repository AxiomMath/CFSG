module

public import CFSG.RankThree.PartOne.S13K.Refl136Shapes
public import CFSG.RankThree.PartOne.S13K.Refl136Coord
import CFSG.RankThree.PartOne.HNB.Tools

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne ReflAlg Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  (C : Sp6Ctx p A c L E f K)

@[expose] noncomputable def eE (ζ : (Qext K)ˣ) (hζ : ζ ^ p = 1) (a : Fin 3 → ZMod p) : ↥E :=
  C.eT (expv ζ a) (expv_pow hζ a)

theorem eE_add {ζ : (Qext K)ˣ} (hζ : ζ ^ p = 1) (a b : Fin 3 → ZMod p) :
    C.eE ζ hζ (a + b) = C.eE ζ hζ a * C.eE ζ hζ b := by
  unfold eE
  rw [C.eT_mul]
  exact C.eT_congr (expv_add hζ a b)

theorem eE_injective {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (C.eE ζ hζ.pow_eq_one) := fun _ _ h =>
  expv_injective hζ (C.eT_injective h)

theorem eE_mem_L {ζ : (Qext K)ˣ} (hζ : ζ ^ p = 1) (a : Fin 3 → ZMod p) :
    ((C.eE ζ hζ a : ↥E) : G) ∈ L :=
  C.phi_mem_L _

theorem tSgn_eE {ζ : (Qext K)ˣ} (hζ : ζ ^ p = 1) (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool)
    (a : Fin 3 → ZMod p) : C.tSgn π ε (C.eE ζ hζ a) = C.eE ζ hζ (sgnVec π ε a) := by
  unfold eE
  rw [C.tSgn_apply_eT]
  exact C.eT_congr (sact_expv hζ π ε a)

theorem exists_eE_of_mem_L {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) {e : ↥E} (he : (e : G) ∈ L) :
    ∃ a : Fin 3 → ZMod p, e = C.eE ζ hζ.pow_eq_one a := by
  obtain ⟨x, hx, k, rfl⟩ := C.exists_decomp_eT e
  have hcord : orderOf c = p := by
    have := C.h.A_elem
    refine orderOf_eq_prime ?_ C.h.c_ne_one
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c C.h.c_mem
  have hck : c ^ k ∈ L := by
    have h1 : ((C.eT x hx : ↥E) : G) ∈ L := C.phi_mem_L _
    have h2 : (((C.eT x hx * C.cE ^ k : ↥E)) : G) = ((C.eT x hx : ↥E) : G) * c ^ k := rfl
    rw [h2] at he
    have := L.mul_mem (L.inv_mem h1) he
    simpa using this
  have hk1 : c ^ k = 1 := by
    by_contra hne
    exact C.hcL (Subgroup.zpowers_le.2 hck
      (HNB.mem_zpowers_of_mem_zpowers_prime hcord (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩) hne))
  obtain ⟨a, ha⟩ := expv_surj C.h.prime hζ hx
  refine ⟨a, ?_⟩
  have h3 : C.cE ^ k = 1 := Subtype.ext hk1
  rw [h3, mul_one]
  exact C.eT_congr ha.symm


structure YData (C : Sp6Ctx p A c L E f K) where
  ζ : (Qext K)ˣ
  hζ : IsPrimitiveRoot ζ p
  y : MulAut ↥E
  hyL : ∀ e : ↥E, (e : G) ∈ L → ((y e : ↥E) : G) ∈ L

namespace YData

variable {C} (D : YData C)

theorem exists_yE (a : Fin 3 → ZMod p) :
    ∃ a', D.y (C.eE D.ζ D.hζ.pow_eq_one a) = C.eE D.ζ D.hζ.pow_eq_one a' :=
  C.exists_eE_of_mem_L D.hζ (D.hyL _ (C.eE_mem_L _ a))

@[expose] noncomputable def yE (a : Fin 3 → ZMod p) : Fin 3 → ZMod p := Classical.choose (D.exists_yE a)

theorem y_eE (a : Fin 3 → ZMod p) :
    D.y (C.eE D.ζ D.hζ.pow_eq_one a) = C.eE D.ζ D.hζ.pow_eq_one (D.yE a) :=
  Classical.choose_spec (D.exists_yE a)

theorem yE_add (a b : Fin 3 → ZMod p) : D.yE (a + b) = D.yE a + D.yE b := by
  apply C.eE_injective D.hζ
  rw [← D.y_eE, C.eE_add, map_mul, D.y_eE, D.y_eE, C.eE_add]

theorem yE_yE (hy2 : D.y * D.y = 1) (a : Fin 3 → ZMod p) : D.yE (D.yE a) = a := by
  apply C.eE_injective D.hζ
  rw [← D.y_eE, ← D.y_eE]
  have := congrArg (fun m : MulAut ↥E => m (C.eE D.ζ D.hζ.pow_eq_one a)) hy2
  simpa [MulAut.mul_apply] using this

@[expose] noncomputable def yHom : (Fin 3 → ZMod p) →+ (Fin 3 → ZMod p) :=
  AddMonoidHom.mk' D.yE D.yE_add

@[expose] noncomputable def yMat : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  LinearMap.toMatrix' (D.yHom.toZModLinearMap p)

theorem yMat_mulVec (a : Fin 3 → ZMod p) : D.yMat *ᵥ a = D.yE a := by
  unfold yMat
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem matrix_ext {M N : Matrix (Fin 3) (Fin 3) (ZMod p)} (h : ∀ a, M *ᵥ a = N *ᵥ a) : M = N := by
  ext j i
  have := congrFun (h (Pi.single i 1)) j
  simpa [Matrix.mulVec_single_one] using this

theorem yMat_mul_self (hy2 : D.y * D.y = 1) : D.yMat * D.yMat = 1 := by
  apply matrix_ext
  intro a
  rw [← Matrix.mulVec_mulVec, D.yMat_mulVec, D.yMat_mulVec, D.yE_yE hy2, Matrix.one_mulVec]


@[expose] noncomputable def nHom : (Fin 3 → ZMod p) →+ (Fin 3 → ZMod p) := D.yHom - AddMonoidHom.id _

theorem nHom_apply (a : Fin 3 → ZMod p) : D.nHom a = D.yE a - a := rfl

theorem nHom_eq_zero_iff (a : Fin 3 → ZMod p) : D.nHom a = 0 ↔ D.yE a = a := by
  rw [nHom_apply, sub_eq_zero]

theorem card_ker_nHom (hfix : Nat.card ↥(autFixedInG E D.y ⊓ L) = p ^ 2) :
    Nat.card D.nHom.ker = p ^ 2 := by
  rw [← hfix]
  have hmem : ∀ a : D.nHom.ker, ((C.eE D.ζ D.hζ.pow_eq_one a.1 : ↥E) : G) ∈ autFixedInG E D.y ⊓ L := by
    intro a
    refine Subgroup.mem_inf.2 ⟨?_, C.eE_mem_L _ _⟩
    refine Subgroup.mem_map.2 ⟨C.eE D.ζ D.hζ.pow_eq_one a.1, ?_, rfl⟩
    have h1 : D.yE a.1 = a.1 := (D.nHom_eq_zero_iff a.1).1 a.2
    show D.y (C.eE D.ζ D.hζ.pow_eq_one a.1) = C.eE D.ζ D.hζ.pow_eq_one a.1
    rw [D.y_eE, h1]
  refine Nat.card_congr (Equiv.ofBijective (fun a => ⟨_, hmem a⟩) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : ((C.eE D.ζ D.hζ.pow_eq_one a.1 : ↥E) : G) = ((C.eE D.ζ D.hζ.pow_eq_one b.1 : ↥E) : G) := by
      have := congrArg (fun x : ↥(autFixedInG E D.y ⊓ L) => (x : G)) hab
      simpa using this
    exact Subtype.ext (C.eE_injective D.hζ (Subtype.ext h1))
  · rintro ⟨g, hg⟩
    obtain ⟨hgF, hgL⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hgF
    obtain ⟨a, rfl⟩ := C.exists_eE_of_mem_L D.hζ hgL
    have he' : D.y (C.eE D.ζ D.hζ.pow_eq_one a) = C.eE D.ζ D.hζ.pow_eq_one a := he
    rw [D.y_eE] at he'
    have h1 : D.yE a = a := C.eE_injective D.hζ he'
    exact ⟨⟨a, (D.nHom_eq_zero_iff a).2 h1⟩, rfl⟩

theorem exists_rank_one (hfix : Nat.card ↥(autFixedInG E D.y ⊓ L) = p ^ 2) :
    ∃ u φ : Fin 3 → ZMod p, u ≠ 0 ∧ φ ≠ 0 ∧ D.yMat = 1 + Matrix.vecMulVec u φ := by
  obtain ⟨u, hu, ⟨a₀, ha₀⟩, hk⟩ := exists_line_of_card_ker D.nHom (D.card_ker_nHom hfix)
  obtain ⟨φ, hφ⟩ := exists_phi_of_line (M := D.yMat) (u := u) (fun a => by
    obtain ⟨k, hk'⟩ := hk a
    refine ⟨k, ?_⟩
    rw [D.yMat_mulVec]
    exact hk')
  refine ⟨u, φ, hu, ?_, hφ⟩
  rintro rfl
  apply ha₀
  have h1 : D.yE a₀ = a₀ := by
    rw [← D.yMat_mulVec, hφ]
    simp
  exact (D.nHom_eq_zero_iff a₀).2 h1

theorem yMat_normalizes (hF13 : Sec13Facts G p A c L E) (hp5 : 5 ≤ p) {h : G}
    (hhE : h ∈ Subgroup.normalizer (E : Set G)) (hhL : h ∈ Subgroup.normalizer (L : Set G))
    (hy : D.y = conjAut E h hhE) :
    ∀ α : Fin 3 → ZMod p, IsRoot α → ∃ β, IsRoot β ∧ D.yMat * reflMat α = reflMat β * D.yMat := by
  intro α hα
  obtain ⟨π, ε, hs, hmat⟩ := exists_shape_of_root hp5 hα
  have hr : C.tSgn π ε ∈ reflectionSet p E := C.tSgn_mem_reflectionSet_of_shape hF13 hs
  have hr' : D.y * C.tSgn π ε * D.y⁻¹ ∈ reflectionSet p E := by
    rw [hy]
    exact conj_mem_reflectionSet C.h.prime hr hhE
  have hr'L : D.y * C.tSgn π ε * D.y⁻¹ ∈ torusImage E L := by
    have h1 := torusImage_conjBy E L hhE
    rw [Equivariance.conjBy_eq_of_mem_normalizer hhL] at h1
    rw [h1]
    refine Subgroup.mem_map.2 ⟨C.tSgn π ε, C.tSgn_mem_torusImage π ε, ?_⟩
    rw [hy]
    rfl
  obtain ⟨π', ε', hs', heq⟩ := C.exists_shape hr' hr'L
  obtain ⟨β, hβ, hmat'⟩ := exists_root_of_shape hp5 hs'
  refine ⟨β, hβ, ?_⟩
  rw [← hmat, ← hmat']
  apply matrix_ext
  intro a
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, sgnMat_mulVec, sgnMat_mulVec, D.yMat_mulVec,
    D.yMat_mulVec]
  apply C.eE_injective D.hζ
  have h1 : D.y * C.tSgn π ε = C.tSgn π' ε' * D.y := mul_inv_eq_iff_eq_mul.1 heq
  have h2 := congrArg (fun m : MulAut ↥E => m (C.eE D.ζ D.hζ.pow_eq_one a)) h1
  simp only [MulAut.mul_apply] at h2
  rw [C.tSgn_eE, D.y_eE, D.y_eE, C.tSgn_eE] at h2
  exact h2

end YData

end Sp6Ctx

theorem kf136Refl_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF136Refl := by
  unfold KF136Refl
  intro G _ _ p A c L E hH hF hF13 _ hEA hrow y hy hy2 _ hfix
  obtain ⟨f, hf1, hpf, hmod⟩ := hrow
  obtain ⟨K, _, _, _, ⟨C⟩⟩ := exists_sp6ctx hGA hH hF hEA hf1 hpf hmod
  have : Fact p.Prime := ⟨C.h.prime⟩
  have hp5 : 5 ≤ p := Sec12Three.five_le hH
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot C.h.prime C.hp2 C.hpq'
  obtain ⟨h, hhc, hhE, rfl⟩ := Sec12Three.mem_torusImage_iff.1 hy
  have hhL : h ∈ Subgroup.normalizer (L : Set G) := hF.twoB (Subgroup.mem_inf.2 ⟨hhc, hhE⟩)
  have hyL : ∀ e : ↥E, (e : G) ∈ L → ((conjAut E h hhE e : ↥E) : G) ∈ L := by
    intro e he
    rw [Equivariance.coe_conjAut hhE]
    exact (Subgroup.mem_normalizer_iff.1 hhL _).1 he
  let D : Sp6Ctx.YData C := ⟨ζ, hζ, conjAut E h hhE, hyL⟩
  have hMM : D.yMat * D.yMat = 1 := D.yMat_mul_self hy2
  obtain ⟨u, φ, hu, hφ, hM⟩ := D.exists_rank_one hfix
  obtain ⟨β, hβ, hMβ⟩ := ReflAlg.eq_reflMat_of_normalizes hp5 D.yMat hMM u φ hu hφ hM
    (D.yMat_normalizes hF13 hp5 hhE hhL rfl)
  obtain ⟨π, ε, hs, hmat⟩ := exists_shape_of_root hp5 hβ
  have hyE : ∀ a, D.yE a = sgnVec π ε a := by
    intro a
    rw [← D.yMat_mulVec, hMβ, ← hmat, sgnMat_mulVec]
  refine ⟨C.tSgn π ε, C.tSgn_mem_reflectionSet_of_shape hF13 hs, C.tSgn_mem_torusImage π ε, ?_⟩
  intro b hb
  obtain ⟨a, rfl⟩ := C.exists_eE_of_mem_L hζ hb
  show D.y (C.eE ζ hζ.pow_eq_one a) = C.tSgn π ε (C.eE ζ hζ.pow_eq_one a)
  rw [D.y_eE, hyE, C.tSgn_eE]

end CFSG.RankThree.PartOne.S13K
