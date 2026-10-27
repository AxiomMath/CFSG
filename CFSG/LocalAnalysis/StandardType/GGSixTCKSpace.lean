module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergRank
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.HeisenbergDefs
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib

public section

namespace CFSG.StandardType.ClassicalPosition

section HeisK

private lemma tcPSL_natCast_ne_zero {K : Type} [Field K] {p : ℕ} (hp : (p : K) ≠ 0) :
    (p : AlgebraicClosure K) ≠ 0 := by
  intro h
  apply hp
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [← map_natCast (algebraMap K (AlgebraicClosure K)) p] at h
  simpa using h

private noncomputable def tcPSL_Psi (K U : Type) [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] : (U ≃ₗ[K] U) ≃* GL (Fin (Module.finrank K U)) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm.trans
    (Matrix.GeneralLinearGroup.toLin' (Module.finBasis K U)).symm

private lemma tcPSL_scalar_mulVec (K : Type) [Field K] (N : ℕ) (a : K) (w : Fin N → K) :
    Matrix.mulVec (Matrix.scalar (Fin N) a) w = a • w := by
  rw [Matrix.scalar_apply, Matrix.diagonal_const_mulVec]

private lemma tcPSL_Psi_equivFun (K U : Type) [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (x : U ≃ₗ[K] U) (u : U) :
    (Module.finBasis K U).equivFun (x u)
      = Matrix.mulVec (tcPSL_Psi K U x : Matrix (Fin (Module.finrank K U))
          (Fin (Module.finrank K U)) K) ((Module.finBasis K U).equivFun u) := by
  have h1 : Matrix.GeneralLinearGroup.toLin' (Module.finBasis K U) (tcPSL_Psi K U x)
      = (LinearMap.GeneralLinearGroup.generalLinearEquiv K U).symm x := by
    simp [tcPSL_Psi]
  have h2 : x u = (Matrix.GeneralLinearGroup.toLin' (Module.finBasis K U)
      (tcPSL_Psi K U x)).toLinearEquiv u := by
    rw [h1]
    rfl
  have hlc : ∀ f : Fin (Module.finrank K U) → K,
      Fintype.linearCombination K ⇑(Module.finBasis K U) f
        = (Module.finBasis K U).equivFun.symm f := by
    intro f
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
  rw [h2, Matrix.GeneralLinearGroup.toLin'_apply, hlc, LinearEquiv.apply_symm_apply]
  rfl

private lemma tcPSL_Psi_mem_center_iff (K U : Type) [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (x : U ≃ₗ[K] U) :
    tcPSL_Psi K U x ∈ Subgroup.center (GL (Fin (Module.finrank K U)) K) ↔
      x ∈ HeisRank.scalarAut K U := by
  rw [Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, HeisRank.mem_scalarAut_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun v => ?_⟩
    apply (Module.finBasis K U).equivFun.injective
    rw [tcPSL_Psi_equivFun, ← ha, tcPSL_scalar_mulVec, map_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hbj : ∀ j : Fin (Module.finrank K U),
        (Module.finBasis K U).equivFun (Module.finBasis K U j) = Pi.single j 1 := by
      intro j
      ext k
      simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
    ext i j
    have h1 := tcPSL_Psi_equivFun K U x (Module.finBasis K U j)
    rw [hc, map_smul, hbj, Matrix.mulVec_single_one] at h1
    have h2 := congrFun h1 i
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply, Pi.single_apply] using h2

theorem index_scalarAut_le {K U G : Type} [Field K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] [Group G] {p : ℕ} (hp : (p : K) ≠ 0)
    (φ : G →* (U ≃ₗ[K] U)) (hpow : ∀ g, φ g ^ p ∈ HeisRank.scalarAut K U)
    (hc : ∀ g h, φ g * φ h = φ h * φ g) :
    ((HeisRank.scalarAut K U).comap φ).index ≠ 0 ∧
      ((HeisRank.scalarAut K U).comap φ).index ≤ p ^ (Module.finrank K U - 1) := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : G →* GL (Fin (Module.finrank K U)) K,
      ∀ g, ψ g = tcPSL_Psi K U (φ g) :=
    ⟨(tcPSL_Psi K U).toMonoidHom.comp φ, fun g => rfl⟩
  obtain ⟨φE, -, hker⟩ := HeisRank.exists_rep_over (F := AlgebraicClosure K) ψ.range
  obtain ⟨ρ, hρ⟩ : ∃ ρ : G →*
      ((Fin (Module.finrank K U) → AlgebraicClosure K) ≃ₗ[AlgebraicClosure K]
        (Fin (Module.finrank K U) → AlgebraicClosure K)),
      ∀ g, ρ g = φE (ψ.rangeRestrict g) :=
    ⟨φE.comp ψ.rangeRestrict, fun g => rfl⟩
  have hmem : ∀ g : G,
      ρ g ∈ HeisRank.scalarAut (AlgebraicClosure K)
          (Fin (Module.finrank K U) → AlgebraicClosure K) ↔
        φ g ∈ HeisRank.scalarAut K U := by
    intro g
    rw [hρ, ← Subgroup.mem_comap (f := φE) (x := ψ.rangeRestrict g), hker, Subgroup.mem_subgroupOf,
      MonoidHom.coe_rangeRestrict, hψ]
    exact tcPSL_Psi_mem_center_iff K U (φ g)
  have hcomap : (HeisRank.scalarAut (AlgebraicClosure K)
      (Fin (Module.finrank K U) → AlgebraicClosure K)).comap ρ
        = (HeisRank.scalarAut K U).comap φ := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    exact hmem g
  have hpowρ : ∀ g : G, ρ g ^ p ∈
      HeisRank.scalarAut (AlgebraicClosure K) (Fin (Module.finrank K U) → AlgebraicClosure K) := by
    intro g
    rw [← map_pow, hmem, map_pow]
    exact hpow g
  have hcρ : ∀ g h : G, ρ g * ρ h = ρ h * ρ g := by
    intro g h
    have hcomm : ψ.rangeRestrict g * ψ.rangeRestrict h
        = ψ.rangeRestrict h * ψ.rangeRestrict g := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, MonoidHom.coe_rangeRestrict,
        MonoidHom.coe_rangeRestrict, hψ, hψ, ← map_mul (tcPSL_Psi K U), ← map_mul (tcPSL_Psi K U),
        hc g h]
    rw [hρ, hρ, ← map_mul φE, ← map_mul φE, hcomm]
  have hpF : (p : AlgebraicClosure K) ≠ 0 := tcPSL_natCast_ne_zero hp
  obtain ⟨h0, hle⟩ := HeisRank.index_le_of_commute (F := AlgebraicClosure K)
    (V := Fin (Module.finrank K U) → AlgebraicClosure K) (G := G) (p := p) hpF ρ hpowρ hcρ
  rw [hcomap] at h0 hle
  simp only [Module.finrank_fin_fun] at hle
  exact ⟨h0, hle⟩

end HeisK

end CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.TableCRes

section Root

private theorem tcPSL_exists_primitive {F K : Type} [Field F] [Finite F] [Field K]
    [Algebra F K] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card Fˣ) :
    ∃ ζ : F, IsPrimitiveRoot (algebraMap F K ζ) p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hpF
  refine ⟨(g : F), ?_⟩
  have h1 : IsPrimitiveRoot (g : F) p := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hg]
  exact h1.map_of_injective (algebraMap F K).injective

theorem mem_range_algebraMap_of_pow_eq_one {F K : Type} [Field F] [Finite F] [Field K]
    [Algebra F K] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card Fˣ) {u : K} (hu : u ^ p = 1) :
    u ∈ (algebraMap F K).range := by
  obtain ⟨ζ, hζ⟩ := tcPSL_exists_primitive (F := F) (K := K) hp hpF
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hu
  exact RingHom.mem_range.mpr ⟨ζ ^ i, by rw [map_pow]; exact hi⟩

theorem mem_range_algebraMap_of_pow_eq_pow {F K : Type} [Field F] [Finite F] [Field K]
    [Algebra F K] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card Fˣ) {t : K} {μ : F}
    (ht : t ^ p = (algebraMap F K μ) ^ p) : t ∈ (algebraMap F K).range := by
  by_cases hμ : μ = 0
  · subst hμ
    have ht0 : t ^ p = 0 := by rw [ht, map_zero, zero_pow hp.ne_zero]
    have ht1 : t = 0 := (pow_eq_zero_iff hp.ne_zero).mp ht0
    rw [ht1]
    exact zero_mem _
  · have ha : algebraMap F K μ ≠ 0 := by
      intro h0
      exact hμ ((algebraMap F K).injective (h0.trans (map_zero (algebraMap F K)).symm))
    have hu : (t / algebraMap F K μ) ^ p = 1 := by
      rw [div_pow, ht, div_self (pow_ne_zero p ha)]
    obtain ⟨w, hw⟩ := RingHom.mem_range.mp
      (mem_range_algebraMap_of_pow_eq_one (F := F) (K := K) hp hpF hu)
    refine RingHom.mem_range.mpr ⟨w * μ, ?_⟩
    rw [map_mul, hw, div_mul_cancel₀ t ha]

end Root

section Count

private lemma tcPSL_index_le {G : Type*} [CommGroup G] [Finite G] (p : ℕ)
    (hK : Nat.card (powMonoidHom p : G →* G).ker ≤ p) (Fu : Subgroup G) :
    Fu ≤ Fu.comap (powMonoidHom p) ∧
      Nat.card (↥(Fu.comap (powMonoidHom p)) ⧸ Fu.subgroupOf (Fu.comap (powMonoidHom p))) ≤ p := by
  have hle : Fu ≤ Fu.comap (powMonoidHom p) := fun u hu => by
    rw [Subgroup.mem_comap, powMonoidHom_apply]
    exact Subgroup.pow_mem _ hu p
  refine ⟨hle, ?_⟩
  have hpow : ∀ x : ↥(Fu.comap (powMonoidHom p)), (powMonoidHom p) (x : G) ∈ Fu :=
    fun x => x.2
  let φ : ↥(Fu.comap (powMonoidHom p)) →* ↥Fu :=
    ((powMonoidHom p).comp (Fu.comap (powMonoidHom p)).subtype).codRestrict Fu hpow
  have hmem : ∀ x : φ.ker,
      ((x : ↥(Fu.comap (powMonoidHom p))) : G) ∈ (powMonoidHom p : G →* G).ker := by
    intro x
    rw [MonoidHom.mem_ker]
    have h1 : ((φ (x : ↥(Fu.comap (powMonoidHom p)))) : G) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    exact h1
  have hker : Nat.card φ.ker ≤ p := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : φ.ker => (⟨((x : ↥(Fu.comap (powMonoidHom p))) : G), hmem x⟩ :
        (powMonoidHom p : G →* G).ker)) ?_) hK
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    exact h2
  have hrange : Nat.card φ.range ≤ Nat.card Fu := Subgroup.card_le_card_group _
  have hidx : φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
  have hA : Nat.card φ.ker * φ.ker.index = Nat.card ↥(Fu.comap (powMonoidHom p)) :=
    Subgroup.card_mul_index _
  have hB : Nat.card (Fu.subgroupOf (Fu.comap (powMonoidHom p))) = Nat.card Fu :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hC : Nat.card (Fu.subgroupOf (Fu.comap (powMonoidHom p))) *
      (Fu.subgroupOf (Fu.comap (powMonoidHom p))).index =
        Nat.card ↥(Fu.comap (powMonoidHom p)) :=
    Subgroup.card_mul_index _
  have hpos : 0 < Nat.card Fu := Nat.card_pos
  show (Fu.subgroupOf (Fu.comap (powMonoidHom p))).index ≤ p
  refine le_of_mul_le_mul_right ?_ hpos
  calc (Fu.subgroupOf (Fu.comap (powMonoidHom p))).index * Nat.card Fu
      = Nat.card ↥(Fu.comap (powMonoidHom p)) := by rw [← hB, mul_comm]; exact hC
    _ = Nat.card φ.ker * φ.ker.index := hA.symm
    _ = Nat.card φ.ker * Nat.card φ.range := by rw [hidx]
    _ ≤ p * Nat.card Fu := Nat.mul_le_mul hker hrange

theorem card_quotient_powPreimage_le {F F' : Type} [Field F] [Field F'] [Algebra F F']
    [Finite F'] (p : ℕ) (hp : p.Prime) :
    ((Units.map (algebraMap F F' : F →* F')).range ≤
      (Units.map (algebraMap F F' : F →* F')).range.comap (powMonoidHom p)) ∧
    Nat.card (↥((Units.map (algebraMap F F' : F →* F')).range.comap (powMonoidHom p)) ⧸
      ((Units.map (algebraMap F F' : F →* F')).range).subgroupOf
        ((Units.map (algebraMap F F' : F →* F')).range.comap (powMonoidHom p))) ≤ p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hK : Nat.card (powMonoidHom p : F'ˣ →* F'ˣ).ker ≤ p := by
    rw [← rootsOfUnity_eq_ker]
    exact card_rootsOfUnity F' p
  exact tcPSL_index_le p hK _

end Count

section CoreAll

open CFSG.StandardType.ClassicalPosition

@[expose] def scalarEquiv (F V : Type) [Field F] [AddCommGroup V] [Module F V] :
    Fˣ →* (V ≃ₗ[F] V) where
  toFun u := LinearEquiv.smulOfUnit u
  map_one' := by ext v; simp [LinearEquiv.smulOfUnit]
  map_mul' u w := by ext v; simp [LinearEquiv.smulOfUnit, mul_smul]

theorem scalarEquiv_apply {F V : Type} [Field F] [AddCommGroup V] [Module F V] (u : Fˣ) (v : V) :
    scalarEquiv F V u v = (u : F) • v := rfl


section Core

variable {F K V ι : Type} [Field F] [Field K] [Algebra F K] [Finite K]
  [AddCommGroup V] [Module F V] [Module K V] [IsScalarTower F K V] [FiniteDimensional K V]

theorem card_le_pow_finrank {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0) [Finite ι]
    (g : ι → (V ≃ₗ[F] V))
    (hcomm : ∀ i j, g i * g j = g j * g i)
    (hK : ∀ i (c : K) (v : V), g i (c • v) = c • g i v)
    (hpow : ∀ i, ∃ u : Fˣ, g i ^ p = scalarEquiv F V u)
    (hinj : ∀ i j (u : Fˣ), g i = g j * scalarEquiv F V u → i = j) :
    Nat.card ι ≤ p ^ Module.finrank K V := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[F] V) :=
    Finite.of_injective (fun f : V ≃ₗ[F] V => (f : V → V)) DFunLike.coe_injective
  let T : Set (V ≃ₗ[F] V) := Set.range g ∪ Set.range (scalarEquiv F V)
  let E : Subgroup (V ≃ₗ[F] V) := Subgroup.closure T
  have hscal_comm : ∀ (u : Fˣ) (a : V ≃ₗ[F] V), a * scalarEquiv F V u = scalarEquiv F V u * a := by
    intro u a
    ext v
    simp [scalarEquiv_apply]
  have hTcomm : T.Pairwise Commute := by
    rintro a (⟨i, rfl⟩ | ⟨u, rfl⟩) b (⟨j, rfl⟩ | ⟨w, rfl⟩) _
    · exact hcomm i j
    · exact hscal_comm w (g i)
    · exact (hscal_comm u (g j)).symm
    · exact (Commute.all u w).map (scalarEquiv F V)
  have hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact hTcomm hx hy hxy
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => x * y = y * x)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
    · intro x y hx hy
      exact hTc x hx y hy
    · intro x hx
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz hxz hyz
      exact (Commute.mul_left (show Commute x z from hxz) (show Commute y z from hyz)).eq
    · intro x y z hx hy hz hzx hzy
      exact (Commute.mul_right (show Commute z x from hzx) (show Commute z y from hzy)).eq
    · intro x y hx hy hxy
      exact (Commute.inv_left (show Commute x y from hxy)).eq
    · intro x y hx hy hxy
      exact (Commute.inv_right (show Commute x y from hxy)).eq
  have hKE : ∀ a ∈ E, ∀ (c : K) (v : V), a (c • v) = c • a v := by
    intro a ha
    refine Subgroup.closure_induction (p := fun a _ => ∀ (c : K) (v : V), a (c • v) = c • a v)
      ?_ ?_ ?_ ?_ ha
    · rintro a (⟨i, rfl⟩ | ⟨u, rfl⟩)
      · exact hK i
      · intro c v
        simp only [scalarEquiv_apply]
        exact smul_comm _ _ _
    · intro c v
      simp
    · intro a b _ _ ha hb c v
      simp [LinearEquiv.mul_apply, hb, ha]
    · intro a _ ha c v
      apply a.injective
      simp [ha]
  have hpE : ∀ a ∈ E, ∃ u : Fˣ, a ^ p = scalarEquiv F V u := by
    intro a ha
    refine Subgroup.closure_induction (p := fun a _ => ∃ u : Fˣ, a ^ p = scalarEquiv F V u)
      ?_ ?_ ?_ ?_ ha
    · rintro a (⟨i, rfl⟩ | ⟨u, rfl⟩)
      · exact hpow i
      · exact ⟨u ^ p, by rw [map_pow]⟩
    · exact ⟨1, by simp⟩
    · rintro a b ha' hb' ⟨u, hu⟩ ⟨w, hw⟩
      refine ⟨u * w, ?_⟩
      rw [Commute.mul_pow (hEcomm a ha' b hb'), hu, hw, map_mul]
    · rintro a ha' ⟨u, hu⟩
      exact ⟨u⁻¹, by rw [inv_pow, hu, map_inv]⟩
  by_cases hV : Subsingleton V
  · have := hV
    have hsub : Subsingleton ι :=
      ⟨fun i j => hinj i j 1 (by ext v; exact Subsingleton.elim _ _)⟩
    have h1 : Nat.card ι ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have h0 : Module.finrank K V = 0 := Module.finrank_zero_of_subsingleton
    rw [h0, pow_zero]
    exact h1
  have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  have hnpos : 0 < Module.finrank K V := Module.finrank_pos
  let toK : ∀ a : V ≃ₗ[F] V, (∀ (c : K) (v : V), a (c • v) = c • a v) → (V ≃ₗ[K] V) :=
    fun a h =>
      { toFun := a, map_add' := a.map_add, map_smul' := fun c v => h c v, invFun := a.symm,
        left_inv := a.left_inv, right_inv := a.right_inv }
  let Φ : E →* (V ≃ₗ[K] V) :=
    { toFun := fun a => toK a.1 (hKE a.1 a.2)
      map_one' := by ext v; rfl
      map_mul' := by intro a b; ext v; rfl }
  have hΦapp : ∀ (a : E) (v : V), Φ a v = a.1 v := fun a v => rfl
  have hΦpow : ∀ a : E, Φ a ^ p ∈ HeisRank.scalarAut K V := by
    intro a
    obtain ⟨u, hu⟩ := hpE a.1 a.2
    refine ⟨algebraMap F K u, fun v => ?_⟩
    have h1 : (Φ a ^ p) v = (a.1 ^ p) v := by
      rw [← map_pow]
      rfl
    rw [h1, hu, scalarEquiv_apply, algebraMap_smul]
  have hΦc : ∀ a b : E, Φ a * Φ b = Φ b * Φ a := by
    intro a b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEcomm a.1 a.2 b.1 b.2)
  obtain ⟨-, hidx⟩ := index_scalarAut_le hpK Φ hΦpow hΦc
  let A₁ : Subgroup E := (HeisRank.scalarAut K V).comap Φ
  let A₀ : Subgroup E := (scalarEquiv F V).range.subgroupOf E
  have hA₀ : ∀ a : E, a ∈ A₀ ↔ ∃ u : Fˣ, scalarEquiv F V u = a.1 := fun a => by
    simp [A₀, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  have hA₀₁ : A₀ ≤ A₁ := by
    intro a ha
    obtain ⟨u, hu⟩ := (hA₀ a).mp ha
    refine ⟨algebraMap F K u, fun v => ?_⟩
    rw [hΦapp, ← hu, scalarEquiv_apply, algebraMap_smul]
  have huniq : ∀ c c' : K, (∀ v : V, c • v = c' • v) → c = c' := fun c c' h =>
    smul_left_injective K hv₀ (h v₀)
  have hex : ∀ a : A₁, ∃ c : K, ∀ v, a.1.1 v = c • v := fun a => a.2
  choose c hc using hex
  have hc_ne : ∀ a : A₁, c a ≠ 0 := by
    intro a h0
    apply hv₀
    apply a.1.1.injective
    rw [hc a v₀, h0, zero_smul, map_zero]
  have hc_pow : ∀ (a : A₁) (n : ℕ) (v : V), (a.1.1 ^ n) v = (c a) ^ n • v := by
    intro a n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ', LinearEquiv.mul_apply, ih v, hKE a.1.1 a.1.2, hc a v, smul_smul, pow_succ]
  have hc_one : c 1 = 1 := huniq _ _ (fun v => by
    rw [← hc (1 : A₁) v, one_smul]; rfl)
  have hc_mul : ∀ a b : A₁, c (a * b) = c a * c b := by
    intro a b
    apply huniq
    intro v
    have h1 : (a * b).1.1 v = a.1.1 (b.1.1 v) := rfl
    rw [← hc (a * b) v, h1, hc b v, hKE a.1.1 a.1.2, hc a v, smul_smul, mul_comm]
  let τ : A₁ →* Kˣ :=
    { toFun := fun a => Units.mk0 (c a) (hc_ne a)
      map_one' := Units.ext hc_one
      map_mul' := fun a b => Units.ext (hc_mul a b) }
  let Fu : Subgroup Kˣ := (Units.map (algebraMap F K : F →* K)).range
  let S : Subgroup Kˣ := Fu.comap (powMonoidHom p)
  obtain ⟨-, hT4⟩ := card_quotient_powPreimage_le (F := F) (F' := K) p hp
  have hτS : τ.range ≤ S := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨u, hu⟩ := hpE a.1.1 a.1.2
    show (τ a) ^ p ∈ Fu
    refine ⟨u, ?_⟩
    apply Units.ext
    show algebraMap F K (u : F) = (c a) ^ p
    apply huniq
    intro v
    have h1 := hc_pow a p v
    rw [hu, scalarEquiv_apply] at h1
    rw [algebraMap_smul, h1]
  have hker : Fu.comap τ = A₀.subgroupOf A₁ := by
    ext a
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hA₀]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      ext v
      have h1 : algebraMap F K (u : F) = c a := congrArg Units.val hu
      rw [scalarEquiv_apply, ← algebraMap_smul K (u : F) v, h1, hc a v]
    · rintro ⟨u, hu⟩
      refine ⟨u, ?_⟩
      apply Units.ext
      show algebraMap F K (u : F) = c a
      apply huniq
      intro v
      rw [algebraMap_smul, ← scalarEquiv_apply, hu, hc a v]
  have hrel : A₀.relIndex A₁ ≤ p := by
    have h1 : A₀.relIndex A₁ = (Fu.comap τ).index := by
      rw [hker]; rfl
    have hfin : Fu.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
    calc A₀.relIndex A₁ = (Fu.comap τ).index := h1
      _ = Fu.relIndex τ.range := Subgroup.index_comap Fu τ
      _ ≤ Fu.relIndex S := Subgroup.relIndex_le_of_le_right hτS hfin
      _ ≤ p := hT4
  have hinj' : Function.Injective
      (fun i => (QuotientGroup.mk (⟨g i, Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)⟩ : E) :
        E ⧸ A₀)) := by
    intro i j hij
    have h1 := QuotientGroup.eq.mp hij
    obtain ⟨u, hu⟩ := (hA₀ _).mp h1
    refine (hinj j i u ?_).symm
    have h2 : scalarEquiv F V u = (g i)⁻¹ * g j := hu
    rw [h2]
    group
  have hcard : Nat.card ι ≤ A₀.index := Nat.card_le_card_of_injective _ hinj'
  have hmul : A₀.relIndex A₁ * A₁.index = A₀.index := Subgroup.relIndex_mul_index hA₀₁
  calc Nat.card ι ≤ A₀.index := hcard
    _ = A₀.relIndex A₁ * A₁.index := hmul.symm
    _ ≤ p * p ^ (Module.finrank K V - 1) := Nat.mul_le_mul hrel hidx
    _ = p ^ Module.finrank K V := by
        rw [← pow_succ']
        congr 1
        omega

end Core

end CoreAll

end CFSG.StandardType.TableCRes
