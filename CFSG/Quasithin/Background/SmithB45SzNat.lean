module

public import CFSG.Quasithin.Background.SmithB45SzDesc
public import CFSG.Quasithin.Background.SmithB45SzMain
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Quasithin.Background.SmithB42Sp4Ident

public section

namespace CFSG.Quasithin

namespace B45Sz

open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Blueprint CFSG.LieType.Ree
open Representation Matrix

section RepOf

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]

abbrev repOfG (π : G →* (M ≃ₗ[ZMod 2] M)) : Representation (ZMod 2) G M :=
  (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := M)).comp π

theorem repOfG_apply (π : G →* (M ≃ₗ[ZMod 2] M)) (g : G) : repOfG π g = (π g).toLinearMap := rfl

end RepOf

section Index

variable {V : Type} [CommGroup V] {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem index_fixV_zpowers_eq (θ : V ≃* Multiplicative M) (t : MulAut V) :
    (fixV (Subgroup.zpowers t)).index =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range ((binPsi θ t).toLinearMap - 1)) := by
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hfix : Nat.card ↥(fixV (Subgroup.zpowers t)) =
      Nat.card (LinearMap.ker ((binPsi θ t).toLinearMap - 1)) := by
    refine Nat.card_congr
      { toFun := fun v => ⟨Multiplicative.toAdd (θ v.1), ?_⟩
        invFun := fun w => ⟨θ.symm (Multiplicative.ofAdd w.1), ?_⟩
        left_inv := fun v => by simp
        right_inv := fun w => by simp }
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
        LinearEquiv.coe_coe, CFSG.Quasithin.B42L2.toAdd_binPsi]
      rw [mem_fixV_zpowers_iff.mp v.2]
    · have hw := w.2
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
        LinearEquiv.coe_coe] at hw
      refine mem_fixV_zpowers_iff.mpr ?_
      apply θ.injective
      apply Multiplicative.toAdd.injective
      rw [← CFSG.Quasithin.B42L2.toAdd_binPsi, MulEquiv.apply_symm_apply, toAdd_ofAdd]
      exact hw
  have hV := (fixV (Subgroup.zpowers t)).card_mul_index
  rw [natCard_eq θ, hfix, natCard_eq_two_pow_finrank' M,
    natCard_eq_two_pow_finrank' (LinearMap.ker _)] at hV
  have hrn := LinearMap.finrank_range_add_finrank_ker ((binPsi θ t).toLinearMap - 1)
  have h2 : 2 ^ Module.finrank (ZMod 2) (LinearMap.ker ((binPsi θ t).toLinearMap - 1)) *
      (fixV (Subgroup.zpowers t)).index =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker ((binPsi θ t).toLinearMap - 1)) *
        2 ^ Module.finrank (ZMod 2) (LinearMap.range ((binPsi θ t).toLinearMap - 1)) := by
    rw [hV, ← pow_add, add_comm, hrn]
  exact Nat.eq_of_mul_eq_mul_left (pow_pos two_pos _) h2

end Index

section Small

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem three_mul_le_half {m : ℕ} (hm : 2 ≤ m) : 3 * m ≤ (4 ^ m - 2 ^ m) / 2 := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 2 ^ m ≤ 4 ^ m := Nat.pow_le_pow_left (by norm_num) m
    have h4 : 4 ^ (m + 1) = 4 * 4 ^ m := by ring
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have h3 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [h4, h2]
    omega

theorem sz_finrank_eq_four_of_small
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M))
    [Fact (repOfG π).IsIrreducible] (hnt : ∃ g, repOfG π g ≠ 1) {t : ↥(suzukiGroup a K)}
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (repOfG π t - 1)) ≤ 2 * (2 * a + 1)) :
    Module.finrank (EndRing (repOfG π)) M = 4 := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sz_descent hK hnt
  have : Module.Finite (EndRing (repOfG π)) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιK, ιD, A, hAne, hA, ⟨Φ⟩, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing (repOfG π)) M)
  let _ : Algebra K E := ιK.toAlgebra
  have hdimκ : Module.finrank (EndRing (repOfG π)) M = Fintype.card (↥A → Fin 4) := by
    rw [hdimW]
    simp
  have hdisp := finrank_range_eq_gen hDcard (Module.finBasis (EndRing (repOfG π)) M) ιD
    (szT E hK A) Φ hdimκ t
  have hfd := le_card_mul_of_shiftSet hA hAne hd1 hshift
  by_contra hne
  have hm2 : 2 ≤ A.card := by
    have h1 : 1 ≤ A.card := Finset.card_pos.mpr hAne
    by_contra h
    have h2 : A.card = 1 := by omega
    rw [h2, pow_one] at hdimW
    exact hne hdimW
  have hz2 : szIncl hK t * szIncl hK t = 1 := by rw [← map_mul, ht2, map_one]
  have hz1 : szIncl hK t ≠ 1 := fun h => ht1 (szIncl_injective hK (h.trans (map_one _).symm))
  have hrank := rank_tensorRepS_sub_one_ge (F := K) E A hz2 hz1
  have h3 := three_mul_le_half hm2
  have hr : (szT E hK A t - 1).rank = (tensorRepS (F := K) E A (szIncl hK t) - 1).rank := rfl
  rw [hdisp, hr] at hsmall
  have h4 : 3 * (2 * a + 1) ≤ d * (tensorRepS (F := K) E A (szIncl hK t) - 1).rank := by
    calc 3 * (2 * a + 1) ≤ 3 * (A.card * d) := Nat.mul_le_mul_left 3 hfd
      _ = d * (3 * A.card) := by ring
      _ ≤ d * (tensorRepS (F := K) E A (szIncl hK t) - 1).rank :=
        Nat.mul_le_mul_left d (h3.trans hrank)
  omega

end Small

section Four

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

theorem glMat_minorAut_two_mul (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : ℕ)
    (g : ↥(suzukiGroup a K)) :
    glMat (((minorAut K ^ (2 * c)) (szIncl hK g) : antiSp K) : GL (Fin 4) K) =
      (glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ c) := by
  have h := B42Sp4.natRepS_add_two_mul_pow (F := K) K 0 c (szIncl hK g)
  rw [zero_add, natRepS_apply, natRepS_apply, pow_zero, MulAut.one_apply] at h
  simpa [Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, coe_szIncl] using h

theorem surjective_of_coords {G : Type} [Group G] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (π : G →* (M ≃ₗ[ZMod 2] M))
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {K D : Type} [Field K] [Field D] (ι : K →+* D) {n : ℕ} (i₀ : Fin n)
    (R : G → Matrix (Fin n) (Fin n) K) (θ : M ≃+ (Fin n → D))
    (hact : ∀ g w j, θ (π g w) j = ∑ c, ι (R g j c) * θ w c) : Function.Surjective ι := by
  classical
  let U₀ : AddSubgroup M :=
    { carrier := {w | ∀ j, θ w j ∈ ι.range}
      add_mem' := fun {x y} hx hy j => by
        rw [map_add, Pi.add_apply]
        exact ι.range.add_mem (hx j) (hy j)
      zero_mem' := fun j => by
        rw [map_zero, Pi.zero_apply]
        exact ι.range.zero_mem
      neg_mem' := fun {x} hx j => by
        rw [map_neg, Pi.neg_apply]
        exact ι.range.neg_mem (hx j) }
  let U : Submodule (ZMod 2) M := AddSubgroup.toZModSubmodule 2 U₀
  have hU : ∀ g, ∀ u ∈ U, π g u ∈ U := by
    intro g u hu j
    rw [hact]
    exact ι.range.sum_mem fun c _ => ι.range.mul_mem ⟨_, rfl⟩ (hu c)
  have hne : θ.symm (Pi.single i₀ 1) ∈ U := by
    intro j
    rw [AddEquiv.apply_symm_apply]
    by_cases hj : j = i₀
    · subst hj
      exact ⟨1, by rw [Pi.single_eq_same, map_one]⟩
    · exact ⟨0, by rw [Pi.single_eq_of_ne hj, map_zero]⟩
  rcases hirr U hU with h | h
  · exfalso
    have h1 : θ.symm (Pi.single i₀ 1) = 0 := by
      have := hne
      rw [h] at this
      exact (Submodule.mem_bot _).mp this
    have h2 := congrArg (fun w => θ w i₀) h1
    simp only [AddEquiv.apply_symm_apply, map_zero, Pi.zero_apply, Pi.single_eq_same] at h2
    exact one_ne_zero h2
  · intro x
    have hx : θ.symm (Pi.single i₀ x) ∈ U := by rw [h]; exact Submodule.mem_top
    have := hx i₀
    rw [AddEquiv.apply_symm_apply, Pi.single_eq_same] at this
    obtain ⟨y, hy⟩ := this
    exact ⟨y, hy⟩

theorem exists_coords_of_surjective {G : Type} [Group G] {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (π : G →* (M ≃ₗ[ZMod 2] M)) {K D : Type} [Field K] [Field D]
    (ι : K →+* D) (hι : Function.Surjective ι) {n : ℕ} (R : G → Matrix (Fin n) (Fin n) K)
    (θ : M ≃+ (Fin n → D)) (hact : ∀ g w j, θ (π g w) j = ∑ c, ι (R g j c) * θ w c) :
    ∃ φ : M ≃+ (Fin n → K), ∀ g w, φ (π g w) = (R g).mulVec (φ w) := by
  let κ : D ≃+* K := (RingEquiv.ofBijective ι ⟨ι.injective, hι⟩).symm
  have hκ' : ∀ y : D, ι (κ y) = y := fun y =>
    (RingEquiv.ofBijective ι ⟨ι.injective, hι⟩).apply_symm_apply y
  obtain ⟨φ, hφ⟩ : ∃ φ : M ≃+ (Fin n → K), ∀ w j, ι (φ w j) = θ w j :=
    ⟨θ.trans (AddEquiv.piCongrRight fun _ : Fin n => κ.toAddEquiv), fun w j => hκ' (θ w j)⟩
  refine ⟨φ, fun g w => ?_⟩
  funext j
  apply ι.injective
  have e : ((R g).mulVec (φ w)) j = ∑ c, R g j c * φ w c := rfl
  rw [hφ, hact, e, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_mul, hφ]

theorem sz_coords_of_four
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M))
    [Fact (repOfG π).IsIrreducible] (hnt : ∃ g, repOfG π g ≠ 1)
    (hdim : Module.finrank (EndRing (repOfG π)) M = 4) :
    ∃ (c : ℕ) (ι : K →+* EndRing (repOfG π)) (θ : M ≃+ (Fin 4 → EndRing (repOfG π))),
      ∀ g w j, θ (π g w) j =
        ∑ c', ι (((glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ c)) j c') * θ w c' := by
  classical
  set ρ := repOfG π with hρ
  obtain ⟨d, hd1, hDcard, hdesc⟩ := sz_descent hK hnt
  have hfinD : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  have hchar : CharP (EndRing ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing ρ)).injective 2
  obtain ⟨E, _, _, _, ιK, ιD, A, hAne, hA, -, hshift, hdimW⟩ :=
    hdesc (Module.finBasis (EndRing ρ) M)
  have hS1 : A.card = 1 := by
    rw [hdim] at hdimW
    have h := (Nat.pow_right_injective (le_refl 2) (by
      rw [show (2 : ℕ) ^ (2 * A.card) = 4 ^ A.card by rw [pow_mul]; norm_num]
      rw [← hdimW]; norm_num : 2 ^ (2 * A.card) = 2 ^ 2))
    omega
  obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp hS1
  have hi₀ : i₀ < 2 * (2 * a + 1) :=
    Finset.mem_range.mp (szOmega_subset (hA (Finset.mem_singleton_self i₀)))
  have hfd : 2 * a + 1 ∣ d := B42Sp4.dvd_of_shiftSet_singleton hi₀ hshift
  obtain ⟨ιK'⟩ := B42Sp4.exists_ringHom_of_dvd hK hDcard hfd
  let _ : Algebra K (EndRing ρ) := ιK'.toAlgebra
  let b : Module.Basis (Fin 4) (EndRing ρ) M := Module.finBasisOfFinrankEq (EndRing ρ) M hdim
  obtain ⟨A', -, hA', ⟨Φ⟩, hdim'⟩ := sz_exists_label hK hnt b ιK' (RingHom.id (EndRing ρ))
  have hS'1 : A'.card = 1 := by
    have h := (Nat.pow_right_injective (le_refl 2) (by
      rw [show (2 : ℕ) ^ (2 * A'.card) = 4 ^ A'.card by rw [pow_mul]; norm_num]
      rw [← hdim']; norm_num : 2 ^ (2 * A'.card) = 2 ^ 2))
    omega
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS'1
  obtain ⟨c, -, rfl⟩ := mem_szOmega.mp (hA' (Finset.mem_singleton_self i))
  obtain ⟨θ, hθ⟩ : ∃ θ : M ≃+ (Fin 4 → EndRing ρ),
      ∀ w a, θ w a = Φ.symm (b.equivFun w) (fun _ => a) :=
    ⟨(b.equivFun.toAddEquiv.trans Φ.symm.toLinearEquiv.toAddEquiv).trans
      (LinearEquiv.funCongrLeft (EndRing ρ) (EndRing ρ)
        (Equiv.funUnique ↥({2 * c} : Finset ℕ) (Fin 4)).symm).toAddEquiv, fun w a => rfl⟩
  have hcoord : ∀ (g : ↥(suzukiGroup a K)) (w : M), b.equivFun (ρ g w) =
      matRepE b (RingHom.id (EndRing ρ)) g (b.equivFun w) := by
    intro g w
    rw [matRepE_apply]
    have := LinearMap.toMatrix_mulVec_repr b b (repD ρ g) w
    rw [repD_apply] at this
    simpa [CFSG.QuasithinUnique.Setup.SL2Modules.matRep] using this.symm
  refine ⟨c, ιK', θ, fun g w j => ?_⟩
  have h1 : θ (π g w) j = θ (ρ g w) j := rfl
  rw [h1, hθ, hcoord, equiv_apply Φ.symm g, CFSG.QuasithinUnique.Setup.X7.matRep_apply,
    szT_apply, B42Sp4.tensorRepS_singleton_mulVec]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [natRepS_apply, Matrix.map_apply, hθ, glMat_minorAut_two_mul hK c g]
  rfl

theorem sz_exists_natural_of_four
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M))
    [Fact (repOfG π).IsIrreducible] (hnt : ∃ g, repOfG π g ≠ 1)
    (hdim : Module.finrank (EndRing (repOfG π)) M = 4) :
    ∃ (c : ℕ) (φ : M ≃+ (Fin 4 → K)), ∀ g w,
      φ (π g w) = ((glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ c)).mulVec (φ w) := by
  obtain ⟨c, ι, θ, hact⟩ := sz_coords_of_four hK π hnt hdim
  obtain ⟨-, hirr⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOfG π)).mp Fact.out
  have hsurj := surjective_of_coords π (fun U hU => hirr U hU) ι 0
    (fun g => (glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ c)) θ hact
  obtain ⟨φ, hφ⟩ := exists_coords_of_surjective π ι hsurj
    (fun g => (glMat (g : GL (Fin 4) K)).map (· ^ 2 ^ c)) θ hact
  exact ⟨c, φ, hφ⟩

end Four

section Real

variable {V : Type} [CommGroup V]

theorem binaryNaturalSz_of_coords {M : Type} [AddCommGroup M]
    [Module (ZMod 2) M] (θ : V ≃* Multiplicative M) {L : Subgroup (MulAut V)} {a : ℕ}
    (ha : 1 ≤ a) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (θL : ↥L ≃* ↥(suzukiGroup a K)) (φ : M ≃+ (Fin 4 → K))
    (hφ : ∀ (g : ↥(suzukiGroup a K)) (w : M),
      φ (binPsi θ ((θL.symm g : ↥L) : MulAut V) w) = (glMat (g : GL (Fin 4) K)).mulVec (φ w)) :
    BinaryNaturalSz L ⊤ ⊥ (2 * a + 1) := by
  let β : V →* Multiplicative (Fin 4 → K) :=
    { toFun := fun v => Multiplicative.ofAdd (φ (Multiplicative.toAdd (θ v)))
      map_one' := by
        apply Multiplicative.toAdd.injective
        simp
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp }
  refine ⟨a, ha, rfl, K, inferInstance, inferInstance, hK, θL.symm.toMonoidHom, ?_⟩
  refine G64.realizesVia_nat_of θL.symm.surjective le_top (fun _ _ _ => trivial)
    (fun h z hz => by
      rw [Subgroup.mem_bot] at hz ⊢
      rw [hz, map_one])
    (β.comp (⊤ : Subgroup V).subtype) ?_ ?_ ?_
  · intro y
    refine ⟨⟨θ.symm (Multiplicative.ofAdd (φ.symm (Multiplicative.toAdd y))), trivial⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    simp [β]
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h1
      have h3 : φ (Multiplicative.toAdd (θ u)) = 0 := congrArg Multiplicative.toAdd h1
      have h4 : Multiplicative.toAdd (θ u) = 0 := by
        rw [← map_zero φ] at h3
        exact φ.injective h3
      have h5 : θ u = 1 := Multiplicative.toAdd.injective h4
      simpa using congrArg θ.symm h5
    · intro h1
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, h1, map_one]
  · intro γ u hu
    apply Multiplicative.toAdd.injective
    have hθ : Multiplicative.toAdd (θ (((θL.symm.toMonoidHom γ : ↥L) : MulAut V) (u : V))) =
        binPsi θ ((θL.symm γ : ↥L) : MulAut V) (Multiplicative.toAdd (θ u)) := by
      rw [B42L2.toAdd_binPsi]
      rfl
    show φ (Multiplicative.toAdd (θ (((θL.symm.toMonoidHom γ : ↥L) : MulAut V) (u : V)))) =
      ((γ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *ᵥ φ (Multiplicative.toAdd (θ u))
    rw [hθ, hφ]

end Real

end B45Sz

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Blueprint B45Sz in
theorem szNaturalOfSmallDisplacement_holds :
    SzNaturalOfSmallDisplacement := by
  classical
  intro a ha K _ _ hK W _ _ hW L hperf hirr ⟨α⟩ ⟨t, htL, ht2, ht1, hidx⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := CFSG.QuasithinUnique.Setup.X7b.charP_two_of_card_pow hK
  have hntW : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply ht1
    ext x
    exact Subsingleton.elim _ _
  obtain ⟨-, hbij, -, -, -⟩ := Setup.Family.suzuki_irreducible_normalizer_excludes a ha hK W hW
    L hperf hirr α
  let θL : ↥L ≃* ↥(suzukiGroup a K) :=
    MulEquiv.ofBijective (α.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) hbij
  obtain ⟨M, _, _, _, ⟨θ⟩⟩ := exists_binModel_of_binary hW
  set ψ := binPsi θ with hψ
  let π : ↥(suzukiGroup a K) →* (M ≃ₗ[ZMod 2] M) :=
    ψ.toMonoidHom.comp (L.subtype.comp θL.symm.toMonoidHom)
  have hπ : ∀ g, π g = ψ ((θL.symm g : ↥L) : MulAut W) := fun g => rfl
  have hirrM : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, repOfG π g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine B42L2.irr_map θ hirr U fun x hx u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hx
    have h1 := hU (θL ⟨l, hl⟩) u hu
    rwa [repOfG_apply, hπ, MulEquiv.symm_apply_apply] at h1
  have hntM : Nontrivial M := by
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    refine ⟨⟨Multiplicative.toAdd (θ w), 0, fun h => hw ?_⟩⟩
    have h1 : θ w = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  have : Fact (repOfG π).IsIrreducible :=
    ⟨(CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff (repOfG π)).mpr ⟨hntM, hirrM⟩⟩
  set t₀ : ↥(suzukiGroup a K) := θL ⟨t, htL⟩ with ht₀
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [ht₀, ← map_mul]
    have : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have ht₀1 : t₀ ≠ 1 := by
    intro h
    apply ht1
    have := congrArg (fun g => ((θL.symm g : ↥L) : MulAut W)) h
    simpa [ht₀] using this
  have hπt : π t₀ = ψ t := by rw [hπ, ht₀, MulEquiv.symm_apply_apply]
  have hnt : ∃ g, repOfG π g ≠ 1 := by
    refine ⟨t₀, fun h => ht1 ?_⟩
    have h1 : π t₀ = 1 := LinearEquiv.toLinearMap_injective (by rw [← repOfG_apply, h]; rfl)
    rw [hπt] at h1
    exact ψ.injective (h1.trans (map_one ψ).symm)
  have hsmall : Module.finrank (ZMod 2) (LinearMap.range (repOfG π t₀ - 1)) ≤
      2 * (2 * a + 1) := by
    rw [index_fixV_zpowers_eq θ t] at hidx
    rw [repOfG_apply, hπt]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hidx
  have hdim := sz_finrank_eq_four_of_small hK π hnt ht₀2 ht₀1 hsmall
  obtain ⟨c, φ, hφ⟩ := sz_exists_natural_of_four hK π hnt hdim
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 c
  let φ' : M ≃+ (Fin 4 → K) := φ.trans (AddEquiv.piCongrRight fun _ : Fin 4 => σ.symm.toAddEquiv)
  refine binaryNaturalSz_of_coords θ ha hK θL φ' fun g w => ?_
  funext j
  have h1 := congrFun (hφ g w) j
  rw [← hπ] at *
  show σ.symm (φ (π g w) j) = _
  rw [h1, Matrix.mulVec, dotProduct, map_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [map_mul, Matrix.map_apply]
  have hσ : σ.symm (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j c' ^ 2 ^ c) =
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j c' := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [hσ]
  rfl

theorem asB45Sz_holds : AsB45Sz :=
  asB45Sz_of_natural szNaturalOfSmallDisplacement_holds

end CFSG.Quasithin
