module

import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpOuterWord
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpOuterField
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL28
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
import CFSG.Quasithin.Background.SmithB42L2Sl2
import CFSG.HardMathSupport.Kantor79.CommutatorSpace
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpArith
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpDescent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

private theorem w135c2_spEven_finrank_eq_mQuot {W : Type} [CommGroup W] [Finite W] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (θ : W ≃* Multiplicative V) (g : MulAut W) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((CFSG.QuasithinUnique.Setup.Layer.binPsi θ g : V →ₗ[ZMod 2] V) - 1)) =
      E3.mQuot ⊤ (fixV (Subgroup.zpowers g)) := by
  have hlin : ∀ w : W, θ (g w) = Multiplicative.ofAdd
      (CFSG.QuasithinUnique.Setup.Layer.binPsi θ g (Multiplicative.toAdd (θ w))) := by
    intro w
    rw [CFSG.Quasithin.B42L2.toAdd_binPsi]
    simp
  have heq := finL28_two_pow_mQuot_eq_card_range θ g
    (CFSG.QuasithinUnique.Setup.Layer.binPsi θ g) hlin
  have hcard : Nat.card (LinearMap.range
      ((CFSG.QuasithinUnique.Setup.Layer.binPsi θ g : V →ₗ[ZMod 2] V) - 1)) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.range
        ((CFSG.QuasithinUnique.Setup.Layer.binPsi θ g : V →ₗ[ZMod 2] V) - 1)) := by
    refine letI : Module.Finite (ZMod 2) (LinearMap.range
        ((CFSG.QuasithinUnique.Setup.Layer.binPsi θ g : V →ₗ[ZMod 2] V) - 1)) :=
      Module.Finite.of_finite; ?_
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard] at heq
  exact (Nat.pow_right_injective (le_refl 2) heq).symm

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
private theorem w135c2_spEven_pair_eq {W : Type} [CommGroup W] {F : Type} [Field F] {n : ℕ}
    {L : Subgroup (MulAut W)} (e : StatedSp n F ≃* ↥L) (σ : F ≃+* F) {t : MulAut W}
    (ht : t * t = 1)
    (he : ∀ y, t * ((e y : ↥L) : MulAut W) * t⁻¹ = ((e (fieldSp n F σ y) : ↥L) : MulAut W))
    (a b : StatedSp n F) :
    (((e a : ↥L) : MulAut W))⁻¹ * t * ((e a : ↥L) : MulAut W) *
        (((e b : ↥L) : MulAut W))⁻¹ * t * ((e b : ↥L) : MulAut W) =
      ((e (a⁻¹ * fieldSp n F σ (a * b⁻¹) * b) : ↥L) : MulAut W) := by
  let φ : StatedSp n F →* MulAut W := (Subgroup.subtype L).comp e.toMonoidHom
  have he' : ∀ y, t * φ y * t⁻¹ = φ (fieldSp n F σ y) := fun y => he y
  change (φ a)⁻¹ * t * φ a * (φ b)⁻¹ * t * φ b =
    φ (a⁻¹ * fieldSp n F σ (a * b⁻¹) * b)
  have hexp : ∀ y, φ (a⁻¹ * y * b) = (φ a)⁻¹ * φ y * φ b := by
    intro y
    rw [map_mul, map_mul, map_inv]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hexp, ← he' (a * b⁻¹), map_mul, map_inv, htinv]
  group

private theorem w135c2_spEven_finrank_le {W : Type} [CommGroup W] [Finite W] {V : Type}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (θ : W ≃* Multiplicative V)
    (t : MulAut W) (c : Fin 3 → MulAut W) :
    ∀ i, Module.finrank (ZMod 2) (LinearMap.range
      ((CFSG.QuasithinUnique.Setup.Layer.binPsi θ ((c i)⁻¹ * t * c i) :
        V →ₗ[ZMod 2] V) - 1)) ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  intro i
  have hconj : E3.mQuot ⊤ (fixV (Subgroup.zpowers ((c i)⁻¹ * t * c i))) =
      E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
    rw [show (c i)⁻¹ * t * c i = (c i)⁻¹ * t * ((c i)⁻¹)⁻¹ by rw [inv_inv],
      w135c2_mQuot_conj]
  rw [w135c2_spEven_finrank_eq_mQuot, hconj]

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp) in
private theorem w135c2_spEven_pairWord_eq {W : Type} [CommGroup W] {F : Type} [Field F]
    {n : ℕ} {L : Subgroup (MulAut W)} (e : StatedSp n F ≃* ↥L) (σ : F ≃+* F) {t : MulAut W}
    (ht : t * t = 1)
    (he : ∀ y, t * ((e y : ↥L) : MulAut W) * t⁻¹ = ((e (fieldSp n F σ y) : ↥L) : MulAut W))
    (k : Fin 3 → StatedSp n F) (ps : List (Fin 3 × Fin 3)) :
    (ps.map fun p =>
        (((e (k p.1) : ↥L) : MulAut W))⁻¹ * t * ((e (k p.1) : ↥L) : MulAut W) *
          (((e (k p.2) : ↥L) : MulAut W))⁻¹ * t * ((e (k p.2) : ↥L) : MulAut W)).prod =
      ((e (ps.map fun p => (k p.1)⁻¹ * fieldSp n F σ (k p.1 * (k p.2)⁻¹) * k p.2).prod :
        ↥L) : MulAut W) := by
  let φ : StatedSp n F →* MulAut W := (Subgroup.subtype L).comp e.toMonoidHom
  have h1 : (ps.map fun p =>
        (((e (k p.1) : ↥L) : MulAut W))⁻¹ * t * ((e (k p.1) : ↥L) : MulAut W) *
          (((e (k p.2) : ↥L) : MulAut W))⁻¹ * t * ((e (k p.2) : ↥L) : MulAut W)) =
      (ps.map fun p => (k p.1)⁻¹ * fieldSp n F σ (k p.1 * (k p.2)⁻¹) * k p.2).map φ := by
    rw [List.map_map]
    apply List.map_congr_left
    intro p _
    exact w135c2_spEven_pair_eq e σ ht he (k p.1) (k p.2)
  rw [h1, ← map_list_prod φ]
  rfl

private theorem w135c2_spEven_word_mem {W : Type} [CommGroup W] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] (B : MulAut W ≃* (V ≃ₗ[ZMod 2] V)) (c : Fin 3 → MulAut W)
    (t : MulAut W) (ps : List (Fin 3 × Fin 3)) (X : MulAut W)
    (hXdef : X = (ps.map fun p => ((c p.1)⁻¹ * t * c p.1) *
      ((c p.2)⁻¹ * t * c p.2)).prod) :
    B X ∈ Subgroup.closure (Set.range fun i => B ((c i)⁻¹ * t * c i)) := by
  have hX' : B X = (ps.map fun p => B ((c p.1)⁻¹ * t * c p.1) *
      B ((c p.2)⁻¹ * t * c p.2)).prod := by
    rw [hXdef, map_list_prod B, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    change B (((c p.1)⁻¹ * t * c p.1) * ((c p.2)⁻¹ * t * c p.2)) =
      B ((c p.1)⁻¹ * t * c p.1) * B ((c p.2)⁻¹ * t * c p.2)
    rw [map_mul]
  rw [hX']
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
  exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨p.1, rfl⟩)
    (Subgroup.subset_closure ⟨p.2, rfl⟩)

private theorem w135c2_spEven_le_six_and_involution
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (htL : t ∉ L) (ht2 : orderOf t = 2) {n f : ℕ}
    (hn : 3 ≤ n) (hf : 2 ≤ f) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f)
    (hle : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {F : Type} [Field F]
    (hF : Nat.card F = 2 ^ f) {σ : F ≃+* F} (hσ : orderOf σ = 2) :
    f ≤ 6 ∧ Even f ∧ (∀ c, σ c = c ^ 2 ^ (f / 2)) := by
  have hf6 : f ≤ 6 := by
    have h := w135c2_sp_outer_le_two_mul hW hctx htY htL ht2 hn hlie
    omega
  have hσσ : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  obtain ⟨hfe, hσc, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.ringEquiv_involution_facts
      (one_le_two.trans hf) hF hσσ hσ1
  exact ⟨hf6, hfe, hσc⟩

theorem w135c2_orderOf_ne_thirteen_of_mem_closure {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (t : Fin 3 → V ≃ₗ[ZMod 2] V)
    (ht : ∀ i, Module.finrank (ZMod 2) (LinearMap.range ((t i : V →ₗ[ZMod 2] V) - 1)) ≤ 3)
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ Subgroup.closure (Set.range t)) : orderOf x ≠ 13 := by
  intro h13
  have hH := CFSG.HardMathSupport.Kantor79.finrank_commutatorSpace_le t ht
  have hle := Submodule.finrank_mono
    (CFSG.HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hx)
  have hdvd := CFSG.RankThree.GF2n.Stroth80.orderOf_card_dvd_finrank_range (K := ZMod 2)
    (by norm_num : Nat.Prime 13) (by norm_num) h13
  rw [Nat.card_zmod, Nat.cast_ofNat,
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.orderOf_two_zmod_thirteen] at hdvd
  have hne : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h13
    omega
  have hpos := CFSG.RankThree.GF2n.Stroth80.finrank_range_sub_one_pos hne
  have h12 : 12 ≤ Module.finrank (ZMod 2) (LinearMap.range ((x : V →ₗ[ZMod 2] V) - 1)) :=
    Nat.le_of_dvd hpos hdvd
  have h9 : Module.finrank (ZMod 2) (LinearMap.range ((x : V →ₗ[ZMod 2] V) - 1)) ≤ 9 :=
    hle.trans (by simpa using hH)
  omega

theorem w135c2_sp_outer_four_le
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (htL : t ∉ L) (ht2 : orderOf t = 2) {n f : ℕ}
    (hn : 3 ≤ n) (hf : 2 ≤ f) (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSp n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  by_contra hm
  have hm3 : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 := by omega
  obtain ⟨F, instF, instFin, hF, e, σ, hσ, he⟩ :=
    w135c2_sp_exists_fieldSp_of_not_mem hctx htY htL ht2 hn hlie
  obtain ⟨hf6, hfe, hσc⟩ :=
    w135c2_spEven_le_six_and_involution hW hctx htY htL ht2 hn hf hlie hm3 hF hσ
  obtain ⟨k, ps, hord⟩ :=
    w135c2_sp_exists_pairWord_orderOf_eq_thirteen hn hF hfe hf6 hσc
  obtain ⟨V, _, _, _, ⟨θ⟩⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.Actor.exists_binModel_of_binary (V := W)
      (fun w => by rw [← pow_two]; exact hW w)
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  let B : MulAut W ≃* (V ≃ₗ[ZMod 2] V) := CFSG.QuasithinUnique.Setup.Layer.binPsi θ
  let c : Fin 3 → MulAut W := fun i => ((e (k i) : ↥L) : MulAut W)
  let T : Fin 3 → V ≃ₗ[ZMod 2] V := fun i => B ((c i)⁻¹ * t * c i)
  have hT : ∀ i, Module.finrank (ZMod 2)
      (LinearMap.range ((T i : V →ₗ[ZMod 2] V) - 1)) ≤ 3 := by
    intro i
    change Module.finrank (ZMod 2) (LinearMap.range
      ((CFSG.QuasithinUnique.Setup.Layer.binPsi θ ((c i)⁻¹ * t * c i) :
        V →ₗ[ZMod 2] V) - 1)) ≤ 3
    exact (w135c2_spEven_finrank_le θ t c i).trans hm3
  set X : MulAut W :=
    (ps.map fun p => ((c p.1)⁻¹ * t * c p.1) *
      ((c p.2)⁻¹ * t * c p.2)).prod with hXdef
  have hX : X = ((e (ps.map fun p =>
      (k p.1)⁻¹ * CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n F σ
        (k p.1 * (k p.2)⁻¹) * k p.2).prod : ↥L) : MulAut W) := by
    rw [hXdef]
    exact w135c2_spEven_pairWord_eq e σ htt he k ps
  have hmem : B X ∈ Subgroup.closure (Set.range T) := by
    change B X ∈ Subgroup.closure (Set.range fun i => B ((c i)⁻¹ * t * c i))
    exact w135c2_spEven_word_mem B c t ps X hXdef
  have hord' : orderOf (B X) = 13 := by
    rw [MulEquiv.orderOf_eq, hX, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
  exact w135c2_orderOf_ne_thirteen_of_mem_closure T hT hmem hord'

end CFSG.LocalAnalysis.WeakClosure81
