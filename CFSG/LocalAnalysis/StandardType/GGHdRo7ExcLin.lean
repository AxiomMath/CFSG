module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylAutInner
public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.Blueprint.Chevalley
public import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeAct
public import CFSG.LieType.Chevalley.RootCommutatorData

open CFSG.StandardType
open CFSG.RankThree.CentralCover
open Multiplicative
open CFSG.LieType.Chevalley hiding cartanFunctional cartanFunctional_apply cartanFunctional_single
open CFSG.Blueprint.Chevalley

public section

local instance instAddCommGroupZModThreeHdRo7ExcLin : AddCommGroup (ZMod 3) := Ring.toAddCommGroup

namespace CFSG.StandardType

theorem cartanE_connected_free (r : ℕ) (hr : 4 ≤ r) (i j : Fin r) :
    Relation.ReflTransGen
      (fun a b : Fin r => Tag.cartanE r a b = -1 ∧ Tag.cartanE r b a = -1) i j := by
  set R := (fun a b : Fin r => Tag.cartanE r a b = -1 ∧ Tag.cartanE r b a = -1) with hR
  have hsymm : Symmetric R := fun a b h => ⟨h.2, h.1⟩
  have hpath : ∀ k (hk : 2 + k < r),
      Relation.ReflTransGen R ⟨2, by omega⟩ ⟨2 + k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro hk
      refine Relation.ReflTransGen.tail (ih (by omega)) ?_
      have hne : ¬ (2 + k = 2 + (k + 1)) := by omega
      have hne' : ¬ (2 + (k + 1) = 2 + k) := by omega
      constructor
      · simp only [Tag.cartanE, Fin.mk.injEq, hne, if_false]
        rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))]
      · simp only [Tag.cartanE, Fin.mk.injEq, hne', if_false]
        rw [if_pos (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))]
  have h02 : R ⟨0, by omega⟩ ⟨2, by omega⟩ := by
    constructor <;> simp [Tag.cartanE]
  have h13 : R ⟨1, by omega⟩ ⟨3, by omega⟩ := by
    constructor <;> simp [Tag.cartanE]
  have h2 : ∀ i : Fin r, Relation.ReflTransGen R ⟨2, by omega⟩ i := by
    intro i
    obtain ⟨v, hv⟩ := i
    rcases (by omega : v = 0 ∨ v = 1 ∨ 2 ≤ v) with rfl | rfl | h
    · exact Relation.ReflTransGen.single (hsymm h02)
    · exact (hpath 1 (by omega)).tail (hsymm h13)
    · obtain ⟨k, rfl⟩ : ∃ k, v = 2 + k := ⟨v - 2, by omega⟩
      exact hpath k hv
  have hsymm' : ∀ a b, Relation.ReflTransGen R a b → Relation.ReflTransGen R b a := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm hbc) ih
  exact (hsymm' _ _ (h2 i)).trans (h2 j)

theorem cartan_connected_free_E7E8 {τ : Tag}
    (hτ : τ = Tag.E7 ∨ τ = Tag.E8) (i j : Fin τ.rank) :
    Relation.ReflTransGen
      (fun a b : Fin τ.rank => τ.cartan a b = -1 ∧ τ.cartan b a = -1) i j := by
  rcases hτ with rfl | rfl
  · exact cartanE_connected_free 7 (by norm_num) i j
  · exact cartanE_connected_free 8 (by norm_num) i j

noncomputable def reflLin {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (c : V →ₗ[ZMod 3] ZMod 3) (δ : V) (h : c δ = 2) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofLinear (Module.reflection (f := c) (x := δ) h)
    (Module.reflection (f := c) (x := δ) h)
    (LinearMap.ext fun y => by
      simp [Module.reflection_apply, map_sub, map_smul])
    (LinearMap.ext fun y => by
      simp [Module.reflection_apply, map_sub, map_smul])

theorem reflLin_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (c : V →ₗ[ZMod 3] ZMod 3) (δ : V) (h : c δ = 2) (x : V) :
    reflLin c δ h x = x - c x • δ := by
  simp [reflLin, LinearEquiv.ofLinear_apply, Module.reflection_apply]

theorem absIrred_reflLin_E7E8 {τ : Tag}
    (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    ZS.AbsIrred 3 (Subgroup.closure (Set.range fun i : Fin τ.rank =>
      reflLin (cartanFunctional τ 3 i) (Pi.single i 1) (cartanFunctional_single i))) := by
  let V := Fin τ.rank → ZMod 3
  let g : Fin τ.rank → (V ≃ₗ[ZMod 3] V) := fun i =>
    reflLin (cartanFunctional τ 3 i) (Pi.single i 1) (cartanFunctional_single i)
  have hg : ∀ i w, g i w = w - (cartanFunctional τ 3 i) w • (Pi.single i 1 : V) := by
    intro i w
    exact reflLin_apply _ _ _ _
  have hα : ∀ i, (cartanFunctional τ 3 i) (Pi.single i 1 : V) = 2 := by
    intro i; exact cartanFunctional_single i
  have hspan : Submodule.span (ZMod 3) (Set.range fun i : Fin τ.rank =>
      (Pi.single i 1 : V)) = ⊤ := by
    rw [← (Pi.basisFun (ZMod 3) (Fin τ.rank)).span_eq]
    congr 1
    ext x
    simp [Pi.basisFun_apply, eq_comm]
  have hdet : (Matrix.of fun i j : Fin τ.rank =>
      (cartanFunctional τ 3 i) (Pi.single j 1)).det ≠ 0 := by
    have hEq : (Matrix.of fun i j : Fin τ.rank =>
        (cartanFunctional τ 3 i) (Pi.single j 1)) =
        (τ.cartan.map (Int.castRingHom (ZMod 3))).transpose := by
      ext i j
      simp [Matrix.map_apply, cartanFunctional_single_apply]
    rw [hEq, Matrix.det_transpose]
    change ((Int.castRingHom (ZMod 3)).mapMatrix τ.cartan).det ≠ 0
    rw [← RingHom.map_det]
    rcases hτ with rfl | rfl
    · rw [det_cartan_E7]; decide
    · rw [det_cartan_E8]; decide
  have hker : ∀ w : V, (∀ i, (cartanFunctional τ 3 i) w = 0) → w = 0 := by
    intro w hw
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    funext i
    rw [Matrix.mulVec, dotProduct]
    have hi := hw i
    rw [CFSG.RankThree.CentralCover.cartanFunctional_apply] at hi
    simpa [Matrix.of_apply, cartanFunctional_single_apply] using hi
  have hconn : ∀ i j, Relation.ReflTransGen
      (fun a b => (cartanFunctional τ 3 a) (Pi.single b 1) ≠ 0 ∧
        (cartanFunctional τ 3 b) (Pi.single a 1) ≠ 0) i j := by
    intro i j
    exact @Relation.ReflTransGen.mono (Fin τ.rank)
      (fun a b => τ.cartan a b = -1 ∧ τ.cartan b a = -1)
      (fun a b => (cartanFunctional τ 3 a) (Pi.single b 1) ≠ 0 ∧
        (cartanFunctional τ 3 b) (Pi.single a 1) ≠ 0)
      (fun a b hab => by
        constructor
        · rw [cartanFunctional_single_apply, hab.2]
          norm_num
        · rw [cartanFunctional_single_apply, hab.1]
          norm_num) i j (cartan_connected_free_E7E8 hτ i j)
  exact ggRC_absIrred_of_connected (p := 3) (by norm_num) g
    (fun i => (Pi.single i 1 : V)) (fun i => cartanFunctional τ 3 i) hg hα hspan hker hconn
    (Subgroup.closure (Set.range g)) rfl



set_option maxHeartbeats 400000 in
theorem excWordProd_smul {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (CoxeterSystem.wordProd (coxeterSystem τ) l) • v =
      l.foldr (CFSG.Blueprint.Chevalley.reflect τ) v := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [CoxeterSystem.wordProd_cons, mul_smul, ih, CFSG.LieType.Chevalley.simple_smul]
      rfl

noncomputable def excW0 (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd ((CFSG.LieType.Chevalley.RootOps.longestWord τ).map τ.idx)

set_option maxHeartbeats 800000 in
theorem excW0_single {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8) (i : Fin τ.rank) :
    excW0 τ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1 := by
  rcases hτ with rfl | rfl <;> fin_cases i <;>
    (rw [excW0, excWordProd_smul]; decide +kernel)

theorem excW0_smul_eq_neg {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    (β : Fin τ.rank → ℤ) : excW0 τ • β = -β := by
  have hsum : β = ∑ i, β i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hi), smul_zero]
    · intro hj
      simp at hj
  conv_lhs => rw [hsum]
  rw [Finset.smul_sum]
  simp only [SMulCommClass.smul_comm, excW0_single hτ, smul_neg]
  rw [Finset.sum_neg_distrib, ← hsum]

theorem redMod_neg_local {τ : Tag} {p : ℕ} (v : Fin τ.rank → ℤ) :
    TableBExc.redMod τ p (-v) = -TableBExc.redMod τ p v := by
  funext i
  simp [TableBExc.redMod]

set_option maxHeartbeats 400000 in
theorem torusAct_excW0_eq_neg {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8)
    (x : Fin τ.rank → ZMod 3) :
    TableBExc.torusAct τ 3 (excW0 τ) x = -x := by
  rw [TableBExc.torusAct, excW0_smul_eq_neg hτ (TableBExc.liftMod τ 3 x),
    redMod_neg_local, TableBExc.redMod_liftMod]

@[expose] noncomputable def negOneMulAut (V : Type) [AddCommGroup V] :
    MulAut (Multiplicative V) :=
  AddEquiv.toMultiplicative (AddEquiv.neg V)

theorem negOneMulAut_apply {V : Type} [AddCommGroup V] (v : V) :
    negOneMulAut V (Multiplicative.ofAdd v) = Multiplicative.ofAdd (-v) := rfl

theorem negOneMulAut_apply_mul {V : Type} [AddCommGroup V]
    (x : Multiplicative V) :
    negOneMulAut V x = Multiplicative.ofAdd (-Multiplicative.toAdd x) := rfl

theorem torusMulAut_excW0_eq_negOne {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    ExcWeylOuter.torusMulAut τ 3 (excW0 τ) =
      negOneMulAut (Fin τ.rank → ZMod 3) := by
  ext x
  rw [← ofAdd_toAdd x]
  rw [ExcWeylOuter.torusMulAut_apply, torusAct_excW0_eq_neg hτ (toAdd x)]
  simp [negOneMulAut_apply_mul]

theorem negOne_mem_range_torusMulAut_E7E8 {τ : Tag}
    (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    negOneMulAut (Fin τ.rank → ZMod 3) ∈
      (ExcWeylOuter.torusMulAut τ 3).range := by
  rw [← torusMulAut_excW0_eq_negOne hτ]
  exact MonoidHom.mem_range.mpr ⟨excW0 τ, rfl⟩



theorem normalizer_eq_of_normInducesInner_of_centralizer_le
    {G : Type} [Group G] (W : Subgroup G) (hNI : NormInducesInner W)
    (hcent : Subgroup.centralizer (W : Set G) ≤ W) :
    Subgroup.normalizer (W : Set G) = W := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨w, hw, hconj⟩ := hNI φ hφ
    have hc : w⁻¹ * φ ∈ Subgroup.centralizer (W : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : φ * v = (w * v * w⁻¹) * φ := by
        have := congrArg (fun x => x * φ) (hconj v hv)
        simpa [mul_assoc] using this
      symm
      calc (w⁻¹ * φ) * v = w⁻¹ * (φ * v) := by group
        _ = w⁻¹ * ((w * v * w⁻¹) * φ) := by rw [h1]
        _ = v * (w⁻¹ * φ) := by group
    have hcW : w⁻¹ * φ ∈ W := hcent hc
    have hφw : φ = w * (w⁻¹ * φ) := by group
    rw [hφw]
    exact W.mul_mem hw hcW
  · exact Subgroup.le_normalizer

theorem centralizer_range_torusMulAut_E7E8_le {τ : Tag}
    (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    Subgroup.centralizer
      ((ExcWeylOuter.torusMulAut τ 3).range :
        Set (MulAut (Multiplicative (Fin τ.rank → ZMod 3)))) ≤
      (ExcWeylOuter.torusMulAut τ 3).range := by
  let V := Fin τ.rank → ZMod 3
  let P : Subgroup (MulAut (Multiplicative V)) := (ExcWeylOuter.torusMulAut τ 3).range
  let g : Fin τ.rank → (V ≃ₗ[ZMod 3] V) := fun i =>
    reflLin (cartanFunctional τ 3 i) (Pi.single i 1) (cartanFunctional_single i)
  let P_lin : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range g)
  have hPabs : ZS.AbsIrred 3 P_lin := absIrred_reflLin_E7E8 hτ
  let toLin : MulAut (Multiplicative V) →* (V ≃ₗ[ZMod 3] V) :=
    { toFun := fun u => AddEquiv.toLinearEquiv (MulEquiv.toAdditive u) (ZMod.map_smul _)
      map_one' := LinearEquiv.ext fun v => rfl
      map_mul' u v := LinearEquiv.ext fun w => rfl }
  have hto_apply : ∀ (u : MulAut (Multiplicative V)) (v : V),
      toLin u v = Multiplicative.toAdd (u (Multiplicative.ofAdd v)) := by
    intro u v
    rfl
  have hsymm : ∀ i j, τ.cartan i j = τ.cartan j i := by
    rcases hτ with rfl | rfl
    · exact TableBExc.Three.cartan_symm_E7
    · exact TableBExc.Three.cartan_symm_E8
  have hto_refl : ∀ i, toLin (torusReflAut (cartanFunctional τ 3 i)
      (Pi.single i 1) (cartanFunctional_single i)) = g i := by
    intro i
    ext v
    rw [hto_apply, torusReflAut_apply, reflLin_apply]
    rfl
  have hmap : P.map toLin = P_lin := by
    change (ExcWeylOuter.torusMulAut τ 3).range.map toLin = _
    rw [ExcWeylOuter.range_torusMulAut hsymm, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hto_refl i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨torusReflAut (cartanFunctional τ 3 i) (Pi.single i 1)
        (cartanFunctional_single i), ⟨i, rfl⟩, hto_refl i⟩
  intro c hc
  have hc' : ∀ p ∈ P, p * c = c * p := Subgroup.mem_centralizer_iff.mp hc
  have hcomm : ∀ p ∈ P.map toLin, toLin c * p = p * toLin c := by
    intro p hp
    obtain ⟨p0, hp0, rfl⟩ := hp
    exact (congrArg toLin (hc' p0 hp0)).symm
  obtain ⟨a, ha⟩ := hPabs.2 (toLin c : V →ₗ[ZMod 3] V) (by
    intro p hp
    have hp' : p ∈ P.map toLin := by rw [hmap]; exact hp
    refine LinearMap.ext fun v => ?_
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e v) (hcomm p hp')
    simpa [LinearMap.comp_apply] using h)
  have : Nonempty (Fin τ.rank) := by
    rcases hτ with rfl | rfl
    · exact ⟨⟨0, by decide⟩⟩
    · exact ⟨⟨0, by decide⟩⟩
  let v0 : V := Pi.single (Classical.choice inferInstance) 1
  have hv0 : v0 ≠ 0 := by
    intro h
    have this : v0 (Classical.choice inferInstance) = 0 := congrFun h _
    have h1 : (1 : ZMod 3) ≠ 0 := by decide
    exact h1 (by simp [v0] at this)
  have hne : (toLin c : V → V) v0 ≠ 0 := by
    intro h
    exact hv0 ((toLin c).map_eq_zero_iff.mp h)
  have ha0 : a ≠ 0 := by
    intro hzero
    have hT : (toLin c : V →ₗ[ZMod 3] V) v0 = 0 := by
      rw [ha, hzero, zero_smul]
      rfl
    exact hne (by simpa using hT)
  have hto_inj : Function.Injective toLin := by
    intro u v h
    refine MulEquiv.ext fun x => ?_
    have hx := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (Multiplicative.toAdd x)) h
    have hx' : Multiplicative.toAdd (u x) = Multiplicative.toAdd (v x) := by
      simpa [hto_apply] using hx
    exact Multiplicative.toAdd.injective hx'
  have hcases_all : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = -1 := by decide
  have hcases : a = 0 ∨ a = 1 ∨ a = -1 := hcases_all a
  rcases hcases with h0 | h1 | hneg
  · exact absurd h0 ha0
  · have hc1 : c = 1 := by
      apply hto_inj
      refine LinearEquiv.ext fun v => ?_
      have h := congrArg (fun f : V →ₗ[ZMod 3] V => f v) ha
      simpa [hto_apply, h1] using h
    rw [hc1]
    exact P.one_mem
  · have hcneg : c = negOneMulAut V := by
      apply hto_inj
      refine LinearEquiv.ext fun v => ?_
      have h := congrArg (fun f : V →ₗ[ZMod 3] V => f v) ha
      simpa [hto_apply, hneg, negOneMulAut_apply] using h
    rw [hcneg]
    exact negOne_mem_range_torusMulAut_E7E8 hτ

theorem normalizer_range_torusMulAut_E7E8
    {τ : Tag} (hτ : τ = Tag.E7 ∨ τ = Tag.E8) :
    Subgroup.normalizer
      ((ExcWeylOuter.torusMulAut τ 3).range :
        Set (MulAut (Multiplicative (Fin τ.rank → ZMod 3)))) =
      (ExcWeylOuter.torusMulAut τ 3).range :=
  normalizer_eq_of_normInducesInner_of_centralizer_le _
    (by
      rcases hτ with rfl | rfl
      · exact normInducesInner_range_torusMulAut_E7 (p := 3) (by norm_num)
      · exact normInducesInner_range_torusMulAut_E8 (p := 3) (by norm_num))
    (centralizer_range_torusMulAut_E7E8_le hτ)



theorem normalizer_range_torusMulAut_E7 :
    Subgroup.normalizer
      ((ExcWeylOuter.torusMulAut Tag.E7 3).range :
        Set (MulAut (Multiplicative (Fin Tag.E7.rank → ZMod 3)))) =
      (ExcWeylOuter.torusMulAut Tag.E7 3).range :=
  normalizer_range_torusMulAut_E7E8 (Or.inl rfl)

theorem normalizer_range_torusMulAut_E8 :
    Subgroup.normalizer
      ((ExcWeylOuter.torusMulAut Tag.E8 3).range :
        Set (MulAut (Multiplicative (Fin Tag.E8.rank → ZMod 3)))) =
      (ExcWeylOuter.torusMulAut Tag.E8 3).range :=
  normalizer_range_torusMulAut_E7E8 (Or.inr rfl)

end CFSG.StandardType
