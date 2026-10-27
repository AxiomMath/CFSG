module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofDual
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open Module

namespace NoOffRest

section Torus

variable {τ : Tag} {p : ℕ}

theorem torusAct_eq_sum [NeZero p] (u : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p u x =
      fun i => ∑ j, (((u • (Pi.single j 1 : Fin τ.rank → ℤ)) i : ℤ) : ZMod p) * x j := by
  funext i
  rw [TableBExc.torusAct, TableBExc.E6Three.weyl_smul_eq_sum]
  simp only [TableBExc.redMod, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum,
    Int.cast_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  simp [TableBExc.liftMod]

variable (τ p) in
@[expose] noncomputable def torusLin [NeZero p] (u : WeylGroup τ) :
    (Fin τ.rank → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) where
  toFun := TableBExc.torusAct τ p u
  map_add' x y := by
    rw [torusAct_eq_sum, torusAct_eq_sum, torusAct_eq_sum]
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    rw [torusAct_eq_sum, torusAct_eq_sum]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem torusLin_apply [NeZero p] (u : WeylGroup τ) (x : Fin τ.rank → ZMod p) :
    torusLin τ p u x = TableBExc.torusAct τ p u x :=
  rfl

variable (τ p) in
@[expose] noncomputable def bform : LinearMap.BilinForm (ZMod p) (Fin τ.rank → ZMod p) :=
  LinearMap.mk₂ (ZMod p)
    (fun x y => ∑ i, ∑ j, x i * ((τ.symmetrizedCartan i j : ℤ) : ZMod p) * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y y' => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem bform_apply (x y : Fin τ.rank → ZMod p) :
    bform τ p x y = ∑ i, ∑ j, x i * ((τ.symmetrizedCartan i j : ℤ) : ZMod p) * y j :=
  rfl

theorem bform_redMod (a b : Fin τ.rank → ℤ) :
    bform τ p (TableBExc.redMod τ p a) (TableBExc.redMod τ p b) = ((iform a b : ℤ) : ZMod p) := by
  rw [bform_apply, iform]
  push_cast
  rfl

theorem bform_torusAct [NeZero p] (u : WeylGroup τ) (x y : Fin τ.rank → ZMod p) :
    bform τ p (TableBExc.torusAct τ p u x) (TableBExc.torusAct τ p u y) = bform τ p x y := by
  rw [TableBExc.torusAct, TableBExc.torusAct, bform_redMod, iform_smul, ← bform_redMod,
    TableBExc.redMod_liftMod, TableBExc.redMod_liftMod]

end Torus

section NondegE8

variable {p : ℕ}

theorem bform_comm (x y : Fin Tag.E8.rank → ZMod p) : bform .E8 p x y = bform .E8 p y x := by
  rw [bform_apply, bform_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [symmetrizedCartan_symm .E8 j i]
  ring

theorem bform_single_left (i : Fin Tag.E8.rank) (y : Fin Tag.E8.rank → ZMod p) :
    bform .E8 p (Pi.single i 1) y =
      Matrix.mulVec (Tag.E8.symmetrizedCartan.map (Int.castRingHom (ZMod p))) y i := by
  rw [bform_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem bform_nondegenerate_E8 [Fact p.Prime] : (bform .E8 p).Nondegenerate := by
  have hinj : Function.Injective
      (Tag.E8.symmetrizedCartan.map (Int.castRingHom (ZMod p))).mulVec := by
    have hd : (Tag.E8.symmetrizedCartan.map (Int.castRingHom (ZMod p))).det =
        ((Tag.E8.symmetrizedCartan.det : ℤ) : ZMod p) := (RingHom.map_det _ _).symm
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hd,
      ExcFrames.det_symmetrizedCartan_E8, Int.cast_one]
    exact isUnit_one
  have hR : ∀ y : Fin Tag.E8.rank → ZMod p, (∀ x, bform .E8 p x y = 0) → y = 0 := by
    intro y hy
    refine hinj ((funext fun i => ?_).trans (Matrix.mulVec_zero _).symm)
    rw [← bform_single_left]
    exact hy _
  exact ⟨fun x hx => hR x fun y => (bform_comm y x).trans (hx y), hR⟩

end NondegE8

section WordW

local instance noOffRestNeZeroRankE8 : NeZero Tag.E8.rank := ⟨by decide⟩

@[expose] def wordE8W : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3,
    0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 1, 3, 0, 2, 0]

@[expose] def weylE8W : WeylGroup .E8 := (coxeterSystem .E8).wordProd wordE8W

theorem weylE8W_sq_single : ∀ j : Fin Tag.E8.rank,
    (weylE8W * weylE8W) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) = -Pi.single j 1 := by
  intro j
  rw [mul_smul, weylE8W, TableBExc.wordProd_smul, TableBExc.wordProd_smul]
  revert j
  decide +kernel

variable {p : ℕ}

theorem torusAct_weylE8W_sq [NeZero p] (x : Fin Tag.E8.rank → ZMod p) :
    TableBExc.torusAct .E8 p weylE8W (TableBExc.torusAct .E8 p weylE8W x) = -x := by
  rw [← TableBExc.torusAct_mul, torusAct_eq_sum]
  funext i
  simp [weylE8W_sq_single, Pi.single_apply]

end WordW

section DualE8

variable {p : ℕ} [Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem dualHyp_E8 (hp2 : p ≠ 2) {u : WeylGroup .E8} (hu : u * weylE8W = weylE8W * u)
    {lam : ZMod p} (hlam : lam * lam = -1) :
    DualHyp (bform .E8 p) (torusLin .E8 p weylE8W) (torusLin .E8 p u) lam where
  nondeg := bform_nondegenerate_E8
  isomT := bform_torusAct weylE8W
  isomU := bform_torusAct u
  comm x := by
    rw [torusLin_apply, torusLin_apply, torusLin_apply, torusLin_apply, ← TableBExc.torusAct_mul,
      ← TableBExc.torusAct_mul, hu]
  sq := torusAct_weylE8W_sq
  lam_sq := hlam
  two_ne := two_ne_zero_zmod hp2

theorem finrank_eigE8 (hp2 : p ≠ 2) {lam : ZMod p} (hlam : lam * lam = -1) :
    finrank (ZMod p) (eigSp (torusLin .E8 p weylE8W) lam) = 4 := by
  have h := dualHyp_E8 (u := 1) hp2 (by rw [one_mul, mul_one]) hlam
  have d1 := h.finrank_eq
  have d2 := h.finrank_eig_eq
  rw [Module.finrank_fin_fun] at d1
  change 8 = _ at d1
  omega

theorem finrank_fix_eq_two_mul_E8 (hp2 : p ≠ 2) {u : WeylGroup .E8}
    (hu : u * weylE8W = weylE8W * u) {lam : ZMod p} (hlam : lam * lam = -1) :
    finrank (ZMod p) (fixSp (torusLin .E8 p u)) =
      2 * finrank (ZMod p) ↥(eigSp (torusLin .E8 p weylE8W) lam ⊓ fixSp (torusLin .E8 p u)) :=
  (dualHyp_E8 hp2 hu hlam).finrank_fix_eq_two_mul

end DualE8

section Model

variable {p : ℕ}

abbrev centE8W : Subgroup (WeylGroup .E8) := Subgroup.centralizer {weylE8W}

theorem mul_comm_of_mem_centE8W {u : WeylGroup .E8} (hu : u ∈ centE8W) :
    u * weylE8W = weylE8W * u :=
  Subgroup.mem_centralizer_singleton_iff.mp hu

variable (p) in
noncomputable abbrev eigE8 [Fact p.Prime] (lam : ZMod p) :
    Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p) :=
  eigSp (torusLin .E8 p weylE8W) lam

noncomputable instance eigE8AddCommGroup [Fact p.Prime] (lam : ZMod p) :
    AddCommGroup (eigE8 p lam) :=
  Submodule.addCommGroup _

theorem torusAct_mem_eigE8 [Fact p.Prime] {lam : ZMod p} {u : WeylGroup .E8} (hu : u ∈ centE8W)
    {x : Fin Tag.E8.rank → ZMod p} (hx : x ∈ eigE8 p lam) :
    TableBExc.torusAct .E8 p u x ∈ eigE8 p lam :=
  map_mem_eigSp (U := torusLin .E8 p u) (fun y => by
    rw [torusLin_apply, torusLin_apply, torusLin_apply, torusLin_apply, ← TableBExc.torusAct_mul,
      ← TableBExc.torusAct_mul, mul_comm_of_mem_centE8W hu]) hx

variable (p) in
@[expose] noncomputable def eigPerm [Fact p.Prime] (lam : ZMod p) :
    centE8W →* Equiv.Perm (eigE8 p lam) where
  toFun u :=
    { toFun := fun x => ⟨TableBExc.torusAct .E8 p u x, torusAct_mem_eigE8 u.2 x.2⟩
      invFun := fun x => ⟨TableBExc.torusAct .E8 p ((u⁻¹ : centE8W) : WeylGroup .E8) x,
        torusAct_mem_eigE8 (u⁻¹).2 x.2⟩
      left_inv x := Subtype.ext (by
        show TableBExc.torusAct .E8 p ((u : WeylGroup .E8)⁻¹)
          (TableBExc.torusAct .E8 p (u : WeylGroup .E8) x) = x
        rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one])
      right_inv x := Subtype.ext (by
        show TableBExc.torusAct .E8 p (u : WeylGroup .E8)
          (TableBExc.torusAct .E8 p ((u : WeylGroup .E8)⁻¹) x) = x
        rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]) }
  map_one' := Equiv.ext fun x => Subtype.ext (TableBExc.torusAct_one _)
  map_mul' u v := Equiv.ext fun x => Subtype.ext (TableBExc.torusAct_mul _ _ _)

theorem natCard_submodule [Fact p.Prime] (S : Submodule (ZMod p) (Fin Tag.E8.rank → ZMod p)) :
    Nat.card S = p ^ finrank (ZMod p) S := by
  classical
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

theorem card_fix_eq_fixSp [Fact p.Prime] (u : WeylGroup .E8) :
    Nat.card {x : Fin Tag.E8.rank → ZMod p // TableBExc.torusAct .E8 p u x = x} =
      p ^ finrank (ZMod p) (fixSp (torusLin .E8 p u)) := by
  rw [← natCard_submodule]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [mem_fixSp, torusLin_apply])

theorem card_fix_eigPerm_le [Fact p.Prime] {lam : ZMod p} {A : Subgroup centE8W} {a : centE8W}
    (ha : a ∈ A) :
    Nat.card {v : eigE8 p lam // ∀ b ∈ A, eigPerm p lam b v = v} ≤
      p ^ finrank (ZMod p) ↥(eigE8 p lam ⊓ fixSp (torusLin .E8 p a)) := by
  rw [← natCard_submodule]
  refine Nat.card_le_card_of_injective (fun v => ⟨v.1.1, v.1.2,
    mem_fixSp.mpr (congrArg Subtype.val (v.2 a ha))⟩) fun v v' h => ?_
  have h1 := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext h1)

theorem card_fix_conj_E8 [NeZero p] (g u : WeylGroup .E8) :
    Nat.card {x : Fin Tag.E8.rank → ZMod p // TableBExc.torusAct .E8 p (g * u * g⁻¹) x = x} =
      Nat.card {x : Fin Tag.E8.rank → ZMod p // TableBExc.torusAct .E8 p u x = x} := by
  have key : ∀ x, TableBExc.torusAct .E8 p (g * u * g⁻¹) x = x ↔
      TableBExc.torusAct .E8 p u (TableBExc.torusAct .E8 p g⁻¹ x) =
        TableBExc.torusAct .E8 p g⁻¹ x := by
    intro x
    rw [TableBExc.torusAct_mul, TableBExc.torusAct_mul]
    constructor
    · intro h
      have h1 := congrArg (TableBExc.torusAct .E8 p g⁻¹) h
      rwa [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one] at h1
    · intro h
      rw [h, ← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one]
  exact Nat.card_congr
    { toFun := fun x => ⟨TableBExc.torusAct .E8 p g⁻¹ x.1, (key x.1).mp x.2⟩
      invFun := fun y => ⟨TableBExc.torusAct .E8 p g y.1, (key _).mpr (by
        have e : TableBExc.torusAct .E8 p g⁻¹ (TableBExc.torusAct .E8 p g y.1) = y.1 := by
          rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]
        rw [e]
        exact y.2)⟩
      left_inv := fun x => Subtype.ext (by
        show TableBExc.torusAct .E8 p g (TableBExc.torusAct .E8 p g⁻¹ x.1) = x.1
        rw [← TableBExc.torusAct_mul, mul_inv_cancel, TableBExc.torusAct_one])
      right_inv := fun y => Subtype.ext (by
        show TableBExc.torusAct .E8 p g⁻¹ (TableBExc.torusAct .E8 p g y.1) = y.1
        rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one]) }

theorem card_fix_le_pow [NeZero p] (u : WeylGroup .E8) (k : ℕ) :
    Nat.card {x : Fin Tag.E8.rank → ZMod p // TableBExc.torusAct .E8 p u x = x} ≤
      Nat.card {x : Fin Tag.E8.rank → ZMod p // TableBExc.torusAct .E8 p (u ^ k) x = x} := by
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩) fun x x' h => ?_
  · induction k with
    | zero => rw [pow_zero, TableBExc.torusAct_one]
    | succ k ih => rw [pow_succ, TableBExc.torusAct_mul, x.2, ih]
  · have h1 := congrArg Subtype.val h
    exact Subtype.ext h1

theorem finrank_eig_fix_le [Fact p.Prime] (hp2 : p ≠ 2) {u : WeylGroup .E8} (hu : u ∈ centE8W)
    {lam : ZMod p} (hlam : lam * lam = -1) {k : ℕ}
    (hk : Nat.card {x : Fin Tag.E8.rank → ZMod p // TableBExc.torusAct .E8 p u x = x} ≤ p ^ k) :
    2 * finrank (ZMod p) ↥(eigE8 p lam ⊓ fixSp (torusLin .E8 p u)) ≤ k := by
  rw [card_fix_eq_fixSp, finrank_fix_eq_two_mul_E8 hp2 (mul_comm_of_mem_centE8W hu) hlam] at hk
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hk

theorem card_eigE8 [Fact p.Prime] (hp2 : p ≠ 2) {lam : ZMod p} (hlam : lam * lam = -1) :
    Nat.card (eigE8 p lam) = p ^ 4 := by
  rw [natCard_submodule, finrank_eigE8 hp2 hlam]

end Model

section Five

local instance noOffRestFactFiveE8 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance noOffRestNeZeroRankE8' : NeZero Tag.E8.rank := ⟨by decide⟩

theorem isElemAbelian_map {H H' : Type*} [Group H] [Group H'] {q : ℕ} (χ : H →* H')
    {E : Subgroup H} (hE : IsElemAbelian q E) : IsElemAbelian q (E.map χ) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem card_fix_le_of_mem_weylE8S {s : WeylGroup .E8} (hs : s ∈ TableBExc.weylE8S) (hs1 : s ≠ 1) :
    Nat.card {x : Fin Tag.E8.rank → ZMod 5 // TableBExc.torusAct .E8 5 s x = x} ≤ 5 ^ 5 := by
  obtain ⟨k, hk⟩ := TableBExc.exists_pow_eq_rep hs hs1
  refine (card_fix_le_pow s k).trans ?_
  rcases hk with hk | ⟨c, hc, hk⟩
  · rw [hk, TableBExc.weylE8B, NoOffExc.card_fix_torusAct_eq TableBExc.Three.cartan_symm_E8]
    exact TableBExc.card_fix_wordE8B
  · rw [hk, ← TableBExc.wordProd_wordE8AB,
      NoOffExc.card_fix_torusAct_eq TableBExc.Three.cartan_symm_E8]
    exact TableBExc.card_fix_wordE8AB hc

theorem card_fix_weylE8AB :
    Nat.card {x : Fin Tag.E8.rank → ZMod 5 //
      TableBExc.torusAct .E8 5 (TableBExc.weylE8A * TableBExc.weylE8B) x = x} ≤ 5 ^ 3 := by
  have e : TableBExc.weylE8A * TableBExc.weylE8B =
      (coxeterSystem .E8).wordProd (TableBExc.wordE8AB 1) := by
    rw [TableBExc.wordProd_wordE8AB, pow_one]
  rw [e, NoOffExc.card_fix_torusAct_eq TableBExc.Three.cartan_symm_E8]
  exact TableBExc.card_fix_torusWord_le (τ := .E8) (TableBExc.wordE8AB 1) ![0, 1, 2, 3, 5]
    ![0, 1, 2, 4, 5] (by decide)
    ![![1, 0, 2, 2, 0], ![0, 2, 0, 0, 0], ![3, 0, 3, 4, 0], ![2, 2, 2, 2, 0], ![2, 2, 2, 2, 4]]
    (by decide +kernel)

theorem weylE8A_mul_weylE8B_mem : TableBExc.weylE8A * TableBExc.weylE8B ∈ TableBExc.weylE8S :=
  Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem actNoOffender_eigPerm {lam : ZMod 5} (hlam : lam * lam = -1) :
    ActNoOffender (eigPerm 5 lam) 5 := by
  intro A hA hA1
  classical
  set Ab := A.map centE8W.subtype with hAb
  have hAbe : IsElemAbelian 5 Ab := isElemAbelian_map _ hA
  have hcardAb : Nat.card Ab = Nat.card A :=
    Subgroup.card_map_of_injective centE8W.subtype_injective
  have hidx : ¬ 5 ∣ TableBExc.weylE8S.index := by
    rw [NoOffExc.index_eq_of_card TableBExc.card_weylE8S NoOffExc.card_weyl_E8
      (show 25 * 27869184 = 696729600 by norm_num) (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_five hidx
    (TableB.isPGroup_of_isElemAbelian hAbe)
  have hcardAg : Nat.card (Ab.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hcardAb
  have hdvd : Nat.card A ∣ 5 ^ 2 := by
    rw [← hcardAg, show (5 : ℕ) ^ 2 = 25 by norm_num, ← TableBExc.card_weylE8S]
    exact Subgroup.card_dvd_of_le hg
  rw [card_eigE8 (by norm_num) hlam]
  by_cases h25 : Nat.card A = 25
  · have hAg : Ab.map (MulAut.conj g).toMonoidHom = TableBExc.weylE8S :=
      Subgroup.eq_of_le_of_card_ge hg (by rw [hcardAg, h25, TableBExc.card_weylE8S])
    have hmem := weylE8A_mul_weylE8B_mem
    rw [← hAg] at hmem
    obtain ⟨_, ⟨a, haA, rfl⟩, hga⟩ := hmem
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hga
    have hfixV : Nat.card {x : Fin Tag.E8.rank → ZMod 5 //
        TableBExc.torusAct .E8 5 (a : WeylGroup .E8) x = x} ≤ 5 ^ 3 := by
      rw [← card_fix_conj_E8 g]
      have hga' : g * (a : WeylGroup .E8) * g⁻¹ = TableBExc.weylE8A * TableBExc.weylE8B := hga
      rw [hga']
      exact card_fix_weylE8AB
    have hd := finrank_eig_fix_le (by norm_num) a.2 hlam hfixV
    calc Nat.card A * Nat.card {v : eigE8 5 lam // ∀ b ∈ A, eigPerm 5 lam b v = v}
        ≤ 25 * 5 ^ 1 := Nat.mul_le_mul h25.le ((card_fix_eigPerm_le haA).trans
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      _ < 5 ^ 4 := by norm_num
  · have hA5 : Nat.card A ≤ 5 := by
      obtain ⟨k, hk, hkA⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
      rw [hkA]
      have hk2 : k ≠ 2 := fun h => h25 (by rw [hkA, h]; norm_num)
      calc 5 ^ k ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 5 := by norm_num
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have ha1' : (a : WeylGroup .E8) ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
    have hgmem : g * (a : WeylGroup .E8) * g⁻¹ ∈ TableBExc.weylE8S :=
      hg ⟨(a : WeylGroup .E8), ⟨a, haA, rfl⟩, rfl⟩
    have hne : g * (a : WeylGroup .E8) * g⁻¹ ≠ 1 := fun h => ha1' (by
      have h1 : (a : WeylGroup .E8) = g⁻¹ * (g * (a : WeylGroup .E8) * g⁻¹) * g := by group
      rw [h1, h]
      group)
    have hfixV : Nat.card {x : Fin Tag.E8.rank → ZMod 5 //
        TableBExc.torusAct .E8 5 (a : WeylGroup .E8) x = x} ≤ 5 ^ 5 := by
      rw [← card_fix_conj_E8 g]
      exact card_fix_le_of_mem_weylE8S hgmem hne
    have hd := finrank_eig_fix_le (by norm_num) a.2 hlam hfixV
    calc Nat.card A * Nat.card {v : eigE8 5 lam // ∀ b ∈ A, eigPerm 5 lam b v = v}
        ≤ 5 * 5 ^ 2 := Nat.mul_le_mul hA5 ((card_fix_eigPerm_le haA).trans
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      _ < 5 ^ 4 := by norm_num

theorem eigPerm_injective {lam : ZMod 5} (hlam : lam * lam = -1) :
    Function.Injective (eigPerm 5 lam) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hfixE : ∀ x ∈ eigE8 5 lam, TableBExc.torusAct .E8 5 (u : WeylGroup .E8) x = x :=
    fun x hx => congrArg Subtype.val (Equiv.ext_iff.mp hu ⟨x, hx⟩)
  have hle : eigE8 5 lam ≤ fixSp (torusLin .E8 5 u) := fun x hx => mem_fixSp.mpr (hfixE x hx)
  have hd : finrank (ZMod 5) ↥(eigE8 5 lam ⊓ fixSp (torusLin .E8 5 u)) = 4 := by
    rw [inf_eq_left.mpr hle, finrank_eigE8 (by norm_num) hlam]
  have h8 : finrank (ZMod 5) (fixSp (torusLin .E8 5 (u : WeylGroup .E8))) = 8 := by
    rw [finrank_fix_eq_two_mul_E8 (by norm_num) (mul_comm_of_mem_centE8W u.2) hlam, hd]
  have htop : fixSp (torusLin .E8 5 (u : WeylGroup .E8)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [h8, Module.finrank_fin_fun]; rfl)
  have hall : ∀ x, TableBExc.torusAct .E8 5 (u : WeylGroup .E8) x = x := fun x => by
    have hx : x ∈ fixSp (torusLin .E8 5 (u : WeylGroup .E8)) := by
      rw [htop]
      exact Submodule.mem_top
    exact mem_fixSp.mp hx
  exact Subtype.ext (NoOffExc.eq_one_of_torusAct (p := 5) (by norm_num) hall)

theorem two_mul_two_zmod_five : (2 : ZMod 5) * 2 = -1 := by decide

theorem three_mul_three_zmod_five : (3 : ZMod 5) * 3 = -1 := by decide

theorem actNoOffender_eigPerm_two : ActNoOffender (eigPerm 5 2) 5 :=
  actNoOffender_eigPerm two_mul_two_zmod_five

theorem actNoOffender_eigPerm_three : ActNoOffender (eigPerm 5 3) 5 :=
  actNoOffender_eigPerm three_mul_three_zmod_five

theorem eigPerm_two_injective : Function.Injective (eigPerm 5 2) :=
  eigPerm_injective two_mul_two_zmod_five

theorem eigPerm_three_injective : Function.Injective (eigPerm 5 3) :=
  eigPerm_injective three_mul_three_zmod_five

end Five

end NoOffRest

end CFSG.StandardType
