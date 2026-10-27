
module

public import CFSG.Milestones.ASVolI.F48.Rest.G23FactsBase
public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.Quasithin.H13.ModelsG2
public import Certificates.Certificate7760
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.ClassicalGroups
public import CFSG.GH74.Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Milestones.ASVolI.F48.Rest.Eng
public import CFSG.Milestones.ASVolI.F48.Rest.G23Pres
public import CFSG.Milestones.ASVolI.F48.Rest.Perm
public import CFSG.Milestones.ASVolI.F48.Small.Base
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
public import CFSG.Sporadic.Schreier.J4SSylow
public import Certificates.Kernel.J4Count.FixCE

@[expose] public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Matrix

section Restrict

variable {G α : Type*} [Group G] [MulAction G α] {m : ℕ} {P : Fin m → α}
  (hP : Function.Injective P) {H : Subgroup G} (hH : ∀ h ∈ H, ∀ k, ∃ l, h • P k = P l)

include hP in
theorem burnsideF48t_inv_preserves {g : G} (hg : ∀ k, ∃ l, g • P k = P l) :
    ∀ k, ∃ l, g⁻¹ • P k = P l := by
  classical
  let f : Fin m → Fin m := fun k => Classical.choose (hg k)
  have hf : ∀ k, P (f k) = g • P k := fun k => (Classical.choose_spec (hg k)).symm
  have hinj : Function.Injective f := fun a b h => by
    have := (hf a).symm.trans ((congrArg P h).trans (hf b))
    exact hP (smul_left_cancel g this)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro k
  obtain ⟨l, hl⟩ := hsurj k
  refine ⟨l, ?_⟩
  rw [← hl, hf, inv_smul_smul]

include hP in
theorem burnsideF48t_closure_preserves {S : Set G} (hS : ∀ s ∈ S, ∀ k, ∃ l, s • P k = P l) :
    ∀ h ∈ Subgroup.closure S, ∀ k, ∃ l, h • P k = P l := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact fun k => ⟨k, one_smul _ _⟩
  | mul a b _ _ ha hb =>
    intro k
    obtain ⟨l, hl⟩ := hb k
    obtain ⟨l', hl'⟩ := ha l
    exact ⟨l', by rw [mul_smul, hl, hl']⟩
  | inv a _ ha => exact burnsideF48t_inv_preserves hP ha

noncomputable def burnsideF48t_resFun (h : H) (k : Fin m) : Fin m :=
  Classical.choose (hH h h.2 k)

theorem burnsideF48t_resFun_spec (h : H) (k : Fin m) :
    P (burnsideF48t_resFun hH h k) = (h : G) • P k :=
  (Classical.choose_spec (hH h h.2 k)).symm

include hP in
theorem burnsideF48t_resFun_one (k : Fin m) : burnsideF48t_resFun hH 1 k = k :=
  hP (by rw [burnsideF48t_resFun_spec (P := P) hH 1 k, Subgroup.coe_one, one_smul])

include hP in
theorem burnsideF48t_resFun_mul (g h : H) (k : Fin m) :
    burnsideF48t_resFun hH (g * h) k = burnsideF48t_resFun hH g (burnsideF48t_resFun hH h k) :=
  hP (by rw [burnsideF48t_resFun_spec (P := P) hH (g * h) k,
    burnsideF48t_resFun_spec (P := P) hH g (burnsideF48t_resFun hH h k),
    burnsideF48t_resFun_spec (P := P) hH h k, Subgroup.coe_mul, mul_smul])

noncomputable def burnsideF48t_resHom : H →* Equiv.Perm (Fin m) where
  toFun h :=
    { toFun := burnsideF48t_resFun hH h
      invFun := burnsideF48t_resFun hH h⁻¹
      left_inv := fun k => by
        rw [← burnsideF48t_resFun_mul hP, inv_mul_cancel, burnsideF48t_resFun_one hP]
      right_inv := fun k => by
        rw [← burnsideF48t_resFun_mul hP, mul_inv_cancel, burnsideF48t_resFun_one hP] }
  map_one' := Equiv.ext fun k => burnsideF48t_resFun_one hP hH k
  map_mul' g h := Equiv.ext fun k => burnsideF48t_resFun_mul hP hH g h k

theorem burnsideF48t_resHom_spec (h : H) (k : Fin m) :
    P (burnsideF48t_resHom hP hH h k) = (h : G) • P k :=
  burnsideF48t_resFun_spec hH h k

end Restrict

section Decode

@[expose] def burnsideF48t_dv (v : Array ℕ) : Fin 14 → ZMod 3 :=
  fun j => ((v[(j : ℕ)]! : ℕ) : ZMod 3)

@[expose] def burnsideF48t_dm (A : Array ℕ) : Matrix (Fin 14) (Fin 14) (ZMod 3) :=
  Matrix.of fun i j => ((A[14 * (i : ℕ) + j]! : ℕ) : ZMod 3)

theorem burnsideF48t_list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

theorem burnsideF48t_dv_mulVec (A v : Array ℕ) :
    burnsideF48t_dv (burnsideF48t_g23MulVec A v) = burnsideF48t_dm A *ᵥ burnsideF48t_dv v := by
  funext i
  simp only [burnsideF48t_dv, burnsideF48t_g23MulVec, burnsideF48t_dm, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  rw [getElem!_ofFn_nat _ i.2, ZMod.natCast_mod, burnsideF48t_g23Dot, Nat.cast_list_sum,
    List.map_map, burnsideF48t_list_sum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, Nat.cast_mul]

theorem burnsideF48t_dv_norm (v : Array ℕ) :
    burnsideF48t_dv v = burnsideF48t_dv (burnsideF48t_g23Norm v) ∨
      burnsideF48t_dv v = (2 : ZMod 3) • burnsideF48t_dv (burnsideF48t_g23Norm v) := by
  unfold burnsideF48t_g23Norm
  split_ifs
  · right
    funext j
    simp only [burnsideF48t_dv, Pi.smul_apply, smul_eq_mul]
    by_cases hj : (j : ℕ) < v.size
    · rw [getElem!_pos (v.map fun x => 2 * x % 3) (j : ℕ) (by simpa using hj), Array.getElem_map,
        getElem!_pos v (j : ℕ) hj, ZMod.natCast_mod, Nat.cast_mul, ← mul_assoc]
      have h4 : (2 : ZMod 3) * ((2 : ℕ) : ZMod 3) = 1 := by decide
      rw [h4, one_mul]
    · rw [getElem!_neg (v.map fun x => 2 * x % 3) (j : ℕ) (by simpa using hj),
        getElem!_neg v (j : ℕ) hj]
      simp
  · left
    rfl

end Decode

section Gen

@[expose] noncomputable def burnsideF48t_g23R : Subgroup (GL (Fin 14) (ZMod 3)) :=
  Subgroup.closure {gX 0, gX 1, gY 0, gY 1}

@[expose] noncomputable def burnsideF48t_g23RGen (i : ℕ) : GL (Fin 14) (ZMod 3) :=
  if i = 0 then gX 0 else if i = 1 then gX 1 else if i = 2 then gY 0 else gY 1

theorem burnsideF48t_g23_coe_RGen {i : ℕ} (hi : i < 4) :
    ((burnsideF48t_g23RGen i : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      burnsideF48t_dm (burnsideF48t_g23Mats ())[i]! := by
  have hdm : ∀ l : List ℕ, burnsideF48t_dm l.toArray = dec14 l := by
    intro l
    ext a b
    simp only [burnsideF48t_dm, dec14, Matrix.of_apply]
    congr 2
    rw [List.getElem!_toArray, List.getD_eq_getElem?_getD]
    simp [List.getElem!_eq_getElem?_getD]
  interval_cases i
  · rw [burnsideF48t_g23RGen, if_pos rfl, coe_gX0]; exact (hdm _).symm
  · rw [burnsideF48t_g23RGen, if_neg (by decide), if_pos rfl, coe_gX1]; exact (hdm _).symm
  · rw [burnsideF48t_g23RGen, if_neg (by decide), if_neg (by decide), if_pos rfl, coe_gY0]
    exact (hdm _).symm
  · rw [burnsideF48t_g23RGen, if_neg (by decide), if_neg (by decide), if_neg (by decide), coe_gY1]
    exact (hdm _).symm

theorem burnsideF48t_g23_XMat_eq (i : Fin Tag.G2.rank) (c : ZMod 3) :
    XMat (ZMod 3) i c = endEquiv (RingEquiv.refl (ZMod 3)) (xOp .G2 (ZMod 3) i c) := by
  rw [endEquiv_xOp]
  rfl

theorem burnsideF48t_g23_YMat_eq (i : Fin Tag.G2.rank) (c : ZMod 3) :
    YMat (ZMod 3) i c = endEquiv (RingEquiv.refl (ZMod 3)) (yOp .G2 (ZMod 3) i c) := by
  rw [endEquiv_yOp]
  rfl

theorem burnsideF48t_g23_XMat_zero_two (i : Fin Tag.G2.rank) :
    XMat (ZMod 3) i 0 = 1 ∧ XMat (ZMod 3) i 2 = XMat (ZMod 3) i 1 * XMat (ZMod 3) i 1 := by
  refine ⟨?_, ?_⟩
  · rw [burnsideF48t_g23_XMat_eq, xOp_zero, map_one]
  · rw [burnsideF48t_g23_XMat_eq, burnsideF48t_g23_XMat_eq, ← map_mul,
      xOp_mul_xOp (upTransport .G2)]
    congr 2

theorem burnsideF48t_g23_YMat_zero_two (i : Fin Tag.G2.rank) :
    YMat (ZMod 3) i 0 = 1 ∧ YMat (ZMod 3) i 2 = YMat (ZMod 3) i 1 * YMat (ZMod 3) i 1 := by
  refine ⟨?_, ?_⟩
  · rw [burnsideF48t_g23_YMat_eq, yOp_zero, map_one]
  · rw [burnsideF48t_g23_YMat_eq, burnsideF48t_g23_YMat_eq, ← map_mul,
      yOp_mul_yOp (downTransport .G2)]
    congr 2

theorem burnsideF48t_g23_mem_R_of {g : GL (Fin 14) (ZMod 3)} (i : Fin Tag.G2.rank) (c : ZMod 3)
    (h : (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) = XMat (ZMod 3) i c ∨
      (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) = YMat (ZMod 3) i c) : g ∈ burnsideF48t_g23R := by
  have hX : ∀ j : Fin 2, gX j ∈ burnsideF48t_g23R := fun j => by
    fin_cases j
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hY : ∀ j : Fin 2, gY j ∈ burnsideF48t_g23R := fun j => by
    fin_cases j
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by
    have h3 : ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = 2 := by decide
    exact h3 c
  have key : ∀ j : Fin 2, ((g : Matrix (Fin 14) (Fin 14) (ZMod 3)) = XMat (ZMod 3) (ix j) c ∨
      (g : Matrix (Fin 14) (Fin 14) (ZMod 3)) = YMat (ZMod 3) (ix j) c) → g ∈ burnsideF48t_g23R := by
    intro j h
    rcases h with h | h
    · obtain ⟨h0, h2⟩ := burnsideF48t_g23_XMat_zero_two (ix j)
      rcases hc with rfl | rfl | rfl
      · rw [h0] at h
        rw [show g = 1 from Units.ext h]
        exact Subgroup.one_mem _
      · rw [show g = gX j from Units.ext (h.trans (coe_gX j).symm)]
        exact hX j
      · rw [h2, ← coe_gX j] at h
        rw [show g = gX j * gX j from Units.ext (h.trans (Units.val_mul _ _).symm)]
        exact Subgroup.mul_mem _ (hX j) (hX j)
    · obtain ⟨h0, h2⟩ := burnsideF48t_g23_YMat_zero_two (ix j)
      rcases hc with rfl | rfl | rfl
      · rw [h0] at h
        rw [show g = 1 from Units.ext h]
        exact Subgroup.one_mem _
      · rw [show g = gY j from Units.ext (h.trans (coe_gY j).symm)]
        exact hY j
      · rw [h2, ← coe_gY j] at h
        rw [show g = gY j * gY j from Units.ext (h.trans (Units.val_mul _ _).symm)]
        exact Subgroup.mul_mem _ (hY j) (hY j)
  exact key i h

theorem burnsideF48t_g23_map_adjointGroup {K : Type} [Field K] (σ : K ≃+* ZMod 3) :
    (adjointGroup .G2 K).map (glHom σ) = burnsideF48t_g23R := by
  apply le_antisymm
  · rw [adjointGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨i, c, h⟩, rfl⟩
    refine burnsideF48t_g23_mem_R_of i (σ c) ?_
    rw [glHom_apply, coe_glEquiv]
    rcases h with h | h
    · exact Or.inl (by rw [h, endEquiv_xOp])
    · exact Or.inr (by rw [h, endEquiv_yOp])
  · rw [burnsideF48t_g23R, Subgroup.closure_le]
    have hx : ∀ j : Fin 2, gX j ∈ (adjointGroup .G2 K).map (glHom σ) := fun j =>
      ⟨xUnit .G2 K (ix j) (σ.symm 1), xUnit_mem_adjointGroup _ _, Units.ext (by
        rw [glHom_apply, coe_glEquiv, coe_xUnit, endEquiv_xOp, RingEquiv.apply_symm_apply,
          coe_gX])⟩
    have hy : ∀ j : Fin 2, gY j ∈ (adjointGroup .G2 K).map (glHom σ) := fun j =>
      ⟨yUnit .G2 K (ix j) (σ.symm 1), yUnit_mem_adjointGroup _ _, Units.ext (by
        rw [glHom_apply, coe_glEquiv, coe_yUnit, endEquiv_yOp, RingEquiv.apply_symm_apply,
          coe_gY])⟩
    rintro _ (rfl | rfl | rfl | rfl)
    · exact hx 0
    · exact hx 1
    · exact hy 0
    · exact hy 1

end Gen

section Points

theorem burnsideF48t_g23_ptsGen {k : ℕ} (hk : k < 4) (i : Fin 728) :
    (burnsideF48t_g23Pts ())[((burnsideF48t_g23γ k i : Fin 728) : ℕ)]! =
      burnsideF48t_g23Norm
        (burnsideF48t_g23MulVec (burnsideF48t_g23Mats ())[k]! (burnsideF48t_g23Pts ())[(i : ℕ)]!) :=
  Certificates.certificate7760.2.2.2 k hk i

@[expose] def burnsideF48t_g23vec (k : ℕ) : Fin 14 → ZMod 3 :=
  burnsideF48t_dv (burnsideF48t_g23Pts ())[k]!

theorem burnsideF48t_cast_three_inj {a b : ℕ} (ha : a < 3) (hb : b < 3)
    (h : (a : ZMod 3) = (b : ZMod 3)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at this

@[expose] def burnsideF48t_g23Pt (k : Fin 728) : Set (Fin 14 → ZMod 3) :=
  {burnsideF48t_g23vec k, (2 : ZMod 3) • burnsideF48t_g23vec k}

theorem burnsideF48t_g23_RGen0 : burnsideF48t_g23RGen 0 = gX 0 := if_pos rfl

theorem burnsideF48t_g23_RGen1 : burnsideF48t_g23RGen 1 = gX 1 := by
  rw [burnsideF48t_g23RGen, if_neg (by decide), if_pos rfl]

theorem burnsideF48t_g23_RGen2 : burnsideF48t_g23RGen 2 = gY 0 := by
  rw [burnsideF48t_g23RGen, if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem burnsideF48t_g23_RGen3 : burnsideF48t_g23RGen 3 = gY 1 := by
  rw [burnsideF48t_g23RGen, if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem burnsideF48t_g23_RGen_mem (i : ℕ) : burnsideF48t_g23RGen i ∈ burnsideF48t_g23R := by
  unfold burnsideF48t_g23RGen
  split_ifs <;> exact Subgroup.subset_closure (by simp)

open scoped Pointwise in
theorem burnsideF48t_g23_RGen_smul {i : ℕ} (hi : i < 4) (k : Fin 728) :
    burnsideF48t_g23RGen i • burnsideF48t_g23Pt k =
      burnsideF48t_g23Pt (burnsideF48t_g23γ i k) := by
  have hv : burnsideF48t_g23RGen i • burnsideF48t_g23vec k =
      burnsideF48t_dv (burnsideF48t_g23MulVec (burnsideF48t_g23Mats ())[i]!
        (burnsideF48t_g23Pts ())[(k : ℕ)]!) := by
    rw [Units.smul_def, Matrix.smul_eq_mulVec, burnsideF48t_g23_coe_RGen hi, burnsideF48t_g23vec,
      burnsideF48t_dv_mulVec]
  have hw : burnsideF48t_g23vec (burnsideF48t_g23γ i k) =
      burnsideF48t_dv (burnsideF48t_g23Norm (burnsideF48t_g23MulVec (burnsideF48t_g23Mats ())[i]!
        (burnsideF48t_g23Pts ())[(k : ℕ)]!)) := by
    rw [burnsideF48t_g23vec, burnsideF48t_g23_ptsGen hi k]
  have h22 : ∀ w : Fin 14 → ZMod 3, (2 : ZMod 3) • (2 : ZMod 3) • w = w := fun w => by
    rw [smul_smul, show (2 : ZMod 3) * 2 = 1 by decide, one_smul]
  have hc : burnsideF48t_g23RGen i • ((2 : ZMod 3) • burnsideF48t_g23vec k) =
      (2 : ZMod 3) • (burnsideF48t_g23RGen i • burnsideF48t_g23vec k) := smul_comm _ _ _
  rw [burnsideF48t_g23Pt, burnsideF48t_g23Pt, Set.smul_set_insert, Set.smul_set_singleton, hc, hv,
    hw]
  rcases burnsideF48t_dv_norm (burnsideF48t_g23MulVec (burnsideF48t_g23Mats ())[i]!
      (burnsideF48t_g23Pts ())[(k : ℕ)]!) with h | h
  · rw [← h]
  · rw [h, h22, Set.pair_comm]

end Points

section Iso

theorem burnsideF48t_g23_card_R : Nat.card ↥burnsideF48t_g23R = 4245696 := by
  rw [← burnsideF48t_g23_map_adjointGroup (RingEquiv.refl (ZMod 3))]
  exact card_R3

end Iso

end CFSG.ASVolI
