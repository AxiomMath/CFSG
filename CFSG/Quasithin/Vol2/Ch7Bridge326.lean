module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Background.BlueprintB2Reduced
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLieModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)
open scoped IsMulCommutative

theorem sq_eq_one_of_mem_closure_of_comm {G : Type*} [Group G] {S : Set G}
    (hS : ∀ s ∈ S, s ^ 2 = 1)
    (hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) {x : G}
    (hx : x ∈ Subgroup.closure S) : x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := hc x hx y hy
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

private theorem nonempty_mulEquiv_zmod_prod_aux {p : ℕ} [hp : Fact p.Prime] {X : Type*}
    [CommGroup X] [Finite X] [Module (ZMod p) (Additive X)] (hcard : Nat.card X = p ^ 2) :
    Nonempty (X ≃* Multiplicative (ZMod p × ZMod p)) := by
  have : Module.Finite (ZMod p) (Additive X) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod p) (Additive X) =
      Module.finrank (ZMod p) (ZMod p × ZMod p) := by
    have h1 := FiniteField.pow_finrank_eq_natCard p (Additive X)
    have h2 : Module.finrank (ZMod p) (ZMod p × ZMod p) = 2 := by simp
    rw [h2]
    have h3 : Nat.card (Additive X) = p ^ 2 := hcard
    rw [h3] at h1
    exact Nat.pow_right_injective hp.out.two_le h1
  obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (R := ZMod p) hfin
  exact ⟨MulEquiv.toAdditiveLeft.symm e.toAddEquiv⟩

theorem nonempty_mulEquiv_zmod_prod {p : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (hcard : Nat.card X = p ^ 2) (hexp : ∀ x : X, x ^ p = 1) :
    Nonempty (X ≃* Multiplicative (ZMod p × ZMod p)) := by
  let _ : CommGroup X := IsPGroup.commGroupOfCardEqPrimeSq hcard
  have hA : ∀ a : Additive X, p • a = 0 := fun a => by
    change Additive.ofMul ((Additive.toMul a) ^ p) = Additive.ofMul 1
    rw [hexp]
  exact @nonempty_mulEquiv_zmod_prod_aux p hp X (IsPGroup.commGroupOfCardEqPrimeSq hcard) _
    (AddCommGroup.zmodModule hA) hcard

private theorem twoResidual_eq_oTwoUpper_bridge {D : Type*} [Group D] [Finite D]
    (X : Subgroup D) : twoResidual X = oTwoUpper X := by
  unfold twoResidual
  exact le_antisymm (iInf₂_le _ ⟨oTwoUpper_le X, le_normalizer_oTwoUpper X,
    fun _ hx => exists_pow_mem_oTwoUpper X hx⟩)
    (le_iInf₂ fun _ hN => oTwoUpper_le_of_pow_mem hN.2.2)

theorem two_le_of_lieModel_psl_two {X : Type} [Group X] {n : ℕ} (h : LieModel X .PSL 2 2 n) :
    2 ≤ n := by
  rcases h with ⟨-, hadm, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, h1, -, h2, -⟩ := hadm
    by_contra hn
    have hn1 : n = 1 := by omega
    subst hn1
    exact h2 rfl
  all_goals exact absurd h0 (by norm_num)

private theorem nonempty_mulEquiv_SL32_of_lieModel {X : Type} [Group X]
    (h : LieModel X .PSL 3 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.Blueprint.LieModel.nonempty_mulEquiv_SL_three_two h

variable {G : Type} [Group G]

theorem realizesMod_of_eq {W₁ W₂ : Subgroup G} (h : W₁ = W₂) [IsMulCommutative ↥W₁]
    [IsMulCommutative ↥W₂] (D : FFModel) (X : Subgroup G)
    (hD : D.Realizes (V := ↥W₂) (autOn X W₂) ⊤ ⊥) :
    D.RealizesMod (V := ↥W₁) (autOn X W₁) := by
  subst h
  exact hD

theorem tensorNatModel_eq (d : ℕ) (K : Type) [Field K] :
    tensorNatModel d K = tensorPairModel (StatedSL d K) (StatedSL d K) :=
  rfl

theorem isElemAbelian_fsuVM [Finite G] {T L I : Subgroup G} (hfsu : FSU G T L I)
    [IsMulCommutative ↥(fsuVM T L I)] : IsElemAbelian 2 (fsuVM T L I) := by
  refine ⟨inferInstance, ?_⟩
  have hI : ∀ i ∈ I, i ^ 2 = 1 := fun i hi => by
    obtain ⟨r, hr, rfl⟩ := hfsu.irrPlus.1 hi
    obtain ⟨-, -, hRc⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥(L ⊔ T)) 2
    obtain ⟨-, -, h3⟩ := BlueprintB2.mem_centerTorsion_iff.1 (hRc hr)
    simpa using congrArg Subtype.val h3
  have hcomm : ∀ x ∈ fsuVM T L I, ∀ y ∈ fsuVM T L I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥(fsuVM T L I)) ⟨y, hy⟩)
  have hVVM : fsuV T I ≤ fsuVM T L I := le_conjClosure _ _
  have hV : ∀ v ∈ fsuV T I, v ^ 2 = 1 := by
    intro v hv
    refine sq_eq_one_of_mem_closure_of_comm ?_ (fun x hx y hy => hcomm x (hVVM hx) y (hVVM hy))
      hv
    rintro _ ⟨t, -, i, hi, rfl⟩
    rw [conj_pow, hI i hi, mul_one, mul_inv_cancel]
  intro v hv
  refine sq_eq_one_of_mem_closure_of_comm ?_ hcomm hv
  rintro _ ⟨m, -, w, hw, rfl⟩
  rw [conj_pow, hV w hw, mul_one, mul_inv_cancel]

theorem fsuVM_le_normalizer_fsuCVM {T L I : Subgroup G} [IsMulCommutative ↥(fsuVM T L I)] :
    fsuVM T L I ≤ Subgroup.normalizer (fsuCVM T L I : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hc : g * h = h * g :=
      congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : ↥(fsuVM T L I)) ⟨h, hh.1⟩)
    rw [hc, mul_inv_cancel_right]
    exact hh
  · intro hh
    have hhV : g * h * g⁻¹ ∈ fsuVM T L I := hh.1
    have hhV' : h ∈ fsuVM T L I := by
      have := (fsuVM T L I).mul_mem ((fsuVM T L I).mul_mem ((fsuVM T L I).inv_mem hg) hhV) hg
      simpa [mul_assoc] using this
    have hc : g * h = h * g :=
      congrArg Subtype.val (mul_comm' (⟨g, hg⟩ : ↥(fsuVM T L I)) ⟨h, hhV'⟩)
    rw [hc, mul_inv_cancel_right] at hh
    exact hh

theorem tmpL6_3_2_6_of_stmt3_2_6 (h326 : Stmt3_2_6) : Vol2.Ch10.TmpL6_3_2_6 := by
  intro G _ _ T L I hfsu hlt
  obtain ⟨⟨hcV, hqV⟩, hcVM, hqVM, hcases⟩ := h326 G T L I hfsu hlt.ne
  refine ⟨⟨hcV, hqV⟩, ⟨hcVM, hqVM⟩, ?_⟩
  rcases hcases with ⟨n, K, _, _, hcard, hlie, hV0, hVVM, hreal⟩ | ⟨-, hV0, hVVM, hreal⟩ | h3
  ·
    refine Or.inl ⟨hcV, hV0, hVVM, Or.inl ⟨n, hlt, two_le_of_lieModel_psl_two hlie, K,
      inferInstance, inferInstance, hcard, ?_⟩⟩
    rw [← tensorNatModel_eq]
    exact realizesMod_of_eq hVVM _ _ hreal
  ·
    refine Or.inl ⟨hcV, hV0, hVVM, Or.inr ⟨hlt, ?_⟩⟩
    rw [← tensorNatModel_eq]
    exact realizesMod_of_eq hVVM _ _ hreal
  ·
    obtain ⟨ha, hb, hb', hc⟩ := h3
    refine Or.inr ⟨hcVM, isElemAbelian_fsuVM hfsu, fsuVM_le_normalizer_fsuCVM, ha, hb, hb', ?_⟩
    rcases hc with hi | ⟨⟨e⟩, hVVM, ⟨s, hsT, hsn⟩, hall, hcard⟩ | ⟨_, hlie, hsum, h5⟩
    · exact Or.inl hi
    · obtain ⟨hU, hUs⟩ := hall s hsT hsn
      exact Or.inr (Or.inl ⟨⟨e.trans (MulAut.congr
        (specialLinearGroupEquivStatedSL 3 (ZMod 2))).symm⟩, hVVM, hcard, s, hsT.1, hsT.2, hsn,
        hU, hUs⟩)
    · refine Or.inr (Or.inr ⟨nonempty_mulEquiv_SL32_of_lieModel hlie, hsum, ?_⟩)
      have : Finite (MulAut ↥(fsuVM T L I)) := MulEquiv.finite_left
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      rw [twoResidual_eq_oTwoUpper_bridge]
      rcases h5 with h5 | ⟨h25, hexp⟩
      · exact Or.inl ⟨mulEquivOfPrimeCardEq h5 (by simp)⟩
      · exact Or.inr (nonempty_mulEquiv_zmod_prod (p := 5) (by rw [h25]; norm_num)
          (fun x => Subtype.ext (by simpa using hexp x.1 x.2)))

end CFSG.Quasithin.H13
