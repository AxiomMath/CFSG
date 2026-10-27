module

public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGResDepType
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeProp1010
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoBstar
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Plus
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7Arith
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Dynkin

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e78_cartan_det_E7 {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (e : Fin 7 ≃ Λ)
    (hM : M = (CoxeterMatrix.E₇).reindex e) (hC : GGIntCartan M C) : C.det = 2 := by
  subst hM
  rw [l05nL3_det_eq_of_reindex (ggIntCartan_E₇) (ggAtMostOneMultipleEdge_E₇) e hC,
    CartanMatrix.E₇_det]

theorem e78_cartan_det_E8 {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (e : Fin 8 ≃ Λ)
    (hM : M = (CoxeterMatrix.E₈).reindex e) (hC : GGIntCartan M C) : C.det = 1 := by
  subst hM
  rw [l05nL3_det_eq_of_reindex (ggIntCartan_E₈) (ggAtMostOneMultipleEdge_E₈) e hC,
    CartanMatrix.E₈_det]

theorem e78_apply_eq_zero_of_fixed {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {φ : V ≃ₗ[ZMod p] V} {α : Module.Dual (ZMod p) V} {h x : V}
    (hlin : ∀ v, φ v = v - α v • h) (hfix : φ x = x) (hh : h ≠ 0) : α x = 0 := by
  have h1 : α x • h = 0 := by
    have := hlin x
    rw [hfix] at this
    exact sub_eq_self.mp this.symm
  rcases smul_eq_zero.mp h1 with h0 | h0
  · exact h0
  · exact absurd h0 hh

theorem e78_eq_zero_of_mem_span_of_cartan {p : ℕ} [Fact p.Prime]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (C : Matrix Λ Λ ℤ)
    (hCdet : IsUnit ((C.det : ℤ) : ZMod p))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {x : V} (hx : x ∈ Submodule.span (ZMod p) (Set.range h))
    (hα : ∀ i, α i x = 0) : x = 0 := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hx
  let A : Matrix Λ Λ (ZMod p) := Matrix.of fun i j => α i (h j)
  have hA : Matrix.mulVec A c = 0 := by
    funext j
    have h1 : α j (∑ i, c i • h i) = 0 := by rw [hc]; exact hα j
    simp only [map_sum, map_smul, smul_eq_mul] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, A, Matrix.of_apply]
    simpa only [mul_comm] using h1
  have hAeq : C.map (Int.castRingHom (ZMod p)) = A := by
    ext i j
    change (Int.castRingHom (ZMod p)) (C i j) = α i (h j)
    rw [show (Int.castRingHom (ZMod p)) (C i j) = ((C i j : ℤ) : ZMod p) from rfl]
    exact (hpair i j).symm
  have hunit : IsUnit (C.map (Int.castRingHom (ZMod p))).det := by
    have hcast : (C.map (Int.castRingHom (ZMod p))).det =
        (Int.castRingHom (ZMod p)) C.det := (RingHom.map_det _ C).symm
    rw [hcast]
    exact hCdet
  have hunitA : IsUnit A.det := by
    rw [← hAeq]
    exact hunit
  have hinj : Function.Injective (fun v => Matrix.mulVec A v) :=
    (Matrix.mulVec_injective_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hunitA)
  have hc0 : c = 0 := hinj (by change A.mulVec c = A.mulVec 0; rw [hA]; simp)
  have hzero : (∑ i, c i • h i) = 0 := by simp [hc0]
  rw [hc] at hzero
  exact hzero

theorem e78_span_isCompl_of_card_of_independent {p : ℕ} [Fact p.Prime]
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (C : Matrix Λ Λ ℤ) (hli : LinearIndependent (ZMod p) h)
    (hunit : IsUnit ((C.det : ℤ) : ZMod p))
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    {x : V} (hx0 : x ≠ 0) (hα : ∀ i, α i x = 0)
    (hcard : Nat.card V = p ^ (Fintype.card Λ + 1)) :
    Submodule.span (ZMod p) (Set.range h) ⊓ Submodule.span (ZMod p) ({x} : Set V) = ⊥ ∧
      Submodule.span (ZMod p) (Set.range h) ⊔ Submodule.span (ZMod p) ({x} : Set V) = ⊤ := by
  classical
  letI : Finite V := Nat.finite_of_card_ne_zero
    (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  set U : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range h) with hU
  set L : Submodule (ZMod p) V := Submodule.span (ZMod p) ({x} : Set V) with hL
  have hxU : x ∉ U := by
    intro hx
    exact hx0 (e78_eq_zero_of_mem_span_of_cartan h α C hunit hpair hx hα)
  have hdisj : U ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨hyU, hyL⟩ := hy
    rw [Submodule.mem_span_singleton] at hyL
    obtain ⟨c, rfl⟩ := hyL
    by_cases hc : c = 0
    · simp [hc]
    · have hx' : x ∈ U := by
        have h1 : c⁻¹ • (c • x) = x := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [← h1]
        exact U.smul_mem _ hyU
      exact absurd hx' hxU
  have hdimU : Module.finrank (ZMod p) U = Fintype.card Λ := by
    rw [hU, finrank_span_eq_card hli]
  have hdimL : Module.finrank (ZMod p) L = 1 := by
    rw [hL, finrank_span_singleton hx0]
  have hcardV : Nat.card V = Nat.card (ZMod p) ^ Module.finrank (ZMod p) V :=
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
  have hpn : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hfin : Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
    have h1 : p ^ Module.finrank (ZMod p) V = p ^ (Fintype.card Λ + 1) := by
      have hcv := hcardV
      rw [Nat.card_zmod] at hcv
      rw [← hcv, hcard]
    exact Nat.pow_right_injective hpn h1
  have hdimSup : Module.finrank (ZMod p) (↥(U ⊔ L)) = Fintype.card Λ + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U L
    rw [hdisj, hdimU, hdimL] at h
    simp only [finrank_bot, add_zero] at h
    omega
  refine ⟨hdisj, Submodule.eq_top_of_finrank_eq ?_⟩
  rw [hdimSup, hfin]

section UpperBoundCerts

theorem e78_bstar_card_le_E7 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .E7 ∧ lab.n = 1) p Bs L) :
    Nat.card Bs ≤ 3 ^ 8 := by
  have hcomm : commutator L = ⊤ := hM.1
  obtain ⟨lab, hlab, hhas, R, iR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp, htag, hn⟩ := hP.1
  obtain ⟨t, r, n⟩ := lab
  change t = .E7 at htag
  subst htag
  subst hn
  dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
  obtain ⟨K, iK, iFin, hK, ⟨e⟩⟩ := hhas
  let := iK
  let := iFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hE : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.2
  have hBN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  have hβ := card_range_ggBeta_mul_of (p := p) (Fact.out : p.Prime) hE hxBs hx1 hLx hcyc
    hcomm e hBN
  have hβe : IsElemAbelian p (ggBeta L e hBN).range :=
    isElemAbelian_range (fun a b : ↥Bs => Subtype.ext (CFSG.Open.IsElemAbelian.comm hE a.2 b.2))
      (fun a : ↥Bs => Subtype.ext (by simpa using hE.2 a a.2)) _
  have hβe3 : IsElemAbelian 3 (ggBeta L e hBN).range := by
    rw [← hp]
    exact hβe
  have hbound : Nat.card (ggBeta L e hBN).range ≤ 3 ^ 7 :=
    TableBExcTwo.card_le_mulAut_E7 hK2 hβe3
  calc Nat.card Bs = Nat.card (ggBeta L e hBN).range * p := hβ.symm
    _ = Nat.card (ggBeta L e hBN).range * 3 := by rw [hp]
    _ ≤ 3 ^ 7 * 3 := Nat.mul_le_mul_right 3 hbound
    _ = 3 ^ 8 := by norm_num

theorem e78_bstar_card_le_E8 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .E8 ∧ lab.n = 1) p Bs L) :
    Nat.card Bs ≤ 3 ^ 9 := by
  have hcomm : commutator L = ⊤ := hM.1
  obtain ⟨lab, hlab, hhas, R, iR, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp, htag, hn⟩ := hP.1
  obtain ⟨t, r, n⟩ := lab
  change t = .E8 at htag
  subst htag
  subst hn
  dsimp only [GGHasLabel, LargeEvenRawDatum] at hhas
  obtain ⟨K, iK, iFin, hK, ⟨e⟩⟩ := hhas
  let := iK
  let := iFin
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hE : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.2
  have hBN : Bs ≤ Subgroup.normalizer (L : Set G) := hP.2.1
  have hβ := card_range_ggBeta_mul_of (p := p) (Fact.out : p.Prime) hE hxBs hx1 hLx hcyc
    hcomm e hBN
  have hβe : IsElemAbelian p (ggBeta L e hBN).range :=
    isElemAbelian_range (fun a b : ↥Bs => Subtype.ext (CFSG.Open.IsElemAbelian.comm hE a.2 b.2))
      (fun a : ↥Bs => Subtype.ext (by simpa using hE.2 a a.2)) _
  have hβe3 : IsElemAbelian 3 (ggBeta L e hBN).range := by
    rw [← hp]
    exact hβe
  have hbound : Nat.card (ggBeta L e hBN).range ≤ 3 ^ 8 :=
    TableBExcTwo.card_le_mulAut_E8 hK2 hβe3
  calc Nat.card Bs = Nat.card (ggBeta L e hBN).range * p := hβ.symm
    _ = Nat.card (ggBeta L e hBN).range * 3 := by rw [hp]
    _ ≤ 3 ^ 8 * 3 := Nat.mul_le_mul_right 3 hbound
    _ = 3 ^ 9 := by norm_num

end UpperBoundCerts

section E8TorusCerts

theorem e78_e8_torus_model_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J : Subgroup G} {x : G} (hp : p = 3)
    (hcfg : GGConfig p B Bs x L D J)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hcomm : commutator L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E8 K)
    (hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hBsN hb⟩ ∈ TableBExc.RecipeID .E8 K) :
    ∃ w : GGTorusTorWit 3 8 L (ggGamma L hBsN).range,
      w.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ ∧
        ∃ e : CoxeterMatrix.E₈.Group ≃*
          ↥(ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range),
          ∀ k, (e (CoxeterMatrix.E₈.simple k) : MulAut ↥(ggGamma L hBsN).range) =
            ggConjAut (ggGamma L hBsN).range (w.hn k) := by
  subst hp
  have hp3 : (3 : ℕ).Prime := by norm_num
  obtain ⟨hrank, -⟩ := card_range_ggGamma_bstar_ge (p := 3) (r := 7) hcfg hcomm θ hBsN
    (TableBExcTwo.ggTorusLift_E8Two (K := K))
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by
    exact le_trans (by norm_num : 3 ^ 3 ≤ 3 ^ 7) hrank
  have hTB : GGTorusTBGroup 3 7 (TableBExc.RecipeGroup .E8 K)
      (TableBExc.RecipeID .E8 K) L (ggQuotHom θ) (ggGamma L hBsN).range :=
    ggTorusTBGroup_of_marking (p := 3) (r := 7) hp3 hcfg.2.1.2.1 hcfg.2.1.2.2.2 hcomm θ hBsN hBsI
      hrank h3
  have hq : 3 ∣ Nat.card K + 1 := by simp [hK]
  have hTD : GGTorusTorData 3 8 CartanMatrix.E₈ CoxeterMatrix.E₈ L
      (ggGamma L hBsN).range := by
    simpa [hK] using (ggTorusTorW_recipe_E8_three_plus (K := K) (hq := hq))
      L (ggQuotHom θ) (ggGamma L hBsN).range hTB
  obtain ⟨w, hw⟩ := hTD
  refine ⟨w, hw, ?_⟩
  exact (w.weylOfType hw ggIsWeylMatrix_E8 ggIntCartan_E₈).2.2

end E8TorusCerts

section E8ActualModule

private theorem e78_hC0_E8 {c : Fin 8 → ZMod 3}
    (hc : ∀ j, ∑ k, (CartanMatrix.E₈ j k : ZMod 3) * c k = 0) : c = 0 := by
  have hunit : IsUnit (CartanMatrix.E₈.map (Int.castRingHom (ZMod 3))) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : (CartanMatrix.E₈.map (Int.castRingHom (ZMod 3))).det = 1 := by
      change (CartanMatrix.E₈.map (fun x : ℤ => (x : ZMod 3))).det = 1
      rw [← Int.cast_det, CartanMatrix.E₈_det]
      norm_num
    rw [hdet]
    exact isUnit_one
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  exact hinj (by
    funext j
    simpa [Matrix.mulVec, dotProduct] using hc j)

theorem e78_e8_actual_module {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .E8 ∧ lab.n = 1) p Bs L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (ι : Additive ↥Bs ≃+ V) (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V)
      (α : Fin 8 → Module.Dual (ZMod 3) V),
      (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection 3 (φ i)) ∧
      (∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod 3)) ∧
      (∃ e : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (e (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
      Nat.card Bs = 3 ^ 9 ∧
      (∃ xv : V, xv = ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) ∧
        (∀ i, α i xv = 0) ∧
        IsCompl (Submodule.span (ZMod 3) (Set.range h))
          (Submodule.span (ZMod 3) ({xv} : Set V))) := by
  classical
  have hRig' := hRig
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hRig
  obtain ⟨t, r, n⟩ := lab
  cases t
  all_goals
    obtain ⟨R, iR, I, F, hQ⟩ := CFSG.GGQ2Prime.rawDatumLegacy_exists hraw
    obtain ⟨hsimple, hna, θ, hP⟩ := hQ
    obtain ⟨hp, hBsN, h3⟩ := hP
    obtain ⟨hp3, htag, hn⟩ := hp
    subst hn
    cases htag
    all_goals
      dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley] at hraw
      obtain ⟨K, iK, iFin, hK, hQ⟩ := hraw
      obtain ⟨hsimple, hna, θ, hP⟩ := hQ
      obtain ⟨hp, hBsN, h3⟩ := hP
      let := iK
      let := iFin
      have hK2 : Nat.card K = 2 := by simpa using hK
      haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (p := 2) (k := 1) Nat.prime_two (by norm_num) (by simpa using hK)
      have hBsI : ∀ (b : G) (hb : b ∈ Bs),
          ggLAut L θ ⟨b, hBsN hb⟩ ∈ TableBExc.RecipeID .E8 K :=
        fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb
      obtain ⟨w, hw, -⟩ := e78_e8_torus_model_core (p := p) hp.1 hH.1 hK2 hcomm hBsN θ hBsI
      have hTor : GGTorusTorData 3 8 CartanMatrix.E₈ CoxeterMatrix.E₈ L
          (ggGamma L hBsN).range := ⟨w, hw⟩
      have hInd : ∀ w' : GGTorusTorWit 3 8 L (ggGamma L hBsN).range,
          w'.Holds CartanMatrix.E₈ CoxeterMatrix.E₈ →
          ∀ c : Fin 8 → ZMod 3,
            (List.ofFn fun k => w'.cor k (ggZetaP 3 3 ^ (c k).val)).prod = 1 → c = 0 :=
        fun w' hw' => w'.coroot_indep_of_ker_zero (p := 3) (m := 3) (N := 8)
          (by norm_num) (by norm_num) (by norm_num) hw' (fun c hc => e78_hC0_E8 hc)
      have main : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
          (ι : Additive ↥Bs ≃+ V),
          ∃ (φ : Fin 8 → MulAut ↥Bs) (h : Fin 8 → V)
            (α : Fin 8 → Module.Dual (ZMod 3) V),
            (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
            (∀ i, GGIsReflection 3 (φ i)) ∧
            (∀ i j, α i (h j) = ((CartanMatrix.E₈ i j : ℤ) : ZMod 3)) ∧
            (∃ e : CoxeterMatrix.E₈.Group ≃* ↥(ggAutomizer L Bs),
              ∀ i, (e (CoxeterMatrix.E₈.simple i) : MulAut ↥Bs) = φ i) ∧
            ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
            Nat.card Bs = 3 ^ 9 ∧
            (∃ xv : V, xv = ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) ∧
              (∀ i, α i xv = 0) ∧
              IsCompl (Submodule.span (ZMod 3) (Set.range h))
                (Submodule.span (ZMod 3) ({xv} : Set V))) := by
        intro V _ _ ι
        have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
        have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
          hH.1.2.1.2.2.2
        have hBs3 : IsElemAbelian 3 Bs := hp.1 ▸ hBs
        have hS3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hp.1 ▸ hS
        have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
        have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
        have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
        have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) →
            IsPGroup p S → IsCyclic S := hH.1.1.2.2.2.2.2.2.1.2.2.2.2
        have hCx : ∀ b ∈ Bs, b ∈ Subgroup.centralizer (L : Set G) →
            b ∈ Subgroup.zpowers x := by
          intro b hb hbC
          have hmem : b ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hb, hbC⟩
          rw [inf_centralizer_eq_zpowers_of_elemAbelian (Fact.out : p.Prime) hBs hxBs hx1 hLx hcyc] at hmem
          exact hmem
        have hIC := hH.1.1.2.2.2.2.2.2.1.2.2.2.1
        have hQ : CFSG.IsQuasisimple ↥L :=
          (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥L).1 hIC.2.2
        have hZL : Subgroup.center ↥L = ⊥ := by
          have hKpow : Nat.card K = 2 ^ 1 := by simpa using hK
          have hθ : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.Blueprint.AdjointQuotient .E8 K :=
            θ.trans (Classical.choice (centerQuot_chevGroup_equiv K .E8))
          exact CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.center_eq_bot_of_E8
            hQ (by norm_num) hKpow hθ
        have hxL : x ∉ L := by
          intro hxmem
          have hxcenter : (⟨x, hxmem⟩ : ↥L) ∈ Subgroup.center ↥L := by
            rw [Subgroup.mem_center_iff]
            intro g
            apply Subtype.ext
            have hg := hLx g.2
            have hcomm : (g : G) * x = x * (g : G) := by
              simpa using (Subgroup.mem_centralizer_iff.mp hg x (by simp)).symm
            exact hcomm
          rw [hZL] at hxcenter
          have hx1' : x = 1 := by simpa using (Subgroup.mem_bot.mp hxcenter)
          exact hx1 hx1'
        have hcard : Nat.card Bs ≤ 3 ^ 9 := e78_bstar_card_le_E8 hH.1 hRig'
        obtain ⟨φ, h, α, hM, hMC, hφgen, hlin, hpair, hα1, hli, hspan, hclos, e, he⟩ :=
          ggTBDatumOpt_of_torW_weyl (p := 3) (m := 3) (N := 8) (C := CartanMatrix.E₈)
            (M := CoxeterMatrix.E₈) (by norm_num) (by norm_num) (by norm_num)
            ggIsWeylMatrix_E8 ggIntCartan_E₈ hBs3 hS3 hBsN hxBs hxL hCx hTor hInd hcard V ι
        refine ⟨φ, h, α, hlin, ?_, hpair, ⟨e, he⟩, hclos, ?_, ?_⟩
        · intro i
          have h2 : α i (h i) = 2 := by
            rw [hpair i i, hMC.1 i]
            norm_num
          exact ggIsReflection_of_eq_reflection (p := 3) (by norm_num) ι h2
            (ggLin_eq_reflection ι h2 (hlin i))
        · have hcardV : Nat.card V = 3 ^ 9 := by
            haveI : Fintype (Additive ↥Bs) := Fintype.ofFinite _
            haveI : Fintype V := Fintype.ofEquiv (Additive ↥Bs) ι.toEquiv
            haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
            have hdim : Module.finrank (ZMod 3) V = 9 := by
              have h1 := hli.fintype_card_le_finrank
              have h2 := finrank_span_finset_le_card (R := ZMod 3)
                (s := Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h))
              have hspan' : Submodule.span (ZMod 3)
                  (↑(Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)) : Set V) = ⊤ := by
                simpa [Finset.coe_image] using hspan
              rw [Set.finrank] at h2
              rw [hspan'] at h2
              have h2' : Module.finrank (ZMod 3) V ≤
                  (Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)).card := by
                simpa using h2
              have h2le : Module.finrank (ZMod 3) V ≤ 9 := by
                calc
                  _ ≤ (Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)).card := h2'
                  _ ≤ (Finset.univ : Finset (Option (Fin 8))).card := Finset.card_image_le
                  _ = 9 := by
                    rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
              simp only [Fintype.card_option, Fintype.card_fin] at h1
              omega
            rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V), Nat.card_zmod, hdim]
          rw [← Nat.card_congr Additive.toMul, Nat.card_congr ι.toEquiv, hcardV]
        · let xv : V := ι (Additive.ofMul ⟨x, hxBs⟩)
          have hx0 : xv ≠ 0 := by
            intro h0
            have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
              have h2 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
                apply ι.injective
                simpa [xv] using h0
              simpa using congrArg Additive.toMul h2
            exact hx1 (congrArg Subtype.val h1)
          have hdisj : Disjoint (Submodule.span (ZMod 3) (Set.range h))
              (Submodule.span (ZMod 3) ({xv} : Set V)) := by
            have hd := hli.disjoint_span_image
              (s := ({none} : Set (Option (Fin 8))))
              (t := Set.range (Option.some : Fin 8 → Option (Fin 8)))
              (by
                rw [Set.disjoint_left]
                intro o ho1 ho2
                rw [Set.mem_singleton_iff] at ho1
                subst o
                simp at ho2)
            have himage : ggOptFam xv h '' Set.range (Option.some : Fin 8 → Option (Fin 8)) =
                Set.range h := by
              ext v
              constructor
              · rintro ⟨o, ho, rfl⟩
                rcases ho with ⟨i, rfl⟩
                exact ⟨i, by simp [ggOptFam]⟩
              · rintro ⟨i, rfl⟩
                exact ⟨some i, ⟨i, rfl⟩, by simp [ggOptFam]⟩
            rw [himage] at hd
            simpa [xv, ggOptFam, Set.image_singleton] using hd.symm
          have hsup : Submodule.span (ZMod 3) (Set.range h) ⊔
              Submodule.span (ZMod 3) ({xv} : Set V) = ⊤ := by
            have hrange : Set.range (ggOptFam xv h) = Set.range h ∪ {xv} := by
              ext v
              constructor
              · rintro ⟨o, rfl⟩
                cases o with
                | none => simp [ggOptFam]
                | some i => simp [ggOptFam]
              · rintro (⟨i, rfl⟩ | rfl)
                · exact ⟨some i, by simp [ggOptFam]⟩
                · exact ⟨none, by simp [ggOptFam]⟩
            rw [hrange, Submodule.span_union] at hspan
            exact hspan
          exact ⟨xv, rfl, hα1, ⟨hdisj, codisjoint_iff.mpr hsup⟩⟩
      letI : AddCommGroup (Additive ↥Bs) :=
        { (inferInstance : AddGroup (Additive ↥Bs)) with
          add_comm := fun a b => by
            have h := (hH.1.2.1.2.1).1.is_comm.comm (Additive.toMul a) (Additive.toMul b)
            exact congrArg Additive.ofMul h }
      letI : Module (ZMod 3) (Additive ↥Bs) :=
        AddCommGroup.zmodModule (n := 3) fun a => by
          have h : (Additive.toMul a) ^ 3 = 1 :=
            Subtype.ext ((hp.1 ▸ hH.1.2.1.2.1).2 _ (Additive.toMul a).2)
          rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
      obtain ⟨φ', h', α', hlin, hrefl, hpair, ⟨e, he⟩, hclos, hcard, hcompl⟩ :=
        main (Additive ↥Bs) (AddEquiv.refl _)
      exact ⟨Additive ↥Bs, inferInstance, inferInstance, AddEquiv.refl _,
        φ', h', α', hlin, hrefl, hpair, ⟨e, he⟩, hclos, hcard, hcompl⟩

end E8ActualModule

section E7ActualModule

private theorem e78_hC0_E7 {c : Fin 7 → ZMod 3}
    (hc : ∀ j, ∑ k, (CartanMatrix.E₇ j k : ZMod 3) * c k = 0) : c = 0 := by
  have hunit : IsUnit (CartanMatrix.E₇.map (Int.castRingHom (ZMod 3))) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : (CartanMatrix.E₇.map (Int.castRingHom (ZMod 3))).det = 2 := by
      change (CartanMatrix.E₇.map (fun x : ℤ => (x : ZMod 3))).det = 2
      rw [← Int.cast_det, CartanMatrix.E₇_det]
      norm_num
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (by decide)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  exact hinj (by
    funext j
    simpa [Matrix.mulVec, dotProduct] using hc j)

theorem e78_e7_torus_model_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J : Subgroup G} {x : G} (hp : p = 3)
    (hcfg : GGConfig p B Bs x L D J)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hcomm : commutator L = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E7 K)
    (hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut L θ ⟨b, hBsN hb⟩ ∈ TableBExc.RecipeID .E7 K) :
    ∃ w : GGTorusTorWit 3 7 L (ggGamma L hBsN).range,
      w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇ ∧
        ∃ e : CoxeterMatrix.E₇.Group ≃*
          ↥(ggAutomizer (MulAut.conj : L →* MulAut L).range (ggGamma L hBsN).range),
          ∀ k, (e (CoxeterMatrix.E₇.simple k) : MulAut ↥(ggGamma L hBsN).range) =
            ggConjAut (ggGamma L hBsN).range (w.hn k) := by
  subst hp
  have hp3 : (3 : ℕ).Prime := by norm_num
  obtain ⟨hrank, -⟩ := card_range_ggGamma_bstar_ge (p := 3) (r := 6) hcfg hcomm θ hBsN
    (TableBExcTwo.ggTorusLift_E7Two (K := K))
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma L hBsN).range := by
    exact le_trans (by norm_num : 3 ^ 3 ≤ 3 ^ 6) hrank
  have hTB : GGTorusTBGroup 3 6 (TableBExc.RecipeGroup .E7 K)
      (TableBExc.RecipeID .E7 K) L (ggQuotHom θ) (ggGamma L hBsN).range :=
    ggTorusTBGroup_of_marking (p := 3) (r := 6) hp3 hcfg.2.1.2.1 hcfg.2.1.2.2.2 hcomm θ hBsN hBsI
      hrank h3
  have hq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hTD : GGTorusTorData 3 7 (CartanMatrix.E 7) CoxeterMatrix.E₇ L
      (ggGamma L hBsN).range := by
    simpa [hK] using
      (ggTorusTorW_recipe_E7_plus (K := K) (p := 3) (by norm_num) (by norm_num) hq)
        L (ggQuotHom θ) (ggGamma L hBsN).range hTB
  obtain ⟨w, hw⟩ := hTD
  refine ⟨w, hw, ?_⟩
  exact (w.weylOfType hw ggIsWeylMatrix_E7 ggIntCartan_E₇).2.2

theorem e78_e7_actual_module {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab.tag = .E7 ∧ lab.n = 1) p Bs L) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 3) V)
      (ι : Additive ↥Bs ≃+ V) (φ : Fin 7 → MulAut ↥Bs) (h : Fin 7 → V)
      (α : Fin 7 → Module.Dual (ZMod 3) V),
      (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
      (∀ i, GGIsReflection 3 (φ i)) ∧
      (∀ i j, α i (h j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3)) ∧
      (∃ e : CoxeterMatrix.E₇.Group ≃* ↥(ggAutomizer L Bs),
        ∀ i, (e (CoxeterMatrix.E₇.simple i) : MulAut ↥Bs) = φ i) ∧
      ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
      Nat.card Bs = 3 ^ 8 ∧
      (∃ xv : V, xv = ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) ∧
        (∀ i, α i xv = 0) ∧
        IsCompl (Submodule.span (ZMod 3) (Set.range h))
          (Submodule.span (ZMod 3) ({xv} : Set V))) := by
  classical
  have hRig' := hRig
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hRig
  obtain ⟨t, r, n⟩ := lab
  cases t
  all_goals
    obtain ⟨R, iR, I, F, hQ⟩ := CFSG.GGQ2Prime.rawDatumLegacy_exists hraw
    obtain ⟨hsimple, hna, θ, hP⟩ := hQ
    obtain ⟨hp, hBsN, h3⟩ := hP
    obtain ⟨hp3, htag, hn⟩ := hp
    subst hn
    cases htag
    all_goals
      dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeChevalley] at hraw
      obtain ⟨K, iK, iFin, hK, hQ⟩ := hraw
      obtain ⟨hsimple, hna, θ, hP⟩ := hQ
      obtain ⟨hp, hBsN, h3⟩ := hP
      let := iK
      let := iFin
      have hK2 : Nat.card K = 2 := by simpa using hK
      haveI : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (p := 2) (k := 1) Nat.prime_two (by norm_num) (by simpa using hK)
      have hBsI : ∀ (b : G) (hb : b ∈ Bs),
          ggLAut L θ ⟨b, hBsN hb⟩ ∈ TableBExc.RecipeID .E7 K :=
        fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb
      obtain ⟨w, hw, -⟩ := e78_e7_torus_model_core (p := p) hp.1 hH.1 hK2 hcomm hBsN θ hBsI
      have hTor : GGTorusTorData 3 7 (CartanMatrix.E 7) CoxeterMatrix.E₇ L
          (ggGamma L hBsN).range := ⟨w, hw⟩
      have hInd : ∀ w' : GGTorusTorWit 3 7 L (ggGamma L hBsN).range,
          w'.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇ →
          ∀ c : Fin 7 → ZMod 3,
            (List.ofFn fun k => w'.cor k (ggZetaP 3 3 ^ (c k).val)).prod = 1 → c = 0 :=
        fun w' hw' => w'.coroot_indep_of_ker_zero (p := 3) (m := 3) (N := 7)
          (by norm_num) (by norm_num) (by norm_num) hw' (fun c hc => e78_hC0_E7 hc)
      have main : ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
          (ι : Additive ↥Bs ≃+ V),
          ∃ (φ : Fin 7 → MulAut ↥Bs) (h : Fin 7 → V)
            (α : Fin 7 → Module.Dual (ZMod 3) V),
            (∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) ∧
            (∀ i, GGIsReflection 3 (φ i)) ∧
            (∀ i j, α i (h j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3)) ∧
            (∃ e : CoxeterMatrix.E₇.Group ≃* ↥(ggAutomizer L Bs),
              ∀ i, (e (CoxeterMatrix.E₇.simple i) : MulAut ↥Bs) = φ i) ∧
            ggAutomizer L Bs = Subgroup.closure (Set.range φ) ∧
            Nat.card Bs = 3 ^ 8 ∧
            (∃ xv : V, xv = ι (Additive.ofMul ⟨x, hH.1.tableB_facts.2.2.1⟩) ∧
              (∀ i, α i xv = 0) ∧
              IsCompl (Submodule.span (ZMod 3) (Set.range h))
                (Submodule.span (ZMod 3) ({xv} : Set V))) := by
        intro V _ _ ι
        have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
        have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
          hH.1.2.1.2.2.2
        have hBs3 : IsElemAbelian 3 Bs := hp.1 ▸ hBs
        have hS3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hp.1 ▸ hS
        have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
        have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
        have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
        have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) →
            IsPGroup p S → IsCyclic S := hH.1.1.2.2.2.2.2.2.1.2.2.2.2
        have hCx : ∀ b ∈ Bs, b ∈ Subgroup.centralizer (L : Set G) →
            b ∈ Subgroup.zpowers x := by
          intro b hb hbC
          have hmem : b ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨hb, hbC⟩
          rw [inf_centralizer_eq_zpowers_of_elemAbelian (Fact.out : p.Prime) hBs hxBs hx1 hLx hcyc] at hmem
          exact hmem
        have hIC := hH.1.1.2.2.2.2.2.2.1.2.2.2.1
        have hQ : CFSG.IsQuasisimple ↥L :=
          (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥L).1 hIC.2.2
        have hZL : Subgroup.center ↥L = ⊥ := by
          have hKpow : Nat.card K = 2 ^ 1 := by simpa using hK
          have hθ : ↥L ⧸ Subgroup.center ↥L ≃* CFSG.Blueprint.AdjointQuotient .E7 K :=
            θ.trans (Classical.choice (centerQuot_chevGroup_equiv K .E7))
          exact CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7
            hQ (by norm_num) hKpow hθ
        have hxL : x ∉ L := by
          intro hxmem
          have hxcenter : (⟨x, hxmem⟩ : ↥L) ∈ Subgroup.center ↥L := by
            rw [Subgroup.mem_center_iff]
            intro g
            apply Subtype.ext
            have hg := hLx g.2
            have hcomm : (g : G) * x = x * (g : G) := by
              simpa using (Subgroup.mem_centralizer_iff.mp hg x (by simp)).symm
            exact hcomm
          rw [hZL] at hxcenter
          have hx1' : x = 1 := by simpa using (Subgroup.mem_bot.mp hxcenter)
          exact hx1 hx1'
        have hcard : Nat.card Bs ≤ 3 ^ 8 := e78_bstar_card_le_E7 hH.1 hRig'
        obtain ⟨φ, h, α, hM, hMC, hφgen, hlin, hpair, hα1, hli, hspan, hclos, e, he⟩ :=
          ggTBDatumOpt_of_torW_weyl (p := 3) (m := 3) (N := 7) (C := CartanMatrix.E 7)
            (M := CoxeterMatrix.E₇) (by norm_num) (by norm_num) (by norm_num)
            ggIsWeylMatrix_E7 ggIntCartan_E₇ hBs3 hS3 hBsN hxBs hxL hCx hTor hInd hcard V ι
        refine ⟨φ, h, α, hlin, ?_, hpair, ⟨e, he⟩, hclos, ?_, ?_⟩
        · intro i
          have h2 : α i (h i) = 2 := by
            rw [hpair i i, hMC.1 i]
            norm_num
          exact ggIsReflection_of_eq_reflection (p := 3) (by norm_num) ι h2
            (ggLin_eq_reflection ι h2 (hlin i))
        · have hcardV : Nat.card V = 3 ^ 8 := by
            haveI : Fintype (Additive ↥Bs) := Fintype.ofFinite _
            haveI : Fintype V := Fintype.ofEquiv (Additive ↥Bs) ι.toEquiv
            haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
            have hdim : Module.finrank (ZMod 3) V = 8 := by
              have h1 := hli.fintype_card_le_finrank
              have h2 := finrank_span_finset_le_card (R := ZMod 3)
                (s := Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h))
              have hspan' : Submodule.span (ZMod 3)
                  (↑(Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)) : Set V) = ⊤ := by
                simpa [Finset.coe_image] using hspan
              rw [Set.finrank] at h2
              rw [hspan'] at h2
              have h2' : Module.finrank (ZMod 3) V ≤
                  (Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)).card := by
                simpa using h2
              have h2le : Module.finrank (ZMod 3) V ≤ 8 := by
                calc
                  _ ≤ (Finset.univ.image (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)).card := h2'
                  _ ≤ (Finset.univ : Finset (Option (Fin 7))).card := Finset.card_image_le
                  _ = 8 := by
                    rw [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
              simp only [Fintype.card_option, Fintype.card_fin] at h1
              omega
            rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V), Nat.card_zmod, hdim]
          rw [← Nat.card_congr Additive.toMul, Nat.card_congr ι.toEquiv, hcardV]
        · let xv : V := ι (Additive.ofMul ⟨x, hxBs⟩)
          have hx0 : xv ≠ 0 := by
            intro h0
            have h1 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by
              have h2 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
                apply ι.injective
                simpa [xv] using h0
              simpa using congrArg Additive.toMul h2
            exact hx1 (congrArg Subtype.val h1)
          have hdisj : Disjoint (Submodule.span (ZMod 3) (Set.range h))
              (Submodule.span (ZMod 3) ({xv} : Set V)) := by
            have hd := hli.disjoint_span_image
              (s := ({none} : Set (Option (Fin 7))))
              (t := Set.range (Option.some : Fin 7 → Option (Fin 7)))
              (by
                rw [Set.disjoint_left]
                intro o ho1 ho2
                rw [Set.mem_singleton_iff] at ho1
                subst o
                simp at ho2)
            have himage : ggOptFam xv h '' Set.range (Option.some : Fin 7 → Option (Fin 7)) =
                Set.range h := by
              ext v
              constructor
              · rintro ⟨o, ho, rfl⟩
                rcases ho with ⟨i, rfl⟩
                exact ⟨i, by simp [ggOptFam]⟩
              · rintro ⟨i, rfl⟩
                exact ⟨some i, ⟨i, rfl⟩, by simp [ggOptFam]⟩
            rw [himage] at hd
            simpa [xv, ggOptFam, Set.image_singleton] using hd.symm
          have hsup : Submodule.span (ZMod 3) (Set.range h) ⊔
              Submodule.span (ZMod 3) ({xv} : Set V) = ⊤ := by
            have hrange : Set.range (ggOptFam xv h) = Set.range h ∪ {xv} := by
              ext v
              constructor
              · rintro ⟨o, rfl⟩
                cases o with
                | none => simp [ggOptFam]
                | some i => simp [ggOptFam]
              · rintro (⟨i, rfl⟩ | rfl)
                · exact ⟨some i, by simp [ggOptFam]⟩
                · exact ⟨none, by simp [ggOptFam]⟩
            rw [hrange, Submodule.span_union] at hspan
            exact hspan
          exact ⟨xv, rfl, hα1, ⟨hdisj, codisjoint_iff.mpr hsup⟩⟩
      letI : AddCommGroup (Additive ↥Bs) :=
        { (inferInstance : AddGroup (Additive ↥Bs)) with
          add_comm := fun a b => by
            have h := (hH.1.2.1.2.1).1.is_comm.comm (Additive.toMul a) (Additive.toMul b)
            exact congrArg Additive.ofMul h }
      letI : Module (ZMod 3) (Additive ↥Bs) :=
        AddCommGroup.zmodModule (n := 3) fun a => by
          have h : (Additive.toMul a) ^ 3 = 1 :=
            Subtype.ext ((hp.1 ▸ hH.1.2.1.2.1).2 _ (Additive.toMul a).2)
          rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
      obtain ⟨φ', h', α', hlin, hrefl, hpair, ⟨e, he⟩, hclos, hcard, hcompl⟩ :=
        main (Additive ↥Bs) (AddEquiv.refl _)
      exact ⟨Additive ↥Bs, inferInstance, inferInstance, AddEquiv.refl _,
        φ', h', α', hlin, hrefl, hpair, ⟨e, he⟩, hclos, hcard, hcompl⟩

end E7ActualModule

end CFSG.StandardType

end
