module

public import CFSG.LocalAnalysis.StandardType.GGResidualRk1Frame
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlus
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
import CFSG.LocalAnalysis.StandardType.GGReflClosedOfWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylEltOfAutomizer
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlusAux
import CFSG.LocalAnalysis.StandardType.GGResidualExcRows
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflTypeE
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaExcPlusAux2
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6FrameAux
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Plus
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaCenter
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggFix_of_overGamma_of_involution {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    {hN : Bs ≤ Subgroup.normalizer (X : Set G)} {c c' : MulAut ↥Bs} (hc' : c' ∈ ggAutomizer X Bs)
    (hc'2 : c' * c' = 1) {a : MulAut ↥(ggGamma X hN).range} (hov : GGOverGamma hN c a)
    (hov' : GGOverGamma hN c' a) {b : ↥Bs} (hb : c b = b) : c' b = b := by
  obtain ⟨g, hgX, -, hcg⟩ := mem_ggAutomizer_iff.mp hc'
  set d : ↥Bs := c' b * b⁻¹ with hd
  have hγ : (ggGamma X hN).rangeRestrict (c' b) = (ggGamma X hN).rangeRestrict b := by
    rw [hov' b, ← hov b, hb]
  have hd1 : ggGamma X hN d = 1 := by
    have h1 : (ggGamma X hN).rangeRestrict d = 1 := by
      rw [hd, map_mul, map_inv, hγ, mul_inv_cancel]
    exact congrArg Subtype.val h1
  have hdC : (d : G) ∈ Subgroup.centralizer (X : Set G) := (ggGamma_eq_one_iff X hN d).mp hd1
  have hc'd : c' d = d := by
    apply Subtype.ext
    rw [hcg d, Subgroup.mem_centralizer_iff.mp hdC g hgX, mul_inv_cancel_right]
  have hc'b : c' b = d * b := by rw [hd, inv_mul_cancel_right]
  have hdd : d * d = 1 := by
    have hcc : c' (c' b) = b := by rw [← MulAut.mul_apply, hc'2, MulAut.one_apply]
    rw [hc'b, map_mul, hc'd, hc'b, ← mul_assoc] at hcc
    exact mul_right_cancel (hcc.trans (one_mul b).symm)
  have hdp : d ^ p = 1 := Subtype.ext (by simpa using hBs.2 d d.2)
  have hd2 : d ^ 2 = 1 := by rw [pow_two, hdd]
  have hgcd : p.gcd 2 = 1 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hd1' : d = 1 := by
    have h1 : d ^ p.gcd 2 = 1 := pow_gcd_eq_one.mpr ⟨hdp, hd2⟩
    rwa [hgcd, pow_one] at h1
  rw [hc'b, hd1', one_mul]

theorem ggRankOneIn_congr_fix {G : Type} [Group G] {Bs X : Subgroup G} {r r' : MulAut ↥Bs}
    (h : ∀ b : ↥Bs, r b = b ↔ r' b = b) : ggRankOneIn X Bs r = ggRankOneIn X Bs r' := by
  have hH : ggHyperplane Bs r = ggHyperplane Bs r' := by
    unfold ggHyperplane
    congr 1
    ext b
    exact h b
  unfold ggRankOneIn
  rw [hH]

private theorem isConj_simple_of_matrix_eq {τ : Tag} {M : CoxeterMatrix (Fin τ.rank)}
    (hM : M = CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan τ))
    {a b : Fin τ.rank} (hab : M a b = 3) :
    IsConj (simple τ a) (simple τ b) := by
  have hodd : Odd (M a b) := by
    rw [hab]
    exact ⟨1, by norm_num⟩
  have hconj := S2MathFi1451.isConj_simple_of_odd (M := M) (j := a) (l := b) hodd
  rw [hM] at hconj
  simpa [simple, coxeterSystem, CoxeterMatrix.toCoxeterSystem_simple] using hconj

theorem isConj_simple_of_tag_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (i j : Fin τ.rank) :
    IsConj (simple τ i) (simple τ j) := by
  rcases hτ with rfl | rfl | rfl
  · have hM6 : CoxeterMatrix.E₆ =
        CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E6) := by
      refine (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E6) ?_).symm
      have hc : Tag.cartan .E6 = CartanMatrix.E 6 := cartanE_eq 6
      rw [hc]
      exact ggIntCartan_E₆
    have h02 : IsConj (simple .E6 0) (simple .E6 2) :=
      isConj_simple_of_matrix_eq hM6 (by decide)
    have h23 : IsConj (simple .E6 2) (simple .E6 3) :=
      isConj_simple_of_matrix_eq hM6 (by decide)
    have h13 : IsConj (simple .E6 1) (simple .E6 3) :=
      isConj_simple_of_matrix_eq hM6 (by decide)
    have h34 : IsConj (simple .E6 3) (simple .E6 4) :=
      isConj_simple_of_matrix_eq hM6 (by decide)
    have h45 : IsConj (simple .E6 4) (simple .E6 5) :=
      isConj_simple_of_matrix_eq hM6 (by decide)
    have h03 := h02.trans h23
    have h01 := h03.trans (isConj_comm.mp h13)
    have h04 := h03.trans h34
    have h05 := h04.trans h45
    have hroot : ∀ k : Fin Tag.E6.rank, IsConj (simple .E6 0) (simple .E6 k) := by
      intro k
      fin_cases k
      · exact IsConj.refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
    exact (isConj_comm.mp (hroot i)).trans (hroot j)
  · have hM7 : CoxeterMatrix.E₇ =
        CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E7) := by
      refine (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E7) ?_).symm
      have hc : Tag.cartan .E7 = CartanMatrix.E 7 := cartanE_eq 7
      rw [hc]
      exact ggIntCartan_E₇
    have h02 : IsConj (simple .E7 0) (simple .E7 2) :=
      isConj_simple_of_matrix_eq hM7 (by decide)
    have h23 : IsConj (simple .E7 2) (simple .E7 3) :=
      isConj_simple_of_matrix_eq hM7 (by decide)
    have h13 : IsConj (simple .E7 1) (simple .E7 3) :=
      isConj_simple_of_matrix_eq hM7 (by decide)
    have h34 : IsConj (simple .E7 3) (simple .E7 4) :=
      isConj_simple_of_matrix_eq hM7 (by decide)
    have h45 : IsConj (simple .E7 4) (simple .E7 5) :=
      isConj_simple_of_matrix_eq hM7 (by decide)
    have h56 : IsConj (simple .E7 5) (simple .E7 6) :=
      isConj_simple_of_matrix_eq hM7 (by decide)
    have h03 := h02.trans h23
    have h01 := h03.trans (isConj_comm.mp h13)
    have h04 := h03.trans h34
    have h05 := h04.trans h45
    have h06 := h05.trans h56
    have hroot : ∀ k : Fin Tag.E7.rank, IsConj (simple .E7 0) (simple .E7 k) := by
      intro k
      fin_cases k
      · exact IsConj.refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
      · exact h06
    exact (isConj_comm.mp (hroot i)).trans (hroot j)
  · have hM8 : CoxeterMatrix.E₈ =
        CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E8) := by
      refine (coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E8) ?_).symm
      have hc : Tag.cartan .E8 = CartanMatrix.E 8 := cartanE_eq 8
      rw [hc]
      exact ggIntCartan_E₈
    have h02 : IsConj (simple .E8 0) (simple .E8 2) :=
      isConj_simple_of_matrix_eq hM8 (by decide)
    have h23 : IsConj (simple .E8 2) (simple .E8 3) :=
      isConj_simple_of_matrix_eq hM8 (by decide)
    have h13 : IsConj (simple .E8 1) (simple .E8 3) :=
      isConj_simple_of_matrix_eq hM8 (by decide)
    have h34 : IsConj (simple .E8 3) (simple .E8 4) :=
      isConj_simple_of_matrix_eq hM8 (by decide)
    have h45 : IsConj (simple .E8 4) (simple .E8 5) :=
      isConj_simple_of_matrix_eq hM8 (by decide)
    have h56 : IsConj (simple .E8 5) (simple .E8 6) :=
      isConj_simple_of_matrix_eq hM8 (by decide)
    have h67 : IsConj (simple .E8 6) (simple .E8 7) :=
      isConj_simple_of_matrix_eq hM8 (by decide)
    have h03 := h02.trans h23
    have h01 := h03.trans (isConj_comm.mp h13)
    have h04 := h03.trans h34
    have h05 := h04.trans h45
    have h06 := h05.trans h56
    have h07 := h06.trans h67
    have hroot : ∀ k : Fin Tag.E8.rank, IsConj (simple .E8 0) (simple .E8 k) := by
      intro k
      fin_cases k
      · exact IsConj.refl _
      · exact h01
      · exact h02
      · exact h03
      · exact h04
      · exact h05
      · exact h06
      · exact h07
    exact (isConj_comm.mp (hroot i)).trans (hroot j)

theorem ggExcPlusModel_exists_conj_of_isReflection
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A) (hM : GGExcPlusWeylModel τ p A)
    {a a' : MulAut ↥A} (ha : a ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (haR : GGIsReflection p a) (ha' : a' ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (haR' : GGIsReflection p a') :
    ∃ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, a' = v * a * v⁻¹ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨Φ, w, hw, hact, hnorm⟩ := hM
  have hN : ∀ i, MulAut.conj (w i) ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    fun i => conj_mem_normalizer_of_torusWeylElt hsc (hw i)
  let ρ : Fin τ.rank → MulAut A := fun i => ggConjAut A (hN i)
  have hρ : ∀ i (b : A), Multiplicative.toAdd (Φ (ρ i b)) =
      TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ b)) :=
    fun i b => hact i b (ρ i b) (ggConjAut_apply A (hN i) b)
  have hreal : ∀ u : WeylGroup τ, ∃ φ ∈ Subgroup.closure (Set.range ρ),
      ∀ b : A, Multiplicative.toAdd (Φ (φ b)) =
        TableBExc.torusAct τ p u (Multiplicative.toAdd (Φ b)) := by
    intro u
    obtain ⟨ω, rfl⟩ := (coxeterSystem τ).wordProd_surjective u
    induction ω with
    | nil =>
      refine ⟨1, Subgroup.one_mem _, fun b => ?_⟩
      rw [CoxeterSystem.wordProd_nil, TableBExc.torusAct_one]
      rfl
    | cons i ω ih =>
      obtain ⟨φ, hφ, hφact⟩ := ih
      refine ⟨ρ i * φ, Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hφ, fun b => ?_⟩
      rw [CoxeterSystem.wordProd_cons, TableBExc.torusAct_mul, MulAut.mul_apply, hρ, hφact]
  have hAL : ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      Subgroup.closure (Set.range ρ) := by
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le _).mpr ?_
      rintro φ ⟨g, hgH, hgN, hφ⟩
      obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hgH
      obtain ⟨u, hu⟩ := hnorm m hgN
      obtain ⟨φu, hφu, hact'⟩ := hreal u
      have hφeq : φ = φu := by
        refine MulEquiv.ext fun b => ?_
        apply Φ.injective
        apply Multiplicative.toAdd.injective
        rw [hact' b]
        exact hu b (φ b) (hφ b)
      rw [hφeq]
      exact hφu
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨w i, rfl⟩) (hN i)
  let V := Fin τ.rank → ZMod p
  let ι : Additive A ≃+ V := Φ.toAdditive
  let h : Fin τ.rank → V := fun i => Pi.single i 1
  let α : Fin τ.rank → Module.Dual (ZMod p) V := fun i =>
    ∑ j : Fin τ.rank, ((τ.cartan i j : ℤ) : ZMod p) • (LinearMap.proj j : V →ₗ[ZMod p] ZMod p)
  have hα_apply : ∀ (i : Fin τ.rank) (v : V),
      α i v = ∑ j, ((τ.cartan i j : ℤ) : ZMod p) * v j := by
    intro i v
    simp [α, smul_eq_mul, LinearMap.proj]
  have hpair : ∀ i j, α i (h j) = ((τ.cartan i j : ℤ) : ZMod p) := by
    intro i j
    rw [hα_apply]
    rw [Finset.sum_eq_single j]
    · dsimp [h]
      rw [Pi.single_eq_same, mul_one]
    · intro b _ hbj
      dsimp [h]
      rw [Pi.single_eq_of_ne hbj, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hind : LinearIndependent (ZMod p) h := by
    have hb : (⇑(Pi.basisFun (ZMod p) (Fin τ.rank)) : Fin τ.rank → V) = h := by
      funext i
      simp [h]
    exact hb ▸ (Pi.basisFun (ZMod p) (Fin τ.rank)).linearIndependent
  have hs : ∀ i (v : V), ggLin (p := p) ι (ρ i) v = v - α i v • h i := by
    intro i v
    let b : A := Additive.toMul (ι.symm v)
    have hv : ι (Additive.ofMul b) = v := by
      dsimp [b]
      exact AddEquiv.apply_symm_apply ι v
    calc ggLin (p := p) ι (ρ i) v
        = ggLin (p := p) ι (ρ i) (ι (Additive.ofMul b)) :=
          congrArg (fun x => ggLin (p := p) ι (ρ i) x) hv.symm
      _ = ι (Additive.ofMul (ρ i b)) := ggLin_apply_ofMul ι (ρ i) b
      _ = Multiplicative.toAdd (Φ (ρ i b)) := rfl
      _ = TableBExc.torusAct τ p (simple τ i) (Multiplicative.toAdd (Φ b)) := hρ i b
      _ = Multiplicative.toAdd (Φ b) -
            (∑ j, ((τ.cartan i j : ℤ) : ZMod p) * (Multiplicative.toAdd (Φ b)) j) •
              Pi.single i 1 := ggExcPlus_torusAct_simple_eq τ i _
      _ = v - α i v • h i := by
          have hb : Multiplicative.toAdd (Φ b) = v := hv
          rw [hb, ← hα_apply]
  have hRC : GGReflClosed (fun i : Fin τ.rank => ggLin (p := p) ι (ρ i)) :=
    ggReflClosed_of_indep (p := p) hp2 (isFiniteType_cartan τ) (SpJoinRefl.ggIntCartan_tag_E hτ)
      h α hpair hind (fun i => ggLin (p := p) ι (ρ i)) hs
  have hconj : GGReflConjSimple p
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ρ :=
    ggReflConjSimple_of_reflClosed (G := MulAut L') (Bs := A)
      (L := (MulAut.conj : L' →* MulAut L').range) ι ρ hAL hRC
  obtain ⟨w₁, hw₁, i, hai⟩ := hconj a ha haR
  obtain ⟨w₂, hw₂, j, ha'j⟩ := hconj a' ha' haR'
  obtain ⟨u, hu⟩ := isConj_iff.mp (isConj_simple_of_tag_E hτ i j)
  obtain ⟨φu, hφu, hφua⟩ := hreal u
  have hφuA : φu ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
    rw [hAL]
    exact hφu
  have hφu_inv : ∀ b : A, Multiplicative.toAdd (Φ (φu⁻¹ b)) =
      TableBExc.torusAct τ p u⁻¹ (Multiplicative.toAdd (Φ b)) := by
    intro b
    have h1 := hφua (φu⁻¹ b)
    rw [MulAut.apply_inv_self] at h1
    have h2 := congrArg (TableBExc.torusAct τ p u⁻¹) h1
    rw [← TableBExc.torusAct_mul, inv_mul_cancel, TableBExc.torusAct_one] at h2
    exact h2.symm
  have hconjρ : φu * ρ i * φu⁻¹ = ρ j := by
    refine MulEquiv.ext fun b => ?_
    apply Φ.injective
    apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, MulAut.mul_apply, hφua, hρ, hφu_inv,
      ← TableBExc.torusAct_mul, ← TableBExc.torusAct_mul, hu, ← hρ j b]
  refine ⟨w₂ * φu * w₁⁻¹, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw₂ hφuA) (Subgroup.inv_mem _ hw₁)
  · rw [ha'j, hai, ← hconjρ]
    group

section Transport


theorem GGRk1ConclEx.of_fix_iff {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {r r' : MulAut ↥Bs} (hr : GGRk1ConclEx p Bs X r) (hr' : r' ∈ ggAutomizer X Bs)
    (hr'2 : r' * r' = 1) (h : ∀ b : ↥Bs, r b = b ↔ r' b = b) : GGRk1ConclEx p Bs X r' := by
  obtain ⟨F, hF, hFin, θ, hchar, hinj, hrange, -, hs, hns, hlab, hex⟩ := hr
  exact ⟨F, hF, hFin, θ, hchar, hinj, hrange.trans (ggRankOneIn_congr_fix h),
    ggExists_weylElt_of_mem_ggAutomizer hr' hr'2, hs, hns, hlab, hex⟩

theorem ggRk1ConclEx_of_isReflection_of_excPlusModel {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (hM : GGExcPlusWeylModel τ p (ggGamma X hN).range) {t : MulAut ↥Bs}
    (ht : t ∈ ggAutomizer X Bs) (htR : GGIsReflection p t) (hcon : GGRk1ConclEx p Bs X t)
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs) (hrR : GGIsReflection p r) :
    GGRk1ConclEx p Bs X r := by
  classical
  have hsc : GGTorusSelfCent p (ggGamma X hN).range := ggTorusSelfCent_ggGamma hN hSC
  have hW := (ggWTEx1_weylFrame_of_excPlusModel hp hp2 hsc hM).automizer_le_closure
  obtain ⟨n₀, hn₀, hov₀, hR₀, hA₀⟩ :=
    ggReflection_overGamma_of_induced hp hp2 hBs hN (mem_ggAutomizer_iff.mp ht) htR
  obtain ⟨n₁, hn₁, hov₁, hR₁, hA₁⟩ :=
    ggReflection_overGamma_of_induced hp hp2 hBs hN (mem_ggAutomizer_iff.mp hr) hrR
  obtain ⟨v, hv, hva⟩ := ggExcPlusModel_exists_conj_of_isReflection hτ hp hp2 hsc hM hA₀ hR₀ hA₁ hR₁
  obtain ⟨c, hc, hovc⟩ := exists_overGamma_of_weylReflSet hp hp2 hBs hSC hN hW v hv
  have hcA : c ∈ ggAutomizer X Bs := (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1) hc
  have hctA : c * t * c⁻¹ ∈ ggAutomizer X Bs :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hcA ht) (Subgroup.inv_mem _ hcA)
  have hov : GGOverGamma hN (c * t * c⁻¹) (ggConjAut (ggGamma X hN).range hn₁) := by
    rw [hva]
    exact (hovc.mul hov₀).mul hovc.inv
  have ht2 : t * t = 1 := by simpa [pow_two] using htR.1
  have hct2 : c * t * c⁻¹ * (c * t * c⁻¹) = 1 := by
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
  have hr2 : r * r = 1 := by simpa [pow_two] using hrR.1
  refine (ggRk1ConclEx_conj hcon hcA).of_fix_iff hr hr2 fun b => ⟨fun hb => ?_, fun hb => ?_⟩
  · exact ggFix_of_overGamma_of_involution hp hp2 hBs hr hr2 hov hov₁ hb
  · exact ggFix_of_overGamma_of_involution hp hp2 hBs hctA hct2 hov₁ hov hb

end Transport

section Rows


theorem largeEvenLabelAll_excPlusModel_EE7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : ggRowP_EE7 p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGExcPlusWeylModel .E7 p A := by
  obtain ⟨htag, hpn⟩ := h
  refine (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_excPlus hp hp2 ⟨Or.inl htag, hpn⟩)
    (ggNEE_largeEvenLabelAll_model_excPlus hp hp2 (Or.inl htag) hpn)).mono fun R _ I _ h => ?_
  refine ⟨_, h.1, fun L' _ _ ψ A hA => ?_⟩
  have hm := h.2 L' ψ A hA
  rw [htag] at hm
  exact hm

theorem largeEvenLabelAll_excPlusModel_ETwE6 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : ggRowP_ETwE6 p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGExcPlusWeylModel .E6 p A := by
  obtain ⟨htag, hpn⟩ := h
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hW : LargeEvenLabelAll lab fun R _ I _ => GGExcPlusWeylModelSCr .E6 p 5 R I :=
    TwE6Delta.labelAll htag fun K _ _ hK => by
      haveI : CharP K 2 := charP_two_of_card (K := K) (m := 2 * lab.n)
        (by rw [hK, ← pow_mul, mul_comm])
      obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hlab.1 hK (iterateFrobenius K 2 lab.n)
        (fun c => iterateFrobenius_def 2 lab.n c)
      exact ggExcPlusWeylModelSCr_of_frameModelOn hp (TwE6Delta.center_recipeR_eq_bot hlab.1 hK)
        (fun φ hφ hφp => TwE6Delta.ggOutdiagPrime_twE6 hlab.1 hK hp hp3 φ hφ hφp)
        (TwE6Delta.ggCenterPrime_twE6 hlab.1 hK hp hp2 hp3)
        ((excPlusFrameModelOn_twE6Plus hp hp5 hlab.1 hpn K hK (iterateFrobenius K 2 lab.n)
          (fun c => iterateFrobenius_def 2 lab.n c)).of_mulEquiv e)
  refine (largeEvenLabelAll_and
    (largeEvenLabelAll_torusLift_twE6Add_holds hp hlab ⟨htag, hpn⟩) hW).mono
    fun _ _ _ _ ⟨hl, hw⟩ => ⟨5, ?_, fun L' _ _ ψ A hA => hw L' ψ A hA⟩
  rwa [TwE6Delta.liftRank_of_ne hp3] at hl

theorem ggRk1ConclEx_of_isReflection_excRow (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ ∃ y, GGNbr p B x D J y X)
    (hrow : GGInnerDiagOnLabel (fun p lab => ggRowP_EE7 p lab ∨ (ggRowP_ETwE6 p lab ∧ 5 ≤ p)) p Bs X)
    {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs) (htR : GGIsReflection p t)
    (hcon : GGRk1ConclEx p Bs X t) {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer X Bs)
    (hrR : GGIsReflection p r) : GGRk1ConclEx p Bs X r := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 y X hnb
  obtain ⟨-, hBs, -, -, -⟩ := hcfg.1.1.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.1.1.2.1.2.2.2
  obtain ⟨lab, hΛ, hhas, R, _, I, _, θ, hS, -⟩ := largeEvenMarking_exists_hasLabel hrow
  rcases hS with hE7 | ⟨hTw, hp5⟩
  · obtain ⟨hN, hM, -⟩ := ggX_exists_overGamma_lift hRig hcfg hX hInn hΛ hhas
      (fun _ _ A => GGExcPlusWeylModel .E7 p A) (largeEvenLabelAll_excPlusModel_EE7 hp hp2 hE7)
    exact ggRk1ConclEx_of_isReflection_of_excPlusModel hp hp2 hBs hSC hN (Or.inr (Or.inl rfl)) hM
      ht htR hcon hr hrR
  · obtain ⟨hN, hM, -⟩ := ggX_exists_overGamma_lift hRig hcfg hX hInn hΛ hhas
      (fun _ _ A => GGExcPlusWeylModel .E6 p A) (largeEvenLabelAll_excPlusModel_ETwE6 hp hp5 hΛ hTw)
    exact ggRk1ConclEx_of_isReflection_of_excPlusModel hp hp2 hBs hSC hN (Or.inl rfl) hM
      ht htR hcon hr hrR

end Rows

end CFSG.StandardType

end
