module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpLocal
public import CFSG.RankThree.PartOne.AUTSL.TraceAS
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveLocalIso
import CFSG.OddTranspositions.PartThree.Twelve.FourSp
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpArith
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelChart
import CFSG.OddTranspositions.PartThree.Twelve.ElevenSpModelOrder
import CFSG.RankThree.GF2n.Stroth80.Sec310ClQuad
import CFSG.ClassicalGroups.Symplectic.PointRadicalNormal
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.OddTranspositions.PartThree.Twelve.NineSp
import CFSG.ClassicalGroups.Alternating.TransvectionGeneration
import CFSG.RankThree.PartOne.S11d.OddAlt

public section

namespace CFSG.OddTranspositions.PartThree.ElevenSp

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
open CFSG.OddTranspositions.QZ CFSG.GroupTheory.WeirSylow
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.AUTSL

variable {G : Type} [Group G] [Finite G] {D : Set G} {hC : HypothesisC D} {B : SpBranch hC}
  {k : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

private lemma mem_span_setOf_eq_one_of_quadraticForm_ne_zero {K V : Type} [Field K] [Fintype K]
    [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {W : Submodule K V}
    {y : V} (hyW : y ∈ W) (hy0 : Q y ≠ 0) :
    y ∈ Submodule.span K {x : V | x ∈ W ∧ Q x = 1} := by
  classical
  have : Finite K := Finite.of_fintype K
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q y)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hy0 hs
  have hQinv : Q (s⁻¹ • y) = 1 := by
    rw [QuadraticMap.map_smul Q s⁻¹ y, hs, smul_eq_mul]
    calc s⁻¹ * s⁻¹ * (s * s) = (s⁻¹ * s) * (s⁻¹ * s) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hs0, one_mul]
  have hy : y = s • (s⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
  rw [hy]
  exact Submodule.smul_mem _ s
    (Submodule.subset_span ⟨Submodule.smul_mem _ s⁻¹ hyW, hQinv⟩)

private lemma mem_span_setOf_eq_one_of_quadraticForm_eq_zero {K V : Type} [Field K] [Fintype K]
    [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {W : Submodule K V}
    (hK : 2 < Fintype.card K) {x : V} (hxW : x ∈ W) (hx0 : Q x = 0)
    {a : V} (haW : a ∈ W) (haQ : Q a ≠ 0) :
    x ∈ Submodule.span K {y : V | y ∈ W ∧ Q y = 1} := by
  classical
  have hlt : ({0, polar Q x a / Q a} : Finset K).card <
      (Finset.univ : Finset K).card := by
    rw [Finset.card_univ]
    have hle : ({0, polar Q x a / Q a} : Finset K).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    exact lt_of_le_of_lt hle hK
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have ht0 : t ≠ 0 := by
    intro h
    exact ht (by simp [h])
  have htne : t ≠ polar Q x a / Q a := by
    intro h
    exact ht (by simp [h])
  have hQxa : Q (x + t • a) ≠ 0 := by
    rw [QuadraticMap.map_add Q x (t • a), hx0, zero_add,
      QuadraticMap.map_smul Q t a, QuadraticMap.polar_smul_right Q t x a]
    intro h
    have h1 : t * (t * Q a + polar Q x a) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h1 with ht' | h2
    · exact ht0 ht'
    · apply htne
      rw [eq_div_iff haQ]
      have h3 : t * Q a = -polar Q x a := eq_neg_of_add_eq_zero_left h2
      rwa [CharTwo.neg_eq] at h3
  have hxa : x + t • a ∈ Submodule.span K {y : V | y ∈ W ∧ Q y = 1} :=
    mem_span_setOf_eq_one_of_quadraticForm_ne_zero
      (Submodule.add_mem _ hxW (Submodule.smul_mem _ t haW)) hQxa
  have hta : t • a ∈ Submodule.span K {y : V | y ∈ W ∧ Q y = 1} :=
    Submodule.smul_mem _ t (mem_span_setOf_eq_one_of_quadraticForm_ne_zero haW haQ)
  have hsub : x = (x + t • a) - t • a := by abel
  rw [hsub]
  exact Submodule.sub_mem _ hxa hta

private theorem span_setOf_eq_one_of_exists_ne_zero {K V : Type} [Field K] [Fintype K]
    [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {W : Submodule K V}
    (hK : 2 < Fintype.card K) (hQ : ∃ a ∈ W, Q a ≠ 0) :
    Submodule.span K {x : V | x ∈ W ∧ Q x = 1} = W := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
  · rintro x ⟨hx, -⟩
    exact hx
  · by_cases hx0 : Q x = 0
    · obtain ⟨a, haW, haQ⟩ := hQ
      exact mem_span_setOf_eq_one_of_quadraticForm_eq_zero hK hx hx0 haW haQ
    · exact mem_span_setOf_eq_one_of_quadraticForm_ne_zero hx hx0

omit [Finite G] [Fintype F] [DecidableEq F] [CharP F 2] in
private lemma fixedSpace_key {hα : hC.alpha = {hC.d}} {c : SpChart hC hα k F}
    {v x : G} (hv : v ∈ commSet D hC.d)
    {Q : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQline : ∀ z, z ∈ commSet D hC.d → (z ∈ commSet D x ↔ Q (c.vec z) = 1))
    {a₀ : Fin k ⊕ Fin k → F} (ha₀ : a₀ = c.vec v)
    {K : Submodule F (Fin k ⊕ Fin k → F)} (hK : ∀ y, y ∈ K ↔ spForm k F a₀ y = 0)
    (hsymm : ∀ y, spForm k F y a₀ = spForm k F a₀ y)
    {b : Fin k ⊕ Fin k → F}
    (hb : ∀ r : ↥(Halpha D hC.alpha), (r : G) ∈ hypLineGroup D hC.d v →
      Commute (r : G) x → spEnd (c.ρ r) b = b)
    {y : Fin k ⊕ Fin k → F} (hyK : y ∈ K) (hyQ : Q y = 1) (hya : y ≠ a₀) :
    spForm k F b y = 0 := by
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hyQ
    exact zero_ne_one hyQ
  obtain ⟨z, hzD, hzy⟩ := c.exists_vec y hy0
  have hzv : z ∈ commSet D v := by
    refine ⟨hzD.1, ?_, ?_⟩
    · rw [c.commute_iff z hzD v hv, hzy, ← ha₀]
      rw [hsymm y]
      exact (hK y).mp hyK
    · intro hzv
      apply hya
      rw [← hzy, hzv, ← ha₀]
  have hzH : z ∈ Halpha D hC.alpha := mem_Halpha_of_mem_commSet hC hα hzD
  have hzx : z ∈ commSet D x := (hQline z hzD).mpr (by rw [hzy]; exact hyQ)
  have hzline : z ∈ hypLineGroup D hC.d v :=
    Subgroup.subset_closure ⟨hzD, hzv⟩
  have hr := hb ⟨z, hzH⟩ hzline hzx.2.1
  have hmap : c.ρ ⟨z, hzH⟩ = spTransvection y 1 := by
    rw [c.map_eq z hzD, hzy]
  rw [hmap, spEnd_spTransvection] at hr
  simp only [one_mul] at hr
  rw [add_eq_left, smul_eq_zero] at hr
  exact hr.resolve_right hy0

omit [Finite G] [Fintype F] [DecidableEq F] in
private lemma fixedSpace_exists_one {hα : hC.alpha = {hC.d}} {c : SpChart hC hα k F}
    (hk : 2 ≤ k) {v : G} (hv : v ∈ commSet D hC.d)
    {Q : QuadraticForm F (Fin k ⊕ Fin k → F)} {a₀ : Fin k ⊕ Fin k → F}
    (ha₀ : a₀ = c.vec v) {K : Submodule F (Fin k ⊕ Fin k → F)}
    (hK : K = LinearMap.ker (spForm k F a₀))
    (hSP : Submodule.span F {y : Fin k ⊕ Fin k → F | y ∈ K ∧ Q y = 1} = K) :
    ∃ p, p ∈ K ∧ Q p = 1 ∧ p ≠ a₀ := by
  have ha₀ne : a₀ ≠ 0 := by
    rw [ha₀]
    exact c.vec_ne_zero v hv
  by_contra h
  push Not at h
  have hle : Submodule.span F {x : Fin k ⊕ Fin k → F | x ∈ K ∧ Q x = 1} ≤
      Submodule.span F {a₀} := by
    refine Submodule.span_le.mpr ?_
    rintro p ⟨hpK, hpQ⟩
    rw [h p hpK hpQ]
    exact Submodule.mem_span_singleton_self a₀
  rw [hSP] at hle
  obtain ⟨y, hy0, hyne⟩ :=
    CFSG.OddTranspositions.PartThree.exists_spForm_eq_zero_forall_ne_smul
      (k := k) (F := F) hk ha₀ne
  have hyK : y ∈ K := by
    rw [hK]
    rwa [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt] at hy0
  have hya : y ∉ Submodule.span F {a₀} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact hyne c hc.symm
  exact hya (hle hyK)

omit [Finite G] [Fintype F] [DecidableEq F] in
private lemma quadraticForm_add_smul_eq_one {V : Type} [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {K : Submodule F V} {p a₀ : V} (hpK : p ∈ K) (ha₀K : a₀ ∈ K)
    (hpQ : Q p = 1) (hQa₀ : Q a₀ = 1) (hBpa : polar Q p a₀ = 0) (lam : F) :
    lam • p + (1 + lam) • a₀ ∈ K ∧ Q (lam • p + (1 + lam) • a₀) = 1 := by
  refine ⟨Submodule.add_mem _ (Submodule.smul_mem _ lam hpK)
    (Submodule.smul_mem _ (1 + lam) ha₀K), ?_⟩
  rw [QuadraticMap.map_add Q (lam • p) ((1 + lam) • a₀),
    QuadraticMap.map_smul, QuadraticMap.map_smul,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpQ, hQa₀, hBpa,
    smul_eq_mul, smul_eq_mul]
  rw [smul_zero, smul_zero, add_zero, mul_one, mul_one]
  have hsq : (1 + lam) * (1 + lam) = 1 + lam * lam := by
    rw [← pow_two, CharTwo.add_sq, pow_two, pow_two, one_mul]
  rw [hsq, add_comm (lam * lam) (1 + lam * lam), add_assoc,
    CharTwo.add_self_eq_zero (lam * lam), add_zero]

omit [Finite G] [Fintype F] [DecidableEq F] in
private lemma add_smul_ne_of_ne_of_ne_zero {V : Type} [AddCommGroup V] [Module F V]
    {p a₀ : V} (hpa : p ≠ a₀) {lam : F} (hlam0 : lam ≠ 0) :
    lam • p + (1 + lam) • a₀ ≠ a₀ := by
  intro h
  apply hpa
  have hcc : (1 + lam) • a₀ + (1 + lam) • a₀ = 0 := by
    rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
  have h4 : lam • p = lam • a₀ := by
    have h3 : lam • p = a₀ + (1 + lam) • a₀ := by
      have h' := congrArg (fun X => X + (1 + lam) • a₀) h
      rw [add_assoc, hcc, add_zero] at h'
      exact h'
    rw [h3]
    calc a₀ + (1 + lam) • a₀ = (1 : F) • a₀ + (1 + lam) • a₀ := by rw [one_smul]
      _ = (1 + (1 + lam)) • a₀ := (add_smul _ _ _).symm
      _ = lam • a₀ := by
          rw [show 1 + (1 + lam) = lam by
            rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]]
  have h5 : lam • (p - a₀) = 0 := by rw [smul_sub, h4, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_left hlam0)

omit [Finite G] [DecidableEq F] in
private lemma fixedSpace_orthogonal_a₀ {hα : hC.alpha = {hC.d}} {c : SpChart hC hα k F}
    (hF : 2 < Fintype.card F) {x : G} {Q : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ : IsFormOfLine c Q x)
    {a₀ : Fin k ⊕ Fin k → F}
    {K : Submodule F (Fin k ⊕ Fin k → F)} (hK : K = LinearMap.ker (spForm k F a₀))
    (ha₀K : a₀ ∈ K) (hQa₀ : Q a₀ = 1)
    {b : Fin k ⊕ Fin k → F}
    (key : ∀ y ∈ K, Q y = 1 → y ≠ a₀ → spForm k F b y = 0)
    (hsymm : ∀ y, spForm k F y a₀ = spForm k F a₀ y)
    (p : Fin k ⊕ Fin k → F) (hpK : p ∈ K) (hpQ : Q p = 1) (hpa : p ≠ a₀) :
    spForm k F b a₀ = 0 := by
  classical
  obtain ⟨hQpol, -⟩ := hQ
  have hpker : p ∈ LinearMap.ker (spForm k F a₀) := by rwa [hK] at hpK
  obtain ⟨lam, hlam0, hlam1⟩ :=
    CFSG.ClassicalGroups.Alternating.exists_ne_zero_ne_one_of_two_lt_card
      (K := F) (by rw [Nat.card_eq_fintype_card]; exact hF)
  have hBpa : polar Q p a₀ = 0 := by
    rw [hQpol p a₀]
    rw [hsymm p]
    exact LinearMap.mem_ker.mp hpker
  have h1lam : 1 + lam ≠ 0 := by
    intro h
    apply hlam1
    have h' : lam = -1 := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at h'
  obtain ⟨hwK, hwQ⟩ := quadraticForm_add_smul_eq_one hpK ha₀K hpQ hQa₀ hBpa lam
  have hwa := add_smul_ne_of_ne_of_ne_zero hpa hlam0
  have hkeyw : spForm k F b (lam • p + (1 + lam) • a₀) = 0 := key _ hwK hwQ hwa
  have hkeyp : spForm k F b p = 0 := key p hpK hpQ hpa
  have hlin : spForm k F b (lam • p + (1 + lam) • a₀) =
      lam * spForm k F b p + (1 + lam) * spForm k F b a₀ := by
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [hlin, hkeyp, mul_zero, zero_add] at hkeyw
  exact (mul_eq_zero.mp hkeyw).resolve_left h1lam

omit [Finite G] [Fintype F] [CharP F 2] in
private lemma forall_spForm_eq_zero_of_span_setOf_eq_one {K : Submodule F (Fin k ⊕ Fin k → F)}
    {Q : QuadraticForm F (Fin k ⊕ Fin k → F)} {b a₀ : Fin k ⊕ Fin k → F}
    (hSP : Submodule.span F {z : Fin k ⊕ Fin k → F | z ∈ K ∧ Q z = 1} = K)
    (key : ∀ y ∈ K, Q y = 1 → y ≠ a₀ → spForm k F b y = 0)
    (hba : spForm k F b a₀ = 0) :
    ∀ y ∈ K, spForm k F b y = 0 := by
  intro y hyK
  have hy : y ∈ Submodule.span F {z : Fin k ⊕ Fin k → F | z ∈ K ∧ Q z = 1} := by
    rw [hSP]
    exact hyK
  refine Submodule.span_induction (p := fun z _ => spForm k F b z = 0) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨hzK, hzQ⟩
    by_cases hza : z = a₀
    · rw [hza]
      exact hba
    · exact key z hzK hzQ hza
  · exact map_zero _
  · intro u w _ _ hu hw
    rw [map_add, hu, hw, add_zero]
  · intro t u _ hu
    rw [map_smul, hu, smul_eq_mul, mul_zero]

omit [Finite G] in
private lemma fixedSpace_mem_span {hα : hC.alpha = {hC.d}} {c : SpChart hC hα k F}
    (hk : 2 ≤ k) (hF : 2 < Fintype.card F) {v x : G} (hv : v ∈ commSet D hC.d)
    (hx : x ∈ commSet D v) {Q : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ : IsFormOfLine c Q x) {b : Fin k ⊕ Fin k → F}
    (hb : ∀ r : ↥(Halpha D hC.alpha), (r : G) ∈ hypLineGroup D hC.d v →
      Commute (r : G) x → spEnd (c.ρ r) b = b) :
    b ∈ Submodule.span F {c.vec v} := by
  classical
  have hQline := hQ.2
  set a₀ : Fin k ⊕ Fin k → F := c.vec v with ha₀
  set K : Submodule F (Fin k ⊕ Fin k → F) := LinearMap.ker (spForm k F a₀) with hK
  have ha₀K : a₀ ∈ K := by
    rw [hK]
    exact LinearMap.mem_ker.mpr (spForm_isAlt.self_eq_zero a₀)
  have hQa₀ : Q a₀ = 1 := by
    have hvx : v ∈ commSet D x := ⟨hv.1, hx.2.1.symm, hx.2.2.symm⟩
    have h := (hQline v hv).mp hvx
    simpa [ha₀] using h
  have hsymm : ∀ y : Fin k ⊕ Fin k → F, spForm k F y a₀ = spForm k F a₀ y := fun y =>
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt y a₀
  have hSP : Submodule.span F {y : Fin k ⊕ Fin k → F | y ∈ K ∧ Q y = 1} = K :=
    span_setOf_eq_one_of_exists_ne_zero (Q := Q) (W := K) hF
      ⟨a₀, ha₀K, by rw [hQa₀]; exact one_ne_zero⟩
  have hKmem : ∀ y : Fin k ⊕ Fin k → F, y ∈ K ↔ spForm k F a₀ y = 0 := by
    intro y
    rw [hK]
    exact LinearMap.mem_ker
  have key : ∀ y ∈ K, Q y = 1 → y ≠ a₀ → spForm k F b y = 0 :=
    fun y hyK hyQ hya => fixedSpace_key hv hQline ha₀ hKmem hsymm hb hyK hyQ hya
  obtain ⟨p, hpK, hpQ, hpa⟩ := fixedSpace_exists_one hk hv ha₀ hK hSP
  have hba : spForm k F b a₀ = 0 :=
    fixedSpace_orthogonal_a₀ hF hQ hK ha₀K hQa₀ key hsymm p hpK hpQ hpa
  have hbK : ∀ y ∈ K, spForm k F b y = 0 :=
    forall_spForm_eq_zero_of_span_setOf_eq_one hSP key hba
  have hspan : b ∈ Submodule.span F {a₀} := by
    have h := CFSG.ClassicalGroups.Alternating.mem_span_of_forall_orthogonal
      (B := spForm k F) spForm_nondegenerate
      (fun _ : Unit => a₀) b (fun y hy => hbK y (hy ()))
    simpa using h
  exact hspan

omit [Finite G] in
theorem fixedSpace_hypLineGroup_inf_centralizer {hα : hC.alpha = {hC.d}} (c : SpChart hC hα k F)
    (hk : 2 ≤ k) (hF : 2 < Fintype.card F) {v x : G} (hv : v ∈ commSet D hC.d)
    (hx : x ∈ commSet D v) {Q : QuadraticForm F (Fin k ⊕ Fin k → F)} (hQ : IsFormOfLine c Q x) :
    {a | ∀ r : ↥(Halpha D hC.alpha), (r : G) ∈ hypLineGroup D hC.d v → Commute (r : G) x →
        spEnd (c.ρ r) a = a} = (Submodule.span F {c.vec v} : Set (Fin k ⊕ Fin k → F)) := by
  classical
  ext b
  constructor
  · intro hb
    exact fixedSpace_mem_span hk hF hv hx hQ hb
  · intro hb r hr hcomm
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_smul]
    have hcommv : Commute (r : G) v :=
      OddLocal.commute_of_mem_closure_commSet
        (Subgroup.closure_mono Set.inter_subset_right hr)
    have hconjv : (r : G) * v * (r : G)⁻¹ = v := by
      rw [hcommv.eq, mul_assoc, mul_inv_cancel, mul_one]
    have h1 := (SpChart.vec_conj c r hv).2
    rw [hconjv] at h1
    rw [← h1]

omit [DecidableEq F] in
theorem exists_eq_add_sq_spForm_of_fixed {S : Set ↥(StatedSp k F)} {y : Fin k ⊕ Fin k → F}
    (hS : ∀ a, (∀ g ∈ S, spEnd g a = a) → a ∈ Submodule.span F {y})
    {Q Q' : QuadraticForm F (Fin k ⊕ Fin k → F)} (hQ : ∀ a b, polar Q a b = spForm k F a b)
    (hQ' : ∀ a b, polar Q' a b = spForm k F a b) (hSQ : ∀ g ∈ S, ∀ a, Q (spEnd g a) = Q a)
    (hSQ' : ∀ g ∈ S, ∀ a, Q' (spEnd g a) = Q' a) :
    ∃ c : F, ∀ a, Q' a = Q a + (c * spForm k F y a) ^ 2 := by
  have hQb : Q.polarBilin = spForm k F := by
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hQ a b
  have hQ'b : Q'.polarBilin = spForm k F := by
    refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hQ' a b
  obtain ⟨u, hu⟩ := CFSG.RankThree.GF2n.Stroth80.Classify.quadForm_sub_eq_sq
    (F := spForm k F) spForm_nondegenerate Q Q' hQb hQ'b
  have hfix : ∀ g ∈ S, spEnd g u = u := by
    intro g hg
    have hinv : spEnd g⁻¹ u = u := by
      have hzero : spEnd g⁻¹ u - u = 0 := by
        apply spForm_nondegenerate.2
        intro a
        have h1 : spForm k F a (spEnd g⁻¹ u) = spForm k F a u := by
          have h2 : spForm k F (spEnd g a) u = spForm k F a u := by
            have h3 : (spForm k F (spEnd g a) u) ^ 2 = (spForm k F a u) ^ 2 := by
              have e1 := hu (spEnd g a)
              rw [hSQ' g hg a, hSQ g hg a, hu a] at e1
              exact (add_left_cancel e1).symm
            exact CharTwo.sq_injective h3
          calc spForm k F a (spEnd g⁻¹ u)
              = spForm k F (spEnd g a) (spEnd g (spEnd g⁻¹ u)) :=
                (spForm_spEnd_spEnd g a (spEnd g⁻¹ u)).symm
            _ = spForm k F (spEnd g a) u := by rw [spEnd_spEnd_inv_apply]
            _ = spForm k F a u := h2
        rw [map_sub, h1, sub_self]
      exact sub_eq_zero.mp hzero
    calc spEnd g u = spEnd g (spEnd g⁻¹ u) := by rw [hinv]
      _ = u := spEnd_spEnd_inv_apply g u
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hS u hfix)
  have hsymm : ∀ a, spForm k F a y = spForm k F y a := fun a =>
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt a y
  refine ⟨c, fun a => ?_⟩
  rw [hu a, ← hc, map_smul, smul_eq_mul, hsymm a]

private structure PencilData {G : Type} [Group G] [Finite G] {D : Set G} (hC : HypothesisC D)
    (B : SpBranch hC) (k : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] where
  c : SpChart hC B.hα k F
  hnk : B.n = 2 * k
  hF : Nat.card F = 2 ^ B.f
  Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)
  hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b
  hu : hC.d ∈ Halpha D hC.alpha
  θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})
  hθ : IsBasePointIdentification (hα := B.hα) c hu θ
  g : G
  hv : (hC.conj g).d ∈ commSet D hC.d
  hQ₀ty : ∃ w₀ : G, w₀ ∈ D ∧ (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1 ∧
    IsFormOfLine c Q₀ w₀
  σ : F ≃+* F
  A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)
  γ : MSpace k F ≃ₗ[F] MSpace k F
  y' : Fin k ⊕ Fin k → F
  ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
    ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})
  hA : Function.Bijective A
  hAadd : ∀ x z, A (x + z) = A x + A z
  hAsmul : ∀ (t : F) x, A (t • x) = σ t • A x
  hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z)
  hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X
  hγU : γ mU = mLift Q₀ (c.vec (hC.conj g).d)
  hy' : y' ≠ 0
  hγy' : γ (mLift Q₀ y') = mU
  hAy : A ((SpChart.conj (B := B) c g).vec hC.d) = y'
  hψθ : ∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
    (ψ₁ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀)
  hψz : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
    (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
      mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))


private noncomputable abbrev pencilCv (P : PencilData hC B k F) :
    SpChart (hC.conj P.g) (B.conj P.g).hα k F :=
  SpChart.conj (B := B) P.c P.g

private noncomputable abbrev pencilVec (P : PencilData hC B k F) (x : G) : MSpace k F :=
  P.γ (mLift P.Q₀ (P.A ((pencilCv P).vec x)))

private noncomputable abbrev pencilForm (P : PencilData hC B k F) (x : G) :
    QuadraticForm F (Fin k ⊕ Fin k → F) :=
  mStabForm P.Q₀ (pencilVec P x)

omit [Fintype F] [DecidableEq F] in
omit [Finite G] in
private lemma mem_commSet_conj_iff_of_commute (hC : HypothesisC D) {r z x : G}
    (hrx : Commute r x) :
    r * z * r⁻¹ ∈ commSet D x ↔ z ∈ commSet D x := by
  constructor
  · intro h
    have h1 := conj_mem_commSet_of_commute hC.setup.normal hrx.inv_left h
    simpa [mul_assoc] using h1
  · intro h
    exact conj_mem_commSet_of_commute hC.setup.normal hrx h

private noncomputable def PencilData.lineForm (P : PencilData hC B k F) (x : G)
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    QuadraticForm F (Fin k ⊕ Fin k → F) :=
  (exists_quadraticForm_commSet_inter B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp P.c P.hnk P.hF
    P.hv hx.1 hxd hx.2.1).choose

private theorem lineForm_isFormOfLine (P : PencilData hC B k F) (x : G)
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    IsFormOfLine P.c (P.lineForm x hx hxd) x := by
  have h := (exists_quadraticForm_commSet_inter B.hIH hC B.hMZ B.hα B.hs B.hn B.hf B.hSp P.c
    P.hnk P.hF P.hv hx.1 hxd hx.2.1).choose_spec
  exact ⟨h.1, h.2.1⟩

private lemma spForm_vec_conj_ne_zero (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x) ≠ 0 := by
  intro h0
  have h1 : Commute x hC.d ↔
      spForm k F ((pencilCv P).vec x) ((pencilCv P).vec hC.d) = 0 :=
    (pencilCv P).commute_iff x hx hC.d (mem_commSet_symm hC.hd P.hv)
  refine hxd (h1.mpr ?_)
  have hsymm : spForm k F ((pencilCv P).vec x) ((pencilCv P).vec hC.d) =
      spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x) :=
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt _ _
  rw [hsymm]
  exact h0

private lemma snd_pencilVec (P : PencilData hC B k F) {x : G} :
    (pencilVec P x).1.2 =
      P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x)) := by
  calc (pencilVec P x).1.2
      = polar (mForm P.Q₀) mU (pencilVec P x) := (polar_mU_eq_snd _).symm
    _ = polar (mForm P.Q₀) (P.γ (mLift P.Q₀ P.y'))
          (P.γ (mLift P.Q₀ (P.A ((pencilCv P).vec x)))) := by rw [← P.hγy']
    _ = polar (mForm P.Q₀) (mLift P.Q₀ P.y')
          (mLift P.Q₀ (P.A ((pencilCv P).vec x))) :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr P.hγ) _ _
    _ = spForm k F P.y' (P.A ((pencilCv P).vec x)) := by
        rw [polar_mForm P.hQ₀]
        simp [mLift]
    _ = P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x)) := by
        rw [← P.hAy, P.hAform]

private lemma snd_pencilVec_ne_zero (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    (pencilVec P x).1.2 ≠ 0 := by
  rw [snd_pencilVec P]
  intro h
  exact spForm_vec_conj_ne_zero P hx hxd (P.σ.injective (by simpa using h))

private lemma stabForm_vec_conj_eq_one (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    pencilForm P x (P.c.vec (hC.conj P.g).d) = 1 := by
  have hY : mForm P.Q₀ (pencilVec P x) = 1 := by
    rw [pencilVec, P.hγ, mForm_mLift]
  have h1 : Commute (mRefl P.Q₀ (mLift P.Q₀ (P.c.vec (hC.conj P.g).d)))
      (mRefl P.Q₀ (pencilVec P x)) := by
    have h2 := (P.ψ₁ ⟨x, mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx⟩).2
    rw [Subgroup.mem_centralizer_singleton_iff] at h2
    rw [P.hψz x hx] at h2
    exact h2.symm
  exact (commute_mLift_iff P.hQ₀ hY (snd_pencilVec_ne_zero P hx hxd)
    (P.c.vec (hC.conj P.g).d)).mp h1

private lemma stabForm_spEnd_eq (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d)
    (r : ↥(Halpha D hC.alpha)) (hr : (r : G) ∈ hypLineGroup D hC.d (hC.conj P.g).d)
    (hrx : Commute (r : G) x) :
    ∀ a, pencilForm P x (spEnd (P.c.ρ r) a) = pencilForm P x a := by
  intro a
  have hcent : (r : G) ∈ Subgroup.centralizer {(hC.conj P.g).d} :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (OddLocal.commute_of_mem_closure_commSet
        (Subgroup.closure_mono Set.inter_subset_right hr))
  have hrHv : (r : G) ∈ Halpha D (hC.conj P.g).alpha :=
    inf_centralizer_le_Halpha_conj (B := B) P.c P.g P.hv ⟨r.2, hcent⟩
  have hψr : (P.ψ₁ ⟨r, hrHv⟩ : MGroup P.Q₀) = (P.θ r : MGroup P.Q₀) := P.hψθ r hrHv
  have hθr : Commute (P.θ r : MGroup P.Q₀) (mRefl P.Q₀ (pencilVec P x)) := by
    have h2 : Commute (⟨r, hrHv⟩ : ↥(Halpha D (hC.conj P.g).alpha))
        ⟨x, mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx⟩ :=
      Commute.of_map (Subgroup.subtype_injective _) hrx
    have h3 : Commute ((P.ψ₁ ⟨r, hrHv⟩ : MGroup P.Q₀))
        ((P.ψ₁ ⟨x, mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx⟩ :
          MGroup P.Q₀)) :=
      (h2.map P.ψ₁.toMonoidHom).map (Subgroup.subtype _)
    rw [P.hψθ r hrHv, P.hψz x hx] at h3
    exact h3
  have hY : mForm P.Q₀ (pencilVec P x) = 1 := by
    rw [pencilVec, P.hγ, mForm_mLift]
  have hfix : ((P.θ r : MGroup P.Q₀) : MSpace k F ≃ₗ[F] MSpace k F) (pencilVec P x) =
      pencilVec P x :=
    (CFSG.ClassicalGroups.Orthogonal.commute_reflect_iff_apply_eq
      (Q := mForm P.Q₀) (nondegenerate_polarBilin_mForm P.hQ₀)
      (P.θ r) (by rw [hY]; exact one_ne_zero)).mp (by
        simpa [mRefl] using hθr)
  have key := mStabForm_apply_eq_of_mem_centralizer P.hQ₀ (Y := pencilVec P x)
    (snd_pencilVec_ne_zero P hx hxd) (P.θ r).2 a
  rw [hfix] at key
  rw [P.hθ.1 r a]
  exact key

private lemma lineForm_spEnd_eq (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d)
    (r : ↥(Halpha D hC.alpha))
    (hrx : Commute (r : G) x) :
    ∀ a, P.lineForm x hx hxd (spEnd (P.c.ρ r) a) = P.lineForm x hx hxd a := by
  have hQ := lineForm_isFormOfLine P x hx hxd
  set Q' : QuadraticForm F (Fin k ⊕ Fin k → F) :=
    (P.lineForm x hx hxd).comp (spEnd (P.c.ρ r)) with hQ'def
  have hQ' : IsFormOfLine P.c Q' x := by
    refine ⟨?_, ?_⟩
    · intro u v
      rw [hQ'def, ← QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_comp,
        LinearMap.compl₁₂_apply, QuadraticMap.polarBilin_apply_apply, hQ.1, spForm_spEnd_spEnd]
    · intro z hz
      have hz' : (r : G) * z * (r : G)⁻¹ ∈ commSet D hC.d := (SpChart.vec_conj P.c r hz).1
      have hvec : P.c.vec ((r : G) * z * (r : G)⁻¹) = spEnd (P.c.ρ r) (P.c.vec z) :=
        (SpChart.vec_conj P.c r hz).2
      rw [show Q' (P.c.vec z) = P.lineForm x hx hxd (P.c.vec ((r : G) * z * (r : G)⁻¹)) from by
        rw [hQ'def, QuadraticMap.comp_apply, hvec]]
      rw [← (hQ.2 _ hz')]
      exact (mem_commSet_conj_iff_of_commute hC hrx).symm
  have huniq : Q' = P.lineForm x hx hxd :=
    eq_of_isFormOfLine (B.two_lt_card P.hF) hQ' hQ
  intro a
  exact congrArg (fun F => F a) huniq

private theorem exists_lineParam (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    ∃ c : F, ∀ a, P.lineForm x hx hxd a =
      pencilForm P x a + (c * spForm k F (P.c.vec (hC.conj P.g).d) a) ^ 2 := by
  have hk : 2 ≤ k := B.two_le_rank P.hnk
  have hq : 2 < Fintype.card F := (B.two_lt_card P.hF).trans_eq Nat.card_eq_fintype_card
  set S : Set ↥(StatedSp k F) :=
    P.c.ρ '' {r : ↥(Halpha D hC.alpha) | (r : G) ∈ hypLineGroup D hC.d (hC.conj P.g).d ∧
      Commute (r : G) x} with hSdef
  refine exists_eq_add_sq_spForm_of_fixed (S := S) (y := P.c.vec (hC.conj P.g).d)
    (Q := pencilForm P x) (Q' := P.lineForm x hx hxd) ?_ (polar_mStabForm P.hQ₀ _)
    (lineForm_isFormOfLine P x hx hxd).1 ?_ ?_
  · intro a ha
    have hmem : a ∈ {b : Fin k ⊕ Fin k → F | ∀ r : ↥(Halpha D hC.alpha),
        (r : G) ∈ hypLineGroup D hC.d (hC.conj P.g).d → Commute (r : G) x →
          spEnd (P.c.ρ r) b = b} := fun r hr hc => ha (P.c.ρ r) ⟨r, ⟨hr, hc⟩, rfl⟩
    rw [fixedSpace_hypLineGroup_inf_centralizer P.c hk hq P.hv hx
      (lineForm_isFormOfLine P x hx hxd)] at hmem
    exact hmem
  · intro g hg a
    obtain ⟨r, hr, rfl⟩ := hg
    exact stabForm_spEnd_eq P hx hxd r hr.1 hr.2 a
  · intro g hg a
    obtain ⟨r, hr, rfl⟩ := hg
    exact lineForm_spEnd_eq P hx hxd r hr.2 a

omit [Finite G] in
private lemma mem_commSet_conj_commSet (hC : HypothesisC D) (r z y : G) :
    r * z * r⁻¹ ∈ commSet D (r * y * r⁻¹) ↔ z ∈ commSet D y := by
  rw [CFSG.OddTranspositions.commSet_conj hC.setup.normal r y,
    CFSG.OddTranspositions.mem_cimg,
    show r⁻¹ * (r * z * r⁻¹) * r = z by group]

private lemma lineForm_comp_spEnd (P : PencilData hC B k F) {x x' : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d)
    (hx' : x' ∈ commSet D (hC.conj P.g).d) (hxd' : ¬ Commute x' hC.d)
    (r : ↥(Halpha D hC.alpha)) (hxx' : (r : G) * x * (r : G)⁻¹ = x') :
    ∀ a, P.lineForm x' hx' hxd' (spEnd (P.c.ρ r) a) = P.lineForm x hx hxd a := by
  have hQ := lineForm_isFormOfLine P x' hx' hxd'
  have hQx := lineForm_isFormOfLine P x hx hxd
  set Q'' : QuadraticForm F (Fin k ⊕ Fin k → F) :=
    (P.lineForm x' hx' hxd').comp (spEnd (P.c.ρ r)) with hQ''
  have hQ'' : IsFormOfLine P.c Q'' x := by
    refine ⟨?_, ?_⟩
    · intro u v
      rw [hQ'', ← QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_comp,
        LinearMap.compl₁₂_apply, QuadraticMap.polarBilin_apply_apply, hQ.1, spForm_spEnd_spEnd]
    · intro z hz
      have hz' : (r : G) * z * (r : G)⁻¹ ∈ commSet D hC.d := (SpChart.vec_conj P.c r hz).1
      have hvec : P.c.vec ((r : G) * z * (r : G)⁻¹) = spEnd (P.c.ρ r) (P.c.vec z) :=
        (SpChart.vec_conj P.c r hz).2
      rw [show Q'' (P.c.vec z) =
        P.lineForm x' hx' hxd' (P.c.vec ((r : G) * z * (r : G)⁻¹)) from by
        rw [hQ'', QuadraticMap.comp_apply, hvec]]
      rw [← hQ.2 _ hz', ← hxx']
      exact (mem_commSet_conj_commSet hC r z x).symm
  have huniq : Q'' = P.lineForm x hx hxd :=
    eq_of_isFormOfLine (B.two_lt_card P.hF) hQ'' hQx
  intro a
  exact congrArg (fun F => F a) huniq

private noncomputable def lineParam (P : PencilData hC B k F) (x : G)
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) : F :=
  (exists_lineParam P hx hxd).choose

private theorem lineParam_spec (P : PencilData hC B k F) (x : G)
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    ∀ a, P.lineForm x hx hxd a = pencilForm P x a +
      (lineParam P x hx hxd * spForm k F (P.c.vec (hC.conj P.g).d) a) ^ 2 :=
  (exists_lineParam P hx hxd).choose_spec

private lemma exists_spForm_vec_conj_eq_one (P : PencilData hC B k F) :
    ∃ a : Fin k ⊕ Fin k → F, spForm k F (P.c.vec (hC.conj P.g).d) a = 1 := by
  have hav : P.c.vec (hC.conj P.g).d ≠ 0 := P.c.vec_ne_zero _ P.hv
  have hex : ∃ a, spForm k F (P.c.vec (hC.conj P.g).d) a ≠ 0 := by
    by_contra h
    push Not at h
    exact hav (spForm_nondegenerate.1 _ h)
  obtain ⟨a, ha⟩ := hex
  refine ⟨(spForm k F (P.c.vec (hC.conj P.g).d) a)⁻¹ • a, ?_⟩
  rw [LinearMap.map_smul, smul_eq_mul, inv_mul_cancel₀ ha]

private lemma spEnd_fixes_vec_conj (P : PencilData hC B k F) (r : ↥(Halpha D hC.alpha))
    (hr : (r : G) ∈ Subgroup.centralizer {(hC.conj P.g).d}) :
    spEnd (P.c.ρ r) (P.c.vec (hC.conj P.g).d) = P.c.vec (hC.conj P.g).d := by
  have hcomm : Commute (r : G) (hC.conj P.g).d :=
    Subgroup.mem_centralizer_singleton_iff.mp hr
  have hconj : (r : G) * (hC.conj P.g).d * (r : G)⁻¹ = (hC.conj P.g).d := by
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h1 := (SpChart.vec_conj P.c r P.hv).2
  rw [hconj] at h1
  exact h1.symm

private lemma pencilForm_conj (P : PencilData hC B k F) {x x' : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d)
    (hx' : x' ∈ commSet D (hC.conj P.g).d)
    (r : ↥(Halpha D hC.alpha)) (hr : (r : G) ∈ Subgroup.centralizer {(hC.conj P.g).d})
    (hxx' : (r : G) * x * (r : G)⁻¹ = x') :
    ∀ a, pencilForm P x' (spEnd (P.c.ρ r) a) = pencilForm P x a := by
  have hrHv : (r : G) ∈ Halpha D (hC.conj P.g).alpha :=
    inf_centralizer_le_Halpha_conj (B := B) P.c P.g P.hv ⟨r.2, hr⟩
  have hY1 : mForm P.Q₀ (pencilVec P x) = 1 := by
    rw [pencilVec, P.hγ, mForm_mLift]
  have hY1' : mForm P.Q₀ (pencilVec P x') = 1 := by
    rw [pencilVec, P.hγ, mForm_mLift]
  have hY : pencilVec P x' =
      ((P.θ r : MGroup P.Q₀) : MSpace k F ≃ₗ[F] MSpace k F) (pencilVec P x) := by
    have hsub : (⟨x', mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx'⟩ :
        ↥(Halpha D (hC.conj P.g).alpha)) =
        ⟨r, hrHv⟩ * ⟨x, mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx⟩ *
          ⟨r, hrHv⟩⁻¹ := by
      refine Subtype.ext ?_
      show x' = (r : G) * x * (r : G)⁻¹
      rw [hxx']
    have h1 : P.ψ₁ ⟨x', mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx'⟩ =
        P.ψ₁ ⟨r, hrHv⟩ *
          P.ψ₁ ⟨x, mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx⟩ *
          (P.ψ₁ ⟨r, hrHv⟩)⁻¹ := by
      rw [hsub, map_mul, map_mul, map_inv]
    have h2 : (P.ψ₁ ⟨x', mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx'⟩ :
        MGroup P.Q₀) =
        (P.θ r : MGroup P.Q₀) * mRefl P.Q₀ (pencilVec P x) * (P.θ r : MGroup P.Q₀)⁻¹ := by
      rw [h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, P.hψθ r hrHv, P.hψz x hx]
    have h3 : mRefl P.Q₀ (pencilVec P x') =
        mRefl P.Q₀ (((P.θ r : MGroup P.Q₀) : MSpace k F ≃ₗ[F] MSpace k F) (pencilVec P x)) := by
      rw [← P.hψz x' hx', h2, mRefl_mul_conj]
    have hY2 : mForm P.Q₀
        (((P.θ r : MGroup P.Q₀) : MSpace k F ≃ₗ[F] MSpace k F) (pencilVec P x)) = 1 := by
      rw [map_of_mem ((P.θ r : MGroup P.Q₀)).2, hY1]
    exact (CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflect_iff
      (nondegenerate_polarBilin_mForm P.hQ₀) hY1' hY2).mp
      (congrArg (Subtype.val : MGroup P.Q₀ → MSpace k F ≃ₗ[F] MSpace k F) h3)
  intro a
  have hβ : (pencilVec P x).1.2 ≠ 0 := snd_pencilVec_ne_zero P hx hxd
  have key := mStabForm_apply_eq_of_mem_centralizer P.hQ₀ (Y := pencilVec P x) hβ (P.θ r).2 a
  rw [← hY, ← P.hθ.1 r a] at key
  exact key

private lemma lineParam_conj (P : PencilData hC B k F) {x x' : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d)
    (hx' : x' ∈ commSet D (hC.conj P.g).d) (hxd' : ¬ Commute x' hC.d)
    (r : ↥(Halpha D hC.alpha)) (hr : (r : G) ∈ Subgroup.centralizer {(hC.conj P.g).d})
    (hxx' : (r : G) * x * (r : G)⁻¹ = x') :
    lineParam P x' hx' hxd' = lineParam P x hx hxd := by
  have hcomp := lineForm_comp_spEnd P hx hxd hx' hxd' r hxx'
  have hS := pencilForm_conj P hx hxd hx' r hr hxx'
  obtain ⟨a, ha⟩ := exists_spForm_vec_conj_eq_one P
  have hsp : spForm k F (P.c.vec (hC.conj P.g).d) (spEnd (P.c.ρ r) a) =
      spForm k F (P.c.vec (hC.conj P.g).d) a := by
    calc spForm k F (P.c.vec (hC.conj P.g).d) (spEnd (P.c.ρ r) a)
        = spForm k F (spEnd (P.c.ρ r) (P.c.vec (hC.conj P.g).d)) (spEnd (P.c.ρ r) a) := by
          rw [spEnd_fixes_vec_conj P r hr]
      _ = spForm k F (P.c.vec (hC.conj P.g).d) a := spForm_spEnd_spEnd _ _ _
  have h1 := lineParam_spec P x' hx' hxd' (spEnd (P.c.ρ r) a)
  have h2 := lineParam_spec P x hx hxd a
  rw [hS a, hsp] at h1
  have h4 : (lineParam P x' hx' hxd' * spForm k F (P.c.vec (hC.conj P.g).d) a) ^ 2 =
      (lineParam P x hx hxd * spForm k F (P.c.vec (hC.conj P.g).d) a) ^ 2 := by
    have h5 : pencilForm P x a +
        (lineParam P x' hx' hxd' * spForm k F (P.c.vec (hC.conj P.g).d) a) ^ 2 =
        pencilForm P x a +
        (lineParam P x hx hxd * spForm k F (P.c.vec (hC.conj P.g).d) a) ^ 2 :=
      (h1.symm.trans (hcomp a)).trans h2
    exact add_left_cancel h5
  simp only [ha, mul_one] at h4
  exact CharTwo.sq_injective h4

private lemma lineParam_eq_of_sigma_spForm_eq (P : PencilData hC B k F) {x x' : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d)
    (hx' : x' ∈ commSet D (hC.conj P.g).d) (hxd' : ¬ Commute x' hC.d)
    (hb : P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x)) =
      P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x'))) :
    lineParam P x' hx' hxd' = lineParam P x hx hxd := by
  obtain ⟨r, hr, hxx'⟩ :=
    exists_conj_of_spForm_eq (B := B) P.g P.hv (pencilCv P) hx hx' hxd (P.σ.injective hb)
  exact lineParam_conj P hx hxd hx' hxd' ⟨r, hr.1⟩ hr.2 hxx'

private lemma exists_spForm_vec_conj_eq (P : PencilData hC B k F) {b : F} (hb : b ≠ 0) :
    ∃ (x : G) (_hx : x ∈ commSet D (hC.conj P.g).d) (_hxd : ¬ Commute x hC.d),
      spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x) = b := by
  have hy : (pencilCv P).vec hC.d ≠ 0 :=
    (pencilCv P).vec_ne_zero hC.d (mem_commSet_symm hC.hd P.hv)
  have hex : ∃ u, spForm k F ((pencilCv P).vec hC.d) u ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (spForm_nondegenerate.1 _ h)
  obtain ⟨u₀, hu₀⟩ := hex
  have hu₀' : u₀ ≠ 0 := fun h => hu₀ (by rw [h, map_zero])
  have hu : (b / spForm k F ((pencilCv P).vec hC.d) u₀) • u₀ ≠ 0 := by
    intro h
    rcases smul_eq_zero.mp h with h1 | h1
    · exact div_ne_zero hb hu₀ h1
    · exact hu₀' h1
  obtain ⟨x, hx, hvec⟩ := (pencilCv P).exists_vec _ hu
  have hb' : spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x) = b := by
    rw [hvec, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ b hu₀]
  have hxd : ¬ Commute x hC.d := by
    intro hc
    have h1 : spForm k F ((pencilCv P).vec x) ((pencilCv P).vec hC.d) = 0 :=
      ((pencilCv P).commute_iff x hx hC.d (mem_commSet_symm hC.hd P.hv)).mp hc
    have hsymm : spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x) =
        spForm k F ((pencilCv P).vec x) ((pencilCv P).vec hC.d) :=
      CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt _ _
    rw [hsymm, h1] at hb'
    exact hb hb'.symm
  exact ⟨x, hx, hxd, hb'⟩

private noncomputable def kappa (P : PencilData hC B k F) (β : F) : F := by
  classical
  exact if h : ∃ x : {x : G // x ∈ commSet D (hC.conj P.g).d ∧ ¬ Commute x hC.d},
      P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x.1)) = β
    then lineParam P h.choose.1 h.choose.2.1 h.choose.2.2 else 0

private lemma kappa_apply (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    kappa P (P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x))) =
      lineParam P x hx hxd := by
  unfold kappa
  split
  · rename_i h
    exact (lineParam_eq_of_sigma_spForm_eq P h.choose.2.1 h.choose.2.2 hx hxd
      h.choose_spec).symm
  · rename_i h
    exact absurd ⟨⟨x, hx, hxd⟩, rfl⟩ h

private lemma orderOf_mul_eq_mRefl_mul (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) :
    orderOf (hC.d * x) =
      orderOf (mRefl P.Q₀ mU * mRefl P.Q₀ (pencilVec P x)) := by
  have hdH : hC.d ∈ Halpha D (hC.conj P.g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα (mem_commSet_symm hC.hd P.hv)
  have hxH : x ∈ Halpha D (hC.conj P.g).alpha :=
    mem_Halpha_of_mem_commSet (hC.conj P.g) (B.conj P.g).hα hx
  have hcoe : ((⟨hC.d, hdH⟩ * ⟨x, hxH⟩ : ↥(Halpha D (hC.conj P.g).alpha)) : G) = hC.d * x := by
    rw [Subgroup.coe_mul]
  have h1 : orderOf (hC.d * x) =
      orderOf (⟨hC.d, hdH⟩ * ⟨x, hxH⟩ : ↥(Halpha D (hC.conj P.g).alpha)) := by
    rw [← hcoe]
    exact Subgroup.orderOf_coe _
  have h5 : (P.ψ₁ ⟨x, hxH⟩ : MGroup P.Q₀) = mRefl P.Q₀ (pencilVec P x) := P.hψz x hx
  have h4 : (P.ψ₁ ⟨hC.d, hdH⟩ : MGroup P.Q₀) = mRefl P.Q₀ mU := by
    have h := P.hψz hC.d (mem_commSet_symm hC.hd P.hv)
    rw [P.hAy, P.hγy'] at h
    exact h
  have h2 : (P.ψ₁ (⟨hC.d, hdH⟩ * ⟨x, hxH⟩) : MGroup P.Q₀) =
      mRefl P.Q₀ mU * mRefl P.Q₀ (pencilVec P x) := by
    rw [map_mul, Subgroup.coe_mul, h4, h5]
  calc orderOf (hC.d * x) =
      orderOf (⟨hC.d, hdH⟩ * ⟨x, hxH⟩ : ↥(Halpha D (hC.conj P.g).alpha)) := h1
    _ = orderOf (P.ψ₁ (⟨hC.d, hdH⟩ * ⟨x, hxH⟩)) :=
        (orderOf_injective (P.ψ₁ : ↥(Halpha D (hC.conj P.g).alpha) →*
          ↥(Subgroup.centralizer {mRefl P.Q₀ (mLift P.Q₀ (P.c.vec (hC.conj P.g).d))}))
          P.ψ₁.injective _).symm
    _ = orderOf ((P.ψ₁ (⟨hC.d, hdH⟩ * ⟨x, hxH⟩) : MGroup P.Q₀)) :=
        (Subgroup.orderOf_coe _).symm
    _ = orderOf (mRefl P.Q₀ mU * mRefl P.Q₀ (pencilVec P x)) := by rw [h2]

private theorem lineParam_mem_range (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    lineParam P x hx hxd ∈ (artinSchreierHom (K := F)).range := by
  have hβ : (pencilVec P x).1.2 ≠ 0 := snd_pencilVec_ne_zero P hx hxd
  have hY : mForm P.Q₀ (pencilVec P x) = 1 := by
    rw [pencilVec, P.hγ, mForm_mLift]
  have hq : 2 ^ B.f - 1 = Fintype.card F - 1 := by
    rw [← Nat.card_eq_fintype_card, P.hF]
  have hC1 : (lineMem D hC.d x).ncard = 2 ^ B.f - 1 ↔
      (pencilVec P x).1.2⁻¹ ∈ (artinSchreierHom (K := F)).range := by
    rw [← orderOf_mul_dvd_iff_ncard_lineMem (B := B) P.c P.hnk P.hF hx.1 hxd,
      orderOf_mul_eq_mRefl_mul P hx, hq]
    exact orderOf_mRefl_mul_dvd_iff (Q₀ := P.Q₀) P.hQ₀ hY hβ
  have hplus1 : (IsPlusType (P.lineForm x hx hxd) ↔ IsPlusType P.Q₀) ↔
      (pencilVec P x).1.2⁻¹ ∈ (artinSchreierHom (K := F)).range := by
    rw [← hC1]
    obtain ⟨w₀, hw₀D, hw₀n, hw₀Q⟩ := P.hQ₀ty
    exact isPlusType_iff_ncard (B := B) P.c P.hnk P.hF hx.1 hw₀D hw₀n
      (lineForm_isFormOfLine P x hx hxd) hw₀Q
  have hplus2 : IsPlusType (pencilForm P x) ↔
      (IsPlusType P.Q₀ ↔ (pencilVec P x).1.2⁻¹ ∈ (artinSchreierHom (K := F)).range) :=
    isPlusType_mStabForm_iff (Q₀ := P.Q₀) P.hQ₀ hY hβ
  have hAS : IsPlusType (P.lineForm x hx hxd) ↔ IsPlusType (pencilForm P x) := by
    tauto
  have hnd : (polarBilin (pencilForm P x)).Nondegenerate := by
    have hB : polarBilin (pencilForm P x) = spForm k F := by
      refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
      rw [QuadraticMap.polarBilin_apply_apply]
      exact polar_mStabForm P.hQ₀ (pencilVec P x) a b
    rw [hB]
    exact spForm_nondegenerate
  have hw : ∀ a, P.lineForm x hx hxd a = pencilForm P x a +
      polar (pencilForm P x) (lineParam P x hx hxd • P.c.vec (hC.conj P.g).d) a ^ 2 := by
    intro a
    rw [lineParam_spec P x hx hxd a, QuadraticMap.polar_smul_left, smul_eq_mul,
      polar_mStabForm P.hQ₀]
  have hplus3 : IsPlusType (P.lineForm x hx hxd) ↔
      (IsPlusType (pencilForm P x) ↔
        (pencilForm P x) (lineParam P x hx hxd • P.c.vec (hC.conj P.g).d) ∈
          (artinSchreierHom (K := F)).range) :=
    isPlusType_add_sq_polar_iff hnd _ hw
  have hR : (pencilForm P x) (lineParam P x hx hxd • P.c.vec (hC.conj P.g).d) ∈
      (artinSchreierHom (K := F)).range := by
    tauto
  have hc2 : (pencilForm P x) (lineParam P x hx hxd • P.c.vec (hC.conj P.g).d) =
      lineParam P x hx hxd ^ 2 := by
    rw [QuadraticMap.map_smul, smul_eq_mul, stabForm_vec_conj_eq_one P hx hxd, mul_one, _root_.sq]
  rw [hc2] at hR
  exact (sq_mem_range_artinSchreier_iff (lineParam P x hx hxd)).mp hR

private noncomputable def normVec (P : PencilData hC B k F) (x : G) :
    Fin k ⊕ Fin k → F :=
  ((pencilVec P x).1.2)⁻¹ • (pencilVec P x).2

private lemma pencilForm_eq_normVec (P : PencilData hC B k F) (x : G)
    (a : Fin k ⊕ Fin k → F) :
    pencilForm P x a = P.Q₀ a + (spForm k F (normVec P x) a) ^ 2 :=
  mStabForm_apply P.hQ₀ (pencilVec P x) a

private lemma lineForm_eq_normVec (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d)
    (a : Fin k ⊕ Fin k → F) :
    P.lineForm x hx hxd a = P.Q₀ a +
      (spForm k F (normVec P x + lineParam P x hx hxd •
        P.c.vec (hC.conj P.g).d) a) ^ 2 := by
  have hsm : ((spForm k F) (lineParam P x hx hxd • P.c.vec (hC.conj P.g).d)) a =
      lineParam P x hx hxd * ((spForm k F) (P.c.vec (hC.conj P.g).d)) a := by
    rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [lineParam_spec P x hx hxd a, pencilForm_eq_normVec]
  have hsplit : ((spForm k F) (normVec P x + lineParam P x hx hxd •
      P.c.vec (hC.conj P.g).d)) a =
      ((spForm k F) (normVec P x)) a +
        lineParam P x hx hxd * ((spForm k F) (P.c.vec (hC.conj P.g).d)) a := by
    rw [LinearMap.map_add, LinearMap.add_apply, hsm]
  rw [hsplit, CharTwo.add_sq]
  ring

private lemma exists_spForm_vec_conj_eq_any (P : PencilData hC B k F) (b : F) :
    ∃ u : Fin k ⊕ Fin k → F, spForm k F ((pencilCv P).vec hC.d) u = b := by
  have hy : (pencilCv P).vec hC.d ≠ 0 :=
    (pencilCv P).vec_ne_zero hC.d (mem_commSet_symm hC.hd P.hv)
  by_cases hb : b = 0
  · exact ⟨0, by rw [hb, map_zero]⟩
  · have hex : ∃ u, spForm k F ((pencilCv P).vec hC.d) u ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (spForm_nondegenerate.1 _ h)
    obtain ⟨u₀, hu₀⟩ := hex
    exact ⟨(b / spForm k F ((pencilCv P).vec hC.d) u₀) • u₀, by
      rw [LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ b hu₀]⟩

private lemma exists_add_smul_orthogonal_notMem_span (P : PencilData hC B k F)
    {u₁ r₀ : Fin k ⊕ Fin k → F}
    (hu₁ : spForm k F ((pencilCv P).vec hC.d) u₁ ≠ 0)
    (hr₀ : spForm k F u₁ r₀ = 0)
    (hr₀span : r₀ ∉ Submodule.span F {u₁}) :
    ∃ r : Fin k ⊕ Fin k → F, spForm k F ((pencilCv P).vec hC.d) r = 0 ∧
      spForm k F u₁ r = 0 ∧ r ∉ Submodule.span F {u₁} ∧ r ≠ 0 := by
  set r : Fin k ⊕ Fin k → F :=
    r₀ + (spForm k F ((pencilCv P).vec hC.d) r₀ /
      spForm k F ((pencilCv P).vec hC.d) u₁) • u₁ with hr
  have hsymm : spForm k F u₁ ((pencilCv P).vec hC.d) =
      spForm k F ((pencilCv P).vec hC.d) u₁ :=
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt _ _
  have hyr : spForm k F ((pencilCv P).vec hC.d) r = 0 := by
    rw [hr, map_add, LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ hu₁,
      CharTwo.add_self_eq_zero]
  have hu₁r : spForm k F u₁ r = 0 := by
    rw [hr, map_add, LinearMap.map_smul, smul_eq_mul,
      (spForm_isAlt (r := k) (K := F)).self_eq_zero, mul_zero]
    simpa using hr₀
  have hr0 : r ≠ 0 := by
    intro h
    have hneg : -((spForm k F ((pencilCv P).vec hC.d) r₀ /
        spForm k F ((pencilCv P).vec hC.d) u₁) • u₁) =
        (spForm k F ((pencilCv P).vec hC.d) r₀ /
          spForm k F ((pencilCv P).vec hC.d) u₁) • u₁ := by
      funext i
      exact CharTwo.neg_eq _
    have h' : r₀ = (spForm k F ((pencilCv P).vec hC.d) r₀ /
        spForm k F ((pencilCv P).vec hC.d) u₁) • u₁ := by
      rw [hr] at h
      have h2 := add_eq_zero_iff_eq_neg.mp h
      rwa [hneg] at h2
    exact hr₀span (h' ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u₁))
  have hrspan : r ∉ Submodule.span F {u₁} := by
    intro hmem
    apply hr₀span
    have h1 : r₀ = r + (spForm k F ((pencilCv P).vec hC.d) r₀ /
        spForm k F ((pencilCv P).vec hC.d) u₁) • u₁ := by
      rw [hr, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]
    rw [h1]
    exact Submodule.add_mem _ hmem
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u₁))
  exact ⟨r, hyr, hu₁r, hrspan, hr0⟩

private lemma exists_orthogonal_notMem (P : PencilData hC B k F) {u₁ : Fin k ⊕ Fin k → F}
    (hu₁ : spForm k F ((pencilCv P).vec hC.d) u₁ ≠ 0) :
    ∃ r : Fin k ⊕ Fin k → F, spForm k F ((pencilCv P).vec hC.d) r = 0 ∧
      spForm k F u₁ r = 0 ∧ r ∉ Submodule.span F {u₁} ∧
      r ∉ Submodule.span F {(pencilCv P).vec hC.d} := by
  have hu₁' : u₁ ≠ 0 := fun h => hu₁ (by rw [h, map_zero])
  obtain ⟨r₀, hr₀', hr₀ne⟩ :=
    CFSG.OddTranspositions.PartThree.exists_spForm_eq_zero_forall_ne_smul
      (k := k) (F := F) (B.two_le_rank P.hnk) hu₁'
  have hr₀ : spForm k F u₁ r₀ = 0 := by
    rw [CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt]
    exact hr₀'
  have hr₀span : r₀ ∉ Submodule.span F {u₁} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    exact hr₀ne a ha.symm
  obtain ⟨r, hyr, hu₁r, hrspan, hr0⟩ :=
    exists_add_smul_orthogonal_notMem_span P hu₁ hr₀ hr₀span
  have hsymm : spForm k F u₁ ((pencilCv P).vec hC.d) =
      spForm k F ((pencilCv P).vec hC.d) u₁ :=
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt _ _
  have hry : r ∉ Submodule.span F {(pencilCv P).vec hC.d} := by
    intro hmem
    obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 : spForm k F u₁ r = 0 := hu₁r
    rw [← hμ, LinearMap.map_smul, smul_eq_mul, hsymm] at h0
    have hμ0 : μ = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hu₁
    rw [hμ0, zero_smul] at hμ
    exact hr0 hμ.symm
  exact ⟨r, hyr, hu₁r, hrspan, hry⟩

private noncomputable abbrev secondCoord (P : PencilData hC B k F) (x : G) : F :=
  (pencilVec P x).1.2

private lemma normVec_def (P : PencilData hC B k F) (x : G) :
    normVec P x = (secondCoord P x)⁻¹ • (pencilVec P x).2 := rfl

private lemma pencilVec_add (P : PencilData hC B k F) {x₁ x₂ x_t : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d)
    (hcomm : Commute x₁ x₂) {t : F}
    (hvec : (pencilCv P).vec x_t = (1 - t) • (pencilCv P).vec x₁ + t • (pencilCv P).vec x₂) :
    pencilVec P x_t = (1 - P.σ t) • pencilVec P x₁ + P.σ t • pencilVec P x₂ := by
  have hcomm' : spForm k F ((pencilCv P).vec x₁) ((pencilCv P).vec x₂) = 0 :=
    ((pencilCv P).commute_iff x₁ hx₁ x₂ hx₂).mp hcomm
  have horth : spForm k F (P.A ((pencilCv P).vec x₁)) (P.A ((pencilCv P).vec x₂)) = 0 := by
    rw [P.hAform, hcomm', map_zero]
  have hA : P.A ((pencilCv P).vec x_t) = (1 - P.σ t) • P.A ((pencilCv P).vec x₁) +
      P.σ t • P.A ((pencilCv P).vec x₂) := by
    rw [hvec, P.hAadd, P.hAsmul, P.hAsmul, map_sub, map_one]
  calc pencilVec P x_t = P.γ (mLift P.Q₀ (P.A ((pencilCv P).vec x_t))) := rfl
    _ = P.γ (mLift P.Q₀ ((1 - P.σ t) • P.A ((pencilCv P).vec x₁) +
          P.σ t • P.A ((pencilCv P).vec x₂))) := by rw [hA]
    _ = P.γ ((1 - P.σ t) • mLift P.Q₀ (P.A ((pencilCv P).vec x₁)) +
          P.σ t • mLift P.Q₀ (P.A ((pencilCv P).vec x₂))) := by
        rw [mLift_add_smul P.hQ₀ horth]
    _ = (1 - P.σ t) • pencilVec P x₁ + P.σ t • pencilVec P x₂ := by
        rw [map_add, map_smul, map_smul]

private lemma secondCoord_add (P : PencilData hC B k F) {x₁ x₂ x_t : G} {s : F}
    (hvec : pencilVec P x_t = (1 - s) • pencilVec P x₁ + s • pencilVec P x₂) :
    secondCoord P x_t = (1 - s) * secondCoord P x₁ + s * secondCoord P x₂ := by
  have h := congrArg (fun Y : MSpace k F => Y.1.2) hvec
  simpa [secondCoord, smul_eq_mul] using h

private lemma snd_add (P : PencilData hC B k F) {x₁ x₂ x_t : G} {s : F}
    (hvec : pencilVec P x_t = (1 - s) • pencilVec P x₁ + s • pencilVec P x₂) :
    (pencilVec P x_t).2 = (1 - s) • (pencilVec P x₁).2 + s • (pencilVec P x₂).2 := by
  have h := congrArg (fun Y : MSpace k F => Y.2) hvec
  simpa using h

private lemma normVec_add (P : PencilData hC B k F) {x₁ x₂ x_t : G} {s : F}
    (h₁ : secondCoord P x₁ ≠ 0) (h₂ : secondCoord P x₂ ≠ 0)
    (ht : secondCoord P x_t ≠ 0)
    (hvec : pencilVec P x_t = (1 - s) • pencilVec P x₁ + s • pencilVec P x₂) :
    normVec P x_t = (1 + (secondCoord P x_t)⁻¹ * s * secondCoord P x₂) • normVec P x₁ +
      ((secondCoord P x_t)⁻¹ * s * secondCoord P x₂) • normVec P x₂ := by
  have he := secondCoord_add P hvec
  have hw := snd_add P hvec
  set lam : F := (secondCoord P x_t)⁻¹ * s * secondCoord P x₂ with hlam
  have h1 : (secondCoord P x_t)⁻¹ * (1 - s) = (1 + lam) * (secondCoord P x₁)⁻¹ := by
    rw [hlam]
    field_simp [h₁, h₂, ht]
    rw [he]
    ring_nf
    rw [show (2 : F) = 0 from CharP.cast_eq_zero F 2, mul_zero, add_zero]
  have h2 : (secondCoord P x_t)⁻¹ * s = lam * (secondCoord P x₂)⁻¹ := by
    rw [hlam]
    field_simp [h₁, h₂, ht]
  rw [normVec_def, normVec_def, normVec_def, hw, smul_add, smul_smul, smul_smul, smul_smul,
    smul_smul, h1, h2]

omit [DecidableEq F] in
private lemma snd_mem_span_of_mem_span {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {v : Fin k ⊕ Fin k → F} {X : MSpace k F}
    (hX : X ∈ Submodule.span F {mLift Q₀ v, mU}) :
    X.2 ∈ Submodule.span F {v} := by
  refine Submodule.span_induction (p := fun X _ => X.2 ∈ Submodule.span F {v}) ?_ ?_ ?_ ?_ hX
  · intro Y hY
    rcases hY with hY | hY
    · rw [Set.mem_singleton_iff.mp hY]
      exact Submodule.subset_span (Set.mem_singleton v)
    · rw [Set.mem_singleton_iff.mp hY]
      exact Submodule.zero_mem _
  · exact Submodule.zero_mem _
  · intro Y Z _ _ hY hZ
    exact Submodule.add_mem _ hY hZ
  · intro a Y _ hY
    exact Submodule.smul_mem _ a hY

omit [DecidableEq F] in
private lemma mk_mem_span_mU_mLift {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {v : Fin k ⊕ Fin k → F} (m t : F) :
    (((m, 0) : F × F), t • v) ∈ Submodule.span F {mU, mLift Q₀ v} := by
  rw [Submodule.mem_span_pair]
  refine ⟨m - t * (mLift Q₀ v).1.1, t, ?_⟩
  refine Prod.ext ?_ ?_
  · refine Prod.ext ?_ ?_ <;> simp [mU, mLift, smul_eq_mul]
  · funext i
    simp [mU, mLift, smul_eq_mul]

private lemma preimage_span_y' (P : PencilData hC B k F)
    {v : Fin k ⊕ Fin k → F} (hv : P.A v ∈ Submodule.span F {P.y'}) :
    v ∈ Submodule.span F {(pencilCv P).vec hC.d} := by
  rw [← P.hAy] at hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have h1 : c • P.A ((pencilCv P).vec hC.d) =
      P.A (P.σ.symm c • (pencilCv P).vec hC.d) := by
    rw [P.hAsmul, P.σ.apply_symm_apply]
  rw [h1] at hc
  have h2 : v = P.σ.symm c • (pencilCv P).vec hC.d := (P.hA.injective hc).symm
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma semilinear_norm_comb (P : PencilData hC B k F) {u₁ u₂ : Fin k ⊕ Fin k → F}
    {x₁ x₂ : G} :
    (secondCoord P x₁)⁻¹ • P.A u₁ + (secondCoord P x₂)⁻¹ • P.A u₂ =
      P.A ((P.σ.symm (secondCoord P x₁))⁻¹ • u₁ +
        (P.σ.symm (secondCoord P x₂))⁻¹ • u₂) := by
  rw [P.hAadd, P.hAsmul, P.hAsmul]
  congr 2
  · rw [map_inv₀, P.σ.apply_symm_apply]
  · rw [map_inv₀, P.σ.apply_symm_apply]

private lemma snd_gamma_symm_mem_span (P : PencilData hC B k F) {Z : MSpace k F} {t : F}
    (hZ1 : Z.1.2 = 0) (hZ2 : Z.2 = t • P.c.vec (hC.conj P.g).d) :
    (P.γ.symm Z).2 ∈ Submodule.span F {P.y'} := by
  have hZeq : Z = (((Z.1.1, 0) : F × F), t • P.c.vec (hC.conj P.g).d) := by
    refine Prod.ext ?_ ?_
    · refine Prod.ext ?_ ?_
      · rfl
      · exact hZ1
    · exact hZ2
  have hmemZ : Z ∈ Submodule.span F {mU, mLift P.Q₀ (P.c.vec (hC.conj P.g).d)} := by
    rw [hZeq]
    exact mk_mem_span_mU_mLift Z.1.1 t
  have hmap : Submodule.map (P.γ.symm : MSpace k F →ₗ[F] MSpace k F)
      (Submodule.span F {mU, mLift P.Q₀ (P.c.vec (hC.conj P.g).d)}) =
      Submodule.span F {mLift P.Q₀ P.y', mU} := by
    rw [Submodule.map_span]
    have e1 : (P.γ.symm : MSpace k F →ₗ[F] MSpace k F) mU = mLift P.Q₀ P.y' := by
      rw [← P.hγy']
      exact P.γ.symm_apply_apply _
    have e2 : (P.γ.symm : MSpace k F →ₗ[F] MSpace k F) (mLift P.Q₀ (P.c.vec (hC.conj P.g).d)) =
        mU := by
      rw [← P.hγU]
      exact P.γ.symm_apply_apply _
    rw [Set.image_pair, e1, e2]
  have hZs : P.γ.symm Z ∈ Submodule.span F {mLift P.Q₀ P.y', mU} := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem hmemZ
  exact snd_mem_span_of_mem_span hZs

private lemma normVec_add_notMem_span (P : PencilData hC B k F) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hxd₁ : ¬ Commute x₁ hC.d)
    (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d) (hxd₂ : ¬ Commute x₂ hC.d)
    {u₁ u₂ : Fin k ⊕ Fin k → F}
    (hv₁ : (pencilCv P).vec x₁ = u₁) (hv₂ : (pencilCv P).vec x₂ = u₂)
    (hind : (P.σ.symm (secondCoord P x₁))⁻¹ • u₁ + (P.σ.symm (secondCoord P x₂))⁻¹ • u₂ ∉
      Submodule.span F {(pencilCv P).vec hC.d}) :
    normVec P x₁ + normVec P x₂ ∉ Submodule.span F {P.c.vec (hC.conj P.g).d} := by
  intro hmem
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 : secondCoord P x₁ ≠ 0 := snd_pencilVec_ne_zero P hx₁ hxd₁
  have h2 : secondCoord P x₂ ≠ 0 := snd_pencilVec_ne_zero P hx₂ hxd₂
  set Z : MSpace k F :=
    (secondCoord P x₁)⁻¹ • pencilVec P x₁ + (secondCoord P x₂)⁻¹ • pencilVec P x₂ with hZ
  have hZ1 : Z.1.2 = 0 := by
    rw [hZ]
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
      secondCoord]
    rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2, CharTwo.add_self_eq_zero]
  have hZ2 : Z.2 = t • P.c.vec (hC.conj P.g).d := by
    rw [hZ]
    simp only [Prod.snd_add, Prod.smul_snd, secondCoord]
    exact ht.symm
  have hsnd : (P.γ.symm Z).2 ∈ Submodule.span F {P.y'} :=
    snd_gamma_symm_mem_span P hZ1 hZ2
  have hγZ : (P.γ.symm Z).2 =
      (secondCoord P x₁)⁻¹ • P.A u₁ + (secondCoord P x₂)⁻¹ • P.A u₂ := by
    rw [hZ, map_add, map_smul, map_smul]
    have e1 : P.γ.symm (pencilVec P x₁) = mLift P.Q₀ (P.A u₁) := by
      rw [pencilVec, LinearEquiv.symm_apply_apply, hv₁]
    have e2 : P.γ.symm (pencilVec P x₂) = mLift P.Q₀ (P.A u₂) := by
      rw [pencilVec, LinearEquiv.symm_apply_apply, hv₂]
    rw [e1, e2]
    simp [mLift]
  rw [hγZ, semilinear_norm_comb P] at hsnd
  exact hind (preimage_span_y' P hsnd)

private lemma lineForm_eq_one_of_mem_ker_add (P : PencilData hC B k F) {x₁ x₂ x_t : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hxd₁ : ¬ Commute x₁ hC.d)
    (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d) (hxd₂ : ¬ Commute x₂ hC.d)
    (hx_t : x_t ∈ commSet D (hC.conj P.g).d) (hxd_t : ¬ Commute x_t hC.d)
    (hline : x_t ∈ lineMem D x₁ x₂)
    {z₁ z₂ : Fin k ⊕ Fin k → F}
    (hz₁ : z₁ = normVec P x₁ + lineParam P x₁ hx₁ hxd₁ • P.c.vec (hC.conj P.g).d)
    (hz₂ : z₂ = normVec P x₂ + lineParam P x₂ hx₂ hxd₂ • P.c.vec (hC.conj P.g).d)
    {K : Submodule F (Fin k ⊕ Fin k → F)}
    (hK : K = LinearMap.ker ((spForm k F) (z₁ + z₂)))
    {b : Fin k ⊕ Fin k → F} (hbK : b ∈ K) (hb1 : P.lineForm x₁ hx₁ hxd₁ b = 1) :
    P.lineForm x₂ hx₂ hxd₂ b = 1 ∧ P.lineForm x_t hx_t hxd_t b = 1 := by
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb1
    exact zero_ne_one hb1
  have hbK' : ((spForm k F) z₁) b = ((spForm k F) z₂) b := by
    have h := LinearMap.mem_ker.mp (by rwa [hK] at hbK)
    rw [map_add, LinearMap.add_apply] at h
    have h2 : ((spForm k F) z₂) b = -(((spForm k F) z₁) b) :=
      eq_neg_of_add_eq_zero_right h
    rw [CharTwo.neg_eq] at h2
    exact h2.symm
  have hb2 : P.lineForm x₂ hx₂ hxd₂ b = 1 := by
    rw [lineForm_eq_normVec P hx₂ hxd₂ b, ← hz₂, hbK'.symm]
    rw [lineForm_eq_normVec P hx₁ hxd₁ b, ← hz₁] at hb1
    exact hb1
  obtain ⟨z', hz'D, hz'v⟩ := P.c.exists_vec b hb0
  have hmem₁ : z' ∈ commSet D x₁ :=
    (lineForm_isFormOfLine P x₁ hx₁ hxd₁).2 z' hz'D |>.mpr (by rw [hz'v]; exact hb1)
  have hmem₂ : z' ∈ commSet D x₂ :=
    (lineForm_isFormOfLine P x₂ hx₂ hxd₂).2 z' hz'D |>.mpr (by rw [hz'v]; exact hb2)
  have hperp : z' ∈ perpMem D x_t :=
    hline.2 ⟨⟨hmem₁.1, hmem₁.2.1⟩, ⟨hmem₂.1, hmem₂.2.1⟩⟩
  have hne : z' ≠ x_t := by
    intro h
    exact hxd_t (h ▸ hz'D.2.1)
  refine ⟨hb2, ?_⟩
  have hcz : z' ∈ commSet D x_t := ⟨hperp.1, hperp.2, hne⟩
  have h := (lineForm_isFormOfLine P x_t hx_t hxd_t).2 z' hz'D |>.mp hcz
  rwa [hz'v] at h

private lemma shifted_add_perp_orth (P : PencilData hC B k F) {x₁ x₂ x_t : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hxd₁ : ¬ Commute x₁ hC.d)
    (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d) (hxd₂ : ¬ Commute x₂ hC.d)
    (hx_t : x_t ∈ commSet D (hC.conj P.g).d) (hxd_t : ¬ Commute x_t hC.d)
    (hline : x_t ∈ lineMem D x₁ x₂)
    {z₁ z₂ zt : Fin k ⊕ Fin k → F}
    (hz₁ : z₁ = normVec P x₁ + lineParam P x₁ hx₁ hxd₁ • P.c.vec (hC.conj P.g).d)
    (hz₂ : z₂ = normVec P x₂ + lineParam P x₂ hx₂ hxd₂ • P.c.vec (hC.conj P.g).d)
    (hzt : zt = normVec P x_t + lineParam P x_t hx_t hxd_t • P.c.vec (hC.conj P.g).d)
    {K : Submodule F (Fin k ⊕ Fin k → F)}
    (hK : K = LinearMap.ker ((spForm k F) (z₁ + z₂)))
    (hKspan : Submodule.span F {a : Fin k ⊕ Fin k → F | a ∈ K ∧
      P.lineForm x₁ hx₁ hxd₁ a = 1} = K) :
    ∀ a ∈ K, ((spForm k F) (zt + z₁)) a = 0 := by
  intro a ha
  have hsp : a ∈ Submodule.span F {b : Fin k ⊕ Fin k → F | b ∈ K ∧
      P.lineForm x₁ hx₁ hxd₁ b = 1} := by rw [hKspan]; exact ha
  refine Submodule.span_induction (p := fun b _ => ((spForm k F) (zt + z₁)) b = 0) ?_ ?_ ?_ ?_ hsp
  · intro b hb
    obtain ⟨hbK, hb1⟩ := hb
    obtain ⟨hb2, hform⟩ :=
      lineForm_eq_one_of_mem_ker_add P hx₁ hxd₁ hx₂ hxd₂ hx_t hxd_t hline hz₁ hz₂ hK hbK hb1
    have e1 : (((spForm k F) z₁) b) ^ 2 = 1 - P.Q₀ b := by
      have h := hb1
      rw [lineForm_eq_normVec P hx₁ hxd₁ b, ← hz₁] at h
      linear_combination h
    have et : (((spForm k F) zt) b) ^ 2 = 1 - P.Q₀ b := by
      have h := hform
      rw [lineForm_eq_normVec P hx_t hxd_t b, ← hzt] at h
      linear_combination h
    have hzzt : ((spForm k F) zt) b = ((spForm k F) z₁) b :=
      CharTwo.sq_injective (et.trans e1.symm)
    rw [map_add, LinearMap.add_apply, hzzt, CharTwo.add_self_eq_zero]
  · exact map_zero _
  · intro u v _ _ hu hv
    rw [map_add, hu, hv, add_zero]
  · intro c u _ hu
    rw [LinearMap.map_smul, hu, smul_eq_mul, mul_zero]

private lemma lineForm_vec_conj_eq_one (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) (hxd : ¬ Commute x hC.d) :
    P.lineForm x hx hxd (P.c.vec (hC.conj P.g).d) = 1 := by
  have hmem : (hC.conj P.g).d ∈ commSet D x := by
    refine ⟨P.hv.1, hx.2.1.symm, ?_⟩
    intro h
    exact hxd (h ▸ P.hv.2.1)
  exact (lineForm_isFormOfLine P x hx hxd).2 (hC.conj P.g).d P.hv |>.mp hmem

private lemma spForm_shifted_vec_conj_eq (P : PencilData hC B k F) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hxd₁ : ¬ Commute x₁ hC.d)
    (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d) (hxd₂ : ¬ Commute x₂ hC.d)
    {z₁ z₂ : Fin k ⊕ Fin k → F}
    (hz₁ : z₁ = normVec P x₁ + lineParam P x₁ hx₁ hxd₁ • P.c.vec (hC.conj P.g).d)
    (hz₂ : z₂ = normVec P x₂ + lineParam P x₂ hx₂ hxd₂ • P.c.vec (hC.conj P.g).d) :
    ((spForm k F) z₁) (P.c.vec (hC.conj P.g).d) =
      ((spForm k F) z₂) (P.c.vec (hC.conj P.g).d) := by
  have f1 : (((spForm k F) z₁) (P.c.vec (hC.conj P.g).d)) ^ 2 =
      1 - P.Q₀ (P.c.vec (hC.conj P.g).d) := by
    have h := lineForm_vec_conj_eq_one P hx₁ hxd₁
    rw [lineForm_eq_normVec P hx₁ hxd₁ (P.c.vec (hC.conj P.g).d), ← hz₁] at h
    linear_combination h
  have f2 : (((spForm k F) z₂) (P.c.vec (hC.conj P.g).d)) ^ 2 =
      1 - P.Q₀ (P.c.vec (hC.conj P.g).d) := by
    have h := lineForm_vec_conj_eq_one P hx₂ hxd₂
    rw [lineForm_eq_normVec P hx₂ hxd₂ (P.c.vec (hC.conj P.g).d), ← hz₂] at h
    linear_combination h
  exact CharTwo.sq_injective (f1.trans f2.symm)

private lemma shifted_add_perp (P : PencilData hC B k F) {x₁ x₂ x_t : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hxd₁ : ¬ Commute x₁ hC.d)
    (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d) (hxd₂ : ¬ Commute x₂ hC.d)
    (hx_t : x_t ∈ commSet D (hC.conj P.g).d) (hxd_t : ¬ Commute x_t hC.d)
    (hline : x_t ∈ lineMem D x₁ x₂) :
    ∃ mu : F, (normVec P x_t + lineParam P x_t hx_t hxd_t • P.c.vec (hC.conj P.g).d) +
        (normVec P x₁ + lineParam P x₁ hx₁ hxd₁ • P.c.vec (hC.conj P.g).d) =
      mu • ((normVec P x₁ + lineParam P x₁ hx₁ hxd₁ • P.c.vec (hC.conj P.g).d) +
        (normVec P x₂ + lineParam P x₂ hx₂ hxd₂ • P.c.vec (hC.conj P.g).d)) := by
  set av : Fin k ⊕ Fin k → F := P.c.vec (hC.conj P.g).d with hav
  set z₁ : Fin k ⊕ Fin k → F := normVec P x₁ + lineParam P x₁ hx₁ hxd₁ • av with hz₁
  set z₂ : Fin k ⊕ Fin k → F := normVec P x₂ + lineParam P x₂ hx₂ hxd₂ • av with hz₂
  set zt : Fin k ⊕ Fin k → F := normVec P x_t + lineParam P x_t hx_t hxd_t • av with hzt
  have havne : av ≠ 0 := by
    rw [hav]
    exact P.c.vec_ne_zero _ P.hv
  set K : Submodule F (Fin k ⊕ Fin k → F) := LinearMap.ker ((spForm k F) (z₁ + z₂)) with hK
  have hspv : ((spForm k F) z₁) av = ((spForm k F) z₂) av :=
    spForm_shifted_vec_conj_eq P hx₁ hxd₁ hx₂ hxd₂ hz₁ hz₂
  have havK : av ∈ K := by
    rw [hK, LinearMap.mem_ker, map_add, LinearMap.add_apply, hspv, CharTwo.add_self_eq_zero]
  have hQnd : (polarBilin (P.lineForm x₁ hx₁ hxd₁)).Nondegenerate := by
    have hB : polarBilin (P.lineForm x₁ hx₁ hxd₁) = spForm k F := by
      refine LinearMap.ext fun a => LinearMap.ext fun b => ?_
      rw [QuadraticMap.polarBilin_apply_apply]
      exact (lineForm_isFormOfLine P x₁ hx₁ hxd₁).1 a b
    rw [hB]
    exact spForm_nondegenerate
  have hKspan : Submodule.span F {a : Fin k ⊕ Fin k → F | a ∈ K ∧
      P.lineForm x₁ hx₁ hxd₁ a = 1} = K :=
    span_setOf_eq_one_of_exists_ne_zero ((B.two_lt_card P.hF).trans_eq Nat.card_eq_fintype_card)
      ⟨av, havK, by rw [lineForm_vec_conj_eq_one P hx₁ hxd₁]; exact one_ne_zero⟩
  have horthK : ∀ a ∈ K, ((spForm k F) (zt + z₁)) a = 0 :=
    shifted_add_perp_orth P hx₁ hxd₁ hx₂ hxd₂ hx_t hxd_t hline hz₁ hz₂ hzt hK hKspan
  have hspan : zt + z₁ ∈ Submodule.span F {z₁ + z₂} := by
    have h := CFSG.ClassicalGroups.Alternating.mem_span_of_forall_orthogonal
      (B := spForm k F) spForm_nondegenerate (fun _ : Unit => z₁ + z₂) (zt + z₁) ?_
    · simpa using h
    · intro y hy
      exact horthK y (hy ())
  obtain ⟨mu, hmu⟩ := Submodule.mem_span_singleton.mp hspan
  exact ⟨mu, hmu.symm⟩

private lemma normVec_add_shifted_eq (P : PencilData hC B k F) {x₁ x₂ x_t : G}
    {lam ct c1 : F} {av : Fin k ⊕ Fin k → F}
    (hnv : normVec P x_t = (1 + lam) • normVec P x₁ + lam • normVec P x₂) :
    (normVec P x_t + ct • av) + (normVec P x₁ + c1 • av) =
      lam • (normVec P x₁ + normVec P x₂) + (ct + c1) • av := by
  rw [hnv]
  have hcollapse : (1 + lam) • normVec P x₁ + normVec P x₁ = lam • normVec P x₁ := by
    have h1 : (1 + lam) • normVec P x₁ + normVec P x₁ =
        (1 + lam) • normVec P x₁ + (1 : F) • normVec P x₁ := by rw [one_smul]
    rw [h1, ← add_smul,
      show (1 + lam) + 1 = lam by
        rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]]
  rw [show (((1 + lam) • normVec P x₁ + lam • normVec P x₂) + ct • av) +
      (normVec P x₁ + c1 • av) =
      ((1 + lam) • normVec P x₁ + normVec P x₁) +
        (lam • normVec P x₂ + (ct • av + c1 • av)) by abel]
  rw [hcollapse]
  rw [smul_add, add_smul]
  abel

private lemma lineParam_hEq (P : PencilData hC B k F) {x₁ x₂ x_t : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hxd₁ : ¬ Commute x₁ hC.d)
    (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d) (hxd₂ : ¬ Commute x₂ hC.d)
    (hx_t : x_t ∈ commSet D (hC.conj P.g).d) (hxd_t : ¬ Commute x_t hC.d)
    (hcomm : Commute x₁ x₂) {t : F}
    (hvec : (pencilCv P).vec x_t = (1 - t) • (pencilCv P).vec x₁ + t • (pencilCv P).vec x₂)
    (hline : x_t ∈ lineMem D x₁ x₂) :
    ∃ mu : F,
      ((secondCoord P x_t)⁻¹ * P.σ t * secondCoord P x₂) •
          (normVec P x₁ + normVec P x₂) +
        (lineParam P x_t hx_t hxd_t + lineParam P x₁ hx₁ hxd₁) •
          P.c.vec (hC.conj P.g).d =
      mu • (normVec P x₁ + normVec P x₂) +
        (mu * (lineParam P x₁ hx₁ hxd₁ + lineParam P x₂ hx₂ hxd₂)) •
          P.c.vec (hC.conj P.g).d := by
  have h₁ := snd_pencilVec_ne_zero P hx₁ hxd₁
  have h₂ := snd_pencilVec_ne_zero P hx₂ hxd₂
  have ht := snd_pencilVec_ne_zero P hx_t hxd_t
  obtain ⟨mu, hmu⟩ := shifted_add_perp P hx₁ hxd₁ hx₂ hxd₂ hx_t hxd_t hline
  have hvecL : pencilVec P x_t =
      (1 - P.σ t) • pencilVec P x₁ + P.σ t • pencilVec P x₂ :=
    pencilVec_add P hx₁ hx₂ hcomm hvec
  set av : Fin k ⊕ Fin k → F := P.c.vec (hC.conj P.g).d with hav
  set c1 : F := lineParam P x₁ hx₁ hxd₁ with hc1
  set c2 : F := lineParam P x₂ hx₂ hxd₂ with hc2
  set ct : F := lineParam P x_t hx_t hxd_t with hct
  set lam : F := (secondCoord P x_t)⁻¹ * P.σ t * secondCoord P x₂ with hlam
  have hnv : normVec P x_t = (1 + lam) • normVec P x₁ + lam • normVec P x₂ :=
    normVec_add P h₁ h₂ ht hvecL
  have hmu' : (normVec P x_t + ct • av) + (normVec P x₁ + c1 • av) =
      mu • ((normVec P x₁ + c1 • av) + (normVec P x₂ + c2 • av)) := by
    simpa only [hav, hc1, hc2, hct] using hmu
  have hzt := normVec_add_shifted_eq P (av := av) (ct := ct) (c1 := c1) hnv
  have hR : mu • ((normVec P x₁ + c1 • av) + (normVec P x₂ + c2 • av)) =
      mu • (normVec P x₁ + normVec P x₂) + (mu * (c1 + c2)) • av := by
    rw [show (normVec P x₁ + c1 • av) + (normVec P x₂ + c2 • av) =
        (normVec P x₁ + normVec P x₂) + (c1 + c2) • av by rw [add_smul]; abel]
    rw [smul_add, smul_smul]
  refine ⟨mu, ?_⟩
  have hEq : lam • (normVec P x₁ + normVec P x₂) + (ct + c1) • av =
      mu • (normVec P x₁ + normVec P x₂) + (mu * (c1 + c2)) • av := by
    have h := hmu'
    rw [hR] at h
    exact hzt.symm.trans h
  simpa only [hav, hc1, hc2, hct, hlam] using hEq

omit [Fintype F] [DecidableEq F] in
private lemma coeff_eq_of_shifted_perp {a b av : Fin k ⊕ Fin k → F} {c1 c2 ct lam mu : F}
    (hav : av ≠ 0) (hnt : a + b ∉ Submodule.span F {av})
    (hEq : lam • (a + b) + (ct + c1) • av =
      mu • (a + b) + (mu * (c1 + c2)) • av) :
    lam = mu ∧ ct = (1 + lam) * c1 + lam * c2 := by
  have hzero : (lam • (a + b) + (ct + c1) • av) +
      (mu • (a + b) + (mu * (c1 + c2)) • av) = 0 := by
    rw [hEq]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hcomb : (lam + mu) • (a + b) + (ct + c1 + mu * (c1 + c2)) • av = 0 := by
    have h1 : (lam + mu) • (a + b) = lam • (a + b) + mu • (a + b) := add_smul lam mu _
    have h2 : (ct + c1 + mu * (c1 + c2)) • av =
        (ct + c1) • av + (mu * (c1 + c2)) • av := add_smul _ _ _
    rw [h1, h2]
    rw [show lam • (a + b) + mu • (a + b) + ((ct + c1) • av + (mu * (c1 + c2)) • av) =
        (lam • (a + b) + (ct + c1) • av) +
          (mu • (a + b) + (mu * (c1 + c2)) • av) by abel]
    exact hzero
  have hneg : -((ct + c1 + mu * (c1 + c2)) • av) = (ct + c1 + mu * (c1 + c2)) • av := by
    funext i
    exact CharTwo.neg_eq _
  have hstep : (lam + mu) • (a + b) = (ct + c1 + mu * (c1 + c2)) • av :=
    (eq_neg_of_add_eq_zero_left hcomb).trans hneg
  have hml : lam = mu := by
    have hsum : lam + mu = 0 := by
      by_contra hne
      apply hnt
      have hmem : (lam + mu) • (a + b) ∈ Submodule.span F {av} := by
        rw [hstep]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self av)
      have heq : a + b = (lam + mu)⁻¹ • ((lam + mu) • (a + b)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [heq]
      exact Submodule.smul_mem _ _ hmem
    exact CharTwo.add_eq_zero.mp hsum
  have hct0 : ct + c1 + lam * (c1 + c2) = 0 := by
    have h := hcomb
    rw [← hml] at h
    rw [CharTwo.add_self_eq_zero, zero_smul, zero_add] at h
    exact (smul_eq_zero.mp h).resolve_right hav
  refine ⟨hml, ?_⟩
  have h2 : ct + ((1 + lam) * c1 + lam * c2) = 0 := by
    rw [← hct0]
    ring
  exact (eq_neg_of_add_eq_zero_left h2).trans (CharTwo.neg_eq _)

private lemma lineParam_add (P : PencilData hC B k F) {x₁ x₂ x_t : G}
    (hx₁ : x₁ ∈ commSet D (hC.conj P.g).d) (hxd₁ : ¬ Commute x₁ hC.d)
    (hx₂ : x₂ ∈ commSet D (hC.conj P.g).d) (hxd₂ : ¬ Commute x₂ hC.d)
    (hx_t : x_t ∈ commSet D (hC.conj P.g).d) (hxd_t : ¬ Commute x_t hC.d)
    (hcomm : Commute x₁ x₂) {t : F}
    (hvec : (pencilCv P).vec x_t = (1 - t) • (pencilCv P).vec x₁ + t • (pencilCv P).vec x₂)
    (hnotspan : (P.σ.symm (secondCoord P x₁))⁻¹ • (pencilCv P).vec x₁ +
      (P.σ.symm (secondCoord P x₂))⁻¹ • (pencilCv P).vec x₂ ∉
        Submodule.span F {(pencilCv P).vec hC.d})
    (hline : x_t ∈ lineMem D x₁ x₂) :
    secondCoord P x_t * lineParam P x_t hx_t hxd_t =
      (1 - P.σ t) * (secondCoord P x₁ * lineParam P x₁ hx₁ hxd₁) +
        P.σ t * (secondCoord P x₂ * lineParam P x₂ hx₂ hxd₂) := by
  obtain ⟨mu, hEq⟩ := lineParam_hEq P hx₁ hxd₁ hx₂ hxd₂ hx_t hxd_t hcomm hvec hline
  set av : Fin k ⊕ Fin k → F := P.c.vec (hC.conj P.g).d with hav
  set c1 : F := lineParam P x₁ hx₁ hxd₁ with hc1
  set c2 : F := lineParam P x₂ hx₂ hxd₂ with hc2
  set ct : F := lineParam P x_t hx_t hxd_t with hct
  set lam : F := (secondCoord P x_t)⁻¹ * P.σ t * secondCoord P x₂ with hlam
  have havne : av ≠ 0 := by
    rw [hav]
    exact P.c.vec_ne_zero _ P.hv
  have hnt : normVec P x₁ + normVec P x₂ ∉ Submodule.span F {av} := by
    simpa only [av] using normVec_add_notMem_span P hx₁ hxd₁ hx₂ hxd₂
      (u₁ := (pencilCv P).vec x₁) (u₂ := (pencilCv P).vec x₂) rfl rfl
      (by simpa only [av] using hnotspan)
  obtain ⟨hml, hc_eq⟩ := coeff_eq_of_shifted_perp havne hnt
    (by simpa only [hav, hc1, hc2, hct, hlam] using hEq)
  have hc_eq' : ct = (1 + lam) * c1 + lam * c2 := by
    simpa only [hc1, hc2, hct, hlam] using hc_eq
  have ht := snd_pencilVec_ne_zero P hx_t hxd_t
  have hBt : secondCoord P x_t * lam = P.σ t * secondCoord P x₂ := by
    rw [hlam]
    field_simp
  have hBt' : secondCoord P x_t * (1 + lam) = (1 - P.σ t) * secondCoord P x₁ := by
    have hβ := secondCoord_add P (pencilVec_add P hx₁ hx₂ hcomm hvec)
    rw [mul_add, mul_one, hBt, hβ]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  calc secondCoord P x_t * ct
      = secondCoord P x_t * ((1 + lam) * c1 + lam * c2) := by rw [hc_eq']
    _ = (secondCoord P x_t * (1 + lam)) * c1 + (secondCoord P x_t * lam) * c2 := by ring
    _ = ((1 - P.σ t) * secondCoord P x₁) * c1 +
          (P.σ t * secondCoord P x₂) * c2 := by rw [hBt', hBt]
    _ = (1 - P.σ t) * (secondCoord P x₁ * c1) +
          P.σ t * (secondCoord P x₂ * c2) := by ring

private lemma not_commute_d_of_spForm_ne_zero (P : PencilData hC B k F) {x : G}
    (hx : x ∈ commSet D (hC.conj P.g).d) {u : Fin k ⊕ Fin k → F}
    (hv : (pencilCv P).vec x = u)
    (hu : spForm k F ((pencilCv P).vec hC.d) u ≠ 0) : ¬ Commute x hC.d := by
  intro hc
  apply hu
  have h0 : spForm k F ((pencilCv P).vec x) ((pencilCv P).vec hC.d) = 0 :=
    ((pencilCv P).commute_iff x hx hC.d (mem_commSet_symm hC.hd P.hv)).mp hc
  rw [hv] at h0
  have hsymm : spForm k F ((pencilCv P).vec hC.d) u =
      spForm k F u ((pencilCv P).vec hC.d) :=
    CFSG.RankThree.PartOne.OddIso.alt_comm spForm_isAlt _ _
  rw [hsymm]
  exact h0

private lemma kappa_pencil_coords (P : PencilData hC B k F) {β₁ β₂ s : F} {x₁ x₂ x_t : G}
    {b₁ b₂ t : F} {u₁ u₂ u_t : Fin k ⊕ Fin k → F}
    (hv₁ : (pencilCv P).vec x₁ = u₁) (hu₁ : spForm k F ((pencilCv P).vec hC.d) u₁ = b₁)
    (hβ₁ : P.σ b₁ = β₁)
    (hv₂ : (pencilCv P).vec x₂ = u₂) (hy₂ : spForm k F ((pencilCv P).vec hC.d) u₂ = b₂)
    (hβ₂ : P.σ b₂ = β₂)
    (hvt : (pencilCv P).vec x_t = u_t)
    (hyt : spForm k F ((pencilCv P).vec hC.d) u_t = (1 - t) * b₁ + t * b₂)
    (hσt : P.σ t = s) :
    secondCoord P x₁ = β₁ ∧ secondCoord P x₂ = β₂ ∧
      secondCoord P x_t = (1 - s) * β₁ + s * β₂ := by
  refine ⟨?_, ?_, ?_⟩
  · show (pencilVec P x₁).1.2 = β₁
    rw [snd_pencilVec P, hv₁, hu₁, hβ₁]
  · show (pencilVec P x₂).1.2 = β₂
    rw [snd_pencilVec P, hv₂, hy₂, hβ₂]
  · show (pencilVec P x_t).1.2 = (1 - s) * β₁ + s * β₂
    rw [snd_pencilVec P, hvt, hyt, map_add, map_mul, map_mul, map_sub, map_one,
      hβ₁, hβ₂, hσt]

private lemma kappa_pencil_notspan (P : PencilData hC B k F) {x₁ x₂ : G}
    {u₁ u₂ r : Fin k ⊕ Fin k → F} {b₁ b₂ : F}
    (hv₁ : (pencilCv P).vec x₁ = u₁) (hv₂ : (pencilCv P).vec x₂ = u₂)
    (hu₂ : u₂ = (b₂ / b₁) • u₁ + r)
    (hs₁ : P.σ.symm (secondCoord P x₁) = b₁)
    (hs₂ : P.σ.symm (secondCoord P x₂) = b₂)
    (hb₂ne : b₂ ≠ 0) (hrspany : r ∉ Submodule.span F {(pencilCv P).vec hC.d}) :
    (P.σ.symm (secondCoord P x₁))⁻¹ • (pencilCv P).vec x₁ +
      (P.σ.symm (secondCoord P x₂))⁻¹ • (pencilCv P).vec x₂ ∉
        Submodule.span F {(pencilCv P).vec hC.d} := by
  rw [hs₁, hs₂, hv₁, hv₂]
  have hcalc : b₁⁻¹ • u₁ + b₂⁻¹ • u₂ = b₂⁻¹ • r := by
    rw [hu₂, smul_add, smul_smul]
    have hcoef : b₂⁻¹ * (b₂ / b₁) = b₁⁻¹ := by
      rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hb₂ne, one_mul]
    rw [hcoef]
    rw [show b₁⁻¹ • u₁ + (b₁⁻¹ • u₁ + b₂⁻¹ • r) =
      (b₁⁻¹ • u₁ + b₁⁻¹ • u₁) + b₂⁻¹ • r by abel]
    rw [show b₁⁻¹ • u₁ + b₁⁻¹ • u₁ = 0 by
      rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul], zero_add]
  rw [hcalc]
  intro hmem
  apply hrspany
  have hr : r = b₂ • (b₂⁻¹ • r) := by rw [smul_smul, mul_inv_cancel₀ hb₂ne, one_smul]
  rw [hr]
  exact Submodule.smul_mem _ _ hmem

private lemma exists_pencil_vectors (P : PencilData hC B k F) {b₁ b₂ t : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hbt : (1 - t) * b₁ + t * b₂ ≠ 0) :
    ∃ (u₁ u₂ u_t r : Fin k ⊕ Fin k → F),
      spForm k F ((pencilCv P).vec hC.d) u₁ = b₁ ∧
      spForm k F ((pencilCv P).vec hC.d) u₂ = b₂ ∧
      spForm k F ((pencilCv P).vec hC.d) u_t = (1 - t) * b₁ + t * b₂ ∧
      spForm k F u₁ u₂ = 0 ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u_t ≠ 0 ∧
      u₂ = (b₂ / b₁) • u₁ + r ∧ u_t = (1 - t) • u₁ + t • u₂ ∧
      r ∉ Submodule.span F {u₁} ∧
      r ∉ Submodule.span F {(pencilCv P).vec hC.d} := by
  obtain ⟨u₁, hu₁⟩ := exists_spForm_vec_conj_eq_any P b₁
  have hu₁ne : spForm k F ((pencilCv P).vec hC.d) u₁ ≠ 0 := by rw [hu₁]; exact hb₁
  obtain ⟨r, hyr, hu₁r, hrspan₁, hrspany⟩ := exists_orthogonal_notMem P hu₁ne
  set u₂ : Fin k ⊕ Fin k → F := (b₂ / b₁) • u₁ + r with hu₂
  set u_t : Fin k ⊕ Fin k → F := (1 - t) • u₁ + t • u₂ with hut
  have hy₂ : spForm k F ((pencilCv P).vec hC.d) u₂ = b₂ := by
    rw [hu₂, map_add, LinearMap.map_smul, smul_eq_mul, hu₁, hyr, add_zero,
      div_mul_cancel₀ b₂ hb₁]
  have hu₁₂ : spForm k F u₁ u₂ = 0 := by
    rw [hu₂, map_add, LinearMap.map_smul, smul_eq_mul,
      (spForm_isAlt (r := k) (K := F)).self_eq_zero, mul_zero, hu₁r, add_zero]
  have hyt : spForm k F ((pencilCv P).vec hC.d) u_t = (1 - t) * b₁ + t * b₂ := by
    rw [hut, map_add, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
      hu₁, hy₂]
  have hu₁0 : u₁ ≠ 0 := by
    intro h0
    exact hb₁ (by rw [← hu₁, h0, map_zero])
  have hu₂ne : u₂ ≠ 0 := by
    intro h0
    exact hb₂ (by rw [← hy₂, h0, map_zero])
  have hutne : u_t ≠ 0 := by
    intro h0
    exact hbt (by rw [← hyt, h0, map_zero])
  exact ⟨u₁, u₂, u_t, r, hu₁, hy₂, hyt, hu₁₂, hu₁0, hu₂ne, hutne, hu₂, hut,
    hrspan₁, hrspany⟩

private lemma exists_pencil_points (P : PencilData hC B k F) {u₁ u₂ u_t : Fin k ⊕ Fin k → F}
    {b₁ b₂ t : F} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hut : u_t ≠ 0)
    (hu₁₂ : spForm k F u₁ u₂ = 0)
    (hb₁ : spForm k F ((pencilCv P).vec hC.d) u₁ = b₁) (hb₁ne : b₁ ≠ 0)
    (hb₂ : spForm k F ((pencilCv P).vec hC.d) u₂ = b₂) (hb₂ne : b₂ ≠ 0)
    (hbt : (1 - t) * b₁ + t * b₂ ≠ 0)
    (hyt : spForm k F ((pencilCv P).vec hC.d) u_t = (1 - t) * b₁ + t * b₂)
    (hut' : u_t = (1 - t) • u₁ + t • u₂) :
    ∃ (x₁ x₂ x_t : G) (_ : x₁ ∈ commSet D (hC.conj P.g).d)
      (_ : ¬ Commute x₁ hC.d) (_ : x₂ ∈ commSet D (hC.conj P.g).d)
      (_ : ¬ Commute x₂ hC.d) (_ : x_t ∈ commSet D (hC.conj P.g).d)
      (_ : ¬ Commute x_t hC.d),
      (pencilCv P).vec x₁ = u₁ ∧ (pencilCv P).vec x₂ = u₂ ∧
      (pencilCv P).vec x_t = u_t ∧ Commute x₁ x₂ ∧ x_t ∈ lineMem D x₁ x₂ ∧
      (pencilCv P).vec x_t = (1 - t) • (pencilCv P).vec x₁ + t • (pencilCv P).vec x₂ := by
  obtain ⟨x₁, hx₁, hv₁⟩ := (pencilCv P).exists_vec u₁ hu₁
  obtain ⟨x₂, hx₂, hv₂⟩ := (pencilCv P).exists_vec u₂ hu₂
  obtain ⟨x_t, hx_t, hvt⟩ := (pencilCv P).exists_vec u_t hut
  have hxd₁ : ¬ Commute x₁ hC.d :=
    not_commute_d_of_spForm_ne_zero P hx₁ hv₁ (by rw [hb₁]; exact hb₁ne)
  have hxd₂ : ¬ Commute x₂ hC.d :=
    not_commute_d_of_spForm_ne_zero P hx₂ hv₂ (by rw [hb₂]; exact hb₂ne)
  have hxd_t : ¬ Commute x_t hC.d :=
    not_commute_d_of_spForm_ne_zero P hx_t hvt (by rw [hyt]; exact hbt)
  have hcomm : Commute x₁ x₂ :=
    ((pencilCv P).commute_iff x₁ hx₁ x₂ hx₂).mpr (by rw [hv₁, hv₂]; exact hu₁₂)
  have hvec : (pencilCv P).vec x_t =
      (1 - t) • (pencilCv P).vec x₁ + t • (pencilCv P).vec x₂ := by
    rw [hvt, hv₁, hv₂, hut']
  have hline : x_t ∈ lineMem D x₁ x₂ :=
    mem_lineMem_of_vec_pencil P.hnk P.hF P.g (pencilCv P) hx₁ hx₂ hx_t hcomm hvec
  exact ⟨x₁, x₂, x_t, hx₁, hxd₁, hx₂, hxd₂, hx_t, hxd_t, hv₁, hv₂, hvt, hcomm, hline, hvec⟩

private lemma kappa_pencil (P : PencilData hC B k F) {β₁ β₂ s : F}
    (hβ₁ne0 : β₁ ≠ 0) (hβ₂ne0 : β₂ ≠ 0) (ht : (1 - s) * β₁ + s * β₂ ≠ 0) :
    ((1 - s) * β₁ + s * β₂) * kappa P ((1 - s) * β₁ + s * β₂) =
      (1 - s) * (β₁ * kappa P β₁) + s * (β₂ * kappa P β₂) := by
  classical
  set b₁ : F := P.σ.symm β₁ with hb₁
  set b₂ : F := P.σ.symm β₂ with hb₂
  set t : F := P.σ.symm s with htm
  have hβ₁ : P.σ b₁ = β₁ := by rw [hb₁]; exact P.σ.apply_symm_apply β₁
  have hβ₂ : P.σ b₂ = β₂ := by rw [hb₂]; exact P.σ.apply_symm_apply β₂
  have hσt : P.σ t = s := by rw [htm]; exact P.σ.apply_symm_apply s
  have hb₁ne : b₁ ≠ 0 := by
    intro h0
    exact hβ₁ne0 (by rw [← hβ₁, h0, map_zero])
  have hb₂ne : b₂ ≠ 0 := by
    intro h0
    exact hβ₂ne0 (by rw [← hβ₂, h0, map_zero])
  have hbtne : (1 - t) * b₁ + t * b₂ ≠ 0 := by
    intro h0
    apply ht
    have h := congrArg P.σ h0
    rw [map_add, map_mul, map_mul, map_sub, map_one, hβ₁, hβ₂, hσt, map_zero] at h
    exact h
  obtain ⟨u₁, u₂, u_t, r, hu₁, hy₂, hyt, hu₁₂, hu₁0, hu₂ne, hutne, hu₂, hut,
    hrspan₁, hrspany⟩ := exists_pencil_vectors P hb₁ne hb₂ne hbtne
  obtain ⟨x₁, x₂, x_t, hx₁, hxd₁, hx₂, hxd₂, hx_t, hxd_t, hv₁, hv₂, hvt, hcomm, hline,
    hvec⟩ := exists_pencil_points P hu₁0 hu₂ne hutne hu₁₂ hu₁ hb₁ne hy₂ hb₂ne hbtne hyt hut
  obtain ⟨hβ₁', hβ₂', hβt'⟩ :=
    kappa_pencil_coords P hv₁ hu₁ hβ₁ hv₂ hy₂ hβ₂ hvt hyt hσt
  have hnotspan := kappa_pencil_notspan P hv₁ hv₂ hu₂ (by rw [hβ₁', hb₁])
    (by rw [hβ₂', hb₂]) hb₂ne hrspany
  have hp := lineParam_add P hx₁ hxd₁ hx₂ hxd₂ hx_t hxd_t hcomm hvec hnotspan hline
  have hk₁ : lineParam P x₁ hx₁ hxd₁ = kappa P β₁ := by
    rw [← kappa_apply P hx₁ hxd₁, hv₁, hu₁, hβ₁]
  have hk₂ : lineParam P x₂ hx₂ hxd₂ = kappa P β₂ := by
    rw [← kappa_apply P hx₂ hxd₂, hv₂, hy₂, hβ₂]
  have hkt : lineParam P x_t hx_t hxd_t = kappa P ((1 - s) * β₁ + s * β₂) := by
    rw [← kappa_apply P hx_t hxd_t, hvt, hyt, map_add, map_mul, map_mul, map_sub, map_one,
      hβ₁, hβ₂, hσt]
  rw [hβ₁', hβ₂', hβt', hk₁, hk₂, hkt, hσt] at hp
  exact hp

private lemma exists_kappa_const (P : PencilData hC B k F) :
    ∃ A₀ ∈ (artinSchreierHom (K := F)).range, ∀ β : F, β ≠ 0 → kappa P β = A₀ := by
  have hk : 2 < Fintype.card F := (B.two_lt_card P.hF).trans_eq Nat.card_eq_fintype_card
  obtain ⟨A, B, hAB⟩ := exists_affine_of_pencil (K := F) (fun β => β * kappa P β)
    (fun b c t hb hc ht => kappa_pencil P hb hc ht)
  have hmem : ∀ β : F, β ≠ 0 → A + B / β ∈ (artinSchreierHom (K := F)).range := by
    intro β hβ
    have hbne : P.σ.symm β ≠ 0 := by
      intro h0
      apply hβ
      rw [← P.σ.apply_symm_apply β, h0, map_zero]
    obtain ⟨x, hx, hxd, hsp⟩ := exists_spForm_vec_conj_eq P (b := P.σ.symm β) hbne
    have hβeq : P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x)) = β := by
      rw [hsp, P.σ.apply_symm_apply]
    have hκ : kappa P β = lineParam P x hx hxd := by
      rw [← hβeq]
      exact kappa_apply P hx hxd
    have hφ : β * lineParam P x hx hxd = A * β + B := by
      rw [← hκ]
      exact hAB β hβ
    have hlin : lineParam P x hx hxd = A + B / β := by
      rw [show A + B / β = (A * β + B) / β by field_simp, ← hφ]
      field_simp
    rw [← hlin]
    exact lineParam_mem_range P hx hxd
  have hB0 : B = 0 := eq_zero_of_forall_add_div_mem_range hk hmem
  have hA : ∀ β : F, β ≠ 0 → kappa P β = A := by
    intro β hβ
    have h := hAB β hβ
    rw [hB0, add_zero, mul_comm A β] at h
    exact mul_left_cancel₀ hβ h
  have hone : P.σ.symm (1 : F) ≠ 0 := by
    intro h0
    have h := congrArg P.σ h0
    rw [P.σ.apply_symm_apply, map_zero] at h
    exact one_ne_zero h
  obtain ⟨x, hx, hxd, hsp⟩ := exists_spForm_vec_conj_eq P (b := P.σ.symm 1) hone
  have hβeq : P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x)) = 1 := by
    rw [hsp, P.σ.apply_symm_apply]
  refine ⟨A, ?_, hA⟩
  rw [← hA 1 one_ne_zero]
  rw [show kappa P 1 = lineParam P x hx hxd from by
    rw [← hβeq]
    exact kappa_apply P hx hxd]
  exact lineParam_mem_range P hx hxd

omit [DecidableEq F] [CharP F 2] in
private lemma bijective_of_additive_of_spForm {σ : F ≃+* F}
    {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    (hAadd : ∀ x z, A (x + z) = A x + A z)
    (hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z)) :
    Function.Bijective A := by
  have hA0 : A 0 = 0 := map_zero (AddMonoidHom.mk' A hAadd)
  refine Finite.injective_iff_bijective.mp ?_
  intro x z hxz
  have hneg : A (-z) = -A z := by
    have h := hAadd z (-z)
    rw [add_neg_cancel, hA0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hsub : A (x - z) = 0 := by
    rw [sub_eq_add_neg, hAadd x (-z), hneg, hxz, add_neg_cancel]
  have hperp : ∀ w, spForm k F (x - z) w = 0 := by
    intro w
    have h := hAform (x - z) w
    have h' : (0 : F) = σ (spForm k F (x - z) w) := by simpa [hsub] using h
    exact σ.injective (h'.symm.trans (map_zero σ).symm)
  exact sub_eq_zero.mp (spForm_nondegenerate.1 (x - z) hperp)

omit [DecidableEq F] in
private lemma gamma_lift_eq_mU_of_psi (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X)
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
      (ψ₁ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψz : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
        mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))) :
    γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec hC.d))) = mU := by
  have hz : hC.d ∈ commSet D (hC.conj g).d := mem_commSet_symm hC.hd hv
  have hψd : (ψ₁ ⟨hC.d, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ :
      MGroup Q₀) = mRefl Q₀ mU := by
    rw [hψθ ⟨hC.d, hu⟩ (mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz), hθ.2.1]
  have hEq : mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec hC.d)))) =
      mRefl Q₀ mU := by
    rw [← hψz hC.d hz, hψd]
  exact (reflect_eq_reflect_iff (nondegenerate_polarBilin_mForm hQ₀)
    (by rw [hγ]; exact mForm_mLift (Q₀ := Q₀) _) mForm_mU).mp (by
      simpa [mRefl] using congrArg Subtype.val hEq)

omit [Finite G] [DecidableEq F] in
private lemma ne_zero_of_gamma_lift_eq_mU (c : SpChart hC B.hα k F)
    {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F} {w : Fin k ⊕ Fin k → F} {g : G}
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (hγU : γ mU = mLift Q₀ (c.vec (hC.conj g).d))
    (hγw : γ (mLift Q₀ w) = mU) : w ≠ 0 := by
  intro hw
  have hγmU : γ mU = mU := by
    rw [hw, mLift_zero] at hγw
    exact hγw
  have hlift : mLift Q₀ (c.vec (hC.conj g).d) = mLift Q₀ (0 : Fin k ⊕ Fin k → F) := by
    rw [mLift_zero, ← hγU]
    exact hγmU
  exact c.vec_ne_zero (hC.conj g).d hv (by
    simpa [mLift] using congrArg (fun Y : MSpace k F => Y.2) hlift)

private noncomputable abbrev pencilDataOf (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (hQ₀ty : ∃ w₀ : G, w₀ ∈ D ∧ (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1 ∧
      IsFormOfLine c Q₀ w₀)
    {σ : F ≃+* F} {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hAadd : ∀ x z, A (x + z) = A x + A z)
    (hAsmul : ∀ (t : F) x, A (t • x) = σ t • A x)
    (hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z))
    (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X) (hγU : γ mU = mLift Q₀ (c.vec (hC.conj g).d))
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
      (ψ₁ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψz : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
        mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))) :
    PencilData hC B k F :=
  let y' : Fin k ⊕ Fin k → F := A ((SpChart.conj (B := B) c g).vec hC.d)
  { c := c, hnk := hnk, hF := hF, Q₀ := Q₀, hQ₀ := hQ₀, hu := hu, θ := θ, hθ := hθ
    g := g, hv := hv, hQ₀ty := hQ₀ty, σ := σ, A := A, γ := γ, y' := y'
    ψ₁ := ψ₁, hA := bijective_of_additive_of_spForm hAadd hAform
    hAadd := hAadd, hAsmul := hAsmul, hAform := hAform, hγ := hγ, hγU := hγU
    hγy' := gamma_lift_eq_mU_of_psi (B := B) c hQ₀ hθ hv hγ hψθ hψz
    hy' := ne_zero_of_gamma_lift_eq_mU (B := B) c hv hγU
      (gamma_lift_eq_mU_of_psi (B := B) c hQ₀ hθ hv hγ hψθ hψz)
    hAy := rfl, hψθ := hψθ, hψz := hψz }

theorem exists_formOfLine_eq_mStabForm_add_sq (c : SpChart hC B.hα k F) (hnk : B.n = 2 * k)
    (hF : Nat.card F = 2 ^ B.f) {Q₀ : QuadraticForm F (Fin k ⊕ Fin k → F)}
    (hQ₀ : ∀ a b, polar Q₀ a b = spForm k F a b)
    {hu : hC.d ∈ Halpha D hC.alpha}
    {θ : ↥(Halpha D hC.alpha) ≃* ↥(Subgroup.centralizer {mRefl Q₀ mU})}
    (hθ : IsBasePointIdentification (hα := B.hα) c hu θ) (g : G)
    (hv : (hC.conj g).d ∈ commSet D hC.d)
    (hQ₀ty : ∃ w₀ : G, w₀ ∈ D ∧ (lineMem D hC.d w₀).ncard = 2 ^ B.f - 1 ∧
      IsFormOfLine c Q₀ w₀)
    {σ : F ≃+* F} {A : (Fin k ⊕ Fin k → F) → (Fin k ⊕ Fin k → F)}
    {γ : MSpace k F ≃ₗ[F] MSpace k F}
    {ψ₁ : ↥(Halpha D (hC.conj g).alpha) ≃*
      ↥(Subgroup.centralizer {mRefl Q₀ (mLift Q₀ (c.vec (hC.conj g).d))})}
    (hAadd : ∀ x z, A (x + z) = A x + A z)
    (hAsmul : ∀ (t : F) x, A (t • x) = σ t • A x)
    (hAform : ∀ x z, spForm k F (A x) (A z) = σ (spForm k F x z))
    (hγ : ∀ X, mForm Q₀ (γ X) = mForm Q₀ X) (hγU : γ mU = mLift Q₀ (c.vec (hC.conj g).d))
    (hψθ : ∀ (r : ↥(Halpha D hC.alpha)), ∀ hr : (r : G) ∈ Halpha D (hC.conj g).alpha,
      (ψ₁ ⟨r, hr⟩ : MGroup Q₀) = (θ r : MGroup Q₀))
    (hψz : ∀ z, ∀ hz : z ∈ commSet D (hC.conj g).d,
      (ψ₁ ⟨z, mem_Halpha_of_mem_commSet (hC.conj g) (B.conj g).hα hz⟩ : MGroup Q₀) =
        mRefl Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec z))))) :
    ∃ A₀ ∈ (artinSchreierHom (K := F)).range, ∀ x ∈ commSet D (hC.conj g).d,
      ¬ Commute x hC.d → ∀ Q : QuadraticForm F (Fin k ⊕ Fin k → F), IsFormOfLine c Q x →
        ∀ a, Q a = mStabForm Q₀ (γ (mLift Q₀ (A ((SpChart.conj (B := B) c g).vec x)))) a +
          (A₀ * spForm k F (c.vec (hC.conj g).d) a) ^ 2 := by
  let P : PencilData hC B k F :=
    pencilDataOf c hnk hF hQ₀ (hu := hu) (θ := θ) hθ g hv hQ₀ty (σ := σ) (A := A)
      (γ := γ) (ψ₁ := ψ₁) hAadd hAsmul hAform hγ hγU hψθ hψz
  obtain ⟨A₀, hA₀, hconst⟩ := exists_kappa_const P
  refine ⟨A₀, hA₀, ?_⟩
  intro x hx hxd Q hQ a
  have hQeq : Q = P.lineForm x hx hxd :=
    eq_of_isFormOfLine (B.two_lt_card P.hF) hQ (lineForm_isFormOfLine P x hx hxd)
  have hβne : P.σ (spForm k F ((pencilCv P).vec hC.d) ((pencilCv P).vec x)) ≠ 0 := by
    intro h0
    exact spForm_vec_conj_ne_zero P hx hxd (P.σ.injective (by simpa using h0))
  have hlp : lineParam P x hx hxd = A₀ := by
    rw [← kappa_apply P hx hxd]
    exact hconst _ hβne
  rw [hQeq, lineParam_spec P x hx hxd a, hlp]

end CFSG.OddTranspositions.PartThree.ElevenSp

end
