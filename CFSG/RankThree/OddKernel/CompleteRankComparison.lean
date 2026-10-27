module

public import CFSG.RankThree.OddKernel.CompositionFactors
public import CFSG.RankThree.OddKernel.ThreeDimCentralCover
public import CFSG.RankThree.OddKernel.FixedPlaneKernel
public import CFSG.RankThree.CentralExtension.MinimalCoverFrattini

public section

namespace CFSG.RankThree.OddKernel

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm Module
open CFSG.Assembly.RankThreeEven (localRank)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

section Linear

variable {p : ℕ} [hp : Fact p.Prime]

@[expose] noncomputable def linAction {Y W : Type*} [Group Y] [Group W] {n : ℕ}
    (e : W ≃* Multiplicative (Fin n → ZMod p)) (β : Y →* MulAut W) :
    Y →* ((Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) where
  toFun y := LinearEquiv.ofLinearMap (coordLin e (β y)) (coordLin e (β y⁻¹))
    (by rw [← coordLin_mul, ← map_mul, mul_inv_cancel, map_one, coordLin_one])
    (by rw [← coordLin_mul, ← map_mul, inv_mul_cancel, map_one, coordLin_one])
  map_one' := LinearEquiv.ext fun v => by
    change coordLin e (β 1) v = v
    rw [map_one, coordLin_one, LinearMap.id_apply]
  map_mul' x y := LinearEquiv.ext fun v => by
    change coordLin e (β (x * y)) v = coordLin e (β x) (coordLin e (β y) v)
    rw [map_mul, coordLin_mul, LinearMap.comp_apply]

theorem linAction_toLinearMap {Y W : Type*} [Group Y] [Group W] {n : ℕ}
    (e : W ≃* Multiplicative (Fin n → ZMod p)) (β : Y →* MulAut W) (y : Y) :
    (linAction e β y).toLinearMap = coordLin e (β y) := rfl

theorem exists_frattini_coordinates {Y : Type*} [Group Y] (P : Subgroup Y) [P.Normal]
    (D : Subgroup P) [D.Characteristic] [(D.map P.subtype).Normal] {n : ℕ}
    (e : D ⧸ frattini D ≃* Multiplicative (Fin n → ZMod p)) :
    ∃ π : D.map P.subtype →* Multiplicative (Fin n → ZMod p), Function.Surjective π ∧
      π.ker = frattini (D.map P.subtype) ∧
      ∀ (y : Y) (d : D.map P.subtype), π (MulAut.conjNormal y d) =
        Multiplicative.ofAdd (linAction e (frattiniConjAction P D) y
          (Multiplicative.toAdd (π d))) := by
  let ι : D ≃* D.map P.subtype := D.equivMapOfInjective P.subtype P.subtype_injective
  let π : D.map P.subtype →* Multiplicative (Fin n → ZMod p) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (frattini D)).comp ι.symm.toMonoidHom)
  have hιs : ∀ x : D.map P.subtype, (((ι.symm x : D) : P) : Y) = x := fun x => by
    have h := congrArg Subtype.val (ι.apply_symm_apply x)
    exact h
  refine ⟨π, fun v => ?_, ?_, fun y d => ?_⟩
  · obtain ⟨q, rfl⟩ := e.surjective v
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (frattini D) q
    exact ⟨ι d, by simp [π]⟩
  · ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (frattini D) (ι.symm x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h1 := frattini_le_comap_frattini_of_surjective (φ := ι.toMonoidHom) ι.surjective h
      rw [mem_comap] at h1
      simpa using h1
    · intro h
      exact frattini_le_comap_frattini_of_surjective (φ := ι.symm.toMonoidHom)
        ι.symm.surjective h
  · have hconj : ι.symm (MulAut.conjNormal y d) =
        MulAut.characteristic D (MulAut.conjNormal (H := P) y) (ι.symm d) := by
      apply Subtype.ext
      apply Subtype.ext
      rw [hιs, MulAut.conjNormal_apply, (frattiniConjAction_mk P D y (ι.symm d)).2, hιs]
    change e (QuotientGroup.mk' (frattini D) (ι.symm (MulAut.conjNormal y d))) =
      Multiplicative.ofAdd (coordLin e (frattiniConjAction P D y)
        (Multiplicative.toAdd (e (QuotientGroup.mk' (frattini D) (ι.symm d)))))
    rw [coordLin_apply, ofAdd_toAdd, hconj]
    rfl

theorem exists_dim_pair (hp2 : p ≠ 2) {W : Type*} [Group W] [Finite W]
    (hWcomm : ∀ x y : W, x * y = y * x) (hWpow : ∀ x : W, x ^ p = 1)
    {R : Subgroup (MulAut W)} {c : ℕ} (hc : c = 1 ∨ c = 2)
    (hcR : ∀ r : R, orderOf r = 2 → Nat.card {w : W // (r : MulAut W) w = w} = p ^ c)
    (h2 : 2 ≤ pRank 2 R) :
    ∃ n : ℕ, ((n, c) = (3, 1) ∨ (n, c) = (4, 2) ∨ (n, c) = (6, 2)) ∧ Nat.card W = p ^ n := by
  classical
  have : Finite R := Subtype.finite
  rw [pRank_eq_open_pRank_top] at h2
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2)
    (⊤ : Subgroup R)
  have hE4 : 4 ≤ Nat.card E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup R) := Nat.pow_le_pow_right (by norm_num) h2
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1} : Finset E)) (by
      rw [Finset.card_univ, Finset.card_singleton, ← Nat.card_eq_fintype_card]; omega)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card (t := Finset.univ)
    (s := ({1, a} : Finset E)) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb
  obtain ⟨hb1, hba⟩ := hb
  have hEc := hE.1
  have hsq : ∀ x : E, x * x = 1 := fun x => Subtype.ext (by
    rw [← sq]
    exact hE.2 x x.2)
  have hab1 : a * b ≠ 1 := fun h => hba (by
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a)
    rw [← hainv]
    exact eq_inv_of_mul_eq_one_right h)
  have hord : ∀ x : E, x ≠ 1 → orderOf ((x : R)) = 2 := fun x hx =>
    orderOf_eq_prime (by rw [sq]; exact congrArg Subtype.val (hsq x))
      (fun h => hx (Subtype.ext h))
  have hcoe : ∀ x y : E,
      (((x * y : E) : R) : MulAut W) = ((x : R) : MulAut W) * ((y : R) : MulAut W) :=
    fun _ _ => rfl
  have hσ : ((a : R) : MulAut W) * ((a : R) : MulAut W) = 1 := by rw [← hcoe, hsq]; rfl
  have hτ : ((b : R) : MulAut W) * ((b : R) : MulAut W) = 1 := by rw [← hcoe, hsq]; rfl
  have hστ : ((a : R) : MulAut W) * ((b : R) : MulAut W) =
      ((b : R) : MulAut W) * ((a : R) : MulAut W) := by
    rw [← hcoe, ← hcoe, mul_comm' a b]
  have hσ1 : ((a : R) : MulAut W) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
  have hcσ := hcR (a : R) (hord a ha)
  have hcτ := hcR (b : R) (hord b hb1)
  have hcστ := hcR ((a * b : E) : R) (hord (a * b) hab1)
  rw [hcoe] at hcστ
  obtain ⟨d₀, d, hsum, hd, hcard, -⟩ := four_group_weights hp2 hWcomm hWpow hσ hτ hστ hσ1 hcσ hcτ
    hcστ
  refine ⟨d₀ + 3 * d, ?_, hcard⟩
  simp only [Prod.mk.injEq]
  omega

theorem orderOf_rangeRestrict_eq_two {Y M : Type*} [Group Y] [Group M] (β : Y →* M)
    (hodd : Odd (Nat.card β.ker)) {t : Y} (ht : orderOf t = 2) :
    orderOf (β.rangeRestrict t) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime (by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]) fun h => ?_
  have htK : t ∈ β.ker := by
    rw [← MonoidHom.ker_rangeRestrict]
    exact h
  have hdvd : orderOf t ∣ Nat.card β.ker := by
    have := Subgroup.orderOf_dvd_natCard β.ker htK
    exact this
  rw [ht] at hdvd
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem exists_central_quotient_map {Y E : Type*} [Group Y] [Group E] (P : Subgroup Y)
    [P.Normal] (f : Y →* E) (hf : Function.Surjective f) (hAP : f.ker ≤ P)
    (hpre : (center E).comap f = P) :
    ∃ π : E →* Y ⧸ P, Function.Surjective π ∧ π.ker = center E ∧
      ∀ y, π (f y) = QuotientGroup.mk y := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let q : Y ⧸ f.ker →* Y ⧸ P := QuotientGroup.map f.ker P (MonoidHom.id Y) (by
    rw [comap_id]
    exact hAP)
  let π : E →* Y ⧸ P := q.comp e.symm.toMonoidHom
  have hπf : ∀ y, π (f y) = QuotientGroup.mk y := fun y => by
    change q (e.symm (f y)) = _
    have h : e.symm (f y) = QuotientGroup.mk y := e.symm_apply_eq.2 rfl
    rw [h]
    rfl
  refine ⟨π, fun z => ?_, ?_, hπf⟩
  · obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨f y, hπf y⟩
  · ext x
    obtain ⟨y, rfl⟩ := hf x
    rw [MonoidHom.mem_ker, hπf, QuotientGroup.eq_one_iff, ← hpre, mem_comap]

theorem complete_rank_three_dim_case (hp3 : 3 < p) {Y E : Type*} [Group Y] [Finite Y] [Group E]
    [Finite E] [Group.IsPerfect E] (P : Subgroup Y) [P.Normal] [IsSimpleGroup (Y ⧸ P)]
    (hnab : ∃ a b : Y ⧸ P, a * b ≠ b * a) (f : Y →* E) (hf : Function.Surjective f)
    (hAP : f.ker ≤ P) (hZE : IsPGroup p (center E)) (hpre : (center E).comap f = P)
    {X : Type*} [AddCommGroup X] [Module (ZMod p) X] (hX : finrank (ZMod p) X = 3)
    (ι : Y ⧸ P →* (X ≃ₗ[ZMod p] X)) (hι : Function.Injective ι)
    (hirr : ∀ Z : Submodule (ZMod p) X, (∀ s, ∀ v ∈ Z, ι s v ∈ Z) → Z = ⊥ ∨ Z = ⊤) :
    pRank p E ≤ 2 ∧ localRank p E ≤ 2 := by
  obtain ⟨π, hπ, hker, -⟩ := exists_central_quotient_map P f hf hAP hpre
  obtain ⟨-, hrank, -⟩ := prime_three_dimensional_simple_module_central_cover hp3 hnab hX ι hι hirr
    π hπ (hker ▸ le_rfl) (hker ▸ hZE)
  refine ⟨hrank, ?_⟩
  have h := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_pRank p hp.out E
  refine h.trans ?_
  change CFSG.Open.pRank p (⊤ : Subgroup E) ≤ 2
  rw [← pRank_eq_open_pRank_top]
  exact hrank

theorem frattini_dim_eq_three (hp2 : p ≠ 2) {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal] (hP : IsPGroup p P)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤)
    (D : Subgroup P) [D.Characteristic] (hexp : Monoid.exponent D = p)
    (hDZ : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ centralizer (D : Set P)) (hrank : pRank p Y ≤ 3)
    {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 6) (hcard : Nat.card (D ⧸ frattini D) = p ^ n) :
    n = 3 := by
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hexp' : ∀ x : D, x ^ p = 1 := fun x => hexp ▸ Monoid.pow_exponent_eq_one x
  have hclass : commutator D ≤ center D := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    have h := hDZ (commutator_mem_commutator a.2 (mem_top (b : P)))
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    exact mem_centralizer_iff.1 h.2 g g.2
  have hfc : frattini D = commutator D :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hexp'
  have hDrank : pRank p D ≤ 3 := by
    refine le_trans ?_ hrank
    rw [pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact pRank_top_le_of_injective hp.out.one_lt (P.subtype.comp D.subtype)
      (P.subtype_injective.comp D.subtype_injective)
  obtain ⟨h1, h2, h3⟩ :=
    CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hexp' hclass
  have hW := (frattini_quotient_elementary hDp).2
  have hWn : pRank p (D ⧸ frattini D) = n :=
    CFSG.RankThree.PartTwo.pRank_eq_of_isMulCommutative hp.out hW.2 ⟨⟨hW.1⟩⟩ hcard
  have hrankq : pRank p (D ⧸ commutator D) = n := by
    rw [← hWn, pRank_eq_open_pRank_top, pRank_eq_open_pRank_top]
    exact (pRank_top_eq_of_mulEquiv hp.out.one_lt (QuotientGroup.quotientMulEquivOfEq hfc)).symm
  have hn4 : n ≤ 4 := hrankq ▸ h3 hDrank
  rcases hn with h | h | h
  · exact h
  · exfalso
    subst h
    have hD3 : pRank p D = 3 := by
      by_contra hne
      have := h1 (by omega)
      omega
    obtain ⟨i, hi, -⟩ := h2 hD3
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      omega
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hi
      obtain ⟨-, hZcard, hZ, -⟩ := hi
      apply CentralExtension.perfect_minimal_cover_excludes_extraspecial_frattini_subgroup hp2 P
        hmin
      let φ : D ≃* D.map P.subtype := D.equivMapOfInjective P.subtype P.subtype_injective
      have hcomm : commutator (D.map P.subtype) = (commutator D).map φ.toMonoidHom := by
        rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
          map_top_of_surjective _ φ.surjective]
      refine ⟨D.map P.subtype, ConjAct.normal_of_characteristic_of_normal, map_subtype_le _,
        ?_, ?_, ?_⟩
      · rintro _ ⟨d, hd, rfl⟩
        have h := congrArg (fun x : D => ((x : P) : Y)) (hexp' ⟨d, hd⟩)
        simpa using h
      · rw [← map_center_eq φ, hcomm, hZ]
        rfl
      · rw [← map_center_eq φ]
        change Nat.card ((center D).map φ.toMonoidHom) = p
        rw [card_map_of_injective φ.injective, hZcard]
    · simp only [Fin.reduceFinMk, Matrix.cons_val] at hi
      omega
  · omega

theorem pRank_two_le_of_central_cover {Y E : Type*} [Group Y] [Finite Y] [Group E] [Finite E]
    (hp2 : p ≠ 2) (P : Subgroup Y) [P.Normal] (f : Y →* E) (hf : Function.Surjective f)
    (hAP : f.ker ≤ P) (hZE : IsPGroup p (center E)) (hpre : (center E).comap f = P)
    (hS2 : pRank 2 (Y ⧸ P) = 2) : pRank 2 E ≤ 2 := by
  obtain ⟨π, hπ, hker, -⟩ := exists_central_quotient_map P f hf hAP hpre
  have hodd : Odd (Nat.card (center E)) := by
    obtain ⟨k, hk⟩ := hZE.exists_card_eq
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  have e1 : E ⧸ center E ≃* Y ⧸ P :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  rw [← pRank_two_quotient_eq (center E) hodd, pRank_eq_open_pRank_top,
    pRank_top_eq_of_mulEquiv (by norm_num) e1, ← pRank_eq_open_pRank_top, hS2]

theorem noncentral_odd_prime_kernel_complete_rank_comparison (hp3 : 3 < p) {Y : Type u}
    [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal] (hP : IsPGroup p P)
    (hP1 : P ≠ ⊥) (hE : CFSG.layer (Y ⧸ P) = ⊤) (hZ : center (Y ⧸ P) = ⊥)
    (hYP : ⁅(⊤ : Subgroup Y), P⁆ ≠ ⊥) (hloc : localRank p Y ≤ 2) {E : Type u} [Group E]
    [Finite E] [Group.IsPerfect E] (f : Y →* E) (hf : Function.Surjective f)
    (hAP : f.ker ≤ P) (hZE : IsPGroup p (center E)) (hpre : (center E).comap f = P)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤) :
    localRank p E ≤ 2 ∧ (pRank p Y ≤ 3 → pRank p E ≤ 2) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk]
    exact (hp.out.odd_of_ne_two hp2).pow
  have hWM := noncentral_odd_prime_kernel_critical_weight_models hp3 P hP hP1 hE hZ hYP hloc
  obtain ⟨D, hDc, -, hexp, hDZ, -, hKP, hSs, hSnab, hS2, -, -, -, -, hiso, -, ⟨c, hc, hcR⟩,
    -⟩ := hWM
  have hY2 := (noncentral_odd_prime_kernel_two_rank_exactly_two hp3 P hP hP1 hE hZ hYP
    hloc).2.2.2.1
  have := hSs
  have hDp : IsPGroup p D := hP.to_subgroup D
  obtain ⟨-, hWc, hWp⟩ := frattini_quotient_elementary hDp
  have hR2 : 2 ≤ pRank 2 (frattiniConjAction P D).range := by
    obtain ⟨hBn, eR, -⟩ := hiso
    have hBodd : Odd (Nat.card (P.map (frattiniConjAction P D).rangeRestrict)) :=
      Odd.of_dvd_nat hPodd (Subgroup.card_map_dvd P _)
    rw [← pRank_two_quotient_eq _ hBodd, pRank_eq_open_pRank_top,
      pRank_top_eq_of_mulEquiv (by norm_num) eR, ← pRank_eq_open_pRank_top, hS2]
  obtain ⟨n, hnc, hWn⟩ := exists_dim_pair hp2 hWc hWp hc hcR hR2
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWc hWp hWn
  have hKodd : Odd (Nat.card (frattiniConjAction P D).ker) :=
    Odd.of_dvd_nat hPodd (Subgroup.card_dvd_of_le hKP)
  have hfixc : ∀ t : Y, orderOf t = 2 →
      finrank (ZMod p) (fixSpace (linAction e (frattiniConjAction P D) t).toLinearMap) = c := by
    intro t ht
    have h1 := hcR _ (orderOf_rangeRestrict_eq_two _ hKodd ht)
    have h2 := card_fixed_eq_pow e (frattiniConjAction P D t)
    change Nat.card {w // frattiniConjAction P D t w = w} = p ^ c at h1
    rw [h1] at h2
    rw [linAction_toLinearMap]
    exact (Nat.pow_right_injective hp.out.two_le h2).symm
  have hconj : ∀ s s' : Y ⧸ P, orderOf s = 2 → orderOf s' = 2 → IsConj s s' := by
    have h2 : CFSG.Assembly.twoRank (Y ⧸ P) = 2 := by
      change CFSG.Open.pRank 2 (⊤ : Subgroup (Y ⧸ P)) = 2
      rw [← pRank_eq_open_pRank_top]
      exact hS2
    obtain ⟨z, -, hz⟩ := CFSG.RankTwoShapes.rank_two_simple_involutions_conjugate hSnab h2
    have hconjz : ∀ s : Y ⧸ P, orderOf s = 2 → IsConj s z := fun s hs => by
      obtain ⟨g, hg⟩ := hz s hs
      exact isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]; exact hg⟩
    exact fun s s' hs hs' => (hconjz s hs).trans (hconjz s' hs').symm
  have hαker : (linAction e (frattiniConjAction P D)).ker ≤ P := fun y hy => hKP (by
    rw [MonoidHom.mem_ker] at hy ⊢
    apply coordLin_injective e
    rw [coordLin_one, ← linAction_toLinearMap e (frattiniConjAction P D) y, hy]
    rfl)
  have hCF := noncentral_critical_composition_factor_alternatives hp3 P hP hSnab hS2
    (linAction e (frattiniConjAction P D)) hαker hconj
    ⟨n, c, hnc, Module.finrank_fin_fun (ZMod p), hfixc⟩
  obtain ⟨-, -, -, hcase⟩ := hCF
  rcases hcase with ⟨X, _, _, hX3, ι, hι, hirr⟩ | ⟨hnt, hfix2⟩
  · have h := complete_rank_three_dim_case hp3 P hSnab f hf hAP hZE hpre hX3 ι hι hirr
    exact ⟨h.2, fun _ => h.1⟩
  have hD'n : (D.map P.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  obtain ⟨πD, hπD, hπDker, hπDα⟩ := exists_frattini_coordinates P D e
  have hD'p : IsPGroup p (D.map P.subtype) := hDp.map _
  have hDZE : (D.map P.subtype).map f ≤ center E := by
    rintro _ ⟨y, hy, rfl⟩
    have hyP : y ∈ P := map_subtype_le D hy
    rw [← hpre] at hyP
    exact hyP
  have h2E := pRank_two_le_of_central_cover hp2 P f hf hAP hZE hpre hS2
  have hloc' := (critical_fixed_plane_kernel_local_comparison hp3 hloc f hf (hP.to_le hAP) h2E
    (D.map P.subtype) hD'p (linAction e (frattiniConjAction P D)) πD hπD hπDker hπDα hDZE hnt
    hfix2).2
  refine ⟨hloc', fun hrank => ?_⟩
  exfalso
  have hn : n = 3 ∨ n = 4 ∨ n = 6 := by
    simp only [Prod.mk.injEq] at hnc
    omega
  have hn3 := frattini_dim_eq_three hp2 P hP hmin D hexp hDZ hrank hn hWn
  have hc1 : c = 1 := by
    simp only [Prod.mk.injEq] at hnc
    omega
  have h2dvd : 2 ∣ Nat.card Y := by
    rw [pRank_eq_open_pRank_top] at hY2
    obtain ⟨E₂, -, -, hE₂⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) (⊤ : Subgroup Y)
    rw [hY2] at hE₂
    exact (dvd_pow_self 2 (by norm_num)).trans (hE₂ ▸ card_subgroup_dvd_card E₂)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have := (hfix2 t ht).symm.trans (hfixc t ht)
  omega

end Linear

end CFSG.RankThree.OddKernel
