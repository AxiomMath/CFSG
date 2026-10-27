module

public import CFSG.RankThree.PartOne.Q1327T.Item7Block
public import CFSG.RankThree.PartOne.Q1327T.Item7UBasic
public import CFSG.RankThree.PartOne.Q1327T.Item7U3
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartOne.N143X.EvenSmall
public import CFSG.RankThree.PartOne.KF.F128SU
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Open.StatedAPI

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

section SL

variable {K : Type} [Field K]

theorem mem_statedSL_of_det {n : ℕ} {A : GL (Fin n) K}
    (h : (A : Matrix (Fin n) (Fin n) K).det = 1) : A ∈ StatedSL n K :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

theorem swGL12_mem_sl [CharP K 2] : (swGL12 : GL (Fin 3) K) ∈ StatedSL 3 K := by
  apply mem_statedSL_of_det
  change (sw12 : Matrix (Fin 3) (Fin 3) K).det = 1
  have h := CharTwo.neg_eq (1 : K)
  rw [Matrix.det_fin_three]
  simp [sw12, h]

theorem swGL02_mem_sl [CharP K 2] : (swGL02 : GL (Fin 3) K) ∈ StatedSL 3 K := by
  apply mem_statedSL_of_det
  change (sw02 : Matrix (Fin 3) (Fin 3) K).det = 1
  have h := CharTwo.neg_eq (1 : K)
  rw [Matrix.det_fin_three]
  simp [sw02, h]

@[expose] noncomputable def blockSL : SL(2, K) →* GL (Fin 3) K :=
  blockGL3.comp Matrix.SpecialLinearGroup.toGL

theorem coe_blockSL (A : SL(2, K)) :
    ((blockSL A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      leviMat (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blockSL_injective : Function.Injective (blockSL : SL(2, K) →* GL (Fin 3) K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 : (Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) K) = 1 :=
    blockGL3_eq_one_of_scalar (by
      rw [show blockGL3 (Matrix.SpecialLinearGroup.toGL A) = blockSL A from rfl, hA]
      exact Subgroup.one_mem _)
  have h2 : Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K) :=
    fun a b hab => Subtype.ext
      (congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) hab)
  exact h2 (by rw [h1, map_one])

theorem blockSL_mem (A : SL(2, K)) : (blockSL A : GL (Fin 3) K) ∈ StatedSL 3 K := by
  apply mem_statedSL_of_det
  rw [coe_blockSL, det_leviMat, A.2]

@[expose] noncomputable def levi3L : Subgroup (StatedSL 3 K) :=
  (blockSL (K := K)).range.subgroupOf (StatedSL 3 K)

theorem mem_levi3L {g : StatedSL 3 K} :
    g ∈ levi3L ↔ ∃ A : SL(2, K), blockSL A = (g : GL (Fin 3) K) := Iff.rfl

end SL

section Levi

variable {K : Type} [Field K]

theorem levi3L_diag {d : Fin 3 → Kˣ} (h01 : d 0 = d 1) {g : StatedSL 3 K} (hg : g ∈ levi3L) :
    (g : GL (Fin 3) K) * diagU d = diagU d * g := by
  obtain ⟨A, hA⟩ := mem_levi3L.1 hg
  rw [← hA]
  exact blockGL3_commute_diagU h01 _

theorem levi3L_inj {g : StatedSL 3 K} (hg : g ∈ levi3L)
    (hs : (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) : g = 1 := by
  obtain ⟨A, hA⟩ := mem_levi3L.1 hg
  have h1 : (Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) K) = 1 :=
    blockGL3_eq_one_of_scalar (by
      rw [show blockGL3 (Matrix.SpecialLinearGroup.toGL A) = blockSL A from rfl, hA]
      exact hs)
  have h2 : Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(2, K) →* GL (Fin 2) K) :=
    fun a b hab => Subtype.ext (congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K))
      hab)
  have hA1 : A = 1 := h2 (by rw [h1, map_one])
  apply Subtype.ext
  rw [← hA, hA1, map_one]
  rfl

theorem levi3L_mem {g : StatedSL 3 K} (h02 : ent3 (g : GL (Fin 3) K) 0 2 = 0)
    (h12 : ent3 (g : GL (Fin 3) K) 1 2 = 0) (h20 : ent3 (g : GL (Fin 3) K) 2 0 = 0)
    (h21 : ent3 (g : GL (Fin 3) K) 2 1 = 0) (h22 : ent3 (g : GL (Fin 3) K) 2 2 = 1) :
    g ∈ levi3L := by
  set B : Matrix (Fin 2) (Fin 2) K :=
    !![(g : GL (Fin 3) K).val 0 0, (g : GL (Fin 3) K).val 0 1;
      (g : GL (Fin 3) K).val 1 0, (g : GL (Fin 3) K).val 1 1] with hB
  have hgB : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = leviMat B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp_all [leviMat, ent3]
  have hdet : B.det = 1 := by
    have h1 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = B.det := by
      rw [hgB, det_leviMat]
    rw [← h1]
    exact N143X.det_eq_one_of_mem_statedSL' g.2
  let A : SL(2, K) := ⟨B, hdet⟩
  refine mem_levi3L.2 ⟨A, Units.ext ?_⟩
  rw [coe_blockSL, hgB]

end Levi

section LeviSimple

variable {K : Type} [Field K] [Finite K] {f : ℕ}

omit [Finite K] in
theorem levi3L_le : (blockSL (K := K)).range ≤ StatedSL 3 K := by
  rintro _ ⟨A, rfl⟩
  exact blockSL_mem A

@[expose] noncomputable def levi3LEquiv : SL(2, K) ≃* (levi3L : Subgroup (StatedSL 3 K)) :=
  (MonoidHom.ofInjective blockSL_injective).trans (Subgroup.subgroupOfEquivOfLe levi3L_le).symm

omit [Finite K] in
theorem isSimpleGroup_levi3L [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (levi3L : Subgroup (StatedSL 3 K)) := by
  have := CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup (K := K) h4
  exact levi3LEquiv.symm.isSimpleGroup

theorem card_levi3L :
    Nat.card (levi3L : Subgroup (StatedSL 3 K)) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  rw [← Nat.card_congr levi3LEquiv.toEquiv]
  exact CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two K

end LeviSimple

section Cover

variable {Q : Type} [Group Q] {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_cover_proj {H : Subgroup (GL ι K)} (hZ : Subgroup.center Q = ⊥)
    (e : (Q ⧸ Subgroup.center Q) ≃* StatedProj H) :
    ∃ π : H →* Q, Function.Surjective π ∧ π.ker = (StatedScalars ι K).subgroupOf H := by
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  let π : H →* Q := (ce.symm.toMonoidHom.comp e.symm.toMonoidHom).comp (QuotientGroup.mk' N)
  refine ⟨π, ?_, ?_⟩
  · exact (ce.symm.surjective.comp e.symm.surjective).comp (QuotientGroup.mk'_surjective N)
  · ext x
    rw [MonoidHom.mem_ker]
    change ce.symm (e.symm (QuotientGroup.mk' N x)) = 1 ↔ x ∈ N
    rw [map_eq_one_iff ce.symm ce.symm.injective, map_eq_one_iff e.symm e.symm.injective]
    exact QuotientGroup.eq_one_iff (N := N) x

end Cover

section Scalars

variable {K : Type} [Field K] [Finite K] {p : ℕ}

theorem not_dvd_card_scalars_sl3 (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) := by
  intro hd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 x.2
  have hdet := N143X.det_eq_one_of_mem_statedSL' x.1.2
  have hc3 : c ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h1 : ((x.1 : StatedSL 3 K) : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c :=
      hc.symm
    rw [h1] at hdet
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_univ_three, pow_succ] using hdet
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ((x.1 : StatedSL 3 K) : GL (Fin 3) K) = Matrix.GeneralLinearGroup.scalar (Fin 3) c :=
      hc.symm
    change ((x.1 : StatedSL 3 K) : GL (Fin 3) K) ^ 3 = 1
    rw [h1, ← map_pow, hc3, map_one]
  have := orderOf_dvd_of_pow_eq_one hx3
  rw [hx] at this
  have := Nat.le_of_dvd (by norm_num) this
  omega

end Scalars

section Diag

variable {K : Type} [Field K]

theorem det_conj_gl {n : ℕ} (A y : GL (Fin n) K) :
    ((A * y * A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (y : Matrix (Fin n) (Fin n) K).det := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.det_units_conj A _

@[expose] def conjSL {n : ℕ} (A : GL (Fin n) K) : StatedSL n K ≃* StatedSL n K where
  toFun y := ⟨A * (y : GL (Fin n) K) * A⁻¹, by
    apply mem_statedSL_of_det
    rw [det_conj_gl]
    exact N143X.det_eq_one_of_mem_statedSL' y.2⟩
  invFun y := ⟨A⁻¹ * (y : GL (Fin n) K) * A, by
    apply mem_statedSL_of_det
    have := det_conj_gl A⁻¹ y
    rw [inv_inv] at this
    rw [this]
    exact N143X.det_eq_one_of_mem_statedSL' y.2⟩
  left_inv y := Subtype.ext (by
    change A⁻¹ * (A * (y : GL (Fin n) K) * A⁻¹) * A = (y : GL (Fin n) K)
    group)
  right_inv y := Subtype.ext (by
    change A * (A⁻¹ * (y : GL (Fin n) K) * A) * A⁻¹ = (y : GL (Fin n) K)
    group)
  map_mul' y z := Subtype.ext (by
    change A * ((y : GL (Fin n) K) * (z : GL (Fin n) K)) * A⁻¹ =
      (A * (y : GL (Fin n) K) * A⁻¹) * (A * (z : GL (Fin n) K) * A⁻¹)
    group)

variable [Finite K]

theorem exists_diag_conj_sl {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (E₀ : Subgroup (StatedSL 3 K)) (hexp : ∀ x ∈ E₀, x ^ p = 1)
    (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) :
    ∃ (P : GL (Fin 3) K) (β : StatedSL 3 K ≃* StatedSL 3 K),
      (∀ x, ((β x : StatedSL 3 K) : GL (Fin 3) K) = P⁻¹ * x * P) ∧
      ∀ x ∈ E₀, (((β x : StatedSL 3 K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag := by
  classical
  let φ : SL(3, K) →* GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hab)
  let E' : Subgroup SL(3, K) := (E₀.map (StatedSL 3 K).subtype).comap φ
  have hE' : ∀ x ∈ E', ∃ y ∈ E₀, (y : GL (Fin 3) K) = φ x := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    exact ⟨y, hy, hyx⟩
  have hcomm' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', hx', hxx⟩ := hE' x hx
    obtain ⟨y', hy', hyy⟩ := hE' y hy
    apply hφ
    rw [map_mul, map_mul, ← hxx, ← hyy]
    have := congrArg Subtype.val (hcomm x' hx' y' hy')
    simpa using this
  have hexp' : ∀ x ∈ E', x ^ p = 1 := by
    intro x hx
    obtain ⟨x', hx', hxx⟩ := hE' x hx
    apply hφ
    rw [map_pow, ← hxx, map_one]
    have := congrArg Subtype.val (hexp x' hx')
    simpa using this
  obtain ⟨A, hA⟩ := exists_conj_diagonal_of_commuting_pow_eq_one hζ E' hcomm' hexp'
  refine ⟨A⁻¹, conjSL A, fun x => ?_, fun x hx => ?_⟩
  · rw [inv_inv]
    rfl
  · intro i j hij
    have hdet := N143X.det_eq_one_of_mem_statedSL' x.2
    let xs : SL(3, K) := ⟨((x : StatedSL 3 K) : GL (Fin 3) K), hdet⟩
    have hxs : xs ∈ E' := Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨x, hx, Units.ext rfl⟩)
    have h1 := hA xs hxs i j hij
    have h2 : (((conjSL A x : StatedSL 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (A : Matrix (Fin 3) (Fin 3) K) * ((xs : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
          ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl
    rw [h2]
    exact h1

end Diag

section Rank

variable {K : Type} [Field K] [Finite K] {p n : ℕ}

theorem two_le_orderOf_of_not_dvd {q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) (h1 : ¬ p ∣ q - 1)
    (hq1 : 1 ≤ q) : 2 ≤ orderOf (q : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : (q : ZMod p) ≠ 1 := fun h => h1 (by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h]; simp)
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff _ _).1 h)
  have hpos : 0 < orderOf (q : ZMod p) :=
    orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p - 1, Nat.sub_pos_of_lt hp.one_lt, ZMod.pow_card_sub_one_eq_one hq0⟩)
  by_contra hlt
  push Not at hlt
  exact hne1 (orderOf_eq_one_iff.1 (le_antisymm (Nat.le_of_lt_succ hlt) hpos))

open CFSG.GroupTheory.WeirSylow in
theorem pRank_statedProj_statedSL_le_one (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hN : ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)))
    (h : n / orderOf (Nat.card K : ZMod p) ≤ 1) :
    CFSG.pRank p (StatedProj (StatedSL n K)) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype K := Fintype.ofFinite K
  rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hN]
  refine pRank_le_one_of_injective (p := p) (StatedSL n K).subtype
    (StatedSL n K).subtype_injective ?_
  intro P
  have hcard : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  obtain ⟨e⟩ := sylow_GL (hp.odd_of_ne_two hp2) K (by rwa [hcard]) n P
  rw [hcard] at e
  exact (MulEquiv.isCyclic e).2 (isCyclic_sigmaModel_of_div_le_one h)

end Rank

section Multiplier

theorem not_dvd_card_multiplier_psl3 {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ∣ Nat.card (Blueprint.Multiplier.generic .PSL 3 2 f ×
      Blueprint.Multiplier.exceptional .PSL 3 2 f) := by
  intro hd
  have h48 : Nat.card (Blueprint.Multiplier.generic .PSL 3 2 f ×
      Blueprint.Multiplier.exceptional .PSL 3 2 f) ∣ 48 := by
    unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
    have hgen : Blueprint.Multiplier.genericOrders .PSL 3 2 f = (Nat.gcd 3 (2 ^ f - 1), 1) := rfl
    rw [hgen]
    have hg : Nat.gcd 3 (2 ^ f - 1) ∣ 3 := Nat.gcd_dvd_left _ _
    rcases Nat.lt_or_ge f 3 with hf | hf
    · interval_cases f <;> simp [Blueprint.Multiplier.exceptionalOrders]
    · have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 3 2 f = (1, 1) := by
        unfold Blueprint.Multiplier.exceptionalOrders
        split <;> simp_all
      rw [hexc]
      simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
      exact Dvd.dvd.trans hg (by norm_num)
  have := Nat.le_of_dvd (by norm_num) (hd.trans h48)
  have h2 : p ∣ 2 ^ 4 * 3 := by simpa using hd.trans h48
  rcases (Nat.Prime.dvd_mul hp).1 h2 with h | h
  · have := hp.dvd_of_dvd_pow h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have := Nat.le_of_dvd (by norm_num) h
    omega

end Multiplier

theorem row8U3At_leaf7_three
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 3) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSL 3 2 q.exponent := by
    have := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e0
    rw [hq2] at this
    exact this
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hmod
  have hf : 1 ≤ q.exponent := q.exponent_pos
  generalize q.exponent = f at hmod hK e hf hadm
  exfalso
  have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have hpQ : ¬ p ∣ 2 ^ f := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hN := not_dvd_card_scalars_sl3 (K := K) hp hp5
  by_cases hpq : p ∣ 2 ^ f - 1
  swap
  · have hd2 := two_le_orderOf_of_not_dvd hp hpQ hpq hq1
    have hrk := pRank_statedProj_statedSL_le_one (n := 3) hp hp2
      (by rw [hK]; exact hpQ) hN (by
        rw [hK]
        exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
    have h2 := h.two_le_pRank
    rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e] at h2
    omega
  have hf3 : 3 ≤ f := by
    by_contra hlt
    have : f = 1 ∨ f = 2 := by omega
    rcases this with rfl | rfl
    · have := Nat.le_of_dvd (by norm_num) hpq
      omega
    · have := Nat.le_of_dvd (by norm_num) hpq
      omega
  have hZ : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p (t := .PSL) (n := 3) (f := f)
      ⟨hmod.1, Or.inl hmod⟩ (not_dvd_card_multiplier_psl3 hp hp5)
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow (n := f)
      Nat.prime_two (by rw [hK])
  obtain ⟨π, hπ, hπk⟩ := exists_cover_proj hZ e
  have hscal : ∀ x, π x = 1 ↔ (x : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := fun x => by
    rw [← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf]
  have hker := ker_eq_scalars π hscal
  have hpk : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    exact hN
  obtain ⟨c, hcE, hc1, Kb, x, hKbc, hKbN, hmodKb, hxK, hxo, hgen⟩ := h.conf
  have hKbq := S15K.isQuasisimple_of_model hmodKb
  have hKbp : ⁅Kb, Kb⁆ = Kb := commutator_eq_self_of_perfect hKbq.1
  have hKb1 : Kb ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hxK
    rw [hxK, orderOf_one] at hxo
    exact hp.ne_one hxo.symm
  have := h.elem
  obtain ⟨E₀, hE₀, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian π hp hpk Ē
    (fun y _ => hπ y) h.card
  obtain ⟨ct0, hct0E, hct0⟩ : ∃ ct0 ∈ E₀, π ct0 = c := by
    rw [← hE₀map] at hcE
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hcE
    exact ⟨y, hy, hyc⟩
  have hE₀exp : ∀ y ∈ E₀, y ^ p = 1 := fun y hy =>
    elemPow_eq_one_of_isElementaryAbelian (A := E₀) y hy
  have hE₀comm : ∀ y ∈ E₀, ∀ z ∈ E₀, y * z = z * y := fun y hy z hz => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := E₀)).comm ⟨y, hy⟩ ⟨z, hz⟩)
    simpa using this
  have : Fact p.Prime := ⟨hp⟩
  have hpK1 : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    exact hpq
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK1
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨P, β, hβP, hβ⟩ := exists_diag_conj_sl (IsPrimitiveRoot.coe_units_iff.mpr
    (hζ ▸ IsPrimitiveRoot.orderOf ζ)) E₀ hE₀exp hE₀comm
  let π₂ : StatedSL 3 K →* Q := π.comp β.symm.toMonoidHom
  have hπ₂ : Function.Surjective π₂ := hπ.comp β.symm.surjective
  have hβsymm : ∀ y : StatedSL 3 K, ((β.symm y : StatedSL 3 K) : GL (Fin 3) K) = P * y * P⁻¹ := by
    intro y
    have h1 := hβP (β.symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    group
  have hscal₂ : ∀ y, π₂ y = 1 ↔ (y : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := fun y => by
    change π (β.symm y) = 1 ↔ _
    rw [hscal, hβsymm, conj_mem_scalars_iff']
  have hπ₂β : ∀ y, π₂ (β y) = π y := fun y => by
    change π (β.symm (β y)) = π y
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag (hβ ct0 hct0E)
  have hct : π₂ (β ct0) = c := by rw [hπ₂β, hct0]
  have hcp : (β ct0) ^ p = 1 := by
    rw [← map_pow, hE₀exp ct0 hct0E, map_one]
  have hf2 : 2 ≤ f := by omega
  have hcard := block_card_of_diag (M := StatedSL 3 K) hp swGL12_mem_sl swGL02_mem_sl π₂ hπ₂
    hscal₂ hN hcp (by rw [hct]; exact hc1) (d := d) hd.symm (Kb := Kb) (by rw [hct]; exact hKbc)
    (by rw [hct]; exact hKbN) hKbp hKb1 levi3L (fun d' h01 g hg => levi3L_diag h01 hg)
    (isSimpleGroup_levi3L (by rw [hK]; calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2))
    (fun g hg hs => levi3L_inj hg hs)
    (fun g h02 h12 h20 h21 h22 => levi3L_mem h02 h12 h20 h21 h22)
  rw [card_levi3L, hK, card_psl2_even hmodKb] at hcard
  have hg1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have h2 : 2 ^ g = 2 ^ f := eq_of_mul_sq_sub_one_eq' hg1 hq1 hcard
  have hfg : g = f := Nat.pow_right_injective (le_refl 2) h2
  have hpg := h.p_dvd
  rw [hfg] at hpg
  have h3 : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hpg hpq
  have h4 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h3)

end CFSG.RankThree.PartOne.Q1327T
