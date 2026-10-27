module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218Borel
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4CartanRank
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevUni
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevToral
import CFSG.RankThree.PartOne.AUTSL.FieldExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c
import CFSG.GH74.GLS.IVK.Proofs2.NoOuter
import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Quasithin.H13.Sec53F.Unit (borelAutData_u4 hypSU_ext' hypTorus_comm fieldAutHom
  fieldAutHom_apply mat_fieldHom)
open CFSG.RankThree.CentralLiftU (mem_hypTorus_of_diag hypSU_eq_of_diag)

set_option linter.unusedSectionVars false

theorem uc22s218_u4_not_dvd_pow_two {n p : ℕ} (hp : p.Prime) (h1 : ¬ p ∣ 2 ^ n - 1)
    (h2 : ¬ p ∣ 2 ^ n + 1) : ¬ p ∣ 2 ^ (2 * n) - 1 := by
  have hfac : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e]
    generalize 2 ^ n = x at h ⊢
    have h3 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ h
    zify [h, h3]
    ring
  rw [hfac]
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact h1 h
  · exact h2 h

theorem uc22s218_u4_div_le_two {e : ℕ} (he : e ≠ 1) : 4 / e ≤ 2 := by
  rcases Nat.lt_or_ge e 2 with h | h
  · obtain rfl : e = 0 := by omega
    simp
  · calc 4 / e ≤ 4 / 2 := Nat.div_le_div_left h (by norm_num)
      _ = 2 := by norm_num

theorem uc22s218_u4_div_orderOf_eq_two {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q - 1)
    (hq : 1 ≤ q) : 4 / orderOf (-(q : ZMod p)) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : (q : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) p).2 hpq
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
    exact h
  rw [hq1, orderOf_neg_one, ZMod.ringChar_zmod_n, if_neg hp2]

theorem uc22s218_u4_orderOf_ne_one {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q + 1) :
    orderOf (-(q : ZMod p)) ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Ne, orderOf_eq_one_iff, neg_eq_iff_add_eq_zero]
  intro h
  apply hpq
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h

section Model

variable {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

theorem uc22s218_u4_mat_pow {t : ↥(hypSU h 2 0)} {v : HypIndex 2 0 → K}
    (hm : ((t : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = diagonal v)
    (k : ℕ) :
    (((t ^ k : ↥(hypSU h 2 0)) : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      diagonal (v ^ k) := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hm, diagonal_pow]

theorem uc22s218_u4_torusEntries_ne_zero (a : Fin 2 → Kˣ) (d : Fin 0 → Kˣ) (x : HypIndex 2 0) :
    torusEntries h a d x ≠ 0 := by
  rcases x with i | k | i
  · exact (a i).ne_zero
  · exact k.elim0
  · exact inv_ne_zero ((map_ne_zero h.bar).2 (a i).ne_zero)

theorem uc22s218_u4_pow_card {m : ℕ} [Finite K] (hK : Nat.card K = 2 ^ m) {x : K} (hx : x ≠ 0) :
    x ^ (2 ^ m - 1) = 1 := by
  have h1 := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 x hx)
  rw [Nat.card_units, hK] at h1
  simpa using congrArg Units.val h1

theorem uc22s218_u4_fieldAut_pow {φ : MulAut ↥(hypSU h 2 0)}
    (hφ : φ ∈ MonoidHom.range (fieldAutHom h 2 0)) :
    ∃ j : ℕ, ∀ t ∈ hypTorus h 2 0, φ t = t ^ 2 ^ j := by
  have := h.finite
  have := h.charP
  obtain ⟨τ, rfl⟩ := hφ
  obtain ⟨j, hj⟩ := CFSG.RankThree.PartOne.AUTSL.exists_ringEquiv_eq_pow_two τ
  refine ⟨j, fun t ht => ?_⟩
  obtain ⟨a, d, -, -, hm⟩ := ht
  apply hypSU_ext'
  rw [fieldAutHom_apply, mat_fieldHom, hm, uc22s218_u4_mat_pow h hm, diagonal_map (map_zero τ)]
  congr 1
  funext x
  exact hj _

theorem uc22s218_u4_torus_pow {t : ↥(hypSU h 2 0)} (ht : t ∈ hypTorus h 2 0) :
    t ^ (2 ^ (2 * n) - 1) = 1 := by
  have := h.finite
  obtain ⟨a, d, -, -, hm⟩ := ht
  apply hypSU_ext'
  rw [uc22s218_u4_mat_pow h hm, Subgroup.coe_one, Units.val_one, ← diagonal_one]
  congr 1
  funext x
  exact uc22s218_u4_pow_card h.card (uc22s218_u4_torusEntries_ne_zero h a d x)

theorem uc22s218_u4_exists_orderOf_torus {s : ℕ} (hsn : s ∣ n) :
    ∃ d ∈ hypTorus h 2 0, orderOf d = 2 ^ s - 1 := by
  have := h.finite
  obtain ⟨u, hu⟩ := uc22p218c_exists_orderOf_units (K := K) (n := 2 * n) h.card
    (Dvd.dvd.mul_left hsn 2)
  have hu1 : u ^ (2 ^ n - 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hu]
    exact Nat.pow_sub_one_dvd_pow_sub_one 2 hsn
  have hbar : h.bar (u : K) = (u : K) := by
    rw [UnitaryFieldData.bar_apply]
    have : u ^ 2 ^ n = u := by
      rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := n)), pow_succ, hu1, one_mul]
    simpa using congrArg Units.val this
  let a : Fin 2 → Kˣ := ![u, 1]
  have hratio : torusRatio h a (isEmptyElim : Fin 0 → Kˣ) = 1 := by
    have e0 : ∏ k : Fin 0, (((isEmptyElim k : Kˣ)) : K) = 1 := Fin.prod_univ_zero _
    rw [torusRatio, e0, mul_one, Fin.prod_univ_two]
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, map_one, div_one, hbar]
    rw [mul_one]
    exact div_self u.ne_zero
  obtain ⟨g, hg, hgm⟩ := torusMat_mem_hypSU h a (d := isEmptyElim) (fun k => isEmptyElim k) hratio
  refine ⟨g, hg, ?_⟩
  rw [← hu, orderOf_eq_orderOf_iff]
  intro m
  have hmat := uc22s218_u4_mat_pow h hgm m
  constructor
  · intro hgm1
    have h1 := congrArg (fun z : ↥(hypSU h 2 0) =>
      ((z : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inl 0) (.inl 0)) hgm1
    simp only [hmat, diagonal_apply_eq, Pi.pow_apply, Subgroup.coe_one, Units.val_one,
      Matrix.one_apply_eq, torusEntries, a, Matrix.cons_val_zero] at h1
    exact Units.ext (by simpa using h1)
  · intro hum
    apply hypSU_eq_of_diag h hmat (q' := fun _ => 1)
    · rw [Subgroup.coe_one, Units.val_one, diagonal_one.symm]
    · intro x
      fin_cases x
      · simp [torusEntries, a, ← Units.val_pow_eq_pow_val, hum]
      · simp [torusEntries, a]
    · intro k
      exact k.elim0

theorem uc22s218_u4_fieldBorelData_model :
    FieldBorelData n (2 ^ (2 * n) - 1) (hypUnitriangular h 2 0) (hypTorus h 2 0)
      (MonoidHom.range (fieldAutHom h 2 0)) where
  borel := borelAutData_u4 h
  pow := fun _ hφ => uc22s218_u4_fieldAut_pow h hφ
  exp := fun _ ht => uc22s218_u4_torus_pow h ht
  exists_d := fun _ hsn => uc22s218_u4_exists_orderOf_torus h hsn

theorem uc22s218_u4_model_elemAbelian {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ℓ ∣ 2 ^ n - 1) :
    ∃ A : Subgroup ↥(hypSU h 2 0), A ≤ hypTorus h 2 0 ∧ IsElemAbelian ℓ A ∧
      Nat.card A = ℓ ^ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := h.finite
  have hℓK : ℓ ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    exact hℓn.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left n 2))
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ hℓK
  have hprim : IsPrimitiveRoot (ζ : K) ℓ := by
    have := IsPrimitiveRoot.orderOf ζ
    rw [hζ] at this
    exact IsPrimitiveRoot.coe_units_iff.2 this
  have hζ1 : ζ ^ (2 ^ n - 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hζ]
    exact hℓn
  have hbar : h.bar (ζ : K) = (ζ : K) := by
    rw [UnitaryFieldData.bar_apply]
    have : ζ ^ 2 ^ n = ζ := by
      rw [← Nat.sub_add_cancel (Nat.one_le_two_pow (n := n)), pow_succ, hζ1, one_mul]
    simpa using congrArg Units.val this
  obtain ⟨ι, hι⟩ := CFSG.StandardType.exists_hypTorusHom (r := 2) h hℓ hprim hbar
  have hpow : ∀ m : Multiplicative (Fin 2 → ZMod ℓ), m ^ ℓ = 1 := fun m => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp [nsmul_eq_mul]
  refine ⟨(⊤ : Subgroup (Multiplicative (Fin 2 → ZMod ℓ))).map ι, ?_, ?_, ?_⟩
  · rintro _ ⟨m, -, rfl⟩
    exact mem_hypTorus_of_diag h (hι (Multiplicative.toAdd m))
  · exact CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, fun m _ => hpow m⟩ ι
  · rw [← MonoidHom.range_eq_map]
    exact CFSG.StandardType.card_range_hypTorusHom h hℓ hprim ι hι

theorem uc22s218_u4_exists_prime_orderOf_torus {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓK : ℓ ∣ 2 ^ (2 * n) - 1) : ∃ d ∈ hypTorus h 2 0, orderOf d = ℓ := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := h.finite
  have hℓK' : ℓ ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    exact hℓK
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ hℓK'
  let a : Fin 2 → Kˣ := ![u, u⁻¹]
  have hratio : torusRatio h a (isEmptyElim : Fin 0 → Kˣ) = 1 := by
    have e0 : ∏ k : Fin 0, (((isEmptyElim k : Kˣ)) : K) = 1 := Fin.prod_univ_zero _
    rw [torusRatio, e0, mul_one, Fin.prod_univ_two]
    have hb : h.bar (u : K) ≠ 0 := (map_ne_zero h.bar).2 u.ne_zero
    have hu0 : (u : K) ≠ 0 := u.ne_zero
    simp only [a, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
  obtain ⟨g, hg, hgm⟩ := torusMat_mem_hypSU h a (d := isEmptyElim) (fun k => isEmptyElim k) hratio
  refine ⟨g, hg, ?_⟩
  rw [← hu, orderOf_eq_orderOf_iff]
  intro m
  have hmat := uc22s218_u4_mat_pow h hgm m
  constructor
  · intro hgm1
    have h1 := congrArg (fun z : ↥(hypSU h 2 0) =>
      ((z : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inl 0) (.inl 0)) hgm1
    simp only [hmat, diagonal_apply_eq, Pi.pow_apply, Subgroup.coe_one, Units.val_one,
      Matrix.one_apply_eq, torusEntries, a, Matrix.cons_val_zero] at h1
    exact Units.ext (by simpa using h1)
  · intro hum
    apply hypSU_eq_of_diag h hmat (q' := fun _ => 1)
    · rw [Subgroup.coe_one, Units.val_one, diagonal_one.symm]
    · intro x
      fin_cases x
      · simp [torusEntries, a, ← Units.val_pow_eq_pow_val, hum]
      · simp [torusEntries, a, ← Units.val_pow_eq_pow_val, hum]
    · intro k
      exact k.elim0

end Model

section Rank

theorem uc22s218_u4_fieldBorel {Y : Type} [Group Y] {n : ℕ} (hY : IsU4 Y n) :
    FieldBorel Y n (2 ^ (2 * n) - 1) := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  exact FieldBorel.of_mulEquiv (Y := ↥(hypSU h 2 0))
    ⟨_, _, _, uc22s218_u4_fieldBorelData_model h⟩ e

theorem uc22s218_u4_torus {Y : Type} [Group Y] {n : ℕ} (hY : IsU4 Y n) :
    ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 →
        ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ (2 * n) - 1 → ∃ y ∈ T, orderOf y = ℓ := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  refine ⟨(hypTorus h 2 0).map e.toMonoidHom, ?_, fun ℓ hℓ hℓn => ?_, fun ℓ hℓ hℓn => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hypTorus_comm h hx hy]
  · obtain ⟨A, hAT, hAe, hAc⟩ := uc22s218_u4_model_elemAbelian h hℓ hℓn
    refine ⟨A.map e.toMonoidHom, Subgroup.map_mono hAT,
      CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, hAc]
  · obtain ⟨d, hdH, hdo⟩ := uc22s218_u4_exists_prime_orderOf_torus h hℓ hℓn
    exact ⟨e d, ⟨d, hdH, rfl⟩, by rw [MulEquiv.orderOf_eq, hdo]⟩

theorem uc22s218_u4_pRank_eq_div {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp1 : ¬ p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) = 4 / orderOf (-((2 ^ n : ℕ) : ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  have := h.finite
  let := Fintype.ofFinite K
  obtain ⟨e₀⟩ := CFSG.Quasithin.H13.U4Par.nonempty_hypSU_equiv_statedProj h
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hpq : ¬ p ∣ 2 ^ n := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  let S : Subgroup ↥(StatedSU 4 (2 ^ n) K) :=
    (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ n) K)
  have hSdvd : Nat.card S ∣ 4 :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.RankChevUniProof.card_scalars_statedSU_dvd (F := K)
      (p := 2) (f := n) (m := 4) Nat.prime_two hK (by norm_num)).1
  have hSnot : ¬ p ∣ Nat.card S := by
    intro hdiv
    have h4 : p ∣ 2 ^ 2 := by simpa using hdiv.trans hSdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  calc CFSG.Open.pRank p (⊤ : Subgroup Y)
      = CFSG.Open.pRank p (⊤ : Subgroup ↥(hypSU h 2 0)) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 4 (2 ^ n) K))) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e₀
    _ = CFSG.Open.pRank p (⊤ : Subgroup (↥(StatedSU 4 (2 ^ n) K) ⧸ S)) := rfl
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSU 4 (2 ^ n) K)) :=
        CFSG.SectionRank.pRank_quotient_eq S hSnot
    _ = 4 / orderOf (-((2 ^ n : ℕ) : ZMod p)) :=
        CFSG.LocalAnalysis.RankThreeUC.S15.pRank_statedSU_of_not_dvd hp hp2
          (by rw [← Nat.card_eq_fintype_card, hK]) hpq hp1 4 (by norm_num)

theorem uc22s218_u4_pRank_le_three {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  have := h.finite
  have := h.charP
  let := Fintype.ofFinite K
  obtain ⟨e₀⟩ := CFSG.Quasithin.H13.U4Par.nonempty_hypSU_equiv_statedProj h
  have hK : Nat.card K = (2 ^ n) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).1 h0
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  let S : Subgroup ↥(StatedSU 4 (2 ^ n) K) :=
    (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ n) K)
  have hSdvd : Nat.card S ∣ 4 :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.RankChevUniProof.card_scalars_statedSU_dvd (F := K)
      (p := 2) (f := n) (m := 4) Nat.prime_two hK (by norm_num)).1
  have hSnot : ¬ p ∣ Nat.card S := by
    intro hdiv
    have h4 : p ∣ 2 ^ 2 := by simpa using hdiv.trans hSdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  calc CFSG.Open.pRank p (⊤ : Subgroup Y)
      = CFSG.Open.pRank p (⊤ : Subgroup ↥(hypSU h 2 0)) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
    _ = CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 4 (2 ^ n) K))) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e₀
    _ = CFSG.Open.pRank p (⊤ : Subgroup (↥(StatedSU 4 (2 ^ n) K) ⧸ S)) := rfl
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSU 4 (2 ^ n) K)) :=
        CFSG.SectionRank.pRank_quotient_eq S hSnot
    _ = CFSG.Open.pRank p (StatedSU 4 (2 ^ n) K) :=
        (CFSG.SectionRank.pRank_eq_pRank_top_subgroup _).symm
    _ ≤ 3 := by
        have hle := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_statedSU_le (F := K) (q := 2 ^ n)
          (r := p) (m := 4) (by norm_num) hpK
        simpa using hle

theorem uc22s218_u4_pRank_le_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp1 : ¬ p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  rw [uc22s218_u4_pRank_eq_div hY hp hp2 hp1]
  exact uc22s218_u4_div_le_two (uc22s218_u4_orderOf_ne_one hp (by exact_mod_cast hp1))

theorem uc22s218_u4_pRank_eq_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup Y) = 2 := by
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hr1 : ¬ r ∣ 2 ^ n + 1 := by
    intro hd
    have h2 : r ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub hd hrn
    rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by have := Nat.one_le_two_pow (n := n); omega] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  rw [uc22s218_u4_pRank_eq_div hY hr hr2 hr1]
  exact uc22s218_u4_div_orderOf_eq_two hr hr2 hrn Nat.one_le_two_pow

theorem uc22s218_u4_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU4 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨K, _, h, -⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hq : 2 < 2 ^ n := by
    have h1 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.one_le
    have h2 := Nat.le_of_dvd (by omega) hrn
    have := hr.two_le
    omega
  obtain ⟨P⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hK := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_U4CartanRank_holds Y n hY hq
    (P : Subgroup Y) (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P) r hr hr2 hrn
  have hv := hK.2.2
  have hdvd : Nat.card (TauCeti.Subgroup.normalizerQuotient (P : Subgroup Y)) ∣
      Nat.card (normalizer ((P : Subgroup Y) : Set Y)) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((P : Subgroup Y).subgroupOf (normalizer ((P : Subgroup Y) : Set Y)))
    exact Dvd.intro _ h.symm
  refine CFSG.RankThree.PartOne.K133.not_dvd_card_sylow_of_le_normalizer hr P
    (normalizer ((P : Subgroup Y) : Set Y)) le_rfl (fun k hk => ?_)
  have hk' := (Nat.Prime.pow_dvd_iff_le_factorization hr Nat.card_pos.ne').1 hk
  rw [hv] at hk'
  exact ((Nat.Prime.pow_dvd_iff_le_factorization hr Nat.card_pos.ne').2 hk').trans hdvd

theorem torusFacts218_U4 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsU4 Y n) :
    TorusFacts218 Y n (fun p => p ∣ 2 ^ n - 1)
      (fun p => ¬ p ∣ 2 ^ n - 1 ∧ ¬ p ∣ 2 ^ n + 1) :=
  torusFacts218_of_fieldBorel (E := 2 ^ (2 * n) - 1) (uc22s218_u4_fieldBorel hY)
    (fun _ hsn _ hrs => hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))
    (fun hp _ hout => uc22s218_u4_not_dvd_pow_two hp hout.1 hout.2)
    (let ⟨T, hTc, hTE, _⟩ := uc22s218_u4_torus hY; ⟨T, hTc, hTE⟩)
    (fun hs hsn hr hrs => uc22s218_u4_pRank_eq_two hY hs hsn hr hrs)
    (fun hs hsn hr hrs => uc22s218_u4_not_dvd_card_sylow hY hs hsn hr hrs)
    (fun hp hp2 hout => uc22s218_u4_pRank_le_two hY hp hp2 hout.2)

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
