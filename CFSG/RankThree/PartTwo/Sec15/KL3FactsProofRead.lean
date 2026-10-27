module

public import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofRead
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3TwoMod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverRanks
import CFSG.RankThree.PartTwo.Sec15.KL3FactsProofTools
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.Classical.SiegelRadical
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.SubgroupLists.SL3Involutions
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec17.Proof17Res7
open CFSG.RankThree.PartTwo.Sec4.Census (sqZeroUnit sqZeroHom)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial
open Matrix

namespace KL3FactsProof

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_elemAbelian_of_sqZero (hK : PiField π p f K) (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Finite V] (N : V →+ Matrix (Fin 3) (Fin 3) K)
    (hN : Function.Injective N) (h0 : ∀ x y, N x * N y = 0) (hpV : ∀ x : V, p • x = 0)
    (hS : ∀ x, sqZeroUnit N h0 x ∈ slPi π 3 (p ^ f) K)
    (hC : ∀ x, sqZeroUnit N h0 x * tOne K = tOne K * sqZeroUnit N h0 x) :
    ∃ E : Subgroup (projImage (slPi π 3 (p ^ f) K)),
      E ≤ Subgroup.centralizer {tM hK hp2 _ isTInv_tOne} ∧
        CFSG.Assembly.IsElemAbelian p E ∧ Nat.card E = Nat.card V := by
  let φ : Multiplicative V →* projImage (slPi π 3 (p ^ f) K) :=
    (ProjGenLinGroup.mk.comp (sqZeroHom N h0)).codRestrict _ fun x =>
      ⟨sqZeroUnit N h0 (Multiplicative.toAdd x), hS _, rfl⟩
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : ProjGenLinGroup.mk (sqZeroUnit N h0 (Multiplicative.toAdd x)) = 1 :=
      congrArg Subtype.val hx
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : scalar (Fin 3) a = 1 + N (Multiplicative.toAdd x) := ha
    have hNx : N (Multiplicative.toAdd x) = scalar (Fin 3) (a - 1) := by
      rw [map_sub, map_one, ha', add_sub_cancel_left]
    have hsq := h0 (Multiplicative.toAdd x) (Multiplicative.toAdd x)
    rw [hNx, ← map_mul, ← map_zero (scalar (Fin 3)), scalar_inj] at hsq
    have hN0 : N (Multiplicative.toAdd x) = 0 := by
      rw [hNx, mul_self_eq_zero.mp hsq, map_zero]
    exact hN (hN0.trans (map_zero N).symm)
  refine ⟨φ.range, ?_, CFSG.RankThree.Classical.isElemAbelian_range hpV φ, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change ProjGenLinGroup.mk (sqZeroUnit N h0 (Multiplicative.toAdd x)) *
        ProjGenLinGroup.mk (tOne K) =
      ProjGenLinGroup.mk (tOne K) * ProjGenLinGroup.mk (sqZeroUnit N h0 (Multiplicative.toAdd x))
    rw [← map_mul, ← map_mul, hC]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hφ, Subgroup.card_top]
    rfl

@[expose] noncomputable def linRoot : K →+ Matrix (Fin 3) (Fin 3) K where
  toFun a := !![0, 0, 0; 0, 0, a; 0, 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem linRoot_injective : Function.Injective (linRoot (K := K)) := by
  intro a b h
  have := congrFun (congrFun h 1) 2
  simpa [linRoot] using this

theorem linRoot_mul (a b : K) : linRoot a * linRoot b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linRoot, mul_apply, Fin.sum_univ_three]

theorem coe_tOne_eq : ((tOne K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![1, 0, 0; 0, -1, 0; 0, 0, -1] := by
  rw [tOne, CFSG.RankThree.PartTwo.Sec4.coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem linRoot_mem (q : ℕ) (a : K) : sqZeroUnit linRoot linRoot_mul a ∈ slPi true 3 q K := by
  rw [mem_slPi_true]
  change (1 + linRoot a).det = 1
  rw [det_fin_three]
  simp [linRoot]

theorem linRoot_comm (a : K) :
    sqZeroUnit linRoot linRoot_mul a * tOne K = tOne K * sqZeroUnit linRoot linRoot_mul a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_tOne_eq]
  change (1 + linRoot a) * _ = _ * (1 + linRoot a)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [linRoot, mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def uniRoot (h : UnitaryFieldData p f K) (u : K) :
    h.traceZero →+ Matrix (Fin 3) (Fin 3) K where
  toFun a := (a : K) • !![0, 0, 0; 0, 1, h.bar u; 0, u, -1]
  map_zero' := by simp
  map_add' a b := by rw [AddSubgroup.coe_add, add_smul]

theorem uniRoot_injective (h : UnitaryFieldData p f K) (u : K) :
    Function.Injective (uniRoot h u) := by
  intro a b hab
  have := congrFun (congrFun hab 1) 1
  simp only [uniRoot, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.smul_apply] at this
  apply Subtype.ext
  simpa using this

theorem uniRoot_mul (h : UnitaryFieldData p f K) {u : K} (hu : h.bar u * u = -1)
    (a b : h.traceZero) : uniRoot h u a * uniRoot h u b = 0 := by
  have hu' : u * h.bar u = -1 := by rw [mul_comm]; exact hu
  simp only [uniRoot, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_mul_smul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hu, hu']

theorem uniRoot_mem (h : UnitaryFieldData p f K) {u : K} (hu : h.bar u * u = -1)
    (a : h.traceZero) :
    sqZeroUnit (uniRoot h u) (uniRoot_mul h hu) a ∈ slPi false 3 (p ^ f) K := by
  have ha : h.bar (a : K) = -(a : K) := by
    have := (h.mem_traceZero.mp a.2)
    rw [UnitaryFieldData.trace] at this
    linear_combination this
  have hbb : h.bar (h.bar u) = u := h.bar_bar u
  rw [mem_slPi_false h]
  change (1 + uniRoot h u a).det = 1 ∧ ((1 + uniRoot h u a).map h.bar)ᵀ * (1 + uniRoot h u a) = 1
  simp only [uniRoot, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · rw [det_fin_three]
    simp
    linear_combination (-(a : K) ^ 2) * hu
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, ha, hbb, transpose_apply]
    all_goals first | ring1 | linear_combination (-(a : K) ^ 2) * hu

theorem uniRoot_comm (h : UnitaryFieldData p f K) {u : K} (hu : h.bar u * u = -1)
    (a : h.traceZero) :
    sqZeroUnit (uniRoot h u) (uniRoot_mul h hu) a * tOne K =
      tOne K * sqZeroUnit (uniRoot h u) (uniRoot_mul h hu) a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_tOne_eq]
  change (1 + uniRoot h u a) * _ = _ * (1 + uniRoot h u a)
  simp only [uniRoot, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]

theorem nsmul_eq_zero_of_piField (hK : PiField π p f K) (x : K) : p • x = 0 := by
  have := hK.finite
  have := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hK.prime⟩
  have hc : CharP K p := by
    refine charP_of_card_eq_prime_pow (f := cond π f (2 * f)) ?_
    rw [← Nat.card_eq_fintype_card, hK.card]
    cases π
    · change (p ^ f) ^ 2 = p ^ (2 * f)
      rw [← pow_mul, mul_comm]
    · rfl
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

theorem commute_of_mk_commute_involution {g t : GL (Fin 3) K}
    (ht : (t : Matrix (Fin 3) (Fin 3) K).det = 1) (ht2 : t * t = 1)
    (h : ProjGenLinGroup.mk g * ProjGenLinGroup.mk t =
      ProjGenLinGroup.mk t * ProjGenLinGroup.mk g) :
    g * t = t * g := by
  obtain ⟨μ, hμ⟩ := exists_scalar_of_mk_commute h
  set z := GeneralLinearGroup.scalar (Fin 3) μ with hz
  have hc : ∀ x : GL (Fin 3) K, x * z = z * x := fun x =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ x).eq
  have hsq : z * z = 1 := by
    have e : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht2, mul_one, mul_inv_cancel]
    rw [hμ] at e
    calc z * z = z * z * (t * t) := by rw [ht2, mul_one]
      _ = z * (z * t) * t := by group
      _ = z * (t * z) * t := by rw [hc t]
      _ = z * t * (z * t) := by group
      _ = 1 := e
  have hdet : (μ : K) ^ 3 = 1 := by
    have e := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K).det) hμ
    simp only [Units.val_mul, det_mul] at e
    rw [det_scalar, ht, mul_one] at e
    have hgi : (g : Matrix (Fin 3) (Fin 3) K).det * ((g⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).det = 1 := by
      rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
    rw [mul_one] at e
    rw [← e, hgi]
  have hsq' : (μ : K) ^ 2 = 1 := by
    have e := congrFun (congrFun (congrArg (fun x : GL (Fin 3) K =>
      (x : Matrix (Fin 3) (Fin 3) K)) hsq) 0) 0
    simp only [hz, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_one] at e
    simpa [sq] using e
  have hμ1 : μ = 1 := by
    apply Units.ext
    rw [Units.val_one]
    calc (μ : K) = (μ : K) ^ 3 * ((μ : K) ^ 2)⁻¹ := by
          have : (μ : K) ≠ 0 := μ.ne_zero
          field_simp
      _ = 1 := by rw [hdet, hsq', inv_one, one_mul]
  have hz1 : z = 1 := by rw [hz, hμ1, map_one]
  rw [hz1, one_mul] at hμ
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [hμ]

theorem exists_lift_sq_eq_one {q : ℕ} {z : projImage (slPi true 3 q K)} (hz : z * z = 1) :
    ∃ g : GL (Fin 3) K, g ∈ slPi true 3 q K ∧ ProjGenLinGroup.mk g = z ∧ g * g = 1 := by
  obtain ⟨g₀, hg₀, hzg⟩ := z.2
  have hdet0 : (g₀ : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_slPi_true q).mp hg₀
  have h1 : ProjGenLinGroup.mk (g₀ * g₀) = 1 := by
    rw [map_mul, hzg]
    exact congrArg Subtype.val hz
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨l, hl⟩ := h1
  have hl3 : (l : K) ^ 3 = 1 := by
    have e := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K).det) hl
    simp only [Units.val_mul, det_mul, hdet0, mul_one] at e
    rw [det_scalar] at e
    exact e
  have hl3' : l ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hl3, Units.val_one])
  set s := GeneralLinearGroup.scalar (Fin 3) l with hs
  have hc : ∀ x : GL (Fin 3) K, x * s = s * x := fun x =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar l x).eq
  refine ⟨s * g₀, ?_, ?_, ?_⟩
  · rw [mem_slPi_true, Units.val_mul, det_mul, det_scalar, hl3, hdet0, one_mul]
  · rw [map_mul, hzg]
    have : ProjGenLinGroup.mk s = 1 := ProjGenLinGroup.mk_scalar l
    rw [this, one_mul]
  · calc s * g₀ * (s * g₀) = s * s * (g₀ * g₀) := by
          rw [show s * g₀ * (s * g₀) = s * (g₀ * s) * g₀ by group, hc g₀]
          group
      _ = s * s * s := by rw [← hl]
      _ = 1 := by
          rw [hs, ← map_mul, ← map_mul, ← pow_two, ← pow_succ, hl3', map_one]

theorem card_le_four_of_sq_eq_one [Finite K] {q : ℕ} (h2 : (2 : K) ≠ 0)
    (Z : Subgroup (projImage (slPi true 3 q K))) (hsq : ∀ z ∈ Z, z * z = 1)
    (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : Nat.card Z ≤ 4 := by
  let Zt : Subgroup (GL (Fin 3) K) :=
    { carrier := {g | (g : Matrix (Fin 3) (Fin 3) K).det = 1 ∧ g * g = 1 ∧
        ∃ z ∈ Z, (z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk g}
      mul_mem' := by
        rintro g h ⟨hg1, hg2, z₁, hz₁, hzg⟩ ⟨hh1, hh2, z₂, hz₂, hzh⟩
        have hgh : g * h = h * g := by
          refine commute_of_mk_commute_involution hh1 hh2 ?_
          rw [← hzg, ← hzh]
          exact congrArg Subtype.val (hcomm z₁ hz₁ z₂ hz₂)
        refine ⟨by rw [Units.val_mul, det_mul, hg1, hh1, one_mul], ?_,
          z₁ * z₂, Z.mul_mem hz₁ hz₂, by rw [Subgroup.coe_mul, hzg, hzh, map_mul]⟩
        calc g * h * (g * h) = g * (h * g) * h := by group
          _ = g * (g * h) * h := by rw [hgh]
          _ = (g * g) * (h * h) := by group
          _ = 1 := by rw [hg2, hh2, one_mul]
      one_mem' := ⟨by rw [Units.val_one, det_one], one_mul 1, 1, Z.one_mem, by
        rw [map_one]; rfl⟩
      inv_mem' := by
        rintro g ⟨hg1, hg2, hz⟩
        have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
        rw [hgi]
        exact ⟨hg1, hg2, hz⟩ }
  have : Finite (GL (Fin 3) K) := Finite.of_injective _ Units.val_injective
  have hle : Nat.card Zt ≤ 4 :=
    CFSG.RankThree.SubgroupLists.card_le_four_of_sq_eq_one_sl3 h2 Zt (fun x hx => hx.2.1)
      (fun x hx => hx.1)
  refine le_trans (Nat.card_le_card_of_surjective
    (fun g : Zt => (⟨⟨ProjGenLinGroup.mk (g : GL (Fin 3) K),
      ⟨g, (mem_slPi_true q).mpr g.2.1, rfl⟩⟩, by
        obtain ⟨z, hz, hzg⟩ := g.2.2.2
        have : (⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), ⟨g, (mem_slPi_true q).mpr g.2.1, rfl⟩⟩ :
          projImage (slPi true 3 q K)) = z := Subtype.ext hzg.symm
        rw [this]
        exact hz⟩ : Z)) ?_) hle
  rintro ⟨z, hz⟩
  obtain ⟨g, hgS, hgz, hg2⟩ := exists_lift_sq_eq_one (hsq z hz)
  refine ⟨⟨g, (mem_slPi_true q).mp hgS, hg2, z, hz, hgz.symm⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hgz

theorem commute_of_mem_normalizer_of_card_lt {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {Z : Subgroup G} {x : G} {k : ℕ} (hx : x ^ p ^ k = 1)
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hZ : Nat.card Z < p) :
    ∀ z ∈ Z, x * z = z * x := by
  classical
  have hmem : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z := fun z hz => (Subgroup.mem_normalizer_iff.mp hxZ z).mp hz
  let fZ : Function.End ↥Z := fun z => ⟨x * z * x⁻¹, hmem z z.2⟩
  have hfpow : ∀ (n : ℕ) (z : ↥Z), (((fZ ^ n) z : ↥Z) : G) = x ^ n * z * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z; simp; rfl
    | succ n ih =>
      intro z
      rw [pow_succ]
      change (((fZ ^ n) (fZ z) : ↥Z) : G) = _
      rw [ih]
      change x ^ n * (x * z * x⁻¹) * (x ^ n)⁻¹ = _
      rw [pow_succ]
      group
  have hfr : fZ ^ p ^ k = 1 := by
    funext z
    apply Subtype.ext
    rw [hfpow, hx, one_mul, inv_one, mul_one]
    rfl
  set F := Z ⊓ Subgroup.centralizer ({x} : Set G) with hF
  have hfix : Nat.card ↥(Function.fixedPoints fZ) = Nat.card F := by
    refine Nat.card_congr ⟨fun z => ⟨z.1, z.1.2, ?_⟩, fun y => ⟨⟨y, y.2.1⟩, ?_⟩, ?_, ?_⟩
    · have h := congrArg Subtype.val (z.2 : fZ z.1 = z.1)
      change x * (z.1 : G) * x⁻¹ = z.1 at h
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc (z.1 : G) * x = x * z.1 * x⁻¹ * x := by rw [h]
        _ = x * z.1 := by group
    · apply Subtype.ext
      change x * (y : G) * x⁻¹ = y
      have h := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
      rw [← h]
      group
    · intro z
      rfl
    · intro y
      rfl
  have : Fintype ↥Z := Fintype.ofFinite _
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := k) hfr
  simp only [← Nat.card_eq_fintype_card] at hmod
  rw [hfix] at hmod
  have hFZ : Nat.card F ≤ Nat.card Z := Subgroup.card_le_of_le inf_le_left
  have heq : Nat.card Z = Nat.card F :=
    Nat.ModEq.eq_of_lt_of_lt hmod hZ (lt_of_le_of_lt hFZ hZ)
  have hFeq : F = Z := Subgroup.eq_of_le_of_card_ge inf_le_left heq.le
  intro z hz
  have hzF : z ∈ F := hFeq ▸ hz
  exact (Subgroup.mem_centralizer_singleton_iff.mp hzF.2).symm

theorem not_pow_three_dvd_card_normalizer [Finite K] {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = p ^ 2) (N : Subgroup (projImage (slPi true 3 q K))) (hN : N ≠ ⊥)
    (hN2 : IsPGroup 2 N) :
    ¬ p ^ 3 ∣ Nat.card (Subgroup.normalizer (N : Set (projImage (slPi true 3 q K)))) := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (GL (Fin 3) K) := Finite.of_injective _ Units.val_injective
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective _ (ProjGenLinGroup.mk_surjective (n := Fin 3) (R := K))
  have hchar : CharP K p := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := ↥(Subgroup.normalizer (N : Set (projImage (slPi true 3 q K))))) p hdvd
  set P := P₀.map (Subgroup.normalizer (N : Set (projImage (slPi true 3 q K)))).subtype with hPdef
  have hPN : P ≤ Subgroup.normalizer (N : Set (projImage (slPi true 3 q K))) :=
    Subgroup.map_subtype_le _
  have hP : Nat.card P = p ^ 3 := by
    rw [hPdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hP₀]
  let Z0 : Subgroup (projImage (slPi true 3 q K)) :=
    { carrier := {z | z ∈ N ∧ (∀ n ∈ N, z * n = n * z) ∧ z * z = 1}
      mul_mem' := by
        rintro a b ⟨haN, hac, ha2⟩ ⟨hbN, hbc, hb2⟩
        refine ⟨N.mul_mem haN hbN, fun n hn => ?_, ?_⟩
        · rw [mul_assoc, hbc n hn, ← mul_assoc, hac n hn, mul_assoc]
        · calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hbc a haN]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2, one_mul]
      one_mem' := ⟨N.one_mem, fun n _ => by rw [one_mul, mul_one], mul_one 1⟩
      inv_mem' := by
        rintro a ⟨haN, hac, ha2⟩
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [hai]
        exact ⟨haN, hac, ha2⟩ }
  obtain ⟨t, htZ, ht1⟩ : ∃ t ∈ Z0, t ≠ 1 := by
    have hnt : Nontrivial N := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      exact hN
    have hZn := hN2.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center N)
    have hzp : IsPGroup 2 (Subgroup.center N) := hN2.to_subgroup _
    have h2c : 2 ∣ Nat.card (Subgroup.center N) := by
      obtain ⟨n, hn⟩ := hzp.exists_card_eq
      rcases n with _ | n
      · exfalso
        apply hz1
        rw [pow_zero] at hn
        have := (Nat.card_eq_one_iff_unique.mp hn).1
        exact Subsingleton.elim _ _
      · rw [hn, pow_succ]
        exact dvd_mul_left _ _
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2c
    refine ⟨((w : N) : projImage (slPi true 3 q K)), ⟨(w : N).2, fun n hn => ?_, ?_⟩, ?_⟩
    · have := Subgroup.mem_center_iff.mp w.2 ⟨n, hn⟩
      exact (congrArg Subtype.val this).symm
    · have h := pow_orderOf_eq_one w
      rw [hw, pow_two] at h
      exact congrArg (fun y : Subgroup.center N => ((y : N) : projImage (slPi true 3 q K))) h
    · intro h1
      have : w = 1 := Subtype.ext (Subtype.ext h1)
      rw [this, orderOf_one] at hw
      norm_num at hw
  have hZ4 : Nat.card Z0 ≤ 4 := card_le_four_of_sq_eq_one h2 Z0 (fun z hz => hz.2.2)
    (fun a ha b hb => ha.2.1 b hb.1)
  have hPt : ∀ x ∈ P, x * t = t * x := by
    intro x hx
    have hxp : x ^ p ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ↥P) (x := ⟨x, hx⟩)
      rw [hP] at h
      exact congrArg Subtype.val h
    have hxZ : x ∈ Subgroup.normalizer (Z0 : Set (projImage (slPi true 3 q K))) := by
      have hxN := hPN hx
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      obtain ⟨hzN, hzc, hz2⟩ := hz
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxN z).mp hzN, fun n hn => ?_, ?_⟩
      · have hn' : x⁻¹ * n * x⁻¹⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) n).mp hn
        have h := hzc _ hn'
        calc x * z * x⁻¹ * n = x * (z * (x⁻¹ * n * x⁻¹⁻¹)) * x⁻¹ := by group
          _ = x * ((x⁻¹ * n * x⁻¹⁻¹) * z) * x⁻¹ := by rw [h]
          _ = n * (x * z * x⁻¹) := by group
      · calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
          _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    exact commute_of_mem_normalizer_of_card_lt hxp hxZ (by omega) t htZ
  obtain ⟨tt, htt, httm, htt2⟩ := exists_lift_sq_eq_one htZ.2.2
  have httd : (tt : Matrix (Fin 3) (Fin 3) K).det = 1 := (mem_slPi_true q).mp htt
  have htt1 : tt ≠ 1 := by
    intro h
    apply ht1
    apply Subtype.ext
    rw [← httm, h, map_one]
    rfl
  set Pt : Subgroup (GL (Fin 3) K) := slPi true 3 q K ⊓
    (P.map (projImage (slPi true 3 q K)).subtype).comap ProjGenLinGroup.mk with hPtdef
  have hPtc : ∀ g ∈ Pt, g * tt = tt * g := by
    rintro g ⟨hgS, ⟨m, hmP, hmg⟩⟩
    refine commute_of_mk_commute_involution httd htt2 ?_
    rw [← hmg, httm]
    exact congrArg Subtype.val (hPt m hmP)
  obtain ⟨ρ, hρ, -⟩ := CFSG.RankThree.SubgroupLists.exists_injective_gl2_of_commute h2 htt2 htt1
    httd Pt hPtc (fun g hg => (mem_slPi_true q).mp hg.1)
  have hdvd1 : Nat.card Pt ∣ Nat.card (GL (Fin 2) K) := Subgroup.card_dvd_of_injective ρ hρ
  let φ : Pt →* P :=
    { toFun := fun g => ⟨⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), ⟨g, g.2.1, rfl⟩⟩, by
        obtain ⟨m, hmP, hmg⟩ := g.2.2
        have : (⟨ProjGenLinGroup.mk (g : GL (Fin 3) K), ⟨g, g.2.1, rfl⟩⟩ :
          projImage (slPi true 3 q K)) = m := Subtype.ext hmg.symm
        rw [this]
        exact hmP⟩
      map_one' := Subtype.ext (Subtype.ext (map_one _))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (map_mul _ _ _)) }
  have hφ : Function.Surjective φ := by
    rintro ⟨m, hmP⟩
    obtain ⟨g, hg, hgm⟩ := m.2
    refine ⟨⟨g, hg, m, hmP, hgm.symm⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hgm
  have hdvd2 : Nat.card P ∣ Nat.card Pt := Subgroup.card_dvd_of_surjective hφ
  rw [hP] at hdvd2
  have hGL : Nat.card (GL (Fin 2) K) = (p ^ 4 - 1) * (p ^ 4 - p ^ 2) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hK]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    ring_nf
  have hall := hdvd2.trans (hdvd1.trans (dvd_of_eq hGL))
  have hp1 : 1 < p := hp.one_lt
  have e : (p ^ 4 - 1) * (p ^ 4 - p ^ 2) = p ^ 2 * ((p ^ 4 - 1) * (p ^ 2 - 1)) := by
    have : p ^ 4 - p ^ 2 = p ^ 2 * (p ^ 2 - 1) := by
      rw [Nat.mul_sub_one, ← pow_add]
    rw [this]
    ring
  rw [e, show p ^ 3 = p ^ 2 * p by ring] at hall
  have hm := Nat.dvd_of_mul_dvd_mul_left (by positivity) hall
  have hsub : ∀ k : ℕ, 1 ≤ k → ¬ p ∣ p ^ k - 1 := by
    intro k hk h
    have h1 : p ∣ p ^ k := dvd_pow_self p (by omega)
    have h2 := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
  rcases (Nat.Prime.dvd_mul hp).mp hm with h | h
  · exact hsub 4 (by norm_num) h
  · exact hsub 2 (by norm_num) h

end KL3FactsProof

open KL3FactsProof

theorem ks1518InvRank : KS1518InvRank := by
  intro X _ _ p e _ hp2 he hiso
  obtain ⟨π, K, _, hK, hq, ⟨ψ⟩⟩ := Sec13.exists_projImage_model he hiso
  have := hK.finite
  obtain ⟨E, hEC, hE, hEcard⟩ : ∃ E : Subgroup (projImage (slPi π 3 (p ^ e) K)),
      E ≤ Subgroup.centralizer {tM hK hp2 _ isTInv_tOne} ∧ CFSG.Assembly.IsElemAbelian p E ∧
      Nat.card E = p ^ e := by
    cases π
    · have h := hK.unitary
      obtain ⟨u, hu⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_bar_mul_eq_neg_one h
      obtain ⟨E, h1, h2, h3⟩ := exists_elemAbelian_of_sqZero hK hp2 (uniRoot h u)
        (uniRoot_injective h u) (uniRoot_mul h hu)
        (fun x => Subtype.ext (by
          rw [AddSubgroup.coe_nsmul, nsmul_eq_zero_of_piField hK, AddSubgroup.coe_zero]))
        (uniRoot_mem h hu) (uniRoot_comm h hu)
      exact ⟨E, h1, h2, h3.trans h.card_traceZero⟩
    · obtain ⟨E, h1, h2, h3⟩ := exists_elemAbelian_of_sqZero hK hp2 linRoot linRoot_injective
        linRoot_mul (nsmul_eq_zero_of_piField hK) (linRoot_mem _) linRoot_comm
      exact ⟨E, h1, h2, h3.trans hK.card⟩
  refine ⟨ψ.symm (tM hK hp2 _ isTInv_tOne), ?_, E.map ψ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (tM_sq hK hp2 _) (tM_ne_one hK hp2 _)
  · rw [← CFSG.RankThree.PartTwo.KFacts.KP4.map_centralizer_singleton]
    exact Subgroup.map_mono hEC
  · exact CFSG.SectionRank.isElemAbelian_map hE _
  · rw [Subgroup.card_map_of_injective ψ.symm.injective, hEcard]

theorem ks1518PRank : KS1518PRank := by
  intro X _ _ p f _ hp2 hf hX
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h6 : 2 * f ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
    rcases hX with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have := Sec17.HeadProof.finite_projGenLinGroup_three (GaloisField p f)
      have h := Sec17.HeadProof.two_mul_le_pRank_projSL_three (GaloisField p f) (p := p)
        (GaloisField.card p f (by omega))
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
      rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ]
    · have := Sec17.HeadProof.finite_projGenLinGroup_three (GaloisField p (2 * f))
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 φ]
      exact Sec17.HeadProof.two_mul_le_pRank_projSU_three hp2
  obtain ⟨E, -, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (k := 3) (H := ⊤)
      (by omega)
  exact ⟨E, hE, hEcard⟩

theorem ks1518TwoLoc : KS1518TwoLoc := by
  intro X _ _ p _ hp2 hiso N hN hN2 hdvd
  have hp : p.Prime := Fact.out
  have hmod : p ^ 2 % 3 = (p % 3) ^ 2 % 3 := Nat.pow_mod p 2 3
  rcases hiso with ⟨h31, ⟨φ⟩⟩ | ⟨h32, -⟩
  · have hp3 : p ≠ 3 := by
      rintro rfl
      norm_num at h31
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      by_contra h
      interval_cases p <;> simp_all (config := {decide := true})
    set K := GaloisField p 2
    have hK : Nat.card K = p ^ 2 := GaloisField.card p 2 (by norm_num)
    have ψ : X ≃* projImage (slPi true 3 (p ^ 2) K) :=
      φ.trans (MulEquiv.subgroupCongr (projSL_eq_projImage (p ^ 2) K))
    have hN' : N.map ψ.toMonoidHom ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective]
      exact hN
    have hN2' : IsPGroup 2 (N.map ψ.toMonoidHom) := hN2.map _
    refine not_pow_three_dvd_card_normalizer hp hp5 hK _ hN' hN2' ?_
    rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective ψ.injective]
    exact hdvd
  · exfalso
    have : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : p % 3 <;> simp_all

theorem step1518Read : Step1518Read :=
  step1518Read_of ks1518InvRank ks1518PRank ks1518TwoLoc

end CFSG.RankThree.PartTwo.Sec15
