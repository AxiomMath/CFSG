module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardAbs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofFrame
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item423ResProof432
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Cover
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

namespace L3Hard

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec12

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem cycThree_mul_scalar_ne_diagUnits (u a b c : Kˣ) :
    (cycThree : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) u ≠ diagUnits a b c := by
  intro h
  have e1 : (((cycThree : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 2 = (u : K) := by
    simp [coe_cycThree, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_diagonal]
  have e2 : ((diagUnits a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 := by
    simp [coe_diagUnits, Matrix.diagonal_apply]
  have h02 : (((cycThree : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 2 = ((diagUnits a b c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 := by
    rw [h]
  rw [e1, e2] at h02
  exact u.ne_zero h02

theorem mk_cycThree_ne_mk_diagUnits (a b c : Kˣ) :
    pmk (cycThree : GL (Fin 3) K) ≠ pmk (diagUnits a b c : GL (Fin 3) K) := by
  intro h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  exact cycThree_mul_scalar_ne_diagUnits u a b c hu

theorem cycThree_cube : (cycThree : GL (Fin 3) K) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_cycThree, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem mk_commute_cycThree_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    pmk (cycThree : GL (Fin 3) K) * pmk (diagTau hτ) =
      pmk (diagTau hτ) * pmk (cycThree : GL (Fin 3) K) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h := cycThree_pow_conj_diagTau hτ hτ0 1
  rw [pow_one] at h
  exact hom_commute_of_conj_eq (pmk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) h
    (ProjGenLinGroup.mk_scalar _)

theorem mk_cycThree_notMem_zpowers {τ : K} (hτ : τ ^ 3 = 1) :
    pmk (cycThree : GL (Fin 3) K) ∉ Subgroup.zpowers (pmk (diagTau hτ)) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  have h3 : pmk (diagTau hτ) ^ 3 = 1 := by
    rw [← map_pow, diagTau_pow_three hτ, map_one]
  intro hmem
  rcases mem_zpowers_cases_of_pow_three h3 hmem with h | h | h
  · refine mk_cycThree_ne_mk_diagUnits (K := K) 1 1 1 ?_
    rw [h, KS128Move.diagUnits_one, map_one]
  · refine mk_cycThree_ne_mk_diagUnits (Units.mk0 τ hτ0) (Units.mk0 τ hτ0 ^ 2) 1 ?_
    rw [h, diagTau_eq_diagUnits hτ hτ0]
  · refine mk_cycThree_ne_mk_diagUnits (Units.mk0 τ hτ0)⁻¹ (Units.mk0 τ hτ0 ^ 2)⁻¹ 1⁻¹ ?_
    rw [h, ← map_inv, diagTau_eq_diagUnits hτ hτ0, KS128Move.diagUnits_inv]

theorem mk_diagUnits_eq_iff (a b c a' b' c' : Kˣ) :
    pmk (diagUnits a b c : GL (Fin 3) K) = pmk (diagUnits a' b' c' : GL (Fin 3) K) ↔
      ∃ u : Kˣ, a * u = a' ∧ b * u = b' ∧ c * u = c' := by
  rw [ProjGenLinGroup.mk_eq_mk_iff]
  refine exists_congr fun u => ?_
  rw [KS128Move.scalar_eq_diagUnits, diagUnits_mul, KS128Move.diagUnits_eq_iff]

theorem mk_commute_diagUnits_diagE (e : Kˣ) :
    pmk (diagUnits 1 e 1 : GL (Fin 3) K) * pmk (diagE e) =
      pmk (diagE e) * pmk (diagUnits 1 e 1 : GL (Fin 3) K) := by
  rw [← map_mul, ← map_mul]
  exact congrArg (fun w : GL (Fin 3) K => pmk w) (KS128Move.diagUnits_comm 1 e 1 e 1 1)

theorem mk_diagUnits_notMem_zpowers {e : Kˣ} (he3 : (e : K) ^ 3 = 1) (he1 : e ≠ 1) :
    pmk (diagUnits 1 e 1 : GL (Fin 3) K) ∉ Subgroup.zpowers (pmk (diagE e)) := by
  have h3 : pmk (diagE e) ^ 3 = 1 := by
    rw [← map_pow, diagE_pow_three he3, map_one]
  intro hmem
  rcases mem_zpowers_cases_of_pow_three h3 hmem with h | h | h
  · have h' : pmk (diagUnits 1 e 1 : GL (Fin 3) K) = pmk (diagUnits 1 1 1 : GL (Fin 3) K) := by
      rw [h, KS128Move.diagUnits_one, map_one]
    obtain ⟨u, h1, h2, -⟩ := (mk_diagUnits_eq_iff _ _ _ _ _ _).mp h'
    have hu : u = 1 := by simpa using h1
    subst hu
    exact he1 (by simpa using h2)
  · have h' : pmk (diagUnits 1 e 1 : GL (Fin 3) K) = pmk (diagUnits e 1 1 : GL (Fin 3) K) := h
    obtain ⟨u, h1, -, h3'⟩ := (mk_diagUnits_eq_iff _ _ _ _ _ _).mp h'
    have hu : u = 1 := by simpa using h3'
    subst hu
    exact he1 (by simpa using h1.symm)
  · have h' : pmk (diagUnits 1 e 1 : GL (Fin 3) K) = pmk (diagUnits e⁻¹ 1⁻¹ 1⁻¹ : GL (Fin 3) K) := by
      rw [h, ← map_inv]
      exact congrArg (fun w : GL (Fin 3) K => pmk w) (KS128Move.diagUnits_inv e 1 1)
    obtain ⟨u, h1, -, h3'⟩ := (mk_diagUnits_eq_iff _ _ _ _ _ _).mp h'
    have hu : u = 1 := by simpa using h3'
    subst hu
    exact he1 (by simpa using h1.symm)

theorem permGL_swap_conj_diagE (e : Kˣ) :
    Res417Frame.permGL (Equiv.swap (0 : Fin 3) 1) * diagE e *
        (Res417Frame.permGL (Equiv.swap (0 : Fin 3) 1))⁻¹ = (diagUnits 1 e 1 : GL (Fin 3) K) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagE, coe_diagUnits, Res417Frame.permGL_mul_diagonal]
  congr 2
  funext i
  have h2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  fin_cases i <;> simp [h2]

theorem exists_witness_of_typeOne (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {y g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hy : g⁻¹ * y * g = diagTau hτ) :
    ∃ t ∈ slPi π 3 (p ^ f) K,
      (pmk t * pmk y * (pmk t)⁻¹) * pmk y = pmk y * (pmk t * pmk y * (pmk t)⁻¹) ∧
        pmk t * pmk y * (pmk t)⁻¹ ∉ Subgroup.zpowers (pmk y) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcL : (cycThree : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := cycThree_mem_slPi hπ
  have hcZ : (cycThree : GL (Fin 3) K) ∉ zPi π 3 (p ^ f) K := by
    intro h
    obtain ⟨u, hu⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h
    refine mk_cycThree_ne_mk_diagUnits (K := K) 1 1 1 ?_
    rw [KS128Move.diagUnits_one, map_one, ← hu, ProjGenLinGroup.mk_scalar]
  have hc1 : (cycThree : GL (Fin 3) K) ≠ 1 := by
    intro h
    refine mk_cycThree_ne_mk_diagUnits (K := K) 1 1 1 ?_
    rw [KS128Move.diagUnits_one, h]
  have hco : orderOf (cycThree : GL (Fin 3) K) = 3 := orderOf_eq_prime cycThree_cube hc1
  obtain ⟨k0, hk0, hk0d⟩ := rank3II_4_10_three hK hq hτ hτ1 hcL hcZ hco
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin 3) K, u = diagUnits 1 1 (GeneralLinearGroup.det k0)⁻¹ :=
    ⟨_, rfl⟩
  have huH : u ∈ glPi π 3 (p ^ f) K := by
    rw [hu]
    exact diagUnits_mem_glPi hK (one_mem _) (one_mem _) (inv_mem (det_mem_rootsOfUnity hK hk0))
  have hdetu : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      (((GeneralLinearGroup.det k0)⁻¹ : Kˣ) : K) := by
    rw [hu, coe_diagUnits, det_diagonal, Fin.prod_univ_three]
    simp
  have hdet : ((k0 * u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Units.val_mul, det_mul, hdetu, ← GeneralLinearGroup.val_det_apply, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  have hkL : k0 * u ∈ slPi π 3 (p ^ f) K := (mem_slPi_iff hπ).mpr ⟨mul_mem hk0 huH, hdet⟩
  have hud : u * diagTau hτ = diagTau hτ * u := by
    rw [hu, diagTau_eq_diagUnits hτ hτ0]
    exact KS128Move.diagUnits_comm _ _ _ _ _ _
  have hkd : (k0 * u) * diagTau hτ * (k0 * u)⁻¹ = cycThree := by
    calc (k0 * u) * diagTau hτ * (k0 * u)⁻¹ = k0 * (u * diagTau hτ * u⁻¹) * k0⁻¹ := by group
      _ = k0 * diagTau hτ * k0⁻¹ := by rw [hud]; group
      _ = cycThree := (eq_conj_of_inv_conj hk0d).symm
  refine ⟨g * (k0 * u) * g⁻¹, conj_mem_slPi hπ hg hkL, ?_⟩
  have key := commute_notMem_of_hom_conj (pmk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K) hkd
    (mk_commute_cycThree_diagTau hτ)
    (mk_cycThree_notMem_zpowers hτ) (g := g) (t := g * (k0 * u) * g⁻¹) rfl
  have hy' := eq_conj_of_inv_conj hy
  subst hy'
  exact key

theorem exists_witness_of_typeTwo (hK : PiField π p f K) {e : Kˣ} (he3 : (e : K) ^ 3 = 1)
    (he1 : e ≠ 1) {y g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K)
    (hy : g⁻¹ * y * g = diagE e) :
    ∃ t ∈ slPi π 3 (p ^ f) K,
      (pmk t * pmk y * (pmk t)⁻¹) * pmk y = pmk y * (pmk t * pmk y * (pmk t)⁻¹) ∧
        pmk t * pmk y * (pmk t)⁻¹ ∉ Subgroup.zpowers (pmk y) := by
  obtain ⟨s, hsL, hs⟩ := Res424Six.exists_slPi_mk_permGL hK hg (Equiv.swap (0 : Fin 3) 1)
  refine ⟨s, hsL, ?_⟩
  have key := commute_notMem_of_hom_conj (pmk : GL (Fin 3) K →* ProjGenLinGroup (Fin 3) K)
    (permGL_swap_conj_diagE e)
    (mk_commute_diagUnits_diagE e) (mk_diagUnits_notMem_zpowers he3 he1) (g := g) (t := s) hs
  have hy' := eq_conj_of_inv_conj hy
  subst hy'
  exact key

theorem exists_witness_of_not_type_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K) (hxZ : x ∉ zPi π 3 (p ^ f) K)
    (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K) (hnot3 : ¬ Type123 π (p ^ f) K x 3) :
    ∃ t ∈ slPi π 3 (p ^ f) K,
      (pmk t * pmk x * (pmk t)⁻¹) * pmk x = pmk x * (pmk t * pmk x * (pmk t)⁻¹) ∧
        pmk t * pmk x * (pmk t)⁻¹ ∉ Subgroup.zpowers (pmk x) := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hmk : ∀ z ∈ zPi π 3 (p ^ f) K, pmk (x * z) = pmk x := by
    intro z hz
    rw [map_mul, mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz),
      mul_one]
  rcases type123_exhaust hK hq hxH hxZ hx3 with
    ⟨τ', hτ', hτ1', z, hz, g, hg, hD⟩ | ⟨e, he3, he1, z, hz, g, hg, hD⟩ | h3
  · obtain ⟨t, htL, h⟩ := exists_witness_of_typeOne hK hq hτ' hτ1' hg hD
    exact ⟨t, htL, by rwa [hmk z hz] at h⟩
  · obtain ⟨t, htL, h⟩ := exists_witness_of_typeTwo hK he3 he1 hg hD
    exact ⟨t, htL, by rwa [hmk z hz] at h⟩
  · exact absurd h3 hnot3

theorem exists_witness_of_order_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hxL : x ∈ slPi π 3 (p ^ f) K) (hxs : x ∉ StatedScalars (Fin 3) K)
    (hx3 : x ^ 3 ∈ StatedScalars (Fin 3) K) :
    ∃ t ∈ slPi π 3 (p ^ f) K,
      (pmk t * pmk x * (pmk t)⁻¹) * pmk x = pmk x * (pmk t * pmk x * (pmk t)⁻¹) ∧
        pmk t * pmk x * (pmk t)⁻¹ ∉ Subgroup.zpowers (pmk x) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hxH : x ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hxL
  have hxZ : x ∉ zPi π 3 (p ^ f) K := fun h =>
    hxs (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)
  have hx3Z : x ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.mpr ⟨pow_mem hxH 3, hx3⟩
  exact exists_witness_of_not_type_three hK hq hxH hxZ hx3Z fun h3 =>
    not_inner_of_type3 hK hq hxH h3 ⟨x, hxL, fun m _ => rfl⟩

end L3Hard

end CFSG.RankThree.PartTwo.Sec4.RonanK432
