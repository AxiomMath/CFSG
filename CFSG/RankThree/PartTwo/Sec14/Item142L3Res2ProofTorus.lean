module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJPGL
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

@[expose] def conjSL (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (x : slPi π 3 (p ^ f) K) : slPi π 3 (p ^ f) K :=
  ⟨g * x * g⁻¹, conj_mem_slPi hπ hg x.2⟩

theorem coe_conjSL (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (x : slPi π 3 (p ^ f) K) :
    ((conjSL hπ hg x : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = g * x * g⁻¹ :=
  rfl

theorem projOf_conjSL (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (x : slPi π 3 (p ^ f) K) :
    projOf (slPi π 3 (p ^ f) K) (conjSL hπ hg x) =
      Res8Hess.conjM' hπ hg (projOf (slPi π 3 (p ^ f) K) x) := by
  apply Subtype.ext
  rw [coe_projOf, Res8Hess.coe_conjM', coe_projOf, coe_conjSL, map_mul, map_mul, map_inv]

theorem finite_pgl [Finite K] : Finite (ProjGenLinGroup (Fin 3) K) := by
  unfold ProjGenLinGroup
  infer_instance

theorem projOf_eq_one_iff (x : slPi π 3 (p ^ f) K) :
    projOf (slPi π 3 (p ^ f) K) x = 1 ↔ (x : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
  rw [← MonoidHom.mem_ker, mem_ker_projOf]

@[expose] def torusU (π : Bool) (p f : ℕ) (K : Type) [Field K] (c : GL (Fin 3) K) :
    Subgroup (slPi π 3 (p ^ f) K) :=
  (Subgroup.centralizer {c}).comap (slPi π 3 (p ^ f) K).subtype

theorem mem_torusU {c : GL (Fin 3) K} {x : slPi π 3 (p ^ f) K} :
    x ∈ torusU π p f K c ↔ c * (x : GL (Fin 3) K) = x * c := by
  rw [torusU, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

theorem conjSL_mem_torusU (hπ : π = false → UnitaryFieldData p f K) {c h : GL (Fin 3) K}
    (hh : h ∈ glPi π 3 (p ^ f) K) {s : Kˣ}
    (hhc : h * c * h⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s * c)
    {x : slPi π 3 (p ^ f) K} (hx : x ∈ torusU π p f K c) : conjSL hπ hh x ∈ torusU π p f K c := by
  rw [mem_torusU] at hx ⊢
  rw [coe_conjSL]
  set z := Matrix.GeneralLinearGroup.scalar (Fin 3) s with hz
  have hzc : ∀ y : GL (Fin 3) K, y * z = z * y := fun y =>
    (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s y).eq
  set u : GL (Fin 3) K := (x : GL (Fin 3) K) with hu
  have hc : c = z⁻¹ * (h * c * h⁻¹) := by rw [hhc]; group
  have hzc' : ∀ y : GL (Fin 3) K, y * z⁻¹ = z⁻¹ * y := fun y => by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hzc, inv_mul_cancel_left]
  calc c * (h * u * h⁻¹) = z⁻¹ * (h * c * h⁻¹) * (h * u * h⁻¹) := by rw [← hc]
    _ = z⁻¹ * (h * (c * u) * h⁻¹) := by group
    _ = z⁻¹ * (h * (u * c) * h⁻¹) := by rw [hx]
    _ = z⁻¹ * ((h * u * h⁻¹) * (h * c * h⁻¹)) := by group
    _ = (h * u * h⁻¹) * (z⁻¹ * (h * c * h⁻¹)) := by
        rw [← mul_assoc, ← hzc' (h * u * h⁻¹), mul_assoc]
    _ = (h * u * h⁻¹) * c := by rw [← hc]

theorem torusU_mem_invSet142 [Finite K] (hπ : π = false → UnitaryFieldData p f K) {τ : K}
    (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (h3 : (3 : K) ≠ 0) {cβ c : GL (Fin 3) K}
    (hcβ : cβ ∈ glPi π 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi π 3 (p ^ f) K) {ν : K}
    (hc3 : (c : Matrix (Fin 3) (Fin 3) K) ^ 3 = ν • 1) (hν : ¬ ∃ μ : K, μ ^ 3 = ν) {s₁ s₂ : Kˣ}
    (h1 : cβ * c * cβ⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s₁ * c)
    (h2 : diagTau hτ * c * (diagTau hτ)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 3) s₂ * c) :
    (torusU π p f K c).map (projOf (slPi π 3 (p ^ f) K)) ∈
      invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd) := by
  have hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (c : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    eq_bot_or_eq_top_of_invariant (fun μ hμ => hν ⟨μ, hμ⟩) hc3 hW
  have := finite_pgl (K := K)
  refine ⟨L3PGL.not_three_dvd_card_of_pow_three ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ hg3
    have hs3 : (g : GL (Fin 3) K) ^ 3 ∈ StatedScalars (Fin 3) K := by
      rw [← map_pow, projOf_eq_one_iff] at hg3
      exact hg3
    have hdet : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      ((mem_slPi_iff (p := p) (f := f) hπ).mp g.2).2
    rw [projOf_eq_one_iff]
    by_contra hsZ
    exact Sec12.KS128NotHJTC.false_of_commute_irreducible hτ hτ1 h3 hdet hs3 hsZ
      (mem_torusU.mp hg) hirr
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨conjSL hπ hcβ g, conjSL_mem_torusU hπ hcβ h1 hg, projOf_conjSL hπ hcβ g⟩
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨conjSL hπ hd g, conjSL_mem_torusU hπ hd h2 hg, projOf_conjSL hπ hd g⟩

@[expose] def mU (q : ℕ) : ℕ := ordCompl[3] (q + 1)

theorem coprime_mU (q : ℕ) : Nat.Coprime (mU q) 3 :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
    (Nat.not_dvd_ordCompl Nat.prime_three (Nat.succ_ne_zero q)))

theorem mU_dvd (q : ℕ) : mU q ∣ q + 1 := Nat.ordCompl_dvd (q + 1) 3

@[expose] def diagMuU (p f : ℕ) (K : Type) [Field K] : Subgroup (slPi false 3 (p ^ f) K) :=
  (torusHom.comp ((rootsOfUnity (mU (p ^ f)) K).subtype.prodMap
    (rootsOfUnity (mU (p ^ f)) K).subtype)).range.comap (slPi false 3 (p ^ f) K).subtype

theorem mem_diagMuU {x : slPi false 3 (p ^ f) K} :
    x ∈ diagMuU p f K ↔ ∃ a b : Kˣ, a ∈ rootsOfUnity (mU (p ^ f)) K ∧
      b ∈ rootsOfUnity (mU (p ^ f)) K ∧ (x : GL (Fin 3) K) = torusHom (a, b) := by
  rw [diagMuU, Subgroup.mem_comap, Subgroup.coe_subtype, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩
    exact ⟨a, b, a.2, b.2, hab.symm⟩
  · rintro ⟨a, b, ha, hb, hx⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hx.symm⟩

theorem heisC_mul_diagonal (β a b c : K) :
    heisC β * diagonal ![a, b, c] = diagonal ![c, a, b] * heisC β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisC, Matrix.mul_apply, Matrix.diagonal_apply]
  all_goals ring

theorem conj_torusHom_heisC {β : K} {cβ : GL (Fin 3) K}
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) (a b : Kˣ) :
    cβ * torusHom (a, b) * cβ⁻¹ = torusHom ((a * b)⁻¹, a) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_torusHom, coe_torusHom, hcβm, heisC_mul_diagonal]
  congr 2
  funext i
  fin_cases i <;> simp

theorem diagMuU_mem_invSet142 [Finite K] (hπ : false = false → UnitaryFieldData p f K) {τ : K}
    (hτ : τ ^ 3 = 1) {β : K} {cβ : GL (Fin 3) K}
    (hcβ : cβ ∈ glPi false 3 (p ^ f) K) (hd : diagTau hτ ∈ glPi false 3 (p ^ f) K)
    (hcβm : (cβ : Matrix (Fin 3) (Fin 3) K) = heisC β) :
    (diagMuU p f K).map (projOf (slPi false 3 (p ^ f) K)) ∈
      invSet142 (Res8Hess.conjM' hπ hcβ) (Res8Hess.conjM' hπ hd) := by
  have := finite_pgl (K := K)
  refine ⟨L3PGL.not_three_dvd_card_of_pow_three ?_, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩ hg3
    obtain ⟨a, b, ha, hb, hgab⟩ := mem_diagMuU.mp hg
    have hgm : g ^ mU (p ^ f) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hgab, ← map_pow, Prod.pow_mk, (mem_rootsOfUnity _ _).mp ha,
        (mem_rootsOfUnity _ _).mp hb, ← Prod.one_eq_mk, map_one, Subgroup.coe_one]
    have hm : projOf (slPi false 3 (p ^ f) K) g ^ mU (p ^ f) = 1 := by
      rw [← map_pow, hgm, map_one]
    have := pow_gcd_eq_one.mpr ⟨hm, hg3⟩
    rwa [coprime_mU, pow_one] at this
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨a, b, ha, hb, hgab⟩ := mem_diagMuU.mp hg
    refine ⟨conjSL hπ hcβ g, mem_diagMuU.mpr ⟨(a * b)⁻¹, a, inv_mem (mul_mem ha hb), ha, ?_⟩,
      projOf_conjSL hπ hcβ g⟩
    rw [coe_conjSL, hgab]
    exact conj_torusHom_heisC hcβm a b
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨a, b, ha, hb, hgab⟩ := mem_diagMuU.mp hg
    refine ⟨conjSL hπ hd g, mem_diagMuU.mpr ⟨a, b, ha, hb, ?_⟩, projOf_conjSL hπ hd g⟩
    rw [coe_conjSL, hgab, mul_inv_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_torusHom, coe_diagTau_eq_diagonal,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _

end CFSG.RankThree.PartTwo.Sec14.L3PGLU
