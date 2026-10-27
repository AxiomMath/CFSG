module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

@[expose] def IsPGLAct (π : Bool) (p f : ℕ) (K : Type) [Field K]
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) : Prop :=
  ∃ y ∈ glPi π 3 (p ^ f) K, ∀ m : projImage (slPi π 3 (p ^ f) K),
    (β m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹

@[expose] def IsFieldAct (π : Bool) (p f : ℕ) (K : Type) [Field K]
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) : Prop :=
  ∃ f₀ : ℕ, f = 3 * f₀ ∧ ∃ σ : K ≃+* K,
    ((∀ c, σ c = c ^ piCard π (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (p ^ f₀) ^ 2)) ∧
    ∃ g ∈ glPi π 3 (p ^ f) K, ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) = pmk (g * frobGL σ s * g⁻¹)

structure CentConfig (π : Bool) (p f : ℕ) (K : Type) [Field K] {ι : Type*}
    (α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))) (e₀ : projImage (slPi π 3 (p ^ f) K)) :
    Prop where
  fix : ∀ x, α x e₀ = e₀
  pow_three : ∀ x, α x ^ 3 = 1
  comm : ∀ x y, α x * α y = α y * α x
  conj_e : ∃ x, α x = MulAut.conj e₀
  hV : ∀ W : Subgroup (projImage (slPi π 3 (p ^ f) K)), ¬ 3 ∣ Nat.card W →
    (∀ x, ∀ w ∈ W, α x w ∈ W) → ∀ x, ∀ w ∈ W, α x w = w
  hF3 : ∀ u, u ^ 3 = 1 → (∀ x, α x u = u) → u ∈ Subgroup.zpowers e₀
  dich : ∀ x, IsPGLAct π p f K (α x) ∨ IsFieldAct π p f K (α x)

theorem mulAut_conj_apply_eq {G : Type*} [Group G] (β : MulAut G) (u : G) :
    MulAut.conj (β u) = β * MulAut.conj u * β⁻¹ := by
  ext m
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem eq_one_of_conj_eq_one (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {u : projImage (slPi π 3 (p ^ f) K)} (h : MulAut.conj u = 1) : u = 1 := by
  have := Sec13.isPerfect_projImage_slPi hK hq2
  have hc : u ∈ Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
    rw [Subgroup.mem_center_iff]
    intro m
    have h1 := congrArg (fun β : MulAut (projImage (slPi π 3 (p ^ f) K)) => β m) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc m * u = u * m * u⁻¹ * u := by rw [h1]
      _ = u * m := by group
  rw [center_projImage_eq_bot hK hq] at hc
  exact hc

variable {ι : Type*} {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))}
  {e₀ : projImage (slPi π 3 (p ^ f) K)}

theorem CentConfig.mem_zpowers_of_conj (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (hc : CentConfig π p f K α e₀) {x : ι}
    {u : projImage (slPi π 3 (p ^ f) K)} (hu : α x = MulAut.conj u) :
    u ∈ Subgroup.zpowers e₀ := by
  refine hc.hF3 u ?_ fun y => ?_
  · apply eq_one_of_conj_eq_one hK hq hq2
    rw [map_pow, ← hu, hc.pow_three x]
  · have h1 : MulAut.conj (α y u) = MulAut.conj u := by
      rw [mulAut_conj_apply_eq, ← hu, hc.comm y x, mul_inv_cancel_right]
    have h2 : α y u * u⁻¹ = 1 :=
      eq_one_of_conj_eq_one hK hq hq2 (by rw [map_mul, map_inv, h1, mul_inv_cancel])
    exact mul_inv_eq_one.mp h2

theorem CentConfig.mem_zpowers_of_inner (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (hc : CentConfig π p f K α e₀)
    (hinner : ∀ x, ∃ u : projImage (slPi π 3 (p ^ f) K), α x = MulAut.conj u)
    {w : projImage (slPi π 3 (p ^ f) K)} (hwe : w * e₀ = e₀ * w) (hw3 : w ^ 3 = 1) :
    w ∈ Subgroup.zpowers e₀ := by
  refine hc.hF3 w hw3 fun x => ?_
  obtain ⟨u, hu⟩ := hinner x
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hc.mem_zpowers_of_conj hK hq hq2 hu)
  have hcomm : Commute (e₀ ^ k) w := Commute.zpow_left hwe.symm k
  rw [hu, MulAut.conj_apply, hcomm.eq, mul_inv_cancel_right]

theorem pow_three_mem_scalars (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f)
    {β : MulAut (projImage (slPi π 3 (p ^ f) K))} (hβ3 : β ^ 3 = 1) {y : GL (Fin 3) K}
    (hy : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (β m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹) :
    y ^ 3 ∈ StatedScalars (Fin 3) K := by
  have := Sec13.isPerfect_projImage_slPi hK hq2
  refine mem_statedScalars_of_comm_mod hK hq fun s hs => ?_
  rw [← mk_eq_one_iff_mem_statedScalars]
  have h1 : ((β ^ 3) (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
      pmk y * (pmk y * (pmk y * pmk s * (pmk y)⁻¹) * (pmk y)⁻¹) * (pmk y)⁻¹ := by
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hy, hy, hy, coe_projOf]
  rw [hβ3, MulAut.one_apply, coe_projOf] at h1
  have hy3 : pmk (y ^ 3) = pmk y * pmk y * pmk y := by rw [map_pow, pow_succ, pow_succ, pow_one]
  calc pmk (y ^ 3 * s * (y ^ 3)⁻¹ * s⁻¹)
      = pmk y * (pmk y * (pmk y * pmk s * (pmk y)⁻¹) * (pmk y)⁻¹) * (pmk y)⁻¹ * (pmk s)⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy3]
        group
    _ = 1 := by rw [← h1, mul_inv_cancel]

theorem exists_conj_eq_scalar_mul {β : MulAut (projImage (slPi π 3 (p ^ f) K))}
    {y : GL (Fin 3) K}
    (hy : ∀ m : projImage (slPi π 3 (p ^ f) K),
      (β m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹)
    (hfix : β e₀ = e₀) {d : GL (Fin 3) K} (hd : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk d) :
    ∃ c : Kˣ, y * d * y⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * d := by
  have h1 := hy e₀
  rw [hfix, hd, ← map_inv, ← map_mul, ← map_mul] at h1
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
  refine ⟨u, ?_⟩
  rw [← hu]
  exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u d).eq

theorem exists_frob_conj_eq_scalar_mul {β : MulAut (projImage (slPi π 3 (p ^ f) K))}
    {σ : K ≃+* K} {g : GL (Fin 3) K}
    (hg : ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
      (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) = pmk (g * frobGL σ s * g⁻¹))
    (hfix : β e₀ = e₀) {s₀ : GL (Fin 3) K} (hs₀ : s₀ ∈ slPi π 3 (p ^ f) K)
    (hd : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk s₀) :
    ∃ c : Kˣ, g * frobGL σ s₀ * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * s₀ := by
  have he : e₀ = projOf _ ⟨s₀, hs₀⟩ := Subtype.ext (by rw [coe_projOf, hd])
  have h1 : (β e₀ : ProjGenLinGroup (Fin 3) K) = pmk (g * frobGL σ s₀ * g⁻¹) := by
    rw [he]
    exact hg s₀ hs₀
  rw [hfix, hd] at h1
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h1
  refine ⟨u, ?_⟩
  rw [← hu]
  exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u s₀).eq

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
