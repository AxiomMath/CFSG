module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411J1Group
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order
import CFSG.Sporadic.J1

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.Blueprint

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem relIndex_centralizer_conj {I : Subgroup X} (hI : I.Normal) (g x : X) :
    (centralizer ({g * x * g⁻¹} : Set X)).relIndex I =
      (centralizer ({x} : Set X)).relIndex I := by
  have hcomap : (centralizer ({g * x * g⁻¹} : Set X)).comap
      (MulAut.conj g).toMonoidHom = centralizer ({x} : Set X) := by
    ext y
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := hy.symm
          _ = g * (y * x) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    · intro hy
      calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hy]
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  rw [← hcomap, Subgroup.relIndex_comap]
  congr 1
  exact (Subgroup.normal_iff_map_conj_eq.mp hI g).symm

theorem noSmall1411_of_J1
    (h : Hyp1411 X L S)
    (hJ : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃* NativeSporadic.J1)) :
    NoSmall1411 X L S := by
  obtain ⟨e⟩ := hJ
  intro I hIn hI hLI t htS htQ htt
  by_contra hle
  push Not at hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  have := CFSG.Sporadic.J1.isSimpleGroup_J1
  have hsimp : IsSimpleGroup ↥(L.map π) := e.isSimpleGroup
  have hZ : center ↥(L.map π) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ center NativeSporadic.J1 := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨w, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, hz w]
    rw [center_J1_eq_bot, Subgroup.mem_bot] at hez
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hez, map_one])
  obtain ⟨l₀, hl₀L, hl₀⟩ := exists_not_commute_of_hyp1411 h hZ htS htQ
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  set φ : MulAut NativeSporadic.J1 := e.symm.trans (ψ.trans e) with hφ
  have hψ2 : ψ * ψ = 1 := by
    rw [hψ, ← map_mul, ← map_mul, htt, map_one, map_one]
  have hφ2 : φ * φ = 1 := by
    refine MulEquiv.ext fun x => ?_
    have := congrArg (fun f : MulAut ↥(L.map π) => e (f (e.symm x))) hψ2
    simpa [hφ] using this
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hl₀
    have hmem : π l₀ ∈ L.map π := ⟨l₀, hl₀L, rfl⟩
    have h2 := congrArg (fun f : MulAut NativeSporadic.J1 => e.symm (f (e ⟨π l₀, hmem⟩))) h1
    simp only [hφ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
    have h3 := congrArg Subtype.val h2
    rw [hψ, MulAut.conjNormal_apply] at h3
    calc π t * π l₀ = π t * π l₀ * (π t)⁻¹ * π t := by group
      _ = π l₀ * π t := by rw [h3]
  obtain ⟨x, hx⟩ := exists_orderOf_mul_inv_eq_nineteen_J1 φ hφ2 hφ1
  have hord : orderOf (ψ (e.symm x) * (e.symm x)⁻¹) = 19 := by
    rw [← MulEquiv.orderOf_eq e, map_mul, map_inv]
    simpa [hφ] using hx
  obtain ⟨ℓ, -, hℓ⟩ := (e.symm x).2
  have hu : t ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top t
  have hv : ℓ * t⁻¹ * ℓ⁻¹ ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have hvb : (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4 := by
    rw [relIndex_centralizer_conj hIn, inv_eq_of_mul_eq_one_right htt]
    exact hle
  have hpow := pow_mem_centralizer_of_relIndex_le hI hu hv hle hvb
  have himg : π (t * (ℓ * t⁻¹ * ℓ⁻¹)) =
      ((ψ (e.symm x) * (e.symm x)⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ]
    simp only [map_mul, map_inv]
    group
  have hbot := map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  have h1 : (ψ (e.symm x) * (e.symm x)⁻¹) ^ (2 * (4 * 4).factorial) = 1 := by
    apply Subtype.ext
    have hmem : ((((ψ (e.symm x) * (e.symm x)⁻¹) ^ (2 * (4 * 4).factorial) : ↥(L.map π))) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at hdvd
  have hp : Nat.Prime 19 := by norm_num
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | h2
  · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by norm_num)
  · exact absurd ((Nat.Prime.dvd_factorial hp).mp h2) (by norm_num)

end CFSG.RankThree.PartTwo.Sec20
