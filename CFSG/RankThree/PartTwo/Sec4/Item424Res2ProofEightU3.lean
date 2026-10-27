module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofEightL3

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.SectionRank.OddCover (u3Mat)

namespace Item424Res2

open Res423Two Item434CharThree

section SU

variable {F : Type} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}

theorem ent01_conj {x y : SU σ 3} (hx : x ∈ heisU hσ) (hy : y ∈ heisU hσ) :
    ent01 (y * x * y⁻¹) = ent01 x := by
  rw [ent01_mul ((heisU hσ).mul_mem hy hx) ((heisU hσ).inv_mem hy), ent01_mul hy hx,
    ent01_inv hy]
  ring

theorem mem_lineU_conj {a₀ : F} {x y : SU σ 3} (hx : x ∈ lineU hσ a₀) (hy : y ∈ heisU hσ) :
    y * x * y⁻¹ ∈ lineU hσ a₀ := by
  obtain ⟨hxU, s, hs, hxs⟩ := hx
  exact ⟨(heisU hσ).mul_mem ((heisU hσ).mul_mem hy hxU) ((heisU hσ).inv_mem hy), s, hs,
    by rw [ent01_conj hxU hy, hxs]⟩

variable [CharP F 3]

theorem ent01_eq_zero_of_conj_mem_zpowers {a₀ : F} {x y : SU σ 3} (hx : x ∈ lineU hσ a₀)
    (hy : y ∈ heisU hσ) (hya : a₀ * σ (ent01 y) ≠ ent01 y * σ a₀)
    (h : y * x * y⁻¹ ∈ Subgroup.zpowers x) : ent01 x = 0 := by
  obtain ⟨hxU, s, hs, hxs⟩ := hx
  rcases eq_of_mem_zpowers_of_pow_three (pow_three_eq_one_of_mem_heisU hxU) h with h1 | h1 | h1
  · have h2 := congrArg ent01 h1
    rw [ent01_conj hxU hy] at h2
    rw [h2]
    simp [ent01]
  · have hyx : y * x = x * y := by
      calc y * x = y * x * y⁻¹ * y := by group
        _ = x * y := by rw [h1]
    rw [commute_iff_of_mem_heisU hy hxU, hxs, map_mul, hs] at hyx
    by_contra hne
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hxs
      exact hne hxs
    apply hya
    have h2 : s * (a₀ * σ (ent01 y) - ent01 y * σ a₀) = 0 := by linear_combination -hyx
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hs0)
  · have h2 := congrArg ent01 h1
    rw [ent01_conj hxU hy, sq, ent01_mul hxU hxU] at h2
    linear_combination -h2

theorem pow_three_eq_one_of_commute_regular {x w : SU σ 3} (hx : x ∈ heisU hσ)
    (hx0 : ent01 x ≠ 0) (hw : w * x = x * w) : w ^ 3 = 1 := by
  obtain ⟨b, hxm⟩ := exists_coe_eq_u3Mat_of_mem_heisU hx
  have hcomm := coe_mul_comm_of_commute hw
  rw [hxm] at hcomm
  obtain ⟨a', b', c', hwm, -⟩ := exists_eq_u3Mat_of_commute hx0
    (neg_ne_zero.mpr ((map_ne_zero σ).mpr hx0)) (det_coe_SU w) hcomm
  exact pow_three_eq_one_of_coe_eq_u3Mat hwm

end SU

theorem census424_of_u33 {X : Type} [Group X] [Finite X] (e : X ≃* projSU 3 3 1) :
    Census424 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF := card_galois_two_mul (e := 1) one_ne_zero
  have hσ := unitaryInvolution_involutive hF
  set σ := unitaryInvolution (GaloisField 3 (2 * 1)) 3 1 with hσdef
  intro D c d J h
  exfalso
  set θ : X ≃* SU σ 3 := e.trans (suEquivProjSU one_ne_zero).symm
  obtain ⟨g, a₀, ha₀, hle⟩ := exists_map_le_lineU one_ne_zero θ h.maximal.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  have hDF : D.map e'.toMonoidHom = lineU hσ a₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective e'.injective, h.card_eq]
    have h9 := card_lineU_le hF ha₀
    norm_num at h9
    exact h9
  have hmem : ∀ x ∈ D, e' x ∈ lineU hσ a₀ := fun x hx => by
    rw [← hDF]
    exact ⟨x, hx, rfl⟩
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hζ' : (ζ : GaloisField 3 (2 * 1)) + σ ζ = 0 := (mem_traceZero σ).mp ζ.2
  obtain ⟨-, y, -, b₁, -, hyL, -, -, hym, -⟩ :=
    exists_z_x_mem_lineU hF (a₀ := (ζ : GaloisField 3 (2 * 1)) * a₀)
  have hyU : y ∈ heisU hσ := lineU_le_heisU _ hyL
  have hy01 : ent01 y = ζ * a₀ := by
    rw [ent01, hym]
    simp [u3Mat]
  have hya : a₀ * σ (ent01 y) ≠ ent01 y * σ a₀ := by
    have h3 : (3 : GaloisField 3 (2 * 1)) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (GaloisField 3 (2 * 1)) 3
    have hσζ : σ ζ = -ζ := by linear_combination hζ'
    rw [hy01, map_mul, hσζ]
    intro hc
    have h2 : (ζ : GaloisField 3 (2 * 1)) * (a₀ * σ a₀) = 0 := by
      linear_combination hc + ζ * a₀ * σ a₀ * h3
    rcases mul_eq_zero.mp h2 with h2 | h2
    · exact hζ h2
    · rcases mul_eq_zero.mp h2 with h2 | h2
      · exact ha₀ h2
      · exact ha₀ ((map_eq_zero_iff σ σ.injective).mp h2)
  have hyN : e'.symm y ∈ Subgroup.normalizer (D : Set X) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 : y * e' x * y⁻¹ ∈ lineU hσ a₀ := mem_lineU_conj (hmem x hx) hyU
    rw [← hDF] at h1
    obtain ⟨x', hx', hxx'⟩ := h1
    have : e'.symm y * x * (e'.symm y)⁻¹ = x' := by
      apply e'.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hxx'.symm
    rw [this]
    exact hx'
  have hyd : e'.symm y * d * (e'.symm y)⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (h.normalizer_le hyN) d).mp (Subgroup.mem_zpowers d)
  have hyd' : y * e' d * y⁻¹ ∈ Subgroup.zpowers (e' d) := by
    have h1 := Subgroup.mem_map_of_mem e'.toMonoidHom hyd
    rw [MonoidHom.map_zpowers] at h1
    simpa using h1
  have hd0 : ent01 (e' d) = 0 :=
    ent01_eq_zero_of_conj_mem_zpowers (hmem d h.d_mem) hyU hya hyd'
  have hc0 : ent01 (e' c) ≠ 0 := by
    intro hc0
    have hcl := closure_pair_eq_of_card_nine h.card_eq h.c_mem h.d_mem h.c_ne_one
      (h.maximal.prop.2 c h.c_mem) h.d_not_mem
    have hZ : D ≤ (lineU hσ 0).comap e'.toMonoidHom := by
      rw [← hcl, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact ⟨(hmem z h.c_mem).1, 0, map_zero σ, by rw [MulEquiv.coe_toMonoidHom, hc0,
          zero_mul]⟩
      · exact ⟨(hmem z h.d_mem).1, 0, map_zero σ, by rw [MulEquiv.coe_toMonoidHom, hd0,
          zero_mul]⟩
    obtain ⟨-, x₀, -, b₂, -, hx₀L, -, -, hx₀m, -⟩ := exists_z_x_mem_lineU hF (a₀ := a₀)
    have hx₀ : x₀ ∈ D.map e'.toMonoidHom := by
      rw [hDF]
      exact hx₀L
    obtain ⟨x, hxD, hxe⟩ := hx₀
    obtain ⟨-, s', -, hs'⟩ := hZ hxD
    rw [hxe, mul_zero] at hs'
    apply ha₀
    rw [← hs', ent01, hx₀m]
    simp [u3Mat]
  apply not_isSolvable_centralizer h
  have hp : IsPGroup 3 (Subgroup.centralizer ({c} : Set X)) := by
    intro w
    refine ⟨1, Subtype.ext (e'.injective ?_)⟩
    have hw : (w : X) * c = c * w := Subgroup.mem_centralizer_singleton_iff.mp w.2
    have hw' : e' w * e' c = e' c * e' w := by rw [← map_mul, hw, map_mul]
    rw [pow_one, Subgroup.coe_pow, map_pow, Subgroup.coe_one, map_one]
    exact pow_three_eq_one_of_commute_regular (hmem c h.c_mem).1 hc0 hw'
  have := hp.isNilpotent
  infer_instance

end Item424Res2

end CFSG.RankThree.PartTwo.Sec4
