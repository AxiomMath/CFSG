module

public import CFSG.RankThree.PartOne.SP4C.GAL
public import CFSG.RankThree.PartOne.KF.R7Final

public section

namespace CFSG.RankThree.PartOne.NF7H

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.SP4C
  CFSG.LieType.Universal.Unitary Matrix
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

section Lift

variable {G : Type} [Group G]

theorem row7_exists_involution_lift [Finite G] {p : ℕ} {L A₀ F : Subgroup G}
    (h : Table123Core p L A₀ F) (hmodel : RowModel p L 7) (hZ : Subgroup.center ↥L = ⊥) :
    ∃ u : G, u ∈ L ∧ u ∈ Subgroup.normalizer (F : Set G) ∧ u * u = 1 ∧
      ∀ f ∈ F, u * f * u⁻¹ = f⁻¹ := by
  classical
  obtain ⟨f, K, hKf, hKfin, hf1, hpq, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩ := exists_r7frame h hmodel
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have hFL : F ≤ L := h.F_le
  let T : TFrame p L F K := ⟨hFL, ε, hε, hFT₁, hFT₂, h.F_exp⟩
  have hεinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_eq_center hε, hZ]
  let m₀ : ↥(spRev K) := ⟨permGL (d8Perm d8Comb_four (DihedralGroup.r 2)),
    hP_spRev _ (d8Comb2_four.comm_rev _)⟩
  have hr2 : (DihedralGroup.r 2 : DihedralGroup 4) * DihedralGroup.r 2 = 1 := by decide
  have hm₀sq : m₀ * m₀ = 1 := by
    apply Subtype.ext
    show permGL (d8Perm d8Comb_four (DihedralGroup.r 2)) *
      permGL (d8Perm d8Comb_four (DihedralGroup.r 2)) = 1
    rw [← map_mul, ← map_mul, hr2, map_one, map_one]
  have hm₀inv : m₀⁻¹ = m₀ := inv_eq_of_mul_eq_one_right hm₀sq
  have hconj : ∀ w : D8Mod p K, m₀ * torC p K w * m₀⁻¹ = torC p K (d8Act (DihedralGroup.r 2) w) := by
    intro w
    apply Subtype.ext
    show (permGL (d8Perm d8Comb_four (DihedralGroup.r 2)) : GL (Fin 4) K) *
      ((torC p K w : ↥(spRev K)) : GL (Fin 4) K) *
        (permGL (d8Perm d8Comb_four (DihedralGroup.r 2)) : GL (Fin 4) K)⁻¹ = _
    rw [coe_torC, coe_torC, permGL_conj_diagU, d8Vec_act d8Comb_four]
  have hinvw : ∀ w : D8Mod p K, d8Act (DihedralGroup.r 2) w = w⁻¹ := by
    intro w
    rw [d8Act_r_two]
    rfl
  have hmN : m₀ ∈ Subgroup.normalizer (Tsub p K : Set ↥(spRev K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨w, rfl⟩ := exists_torC_of_mem t ht
      rw [hconj]
      exact torC_mem _
    · intro ht
      obtain ⟨w, hw⟩ := exists_torC_of_mem _ ht
      have h1 : t = m₀ * (m₀ * t * m₀⁻¹) * m₀⁻¹ := by
        rw [hm₀inv]
        calc t = (m₀ * m₀) * t * (m₀ * m₀) := by rw [hm₀sq]; group
          _ = m₀ * (m₀ * t * m₀) * m₀ := by group
      rw [h1, hw, hconj]
      exact torC_mem _
  obtain ⟨u, hu⟩ := hε.surjective (spQe K m₀)
  have huu : u * u = 1 := by
    apply hεinj
    rw [map_mul, hu, ← map_mul, hm₀sq, map_one, map_one]
  refine ⟨(u : G), u.2, T.mem_normalizer hmN hu, ?_, ?_⟩
  · have := congrArg (fun x : ↥L => (x : G)) huu
    simpa using this
  · intro f₀ hf₀
    obtain ⟨t, ht, hft⟩ := T.h₂ ⟨f₀, hf₀⟩
    obtain ⟨w, rfl⟩ := exists_torC_of_mem t ht
    set a : ↥L := Subgroup.inclusion hFL ⟨f₀, hf₀⟩ with ha
    have hft' : ε a = spQe K (torC p K w) := hft
    have hap : a ^ p = 1 := Subtype.ext (h.F_exp f₀ hf₀)
    have hap' : (u * a * u⁻¹) ^ p = 1 := by
      rw [conj_pow, hap]
      group
    have hap'' : a⁻¹ ^ p = 1 := by
      rw [inv_pow, hap, inv_one]
    have key : u * a * u⁻¹ = a⁻¹ := by
      apply hε.eq_of_map_eq hap' hap''
      have h1 : ε (u * a * u⁻¹) = spQe K (m₀ * torC p K w * m₀⁻¹) := by
        rw [map_mul, map_mul, map_inv, hu, hft', map_mul, map_mul, map_inv]
      rw [h1, hconj, hinvw, map_inv, map_inv, map_inv, hft']
    have := congrArg (fun y : ↥L => (y : G)) key
    simpa [ha] using this

end Lift

end CFSG.RankThree.PartOne.NF7H
