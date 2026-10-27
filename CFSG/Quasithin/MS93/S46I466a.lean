module

public import CFSG.Quasithin.MS93.S46Inputs
public import CFSG.Quasithin.MS93.S46I464Lin
public import CFSG.Quasithin.MS93.S46I465

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped Matrix

section Lin

variable {F : Type} [Field F]

theorem finrank_commN_le_one_of_card_le_two [Finite F] [CharP F 2] {E : Subgroup (SL3 F)}
    (hE : Nat.card E ≤ 2) : Module.finrank F (commN E) ≤ 1 := by
  by_cases hbot : E = ⊥
  · have : commN E = ⊥ := by
      rw [eq_bot_iff, commN, Submodule.span_le]
      rintro _ ⟨g, hg, x, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hg
      rw [hg, coe_one_SL3, Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
    rw [this, finrank_bot]
    exact zero_le_one
  obtain ⟨⟨t, htE⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hcard : Nat.card E = 2 := by
    have h1 : 1 < Nat.card E := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hbot
    omega
  have hE2 : ∀ g ∈ E, g = 1 ∨ g = t := by
    intro g hg
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥E)).mp hcard
    by_cases hg1 : g = 1
    · exact Or.inl hg1
    · right
      have e1 : (⟨g, hg⟩ : ↥E) = y := huniq _ fun h => hg1 (congrArg Subtype.val h)
      have e2 : (⟨t, htE⟩ : ↥E) = y := huniq _ ht1
      exact congrArg Subtype.val (e1.trans e2.symm)
  have ht2 : t * t = 1 := by
    have h := orderOf_dvd_natCard (⟨t, htE⟩ : ↥E)
    rw [hcard] at h
    have h' : (⟨t, htE⟩ : ↥E) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h
    have := congrArg Subtype.val h'
    simpa [sq] using this
  set A : Matrix (Fin 3) (Fin 3) F := ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) - 1 with hA
  have hAA : A * A = 0 := by
    have htt : ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F)
        = 1 := by
      rw [← coe_mul_SL3, ht2, coe_one_SL3]
    have h2 : (2 : Matrix (Fin 3) (Fin 3) F) = 0 := by
      rw [show (2 : Matrix (Fin 3) (Fin 3) F) = ((2 : F) • 1 : Matrix (Fin 3) (Fin 3) F) by
        rw [two_smul, one_add_one_eq_two], CharTwo.two_eq_zero, zero_smul]
    calc A * A = ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F)
          - 2 * ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) + 1 := by
            rw [hA]
            noncomm_ring
      _ = 0 := by rw [htt, h2, zero_mul, sub_zero, ← two_mul, h2, zero_mul]
  have hle : commN E ≤ LinearMap.range (Matrix.mulVecLin A) := by
    rw [commN, Submodule.span_le]
    rintro _ ⟨g, hg, x, rfl⟩
    rcases hE2 g hg with rfl | rfl
    · rw [coe_one_SL3, Matrix.one_mulVec, sub_self]
      exact Submodule.zero_mem _
    · refine ⟨x, ?_⟩
      rw [Matrix.mulVecLin_apply, hA, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hrk : LinearMap.range (Matrix.mulVecLin A) ≤ LinearMap.ker (Matrix.mulVecLin A) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hAA, Matrix.zero_mulVec]
  have hsum := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
  rw [Module.finrank_fin_fun] at hsum
  have h1 := Submodule.finrank_mono hrk
  have h2 := Submodule.finrank_mono hle
  omega

end Lin

theorem i466a_two (h464 : I464) (h465 : I465) (G : Type) [Group G] [Finite G]
    (M T L : Subgroup G) (F : Type) [Field F] [Fintype F] (φ : ↥M →* ↥(StatedSL 3 F))
    (c : Hyp46 M T L φ) (α β : Vtx (puAmalgam c.pu.le)) (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hq : Fintype.card F = 2) :
    (Qv _ α).relIndex (Qv _ β) = Fintype.card F ^ 2 := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hβK : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  rw [← card_natImage_eq_relIndex h hφ hα hψ hβK]
  set E := natImage ψ (Qv (puAmalgam h.le) β) with hEdef
  have hq2 : 2 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hq]
  have hU := (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α β hα hαβ).1
  rw [usup_eq_commutator_uloc h hfull hα hαβ, I464.card_commutator_eq_pow hψ hβK,
    ← Nat.card_eq_fintype_card] at hU
  have hcomm : Module.finrank F (commN E) = 2 :=
    Nat.pow_right_injective hq2 hU
  have hfix : commN E ≤ fixN E := by
    refine I464.commN_le_fixN_of_commutator_le_centralizer hψ hβK ?_
    have h1 := h464 G M T L F φ ⟨h, hmin, hb4, hφ⟩ α β hα hαβ
    rw [usup_eq_commutator_uloc h hfull hα hαβ] at h1
    exact h1.trans (zh_le_centralizer _ β)
  have hfix2 : 2 ≤ Module.finrank F (fixN E) := hcomm ▸ Submodule.finrank_mono hfix
  have hfix3 := Submodule.finrank_le (fixN E)
  rw [Module.finrank_fin_fun] at hfix3
  have hup : Nat.card E ≤ Nat.card F ^ 2 := by
    have h1 := card_le_pow_finrank E
    have h2 : (3 - Module.finrank F (fixN E)) * Module.finrank F (commN E) ≤ 2 := by
      rw [hcomm]
      omega
    exact h1.trans (Nat.pow_le_pow_right (by omega) h2)
  have hlow : 2 < Nat.card E := by
    by_contra hle
    have := finrank_commN_le_one_of_card_le_two (not_lt.mp hle)
    omega
  have hEp : IsPGroup 2 E := by
    have hβH : ¬ IsMVtx (puAmalgam h.le) β := by have := isMVtx_iff_of_adj _ hαβ; tauto
    exact isPGroup_natImage (isPGroup_qv _ h.hyp20 hβH) hβK
  have : Finite ↥E := Subgroup.instFiniteSubtypeMem E
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hqN : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hq]
  rw [hqN] at hup
  rw [hk] at hup hlow ⊢
  rw [hq]
  have hk2 : k ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hup
  interval_cases k <;> simp_all

theorem i466a_of (hQ4 : S466aQ4) (h464 : I464) (h465 : I465) : I466a := by
  intro G _ _ M T L F _ _ φ c α β hα hαβ
  by_cases hq : 4 ≤ Fintype.card F
  · exact hQ4 G M T L F φ c α β hα hαβ hq
  · obtain ⟨n, hn⟩ := c.via.1
    have h2 : 2 ≤ Fintype.card F := two_le_card_field
    have hq2 : Fintype.card F = 2 := by
      rw [hn] at hq h2 ⊢
      rcases n with _ | _ | n
      · simp at h2
      · rfl
      · exfalso
        apply hq
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact i466a_two h464 h465 G M T L F φ c α β hα hαβ hq2

end CFSG.Quasithin.MS93.S46
