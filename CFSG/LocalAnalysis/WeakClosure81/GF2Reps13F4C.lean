module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4A
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FourClausesA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts4
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem s134b_case_a {Y K : Subgroup (MulAut W)} {t : MulAut W} (F : S134Frame Y K t)
    {I : Subgroup W} (hI : I ∈ irrSet K) (hKI : commSub I (S134Conj t K) = ⊥) :
    Conc4_134 Y K t := by
  classical
  have ht : t * t = 1 := F.mul_self
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hW2 : ∀ w : W, w * w = 1 := fun w => by simpa [pow_two] using F.exp w
  have hKI_fix : I ≤ fixV (S134Conj t K) := commSub_eq_bot_iff.mp hKI
  have hIstable : StableUnder K I := hI.2.2.1
  have hItwist_fix : I.map t.toMonoidHom ≤ fixV K := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_fixV]
    intro k hk
    have hk' : t * k * t⁻¹ ∈ S134Conj t K := by
      rw [S134Conj]
      exact Subgroup.mem_map.mpr ⟨k, hk, by
        show (MulAut.conj t) k = t * k * t⁻¹
        rw [MulAut.conj_apply]⟩
    have hfix : (t * k * t⁻¹) i = i := hKI_fix hi (t * k * t⁻¹) hk'
    have h1 : t (k (t i)) = i := by
      simpa only [MulAut.mul_apply, htinv] using hfix
    have h2 : k (t i) = t i := by
      have h3 := congrArg t h1
      rw [← MulAut.mul_apply, ht, MulAut.one_apply] at h3
      exact h3
    exact h2
  have hItwist_stable : StableUnder K (I.map t.toMonoidHom) := by
    intro k hk x hx
    rw [mem_fixV.mp (hItwist_fix hx) k hk]
    exact hx
  have hfixV_stable : StableUnder K (fixV K) := by
    intro k hk x hx
    rw [show k x = x from mem_fixV.mp hx k hk]
    exact hx
  let C : Subgroup W := I ⊓ fixV K
  have hC_stable : StableUnder K C := stableUnder_inf hIstable hfixV_stable
  have hker_mem : ∀ i : ↥I, t (i : W) = (i : W) → (i : W) ∈ C := by
    intro i hi
    refine ⟨i.2, ?_⟩
    apply hItwist_fix
    rw [Subgroup.mem_map]
    exact ⟨i, i.2, by simpa using hi⟩
  let θ : ↥I →* W := MonoidHom.mk' (fun i : ↥I => t (i : W) * (i : W)⁻¹) (by
    intro a b
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
    ac_rfl)
  have hker_le : Nat.card θ.ker ≤ Nat.card C := by
    have hinj : Function.Injective (fun x : θ.ker =>
        (⟨(x.1 : W), hker_mem x.1 (mul_inv_eq_one.mp (MonoidHom.mem_ker.mp x.2))⟩ : C)) := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : W)) hxy))
    exact Nat.card_le_card_of_injective _ hinj
  have hrange_le_T : θ.range ≤ commSub ⊤ (Subgroup.zpowers t) := by
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure
      ⟨t, Subgroup.mem_zpowers t, (i : W), Subgroup.mem_top _, rfl⟩
  have hrange_card_le : Nat.card θ.range ≤ Nat.card (commSub ⊤ (Subgroup.zpowers t)) :=
    Subgroup.card_le_of_le hrange_le_T
  have hTcard : Nat.card (commSub ⊤ (Subgroup.zpowers t)) ≤ 8 := by
    rw [card_eq_two_pow F.exp]
    calc 2 ^ rk (commSub ⊤ (Subgroup.zpowers t)) ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) F.rk_le
      _ = 8 := by norm_num
  have hIcard : Nat.card ↥I = Nat.card ↥C * Nat.card (Sec I C) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf I)
    have hcardC : Nat.card ↥(C.subgroupOf I) = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [hcardC, mul_comm] at h
    exact h
  have hker_card : Nat.card θ.ker * Nat.card θ.range = Nat.card ↥I :=
    Subgroup.card_ker_mul_card_range θ
  have hle8 : Nat.card (Sec I C) ≤ 8 := by
    have h1 : Nat.card ↥C * Nat.card (Sec I C) ≤ Nat.card ↥C * 8 := by
      rw [← hIcard, ← hker_card]
      calc Nat.card θ.ker * Nat.card θ.range
          ≤ Nat.card ↥C * Nat.card θ.range := Nat.mul_le_mul_right _ hker_le
        _ ≤ Nat.card ↥C * Nat.card (commSub ⊤ (Subgroup.zpowers t)) :=
            Nat.mul_le_mul_left _ hrange_card_le
        _ ≤ Nat.card ↥C * 8 := Nat.mul_le_mul_left _ hTcard
    exact Nat.le_of_mul_le_mul_left h1 (card_subgroup_pos C)
  have hnt : ∃ k ∈ K, ∃ u ∈ I, (k : MulAut W) u * u⁻¹ ∉ C := by
    by_contra h
    push Not at h
    have hle : commSub I K ≤ C := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨k, hk, u, hu, rfl⟩
      exact h k hk u hu
    have hIC : I ≤ C := by
      rw [← hI.1]
      exact hle
    exact (not_le_of_gt hI.2.1) hIC
  have hcard8 : Nat.card (Sec I C) = 8 :=
    s134b_perfect_sec_card F.exp F.perfect inf_le_left hIstable hC_stable hnt hle8
  have hnatural : BinaryNaturalSL K I C 3 1 :=
    s134b_natural_of_card_eight F.exp F.l3 inf_le_left hIstable hC_stable hcard8 hnt
  have hrange_ge : 8 ≤ Nat.card θ.range := by
    have h8 : Nat.card ↥I = Nat.card ↥C * 8 := by rw [hIcard, hcard8]
    have h1 : Nat.card ↥C * 8 = Nat.card θ.range * Nat.card θ.ker := by
      rw [← h8, ← hker_card]
      exact mul_comm _ _
    have h2 : Nat.card ↥C * 8 ≤ Nat.card ↥C * Nat.card θ.range := by
      calc Nat.card ↥C * 8 = Nat.card θ.range * Nat.card θ.ker := h1
        _ ≤ Nat.card θ.range * Nat.card ↥C := Nat.mul_le_mul_left _ hker_le
        _ = Nat.card ↥C * Nat.card θ.range := by rw [mul_comm]
    exact Nat.le_of_mul_le_mul_left h2 (card_subgroup_pos C)
  have hrange_eq_T : θ.range = commSub ⊤ (Subgroup.zpowers t) :=
    Subgroup.eq_of_le_of_card_ge hrange_le_T (hTcard.trans hrange_ge)
  have hrange_le_U : θ.range ≤ I ⊔ I.map t.toMonoidHom := by
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_sup.mpr ⟨(i : W)⁻¹, I.inv_mem i.2,
      t (i : W), Subgroup.mem_map.mpr ⟨i, i.2, rfl⟩, by rw [mul_comm]; rfl⟩
  have hT_le_U : commSub ⊤ (Subgroup.zpowers t) ≤ I ⊔ I.map t.toMonoidHom := by
    rw [← hrange_eq_T]
    exact hrange_le_U
  let U : Subgroup W := I ⊔ I.map t.toMonoidHom
  have hU_stable : StableUnder K U := stableUnder_sup hIstable hItwist_stable
  have hItwist_bot : commSub (I.map t.toMonoidHom) K = ⊥ := commSub_eq_bot_iff.mpr hItwist_fix
  have hcomm_le_U : commSub ⊤ K ≤ U :=
    s134b_commSub_le_of_t_trivial ht F.comm F.perfect hU_stable (by simpa only [U] using hT_le_U)
  have hcommU : commSub U K = I := by
    have h := commSub_sup_left I (I.map t.toMonoidHom) K
    rw [hI.1, hItwist_bot, sup_bot_eq] at h
    simpa only [U] using h
  have hcommK_le_I : commSub ⊤ K ≤ I :=
    s13_perfect_chain K F.perfect I U ⊤ (le_of_eq hcommU) hcomm_le_U
  have hI_le_commK : I ≤ commSub ⊤ K := by
    rw [← hI.1]
    exact commSub_mono le_top le_rfl
  have hcommK_eq_I : commSub ⊤ K = I := le_antisymm hcommK_le_I hI_le_commK
  have hI' : commSub ⊤ K ∈ irrSet K := by rw [hcommK_eq_I]; exact hI
  refine Or.inr ⟨F.l3, hI', ?_, ?_⟩
  · intro g hg hgK
    exact s134_clause_two hW2 F.comp hg hgK hI'
  · rw [hcommK_eq_I]
    exact hnatural

end CFSG.LocalAnalysis.WeakClosure81
