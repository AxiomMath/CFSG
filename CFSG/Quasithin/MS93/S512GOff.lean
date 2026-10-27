module

public import CFSG.Quasithin.MS93.S512NOff

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512G

theorem mem_of_index_two_of_pow_odd {Γ : Type*} [Group Γ] {H : Subgroup Γ} (hH : H.index = 2)
    {g : Γ} {n : ℕ} (hg : g ^ (2 * n + 1) = 1) : g ∈ H := by
  have e : g = (g ^ n)⁻¹ * (g ^ n)⁻¹ := by
    rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← pow_add, ← pow_succ', ← two_mul]
    exact hg
  rw [e]
  exact Subgroup.mul_self_mem_of_index_two hH _

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem map_mem_commutator_of_mem (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
    {F' : Type} [Field F'] (hF' : Nat.card F' = 2) (ψ : ↥M →* MSP.Sp4 F')
    (hψ : ∀ m : ↥M, a m = 1 → (∃ e : ℕ, m ^ 2 ^ e = 1) → ψ m = 1)
    {m : ↥M} (hm : a m ∈ commutator (MSP.Sp4 F)) : ψ m ∈ commutator (MSP.Sp4 F') := by
  obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hF'
  have hidx := MSP.index_commutator c
  rw [← S5Q2.map_L_eq_commutator h hd] at hm
  obtain ⟨l, hl, hal⟩ := hm
  have hk : a (l⁻¹ * m) = 1 := by rw [map_mul, map_inv, hal, inv_mul_cancel]
  have hm' : m = l * (l⁻¹ * m) := by group
  have hperf : ⁅L.subgroupOf M, L.subgroupOf M⁆ = L.subgroupOf M := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h.L_le, h.perfect]
  have hψl : ψ l ∈ commutator (MSP.Sp4 F') := by
    have hmem : ψ l ∈ (L.subgroupOf M).map ψ := ⟨l, hl, rfl⟩
    rw [← hperf, Subgroup.map_commutator] at hmem
    exact Subgroup.commutator_mono le_top le_top hmem
  have hψk : ψ (l⁻¹ * m) ∈ commutator (MSP.Sp4 F') := by
    set k := l⁻¹ * m
    obtain ⟨e, o, ho, hko⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
    have hk2 : (k ^ o) ^ 2 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hko, pow_orderOf_eq_one]
    have hko1 : ψ (k ^ o) = 1 := hψ _ (by rw [map_pow, hk, one_pow]) ⟨e, hk2⟩
    obtain ⟨n, rfl⟩ := ho
    exact mem_of_index_two_of_pow_odd hidx (by rw [← map_pow]; exact hko1)
  rw [hm', map_mul]
  exact mul_mem hψl hψk

theorem false_of_even_offender (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) {h : PUHyp M T L} (hd : S5.IsSp4Data M T L 1 F a)
    {V : Subgroup (puAmalgam h.le).Universal} (hV : S512N.SecHyp h V)
    {E : Subgroup (puAmalgam h.le).Universal} (hEs : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hEe : CFSG.Open.IsElemAbelian 2 E)
    (hEW : (S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _)) E
      (hV.le_stab.trans hV.le_normalizer_inf)).relIndex V ≤ 2)
    (hEv : S5.vIm h.le a E ≤ commutator (MSP.Sp4 F))
    (hEQ : ¬ E ≤ Qv _ (baseA (puAmalgam h.le))) : False := by
  obtain ⟨S, _, p, ρ, hs⟩ := hV.exists_secMod
  have := hV.finite_S hs
  obtain ⟨S₀, hne, hS₀, hmin⟩ := S512N.exists_minimal_invariant ρ (hV.nontrivial_S hs)
  have hρ := hV.isIrrRep_restrict hs hS₀ hne hmin
  set ρM := (S512N.restrict ρ hS₀).comp (S512N.eM h.le) with hρM
  set A := (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (S512N.restrict ρ hS₀)
    with hAdef
  have hAX : A ≤ ρM.range := by
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨m, rfl⟩ := S512N.eM_surjective h.le g
    exact ⟨m, rfl⟩
  have hEc : E ≤ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hEe.1
  have hA : IsElemAbelian2 A := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 (hEc (Subgroup.mem_subgroupOf.1 hg')) _
        (Subgroup.mem_subgroupOf.1 hg)
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow]
      have : g ^ 2 = 1 := Subtype.ext (by simpa using hEe.2 _ (Subgroup.mem_subgroupOf.1 hg))
      rw [this, map_one]
  have hcA : Nat.card A = (Qv _ (baseA (puAmalgam h.le))).relIndex E :=
    hV.card_map_restrict hs hS₀ hne hmin hEs hEe
  have hidx : (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).index ≤ 2 ^ 1 := by
    rw [hs.index_fixV hEs (hV.le_stab.trans hV.le_normalizer_inf), pow_one]
    exact hEW
  have hAf := hV.card_le_fixV_restrict hs hS₀ hidx
  have hrel2 : 2 ^ 1 ≤ Nat.card A := by
    rw [hcA, pow_one]
    have h0 : (Qv _ (baseA (puAmalgam h.le))).relIndex E ≠ 0 := by
      have hfin : Finite ↥(stab (puAmalgam h.le) (baseA _)) :=
        S310.finite_stab_of_isMVtx h (isMVtx_baseA _)
      have : Finite ↥E := Finite.of_injective _ (Subgroup.inclusion_injective hEs)
      exact Subgroup.index_ne_zero_of_finite
    have h1 : (Qv _ (baseA (puAmalgam h.le))).relIndex E ≠ 1 :=
      fun h1 => hEQ (Subgroup.relIndex_eq_one.1 h1)
    omega
  obtain ⟨F', iF, fF, φ, θ, hcard, -, hθ⟩ := S512N.exists_coord h14 hSQ hT h hd hρ hAX hA hrel2
    hAf (fun hk2 => absurd hk2 (by norm_num))
  have hF' : Nat.card F' = 2 := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hrel2
    norm_num at hrel2
  obtain ⟨p', hp', -, hle⟩ := S512N.exists_point_of_coord hθ hAX hA1
    (by rw [hF']; simpa using hAf)
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  obtain ⟨g, hgE, hgx⟩ := x.2
  obtain ⟨m, rfl⟩ := S512N.eM_surjective h.le g
  set ψ : ↥M →* MSP.Sp4 F' := φ.comp ρM.rangeRestrict with hψdef
  have hρm : ρM m = (x : MulAut ↥S₀) := by rw [hρM, MonoidHom.comp_apply, hgx]
  have hψ1 : ψ m ∉ commutator (MSP.Sp4 F') := by
    have hmem : ψ m ∈ (A.subgroupOf ρM.range).map φ := by
      refine ⟨ρM.rangeRestrict m, ?_, rfl⟩
      change ((ρM.rangeRestrict m : ↥ρM.range) : MulAut ↥S₀) ∈ A
      rw [MonoidHom.coe_rangeRestrict, hρm]
      exact x.2
    have hxP := hle hmem
    obtain ⟨v, hv, rfl⟩ := MSP.exists_eq_span_of_isPoint hp'
    obtain ⟨c, hc⟩ := (MSP.mem_xPoint_span hv).1 hxP
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [MSP.transv_zero] at hc
      apply hx1
      have hinj := S512N.injective_of_coord hθ
      have h1 : ρM.rangeRestrict m = 1 := hinj (by rw [map_one]; exact hc.symm)
      have h2 : ρM m = 1 := by
        have := congrArg Subtype.val h1
        rwa [MonoidHom.coe_rangeRestrict] at this
      exact Subtype.ext (by rw [← hρm, h2]; rfl)
    rw [← hc]
    exact MSP.transv_not_mem_commutator_of_card_two hF' hv c hc0
  apply hψ1
  refine map_mem_commutator_of_mem h hd hF' ψ (fun m' hm' h2 => ?_) ?_
  · have hO := S5B.mem_pCoreOf_of_ker h hd hm' (by
      obtain ⟨e, he⟩ := h2
      exact ⟨e, by simpa using congrArg Subtype.val he⟩)
    have hρ1 : ρM m' = 1 := hρ.pCore m' hO
    rw [hψdef, MonoidHom.comp_apply]
    have : ρM.rangeRestrict m' = 1 := Subtype.ext (by
      rw [MonoidHom.coe_rangeRestrict, hρ1]
      rfl)
    rw [this, map_one]
  · refine hEv ⟨m, ?_, rfl⟩
    have := Subgroup.mem_subgroupOf.1 hgE
    rwa [S512N.coe_eM] at this

end S512G

end CFSG.Quasithin.MS93
