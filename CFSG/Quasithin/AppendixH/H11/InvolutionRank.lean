module

public import CFSG.Quasithin.AppendixH.H11.NativeAction
public import CFSG.Quasithin.AppendixH.H11.AutomorphismGroup
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

private def wL (a b : Equiv.Perm (Fin 12)) : Equiv.Perm (Fin 12) :=
  b * a * b * a * b * a * b * a * b * a * b⁻¹ * a * b⁻¹ * a * b⁻¹

private theorem wL_pow_eleven :
    (wL CFSG.Sporadic.Mathieu.m12gA CFSG.Sporadic.Mathieu.m12gB) ^ 11 = 1 := by
  decide +kernel

private theorem wL_ne_one :
    wL CFSG.Sporadic.Mathieu.m12gA CFSG.Sporadic.Mathieu.m12gB ≠ 1 := by
  decide +kernel

private theorem wL_beta :
    wL CFSG.Sporadic.Mathieu.m12gA CFSG.Sporadic.Schreier.m12bp =
      (wL CFSG.Sporadic.Mathieu.m12gA CFSG.Sporadic.Mathieu.m12gB)⁻¹ := by
  decide +kernel

private def w12 : ↥CFSG.Blueprint.NativeSporadic.M12 :=
  CFSG.Sporadic.Mathieu.m12b * CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12b *
  CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12b * CFSG.Sporadic.Mathieu.m12a *
  CFSG.Sporadic.Mathieu.m12b * CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12b *
  CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12b⁻¹ * CFSG.Sporadic.Mathieu.m12a *
  CFSG.Sporadic.Mathieu.m12b⁻¹ * CFSG.Sporadic.Mathieu.m12a * CFSG.Sporadic.Mathieu.m12b⁻¹

private theorem coe_w12 :
    ((w12 : ↥CFSG.Blueprint.NativeSporadic.M12) : Equiv.Perm (Fin 12)) =
      wL CFSG.Sporadic.Mathieu.m12gA CFSG.Sporadic.Mathieu.m12gB := by
  simp only [w12, wL, Subgroup.coe_mul, Subgroup.coe_inv, CFSG.Sporadic.Mathieu.m12a,
    CFSG.Sporadic.Mathieu.m12b]

theorem exists_inverted_orderOf_eleven
    (α : MulAut ↥CFSG.Blueprint.NativeSporadic.M12) (h2 : orderOf α = 2)
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Blueprint.NativeSporadic.M12) :
    ∃ x : ↥CFSG.Blueprint.NativeSporadic.M12, orderOf x = 11 ∧ α x = x⁻¹ := by
  obtain ⟨g, hg⟩ := CFSG.ComponentClassification.M12Cover.exists_conj_beta_of_outer h2 hα
  haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  have hbetaw : CFSG.ComponentClassification.M12Cover.beta w12 = w12⁻¹ := by
    have hbw : (CFSG.ComponentClassification.M12Cover.beta w12 : Equiv.Perm (Fin 12)) =
        wL CFSG.Sporadic.Mathieu.m12gA CFSG.Sporadic.Schreier.m12bp := by
      simp only [w12, map_mul, map_inv, wL, CFSG.ComponentClassification.M12Cover.beta_m12a,
        CFSG.ComponentClassification.M12Cover.beta_m12b, Subgroup.coe_mul, Subgroup.coe_inv]
    apply Subtype.ext
    rw [Subgroup.coe_inv, coe_w12, ← wL_beta]
    exact hbw
  have hpow : w12 ^ 11 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_w12, wL_pow_eleven]
    rfl
  have hne : w12 ≠ 1 := by
    intro h
    apply wL_ne_one
    have hc := congrArg (fun y : ↥CFSG.Blueprint.NativeSporadic.M12 =>
      (y : Equiv.Perm (Fin 12))) h
    simpa [coe_w12] using hc
  have hordw : orderOf w12 = 11 := orderOf_eq_prime hpow hne
  refine ⟨g * w12 * g⁻¹, ?_, ?_⟩
  · have hconj : g * w12 * g⁻¹ = (MulAut.conj g) w12 := by rw [MulAut.conj_apply]
    rw [hconj, (MulAut.conj g).orderOf_eq w12, hordw]
  · rw [hg]
    have hconj : g * w12 * g⁻¹ = (MulAut.conj g) w12 := by rw [MulAut.conj_apply]
    rw [hconj]
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hbetaw]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    group

private theorem mul_conj_inv_cancel {G : Type*} [Group G] (t x : G) (ht : t * t = 1) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  rw [show t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ by group]
  rw [ht]
  simp

private theorem pi_apply_alpha {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}
    (c : NativeCoords L) (hLM : IsOver L M) {t : MulAut V} (htM : t ∈ M)
    (α : MulAut ↥CFSG.Blueprint.NativeSporadic.M12)
    (hα : α = (MulAut.congr c.mulEquiv.symm) (conjHom hLM ⟨t, htM⟩))
    (γ : ↥CFSG.Blueprint.NativeSporadic.M12) :
    ((c.π (α γ) : ↥L) : MulAut V) = t * ((c.π γ : ↥L) : MulAut V) * t⁻¹ := by
  subst hα
  have hα' : ((MulAut.congr c.mulEquiv.symm) (conjHom hLM ⟨t, htM⟩)) γ
      = c.mulEquiv.symm (conjHom hLM ⟨t, htM⟩ (c.mulEquiv γ)) := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    rfl
  rw [hα']
  have hπ : c.π (c.mulEquiv.symm (conjHom hLM ⟨t, htM⟩ (c.mulEquiv γ)))
      = conjHom hLM ⟨t, htM⟩ (c.mulEquiv γ) := by
    rw [← c.mulEquiv_apply, MulEquiv.apply_symm_apply]
  rw [hπ, c.mulEquiv_apply]
  exact coe_conjHom_apply hLM ⟨t, htM⟩ (c.π γ)

theorem four_le_rkIdx_of_mem_of_orderOf_eq_two [Finite V]
    (c : NativeCoords L) (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V} (htL : t ∈ L)
    (ht : orderOf t = 2) : 4 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  obtain ⟨γ, hγ⟩ := c.surj ⟨t, htL⟩
  have ht_eq : ((c.π γ : ↥L) : MulAut V) = t := by
    have := congrArg (fun x : ↥L => (x : MulAut V)) hγ
    simpa using this
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  have hπ2 : c.π γ * c.π γ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ht_eq, ht2]
  have h2 : γ * γ = 1 := by
    apply c.injective
    rw [map_mul, hπ2, map_one]
  have h1 : γ ≠ 1 := by
    intro hγ1
    have hsub : (⟨t, htL⟩ : ↥L) = 1 := by rw [← hγ, hγ1, map_one]
    have ht1 : t = 1 := by
      have := congrArg (fun x : ↥L => (x : MulAut V)) hsub
      simpa using this
    rw [ht1] at ht
    norm_num at ht
  rw [← ht_eq]
  exact c.four_le_rkIdx_of_involution hV γ h1 h2

theorem five_le_rkIdx_of_not_mem_of_orderOf_eq_two [Finite V] [Finite (MulAut V)]
    (c : NativeCoords L) (hV : ∀ v : V, v ^ 2 = 1) (hLM : IsOver L M)
    (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥) {t : MulAut V} (htM : t ∈ M)
    (htL : t ∉ L) (ht : orderOf t = 2) : 5 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  let α : MulAut ↥CFSG.Blueprint.NativeSporadic.M12 :=
    (MulAut.congr c.mulEquiv.symm) (conjHom hLM ⟨t, htM⟩)
  have hαeq : α = (MulAut.congr c.mulEquiv.symm) (conjHom hLM ⟨t, htM⟩) := rfl
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  have hαsq : α * α = 1 := by
    apply MulEquiv.ext
    intro γ
    apply c.injective
    rw [MulAut.one_apply]
    apply Subtype.ext
    rw [MulAut.mul_apply, pi_apply_alpha c hLM htM α hαeq (α γ),
      pi_apply_alpha c hLM htM α hαeq γ]
    exact mul_conj_inv_cancel t ((c.π γ : ↥L) : MulAut V) ht2
  have hαne : α ≠ 1 := by
    intro hα1
    have hmem : t ∈ Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨γ, hγ⟩ := c.surj ⟨l, hl⟩
      have hγ' : ((c.π γ : ↥L) : MulAut V) = l := by
        have := congrArg (fun x : ↥L => (x : MulAut V)) hγ
        simpa using this
      have hfix : ((c.π (α γ) : ↥L) : MulAut V) = ((c.π γ : ↥L) : MulAut V) := by
        rw [hα1, MulAut.one_apply]
      rw [pi_apply_alpha c hLM htM α hαeq γ, hγ'] at hfix
      have hcomm : t * l = l * t := by
        have := congrArg (· * t) hfix
        simpa [mul_assoc] using this
      exact hcomm.symm
    rw [hC] at hmem
    have ht1 : t = 1 := by simpa using hmem
    rw [ht1] at ht
    norm_num at ht
  have hαouter : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      ↥CFSG.Blueprint.NativeSporadic.M12 := by
    rintro ⟨g, hg⟩
    have hz : (((c.π g : ↥L) : MulAut V))⁻¹ * t ∈
        Subgroup.centralizer (L : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      obtain ⟨γ, hγ⟩ := c.surj ⟨l, hl⟩
      have hγ' : ((c.π γ : ↥L) : MulAut V) = l := by
        have := congrArg (fun x : ↥L => (x : MulAut V)) hγ
        simpa using this
      have hkey : t * ((c.π γ : ↥L) : MulAut V) * t⁻¹ =
          ((c.π g : ↥L) : MulAut V) * ((c.π γ : ↥L) : MulAut V) *
            (((c.π g : ↥L) : MulAut V))⁻¹ := by
        have h1 := pi_apply_alpha c hLM htM α hαeq γ
        rw [show α γ = MulAut.conj g γ by rw [← hg]] at h1
        rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1.symm
      have hzcomm : (((c.π g : ↥L) : MulAut V))⁻¹ * t * ((c.π γ : ↥L) : MulAut V) =
          ((c.π γ : ↥L) : MulAut V) * ((((c.π g : ↥L) : MulAut V))⁻¹ * t) := by
        have := congrArg (fun w => (((c.π g : ↥L) : MulAut V))⁻¹ * w * t) hkey
        simpa [mul_assoc] using this
      rw [← hγ']
      exact hzcomm.symm
    rw [hC] at hz
    have hz1 : (((c.π g : ↥L) : MulAut V))⁻¹ * t = 1 := by simpa using hz
    have ht_eq : t = ((c.π g : ↥L) : MulAut V) := by
      have := congrArg (fun w => ((c.π g : ↥L) : MulAut V) * w) hz1
      simpa [mul_assoc] using this
    exact htL (by rw [ht_eq]; exact (c.π g).2)
  have hα2 : orderOf α = 2 := orderOf_eq_prime hαsq hαne
  obtain ⟨x, hx11, hαx⟩ := exists_inverted_orderOf_eleven α hα2 hαouter
  let l : MulAut V := ((c.π x : ↥L) : MulAut V)
  have htl : t * l * t⁻¹ = l⁻¹ := by
    have h1 := pi_apply_alpha c hLM htM α hαeq x
    rw [hαx] at h1
    rw [map_inv] at h1
    simpa [l, Subgroup.coe_inv] using h1.symm
  have hxx : orderOf (x * x) = 11 := by
    have hcop : (orderOf x).Coprime 2 := by rw [hx11]; norm_num
    have h := hcop.orderOf_pow
    rw [pow_two] at h
    rw [h, hx11]
  have hlfix : ∀ v : V, (l * l) v = v → v = 1 := by
    intro v hv
    have hcoexx : ((c.π (x * x) : ↥L) : MulAut V) = l * l := by
      rw [map_mul]
      simp [l, Subgroup.coe_mul]
    apply c.eq_one_of_fixed_of_orderOf_eq_eleven (x * x) hxx v
    rwa [hcoexx]
  exact five_le_rkIdx_of_inverts hV (card_V_of_nativeCoords c) t l ht2 htl hlfix

theorem four_le_rkIdx_of_mem_M_of_orderOf_eq_two [Finite V] [Finite (MulAut V)]
    (c : NativeCoords L) (hV : ∀ v : V, v ^ 2 = 1) (hLM : IsOver L M)
    (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥) {t : MulAut V} (htM : t ∈ M)
    (ht : orderOf t = 2) : 4 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  by_cases htL : t ∈ L
  · exact four_le_rkIdx_of_mem_of_orderOf_eq_two c hV htL ht
  · have h5 := five_le_rkIdx_of_not_mem_of_orderOf_eq_two c hV hLM hC htM htL ht
    omega

theorem mParam_eq_four [Finite V] [Finite (MulAut V)]
    (c : NativeCoords L) (hV : ∀ v : V, v ^ 2 = 1) (hLM : IsOver L M)
    (hC : Subgroup.centralizer (L : Set (MulAut V)) = ⊥) : E3.mParam M = 4 := by
  unfold E3.mParam
  rw [if_pos (even_card hLM c.mulEquiv.symm)]
  have hmem : 4 ∈ {n : ℕ | ∃ t ∈ M, orderOf t = 2 ∧
      n = rkIdx (fixV (Subgroup.zpowers t))} := by
    refine ⟨((c.π CFSG.Sporadic.Mathieu.m12a : ↥L) : MulAut V),
      hLM.1 (c.π CFSG.Sporadic.Mathieu.m12a).2, c.orderOf_m12a hV, ?_⟩
    exact (c.rkIdx_m12a hV).symm
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨4, hmem⟩ ?_)
  rintro n ⟨s, hs, hso, rfl⟩
  exact four_le_rkIdx_of_mem_M_of_orderOf_eq_two c hV hLM hC hs hso

end CFSG.Quasithin.AppendixH.H11
