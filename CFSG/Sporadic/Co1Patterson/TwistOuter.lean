module

public import CFSG.Sporadic.Co1Patterson.TwistBasic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCover

public section

namespace CFSG.Sporadic.Co1Patterson

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] noncomputable def trialityAut : MulAut omegaT :=
  MulEquiv.ofBijective Cover.triality ⟨Cover.triality_injective, Cover.triality_surjective⟩

theorem trialityAut_apply (g : omegaT) :
    trialityAut g = Cover.triality g := rfl

theorem trialityAut_pow_three : trialityAut ^ 3 = 1 :=
  MulEquiv.ext fun g => by
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, trialityAut_apply,
      MulAut.one_apply]
    exact Cover.triality_cube g

theorem conj_eq_autConj (x : omegaT) :
    MulAut.conj x = autConj ⟨x, omegaT_le_autT x.2⟩ :=
  MulEquiv.ext fun g => Subtype.ext (by rw [autConj_apply, MulAut.conj_apply]; rfl)

theorem trialityAut_not_mem_inner :
    trialityAut ∉ inner omegaT := by
  rintro ⟨x, hx⟩
  have h8 : autConj ⟨gen 8, gen_mem_autT (by norm_num)⟩ = autConj ⟨x, omegaT_le_autT x.2⟩ := by
    rw [← conj_eq_autConj, hx]
    exact MulEquiv.ext fun g => Subtype.ext (by
      rw [autConj_apply, trialityAut_apply, Cover.coe_triality])
  have hx8 : gen 8 = (x : Equiv.Perm (Fin 360)) := congrArg Subtype.val (autConj_injective h8)
  have h0 := (omegaT_le_stab0 (hx8 ▸ x.2 : gen 8 ∈ omegaT)) 0
  rw [gen8_val] at h0
  simp at h0

theorem conj_sZero_mem_wPlus
    {w : Equiv.Perm (Fin 240)} (hw : w ∈ wPlus) : sZero * w * sZero⁻¹ ∈ wPlus := by
  rw [mem_wPlus_iff] at hw ⊢
  refine ⟨mul_mem (mul_mem sZero_mem_wE8 hw.1) (inv_mem sZero_mem_wE8), ?_⟩
  rw [map_mul, map_mul, map_inv, hw.2, mul_one, mul_inv_cancel]

theorem sZero_inv :
    sZero⁻¹ = sZero :=
  inv_eq_of_mul_eq_one_right sZero_mul_self

@[expose] noncomputable def rAut :
    MulAut wPlus where
  toFun w := ⟨sZero * w * sZero⁻¹, conj_sZero_mem_wPlus w.2⟩
  invFun w := ⟨sZero * w * sZero⁻¹, conj_sZero_mem_wPlus w.2⟩
  left_inv w := Subtype.ext (by
    simp only [sZero_inv]
    rw [← mul_assoc, ← mul_assoc, sZero_mul_self, one_mul, mul_assoc, sZero_mul_self, mul_one])
  right_inv w := Subtype.ext (by
    simp only [sZero_inv]
    rw [← mul_assoc, ← mul_assoc, sZero_mul_self, one_mul, mul_assoc, sZero_mul_self, mul_one])
  map_mul' w w' := Subtype.ext (by
    simp only [Subgroup.coe_mul, sZero_inv]
    rw [show sZero * ((w : Equiv.Perm (Fin 240)) * w') * sZero =
      sZero * w * (sZero * sZero) * w' * sZero by rw [sZero_mul_self]; group]
    group)

theorem coe_rAut
    (w : wPlus) : ((rAut w : wPlus) : Equiv.Perm (Fin 240)) = sZero * w * sZero⁻¹ := rfl

theorem rAut_zPlus :
    rAut zPlus = zPlus :=
  Subtype.ext (by
    rw [coe_rAut]
    change sZero * zPerm * sZero⁻¹ = zPerm
    rw [comm_zPerm_of_mem sZero_mem_wE8, mul_inv_cancel_right])

theorem rAut_pow_zPlus
    (m : ℕ) : (rAut ^ m) zPlus = zPlus := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, MulAut.mul_apply, rAut_zPlus, ih]

@[expose] noncomputable def sZeroBar :
    Equiv.Perm (Fin 120) :=
  pHom ⟨sZero, sZero_mem_wE8⟩

theorem sZeroBar_mul_self :
    sZeroBar * sZeroBar = 1 := by
  rw [sZeroBar, ← map_mul, ← map_one pHom]
  exact congrArg pHom (Subtype.ext sZero_mul_self)

theorem sZeroBar_inv :
    sZeroBar⁻¹ = sZeroBar :=
  inv_eq_of_mul_eq_one_right sZeroBar_mul_self

theorem pPlus_rAut
    (w : wPlus) : pPlus (rAut w) = sZeroBar * pPlus w * sZeroBar⁻¹ := by
  rw [pPlus_apply, pPlus_apply, sZeroBar, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg pHom (Subtype.ext rfl)

theorem conj_sZeroBar_mem
    {x : Equiv.Perm (Fin 120)} (hx : x ∈ omega1T) : sZeroBar * x * sZeroBar⁻¹ ∈ omega1T := by
  rw [← range_pPlus] at hx ⊢
  obtain ⟨w, rfl⟩ := hx
  exact ⟨rAut w, pPlus_rAut w⟩

@[expose] noncomputable def graph1 :
    MulAut omega1T where
  toFun x := ⟨sZeroBar * x * sZeroBar⁻¹, conj_sZeroBar_mem x.2⟩
  invFun x := ⟨sZeroBar * x * sZeroBar⁻¹, conj_sZeroBar_mem x.2⟩
  left_inv x := Subtype.ext (by
    simp only [sZeroBar_inv]
    rw [← mul_assoc, ← mul_assoc, sZeroBar_mul_self, one_mul, mul_assoc, sZeroBar_mul_self,
      mul_one])
  right_inv x := Subtype.ext (by
    simp only [sZeroBar_inv]
    rw [← mul_assoc, ← mul_assoc, sZeroBar_mul_self, one_mul, mul_assoc, sZeroBar_mul_self,
      mul_one])
  map_mul' x x' := Subtype.ext (by
    simp only [Subgroup.coe_mul, sZeroBar_inv]
    rw [show sZeroBar * ((x : Equiv.Perm (Fin 120)) * x') * sZeroBar =
      sZeroBar * x * (sZeroBar * sZeroBar) * x' * sZeroBar by rw [sZeroBar_mul_self]; group]
    group)

theorem coe_graph1
    (x : omega1T) : ((graph1 x : omega1T) : Equiv.Perm (Fin 120)) =
      sZeroBar * x * sZeroBar⁻¹ := rfl

theorem pOnto_rAut
    (w : wPlus) : pOnto (rAut w) = graph1 (pOnto w) :=
  Subtype.ext (by rw [coe_graph1]; exact pPlus_rAut w)

@[expose] noncomputable def graphAut :
    MulAut omegaT :=
  omegaRestrictEquiv.trans (graph1.trans omegaRestrictEquiv.symm)

theorem graphAut_apply
    (g : omegaT) : graphAut g = omegaRestrictEquiv.symm (graph1 (omegaRestrictEquiv g)) := rfl

theorem graphAut_pOnto
    (w : wPlus) : graphAut (omegaRestrictEquiv.symm (pOnto w)) =
      omegaRestrictEquiv.symm (pOnto (rAut w)) := by
  rw [graphAut_apply, MulEquiv.apply_symm_apply, pOnto_rAut]

theorem graphAut_pow_pOnto
    (m : ℕ) (w : wPlus) : (graphAut ^ m) (omegaRestrictEquiv.symm (pOnto w)) =
      omegaRestrictEquiv.symm (pOnto ((rAut ^ m) w)) := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih => rw [pow_succ, MulAut.mul_apply, graphAut_pOnto, ih, pow_succ, MulAut.mul_apply]

theorem graphAut_pow_two :
    graphAut ^ 2 = 1 :=
  MulEquiv.ext fun g => by
    rw [pow_two, MulAut.mul_apply, graphAut_apply, graphAut_apply, MulEquiv.apply_symm_apply,
      MulAut.one_apply, MulEquiv.symm_apply_eq]
    exact Subtype.ext (by
      rw [coe_graph1, coe_graph1, sZeroBar_inv, ← mul_assoc, ← mul_assoc, sZeroBar_mul_self,
        one_mul, mul_assoc, sZeroBar_mul_self, mul_one])

theorem graphAut_not_mem_inner :
    graphAut ∉ inner omegaT := by
  rintro ⟨x, hx⟩
  set x₁ : Equiv.Perm (Fin 120) := ((omegaRestrictEquiv x : omega1T) : Equiv.Perm (Fin 120))
    with hx₁
  have hconj : ∀ y : omega1T, sZeroBar * y * sZeroBar⁻¹ = x₁ * y * x₁⁻¹ := by
    intro y
    have h := congrArg (fun α : MulAut omegaT => omegaRestrictEquiv (α (omegaRestrictEquiv.symm y)))
      hx
    simp only [graphAut_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply, map_mul, map_inv]
      at h
    have h' := congrArg Subtype.val h
    rw [coe_graph1] at h'
    rw [← h']
    rfl
  have hc : x₁⁻¹ * sZeroBar = 1 := by
    refine eq_one_of_comm_omega1T fun g hg => ?_
    have h := hconj ⟨g, hg⟩
    simp only at h
    calc x₁⁻¹ * sZeroBar * g = x₁⁻¹ * (sZeroBar * g * sZeroBar⁻¹) * sZeroBar := by group
      _ = x₁⁻¹ * (x₁ * g * x₁⁻¹) * sZeroBar := by rw [h]
      _ = g * (x₁⁻¹ * sZeroBar) := by group
  have hmem : sZeroBar ∈ omega1T := by
    rw [← inv_mul_eq_one.1 hc]
    exact (omegaRestrictEquiv x).2
  exact pHom_sZero_not_mem hmem

theorem exists_eq_conj_mul_triality_mul_graph
    (β : MulAut omegaT) :
    ∃ x : omegaT, ∃ k : Fin 3, ∃ ε : Fin 2,
      β = MulAut.conj x * trialityAut ^ (k : ℕ) * graphAut ^ (ε : ℕ) := by
  have : Finite (MulAut omegaT) := finite_mulAut_omegaT
  have : Finite (Outer omegaT) := Finite.of_surjective _ QuotientGroup.mk_surjective
  obtain ⟨k, ε, h⟩ := exists_eq_pow_mul_pow card_outer_omegaT
    (t := (QuotientGroup.mk trialityAut : Outer omegaT))
    (g := (QuotientGroup.mk graphAut : Outer omegaT))
    (by rw [← QuotientGroup.mk_pow, trialityAut_pow_three, QuotientGroup.mk_one])
    (fun h => trialityAut_not_mem_inner ((QuotientGroup.eq_one_iff _).1 h))
    (by rw [← QuotientGroup.mk_pow, graphAut_pow_two, QuotientGroup.mk_one])
    (fun h => graphAut_not_mem_inner ((QuotientGroup.eq_one_iff _).1 h))
    (QuotientGroup.mk β)
  rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul,
    QuotientGroup.eq_iff_div_mem] at h
  obtain ⟨x, hx⟩ := h
  refine ⟨x, k, ε, ?_⟩
  rw [hx, mul_assoc, div_mul_cancel]

end CFSG.Sporadic.Co1Patterson
