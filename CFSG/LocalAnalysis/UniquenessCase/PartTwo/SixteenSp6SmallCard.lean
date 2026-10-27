module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSp6SmallBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.Quasithin.SmithCurtis

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]

theorem s16sm_mQuot_add_rk {X : Type*} [Group X] [Finite X] {A B : Subgroup X} (hBA : B ≤ A) :
    E3.mQuot A B + rk ↥B = rk ↥A := by
  unfold E3.mQuot rk
  have h := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.2 hBA] at h
  rw [← padicValNat.mul (E3.relIndex_ne_zero' A B) Nat.card_pos.ne', h]

theorem s16sm_rk_eq_finrank [Finite W] (U : Subgroup W) :
    rk ↥U = Module.finrank (ZMod 2) ↥(s16smSubmod U) := by
  haveI : Module.Finite (ZMod 2) ↥(s16smSubmod U) := Module.Finite.of_finite
  have hcard : Nat.card ↥U = Nat.card ↥(s16smSubmod U) :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun _ => mem_s16smSubmod.symm)
  rw [rk, hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    padicValNat.prime_pow]

theorem s16sm_finrank_invariants [Finite W] {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)}
    (π : Γ →* ↥H) (hπ : Function.Surjective π) {U : Subgroup W} (hU : commSub U H = U) :
    Module.finrank (ZMod 2) ↥(s16smRepU π hU).invariants = rk ↥(U ⊓ fixV H) := by
  have hmap : Submodule.map (s16smSubmod U).subtype (s16smRepU π hU).invariants
      = s16smSubmod (U ⊓ fixV H) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨m, hm, rfl⟩
      rw [mem_s16smSubmod, Subgroup.mem_inf]
      exact ⟨mem_s16smSubmod.mp m.2, (s16sm_mem_invariants_iff π hπ hU m).mp hm⟩
    · intro hx
      rw [mem_s16smSubmod, Subgroup.mem_inf] at hx
      have hxU : x ∈ s16smSubmod U := mem_s16smSubmod.mpr hx.1
      exact ⟨⟨x, hxU⟩, (s16sm_mem_invariants_iff π hπ hU ⟨x, hxU⟩).mpr hx.2, rfl⟩
  rw [s16sm_rk_eq_finrank (U ⊓ fixV H),
    ← Submodule.finrank_map_subtype_eq (s16smSubmod U) (s16smRepU π hU).invariants, hmap]

theorem s16sm_finrank_quot_invariants [Finite W] {Γ : Type} [Group Γ]
    {H : Subgroup (MulAut W)} (π : Γ →* ↥H) (hπ : Function.Surjective π) {U : Subgroup W}
    (hU : commSub U H = U) :
    Module.finrank (ZMod 2) (↥(s16smSubmod U) ⧸ (s16smRepU π hU).invariants) =
      E3.mQuot U (U ⊓ fixV H) := by
  haveI : Module.Finite (ZMod 2) ↥(s16smSubmod U) := Module.Finite.of_finite
  have h1 := Submodule.finrank_quotient_add_finrank (s16smRepU π hU).invariants
  rw [s16sm_finrank_invariants π hπ hU, ← s16sm_rk_eq_finrank U] at h1
  have h2 := s16sm_mQuot_add_rk (A := U) (B := U ⊓ fixV H) inf_le_left
  omega

theorem s16sm_invariants_eq_bot_iff {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)}
    (π : Γ →* ↥H) (hπ : Function.Surjective π) {U : Subgroup W} (hU : commSub U H = U) :
    (s16smRepU π hU).invariants = ⊥ ↔ U ⊓ fixV H = ⊥ := by
  constructor
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hx' : Additive.ofMul x ∈ s16smSubmod U := mem_s16smSubmod.mpr hx.1
    have hmem : (⟨Additive.ofMul x, hx'⟩ : ↥(s16smSubmod U)) ∈
        (s16smRepU π hU).invariants :=
      (s16sm_mem_invariants_iff π hπ hU ⟨Additive.ofMul x, hx'⟩).mpr hx.2
    rw [h, Submodule.mem_bot] at hmem
    exact ofMul_eq_zero.mp (congrArg Subtype.val hmem)
  · intro h
    rw [Submodule.eq_bot_iff]
    intro m hm
    rw [s16sm_mem_invariants_iff π hπ hU] at hm
    have hmU : Additive.toMul (m : Additive W) ∈ U := m.2
    have hbot : Additive.toMul (m : Additive W) ∈ (⊥ : Subgroup W) := by
      rw [← h]
      exact Subgroup.mem_inf.mpr ⟨hmU, hm⟩
    have hm1 : Additive.toMul (m : Additive W) = 1 := by simpa using hbot
    exact Subtype.ext (by rw [← ofMul_toMul (m : Additive W), hm1, ofMul_one]; rfl)

theorem s16sm_nontrivial_iff (U : Subgroup W) :
    Nontrivial ↥(s16smSubmod U) ↔ U ≠ ⊥ := by
  rw [Submodule.nontrivial_iff_ne_bot]
  have h : s16smSubmod U = ⊥ ↔ U = ⊥ := by
    constructor
    · intro hS
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hmem : Additive.ofMul x ∈ s16smSubmod U := mem_s16smSubmod.mpr hx
      rw [hS] at hmem
      exact ofMul_eq_zero.mp (by simpa using hmem)
    · intro hU
      rw [Submodule.eq_bot_iff]
      intro x hx
      have hxU : Additive.toMul x ∈ U := mem_s16smSubmod.mp hx
      rw [hU] at hxU
      have hx1 : Additive.toMul x = 1 := by simpa using hxU
      rw [← ofMul_toMul x, hx1, ofMul_one]
  exact not_congr h

theorem s16sm_isIrrOn_of_simple {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (π : Γ →* ↥H)
    (hπ : Function.Surjective π) {U : Subgroup W} (hU : commSub U H = U)
    (h : IsSimpleRep (s16smRepU π hU)) : IsIrrOn H U ⊥ := by
  refine ⟨bot_lt_iff_ne_bot.mpr ((s16sm_nontrivial_iff U).mp h.1), ?_, ?_, ?_⟩
  · intro x hx u hu
    have hcomm : x u * u⁻¹ ∈ commSub U H := Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩
    rw [hU] at hcomm
    have : x u = x u * u⁻¹ * u := by group
    rw [this]
    exact U.mul_mem hcomm hu
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu
    simp [hu]
  · intro J hJ _ hJU
    let J' : Submodule (ZMod 2) ↥(s16smSubmod U) :=
      (s16smSubmod J).comap (s16smSubmod U).subtype
    have memJ' : ∀ w : ↥(s16smSubmod U), w ∈ J' ↔ Additive.toMul (w : Additive W) ∈ J := by
      intro w
      show w ∈ (s16smSubmod J).comap (s16smSubmod U).subtype ↔
        Additive.toMul (w : Additive W) ∈ J
      rw [Submodule.mem_comap, mem_s16smSubmod]
      rfl
    have hstable : ∀ γ : Γ, ∀ w ∈ J', s16smRepU π hU γ w ∈ J' := by
      intro γ w hw
      rw [memJ'] at hw ⊢
      have hwJ : Additive.toMul (w : Additive W) ∈ J := hw
      rw [s16smRepU_apply]
      have hw_eq : (w : Additive W) = Additive.ofMul (Additive.toMul (w : Additive W)) :=
        (ofMul_toMul _).symm
      rw [hw_eq, s16smRepW_apply]
      simpa using hJ (π γ) (π γ).2 _ hwJ
    rcases h.2 J' hstable with hbot | htop
    · left
      rw [Subgroup.eq_bot_iff_forall]
      intro u hu
      have hmemV : Additive.ofMul u ∈ s16smSubmod U := mem_s16smSubmod.mpr (hJU hu)
      have hmem : (⟨Additive.ofMul u, hmemV⟩ : ↥(s16smSubmod U)) ∈ J' := by
        rw [memJ']
        simpa [mem_s16smSubmod] using hu
      rw [hbot] at hmem
      have hzero : (⟨Additive.ofMul u, hmemV⟩ : ↥(s16smSubmod U)) = 0 := by
        simpa using hmem
      have hcongr := congrArg
        (fun z : ↥(s16smSubmod U) => Additive.toMul (z : Additive W)) hzero
      simpa using hcongr
    · right
      apply le_antisymm hJU
      intro u hu
      have hmemV : Additive.ofMul u ∈ s16smSubmod U := mem_s16smSubmod.mpr hu
      have hmem : (⟨Additive.ofMul u, hmemV⟩ : ↥(s16smSubmod U)) ∈ J' := by
        rw [htop]
        exact Submodule.mem_top
      have hmemJ : Additive.toMul (Additive.ofMul u) ∈ J := (memJ' _).mp hmem
      simpa using hmemJ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
