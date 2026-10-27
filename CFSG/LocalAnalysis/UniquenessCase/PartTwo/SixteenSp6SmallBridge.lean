module

public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup CFSG.Quasithin.SmithCurtis

variable {W : Type} [CommGroup W] [Module (ZMod 2) (Additive W)]

@[expose] noncomputable def s16smRepW {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)}
    (π : Γ →* ↥H) : Representation (ZMod 2) Γ (Additive W) where
  toFun γ := AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive ((π γ : MulAut W).toMonoidHom))
  map_one' := by
    ext m
    simp
  map_mul' γ δ := by
    ext m
    simp

theorem s16smRepW_apply {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (π : Γ →* ↥H) (γ : Γ)
    (w : W) : s16smRepW π γ (Additive.ofMul w) = Additive.ofMul ((π γ : MulAut W) w) :=
  rfl

@[expose] def s16smSubmod (U : Subgroup W) : Submodule (ZMod 2) (Additive W) where
  carrier := {x | Additive.toMul x ∈ U}
  add_mem' {a b} ha hb := U.mul_mem ha hb
  zero_mem' := U.one_mem
  smul_mem' c x hx := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simpa using U.one_mem
    · simpa using hx

theorem mem_s16smSubmod {U : Subgroup W} {x : Additive W} :
    x ∈ s16smSubmod U ↔ Additive.toMul x ∈ U := Iff.rfl

theorem s16sm_stable_of_comm {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (π : Γ →* ↥H)
    {U : Subgroup W} (hU : commSub U H = U) :
    ∀ γ, s16smSubmod U ≤ (s16smSubmod U).comap (s16smRepW π γ) := by
  intro γ x hx
  rw [mem_s16smSubmod] at hx
  rw [Submodule.mem_comap, mem_s16smSubmod]
  have hmem : (π γ : MulAut W) (Additive.toMul x) ∈ U := by
    have hc : (π γ : MulAut W) (Additive.toMul x) * (Additive.toMul x)⁻¹ ∈
        commSub U H :=
      Subgroup.subset_closure ⟨(π γ : MulAut W), (π γ).2, Additive.toMul x, hx, rfl⟩
    rw [hU] at hc
    have hsplit : (π γ : MulAut W) (Additive.toMul x) =
        ((π γ : MulAut W) (Additive.toMul x) * (Additive.toMul x)⁻¹) *
          Additive.toMul x := by
      group
    rw [hsplit]
    exact U.mul_mem hc hx
  rw [← ofMul_toMul x, s16smRepW_apply]
  simpa using hmem

@[expose] noncomputable def s16smRepU {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)}
    (π : Γ →* ↥H) {U : Subgroup W} (hU : commSub U H = U) :
    Representation (ZMod 2) Γ ↥(s16smSubmod U) :=
  (s16smRepW π).subrepresentation (s16smSubmod U) (s16sm_stable_of_comm π hU)

theorem s16smRepU_apply {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (π : Γ →* ↥H)
    {U : Subgroup W} (hU : commSub U H = U) (γ : Γ) (m : ↥(s16smSubmod U)) :
    ((s16smRepU π hU γ m : ↥(s16smSubmod U)) : Additive W) = s16smRepW π γ (m : Additive W) :=
  rfl

private theorem s16sm_repW_fix_iff {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (π : Γ →* ↥H)
    (γ : Γ) (m : Additive W) :
    s16smRepW π γ m = m ↔ (π γ : MulAut W) (Additive.toMul m) = Additive.toMul m := by
  constructor
  · intro h
    rw [← ofMul_toMul m] at h
    have h' := congrArg Additive.toMul h
    rwa [s16smRepW_apply, toMul_ofMul] at h'
  · intro h
    rw [← ofMul_toMul m, s16smRepW_apply, h]

theorem s16sm_hperf_of_comm {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (π : Γ →* ↥H)
    (hπ : Function.Surjective π) {U : Subgroup W} (hU : commSub U H = U)
    (ψ : ↥(s16smSubmod U) →ₗ[ZMod 2] ZMod 2)
    (hψ : ∀ γ m, ψ (s16smRepU π hU γ m) = ψ m) : ψ = 0 := by
  ext m
  simp only [LinearMap.zero_apply]
  have key : ∀ u : W, u ∈ commSub U H →
      ∃ v : ↥(s16smSubmod U), (v : Additive W) = Additive.ofMul u ∧ ψ v = 0 := by
    intro u hu
    refine Subgroup.closure_induction (p := fun u _ =>
      ∃ v : ↥(s16smSubmod U), (v : Additive W) = Additive.ofMul u ∧ ψ v = 0)
      ?_ ?_ ?_ ?_ hu
    · rintro c ⟨a, ha, l, hl, rfl⟩
      obtain ⟨γ, hγ⟩ := hπ ⟨a, ha⟩
      have hγ' : (π γ : MulAut W) = a := congrArg Subtype.val hγ
      have hl0 : Additive.ofMul l ∈ s16smSubmod U := by
        rw [mem_s16smSubmod, toMul_ofMul]
        exact hl
      refine ⟨s16smRepU π hU γ ⟨Additive.ofMul l, hl0⟩ -
        ⟨Additive.ofMul l, hl0⟩, ?_, ?_⟩
      · simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_neg, Subtype.coe_mk,
          s16smRepU_apply, s16smRepW_apply, hγ', ofMul_mul, ofMul_inv, sub_eq_add_neg]
      · rw [map_sub, hψ γ ⟨Additive.ofMul l, hl0⟩, sub_self]
    · exact ⟨0, by simp, by simp⟩
    · rintro x y hx hy ⟨vx, hvx, hx0⟩ ⟨vy, hvy, hy0⟩
      refine ⟨vx + vy, ?_, ?_⟩
      · simp only [Submodule.coe_add, hvx, hvy, ofMul_mul]
      · rw [map_add, hx0, hy0, add_zero]
    · rintro x hx ⟨vx, hvx, hx0⟩
      refine ⟨-vx, ?_, ?_⟩
      · simp only [Submodule.coe_neg, hvx, ofMul_inv]
      · rw [map_neg, hx0, neg_zero]
  have hm : Additive.toMul (m : Additive W) ∈ commSub U H := by
    rw [hU]
    exact mem_s16smSubmod.mp m.2
  obtain ⟨v, hv, hv0⟩ := key _ hm
  have hvm : v = m := Subtype.ext (by rw [hv, ofMul_toMul])
  rw [← hv0, ← hvm]

theorem s16sm_mem_invariants_iff {Γ : Type} [Group Γ] {H : Subgroup (MulAut W)} (π : Γ →* ↥H)
    (hπ : Function.Surjective π) {U : Subgroup W} (hU : commSub U H = U)
    (m : ↥(s16smSubmod U)) :
    m ∈ (s16smRepU π hU).invariants ↔ Additive.toMul (m : Additive W) ∈ fixV H := by
  rw [Representation.mem_invariants, mem_fixV]
  constructor
  · intro hm a ha
    obtain ⟨γ, hγ⟩ := hπ ⟨a, ha⟩
    have hγ' : (π γ : MulAut W) = a := congrArg Subtype.val hγ
    have h1 : s16smRepW π γ (m : Additive W) = (m : Additive W) := by
      have hc := congrArg (fun z : ↥(s16smSubmod U) => (z : Additive W)) (hm γ)
      rwa [s16smRepU_apply] at hc
    have h2 := (s16sm_repW_fix_iff π γ (m : Additive W)).1 h1
    rwa [hγ'] at h2
  · intro hm γ
    apply Subtype.ext
    rw [s16smRepU_apply]
    exact (s16sm_repW_fix_iff π γ (m : Additive W)).2 (hm (π γ) (π γ).2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
