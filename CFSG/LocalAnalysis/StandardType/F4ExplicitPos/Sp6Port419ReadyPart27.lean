module

public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart21

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.FiniteAction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.StandardType.F4ExplicitPos.CentralizerGuard

noncomputable def rootSpanOver
    (Ω : Type*) [Field Ω] (F : Subfield Ω)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Subgroup (ModGL Tag.F4 Ω) :=
  Subgroup.closure {x | ∃ α ∈ Ψ, ∃ c : F, x = pinnedX Tag.F4 Ω α (c : Ω)}

theorem rootSpanOver_le_rootSpan
    (Ω : Type*) [Field Ω] (F : Subfield Ω)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    rootSpanOver Ω F Ψ ≤ rootSpan Tag.F4 Ω Ψ := by
  rw [rootSpanOver, Subgroup.closure_le]
  rintro x ⟨α, hα, c, rfl⟩
  rw [rootSpan]
  exact Subgroup.mem_iSup_of_mem α
    (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨(c : Ω), rfl⟩))

theorem exists_finset_coefficients
    (Ω : Type*) [Field Ω]
    {Ψ : Set (Fin Tag.F4.rank → ℤ)} {g : ModGL Tag.F4 Ω}
    (hg : g ∈ rootSpan Tag.F4 Ω Ψ) :
    ∃ T : Finset Ω, ∀ F : Subfield Ω, (∀ c ∈ T, c ∈ F) → g ∈ rootSpanOver Ω F Ψ := by
  classical
  rw [rootSpan_eq_closure] at hg
  refine Subgroup.closure_induction (p := fun g _ => ∃ T : Finset Ω,
      ∀ F : Subfield Ω, (∀ c ∈ T, c ∈ F) → g ∈ rootSpanOver Ω F Ψ)
    ?_ ?_ ?_ ?_ hg
  · rintro x ⟨α, hα, c, rfl⟩
    exact ⟨{c}, fun F hF => Subgroup.subset_closure
      ⟨α, hα, ⟨c, hF c (Finset.mem_singleton_self c)⟩, rfl⟩⟩
  · exact ⟨∅, fun F _ => one_mem _⟩
  · rintro x y hx hy ⟨T, hT⟩ ⟨U, hU⟩
    exact ⟨T ∪ U, fun F hF => mul_mem
      (hT F fun c hc => hF c (Finset.mem_union_left U hc))
      (hU F fun c hc => hF c (Finset.mem_union_right T hc))⟩
  · rintro x hx ⟨T, hT⟩
    exact ⟨T, fun F hF => inv_mem (hT F hF)⟩

theorem exists_frobeniusFixedSubfield_of_finset
    (Ω : Type*) [Field Ω] [CharP Ω 2]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    (S : Finset Ω) {k₀ : ℕ} (hk₀ : k₀ ≠ 0) :
    ∃ k, k ≠ 0 ∧ k₀ ∣ k ∧ ∀ x ∈ S, x ∈ TauCeti.frobeniusFixedSubfield Ω 2 k := by
  classical
  let := ZMod.algebra Ω 2
  have : Algebra.IsAlgebraic (ZMod 2) Ω := halg
  choose n hn hx using fun x : Ω => TauCeti.exists_mem_frobeniusFixedSubfield Ω 2 x
  refine ⟨k₀ * ∏ x ∈ S, n x,
    mul_ne_zero hk₀ (Finset.prod_ne_zero_iff.2 fun x _ => hn x),
    dvd_mul_right _ _, fun x hxS => ?_⟩
  exact TauCeti.frobeniusFixedSubfield_le_of_dvd
    (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem n hxS) _) (hx x)

theorem exists_frobeniusFixedSubfield_subfieldRootSpan
    (Ω : Type*) [Field Ω] [CharP Ω 2] [IsSepClosed Ω]
    (halg : letI := ZMod.algebra Ω 2; Algebra.IsAlgebraic (ZMod 2) Ω)
    {Ψ : Set (Fin Tag.F4.rank → ℤ)} {ι : Type*} [Finite ι]
    (g : ι → ModGL Tag.F4 Ω) (hg : ∀ i, g i ∈ rootSpan Tag.F4 Ω Ψ) :
    ∃ k : ℕ, k ≠ 0 ∧
      (∀ i, g i ∈ rootSpanOver Ω (TauCeti.frobeniusFixedSubfield Ω 2 k) Ψ) ∧
      4 ≤ Nat.card (TauCeti.frobeniusFixedSubfield Ω 2 k) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose T hT using fun i => exists_finset_coefficients Ω (hg i)
  obtain ⟨k, hk, hdiv, hmem⟩ :=
    exists_frobeniusFixedSubfield_of_finset Ω halg (Finset.univ.biUnion T)
      (k₀ := 2) (by norm_num)
  refine ⟨k, hk, fun i => hT i _ (fun c hc => hmem c ?_), ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc⟩
  · rw [TauCeti.card_frobeniusFixedSubfield (K := Ω) (p := 2) k hk]
    have hk2 : 2 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdiv
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

theorem ker_conj_inclusion_eq_center
    {G : Type*} [Group G] {H0 H : Subgroup G} (h0H : H0 ≤ H)
    (hguard : (Subgroup.center H0).map H0.subtype ≤ Subgroup.centralizer (H : Set G)) :
    ((MulAut.conj : H →* MulAut H).comp (Subgroup.inclusion h0H)).ker = Subgroup.center H0 := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have h : (Subgroup.inclusion h0H g) * (Subgroup.inclusion h0H k) *
        (Subgroup.inclusion h0H g)⁻¹ = Subgroup.inclusion h0H k := by
      have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hg) (Subgroup.inclusion h0H k)
      rwa [MonoidHom.comp_apply, MulAut.conj_apply, MulAut.one_apply] at this
    have h' := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] at h'
    have h'' : (↑g : G) * ↑k = ↑k * ↑g := by
      calc (↑g : G) * ↑k = (↑g * ↑k * (↑g)⁻¹) * ↑g := by group
        _ = ↑k * ↑g := by rw [h']
    simpa using h''.symm
  · intro hg
    rw [MonoidHom.mem_ker]
    ext x
    have hgH : (↑g : G) ∈ Subgroup.centralizer (H : Set G) :=
      hguard (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
    have hcomm : (↑g : G) * ↑x = ↑x * ↑g :=
      (Subgroup.mem_centralizer_iff.mp hgH (↑x) x.2).symm
    simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulAut.one_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [hcomm]
    group

theorem center_rootSpanOver_eq
    (Ω : Type*) [Field Ω] (F : Subfield Ω) [Fintype F]
    (hF : 4 ≤ Fintype.card F) (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    (Subgroup.center ↥(rootSpanOver Ω F Ψ)).map (rootSpanOver Ω F Ψ).subtype =
      rootSpanOver Ω F Ψ ⊓
        Subgroup.centralizer
          ((rootSpan Tag.F4 Ω Ψ : Subgroup (ModGL Tag.F4 Ω)) : Set (ModGL Tag.F4 Ω)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_inf]
    refine ⟨z.2, ?_⟩
    have hguard : ∀ α ∈ Ψ, ∀ c : Ω,
        (z : ModGL Tag.F4 Ω) * pinnedX Tag.F4 Ω α c =
          pinnedX Tag.F4 Ω α c * (z : ModGL Tag.F4 Ω) := by
      intro α hα
      refine commute_pinnedX_of_commute_subfield Ω F hF α (z : ModGL Tag.F4 Ω) ?_
      intro c
      have hmem : pinnedX Tag.F4 Ω α (c : Ω) ∈ rootSpanOver Ω F Ψ :=
        Subgroup.subset_closure ⟨α, hα, c, rfl⟩
      have hcz := Subgroup.mem_center_iff.mp hz
        ⟨pinnedX Tag.F4 Ω α (c : Ω), hmem⟩
      exact (congrArg Subtype.val hcz).symm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : rootSpan Tag.F4 Ω Ψ ≤
        Subgroup.centralizer ({↑z} : Set (ModGL Tag.F4 Ω)) := by
      rw [rootSpan]
      apply iSup_le; intro α
      apply iSup_le; intro hα
      rw [rootSubgroup, Subgroup.closure_le]
      rintro y ⟨c, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hguard α hα c).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxH0, hxcent⟩ := hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH0⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxcent (y : ModGL Tag.F4 Ω)
      (rootSpanOver_le_rootSpan Ω F Ψ y.2)

def conjAction {G : Type*} [Group G] {H0 H : Subgroup G} (h0H : H0 ≤ H) : H0 →* MulAut H :=
  (MulAut.conj : H →* MulAut H).comp (Subgroup.inclusion h0H)

noncomputable def quotientAction
    {G B : Type*} [Group G] [Group B]
    {H0 H : Subgroup G} (h0H : H0 ≤ H)
    (hguard : (Subgroup.center H0).map H0.subtype ≤ Subgroup.centralizer (H : Set G))
    (α : B →* MulAut H)
    (hinner : ∀ b : B, ∃ g : H0, conjAction h0H g = α b) :
    B →* H0 ⧸ Subgroup.center H0 :=
  let κ : H0 →* MulAut H := conjAction h0H
  let hker : κ.ker = Subgroup.center H0 := ker_conj_inclusion_eq_center h0H hguard
  let E : H0 ⧸ Subgroup.center H0 ≃* κ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange κ)
  E.symm.toMonoidHom.comp
    (α.codRestrict κ.range fun b => MonoidHom.mem_range.mpr (hinner b))

theorem quotientAction_ker
    {G B : Type*} [Group G] [Group B]
    {H0 H : Subgroup G} (h0H : H0 ≤ H)
    (hguard : (Subgroup.center H0).map H0.subtype ≤ Subgroup.centralizer (H : Set G))
    (α : B →* MulAut H)
    (hinner : ∀ b : B, ∃ g : H0, conjAction h0H g = α b) :
    (quotientAction h0H hguard α hinner).ker = α.ker := by
  let κ : H0 →* MulAut H := conjAction h0H
  let hker : κ.ker = Subgroup.center H0 := ker_conj_inclusion_eq_center h0H hguard
  let E : H0 ⧸ Subgroup.center H0 ≃* κ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange κ)
  have hβ : ∀ b : B, quotientAction h0H hguard α hinner b =
      E.symm (α.codRestrict κ.range (fun b => MonoidHom.mem_range.mpr (hinner b)) b) :=
    fun b => rfl
  ext b
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hβ b]
  constructor
  · intro hb
    have h1 : E (E.symm (α.codRestrict κ.range
        (fun b => MonoidHom.mem_range.mpr (hinner b)) b)) = E 1 := by rw [hb]
    rw [MulEquiv.apply_symm_apply, map_one] at h1
    simpa using Subtype.ext_iff.mp h1
  · intro hb
    have h1 : α.codRestrict κ.range
        (fun b => MonoidHom.mem_range.mpr (hinner b)) b = 1 := by
      apply Subtype.ext
      simpa using hb
    rw [h1, map_one]

end CFSG.StandardType.F4ExplicitPos.FiniteAction
end

end
