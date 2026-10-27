module

public import CFSG.RankThree.PartOne.LIT.McFrame

public section

namespace CFSG.RankThree.PartOne.LIT

open CFSG.RankThree.Classical (IsTransvectionWith invariant_of_generators)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
  (H : Subgroup (V ≃ₗ[ZMod p] V))

@[expose] def IsAplus (U : Submodule (ZMod p) V) (lam : Module.Dual (ZMod p) V) : Prop :=
  (∀ y ∈ U, lam y = 0) ∧ ∀ u ∈ U, TrIn H u lam

@[expose] def IsAminus (L : Submodule (ZMod p) V) (l : V) : Prop :=
  l ∈ L ∧ ∀ φ : Module.Dual (ZMod p) V, (∀ y ∈ L, φ y = 0) → TrIn H l φ

theorem exists_isAminus_of_isAplus
    (hirr : ∀ W : Submodule (ZMod p) V, (∀ h ∈ H, ∀ x ∈ W, h x ∈ W) → W = ⊥ ∨ W = ⊤)
    (hgen : ∃ S : Set (V ≃ₗ[ZMod p] V), (∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) ∧
      H = Subgroup.closure S)
    {U L : Submodule (ZMod p) V} (hF : IsFrame H U L)
    {ψ : Module.Dual (ZMod p) V} (hψ : IsAplus H U ψ) (hψ0 : ψ ≠ 0)
    (hone : ∀ lam, IsAplus H U lam → ∃ t : ZMod p, lam = t • ψ) :
    ∃ l, IsAminus H L l ∧ ψ l ≠ 0 := by
  obtain ⟨S, hS, hHS⟩ := hgen
  have hex : ∃ t ∈ S, ∃ z ∈ LinearMap.ker ψ,
      ¬ (t z ∈ LinearMap.ker ψ ∧ t⁻¹ z ∈ LinearMap.ker ψ) := by
    by_contra hno
    have hall : ∀ t ∈ S, ∀ z ∈ LinearMap.ker ψ,
        t z ∈ LinearMap.ker ψ ∧ t⁻¹ z ∈ LinearMap.ker ψ := by
      intro t ht z hz
      by_contra hc
      exact hno ⟨t, ht, z, hz, hc⟩
    rcases hirr (LinearMap.ker ψ) (invariant_of_generators hHS hall) with hbot | htop
    · have hU0 : U = ⊥ := by
        refine (Submodule.eq_bot_iff U).mpr fun u hu => ?_
        have : u ∈ LinearMap.ker ψ := LinearMap.mem_ker.mpr (hψ.1 u hu)
        rwa [hbot, Submodule.mem_bot] at this
      have hrk := hF.2.1
      rw [hU0, finrank_bot] at hrk
      omega
    · refine hψ0 (LinearMap.ext fun z => ?_)
      have : z ∈ LinearMap.ker ψ := by rw [htop]; trivial
      exact this
  obtain ⟨t, htS, y, hy, hty⟩ := hex
  obtain ⟨x, h, hxh⟩ := hS t htS
  have hTr : TrIn H x h := TrIn.of_isTransvectionWith (hHS ▸ Subgroup.subset_closure htS) hxh
  have hψy : ψ y = 0 := LinearMap.mem_ker.mp hy
  have hhy : h y ≠ 0 := by
    intro h0
    apply hty
    rw [hxh.2.2.2 y, hxh.inv_apply y, h0, zero_smul, add_zero, sub_zero]
    exact ⟨hy, hy⟩
  have hψx : ψ x ≠ 0 := by
    intro h0
    have hx : x ∈ LinearMap.ker ψ := h0
    apply hty
    rw [hxh.2.2.2 y, hxh.inv_apply y]
    exact ⟨(LinearMap.ker ψ).add_mem hy ((LinearMap.ker ψ).smul_mem _ hx),
      (LinearMap.ker ψ).sub_mem hy ((LinearMap.ker ψ).smul_mem _ hx)⟩
  obtain ⟨u₁, hu₁U, hu₁0, hhu₁⟩ := exists_ne_zero_ker_of_finrank_two hF.2.1 h
  have h2 : TrIn H u₁ h := by
    have := (TrIn.rule_R (hψ.2 u₁ hu₁U) hTr hhu₁).smul (ψ x)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hψx, one_smul] at this
  obtain ⟨fU, hfU⟩ : ∃ f : Module.Dual (ZMod p) V, f = h ∘ₗ hF.projU := ⟨_, rfl⟩
  obtain ⟨fL, hfL⟩ : ∃ f : Module.Dual (ZMod p) V, f = h ∘ₗ hF.projL := ⟨_, rfl⟩
  have hfU_app : ∀ z, fU z = h (hF.projU z) := fun z => by rw [hfU]; rfl
  have hfL_app : ∀ z, fL z = h (hF.projL z) := fun z => by rw [hfL]; rfl
  have hfU_L : ∀ l ∈ L, fU l = 0 := fun l hl => by rw [hfU_app, hF.projU_of_mem_L hl, map_zero]
  have hfL_U : ∀ u ∈ U, fL u = 0 := fun u hu => by rw [hfL_app, hF.projL_of_mem_U hu, map_zero]
  have hfU_U : ∀ u ∈ U, fU u = h u := fun u hu => by rw [hfU_app, hF.projU_of_mem hu]
  have hsplit : ∀ z, h z = fU z + fL z := fun z => by
    rw [hfU_app, hfL_app, ← map_add, hF.projU_add_projL]
  have hfL_eq : fL = h - fU := LinearMap.ext fun z => by
    rw [LinearMap.sub_apply, hsplit z]
    abel
  have hUtr : TrIn H u₁ fU := hF.2.2.2 u₁ hu₁U fU hfU_L (by rw [hfU_U u₁ hu₁U]; exact hhu₁)
  have hLtr : TrIn H u₁ fL := by
    rw [hfL_eq]
    exact h2.sub hUtr
  have hLA : IsAplus H U fL :=
    ⟨hfL_U, fun u hu => hF.trIn_center_of_vanish hu₁U hu hu₁0 hfL_U hLtr⟩
  obtain ⟨s, hs⟩ := hone fL hLA
  have hfLz : ∀ z, fL z = s * ψ z := fun z => by rw [hs, LinearMap.smul_apply, smul_eq_mul]
  have hfUy : fU y = h y := by
    have := hsplit y
    rw [hfLz y, hψy, mul_zero, add_zero] at this
    exact this.symm
  have hfU0 : fU ≠ 0 := fun h0 => hhy (by rw [← hfUy, h0, LinearMap.zero_apply])
  have hu₀U : hF.projU y ∈ U := hF.projU_mem y
  have hu₀ : h (hF.projU y) ≠ 0 := by rw [← hfU_app, hfUy]; exact hhy
  obtain ⟨u', hu'U, hu'h⟩ : ∃ u' ∈ U, h u' = s :=
    ⟨(s / h (hF.projU y)) • hF.projU y, U.smul_mem _ hu₀U, by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hu₀]⟩
  obtain ⟨hψu', E, hE, hEx⟩ := hψ.2 u' hu'U
  have hEinv : ∀ z, E.symm z = z - ψ z • u' := fun z => TrIn.inv_apply hψu' hEx z
  have hform : h ∘ₗ E.symm.toLinearMap = fU := LinearMap.ext fun z => by
    show h (E.symm z) = fU z
    rw [hEinv z, map_sub, map_smul, hu'h, smul_eq_mul, hsplit z, hfLz z]
    ring
  have hconj := hTr.conj hE
  rw [hform, hEx x] at hconj
  obtain ⟨x', hx'⟩ : ∃ x', x' = x + ψ x • u' := ⟨_, rfl⟩
  rw [← hx'] at hconj
  have hψx' : ψ x' = ψ x := by rw [hx', map_add, map_smul, hψu', smul_zero, add_zero]
  have hcU : hF.projU x' ∈ U := hF.projU_mem x'
  have hxL : hF.projL x' ∈ L := hF.projL_mem x'
  have hψxL : ψ (hF.projL x') = ψ x := by
    have := congrArg ψ (hF.projU_add_projL x')
    rwa [map_add, hψ.1 _ hcU, zero_add, hψx'] at this
  have hxLtr : TrIn H (hF.projL x') fU := by
    by_cases hc0 : hF.projU x' = 0
    · have := hF.projU_add_projL x'
      rw [hc0, zero_add] at this
      rwa [← this] at hconj
    · have hfc : fU (hF.projU x') = 0 := by
        rw [hfU_U _ hcU, ← hfU_app]
        exact hconj.1
      have hct : TrIn H (hF.projU x') fU := hF.2.2.2 _ hcU fU hfU_L hfc
      have hneg : TrIn H (-hF.projU x') fU := by
        have hsm : TrIn H (hF.projU x') ((-1 : ZMod p) • fU) := hct.smul (-1)
        have hcen := TrIn.smul_center_iff.mpr hsm
        rwa [neg_smul, one_smul] at hcen
      have := TrIn.add_center hconj hneg
      rwa [← sub_eq_add_neg, ← eq_sub_of_add_eq' (hF.projU_add_projL x')] at this
  refine ⟨hF.projL x', ⟨hxL, fun φ hφ => ?_⟩, by rw [hψxL]; exact hψx⟩
  exact hF.trIn_axis_of_vanish hxL hfU_L hφ hfU0 hxLtr

end CFSG.RankThree.PartOne.LIT
