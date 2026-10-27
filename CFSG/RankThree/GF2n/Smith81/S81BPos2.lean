module

public import CFSG.RankThree.GF2n.Smith81.S81BPos

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {V : Type} [AddCommGroup V] [Module K V] {ψ : M₀.E ≃ₗ[K] V}
  {φ : Lgen M (LB M Q B) →* (V ≃ₗ[K] V)} {Γ : Subgroup (V ≃ₗ[K] V)} {p₀ : V}
  {U₀ : Subgroup (V ≃ₗ[K] V)}

theorem EGeom.EUniData.le_QB_iff (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {B' C' : Subgroup G}
    (hB' : Ctx M Q Z B') (hC' : Ctx M Q Z C') {gB gC : V ≃ₗ[K] V} (hgB : d.IsPt B' gB)
    (hgC : d.IsPt C' gC) {n : ℕ} (hcard : Nat.card ↥(Q ⊓ QB B') = Nat.card Z ^ (n + 1))
    (hW : Nat.card (Wsp (Submodule.span K {p₀}) U₀) ≤ Nat.card K ^ n)
    (hK : Nat.card K = Nat.card Z) (hp₀ : p₀ ≠ 0) (hU : ∀ u ∈ U₀, u p₀ = p₀) :
    C' ≤ QB B' ↔ gB⁻¹ (gC p₀) ∈ Wsp (Submodule.span K {p₀}) U₀ := by
  have hWmap : Wsp (Submodule.span K {gB p₀}) (conjSub gB U₀) =
      (Wsp (Submodule.span K {p₀}) U₀).map (gB : V →ₗ[K] V) := by
    have h := Wsp_map gB (Submodule.span K {p₀}) U₀
    rw [Submodule.map_span, Set.image_singleton] at h
    exact h
  have hmemW : ∀ x : V, x ∈ Wsp (Submodule.span K {gB p₀}) (conjSub gB U₀) ↔
      gB⁻¹ x ∈ Wsp (Submodule.span K {p₀}) U₀ := by
    intro x
    rw [hWmap, Submodule.mem_map_equiv, LinearEquiv.coe_inv]
  have hp0W : p₀ ∈ Wsp (Submodule.span K {p₀}) U₀ :=
    mem_Wsp.mpr fun u hu => by rw [hU u hu, sub_self]; exact Submodule.zero_mem _
  have hgBW : gB p₀ ∈ Wsp (Submodule.span K {gB p₀}) (conjSub gB U₀) := by
    refine (hmemW (gB p₀)).mpr ?_
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hp0W
  have hspanW : Submodule.span K {gB p₀} ≤ Wsp (Submodule.span K {gB p₀}) (conjSub gB U₀) :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hgBW)
  by_cases hE : EPosEq Z B' C'
  · have hspan := (d.epos_eq_iff hB' hC' hgB hgC).mp hE
    have hgCW : gC p₀ ∈ Wsp (Submodule.span K {gB p₀}) (conjSub gB U₀) := by
      apply hspanW
      rw [← hspan]
      exact Submodule.mem_span_singleton_self _
    exact ⟨fun _ => (hmemW (gC p₀)).mp hgCW, fun _ => EPosEq.le_QB hB' hE⟩
  · have hne : Submodule.span K {gC p₀} ≠ Submodule.span K {gB p₀} :=
      fun h => hE ((d.epos_eq_iff hB' hC' hgB hgC).mpr h)
    constructor
    · intro hle
      have hQ : EPosQ Z B' C' := ⟨hE, hle⟩
      exact (hmemW (gC p₀)).mp ((d.epos_Q_iff hB' hC' hgB hgC hcard hW hK).mp hQ).2
    · intro hmem
      have hQ : EPosQ Z B' C' := (d.epos_Q_iff hB' hC' hgB hgC hcard hW hK).mpr
        ⟨hne, (hmemW (gC p₀)).mpr hmem⟩
      exact hQ.2

theorem EGeom.EUniData.le_normalizer_iff (hg : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {B' C' : Subgroup G} (hB' : Ctx M Q Z B')
    (hC' : Ctx M Q Z C') {gB gC : V ≃ₗ[K] V} (hgB : d.IsPt B' gB) (hgC : d.IsPt C' gC)
    {β : V →ₗ[K] V →ₗ[K] K} (hβ : ∀ g ∈ Γ, ∀ v w : V, β (g v) (g w) = β v w)
    (hskew : ∀ v w : V, β v w = - β w v) {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f)) :
    C' ≤ Subgroup.normalizer (B' : Set G) ↔ β p₀ (gB⁻¹ (gC p₀)) = 0 := by
  have hinv : ∀ x : V, gB (gB⁻¹ x) = x := fun x => by
    rw [LinearEquiv.coe_inv]
    exact gB.apply_symm_apply x
  have key : β (gC p₀) (gB p₀) = - β p₀ (gB⁻¹ (gC p₀)) := by
    calc β (gC p₀) (gB p₀) = β (gB (gB⁻¹ (gC p₀))) (gB p₀) := by rw [hinv]
      _ = β (gB⁻¹ (gC p₀)) p₀ := hβ gB hgB.1 _ _
      _ = - β p₀ (gB⁻¹ (gC p₀)) := hskew _ _
  rw [Ctx.le_normalizer_iff_comm hB' hC', d.comm_iff_beta hg hB' hC' hgB hgC hlam hform, key,
    neg_eq_zero]

theorem EGeom.EUniData.exists_ctx_with_class (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀)
    (hB : Ctx M Q Z B) (hp₀ : p₀ ≠ 0) {B' : Subgroup G} {gB : V ≃ₗ[K] V} (hgB : d.IsPt B' gB)
    {g : V ≃ₗ[K] V} (hg : g ∈ Γ) :
    ∃ C' : Subgroup G, Ctx M Q Z C' ∧ ∃ gC : V ≃ₗ[K] V, d.IsPt C' gC ∧
      ∃ c : K, c ≠ 0 ∧ gB⁻¹ (gC p₀) = c • g p₀ := by
  obtain ⟨hgBΓ, -, -⟩ := hgB
  obtain ⟨D, hD, himgD⟩ := d.exists_ctx_point hB hp₀ (Γ.mul_mem hgBΓ hg)
  obtain ⟨gC, hgC⟩ := d.exists_isPt hD
  refine ⟨D, hD, gC, hgC, ?_⟩
  obtain ⟨-, himgC, -⟩ := hgC
  have hmem : gC p₀ ∈ Submodule.span K {(gB * g) p₀} := by
    have h1 : gC p₀ ∈ (fun a : G => ψ (M₀.π a)) '' (D : Set G) := by
      rw [himgC]
      exact SetLike.mem_coe.2 (Submodule.mem_span_singleton_self _)
    rw [himgD] at h1
    exact SetLike.mem_coe.1 h1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hc
    exact hp₀ (gC.map_eq_zero_iff.1 hc.symm)
  · rw [← hc, map_smul, LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

theorem EGeom.EUniData.pos_classes (hg : GlobalModelData M Q Z γ M₀)
    (d : EUniData M Q Z B M₀ ψ φ Γ p₀ U₀) {n : ℕ} {B' C' : Subgroup G} (hB' : Ctx M Q Z B')
    (hC' : Ctx M Q Z C') {gB gC : V ≃ₗ[K] V} (hgB : d.IsPt B' gB) (hgC : d.IsPt C' gC)
    (hcard : Nat.card ↥(Q ⊓ QB B') = Nat.card Z ^ (n + 1))
    (hW : Nat.card (Wsp (Submodule.span K {p₀}) U₀) ≤ Nat.card K ^ n)
    (hK : Nat.card K = Nat.card Z) (hp₀ : p₀ ≠ 0) (hU : ∀ u ∈ U₀, u p₀ = p₀)
    {β : V →ₗ[K] V →ₗ[K] K} (hβ : ∀ g ∈ Γ, ∀ v w : V, β (g v) (g w) = β v w)
    (hskew : ∀ v w : V, β v w = - β w v) {lam : K} (hlam : lam ≠ 0)
    (hform : ∀ e f : M₀.E, M₀.B e f = lam * β (ψ e) (ψ f)) :
    (EPosEq Z B' C' ↔ gB⁻¹ (gC p₀) ∈ Submodule.span K {p₀}) ∧
    (EPosQ Z B' C' ↔ gB⁻¹ (gC p₀) ∈ Wsp (Submodule.span K {p₀}) U₀ ∧
      gB⁻¹ (gC p₀) ∉ Submodule.span K {p₀}) ∧
    (EPosM B' C' ↔ β p₀ (gB⁻¹ (gC p₀)) = 0 ∧
      gB⁻¹ (gC p₀) ∉ Wsp (Submodule.span K {p₀}) U₀) ∧
    (EPosOpp B' C' ↔ β p₀ (gB⁻¹ (gC p₀)) ≠ 0) := by
  have hx0 : gC p₀ ≠ 0 := fun h => hp₀ (gC.injective (by rw [h, map_zero]))
  have key1 : ∀ x : V, gB⁻¹ x ∈ Submodule.span K {p₀} ↔ x ∈ Submodule.span K {gB p₀} := by
    intro x
    have hx : gB (gB⁻¹ x) = x := gB.apply_symm_apply x
    rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← hx, ← ha, map_smul]⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, gB.injective (by rw [hx, map_smul, ha])⟩
  have hspan : Submodule.span K {gC p₀} = Submodule.span K {gB p₀} ↔
      gC p₀ ∈ Submodule.span K {gB p₀} := by
    constructor
    · intro h
      rw [← h]
      exact Submodule.mem_span_singleton_self _
    · intro h
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
      have ha0 : a ≠ 0 := fun h0 => hx0 (by rw [← ha, h0, zero_smul])
      have hgBp : gB p₀ = a⁻¹ • gC p₀ := by
        rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
      apply le_antisymm
      · exact (Submodule.span_singleton_le_iff_mem _ _).mpr h
      · rw [Submodule.span_singleton_le_iff_mem, hgBp]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hE : EPosEq Z B' C' ↔ gB⁻¹ (gC p₀) ∈ Submodule.span K {p₀} :=
    (d.epos_eq_iff hB' hC' hgB hgC).trans (hspan.trans (key1 (gC p₀)).symm)
  have hQ : C' ≤ QB B' ↔ gB⁻¹ (gC p₀) ∈ Wsp (Submodule.span K {p₀}) U₀ :=
    d.le_QB_iff hB' hC' hgB hgC hcard hW hK hp₀ hU
  have hN : C' ≤ Subgroup.normalizer (B' : Set G) ↔ β p₀ (gB⁻¹ (gC p₀)) = 0 :=
    d.le_normalizer_iff hg hB' hC' hgB hgC hβ hskew hlam hform
  refine ⟨hE, ?_, ?_, not_congr hN⟩
  · constructor
    · rintro ⟨hne, hle⟩
      exact ⟨hQ.mp hle, fun hs => hne (hE.mpr hs)⟩
    · rintro ⟨hr, hs⟩
      exact And.intro (fun h => hs (hE.mp h)) (hQ.mpr hr)
  · constructor
    · rintro ⟨hle, hnq⟩
      exact ⟨hN.mp hle, fun hr => hnq (hQ.mpr hr)⟩
    · rintro ⟨h0, hr⟩
      exact And.intro (hN.mpr h0) (fun hle => hr (hQ.mp hle))

end CFSG.RankThree.GF2n.Smith81
