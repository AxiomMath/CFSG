module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankJReflection
import CFSG.LocalAnalysis.StandardType.GGF4NbrAutReflKGReduce

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pjs_mem_normalizer_of_conj_mem_inv_conj_mem {M : Type} [Group M] {H : Subgroup M}
    {g : M} (h₁ : ∀ k ∈ H, g * k * g⁻¹ ∈ H) (h₂ : ∀ k ∈ H, g⁻¹ * k * g⁻¹⁻¹ ∈ H) :
    g ∈ Subgroup.normalizer (H : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨h₁ k, fun hk => ?_⟩
  have h := h₂ _ hk
  rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at h

private theorem pjs_conj_mul_centralizer_eq {G : Type} [Group G] {X : Subgroup G} {g y c : G}
    (hgX : g ∈ X) (hc : c ∈ Subgroup.centralizer (X : Set G)) :
    g * (y * c) * g⁻¹ = g * y * g⁻¹ * c := by
  have h := Subgroup.mem_centralizer_iff.mp hc g hgX
  calc g * (y * c) * g⁻¹ = g * y * g⁻¹ * (g * c) * g⁻¹ := by group
    _ = g * y * g⁻¹ * (c * g) * g⁻¹ := by rw [h]
    _ = g * y * g⁻¹ * c := by group

private theorem pjs_ggAutomizer_eq_map_ggExtAut {G : Type} [Group G] {Bs X J : Subgroup G}
    (hJX : J ≤ X)
    (μ : ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≃* ↥Bs)
    (hμ : ∀ q, (μ q : G) = q.1 * q.2) :
    ggAutomizer J Bs = (ggAutomizer J (Bs ⊓ X)).map (F4AutRefl.ggExtAut μ) := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨g, hgJ, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    have hgX : g ∈ X := hJX hgJ
    have hgN₀ : g ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_normalizer_iff.mp hgN h)
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hgX) h)
    refine ⟨ggConjAut (Bs ⊓ X) hgN₀, ggConjAut_mem_ggAutomizer hgJ hgN₀, ?_⟩
    ext b
    obtain ⟨q, rfl⟩ := μ.surjective b
    simp only [F4AutRefl.ggExtAut_apply, hμ, hφg, ggConjAut_apply]
    exact (pjs_conj_mul_centralizer_eq hgX q.2.2.2).symm
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨g, hgJ, hgN, hψg⟩ := mem_ggAutomizer_iff.mp hψ
    have hgX : g ∈ X := hJX hgJ
    have hconj : ∀ g' ∈ X, g' ∈ Subgroup.normalizer ((Bs ⊓ X : Subgroup G) : Set G) →
        ∀ k ∈ Bs, g' * k * g'⁻¹ ∈ Bs := by
      intro g' hg'X hg'N k hk
      obtain ⟨q, hq⟩ := μ.surjective ⟨k, hk⟩
      have hk' : k = q.1 * q.2 := by rw [← hμ q, hq]
      rw [hk', pjs_conj_mul_centralizer_eq hg'X q.2.2.2]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp hg'N q.1).mp q.1.2).1 q.2.2.1
    have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) :=
      pjs_mem_normalizer_of_conj_mem_inv_conj_mem (hconj g hgX hgN)
        (hconj g⁻¹ (inv_mem hgX) (Subgroup.inv_mem _ hgN))
    rw [mem_ggAutomizer_iff]
    refine ⟨g, hgJ, hgBs, fun b => ?_⟩
    obtain ⟨q, rfl⟩ := μ.surjective b
    simp only [F4AutRefl.ggExtAut_apply, hμ, hψg]
    exact (pjs_conj_mul_centralizer_eq hgX q.2.2.2).symm

theorem ggMaxRank_automizerSplit {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X J : Subgroup G}
    (hJX : J ≤ X)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ X, ∃ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), b = a * c)
    (hdisj : Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    ∃ e : ↥(ggAutomizer J Bs) ≃* ↥(ggAutomizer J (Bs ⊓ X)),
      ∀ φ : ↥(ggAutomizer J Bs), GGIsReflection p (φ : MulAut ↥Bs) ↔
        GGIsReflection p (e φ : MulAut ↥(Bs ⊓ X)) := by
  have hB₀ : Bs ⊓ X ≤ Bs := inf_le_left
  have hC₀ : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ Bs := inf_le_left
  have hcomm : ∀ y ∈ Bs ⊓ X, ∀ c ∈ Bs ⊓ Subgroup.centralizer (X : Set G), y * c = c * y := by
    intro y hy c hc
    exact Subgroup.mem_centralizer_iff.mp hc.2 y hy.2
  have hdisj' : ∀ y ∈ Bs ⊓ X, y ∈ Bs ⊓ Subgroup.centralizer (X : Set G) → y = 1 := by
    intro y hy hc
    have hybot : y ∈ Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G) :=
      Subgroup.mem_inf.mpr ⟨hy, hc.2⟩
    rw [hdisj] at hybot
    exact Subgroup.mem_bot.mp hybot
  obtain ⟨μ, hμ⟩ := F4AutRefl.exists_mulEquiv_prod_of_split hB₀ hC₀ hcomm hdisj' hsplit
  have hAut := pjs_ggAutomizer_eq_map_ggExtAut hJX μ hμ
  let f : ↥(ggAutomizer J (Bs ⊓ X)) →* ↥(ggAutomizer J Bs) :=
    { toFun := fun ψ =>
        ⟨F4AutRefl.ggExtAut μ (ψ : MulAut ↥(Bs ⊓ X)), by
          rw [hAut]
          exact ⟨(ψ : MulAut ↥(Bs ⊓ X)), ψ.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one (F4AutRefl.ggExtAut μ))
      map_mul' := fun ψ ψ' => Subtype.ext (map_mul (F4AutRefl.ggExtAut μ) _ _) }
  have hinj : Function.Injective f := by
    intro ψ ψ' h
    apply Subtype.ext
    apply F4AutRefl.ggExtAut_injective μ
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro φ
    have hφ : (φ : MulAut ↥Bs) ∈ (ggAutomizer J (Bs ⊓ X)).map (F4AutRefl.ggExtAut μ) := by
      rw [← hAut]
      exact φ.2
    obtain ⟨ψ, hψ, hψeq⟩ := hφ
    refine ⟨⟨ψ, hψ⟩, Subtype.ext ?_⟩
    exact hψeq
  have hfb : Function.Bijective f := ⟨hinj, hsurj⟩
  let gE : ↥(ggAutomizer J (Bs ⊓ X)) ≃* ↥(ggAutomizer J Bs) :=
    MulEquiv.ofBijective f hfb
  let e : ↥(ggAutomizer J Bs) ≃* ↥(ggAutomizer J (Bs ⊓ X)) := gE.symm
  refine ⟨e, fun φ => ?_⟩
  have h1 : (F4AutRefl.ggExtAut μ
      ((e φ : ↥(ggAutomizer J (Bs ⊓ X))) : MulAut ↥(Bs ⊓ X)) : MulAut ↥Bs) =
      (φ : MulAut ↥Bs) := by
    have h3 := congrArg Subtype.val (MulEquiv.apply_symm_apply gE φ)
    exact h3
  rw [← h1]
  exact F4AutRefl.ggIsReflection_ggExtAut_iff μ
    ((e φ : ↥(ggAutomizer J (Bs ⊓ X))) : MulAut ↥(Bs ⊓ X))

end CFSG.StandardType

end
