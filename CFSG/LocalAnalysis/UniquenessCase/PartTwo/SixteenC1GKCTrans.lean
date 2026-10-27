module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCTransChk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCTransW
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GKCForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LargeExtraspecial.O62 CFSG.RankThree.OrthogonalInvolutions

theorem s16c1c_conj_mem_omega {g x : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ true) (hx : x ∈ Ω₀ true) :
    g * x * g⁻¹ ∈ Ω₀ true := by
  have hL : ∀ v, qModel true (g v) = qModel true v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have h := (mem_omegaGroup_conjL (qModel_nondegenerate true) (qModel_nondegenerate true)
    hL (g := x)).mpr hx
  have e : conjL g x = g * x * g⁻¹ := LinearEquiv.ext fun v => rfl
  rwa [e] at h

private theorem s16c1c_conj_apply {g₀ x : V₀ ≃ₗ[ZMod 2] V₀} (v : V₀) :
    x (g₀ v) = g₀ ((MulAut.conj g₀⁻¹) x v) := by
  simp [MulAut.conj_apply]

private theorem s16c1c_transfer_trans {g₀ x : V₀ ≃ₗ[ZMod 2] V₀} {w : V₀} (hw : w ≠ 0)
    (h1 : ∀ u, (MulAut.conj g₀⁻¹) x u - u = 0 ∨ (MulAut.conj g₀⁻¹) x u - u = w)
    (h2 : ∃ u, (MulAut.conj g₀⁻¹) x u - u = w) :
    ∃ w₀ : V₀, w₀ ≠ 0 ∧ (∀ u, x u - u = 0 ∨ x u - u = w₀) ∧ ∃ u, x u - u = w₀ := by
  have hkey : ∀ v, x (g₀ v) - g₀ v = g₀ ((MulAut.conj g₀⁻¹) x v - v) := by
    intro v
    rw [s16c1c_conj_apply (g₀ := g₀) (x := x) v, ← map_sub]
  refine ⟨g₀ w, fun h => hw (g₀.injective (by simpa using h)), ?_, ?_⟩
  · intro u
    have hsub : x u - u = g₀ ((MulAut.conj g₀⁻¹) x (g₀.symm u) - g₀.symm u) := by
      simpa using hkey (g₀.symm u)
    rcases h1 (g₀.symm u) with h | h
    · left; rw [hsub, h, map_zero]
    · right; rw [hsub, h]
  · obtain ⟨u₀, hu₀⟩ := h2
    refine ⟨g₀ u₀, ?_⟩
    rw [hkey u₀, hu₀]

private theorem s16c1c_transfer_span {g₀ x₁ x₂ : V₀ ≃ₗ[ZMod 2] V₀}
    (h : ∀ u, ∃ u₁, (MulAut.conj g₀⁻¹) x₁ u₁ = u₁ ∧
      (MulAut.conj g₀⁻¹) x₂ (u - u₁) = u - u₁) :
    ∀ u, ∃ u₁, x₁ u₁ = u₁ ∧ x₂ (u - u₁) = u - u₁ := by
  intro u
  obtain ⟨v₁, hv₁, hv₂⟩ := h (g₀.symm u)
  refine ⟨g₀ v₁, ?_, ?_⟩
  · rw [s16c1c_conj_apply (g₀ := g₀) (x := x₁) v₁, hv₁]
  · have h1 : u - g₀ v₁ = g₀ (g₀.symm u - v₁) := by
      rw [map_sub, LinearEquiv.apply_symm_apply]
    rw [h1, s16c1c_conj_apply (g₀ := g₀) (x := x₂) (g₀.symm u - v₁), hv₂]

theorem s16c1c_transPair {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {β : W ≃* Multiplicative V₀} (hβ : IsOmegaModel H β) : OmegaTransPair H := by
  intro E hEN hEab hcard hEH
  let κe : (V₀ ≃ₗ[ZMod 2] V₀) ≃* MulAut W :=
    MulEquiv.ofBijective (s16c1G_kappa β)
      ⟨s16c1G_kappa_injective β, s16c1G44_kappa_surjective β⟩
  let E' : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := E.comap κe.toMonoidHom
  have hmemE' : ∀ g, g ∈ E' ↔ s16c1G_kappa β g ∈ E := fun g => Iff.rfl
  have hcardE' : Nat.card E' = Nat.card E := by
    have h1 : E' = E.map κe.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm κe E
    rw [h1]
    exact Subgroup.card_map_of_injective κe.symm.injective
  have hE'O : E' ≤ O₀ true := fun g hg =>
    s16c1c_mem_O_of_mem_normalizer hβ (hEN ((hmemE' g).1 hg))
  have hE'ab : ∀ g ∈ E', ∀ k ∈ E', g * k = k * g := by
    intro g hg k hk
    apply s16c1G_kappa_injective β
    rw [map_mul, map_mul]
    exact hEab.1 _ ((hmemE' g).1 hg) _ ((hmemE' k).1 hk)
  have hE'2 : ∀ g ∈ E', g ^ 2 = 1 := by
    intro g hg
    apply s16c1G_kappa_injective β
    rw [map_pow, map_one]
    exact hEab.2 _ ((hmemE' g).1 hg)
  have hE'not : ¬ E' ≤ Ω₀ true := by
    intro hle
    apply hEH
    intro e he
    obtain ⟨g, hg⟩ := s16c1G44_kappa_surjective β e
    have hgE' : g ∈ E' := by rw [hmemE', hg]; exact he
    rw [← hg]
    exact (s16c1G_mem_H_iff hβ _).2 ⟨g, hle hgE', rfl⟩
  have hp : IsPGroup 2 E' := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE'2 x x.2⟩
  obtain ⟨g₀, hg₀O, hconj⟩ := s16c1c_exists_conj_mem_T hE'O hp
  set ψ : (V₀ ≃ₗ[ZMod 2] V₀) →* (V₀ ≃ₗ[ZMod 2] V₀) :=
    (MulAut.conj g₀⁻¹).toMonoidHom with hψdef
  have hψ : ∀ x, ψ x = g₀⁻¹ * x * g₀ := fun x => by simp [hψdef, MulAut.conj_apply]
  have hψinj : Function.Injective ψ := (MulAut.conj g₀⁻¹).injective
  let P : Subgroup (V₀ ≃ₗ[ZMod 2] V₀) := E'.map ψ
  have hcardP : Nat.card P = 16 := by
    have h1 : Nat.card P = Nat.card E' := Subgroup.card_map_of_injective hψinj
    rw [h1, hcardE', hcard]
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE'ab a ha b hb]
  have hP2 : ∀ x ∈ P, x ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE'2 a ha, map_one]
  have hPT : ∀ x ∈ P, x ∈ s16c1c_T := by
    rintro _ ⟨a, ha, rfl⟩
    rw [hψ]
    exact hconj a ha
  have hPnot : ¬ P ≤ Ω₀ true := by
    intro hle
    apply hE'not
    intro x hx
    have h1 : ψ x ∈ Ω₀ true := hle (Subgroup.mem_map_of_mem ψ hx)
    have h2 : g₀ * (ψ x) * g₀⁻¹ ∈ Ω₀ true := s16c1c_conj_mem_omega hg₀O h1
    have h3 : g₀ * (ψ x) * g₀⁻¹ = x := by rw [hψ]; group
    rw [h3] at h2
    exact h2
  obtain ⟨y₁, hy₁, y₂, hy₂, ⟨w₁, hw₁, h1₁, hex₁⟩, ⟨w₂, hw₂, h1₂, hex₂⟩, hspan⟩ :=
    s16c1c_exists_trans_pair hPab hP2 hPT hcardP hPnot
  obtain ⟨x₁, hx₁, rfl⟩ := hy₁
  obtain ⟨x₂, hx₂, rfl⟩ := hy₂
  obtain ⟨w₁', hw₁', h1₁', hex₁'⟩ := s16c1c_transfer_trans (g₀ := g₀) hw₁ h1₁ hex₁
  obtain ⟨w₂', hw₂', h1₂', hex₂'⟩ := s16c1c_transfer_trans (g₀ := g₀) hw₂ h1₂ hex₂
  have hspan' : ∀ u, ∃ u₁, x₁ u₁ = u₁ ∧ x₂ (u - u₁) = u - u₁ :=
    s16c1c_transfer_span (g₀ := g₀) hspan
  refine ⟨s16c1G_kappa β x₁, (hmemE' x₁).1 hx₁, s16c1G_kappa β x₂, (hmemE' x₂).1 hx₂,
    ?_, ?_, ?_⟩
  · exact s16c1c_card_commV_kappa β (hE'2 x₁ hx₁) hw₁' h1₁' hex₁'
  · exact s16c1c_card_commV_kappa β (hE'2 x₂ hx₂) hw₂' h1₂' hex₂'
  · exact s16c1c_fixV_sup_kappa β hspan'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
