module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaForkCox
public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveDkForkLeaves
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupFork
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitWeylEquiv
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDkRoots
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

private theorem ggDk_fork_leaves_image {ι : Type} {M : CoxeterMatrix ι} {k : ℕ} (hk : 4 ≤ k)
    {σ : Fin k ≃ ι} {t₀ t₁ t₂ t₃ : M.Group}
    (h₀ : ∃ (w : M.Group) (i : ι), t₀ = w * M.simple i * w⁻¹)
    (h₁ : ∃ (w : M.Group) (i : ι), t₁ = w * M.simple i * w⁻¹)
    (h₂ : ∃ (w : M.Group) (i : ι), t₂ = w * M.simple i * w⁻¹)
    (h₃ : ∃ (w : M.Group) (i : ι), t₃ = w * M.simple i * w⁻¹)
    (h12 : t₁ * t₂ = t₂ * t₁) (h13 : t₁ * t₃ = t₃ * t₁) (h23 : t₂ * t₃ = t₃ * t₂)
    (hn12 : t₁ ≠ t₂) (hn13 : t₁ ≠ t₃) (hn23 : t₂ ≠ t₃)
    (hn01 : t₀ * t₁ ≠ t₁ * t₀) (hn02 : t₀ * t₂ ≠ t₂ * t₀) (hn03 : t₀ * t₃ ≠ t₃ * t₀)
    (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) :
    (GGDSameSupp k (φ t₁) (φ t₂) ∨ GGDSameSupp k (φ t₁) (φ t₃) ∨
        GGDSameSupp k (φ t₂) (φ t₃)) ∧
      (GGDDisjSupp k (φ t₁) (φ t₂) ∨ GGDDisjSupp k (φ t₁) (φ t₃) ∨
        GGDDisjSupp k (φ t₂) (φ t₃)) := by
  have hroot : ∀ t : M.Group, (∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹) →
      ∃ γ, GGDReflRoot k (φ t) γ := by
    rintro t ⟨w, i, rfl⟩
    exact exists_ggDReflRoot_of_conj φ hφ w i
  have hmul : ∀ {a b : M.Group}, a * b = b * a → φ a * φ b = φ b * φ a := by
    intro a b h
    rw [← map_mul, ← map_mul, h]
  have hne : ∀ {a b : M.Group}, a ≠ b → φ a ≠ φ b := fun h hh => h (φ.injective hh)
  have hncomm : ∀ {a b : M.Group}, a * b ≠ b * a → φ a * φ b ≠ φ b * φ a := by
    intro a b h hh
    apply h
    apply φ.injective
    rw [map_mul, map_mul]
    exact hh
  exact ggDk_fork_leaves hk (hroot t₀ h₀) (hroot t₁ h₁) (hroot t₂ h₂) (hroot t₃ h₃)
    (hmul h12) (hmul h13) (hmul h23) (hne hn12) (hne hn13) (hne hn23)
    (hncomm hn01) (hncomm hn02) (hncomm hn03)

theorem ggL_noReflFork_typeD {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hD : GGIsWeylMatrixD M)
    {i j : ι} (hij : i ≠ j) (hMij : M.M i j = 2) (hno : ¬ GGOrbPair L Bs 𝒦 M e i j) :
    GGNoReflFork p Bs L := by
  classical
  rintro ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, hr₀, hr₁, hr₂, hr₃,
    h01, h02, h03, h12, h13, h23⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 :=
    GGIsWeylMatrixAD.le_three (Or.inr hD)
  obtain ⟨t₀, t₁, t₂, t₃, h₀, h₁, h₂, h₃, he₀, he₁, he₂, he₃,
    hcom12, hcom13, hcom23, hn12, hn13, hn23, hn01, hn02, hn03⟩ :=
    ggX_fork_coxeter hcfg hpres hle3 (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl))
      hc₀ hc₁ hc₂ hc₃ hr₀ hr₁ hr₂ hr₃ h01 h02 h03 h12 h13 h23
  obtain ⟨k, σ, hk, hM⟩ := hD
  have hleaves : ∀ {σ : Fin k ≃ ι} (φ : M.Group ≃* ggWeylD k),
      (∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) →
      (GGDSameSupp k (φ t₁) (φ t₂) ∨ GGDSameSupp k (φ t₁) (φ t₃) ∨
          GGDSameSupp k (φ t₂) (φ t₃)) ∧
        (GGDDisjSupp k (φ t₁) (φ t₂) ∨ GGDDisjSupp k (φ t₁) (φ t₃) ∨
          GGDDisjSupp k (φ t₂) (φ t₃)) := by
    intro σ φ hφ
    exact ggDk_fork_leaves_image hk h₀ h₁ h₂ h₃ hcom12 hcom13 hcom23 hn12 hn13 hn23
      hn01 hn02 hn03 φ hφ
  have hdisj : 5 ≤ k → ∀ φ : M.Group ≃* ggWeylD k,
      (∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a) →
      ∃ t t' : M.Group, GGDDisjSupp k (φ t) (φ t') ∧
        ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs ∧
        ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs := by
    intro _ φ hφ
    rcases (hleaves φ hφ).2 with h | h | h
    · exact ⟨t₁, t₂, h, by rw [he₁]; exact hc₁, by rw [he₂]; exact hc₂⟩
    · exact ⟨t₁, t₃, h, by rw [he₁]; exact hc₁, by rw [he₃]; exact hc₃⟩
    · exact ⟨t₂, t₃, h, by rw [he₂]; exact hc₂, by rw [he₃]; exact hc₃⟩
  obtain ⟨σ', hM', hσi, hσj⟩ :=
    ggDk_fork_of_disjPair hk hM hij hMij hno hdisj
  have hno' : ¬ GGOrbPair L Bs 𝒦 M e (σ' ⟨k - 2, by omega⟩) (σ' ⟨k - 1, by omega⟩) := by
    rw [hσi, hσj]
    exact hno
  obtain ⟨φ', hφ'⟩ := ggDk_weylEquiv hM'
  have hNoSame : GGDNoSameSupp e φ' :=
    ggDNoSameSupp_of_not_orbPair hk φ' hφ' hno'
  have key : ∀ (t t' : M.Group),
      ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs →
      ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer L Bs →
      GGDSameSupp k (φ' t) (φ' t') → False := by
    intro t t' ht ht' hsame
    obtain ⟨a, b, s, hab, hs, hr, hr'⟩ := hsame
    rcases hs with rfl | rfl
    · exact hNoSame L (Or.inl rfl) a b hab
        ⟨⟨t, by simpa using hr, ht⟩, ⟨t', by simpa using hr', ht'⟩⟩
    · refine hNoSame L (Or.inl rfl) a b hab ⟨?_, ?_⟩
      · exact ⟨t', by simpa [Pi.single_neg, sub_neg_eq_add] using hr', ht'⟩
      · exact ⟨t, by simpa [Pi.single_neg, sub_eq_add_neg] using hr, ht⟩
  rcases (hleaves φ' hφ').1 with h | h | h
  · exact key t₁ t₂ (by rw [he₁]; exact hc₁) (by rw [he₂]; exact hc₂) h
  · exact key t₁ t₃ (by rw [he₁]; exact hc₁) (by rw [he₃]; exact hc₃) h
  · exact key t₂ t₃ (by rw [he₂]; exact hc₂) (by rw [he₃]; exact hc₃) h

end CFSG.StandardType

end
