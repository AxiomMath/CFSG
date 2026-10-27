module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSLCent
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix

namespace LinFusion

variable {m : ℕ} {F : Type} [Field F]

theorem conjSL_toGL (s u : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (SpecialLinearGroup.toGL s) u = s * u * s⁻¹ := by
  apply Subtype.ext
  rw [InnerDiagA.coe_conjSL]
  rfl

theorem conjSL_toGL_mul (s : SpecialLinearGroup (Fin (m + 1)) F) (A : GL (Fin (m + 1)) F)
    (u : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL (SpecialLinearGroup.toGL s * A) u = s * InnerDiagA.conjSL A u * s⁻¹ := by
  rw [conjSL_mul, conjSL_toGL]

theorem conjSL_conj (A : GL (Fin (m + 1)) F) (h u : SpecialLinearGroup (Fin (m + 1)) F) :
    InnerDiagA.conjSL A (h * u * h⁻¹) =
      h * InnerDiagA.conjSL ((SpecialLinearGroup.toGL h)⁻¹ * A * SpecialLinearGroup.toGL h) u *
        h⁻¹ := by
  rw [← conjSL_toGL_mul, ← conjSL_toGL, ← conjSL_mul]
  congr 2
  group

variable {G : Type*} [Group G]

theorem exists_mem_ggInducedPairs (hm : 2 ≤ m) (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {y : G}
    (hy : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ y⁻¹) :
    ∃ A : GL (Fin (m + 1)) F, (y, A) ∈ ggInducedPairs ψ := by
  obtain ⟨g, hg, χ, hχ⟩ := InnerDiagA.exists_chi_of_ggPsiInnerDiag ψ hy
  obtain ⟨D, hD⟩ := InnerDiagA.exists_conj_eq_conjSL hm ψ hker hχ
  obtain ⟨s, rfl⟩ := hg
  refine ⟨SpecialLinearGroup.toGL s * D, fun u => ?_⟩
  rw [conjSL_toGL_mul, map_mul, map_mul, map_inv, ← hD u]
  group

theorem mem_ggInducedPairs_comp_conj {ψ : SpecialLinearGroup (Fin (m + 1)) F →* G} {y : G}
    {A : GL (Fin (m + 1)) F} (hyA : (y, A) ∈ ggInducedPairs ψ)
    (h : SpecialLinearGroup (Fin (m + 1)) F) :
    (y, (SpecialLinearGroup.toGL h)⁻¹ * A * SpecialLinearGroup.toGL h) ∈
      ggInducedPairs (ψ.comp (MulAut.conj h).toMonoidHom) := by
  intro u
  have h1 := mem_ggInducedPairs.mp hyA (h * u * h⁻¹)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1 ⊢
  rw [h1, conjSL_conj]

theorem exists_zpowers_sup_ggOTwoPrime_of_rootInvolution [Finite F] [CharP F 2] (hm : 2 ≤ m)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {t : StatedLieTag} {r : G}
    (hr : GGRootInvolution (SpecialLinear.rootDatum m F) t ψ r) (Y : Subgroup G)
    (hYr : Y ≤ Subgroup.centralizer {r})
    (hYd : ∀ y ∈ Y, GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ y) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {r}) := by
  obtain ⟨hr2, γ, -, u₀, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨i, j, hij, c, hc, rfl⟩ := exists_transvection_of_mem_rootGroup hx hx1
  obtain ⟨g, hg⟩ := exists_conj_transvection_eq (by omega : 1 ≤ m) hij hc
  set h := u₀ * g⁻¹ with hh
  set ψ' := ψ.comp (MulAut.conj h).toMonoidHom with hψ'
  have hr' : ψ' (ggInvSL (m + 1) 1 F) =
      ψ ((MulAut.conj u₀).toMonoidHom (SpecialLinearGroup.transvection hij c)) := by
    simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hg, hh]
    congr 1
    group
  have hrange : ψ'.range = ψ.range := by
    rw [hψ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  have hker' : ψ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := by
    intro v hv
    have hz : h * v * h⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F) := hker hv
    have h1 := (inferInstance : (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)).Normal).conj_mem
      _ hz h⁻¹
    rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
  have hC' : Subgroup.centralizer (ψ'.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hYr' : Y ≤ Subgroup.centralizer {ψ' (ggInvSL (m + 1) 1 F)} := by rw [hr']; exact hYr
  have hY' : ∀ y ∈ Y, ∃ A : GL (Fin (m + 1)) F, (y, A) ∈ ggInducedPairs ψ' := by
    intro y hy
    obtain ⟨A, hA⟩ := exists_mem_ggInducedPairs hm ψ hker (hYd y⁻¹ (Y.inv_mem hy))
    exact ⟨_, mem_ggInducedPairs_comp_conj hA h⟩
  obtain ⟨y₀, hy₀, hle⟩ :=
    exists_zpowers_sup_ggOTwoPrime_sl (by omega : 1 ≤ m) ψ' hker' hC' Y hYr' hY'
  rw [hrange, hr'] at hle
  exact ⟨y₀, hy₀, hle⟩

end LinFusion

section Tags

@[expose] def GGRootCentralizerCyclicTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K → Subgroup.centralizer (ψ.range : Set G) = ⊥ →
    ∀ r : G, GGRootInvolution (ggU t n f).D t ψ r →
    ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (ψ.range : Set G) ⊓ Subgroup.centralizer {r} →
      (∀ y ∈ Y, GGPsiInnerDiag (ggU t n f).D ψ y) →
        ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {r})

theorem ggRootCentralizerCyclicInput_of_tags (h : ∀ t, GGRootCentralizerCyclicTag t) :
    GGRootCentralizerCyclicInput := by
  intro G _ _ t n f ψ hadm hrk hker hC r hr Y hY hYd
  exact h t G n f ψ hadm hrk hker hC r hr Y hY hYd

theorem ggRootCentralizerCyclicTag_PSL : GGRootCentralizerCyclicTag .PSL := by
  intro G _ _ n f ψ hadm hrk hker hC r hr Y hY hYd
  obtain ⟨-, -, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact LinFusion.exists_zpowers_sup_ggOTwoPrime_of_rootInvolution (F := GaloisField 2 f) hrk ψ
    hker hC hr Y (fun y hy => (hY hy).2) hYd

theorem ggRootCentralizerCyclicTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootCentralizerCyclicTag t := by
  intro G _ _ n f ψ _ hrk
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggRootCentralizerCyclicTag_POmegaOdd : GGRootCentralizerCyclicTag .POmegaOdd :=
  fun _ _ _ _ _ _ hadm => absurd rfl hadm.2.2.2

theorem ggRootCentralizerCyclicInput_of_remaining (hPSU : GGRootCentralizerCyclicTag .PSU)
    (hPSp : GGRootCentralizerCyclicTag .PSp) (hPlus : GGRootCentralizerCyclicTag .POmegaPlus)
    (hMinus : GGRootCentralizerCyclicTag .POmegaMinus) (hF4 : GGRootCentralizerCyclicTag .F4)
    (hE6 : GGRootCentralizerCyclicTag .E6) (hE7 : GGRootCentralizerCyclicTag .E7)
    (hE8 : GGRootCentralizerCyclicTag .E8) (hTwE6 : GGRootCentralizerCyclicTag .twistedE6) :
    GGRootCentralizerCyclicInput := by
  refine ggRootCentralizerCyclicInput_of_tags fun t => ?_
  cases t with
  | PSL => exact ggRootCentralizerCyclicTag_PSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggRootCentralizerCyclicTag_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | G2 => exact ggRootCentralizerCyclicTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggRootCentralizerCyclicTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 =>
    exact ggRootCentralizerCyclicTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggRootCentralizerCyclicTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggRootCentralizerCyclicTag_of_placeholder _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggRootCentralizerCyclicTag_of_placeholder _
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end Tags

end CFSG.StandardType
