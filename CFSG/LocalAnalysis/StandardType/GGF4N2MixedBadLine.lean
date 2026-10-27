module

public import CFSG.LocalAnalysis.StandardType.GGF4N2MixedPower
public import CFSG.LocalAnalysis.StandardType.GGF4N2NbrClassification
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.StandardType.N2PlaneGroup

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

section Conj


theorem ggCentralImage_map_conj {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ} {X : Subgroup G}
    (h : GGCentralImage t n f X) (c : G) :
    GGCentralImage t n f (X.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨ψ, hadm, hker, hrange⟩ := h
  refine ⟨(MulAut.conj c).toMonoidHom.comp ψ, hadm, fun z hz => hker ?_, ?_⟩
  · exact (MulEquiv.map_eq_one_iff (MulAut.conj c)).mp hz
  · rw [MonoidHom.range_comp, hrange]

end Conj

section BadLines



theorem ggF4N2_mixed_no_bad_neighbour (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x) :
    ∀ (y' : G) (K' : Subgroup G), GGNbr 5 B x D J y' K' →
      Subgroup.zpowers y' ≠ Subgroup.zpowers (y * (g * y * g⁻¹) ^ 2) ∧
        Subgroup.zpowers y' ≠ Subgroup.zpowers (y * (g * y * g⁻¹) ^ 3) := by
  classical
  obtain ⟨eJ, hnores⟩ := ggF4N2_mixed_no_residual hR hNbr hL hK hF4 hgL hgN hginv hgx
  have htype := ggF4N2_mixed_type_obstruction hR hNbr hL hK hF4 hgL hgN hginv hgx
  have hfac := ggF4N2_nbrReflectionAt_all hLB hR hNbr hL hK eJ
  obtain ⟨v, ⟨hvD, -⟩, hvo, hDyv, hgy, -⟩ :=
    ggF4N2_swap_exchanges_axes hR hNbr hL hK hF4 hgL hgN hginv hgx
  obtain ⟨-, -, hyo, hDcl, hDcard, hDE⟩ := ggF4N2_x_data hR hNbr
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have huo : orderOf (g * y * g⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
  have huv : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, hvo])
  have hDyu : D = Subgroup.zpowers y ⊔ Subgroup.zpowers (g * y * g⁻¹) := by rw [hDyv, huv]
  have huD : g * y * g⁻¹ ∈ D := (Subgroup.zpowers_le.mpr hvD) hgy
  have hyu : Commute y (g * y * g⁻¹) :=
    congrArg Subtype.val (hDE.1.is_comm.comm (⟨y, hyD⟩ : ↥D) ⟨_, huD⟩)
  have hyu' : y ∉ Subgroup.zpowers (g * y * g⁻¹) := by
    intro h
    have hle : D ≤ Subgroup.zpowers (g * y * g⁻¹) := by
      rw [hDyu]
      exact sup_le (Subgroup.zpowers_le.mpr h) le_rfl
    have := Subgroup.card_le_of_le hle
    rw [hDcard, Nat.card_zpowers, huo] at this
    norm_num at this
  have key : ∀ (y' : G) (K' : Subgroup G), GGNbr 5 B x D J y' K' → ∀ k : ℕ, (k = 2 ∨ k = 3) →
      Subgroup.zpowers y' ≠ Subgroup.zpowers (y * (g * y * g⁻¹) ^ k) := by
    intro y' K' h' k hk hline
    obtain ⟨t', -, -, ht'J, ht'y, ⟨ht'D, ht'o⟩, C, δ, hδ, ht'e⟩ := hfac y' K' h'
    have hfix : t' * (y * (g * y * g⁻¹) ^ k) * t'⁻¹ = y * (g * y * g⁻¹) ^ k := by
      have hmem : y * (g * y * g⁻¹) ^ k ∈ Subgroup.zpowers y' := hline ▸ Subgroup.mem_zpowers _
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hi, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, ht'y]
    set φ := D.normalizerMonoidHom ⟨t', ht'D⟩ with hφ_def
    have hφ : ∀ d : D, ((φ d : D) : G) = t' * d * t'⁻¹ := fun d => rfl
    have hγ : ∀ d ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (g * y * g⁻¹),
        t' * d * t'⁻¹ ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (g * y * g⁻¹) := by
      rw [← hDyu]
      intro d hd
      exact (Subgroup.mem_normalizer_iff.mp ht'D d).mp hd
    have hγ2 : ∀ d ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (g * y * g⁻¹),
        t' ^ 2 * d * (t' ^ 2)⁻¹ = d := by
      rw [← hDyu]
      intro d hd
      have h := congrArg (fun f : MulAut D => ((f ⟨d, hd⟩ : D) : G)) (pow_orderOf_eq_one φ)
      simp only [ht'o, pow_two, MulAut.mul_apply, MulAut.one_apply] at h
      rw [hφ, hφ] at h
      rw [pow_two]
      calc t' * t' * d * (t' * t')⁻¹ = t' * (t' * d * t'⁻¹) * t'⁻¹ := by group
        _ = d := h
    have hγ1 : ∃ d ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers (g * y * g⁻¹), t' * d * t'⁻¹ ≠ d := by
      by_contra hcon
      push Not at hcon
      have hφ1 : φ = 1 := MulEquiv.ext fun d => Subtype.ext (by
        rw [hφ, MulAut.one_apply]
        exact hcon d (hDyu ▸ d.2))
      rw [hφ1, orderOf_one] at ht'o
      norm_num at ht'o
    have hbadfix : t' * (y * (g * y * g⁻¹) ^ 2) * t'⁻¹ = y * (g * y * g⁻¹) ^ 2 ∨
        t' * (y * (g * y * g⁻¹) ^ 3) * t'⁻¹ = y * (g * y * g⁻¹) ^ 3 := by
      rcases hk with rfl | rfl
      · exact Or.inl hfix
      · exact Or.inr hfix
    rcases N2Plane.plane_bad_reflection_dichotomy hyo huo hyu hyu' hγ hγ2 hγ1 hbadfix with
      ⟨e, he, f, hf, hef⟩ | hres
    · exact htype t' ht'J e he f hf hef
    · exact hnores t' ht'J ⟨C, δ, hδ, ht'e⟩ hres
  intro y' K' h'
  exact ⟨key y' K' h' 2 (Or.inl rfl), key y' K' h' 3 (Or.inr rfl)⟩

theorem ggF4N2_mixed_ggG0_eq (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hginv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hgx : g * x * g⁻¹ = x) :
    ggG0 5 B x L D J = L ⊔ K :=
  ggF4N2_mixed_ggG0_eq_sup hR hNbr hL hK hF4 hgL hgN hginv hgx
    (ggF4N2_mixed_no_bad_neighbour hLB hR hNbr hL hK hF4 hgL hgN hginv hgx)

open CFSG.ClassicalInvolution.WeakCT in
theorem ggF4N2_mixed_E6_reduction (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    ∃ ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G, ∃ g ∈ L,
      ψ₁.ker ≤ Subgroup.center _ ∧ ψ₁.range = K ∧
      (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J ∧
      g ∈ Subgroup.normalizer (Bs : Set G) ∧ (∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) ∧ g * x * g⁻¹ = x ∧
      ψ₂.ker ≤ Subgroup.center _ ∧ ψ₂.range = K.map (MulAut.conj g).toMonoidHom ∧
      ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
        ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) ∧
      (∃ rho : Bs →* Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2),
        rho.range = N2KCoordinate.coordinateTorus ∧ rho.ker = (Subgroup.zpowers y).subgroupOf Bs ∧
        (∀ hx : x ∈ Bs, rho ⟨x, hx⟩ ∈ N2KCoordinate.coordT45) ∧ (∀ b : Bs, rho b ^ 5 = 1) ∧
        (∀ (b : Bs) (k : G), k ∈ K → ψ₁ (rho b) * k * (ψ₁ (rho b))⁻¹ = b * k * b⁻¹) ∧
        Nat.card rho.range = 5 ^ 3 ∧ (ψ₁.comp rho).range = Bs ⊓ K) ∧
      ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ ≤ ggG0 5 B x L D J ∧
      ggG0 5 B x L D J = L ⊔ K ∧
      ((∀ a ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁,
          ∀ b ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂, a * b = b * a) →
        ∀ c ∈ ggG0 5 B x L D J,
          L ≤ (ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
            (MulAut.conj c).toMonoidHom →
          K ≤ (ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂).map
            (MulAut.conj c).toMonoidHom →
          GGCentralImage .E6 0 2 (ggG0 5 B x L D J)) := by
  obtain ⟨ψ₁, h₁, hK₁, hJ₁, hrho⟩ := ggF4N2K_chart_blockSL_torus hR hNbr hL hK
  obtain ⟨-, -, -, -, -, g, hgL, hgN, hinv, hxg, -, -, -⟩ := ggF4N2L_exists_swap hR hL
  obtain ⟨ψ₂, h₂, hK₂, hblock⟩ := ggF4N2_secondChart_of_chart hR hL h₁ hK₁ hJ₁ hgL hinv hxg
  obtain ⟨hle, -⟩ := ggF4N2_mixed_E6_of_charts hNbr hgL h₁ hK₁ h₂ hK₂ hblock
  have hG0 : ggG0 5 B x L D J = L ⊔ K :=
    ggF4N2_mixed_ggG0_eq hLB hR hNbr hL hK hF4 hgL hgN hinv hxg
  refine ⟨ψ₁, ψ₂, g, hgL, h₁, hK₁, hJ₁, hgN, hinv, hxg, h₂, hK₂, hblock, hrho, hle, hG0,
    fun hM c hc hLX hKX => ?_⟩
  have hX₀ := ggCentralImage_E6_of_twoSL6Charts (le_refl 2) ψ₁ ψ₂ h₁ h₂ hblock.symm hM
  set X₀ := ψ₁.range ⊔ (blockSL2 (GaloisField 2 2) 5 3).range.map ψ₂ with hX₀_def
  have hXG : X₀.map (MulAut.conj c).toMonoidHom ≤ ggG0 5 B x L D J := by
    rintro _ ⟨z, hz, rfl⟩
    exact (ggG0 5 B x L D J).mul_mem ((ggG0 5 B x L D J).mul_mem hc (hle hz))
      ((ggG0 5 B x L D J).inv_mem hc)
  have hGX : ggG0 5 B x L D J ≤ X₀.map (MulAut.conj c).toMonoidHom := by
    rw [hG0]
    exact sup_le hLX hKX
  rw [← le_antisymm hXG hGX]
  exact ggCentralImage_map_conj hX₀ c

end BadLines

end CFSG.StandardType

end
