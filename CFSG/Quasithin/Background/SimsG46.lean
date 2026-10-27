module

public import CFSG.Quasithin.Background.SimsG46Graph
public import CFSG.Quasithin.Background.SimsG46Imprim
public import CFSG.Quasithin.Background.SimsG46Case3
public import CFSG.Quasithin.Background.SimsG46SL2

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem imprimitive_of_pair (G₀ : Subgroup (V ≃ₗ[F] V)) (V₁ V₂ : Submodule F V)
    (hV₁ne : V₁ ≠ ⊥) (hV₂ne : V₂ ≠ ⊥) (hcompl : IsCompl V₁ V₂)
    (hperm : ∀ g ∈ G₀, (V₁.map (g : V →ₗ[F] V) = V₁ ∧ V₂.map (g : V →ₗ[F] V) = V₂) ∨
      (V₁.map (g : V →ₗ[F] V) = V₂ ∧ V₂.map (g : V →ₗ[F] V) = V₁)) :
    IsImprimitiveOnV G₀ := by
  refine ⟨2, ![V₁, V₂], by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hV₁ne
    · exact hV₂ne
  · rw [iSupIndep_pair (i := 0) (j := 1) (by decide) (fun k => by fin_cases k <;> simp)]
    exact hcompl.disjoint
  · apply le_antisymm le_top
    rw [← hcompl.sup_eq_top]
    exact sup_le (le_iSup_of_le 0 le_rfl) (le_iSup_of_le 1 le_rfl)
  · intro g hg i
    rcases hperm g hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · fin_cases i
      · exact ⟨0, h1⟩
      · exact ⟨1, h2⟩
    · fin_cases i
      · exact ⟨1, h1⟩
      · exact ⟨0, h2⟩

theorem imprimitive_of_case3 (n : ℕ) (B : LinearMap.BilinForm F V)
    (hdim : Module.finrank F V = 4) (G₀ : Subgroup (V ≃ₗ[F] V)) (h : G41Case3 n B G₀) :
    IsImprimitiveOnV G₀ := by
  obtain ⟨V₁, V₂, hV₁, -, hcompl, hperm, -⟩ := h
  have hV₁ne : V₁ ≠ ⊥ := by
    intro h0
    have := hV₁.1
    rw [h0, finrank_bot] at this
    exact absurd this (by norm_num)
  have hV₂ne : V₂ ≠ ⊥ := by
    intro h0
    have htop : V₁ = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [h0, sup_bot_eq] at this
    have := hV₁.1
    rw [htop, finrank_top, hdim] at this
    exact absurd this (by norm_num)
  exact imprimitive_of_pair G₀ V₁ V₂ hV₁ne hV₂ne hcompl hperm

theorem imprimitive_of_decW (B : LinearMap.BilinForm F V)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (V₁ V₂ : Submodule F V) (h1 : Module.finrank F V₁ = 2)
    (h2 : V₂ = LinearMap.BilinForm.orthogonal B V₁) (h3 : V₁ ⊓ V₂ = ⊥)
    (hperm : ∀ g ∈ G₀, (V₁.map (g : V →ₗ[F] V) = V₁ ∧ V₂.map (g : V →ₗ[F] V) = V₂) ∨
      (V₁.map (g : V →ₗ[F] V) = V₂ ∧ V₂.map (g : V →ₗ[F] V) = V₁)) :
    IsImprimitiveOnV G₀ := by
  have hfin : FiniteDimensional F V := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  have hge := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) V₁
  rw [← h2, h1, hdim] at hge
  have hsupdim := Submodule.finrank_sup_add_finrank_inf_eq V₁ V₂
  rw [h3, finrank_bot, h1] at hsupdim
  have hle : Module.finrank F ↥(V₁ ⊔ V₂) ≤ 4 := hdim ▸ Submodule.finrank_le _
  have hV₂ : Module.finrank F V₂ = 2 := by omega
  have hsup : V₁ ⊔ V₂ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hdim]
    omega
  have hne : ∀ W : Submodule F V, Module.finrank F W = 2 → W ≠ ⊥ := by
    intro W hW h0
    rw [h0, finrank_bot] at hW
    exact absurd hW (by norm_num)
  exact imprimitive_of_pair G₀ V₁ V₂ (hne V₁ h1) (hne V₂ hV₂)
    ⟨disjoint_iff.mpr h3, codisjoint_iff.mpr hsup⟩ hperm

theorem g46 (n : ℕ) (hn : Nat.card F = 2 ^ n) [Finite F] [CharP F 2]
    (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty)
    (hodd : ∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀,
      orderOf (a * b) = 2 ∨ Odd (orderOf (a * b))) :
    (¬ (advGraph G₀).Connected ↔
        ¬ ∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀, ∃ g ∈ transvGen G₀, g * a * g⁻¹ = b) ∧
      (¬ (advGraph G₀).Connected ↔ IsImprimitiveOnV G₀) ∧
      (¬ (advGraph G₀).Connected ↔ G41Case3 n B G₀) := by
  have hgraph := connected_iff_transitive (transvSet G₀) hD
    (fun d hd => transv_mul_self d hd.2)
    (fun g hg d hd => conj_mem_transvSet (transvGen_le G₀ hg) hd) hodd
  have h14 : ¬ (advGraph G₀).Connected → G41Case3 n B G₀ :=
    case3_of_not_connected n hn B halt hnd hdim G₀ hSp hirr hD
      (fun T hT hnc => sl2_invol_subgroup n hn T hT hnc)
  have h43 : G41Case3 n B G₀ → IsImprimitiveOnV G₀ := imprimitive_of_case3 n B hdim G₀
  have h31 : IsImprimitiveOnV G₀ → ¬ (advGraph G₀).Connected :=
    not_connected_of_imprimitive B halt hnd hdim G₀ hSp hirr hD
  exact ⟨not_congr hgraph, ⟨fun h => h43 (h14 h), h31⟩, ⟨h14, fun h => h31 (h43 h)⟩⟩

end CFSG.Quasithin.SimsG4
