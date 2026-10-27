module

public import CFSG.Quasithin.Background.F1Borel
public import CFSG.Quasithin.Background.F7Geometry

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

namespace F112W

section Kernels

variable {G : Type u} [Group G]

@[expose] def kerα (G₁ G₂ : Subgroup G) : Subgroup G := coreIn (G₁ ⊓ G₂) G₁

@[expose] def kerβ (G₁ G₂ : Subgroup G) : Subgroup G := coreIn (G₁ ⊓ G₂) G₂

variable {G₀ G₁ G₂ T : Subgroup G}

theorem kerα_eq_ballStab (hG : G₀ = G₁ ⊔ G₂) :
    CosetGeom.ballStab 1 (CosetGeom.γ₀ G₀ G₁ G₂) = kerα G₁ G₂ := (CosetGeom.ballStab_one_γ₀ hG).1

theorem kerβ_eq_ballStab (hG : G₀ = G₁ ⊔ G₂) :
    CosetGeom.ballStab 1 (CosetGeom.γ₁ G₀ G₁ G₂) = kerβ G₁ G₂ := (CosetGeom.ballStab_one_γ₁ hG).1

theorem kerα_le_inf : kerα G₁ G₂ ≤ G₁ ⊓ G₂ := coreIn_le_right _ _

theorem kerβ_le_inf : kerβ G₁ G₂ ≤ G₁ ⊓ G₂ := coreIn_le_right _ _

theorem kerα_le_left : kerα G₁ G₂ ≤ G₁ := kerα_le_inf.trans inf_le_left

theorem kerβ_le_right : kerβ G₁ G₂ ≤ G₂ := kerβ_le_inf.trans inf_le_right

theorem le_normalizer_kerα : G₁ ≤ Subgroup.normalizer (kerα G₁ G₂ : Set G) :=
  le_normalizer_coreIn _ _

theorem le_normalizer_kerβ : G₂ ≤ Subgroup.normalizer (kerβ G₁ G₂ : Set G) :=
  le_normalizer_coreIn _ _

section Fin

variable [Finite G]

theorem pCoreOf_le_kerα (hyp : AmalgamHyp G₀ G₁ G₂ T) : pCoreOf 2 G₁ ≤ kerα G₁ G₂ :=
  le_coreIn (pCoreOf_le 2 G₁) (le_normalizer_pCoreOf 2 G₁)
    (le_inf (pCoreOf_le 2 G₁)
      ((isSylowTwoOf_pCoreOf_le hyp.sylow₁).trans (hyp.T_le.trans inf_le_right)))

theorem pCoreOf_le_kerβ (hyp : AmalgamHyp G₀ G₁ G₂ T) : pCoreOf 2 G₂ ≤ kerβ G₁ G₂ :=
  le_coreIn (pCoreOf_le 2 G₂) (le_normalizer_pCoreOf 2 G₂)
    (le_inf ((isSylowTwoOf_pCoreOf_le hyp.sylow₂).trans (hyp.T_le.trans inf_le_left))
      (pCoreOf_le 2 G₂))

theorem pCoreOf_kerα (hyp : AmalgamHyp G₀ G₁ G₂ T) : pCoreOf 2 (kerα G₁ G₂) = pCoreOf 2 G₁ := by
  apply le_antisymm
  · exact pCoreOf_mono_of_le_normalizer kerα_le_left le_normalizer_kerα
  · exact le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_kerα hyp)
      (kerα_le_left.trans (le_normalizer_pCoreOf 2 G₁)) (pCoreOf_isPGroup 2 G₁)

theorem pCoreOf_kerβ (hyp : AmalgamHyp G₀ G₁ G₂ T) : pCoreOf 2 (kerβ G₁ G₂) = pCoreOf 2 G₂ := by
  apply le_antisymm
  · exact pCoreOf_mono_of_le_normalizer kerβ_le_right le_normalizer_kerβ
  · exact le_pCoreOf_of_le_normalizer 2 (pCoreOf_le_kerβ hyp)
      (kerβ_le_right.trans (le_normalizer_pCoreOf 2 G₂)) (pCoreOf_isPGroup 2 G₂)

theorem kerα_eq_of_isPGroup (hyp : AmalgamHyp G₀ G₁ G₂ T) (h2 : IsPGroup 2 ↥(kerα G₁ G₂)) :
    kerα G₁ G₂ = pCoreOf 2 G₁ := by
  rw [← pCoreOf_kerα hyp]
  exact le_antisymm (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer h2)
    (pCoreOf_le 2 _)

theorem kerβ_eq_of_isPGroup (hyp : AmalgamHyp G₀ G₁ G₂ T) (h2 : IsPGroup 2 ↥(kerβ G₁ G₂)) :
    kerβ G₁ G₂ = pCoreOf 2 G₂ := by
  rw [← pCoreOf_kerβ hyp]
  exact le_antisymm (le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer h2)
    (pCoreOf_le 2 _)

theorem kerα_eq_of_isPGroup_inf (hyp : AmalgamHyp G₀ G₁ G₂ T) (hB : IsPGroup 2 ↥(G₁ ⊓ G₂)) :
    kerα G₁ G₂ = pCoreOf 2 G₁ :=
  kerα_eq_of_isPGroup hyp (hB.to_le kerα_le_inf)

theorem kerβ_eq_of_isPGroup_inf (hyp : AmalgamHyp G₀ G₁ G₂ T) (hB : IsPGroup 2 ↥(G₁ ⊓ G₂)) :
    kerβ G₁ G₂ = pCoreOf 2 G₂ :=
  kerβ_eq_of_isPGroup hyp (hB.to_le kerβ_le_inf)

end Fin

end Kernels

section Hyp111

variable {G : Type u} [Group G] [Finite G] {L1 L2 S : Subgroup G}

theorem inf_alpha_beta (h : Hyp111R L1 L2 S) :
    (L2 ⊔ bigB L1 L2 S) ⊓ (L1 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
  rw [inf_comm]
  exact F1.parabolic_inf_parabolic h

theorem bigB_lt_parabolic (h : Hyp111R L1 L2 S) : bigB L1 L2 S < L1 ⊔ bigB L1 L2 S := by
  refine lt_of_le_of_ne le_sup_right fun heq => ?_
  have hL1 : L1 ≤ bigB L1 L2 S := le_sup_left.trans heq.symm.le
  have h1 : L1 ≤ borelOf L1 S := by
    rw [← F1.inf_bigB_eq_borelOf h]
    exact le_inf le_rfl hL1
  exact (F1.lt_borelOf h).not_ge h1

theorem bigB_lt_parabolic' (h : Hyp111R L1 L2 S) : bigB L1 L2 S < L2 ⊔ bigB L1 L2 S := by
  have := bigB_lt_parabolic h.symm
  rwa [bigB_comm] at this

end Hyp111

section Lemma48

variable {G : Type u} [Group G] {G₀ G₁ G₂ : Subgroup G}

private def Good (U : Subgroup G) (δ : CosetGeom G₀ G₁ G₂) : Prop :=
  U ≤ CosetGeom.stab δ ∧ ∀ ε ∈ CosetGeom.nbrs δ, ∀ ε' ∈ CosetGeom.nbrs δ, ∃ x : ↥G₀,
    (x : G) ∈ Subgroup.normalizer (U : Set G) ∧ x • δ = δ ∧ x • ε = ε'

private theorem Good.propagate {U : Subgroup G} {δ ε₀ : CosetGeom G₀ G₁ G₂} (hδ : Good U δ)
    (hε₀ : Good U ε₀) (hn : ε₀ ∈ CosetGeom.nbrs δ) {ε : CosetGeom G₀ G₁ G₂}
    (hε : ε ∈ CosetGeom.nbrs δ) : Good U ε := by
  obtain ⟨-, hTδ⟩ := hδ
  obtain ⟨hUε₀, hTε₀⟩ := hε₀
  obtain ⟨x, hxN, -, hxε⟩ := hTδ ε₀ hn ε hε
  refine ⟨?_, ?_⟩
  · intro u hu
    rw [← hxε, CosetGeom.stab_smul, mem_conjSub]
    apply hUε₀
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) u).mp hu
    simpa using this
  · intro ζ hζ ζ' hζ'
    have h1 : x⁻¹ • ζ ∈ CosetGeom.nbrs ε₀ := by
      have := (CosetGeom.smul_adj x⁻¹).mpr hζ
      rw [← hxε, inv_smul_smul] at this
      exact this
    have h1' : x⁻¹ • ζ' ∈ CosetGeom.nbrs ε₀ := by
      have := (CosetGeom.smul_adj x⁻¹).mpr hζ'
      rw [← hxε, inv_smul_smul] at this
      exact this
    obtain ⟨y, hyN, hyε₀, hyζ⟩ := hTε₀ _ h1 _ h1'
    refine ⟨x * y * x⁻¹, ?_, ?_, ?_⟩
    · have : ((x * y * x⁻¹ : ↥G₀) : G) = (x : G) * (y : G) * (x : G)⁻¹ := rfl
      rw [this]
      exact (Subgroup.normalizer (U : Set G)).mul_mem
        ((Subgroup.normalizer (U : Set G)).mul_mem hxN hyN) (Subgroup.inv_mem _ hxN)
    · rw [← hxε]
      simp [mul_smul, hyε₀]
    · rw [mul_smul, mul_smul, hyζ, smul_inv_smul]

private theorem exists_nbr_rep₁ (hG : G₀ = G₁ ⊔ G₂) {U : Subgroup G}
    (hN₁ : ∀ g ∈ G₁, ∃ n ∈ G₁ ⊓ Subgroup.normalizer (U : Set G), n⁻¹ * g ∈ G₂)
    {ε : CosetGeom G₀ G₁ G₂} (hε : ε ∈ CosetGeom.nbrs (CosetGeom.γ₀ G₀ G₁ G₂)) :
    ∃ n : ↥G₀, (n : G) ∈ G₁ ∧ (n : G) ∈ Subgroup.normalizer (U : Set G) ∧
      n • CosetGeom.γ₁ G₀ G₁ G₂ = ε := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  obtain ⟨g, hg, hgε⟩ := CosetGeom.stab_transitive_on_nbrs
    (show CosetGeom.γ₁ G₀ G₁ G₂ ∈ CosetGeom.nbrs (CosetGeom.γ₀ G₀ G₁ G₂) from
      CosetGeom.adj_γ₀_γ₁) hε
  rw [CosetGeom.stab_γ₀ h₁] at hg
  obtain ⟨n, ⟨hnG₁, hnN⟩, hng⟩ := hN₁ g hg
  refine ⟨⟨n, h₁ hnG₁⟩, hnG₁, hnN, ?_⟩
  rw [← hgε]
  have hmem : (⟨n⁻¹ * g, G₀.mul_mem (G₀.inv_mem (h₁ hnG₁)) g.2⟩ : ↥G₀) • CosetGeom.γ₁ G₀ G₁ G₂ =
      CosetGeom.γ₁ G₀ G₁ G₂ := CosetGeom.smul_γ₁_of_mem h₂ hng
  have e : g = (⟨n, h₁ hnG₁⟩ : ↥G₀) * ⟨n⁻¹ * g, G₀.mul_mem (G₀.inv_mem (h₁ hnG₁)) g.2⟩ := by
    apply Subtype.ext
    simp
  conv_rhs => rw [e, mul_smul, hmem]

private theorem exists_nbr_rep₂ (hG : G₀ = G₁ ⊔ G₂) {U : Subgroup G}
    (hN₂ : ∀ g ∈ G₂, ∃ n ∈ G₂ ⊓ Subgroup.normalizer (U : Set G), n⁻¹ * g ∈ G₁)
    {ε : CosetGeom G₀ G₁ G₂} (hε : ε ∈ CosetGeom.nbrs (CosetGeom.γ₁ G₀ G₁ G₂)) :
    ∃ n : ↥G₀, (n : G) ∈ G₂ ∧ (n : G) ∈ Subgroup.normalizer (U : Set G) ∧
      n • CosetGeom.γ₀ G₀ G₁ G₂ = ε := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  obtain ⟨g, hg, hgε⟩ := CosetGeom.stab_transitive_on_nbrs
    (show CosetGeom.γ₀ G₀ G₁ G₂ ∈ CosetGeom.nbrs (CosetGeom.γ₁ G₀ G₁ G₂) from
      CosetGeom.adj_γ₀_γ₁.symm) hε
  rw [CosetGeom.stab_γ₁ h₂] at hg
  obtain ⟨n, ⟨hnG₂, hnN⟩, hng⟩ := hN₂ g hg
  refine ⟨⟨n, h₂ hnG₂⟩, hnG₂, hnN, ?_⟩
  rw [← hgε]
  have hmem : (⟨n⁻¹ * g, G₀.mul_mem (G₀.inv_mem (h₂ hnG₂)) g.2⟩ : ↥G₀) • CosetGeom.γ₀ G₀ G₁ G₂ =
      CosetGeom.γ₀ G₀ G₁ G₂ := CosetGeom.smul_γ₀_of_mem h₁ hng
  have e : g = (⟨n, h₂ hnG₂⟩ : ↥G₀) * ⟨n⁻¹ * g, G₀.mul_mem (G₀.inv_mem (h₂ hnG₂)) g.2⟩ := by
    apply Subtype.ext
    simp
  conv_rhs => rw [e, mul_smul, hmem]

private theorem good_γ₀ (hG : G₀ = G₁ ⊔ G₂) {U : Subgroup G} (hU : U ≤ G₁ ⊓ G₂)
    (hN₁ : ∀ g ∈ G₁, ∃ n ∈ G₁ ⊓ Subgroup.normalizer (U : Set G), n⁻¹ * g ∈ G₂) :
    Good U (CosetGeom.γ₀ G₀ G₁ G₂) := by
  have h₁ : G₁ ≤ G₀ := hG ▸ le_sup_left
  refine ⟨?_, ?_⟩
  · rw [CosetGeom.stab_γ₀ h₁]
    exact hU.trans inf_le_left
  · intro ε hε ε' hε'
    obtain ⟨n, hnG, hnN, hnε⟩ := exists_nbr_rep₁ hG hN₁ hε
    obtain ⟨n', hnG', hnN', hnε'⟩ := exists_nbr_rep₁ hG hN₁ hε'
    refine ⟨n' * n⁻¹, ?_, ?_, ?_⟩
    · have : ((n' * n⁻¹ : ↥G₀) : G) = (n' : G) * (n : G)⁻¹ := rfl
      rw [this]
      exact (Subgroup.normalizer (U : Set G)).mul_mem hnN' (Subgroup.inv_mem _ hnN)
    · refine CosetGeom.smul_eq_of_mem_stab ?_
      rw [CosetGeom.stab_γ₀ h₁]
      have : ((n' * n⁻¹ : ↥G₀) : G) = (n' : G) * (n : G)⁻¹ := rfl
      rw [this]
      exact G₁.mul_mem hnG' (G₁.inv_mem hnG)
    · rw [← hnε, ← hnε', mul_smul, inv_smul_smul]

private theorem good_γ₁ (hG : G₀ = G₁ ⊔ G₂) {U : Subgroup G} (hU : U ≤ G₁ ⊓ G₂)
    (hN₂ : ∀ g ∈ G₂, ∃ n ∈ G₂ ⊓ Subgroup.normalizer (U : Set G), n⁻¹ * g ∈ G₁) :
    Good U (CosetGeom.γ₁ G₀ G₁ G₂) := by
  have h₂ : G₂ ≤ G₀ := hG ▸ le_sup_right
  refine ⟨?_, ?_⟩
  · rw [CosetGeom.stab_γ₁ h₂]
    exact hU.trans inf_le_right
  · intro ε hε ε' hε'
    obtain ⟨n, hnG, hnN, hnε⟩ := exists_nbr_rep₂ hG hN₂ hε
    obtain ⟨n', hnG', hnN', hnε'⟩ := exists_nbr_rep₂ hG hN₂ hε'
    refine ⟨n' * n⁻¹, ?_, ?_, ?_⟩
    · have : ((n' * n⁻¹ : ↥G₀) : G) = (n' : G) * (n : G)⁻¹ := rfl
      rw [this]
      exact (Subgroup.normalizer (U : Set G)).mul_mem hnN' (Subgroup.inv_mem _ hnN)
    · refine CosetGeom.smul_eq_of_mem_stab ?_
      rw [CosetGeom.stab_γ₁ h₂]
      have : ((n' * n⁻¹ : ↥G₀) : G) = (n' : G) * (n : G)⁻¹ := rfl
      rw [this]
      exact G₂.mul_mem hnG' (G₂.inv_mem hnG)
    · rw [← hnε, ← hnε', mul_smul, inv_smul_smul]

variable [Finite G] {T : Subgroup G}

theorem eq_bot_of_normalizer_transitive (hyp : AmalgamHyp G₀ G₁ G₂ T) {U : Subgroup G}
    (hU : U ≤ G₁ ⊓ G₂)
    (hN₁ : ∀ g ∈ G₁, ∃ n ∈ G₁ ⊓ Subgroup.normalizer (U : Set G), n⁻¹ * g ∈ G₂)
    (hN₂ : ∀ g ∈ G₂, ∃ n ∈ G₂ ⊓ Subgroup.normalizer (U : Set G), n⁻¹ * g ∈ G₁) : U = ⊥ := by
  have hG := hyp.gen
  have hg0 : Good U (CosetGeom.γ₀ G₀ G₁ G₂) := good_γ₀ hG hU hN₁
  have hg1 : Good U (CosetGeom.γ₁ G₀ G₁ G₂) := good_γ₁ hG hU hN₂
  have hall : ∀ n : ℕ, (∀ δ, CosetGeom.dist (CosetGeom.γ₀ G₀ G₁ G₂) δ ≤ n → Good U δ) ∧
      (∀ δ, CosetGeom.dist (CosetGeom.γ₀ G₀ G₁ G₂) δ ≤ n + 1 → Good U δ) := by
    intro n
    induction n with
    | zero =>
      have h0 : ∀ δ, CosetGeom.dist (CosetGeom.γ₀ G₀ G₁ G₂) δ ≤ 0 → Good U δ := by
        intro δ hδ
        have : CosetGeom.γ₀ G₀ G₁ G₂ = δ := (CosetGeom.dist_eq_zero_iff hG).mp (Nat.le_zero.mp hδ)
        rw [← this]
        exact hg0
      refine ⟨h0, fun δ hδ => ?_⟩
      rcases (CosetGeom.dist_le_one_iff hG).mp hδ with rfl | hadj
      · exact hg0
      · exact Good.propagate hg0 hg1 CosetGeom.adj_γ₀_γ₁ hadj
    | succ n ih =>
      refine ⟨ih.2, fun δ hδ => ?_⟩
      by_cases hle : CosetGeom.dist (CosetGeom.γ₀ G₀ G₁ G₂) δ ≤ n + 1
      · exact ih.2 δ hle
      · have hd : CosetGeom.dist (CosetGeom.γ₀ G₀ G₁ G₂) δ = n + 1 + 1 := by omega
        obtain ⟨β, hβδ, hβd⟩ := CosetGeom.exists_adj_dist_eq hG (d := n + 1) hd
        obtain ⟨β', hββ', hβ'd⟩ := CosetGeom.exists_adj_dist_eq hG (d := n) hβd
        exact Good.propagate (ih.2 β hβd.le) (ih.1 β' hβ'd.le) hββ' hβδ.symm
  obtain ⟨n, -, hbot⟩ := CosetGeom.exists_ballStab_eq_bot hyp
  rw [eq_bot_iff]
  intro u hu
  have hu' : u ∈ CosetGeom.ballStab n (CosetGeom.γ₀ G₀ G₁ G₂) :=
    CosetGeom.mem_ballStab.mpr fun δ hδ => ((hall n).1 δ hδ).1 hu
  rw [hbot] at hu'
  exact hu'

end Lemma48

end F112W

end CFSG.Quasithin
