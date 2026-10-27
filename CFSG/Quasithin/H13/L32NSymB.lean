module

public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

namespace CosetGeom

variable {G₀ G₁ G₂ : Subgroup G}

@[expose] def swap : CosetGeom G₀ G₁ G₂ → CosetGeom G₀ G₂ G₁ := Sum.swap

theorem swap_γ₁ : swap (γ₁ G₀ G₁ G₂) = γ₀ G₀ G₂ G₁ := rfl

theorem swap_smul (g : G₀) (γ : CosetGeom G₀ G₁ G₂) : swap (g • γ) = g • swap γ := by
  cases γ <;> rfl

theorem swap_adj {u v : CosetGeom G₀ G₁ G₂} :
    (graph G₀ G₂ G₁).Adj (swap u) (swap v) ↔ (graph G₀ G₁ G₂).Adj u v := by
  cases u <;> cases v
  · exact Iff.rfl
  · exact ⟨fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩, fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩⟩
  · exact ⟨fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩, fun ⟨g, h1, h2⟩ => ⟨g, h2, h1⟩⟩
  · exact Iff.rfl

theorem swap_swap (u : CosetGeom G₀ G₁ G₂) : swap (swap u) = u := by
  cases u <;> rfl

theorem dist_swap (u v : CosetGeom G₀ G₁ G₂) : dist (swap u) (swap v) = dist u v := by
  have hle : ∀ {H₁ H₂ : Subgroup G} (u v : CosetGeom G₀ H₁ H₂),
      (graph G₀ H₂ H₁).edist (swap u) (swap v) ≤ (graph G₀ H₁ H₂).edist u v := by
    intro H₁ H₂ u v
    by_cases h : (graph G₀ H₁ H₂).edist u v = ⊤
    · rw [h]; exact le_top
    · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
      let φ : graph G₀ H₁ H₂ →g graph G₀ H₂ H₁ := ⟨swap, fun {_ _} hab => swap_adj.mpr hab⟩
      have := SimpleGraph.edist_le (p.map φ)
      rw [SimpleGraph.Walk.length_map, hp] at this
      exact this
  have h1 := hle u v
  have h2 := hle (swap u) (swap v)
  rw [swap_swap, swap_swap] at h2
  unfold dist SimpleGraph.dist
  rw [le_antisymm h1 h2]

theorem stab_swap (γ : CosetGeom G₀ G₁ G₂) : stab (swap γ) = stab γ := by
  ext x
  rw [mem_stab, mem_stab]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨h, ?_⟩
    have := congrArg swap hx
    rw [swap_smul, swap_swap] at this
    exact this
  · rintro ⟨h, hx⟩
    exact ⟨h, by rw [← swap_smul, hx]⟩

theorem ballStab_swap (n : ℕ) (γ : CosetGeom G₀ G₁ G₂) : ballStab n (swap γ) = ballStab n γ := by
  ext x
  rw [mem_ballStab, mem_ballStab]
  constructor
  · intro h δ hδ
    have := h (swap δ) (by rwa [dist_swap])
    rwa [stab_swap] at this
  · intro h δ hδ
    have := h (swap δ) (by rwa [← dist_swap, swap_swap])
    rwa [stab_swap] at this

end CosetGeom

open CosetGeom

namespace H13.L32NSym

variable [Finite G]

theorem false_of_critical {G₀ P₁ P₂ T V W : Subgroup G} (h1 : AmalgamHypV G₀ P₁ P₂ T V)
    (h2 : AmalgamHypV G₀ P₂ P₁ T W) (hV : V ≠ ⊥) (hW : W ≠ ⊥)
    (hb : critDist G₀ P₁ P₂ V ≤ critDist G₀ P₂ P₁ W)
    (hC₁ : P₁ ⊓ Subgroup.centralizer (V : Set G) ≤ P₂)
    (hC₂ : P₂ ⊓ Subgroup.centralizer (W : Set G) ≤ P₁)
    (hcomm : ∀ (A B : Subgroup G), (A = V ∨ A = W) → (B = V ∨ B = W) → ∀ g g' u : G,
      u ∈ conjSub g A → u ∈ conjSub g' B → u ≠ 1 →
        ∀ a ∈ conjSub g A, ∀ b ∈ conjSub g' B, a * b = b * a) : False := by
  have hG := h1.gen
  obtain ⟨α, hα, hVα⟩ := exists_dist_eq_critDist_not_le h1 hV
  have hVstab : V ≤ stab α := V_le_stab_of_dist_le h1 hV hα.le
  have hdist : dist α (γ₀ G₀ P₁ P₂) ≤ critDist G₀ P₁ P₂ V := by rw [CosetGeom.dist_comm, hα]
  have key : ∀ (A P : Subgroup G) (γ' : CosetGeom G₀ P₁ P₂) (g : G₀), (A = V ∨ A = W) →
      α = g • γ' → stab γ' = P → P ≤ Subgroup.normalizer (A : Set G) →
      P ⊓ Subgroup.centralizer (A : Set G) ≤ ballStab 1 γ' →
      conjSub (g : G) A ≤ P₁ → False := by
    intro A P γ' g hA hαg hγ' hPA hPC hAP₁
    set Aα := conjSub (g : G) A with hAα
    have hVn : ∀ v ∈ V, ∀ a ∈ Aα, v * a * v⁻¹ ∈ Aα := by
      intro v hv a ha
      have hvP : v ∈ conjSub (g : G) P := by
        have := hVstab hv
        rwa [hαg, stab_smul, hγ'] at this
      rw [mem_conjSub] at hvP ha ⊢
      have := (Subgroup.mem_normalizer_iff.mp (hPA hvP) _).mp ha
      rwa [show (g : G)⁻¹ * v * g * ((g : G)⁻¹ * a * g) * ((g : G)⁻¹ * v * g)⁻¹ =
        (g : G)⁻¹ * (v * a * v⁻¹) * g by group] at this
    have hAn : ∀ a ∈ Aα, ∀ v ∈ V, a * v * a⁻¹ ∈ V := fun a ha v hv =>
      (Subgroup.mem_normalizer_iff.mp (h1.normalizes (hAP₁ ha)) v).mp hv
    obtain ⟨v, hv, a, ha, hva⟩ : ∃ v ∈ V, ∃ a ∈ Aα, v * a ≠ a * v := by
      by_contra hall
      push Not at hall
      apply hVα
      intro x hx
      have hxP : (g : G)⁻¹ * x * g ∈ P ⊓ Subgroup.centralizer (A : Set G) := by
        have hx' : x ∈ conjSub (g : G) P := by
          have := hVstab hx
          rwa [hαg, stab_smul, hγ'] at this
        refine ⟨mem_conjSub.mp hx', Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        have h1' := hall x hx _ (mul_mem_conjSub (g := (g : G)) hy)
        calc y * ((g : G)⁻¹ * x * g) = (g : G)⁻¹ * ((g * y * (g : G)⁻¹) * x) * g := by group
          _ = (g : G)⁻¹ * (x * (g * y * (g : G)⁻¹)) * g := by rw [h1']
          _ = (g : G)⁻¹ * x * g * y := by group
      have := hPC hxP
      rw [hαg, ballStab_smul, mem_conjSub]
      exact this
    set u := v * a * v⁻¹ * a⁻¹ with hu
    have huV : u ∈ V := by
      rw [hu, show v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) by group]
      exact V.mul_mem hv (hAn a ha _ (V.inv_mem hv))
    have huA : u ∈ Aα := by
      rw [hu]
      exact Aα.mul_mem (hVn v hv a ha) (Aα.inv_mem ha)
    have hu1 : u ≠ 1 := fun h => hva (by
      calc v * a = v * a * v⁻¹ * a⁻¹ * (a * v) := by group
        _ = a * v := by rw [← hu, h, one_mul])
    have hVV : V = conjSub (1 : G) V := (conjSub_one V).symm
    have := hcomm V A (Or.inl rfl) hA 1 g u (hVV ▸ huV) huA hu1 v (hVV ▸ hv) a ha
    exact hva this
  cases hvt : vtype α with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hvt
    refine key V P₁ (γ₀ G₀ P₁ P₂) g (Or.inl rfl) hg (stab_γ₀ h1.le₁) h1.normalizes ?_ ?_
    · exact (ballStab_one_γ₀ hG).2.2 ⟨le_inf inf_le_left hC₁, le_normalizer_inf_centralizer h1⟩
    · intro x hx
      have h' : x ∈ ballStab (critDist G₀ P₁ P₂ V) α := by
        rw [hg, ballStab_smul]
        exact conjSub_mono _ (critDist_spec h1 hV).2.1 hx
      have := ballStab_le_stab_of_dist_le hdist h'
      rwa [stab_γ₀ h1.le₁] at this
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hvt
    have hW' : W ≤ ballStab (critDist G₀ P₂ P₁ W) (γ₁ G₀ P₁ P₂) := by
      rw [← ballStab_swap, swap_γ₁]
      exact (critDist_spec h2 hW).2.1
    refine key W P₂ (γ₁ G₀ P₁ P₂) g (Or.inr rfl) hg (stab_γ₁ h1.le₂) h2.normalizes ?_ ?_
    · exact (ballStab_one_γ₁ hG).2.2 ⟨le_inf hC₂ inf_le_left, le_normalizer_inf_centralizer h2⟩
    · intro x hx
      have h' : x ∈ ballStab (critDist G₀ P₂ P₁ W) α := by
        rw [hg, ballStab_smul]
        exact conjSub_mono _ hW' hx
      have := ballStab_le_stab_of_dist_le (hdist.trans hb) h'
      rwa [stab_γ₀ h1.le₁] at this

theorem false_of_two_amalgams {G₀ P₁ P₂ T V W : Subgroup G} (h1 : AmalgamHypV G₀ P₁ P₂ T V)
    (h2 : AmalgamHypV G₀ P₂ P₁ T W) (hV : V ≠ ⊥) (hW : W ≠ ⊥)
    (hC₁ : P₁ ⊓ Subgroup.centralizer (V : Set G) ≤ P₂)
    (hC₂ : P₂ ⊓ Subgroup.centralizer (W : Set G) ≤ P₁)
    (hcomm : ∀ (A B : Subgroup G), (A = V ∨ A = W) → (B = V ∨ B = W) → ∀ g g' u : G,
      u ∈ conjSub g A → u ∈ conjSub g' B → u ≠ 1 →
        ∀ a ∈ conjSub g A, ∀ b ∈ conjSub g' B, a * b = b * a) : False := by
  rcases le_total (critDist G₀ P₁ P₂ V) (critDist G₀ P₂ P₁ W) with hb | hb
  · exact false_of_critical h1 h2 hV hW hb hC₁ hC₂ hcomm
  · exact false_of_critical h2 h1 hW hV hb hC₂ hC₁ fun A B hA hB =>
      hcomm A B hA.symm hB.symm

end H13.L32NSym

end CFSG.Quasithin
