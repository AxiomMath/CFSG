module

public import CFSG.Timmesfeld.ARS.NaturalModule

public section

namespace CFSG.RankThree.GF2n

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS

theorem sup_image_of_sup_hom {α β : Type*} [Lattice α] [OrderBot α] [Lattice β] [OrderBot β]
    [DecidableEq β] (s : Finset α) (φ : α → β) (hsup : ∀ x y, φ (x ⊔ y) = φ x ⊔ φ y)
    (hbot : φ ⊥ = ⊥) : (s.image φ).sup id = φ (s.sup id) := by
  rw [Finset.sup_image, Finset.apply_sup_eq_sup_comp φ hsup hbot]
  rfl

theorem supIndep_image_of_lattice_hom {α β : Type*} [Lattice α] [OrderBot α] [Lattice β]
    [OrderBot β] [DecidableEq β] {s : Finset α} (hs : s.SupIndep id) (φ : α → β)
    (hsup : ∀ x y, φ (x ⊔ y) = φ x ⊔ φ y) (hinf : ∀ x y, φ (x ⊓ y) = φ x ⊓ φ y)
    (hbot : φ ⊥ = ⊥) : (s.image φ).SupIndep id := by
  refine Finset.SupIndep.image ?_
  intro t ht i hi hit
  have h := hs ht hi hit
  have hsup' : t.sup (id ∘ φ) = φ (t.sup id) := by
    rw [Finset.apply_sup_eq_sup_comp φ hsup hbot]
    rfl
  rw [Function.comp_apply, id, hsup', disjoint_iff, ← hinf,
    (disjoint_iff.mp h : i ⊓ t.sup id = ⊥), hbot]

variable {K V : Type*} [Field K] [CharP K 2] [PerfectRing K 2] [AddCommGroup V] [Finite V]
  [DistribMulAction (SpecialLinearGroup (Fin 2) K) V]

omit [CharP K 2] [PerfectRing K 2] [Finite V] in
theorem sup_isInv {s : Finset (AddSubgroup V)}
    (hs : ∀ W ∈ s, ∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) :
    ∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ s.sup id, g • v ∈ s.sup id := by
  intro g
  refine Finset.sup_induction (p := fun U : AddSubgroup V => ∀ v ∈ U, g • v ∈ U) ?_ ?_
    fun W hW => hs W hW g
  · intro v hv
    rw [AddSubgroup.mem_bot.mp hv, smul_zero]
    exact AddSubgroup.zero_mem _
  · intro U₁ h₁ U₂ h₂ v hv
    obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.mp hv
    rw [smul_add]
    exact AddSubgroup.add_mem _ (AddSubgroup.mem_sup_left (h₁ y hy))
      (AddSubgroup.mem_sup_right (h₂ z hz))

omit [CharP K 2] [PerfectRing K 2] [Finite V] in
theorem eq_bot_or_eq_range {θ : (Fin 2 → K) →+ V}
    (hθ : ∀ (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v)
    {U : AddSubgroup V} (hU : U ≤ θ.range)
    (hUinv : ∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) : U = ⊥ ∨ U = θ.range := by
  by_cases hU0 : U = ⊥
  · exact Or.inl hU0
  right
  obtain ⟨⟨u, huU⟩, hu0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hU0
  have hu0 : u ≠ 0 := fun h => hu0' (Subtype.ext h)
  obtain ⟨v₀, hv₀⟩ := hU huU
  have hv₀0 : v₀ ≠ 0 := fun h => hu0 (by rw [← hv₀, h, map_zero])
  refine le_antisymm hU ?_
  rintro _ ⟨v, rfl⟩
  by_cases hv : v = 0
  · rw [hv, map_zero]
    exact U.zero_mem
  obtain ⟨g₀, hg₀⟩ := NaturalModule.exists_mulVec_eq hv₀0
  obtain ⟨g₁, hg₁⟩ := NaturalModule.exists_mulVec_eq hv
  have h1 : θ v₀ = g₀ • θ ![1, 0] := by rw [← hg₀, hθ]
  have h2 : θ v = g₁ • (g₀⁻¹ • θ v₀) := by rw [h1, inv_smul_smul, ← hθ, hg₁]
  rw [h2]
  exact hUinv _ _ (hUinv _ _ (hv₀ ▸ huU))

theorem exists_supIndep_natural
    (hfix : ∀ v : V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0)
    (hquad : ∀ a ∈ upperUnipotent K, ∀ a' ∈ upperUnipotent K, ∀ v : V,
      a' • (a • v - v) = a • v - v)
    {L : AddSubgroup V} (hL : ∀ w ∈ L, ∀ a ∈ upperUnipotent K, a • w = w)
    (hgen : ∀ U : AddSubgroup V, (∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) →
      L ≤ U → U = ⊤) :
    ∃ s : Finset (AddSubgroup V), s.SupIndep id ∧ s.sup id = ⊤ ∧
      ∀ W ∈ s, (∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) ∧ W ≠ ⊥ ∧
        (∀ U ≤ W, (∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) → U = ⊥ ∨ U = W) ∧
        ∃ θ : (Fin 2 → K) →+ V, Function.Injective θ ∧ θ.range = W ∧
          ∀ (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
            θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v := by
  classical
  set P : AddSubgroup V → Prop := fun W =>
    (∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ W, g • v ∈ W) ∧ W ≠ ⊥ ∧
      (∀ U ≤ W, (∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ U, g • v ∈ U) → U = ⊥ ∨ U = W) ∧
      ∃ θ : (Fin 2 → K) →+ V, Function.Injective θ ∧ θ.range = W ∧
        ∀ (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
          θ ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ v with hP
  have hnat : ∀ w ∈ L, w ≠ 0 → ∃ W, P W ∧ w ∈ W := by
    intro w hw hw0
    obtain ⟨θ, hinj, -, he, hθ⟩ := exists_natural_of_quadratic hfix hquad (hL w hw) hw0
    refine ⟨θ.range, ⟨?_, ?_, fun U hU hUinv => eq_bot_or_eq_range hθ hU hUinv, θ, hinj,
      rfl, hθ⟩, ⟨![1, 0], he⟩⟩
    · rintro g _ ⟨v, rfl⟩
      exact ⟨_, hθ g v⟩
    · intro h
      apply hw0
      have : w ∈ θ.range := ⟨![1, 0], he⟩
      rwa [h, AddSubgroup.mem_bot] at this
  have key : ∀ S : AddSubgroup V, ∀ s : Finset (AddSubgroup V), s.SupIndep id → s.sup id = S →
      (∀ W ∈ s, P W) → ∃ s' : Finset (AddSubgroup V), s'.SupIndep id ∧ L ≤ s'.sup id ∧
        ∀ W ∈ s', P W := by
    intro S
    induction S using WellFoundedGT.induction with
    | _ S ih =>
    intro s hs hsS hsP
    by_cases hLS : L ≤ S
    · exact ⟨s, hs, hsS ▸ hLS, hsP⟩
    obtain ⟨w, hwL, hwS⟩ := IsConcreteLE.not_le_iff_exists.mp hLS
    have hw0 : w ≠ 0 := fun h => hwS (h ▸ S.zero_mem)
    obtain ⟨W, hWP, hwW⟩ := hnat w hwL hw0
    have hSinv : ∀ g : SpecialLinearGroup (Fin 2) K, ∀ v ∈ S, g • v ∈ S := by
      rw [← hsS]
      exact sup_isInv fun W hW => (hsP W hW).1
    have hdis : Disjoint W S := by
      rw [disjoint_iff]
      rcases hWP.2.2.1 (W ⊓ S) inf_le_left (fun g v hv => ⟨hWP.1 g v hv.1, hSinv g v hv.2⟩) with
        h | h
      · exact h
      · exact absurd ((h ▸ inf_le_right : W ≤ S) hwW) hwS
    have hlt : S < W ⊔ S :=
      lt_of_le_of_ne le_sup_right fun h => hwS (h ▸ AddSubgroup.mem_sup_left hwW)
    refine ih (W ⊔ S) hlt (insert W s) (hs.insert (by rw [hsS]; exact hdis)) ?_ ?_
    · rw [Finset.sup_insert, hsS]
      rfl
    · intro V' hV'
      rcases Finset.mem_insert.mp hV' with rfl | hV'
      · exact hWP
      · exact hsP V' hV'
  obtain ⟨s, hs, hLs, hsP⟩ := key ⊥ ∅ (Finset.supIndep_empty _) (by simp) (by simp)
  exact ⟨s, hs, hgen _ (sup_isInv fun W hW => (hsP W hW).1) hLs, hsP⟩

end CFSG.RankThree.GF2n
