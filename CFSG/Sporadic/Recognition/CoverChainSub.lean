module

public import CFSG.Sporadic.Recognition.CoverRecipeSq

public section

namespace CFSG.Sporadic.Recognition.CoverRecipe

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverTransfer

variable {m : ℕ}

theorem mem_cover₂Words_of_subset {R R' : List (List (Fin m × Bool))}
    (hR : ∀ r ∈ R, r ∈ R') {cw : Fin m → List (Fin m × Bool)} {w : List (Fin m × Bool)}
    (hw : w ∈ cover₂Words R cw) : w ∈ cover₂Words R' cw := by
  rw [mem_cover₂Words] at hw ⊢
  simp only [coverWords, squareWords, List.mem_append, List.mem_flatMap, List.mem_map,
    List.mem_finRange, true_and] at hw ⊢
  rcases hw with (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩) | ⟨r, hr, rfl⟩
  · exact Or.inl (Or.inl ⟨i, r, hR r hr, rfl⟩)
  · exact Or.inl (Or.inr ⟨i, rfl⟩)
  · exact Or.inr ⟨r, hR r hr, rfl⟩

theorem mem_restrictWords_of_subset {S : List (Fin m)} {ws ws' : List (List (Fin m × Bool))}
    (h : ∀ w ∈ ws, w ∈ ws') {w : List (Fin S.length × Bool)} (hw : w ∈ restrictWords S ws) :
    w ∈ restrictWords S ws' := by
  simp only [restrictWords, List.mem_filterMap] at hw ⊢
  obtain ⟨v, hv, hvw⟩ := hw
  exact ⟨v, h v hv, hvw⟩

theorem exists_surjective_PG {ws₀ ws : List (List (Fin m × Bool))} (h : ∀ w ∈ ws₀, w ∈ ws) :
    ∃ π : PG m ws₀ →* PG m ws, Function.Surjective π ∧
      ∀ i, π (PresentedGroup.of i) = PresentedGroup.of i := by
  have hrel : ∀ r ∈ {r : FreeGroup (Fin m) | r ∈ ws₀.map FreeGroup.mk},
      FreeGroup.lift (PresentedGroup.of : Fin m → PG m ws) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [← mk_eq_lift_of]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (h w hw))
  refine ⟨PresentedGroup.toGroup hrel, ?_, fun i => PresentedGroup.toGroup.of hrel⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of hrel⟩

theorem card_le_of_subsetCheckShortCC_sub {ws₀ ws : List (List (Fin m × Bool))}
    (hsub : ∀ w ∈ ws₀, w ∈ ws) (S : List ℕ) {k cap n : ℕ}
    (h : subsetCheckShortCC ws₀ S k cap n = true)
    [Finite (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws))] :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤
      n * Nat.card (PG (subsetOf m S).length (restrictWords (subsetOf m S) ws)) := by
  obtain ⟨π, hπs, hπo⟩ := exists_surjective_PG hsub
  obtain ⟨hfi₀, hidx₀⟩ := index_le_of_subsetCheckShortCC ws₀ S h
    (genSub {r : FreeGroup (Fin m) | r ∈ ws₀.map FreeGroup.mk} (subsetOf m S))
    (fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩)
  have hmap : (genSub {r : FreeGroup (Fin m) | r ∈ ws₀.map FreeGroup.mk}
      (subsetOf m S)).map π =
      genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (subsetOf m S) := by
    unfold genSub
    rw [MonoidHom.map_closure, Set.image_image]
    simp only [hπo]
  have hdvd := Subgroup.index_map_dvd (H := genSub {r : FreeGroup (Fin m) |
    r ∈ ws₀.map FreeGroup.mk} (subsetOf m S)) hπs
  rw [hmap] at hdvd
  have hne : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (subsetOf m S)).index ≠ 0 := fun h0 => by
    rw [h0, zero_dvd_iff] at hdvd
    exact hfi₀.index_ne_zero hdvd
  have hfi : (genSub {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
      (subsetOf m S)).FiniteIndex := ⟨hne⟩
  exact card_le_of_genSub_index ws (subsetOf m S) hfi
    ((Nat.le_of_dvd (Nat.pos_of_ne_zero hfi₀.index_ne_zero) hdvd).trans hidx₀)

theorem card_PG_le_of_subsetCheckShortCC_nil_sub {ws₀ ws : List (List (Fin m × Bool))}
    (hsub : ∀ w ∈ ws₀, w ∈ ws) {k cap n : ℕ} (h : subsetCheckShortCC ws₀ [] k cap n = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  obtain ⟨hf, hc⟩ := card_PG_le_of_subsetCheckShortCC_nil ws₀ h
  obtain ⟨π, hπs, -⟩ := exists_surjective_PG hsub
  exact ⟨Finite.of_surjective π hπs, (Nat.card_le_card_of_surjective π hπs).trans hc⟩

theorem card_PG_le_chain₃_sub {ws L₃ : List (List (Fin m × Bool))} {S₁ S₂ : List ℕ}
    {L₂ : List (List (Fin (subsetOf m S₁).length × Bool))}
    {L₁ : List (List (Fin (subsetOf (subsetOf m S₁).length S₂).length × Bool))}
    (h₃s : ∀ w ∈ L₃, w ∈ ws) (h₂s : ∀ w ∈ L₂, w ∈ restrictWords (subsetOf m S₁) ws)
    (h₁s : ∀ w ∈ L₁, w ∈ restrictWords (subsetOf (subsetOf m S₁).length S₂)
      (restrictWords (subsetOf m S₁) ws))
    {k₃ k₂ k₁ c₃ c₂ c₁ n₃ n₂ n₁ : ℕ} (h₃ : subsetCheckShortCC L₃ S₁ k₃ c₃ n₃ = true)
    (h₂ : subsetCheckShortCC L₂ S₂ k₂ c₂ n₂ = true)
    (h₁ : subsetCheckShortCC L₁ [] k₁ c₁ n₁ = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₃ * (n₂ * n₁) := by
  have h₁s' : ∀ w ∈ L₁, w ∈ restrictWords (subsetOf (subsetOf m S₁).length S₂)
      (restrictWords (subsetOf m S₁) ws) := h₁s
  obtain ⟨f1, c1⟩ := card_PG_le_of_subsetCheckShortCC_nil_sub h₁s' h₁
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckShortCC_sub (ws := restrictWords (subsetOf m S₁) ws)
    h₂s S₂ h₂
  have := f2
  obtain ⟨f3, c3⟩ := card_le_of_subsetCheckShortCC_sub h₃s S₁ h₃
  exact ⟨f3, c3.trans (Nat.mul_le_mul_left _ (c2.trans (Nat.mul_le_mul_left _ c1)))⟩

theorem card_PG_le_chain₂_sub {ws L₂ : List (List (Fin m × Bool))} {S : List ℕ}
    {L₁ : List (List (Fin (subsetOf m S).length × Bool))}
    (h₂s : ∀ w ∈ L₂, w ∈ ws) (h₁s : ∀ w ∈ L₁, w ∈ restrictWords (subsetOf m S) ws)
    {k₂ k₁ c₂ c₁ n₂ n₁ : ℕ} (h₂ : subsetCheckShortCC L₂ S k₂ c₂ n₂ = true)
    (h₁ : subsetCheckShortCC L₁ [] k₁ c₁ n₁ = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₂ * n₁ := by
  obtain ⟨f1, c1⟩ := card_PG_le_of_subsetCheckShortCC_nil_sub h₁s h₁
  have := f1
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckShortCC_sub h₂s S h₂
  exact ⟨f2, c2.trans (Nat.mul_le_mul_left _ c1)⟩

theorem card_PG_le_chain₄_sub {ws L₄ : List (List (Fin m × Bool))} {S₁ S₂ S₃ : List ℕ}
    {L₃ : List (List (Fin (subsetOf m S₁).length × Bool))}
    {L₂ : List (List (Fin (subsetOf (subsetOf m S₁).length S₂).length × Bool))}
    {L₁ : List (List (Fin (subsetOf (subsetOf (subsetOf m S₁).length S₂).length S₃).length × Bool))}
    (h₄s : ∀ w ∈ L₄, w ∈ ws) (h₃s : ∀ w ∈ L₃, w ∈ restrictWords (subsetOf m S₁) ws)
    (h₂s : ∀ w ∈ L₂, w ∈ restrictWords (subsetOf (subsetOf m S₁).length S₂)
      (restrictWords (subsetOf m S₁) ws))
    (h₁s : ∀ w ∈ L₁, w ∈ restrictWords
      (subsetOf (subsetOf (subsetOf m S₁).length S₂).length S₃)
      (restrictWords (subsetOf (subsetOf m S₁).length S₂) (restrictWords (subsetOf m S₁) ws)))
    {k₄ k₃ k₂ k₁ c₄ c₃ c₂ c₁ n₄ n₃ n₂ n₁ : ℕ} (h₄ : subsetCheckShortCC L₄ S₁ k₄ c₄ n₄ = true)
    (h₃ : subsetCheckShortCC L₃ S₂ k₃ c₃ n₃ = true) (h₂ : subsetCheckShortCC L₂ S₃ k₂ c₂ n₂ = true)
    (h₁ : subsetCheckShortCC L₁ [] k₁ c₁ n₁ = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₄ * (n₃ * (n₂ * n₁)) := by
  obtain ⟨f1, c1⟩ := card_PG_le_of_subsetCheckShortCC_nil_sub h₁s h₁
  have := f1
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckShortCC_sub h₂s S₃ h₂
  have := f2
  obtain ⟨f3, c3⟩ := card_le_of_subsetCheckShortCC_sub h₃s S₂ h₃
  have := f3
  obtain ⟨f4, c4⟩ := card_le_of_subsetCheckShortCC_sub h₄s S₁ h₄
  exact ⟨f4, c4.trans (Nat.mul_le_mul_left _ (c3.trans (Nat.mul_le_mul_left _
    (c2.trans (Nat.mul_le_mul_left _ c1)))))⟩

end CFSG.Sporadic.Recognition.CoverRecipe
