module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {Γ : Type*} [Group Γ]

theorem isDirectProduct_of_subset {S T : Set (Subgroup Γ)} {L : Subgroup Γ}
    (hL : IsDirectProduct S L) (hT : T ⊆ S) : IsDirectProduct T (sSup T) where
  commute J hJ K hK hJK := hL.commute J (hT hJ) K (hT hK) hJK
  indep := hL.indep.mono hT
  sSup_eq := rfl

theorem le_normalizer_of_conj_mem {H P : Subgroup Γ} (h : ∀ c ∈ H, ∀ x ∈ P, c * x * c⁻¹ ∈ P) :
    H ≤ Subgroup.normalizer (P : Set Γ) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h c hc x, fun hx => ?_⟩
  have := h c⁻¹ (inv_mem hc) _ hx
  simpa [mul_assoc] using this

theorem isMulCommutative_of_le {N P : Subgroup Γ} (hNP : N ≤ P) [IsMulCommutative P] :
    IsMulCommutative N := by
  rw [isMulCommutative_iff]
  intro a b
  have h := congrArg (Subtype.val : P → Γ) (mul_comm' (⟨a, hNP a.2⟩ : P) ⟨b, hNP b.2⟩)
  exact Subtype.ext h

theorem isNilpotent_of_injective {H K : Type*} [Group H] [Group K] [Group.IsNilpotent K]
    (f : H →* K) (hf : Function.Injective f) : Group.IsNilpotent H :=
  Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective hf).symm

theorem map_conj_map_conj (J : Subgroup Γ) (a b : Γ) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, by simp [mul_assoc]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, by simp [mul_assoc]⟩

theorem map_conj_one (J : Subgroup Γ) : J.map (MulAut.conj (1 : Γ)).toMonoidHom = J := by
  ext x
  simp

variable {S S₁ : Set (Subgroup Γ)} {L L₁ : Subgroup Γ}

theorem le_of_subset (hL : IsDirectProduct S L) (hL₁ : IsDirectProduct S₁ L₁) (hS : S₁ ⊆ S) :
    L₁ ≤ L := by
  rw [← hL₁.sSup_eq, ← hL.sSup_eq]
  exact sSup_le_sSup hS

theorem projIn_mono (J : Subgroup Γ) {X Y : Subgroup Γ} (h : X ≤ Y) :
    projIn S J X ≤ projIn S J Y :=
  proj_mono h

variable [Finite Γ]

theorem coord_eq_of_subset (hL : IsDirectProduct S L) (hL₁ : IsDirectProduct S₁ L₁)
    (hS : S₁ ⊆ S) {J : Subgroup Γ} (hJ₁ : J ∈ S₁) {y : Γ} (hy : y ∈ L₁) :
    ((hL₁.coord hJ₁ ⟨y, hy⟩ : J) : Γ) =
      ((hL.coord (hS hJ₁) ⟨y, le_of_subset hL hL₁ hS hy⟩ : J) : Γ) := by
  obtain ⟨j, hj, l, hl, rfl⟩ := (mem_sup_iff_of_commute (hL₁.commute_sSup_diff hJ₁)).mp
    ((hL₁.isDirectPair hJ₁).sup_eq ▸ hy)
  have hl' : l ∈ sSup (S \ {J}) := sSup_le_sSup (Set.sdiff_subset_sdiff_left hS) hl
  rw [hL₁.coord_mul hJ₁ hj hl, hL.coord_mul (hS hJ₁) hj hl']

theorem disjoint_sSup_sSup (hL : IsDirectProduct S L) {T₁ T₂ : Set (Subgroup Γ)} (h₁ : T₁ ⊆ S)
    (h₂ : T₂ ⊆ S) (hd : Disjoint T₁ T₂) : Disjoint (sSup T₁) (sSup T₂) := by
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hxL : x ∈ L := hL.sSup_diff_le T₁ h₁ hx1
  have hx1' : (⟨x, hxL⟩ : L) = 1 := by
    refine hL.ext_coord fun J hJ => ?_
    rw [map_one, hL.coord_eq_one_iff hJ ⟨x, hxL⟩]
    by_cases hJ₁ : J ∈ T₁
    · have hJ₂ : J ∉ T₂ := fun hJ₂ => Set.disjoint_left.mp hd hJ₁ hJ₂
      have hsub : T₂ ⊆ S \ {J} := fun K hK => ⟨h₂ hK, fun hKJ => hJ₂ (hKJ ▸ hK)⟩
      exact sSup_le_sSup hsub hx2
    · have hsub : T₁ ⊆ S \ {J} := fun K hK => ⟨h₁ hK, fun hKJ => hJ₁ (hKJ ▸ hK)⟩
      exact sSup_le_sSup hsub hx1
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx1')

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210
