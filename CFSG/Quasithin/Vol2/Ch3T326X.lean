module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

variable {Γ : Type} [Group Γ]

@[expose] def IsInnerOn (K : Subgroup Γ) (g : Γ) : Prop :=
  ∃ a ∈ K, ∀ b ∈ K, a⁻¹ * g * b = b * (a⁻¹ * g)

theorem conjAct_mem_range_conj_iff {K : Subgroup Γ} (g : Subgroup.normalizer (K : Set Γ)) :
    conjAct K g ∈ (MulAut.conj : ↥K →* MulAut ↥K).range ↔ IsInnerOn K (g : Γ) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, a.2, fun b hb => ?_⟩
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨b, hb⟩ : ↥K) : Γ)) ha
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, Setup.coe_conjAct_apply] at h1
    calc (a : Γ)⁻¹ * g * b = (a : Γ)⁻¹ * ((g : Γ) * b * (g : Γ)⁻¹) * g := by group
      _ = (a : Γ)⁻¹ * ((a : Γ) * b * (a : Γ)⁻¹) * g := by rw [← h1]
      _ = b * ((a : Γ)⁻¹ * g) := by group
  · rintro ⟨a, ha, h⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    ext b
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, Setup.coe_conjAct_apply]
    have h1 := h b b.2
    calc a * (b : Γ) * a⁻¹ = a * ((a⁻¹ * g) * b) * (g : Γ)⁻¹ := by rw [h1]; group
      _ = (g : Γ) * b * (g : Γ)⁻¹ := by group

theorem index_range_conj_eq_two {K : Subgroup Γ} (hK : IsPSL 3 2 1 ↥K) :
    ((MulAut.conj : ↥K →* MulAut ↥K).range).index = 2 := by
  have hcard := SBc11.card_of_isPSL_three_two hK
  have : Finite ↥K := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcen := SBc11.center_eq_bot_of_list (Or.inl hK)
  obtain ⟨e₁⟩ := Bridge.nonempty_sl3_of_isPSL hK
  have hAut : Nat.card (MulAut ↥K) = 336 := by
    set e := e₁.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)) with he
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact S153E58.card_mulAut_statedSL_three_two
  have hinj : Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 := congrArg (fun φ : MulAut ↥K => φ b) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc b * a = a * b * a⁻¹ * a := by rw [h1]
        _ = a * b := by group
    rw [hcen, Subgroup.mem_bot] at hz
    exact hz
  have hInn : Nat.card ↥((MulAut.conj : ↥K →* MulAut ↥K).range) = 168 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]
  have h := Subgroup.index_mul_card ((MulAut.conj : ↥K →* MulAut ↥K).range)
  rw [hInn, hAut] at h
  omega

theorem isInnerOn_mul_inv {K : Subgroup Γ} (hK : IsPSL 3 2 1 ↥K) {g₁ g₂ : Γ}
    (h₁ : g₁ ∈ Subgroup.normalizer (K : Set Γ)) (h₂ : g₂ ∈ Subgroup.normalizer (K : Set Γ))
    (hn₁ : ¬ IsInnerOn K g₁) (hn₂ : ¬ IsInnerOn K g₂) : IsInnerOn K (g₁ * g₂⁻¹) := by
  have hidx := index_range_conj_eq_two hK
  have e : (⟨g₁ * g₂⁻¹, Subgroup.mul_mem _ h₁ (Subgroup.inv_mem _ h₂)⟩ :
      Subgroup.normalizer (K : Set Γ)) = ⟨g₁, h₁⟩ * ⟨g₂, h₂⟩⁻¹ := rfl
  have key := conjAct_mem_range_conj_iff
    (⟨g₁ * g₂⁻¹, Subgroup.mul_mem _ h₁ (Subgroup.inv_mem _ h₂)⟩ : Subgroup.normalizer (K : Set Γ))
  rw [e, map_mul, map_inv, Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff,
    conjAct_mem_range_conj_iff, conjAct_mem_range_conj_iff] at key
  exact key.mp (iff_of_false hn₁ hn₂)

theorem autOn_eq_top {K M : Subgroup Γ} (hK : IsPSL 3 2 1 ↥K) (hKM : K ≤ M) {g : Γ}
    (hgM : g ∈ M) (hg : g ∈ Subgroup.normalizer (K : Set Γ)) (hn : ¬ IsInnerOn K g) :
    autOn M K = ⊤ := by
  have hidx := index_range_conj_eq_two hK
  have hinn : (MulAut.conj : ↥K →* MulAut ↥K).range ≤ autOn M K := by
    rintro _ ⟨a, rfl⟩
    refine Setup.mem_autOn_iff.mpr ⟨⟨a, Subgroup.le_normalizer a.2⟩, hKM a.2, ?_⟩
    ext b
    simp only [Setup.coe_conjAct_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hgA : conjAct K ⟨g, hg⟩ ∈ autOn M K := Setup.mem_autOn_iff.mpr ⟨⟨g, hg⟩, hgM, rfl⟩
  have hgn : conjAct K ⟨g, hg⟩ ∉ (MulAut.conj : ↥K →* MulAut ↥K).range :=
    fun h => hn ((conjAct_mem_range_conj_iff _).mp h)
  rw [eq_top_iff]
  intro β _
  by_cases hβ : β ∈ (MulAut.conj : ↥K →* MulAut ↥K).range
  · exact hinn hβ
  · have h1 : β * (conjAct K ⟨g, hg⟩)⁻¹ ∈ (MulAut.conj : ↥K →* MulAut ↥K).range := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff]
      exact iff_of_false hβ hgn
    have h2 := (autOn M K).mul_mem (hinn h1) hgA
    rwa [inv_mul_cancel_right] at h2

end CFSG.Quasithin.H13.T326
