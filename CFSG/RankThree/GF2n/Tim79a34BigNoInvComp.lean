module

public import CFSG.RankThree.GF2n.Tim79a34SpRad
public import CFSG.Timmesfeld.Bridge.RootStructR2Higman

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped Matrix
open CFSG CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic

section Graph

variable {n : ℕ} {F : Type} [Field F]

theorem exists_graph_fun [CharP F 2] {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T S : Subgroup (StatedSp n F)} (hT : IsTransGroup a T) (hS : S ≤ spRad a)
    (hsup : S ⊔ T = spRad a) (hinf : S ⊓ T = ⊥) :
    ∃ s : (Fin n ⊕ Fin n → F) → F, ∀ w : Fin n ⊕ Fin n → F, spForm a w = 0 → ∀ l : F,
      (∃ x ∈ S, ∀ v, SpExtras.mat n F x *ᵥ v =
        v + spForm a v • w + spForm w v • a + (l * spForm a v) • a) ↔ l = s w := by
  have hex : ∀ w : Fin n ⊕ Fin n → F, ∃ l : F, spForm a w = 0 → ∃ x ∈ S, ∀ v,
      SpExtras.mat n F x *ᵥ v =
        v + spForm a v • w + spForm w v • a + (l * spForm a v) • a := by
    intro w
    by_cases hw : spForm a w = 0
    · obtain ⟨x, hxS, l, hx⟩ := exists_mem_param ha hT hS hsup hw
      exact ⟨l, fun _ => ⟨x, hxS, hx⟩⟩
    · exact ⟨0, fun h => absurd h hw⟩
  choose s hs using hex
  refine ⟨s, fun w hw l => ⟨?_, ?_⟩⟩
  · rintro ⟨x, hxS, hx⟩
    obtain ⟨y, hyS, hy⟩ := hs w hw
    exact param_eq_of_mem_inf ha hT hinf hw hx hy hxS hyS
  · rintro rfl
    exact hs w hw

theorem graph_fun_add [CharP F 2] {a : Fin n ⊕ Fin n → F} {S : Subgroup (StatedSp n F)}
    {s : (Fin n ⊕ Fin n → F) → F}
    (hs : ∀ w : Fin n ⊕ Fin n → F, spForm a w = 0 → ∀ l : F,
      (∃ x ∈ S, ∀ v, SpExtras.mat n F x *ᵥ v =
        v + spForm a v • w + spForm w v • a + (l * spForm a v) • a) ↔ l = s w)
    {w w' : Fin n ⊕ Fin n → F} (hw : spForm a w = 0) (hw' : spForm a w' = 0) :
    s (w + w') = s w + s w' + spForm w w' := by
  obtain ⟨x, hxS, hx⟩ := (hs w hw (s w)).2 rfl
  obtain ⟨y, hyS, hy⟩ := (hs w' hw' (s w')).2 rfl
  have hww' : spForm a (w + w') = 0 := by rw [spForm_add_right, hw, hw', add_zero]
  exact ((hs (w + w') hww' _).1 ⟨x * y, S.mul_mem hxS hyS,
    fun v => mat_mul_mulVec_of_param hw hw' hx hy v⟩).symm

theorem graph_fun_transvection [CharP F 2] {a : Fin n ⊕ Fin n → F}
    {S : Subgroup (StatedSp n F)} {s : (Fin n ⊕ Fin n → F) → F}
    (hs : ∀ w : Fin n ⊕ Fin n → F, spForm a w = 0 → ∀ l : F,
      (∃ x ∈ S, ∀ v, SpExtras.mat n F x *ᵥ v =
        v + spForm a v • w + spForm w v • a + (l * spForm a v) • a) ↔ l = s w)
    {w : Fin n ⊕ Fin n → F} {μ : F} {g : StatedSp n F} (hw : spForm a w = 0)
    (hg : SpExtras.mat n F g = spTrans w μ) (hinv : ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    {u : Fin n ⊕ Fin n → F} (hu : spForm a u = 0) :
    s (u + (μ * spForm w u) • w) = s u := by
  have hga : SpExtras.mat n F g *ᵥ a = a := by
    rw [hg, spTrans_mulVec, spForm_eq_zero_comm hw, mul_zero, zero_smul, add_zero]
  have hgu : SpExtras.mat n F g *ᵥ u = u + (μ * spForm w u) • w := by
    rw [hg, spTrans_mulVec]
  have hgu0 : spForm a (SpExtras.mat n F g *ᵥ u) = 0 := spForm_mat_mulVec_eq_zero hga hu
  obtain ⟨x, hxS, hx⟩ := (hs u hu (s u)).2 rfl
  rw [← hgu]
  exact ((hs _ hgu0 (s u)).1 ⟨g * x * g⁻¹, hinv x hxS,
    fun v => mat_conj_mulVec_of_param hx hga v⟩).symm

theorem graph_fun_const [CharP F 2] {a : Fin n ⊕ Fin n → F} {S : Subgroup (StatedSp n F)}
    {s : (Fin n ⊕ Fin n → F) → F}
    (hs : ∀ w : Fin n ⊕ Fin n → F, spForm a w = 0 → ∀ l : F,
      (∃ x ∈ S, ∀ v, SpExtras.mat n F x *ᵥ v =
        v + spForm a v • w + spForm w v • a + (l * spForm a v) • a) ↔ l = s w)
    (hinv : ∀ (w : Fin n ⊕ Fin n → F) (μ : F) (g : StatedSp n F), spForm a w = 0 →
      SpExtras.mat n F g = spTrans w μ → ∀ x ∈ S, g * x * g⁻¹ ∈ S)
    {x y : Fin n ⊕ Fin n → F} (hx : spForm a x = 0) (hy : spForm a y = 0)
    (hxa : ∀ c : F, x ≠ c • a) (hya : ∀ c : F, y ≠ c • a) : s x = s y := by
  have step : ∀ {x y : Fin n ⊕ Fin n → F}, spForm a x = 0 → spForm a y = 0 →
      spForm x y ≠ 0 → s x = s y := by
    intro x y hx hy hxy
    have hyx : spForm y x ≠ 0 := by rw [spForm_comm]; exact neg_ne_zero.2 hxy
    have hw : spForm a (y - x) = 0 := by rw [spForm_sub_right, hx, hy, sub_zero]
    obtain ⟨g, hg⟩ := exists_mat_eq_spTrans (y - x) (spForm y x)⁻¹
    have h := graph_fun_transvection hs hw hg (hinv _ _ g hw hg) hx
    rw [spForm_sub_left, spForm_self, sub_zero, inv_mul_cancel₀ hyx, one_smul,
      add_sub_cancel] at h
    exact h.symm
  by_cases hxy : spForm x y = 0
  · obtain ⟨z, haz, hxz, hyz⟩ := exists_perp_spForm_ne_zero_both hxa hya
    exact (step hx haz hxz).trans
      (step haz hy (by rw [spForm_comm]; exact neg_ne_zero.2 hyz))
  · exact step hx hy hxy

end Graph

theorem no_invariant_complement_spRad_general {n : ℕ} (hn : 2 ≤ n) {F : Type} [Field F]
    [CharP F 2] [Finite F] (hF : 4 ≤ Nat.card F) {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0)
    {T S : Subgroup (StatedSp n F)} (hT : CaseM.IsTransGroup a T) (hS : S ≤ spRad a)
    (hsup : S ⊔ T = spRad a) (hinf : S ⊓ T = ⊥)
    (hinv : ∀ (w : Fin n ⊕ Fin n → F) (μ : F) (g : StatedSp n F), CaseM.spForm a w = 0 →
      SpExtras.mat n F g = spTrans w μ → ∀ x ∈ S, g * x * g⁻¹ ∈ S) : False := by
  obtain ⟨s, hs⟩ := exists_graph_fun ha hT hS hsup hinf
  obtain ⟨x₀, -, hax₀, hx₀a⟩ := exists_perp_vec_not_smul hn ha
  obtain ⟨u, hau, hxu⟩ := exists_perp_spForm_ne_zero hx₀a
  obtain ⟨l, hl0, hl1⟩ := CFSG.Timmesfeld.Bridge.Higman.exists_ne_zero_ne_one (K := F)
    (by omega)
  have hnot : ∀ y : Fin n ⊕ Fin n → F, spForm x₀ y ≠ 0 → ∀ c : F, y ≠ c • a := by
    intro y hy c hc
    apply hy
    rw [hc, spForm_smul_right', spForm_eq_zero_comm hax₀, mul_zero]
  have key : ∀ μ : F, μ ≠ 0 → μ * spForm x₀ u = -s x₀ := by
    intro μ hμ
    have hy : spForm a (μ • u) = 0 := by rw [spForm_smul_right', hau, mul_zero]
    have hxy : spForm x₀ (μ • u) = μ * spForm x₀ u := spForm_smul_right' μ x₀ u
    have hxy0 : spForm x₀ (μ • u) ≠ 0 := by rw [hxy]; exact mul_ne_zero hμ hxu
    have hxy' : spForm a (x₀ + μ • u) = 0 := by rw [spForm_add_right, hax₀, hy, add_zero]
    have hxy'0 : spForm x₀ (x₀ + μ • u) ≠ 0 := by
      rw [spForm_add_right, spForm_self, zero_add, hxy]
      exact mul_ne_zero hμ hxu
    have h1 := graph_fun_add hs hax₀ hy
    have h2 := graph_fun_const hs hinv hxy' hax₀ (hnot _ hxy'0) hx₀a
    have h3 := graph_fun_const hs hinv hy hax₀ (hnot _ hxy0) hx₀a
    rw [h2, h3, hxy] at h1
    linear_combination (-1 : F) * h1
  have e1 := key 1 one_ne_zero
  have el := key l hl0
  have hβ : (l - 1) * spForm x₀ u = 0 := by linear_combination el - e1
  rcases mul_eq_zero.1 hβ with h | h
  · exact hl1 (sub_eq_zero.1 h)
  · exact hxu h

theorem spNoInvCompGeneralStatement_holds :
    ∀ {n : ℕ}, 2 ≤ n → ∀ {F : Type} [Field F] [CharP F 2] [Finite F], 4 ≤ Nat.card F →
      ∀ {a : Fin n ⊕ Fin n → F}, a ≠ 0 →
      ∀ {T S : Subgroup (StatedSp n F)}, CaseM.IsTransGroup a T → S ≤ spRad a →
        S ⊔ T = spRad a → S ⊓ T = ⊥ →
        (∀ (w : Fin n ⊕ Fin n → F) (μ : F) (g : StatedSp n F), CaseM.spForm a w = 0 →
          SpExtras.mat n F g = CaseM.spTrans w μ → ∀ x ∈ S, g * x * g⁻¹ ∈ S) → False := by
  intro n hn F _ _ _ hF a ha T S hT hS hsup hinf hinv
  exact no_invariant_complement_spRad_general hn hF ha hT hS hsup hinf hinv

end CFSG.RankThree.GF2n.Tim79a

end
