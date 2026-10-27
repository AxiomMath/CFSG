module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

variable {M V₀ V N₁ N₂ Y : Subgroup G} {g : G}

private theorem c23ne_comm_of_conj_comm {a v z : G} (hav : a * v = v * a)
    (hy : (a * z * a⁻¹) * v = v * (a * z * a⁻¹)) : z * v = v * z := by
  have hv : a * v * a⁻¹ = v := by rw [hav]; group
  have h2 : a * (z * v) * a⁻¹ = a * (v * z) * a⁻¹ := by
    calc a * (z * v) * a⁻¹ = (a * z * a⁻¹) * (a * v * a⁻¹) := by group
      _ = (a * z * a⁻¹) * v := by rw [hv]
      _ = v * (a * z * a⁻¹) := hy
      _ = (a * v * a⁻¹) * (a * z * a⁻¹) := by rw [hv]
      _ = a * (v * z) * a⁻¹ := by group
  simpa using h2

private theorem c23ne_V₀_le_N₁' (h : C23NePair M V₀ V N₁ N₂ Y) : V₀ ≤ N₁ := by
  rw [← h.inf]; exact inf_le_left

theorem c23ne_U_normalizes (h : C23NeO2 M V₀ V N₁ N₂ Y g)
    (h0comm : ∀ u ∈ conjSubgroup V g ⊓ M, ∀ w ∈ V₀, u * w = w * u)
    (h1blk : conjSubgroup N₁ g ≤ M ∨ conjSubgroup N₂ g ≤ M) :
    ∀ a ∈ V ⊓ conjSubgroup M g, a ∈ normalizer (conjSubgroup N₁ g : Set G) ∧
      a ∈ normalizer (conjSubgroup N₂ g : Set G) := by
  intro a ha
  have haV : a ∈ V := (Subgroup.mem_inf.1 ha).1
  have haMg : a ∈ conjSubgroup M g := (Subgroup.mem_inf.1 ha).2
  rcases h.pair'.perm a haMg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨conjSubgroup_eq_iff_mem_normalizer.1 h1, conjSubgroup_eq_iff_mem_normalizer.1 h2⟩
  · exfalso
    have hV₀ne : V₀ ≠ ⊥ := by
      intro hbot
      have h2' := h.pair.rank_V₀
      rw [hbot] at h2'
      simp only [mSub] at h2'
      rw [rk_bot] at h2'
      omega
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV₀ne
    have hvV₀ : (v : G) ∈ V₀ := v.2
    have hv1' : (v : G) ≠ 1 := fun h' => hv1 (Subtype.ext h')
    have hV₀V : V₀ ≤ V := (c23ne_V₀_le_N₁' h.pair).trans h.pair.le₁
    have hav : a * (v : G) = (v : G) * a := h.pair.elem.comm haV (hV₀V hvV₀)
    have hbl : ∃ K K' : Subgroup G, K ≤ conjSubgroup V g ∧ K ≤ M ∧
        conjSubgroup V g = K ⊔ K' ∧ conjSubgroup K a = K' := by
      rcases h1blk with hK | hK
      · exact ⟨_, _, h.pair'.le₁, hK, h.pair'.sup.symm, h1⟩
      · exact ⟨_, _, h.pair'.le₂, hK, by rw [← h.pair'.sup, sup_comm], h2⟩
    obtain ⟨K, K', hKV, hKM, hsup, hconj⟩ := hbl
    have hK : ∀ y ∈ K, y * (v : G) = (v : G) * y := fun y hy =>
      h0comm y (Subgroup.mem_inf.2 ⟨hKV hy, hKM hy⟩) v hvV₀
    have hK' : ∀ z ∈ K', z * (v : G) = (v : G) * z := by
      intro z hz
      have hz' : a * z * a⁻¹ ∈ K := mem_conjSubgroup_iff.1 (hconj ▸ hz)
      exact c23ne_comm_of_conj_comm hav (hK _ hz')
    have hVg_le : conjSubgroup V g ≤ centralizer ({(v : G)} : Set G) := by
      rw [hsup]
      exact sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hK y hy))
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.2 (hK' z hz))
    exact h.notLe (hVg_le.trans
      (h.pair.cent (v : G) (Or.inl (c23ne_V₀_le_N₁' h.pair hvV₀)) hv1'))

theorem c23ne_U_centralizes_block (h : C23NeO2 M V₀ V N₁ N₂ Y g) {K : Subgroup G}
    (hK : K ≤ conjSubgroup V g) (hKM : K ≤ M) (hKbot : (V ⊓ conjSubgroup V g) ⊓ K = ⊥)
    (hnorm : ∀ a ∈ V ⊓ conjSubgroup M g, a ∈ normalizer (K : Set G)) :
    ∀ a ∈ V ⊓ conjSubgroup M g, ∀ y ∈ K, a * y = y * a := by
  intro a ha y hy
  have hcD : a * y * a⁻¹ * y⁻¹ ∈ V ⊓ conjSubgroup V g :=
    c23ne_comm_mem_inf h ha (Subgroup.mem_inf.2 ⟨hK hy, hKM hy⟩)
  have hcK : a * y * a⁻¹ * y⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hnorm a ha) y).1 hy) (K.inv_mem hy)
  have hmem : a * y * a⁻¹ * y⁻¹ ∈ (V ⊓ conjSubgroup V g) ⊓ K := Subgroup.mem_inf.2 ⟨hcD, hcK⟩
  rw [hKbot, Subgroup.mem_bot] at hmem
  have h1 : a * y * a⁻¹ = y := by
    have h2 : (a * y * a⁻¹ * y⁻¹) * y = 1 * y := by rw [hmem]
    simpa [mul_assoc] using h2
  calc a * y = a * y * a⁻¹ * a := by group
    _ = y * a := by rw [h1]

theorem c23ne_step2 (h : C23NeO2 M V₀ V N₁ N₂ Y g)
    (h0comm : ∀ u ∈ conjSubgroup V g ⊓ M, ∀ w ∈ V₀, u * w = w * u)
    (h1blk : conjSubgroup N₁ g ≤ M ∨ conjSubgroup N₂ g ≤ M) :
    E3.mQuot (V ⊓ conjSubgroup M g)
      (F11.CTilde (conjSubgroup M g) (conjSubgroup Y g) (conjSubgroup V g)) ≤ 2 := by
  have hn := c23ne_U_normalizes h h0comm h1blk
  have hbot := c23ne_inf_blocks_eq_bot h.pair' h.notLe' (A := V) (X := V ⊓ conjSubgroup V g)
    (fun x hx a ha => h.pair.elem.comm ha hx.1)
  have hUel : IsElemAbelian 2 (V ⊓ conjSubgroup M g) := h.pair.elem.mono inf_le_left
  rcases h1blk with h1 | h1
  · exact h.pair'.rankLe' (V ⊓ conjSubgroup M g) inf_le_right hUel (fun e he => (hn e he).2)
      (c23ne_U_centralizes_block h h.pair'.le₁ h1 hbot.1 (fun a ha => (hn a ha).1))
  · exact h.pair'.rankLe (V ⊓ conjSubgroup M g) inf_le_right hUel (fun e he => (hn e he).1)
      (c23ne_U_centralizes_block h h.pair'.le₂ h1 hbot.2 (fun a ha => (hn a ha).2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
