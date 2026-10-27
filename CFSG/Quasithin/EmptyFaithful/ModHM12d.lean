module

public import CFSG.Quasithin.EmptyFaithful.ModHM12c
public import CFSG.Quasithin.EmptyFaithful.ModHSolv

public section

namespace CFSG.Quasithin.ModH.R12

open CFSG.Quasithin.ModH.S12 CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.ModG (memB memB_iff ev ev_mem ev_append ev_invW ev_nil invW)
open CFSG.Quasithin
open scoped Pointwise
open MulAction

@[expose] def rho (k i : ℕ) : G := ev alph (rW.getD k [] ++ cW.getD i [])

theorem rho_eq (k i : ℕ) : rho k i = rE k * cE i := ev_append _ _ _

@[expose] def Lg (k i : ℕ) : List G := tg ++ [rho k i] ++ (tg.map fun x => x⁻¹) ++ [(rho k i)⁻¹]

theorem map_c_inv_evg {H : Type*} [Group H] (c : H → ℕ) (comp : ℕ → ℕ → ℕ) (kId : ℕ)
    (hmul : ∀ x y, c (x * y) = comp (c x) (c y)) (hone : c 1 = kId) (A : List H) (r : ℕ)
    (hA : ∀ l < r, A.getD (l + r) 1 = (A.getD l 1)⁻¹) (ws : List (List ℕ))
    (hw : ∀ w ∈ ws, ∀ l ∈ w, l < 2 * r) :
    ((ws.map (ev A)).map fun x => x⁻¹).map c = ws.map fun w => evcg comp kId (A.map c) (invW r w) := by
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro w hw'
  simp only [Function.comp]
  rw [← ev_invW hA w (hw w hw')]
  exact c_evg c comp kId hmul hone A _

theorem Lg_codes (k i : ℕ) : (Lg k i).map cd = Lcodes k i := by
  have hw : ∀ l ∈ rW.getD k [] ++ cW.getD i [], l < 2 * 2 := by
    intro l hl
    rcases List.mem_append.1 hl with h | h
    · have := rW_letters k l h; omega
    · have := cW_letters i l h; omega
  have h1 : (tg.map fun x => x⁻¹).map cd = gW.map fun v => evcg (compn 12) (kIdn 12) aC (invW 2 v) := by
    have := map_c_inv_evg cd (compn 12) (kIdn 12) cd_mul cd_one alph 2 alph_inv gW
      (fun w hw' l hl => by have := gW_letters w hw' l hl; omega)
    rw [alph_codes] at this
    exact this
  have h2 : cd ((rho k i)⁻¹) = evcg (compn 12) (kIdn 12) aC (invW 2 (rW.getD k [] ++ cW.getD i [])) := by
    rw [rho, ← ev_invW alph_inv _ hw]
    exact cd_ev_alph _
  have h3 : cd (rho k i) = evcg (compn 12) (kIdn 12) aC (rW.getD k [] ++ cW.getD i []) := cd_ev_alph _
  simp only [Lg, Lcodes, List.map_append, List.map_cons, List.map_nil, tg_codes, h1, h2, h3]

theorem pow_five_eq' {H : Type*} [Group H] (c : H) : c ^ 5 = (c * c) * (c * c) * c := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_succ, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]

theorem not_solvable_of_rep (k i : ℕ) (hk : k < 19) (hi : i < 3) (hn : ¬ (k = 18 ∨ (k = 17 ∧ i = 0)))
    (Z : Subgroup G) (hSZ : Sg ≤ Z) (hρ : rho k i ∈ Z) : ¬ Group.IsSolvable ↥Z := by
  rcases chk5 k hk i hi with h | h | ⟨e, he, hek, hei, hwit, hlet⟩
  · exact absurd (Or.inl h) hn
  · exact absurd (Or.inr h) hn
  intro hZ
  have hLmem : ∀ x ∈ Lg k i, x ∈ Z := by
    intro x hx
    simp only [Lg, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hx
    rcases hx with ((hx | hx) | ⟨y, hy, rfl⟩) | hx
    · exact hSZ (Subgroup.subset_closure hx)
    · rw [hx]; exact hρ
    · exact Z.inv_mem (hSZ (Subgroup.subset_closure hy))
    · rw [hx]; exact Z.inv_mem hρ
  have hlen : (Lg k i).length = 8 := by simp [Lg, tg, gW]
  have hcodes := Lg_codes k i
  set a : G := ev (Lg k i) e.2.2.1 with ha
  set b : G := ev (Lg k i) e.2.2.2 with hb
  have hca : cd a = evcg (compn 12) (kIdn 12) (Lcodes k i) e.2.2.1 := by
    rw [ha, c_evg cd (compn 12) (kIdn 12) cd_mul cd_one, hcodes]
  have hcb : cd b = evcg (compn 12) (kIdn 12) (Lcodes k i) e.2.2.2 := by
    rw [hb, c_evg cd (compn 12) (kIdn 12) cd_mul cd_one, hcodes]
  simp only [witChk, Bool.and_eq_true, Bool.not_eq_true'] at hwit
  rw [← hca, ← hcb] at hwit
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hwit
  have e1 : a * a = 1 := cd_injective (by rw [cd_mul, cd_one]; exact Nat.eq_of_beq_eq_true h1)
  have e2 : b * b * b = 1 := cd_injective (by rw [cd_mul, cd_mul, cd_one]; exact Nat.eq_of_beq_eq_true h2)
  have e3 : (a * b) * (a * b) * ((a * b) * (a * b)) * (a * b) = 1 :=
    cd_injective (by simp only [cd_mul, cd_one]; exact Nat.eq_of_beq_eq_true h3)
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact e1
  have hb3 : b ^ 3 = 1 := by rw [pow_three']; exact e2
  have hab : (a * b) ^ 5 = 1 := by rw [pow_five_eq']; exact e3
  have hb1 : b ≠ 1 := by
    intro h
    have : cd b = kIdn 12 := by rw [h, cd_one]
    rw [this, Nat.beq_refl] at h4
    exact Bool.noConfusion h4
  have hnot := ModG.not_solvable_of_235 ha2 hb3 hab hb1
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Z := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ev_mem hLmem _
    · exact ev_mem hLmem _
  have : Group.IsSolvable ↥Z := hZ
  exact hnot (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle))

@[expose] def tt : G := ev alph (gW.getD 2 [])

theorem Z_cover (Z : Subgroup G) (hSZ : Sg ≤ Z)
    (hZ : Group.IsSolvable ↥Z) :
    ∀ z ∈ Z, z ∈ K ∨ (∃ s ∈ Sg, z = rE 17 * s) ∨ (∃ s ∈ Sg, z = tt * rE 17 * s) := by
  intro z hz
  obtain ⟨σ, hσ, k, hk, i, hi, τ, hτ, rfl⟩ := cover z
  have hρZ : rho k i ∈ Z := by
    rw [rho_eq]
    have : rE k * cE i = σ⁻¹ * (σ * (rE k * cE i) * τ) * τ⁻¹ := by group
    rw [this]
    exact Z.mul_mem (Z.mul_mem (Z.inv_mem (hSZ hσ)) hz) (Z.inv_mem (hSZ hτ))
  by_cases hn : k = 18 ∨ (k = 17 ∧ i = 0)
  · rcases hn with rfl | ⟨rfl, rfl⟩
    · left
      have h18 : rE 18 = 1 := by
        have : rW.getD 18 [] = [] := by decide +kernel
        rw [rE, this, ev_nil]
      rw [h18, one_mul]
      exact K.mul_mem (K.mul_mem (Sg_le_K hσ) (cE_mem_K i hi)) (Sg_le_K hτ)
    · right
      rw [cE_zero, mul_one]
      have hs : cd σ ∈ tK := (mem_Sg_iff σ).1 hσ
      obtain ⟨w, hw, hmem⟩ := chk6 (cd σ) hs
      have hlet : ∀ l ∈ w, l < 2 * 2 := by
        simp only [trA, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · intro l hl; exact absurd hl (by simp)
        · intro l hl
          have := gW_letters _ (by decide +kernel : gW.getD 2 [] ∈ gW) l hl
          omega
      have hρ : cd (rE 17) = rC.getD 17 0 := (rC_getD 17 (by norm_num)).symm
      have hρi : cd (rE 17)⁻¹ = evcg (compn 12) (kIdn 12) aC (invW 2 (rW.getD 17 [])) := by
        rw [rE, ← ev_invW alph_inv _ (fun l hl => by have := rW_letters 17 l hl; omega)]
        exact cd_ev_alph _
      have htw : cd (ev alph w)⁻¹ = evcg (compn 12) (kIdn 12) aC (invW 2 w) := by
        rw [← ev_invW alph_inv _ hlet]
        exact cd_ev_alph _
      have hS' : (rE 17)⁻¹ * ((ev alph w)⁻¹ * (σ * rE 17)) ∈ Sg := by
        rw [mem_Sg_iff, cd_mul, cd_mul, cd_mul, hρ, hρi, htw]
        exact memB_iff.1 hmem
      simp only [trA, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · left
        refine ⟨_ * τ, Sg.mul_mem (by simpa [ev_nil] using hS') hτ, ?_⟩
        simp only [ev_nil, inv_one, one_mul] at hS'
        group
      · right
        refine ⟨_ * τ, Sg.mul_mem hS' hτ, ?_⟩
        rw [tt]
        group
  · exact absurd hρZ (fun h => not_solvable_of_rep k i hk hi hn Z hSZ h hZ)

theorem card_Z_le (Z : Subgroup G) (hSZ : Sg ≤ Z)
    (hZ : Group.IsSolvable ↥Z) : Nat.card Z ≤ 320 := by
  have hsub : (Z : Set G) ⊆ ((K : Set G) ∪ ((fun s => rE 17 * s) '' (Sg : Set G))) ∪
      ((fun s => tt * rE 17 * s) '' (Sg : Set G)) := by
    intro z hz
    rcases Z_cover Z hSZ hZ z hz with h | ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨s, hs, rfl⟩)
    · exact Or.inr ⟨s, hs, rfl⟩
  have hKc : (K : Set G).ncard = 192 := by
    rw [← Nat.card_coe_set_eq]
    exact card_K
  have hSc : (Sg : Set G).ncard = 64 := by
    rw [← Nat.card_coe_set_eq]
    exact card_Sg
  calc Nat.card Z = (Z : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ (((K : Set G) ∪ ((fun s => rE 17 * s) '' (Sg : Set G))) ∪
        ((fun s => tt * rE 17 * s) '' (Sg : Set G))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((K : Set G) ∪ ((fun s => rE 17 * s) '' (Sg : Set G))).ncard +
        ((fun s => tt * rE 17 * s) '' (Sg : Set G)).ncard := Set.ncard_union_le _ _
    _ ≤ ((K : Set G).ncard + ((fun s => rE 17 * s) '' (Sg : Set G)).ncard) +
        ((fun s => tt * rE 17 * s) '' (Sg : Set G)).ncard := by
      gcongr
      exact Set.ncard_union_le _ _
    _ ≤ (192 + 64) + 64 := by
      have h1 := Set.ncard_image_le (f := fun s => rE 17 * s) (Set.toFinite (Sg : Set G))
      have h2 := Set.ncard_image_le (f := fun s => tt * rE 17 * s) (Set.toFinite (Sg : Set G))
      rw [hSc] at h1 h2
      omega
    _ = 320 := by norm_num

theorem solvNine_M12 : SolvNine G := by
  refine solvNine_of_sylow Sg_sylow ?_
  intro Y hN hs h9
  have hZs := isSolvable_sup_of_le_normalizer hs Sg_isPGroup hN
  have hSZ : Sg ≤ Y ⊔ Sg := le_sup_right
  have h64 : 64 ∣ Nat.card ↥(Y ⊔ Sg) := by
    have := Subgroup.card_dvd_of_le hSZ
    rwa [card_Sg] at this
  have h9Z : 9 ∣ Nat.card ↥(Y ⊔ Sg) := h9.trans (Subgroup.card_dvd_of_le le_sup_left)
  have h576 : 64 * 9 ∣ Nat.card ↥(Y ⊔ Sg) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h64 h9Z
  have hpos : 0 < Nat.card ↥(Y ⊔ Sg) := Nat.card_pos
  have h1 := card_Z_le _ hSZ hZs
  have h2 := Nat.le_of_dvd hpos h576
  omega

end CFSG.Quasithin.ModH.R12
