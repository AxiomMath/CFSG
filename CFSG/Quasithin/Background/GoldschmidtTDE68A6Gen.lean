module

public import CFSG.Quasithin.Background.GoldschmidtTDE68A6Fix

public section

namespace CFSG.Quasithin.E6.Alt.A6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Unc25A6 CFSG.Quasithin.E6.Bar

theorem isSimpleGroup_X0 : IsSimpleGroup X0 := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact ψ.isSimpleGroup

theorem card_X0 : Nat.card X0 = 360 := card_psl29

theorem gen_six : ⨆ β ∈ InvSet Dsub, fixedSub β = ⊤ := by
  obtain ⟨c₁, hc₁, c₂, hc₂, h24₁, h24₂, x, hx2, hx1⟩ := invCentD_gen
  obtain ⟨a₁, ha₁, rfl⟩ := exists_aut_of_code (List.mem_filter.1 hc₁).1
  obtain ⟨a₂, ha₂, rfl⟩ := exists_aut_of_code (List.mem_filter.1 hc₂).1
  set M : Subgroup X0 := ⨆ β ∈ InvSet Dsub, fixedSub β with hM
  have hβ₁ : conjAut ⟨a₁, ha₁⟩ ∈ InvSet Dsub := (mem_invSet_iff _).2 ⟨_, rfl, hc₁⟩
  have hβ₂ : conjAut ⟨a₂, ha₂⟩ ∈ InvSet Dsub := (mem_invSet_iff _).2 ⟨_, rfl, hc₂⟩
  have hF₁ : fixedSub (conjAut ⟨a₁, ha₁⟩) ≤ M := le_iSup₂_of_le _ hβ₁ le_rfl
  have hF₂ : fixedSub (conjAut ⟨a₂, ha₂⟩) ≤ M := le_iSup₂_of_le _ hβ₂ le_rfl
  have hcard₁ : Nat.card ↥(fixedSub (conjAut ⟨a₁, ha₁⟩)) = 24 := by
    rw [card_fixedSub]
    exact h24₁
  have hcard₂ : Nat.card ↥(fixedSub (conjAut ⟨a₂, ha₂⟩)) = 24 := by
    rw [card_fixedSub]
    exact h24₂
  by_contra hne
  have hsimple := isSimpleGroup_X0
  have hcore : M.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ M.normalCore_le)) hne
  have h1 := M.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot, card_X0] at h1
  have hmul := M.card_mul_index
  rw [card_X0] at hmul
  have h24 : 24 ∣ Nat.card M := hcard₁ ▸ Subgroup.card_dvd_of_le hF₁
  have hidx : M.index ∣ 15 := by
    obtain ⟨k, hk⟩ := h24
    rw [hk] at hmul
    exact ⟨k, by linarith⟩
  have hdiv : M.index ∈ Nat.divisors 15 := Nat.mem_divisors.2 ⟨hidx, by norm_num⟩
  have h15 : Nat.divisors 15 = {1, 3, 5, 15} := by decide
  rw [h15] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  rcases hdiv with h | h | h | h
  · exact hne (Subgroup.index_eq_one.1 h)
  · rw [h] at h1
    exact absurd h1 (by decide)
  · rw [h] at h1
    exact absurd h1 (by decide)
  · rw [h] at hmul
    have hM24 : Nat.card M = 24 := by omega
    have e1 : fixedSub (conjAut ⟨a₁, ha₁⟩) = M :=
      Subgroup.eq_of_le_of_card_ge hF₁ (by rw [hM24, hcard₁])
    have e2 : fixedSub (conjAut ⟨a₂, ha₂⟩) = M :=
      Subgroup.eq_of_le_of_card_ge hF₂ (by rw [hM24, hcard₂])
    have hxpsl : x ∈ Core.pslLit := (List.mem_filter.1 hx2).1
    obtain ⟨y, hy⟩ := exists_X0_of_code hxpsl
    have hy2 : y ∈ fixedSub (conjAut ⟨a₂, ha₂⟩) := (mem_fixedSub_iff_code _ y).2 (hy ▸ hx2)
    have hy1 : y ∉ fixedSub (conjAut ⟨a₁, ha₁⟩) := fun h' =>
      hx1 (hy ▸ (mem_fixedSub_iff_code _ y).1 h')
    exact hy1 (e1.symm ▸ e2 ▸ hy2)

end CFSG.Quasithin.E6.Alt.A6
