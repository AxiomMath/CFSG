module

public import CFSG.LocalAnalysis.StandardType.GGXInLQuot

public section

namespace CFSG.StandardType.GGXInL

theorem lup8f_f2_exists_lift {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {L E N : Subgroup H} [N.Normal] (hNL : N ≤ L) (hNp : Nat.Coprime p (Nat.card N))
    (hEp : IsPGroup p E) {x l : H} (hxE : x ∈ E) (hlL : l ∈ L)
    (hl : ∀ e ∈ E, QuotientGroup.mk' N (e * l * e⁻¹ * l⁻¹) ∈
      Subgroup.zpowers (QuotientGroup.mk' N x)) :
    ∃ a ∈ L ⊓ Subgroup.normalizer (E : Set H), QuotientGroup.mk' N a = QuotientGroup.mk' N l ∧
      ∀ e ∈ E, e * a * e⁻¹ * a⁻¹ ∈ Subgroup.zpowers x := by
  classical
  have hxπ : Subgroup.zpowers (QuotientGroup.mk' N x) ≤ E.map (QuotientGroup.mk' N) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hxE)
  have hconj : ∀ y ∈ E.map (QuotientGroup.mk' N), QuotientGroup.mk' N l * y *
      (QuotientGroup.mk' N l)⁻¹ ∈ E.map (QuotientGroup.mk' N) := by
    rintro _ ⟨e, he, rfl⟩
    have h := hxπ (hl e⁻¹ (E.inv_mem he))
    have h' : QuotientGroup.mk' N l * QuotientGroup.mk' N e * (QuotientGroup.mk' N l)⁻¹ =
        QuotientGroup.mk' N e * QuotientGroup.mk' N (e⁻¹ * l * e⁻¹⁻¹ * l⁻¹) := by
      simp only [map_mul, map_inv]
      group
    rw [h']
    exact (E.map (QuotientGroup.mk' N)).mul_mem (Subgroup.mem_map_of_mem _ he) h
  have hnorm : QuotientGroup.mk' N l ∈ Subgroup.normalizer
      ((E.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      exact hconj y hy
    · exact (Subgroup.card_map_of_injective (MulAut.conj _).injective).ge
  have hlift : QuotientGroup.mk' N l ∈
      (L ⊓ Subgroup.normalizer (E : Set H)).map (QuotientGroup.mk' N) :=
    lup8c_mem_map_inf_normalizer L E N hNL hNp hEp hlL hnorm
  obtain ⟨a, ⟨haL, haN⟩, hal⟩ := Subgroup.mem_map.mp hlift
  refine ⟨a, ⟨haL, haN⟩, hal, fun e he => ?_⟩
  have hbot : E ⊓ N = ⊥ := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hEp
    exact Subgroup.inf_eq_bot_of_coprime (by rw [hm]; exact hNp.pow_left m)
  have hd : e * a * e⁻¹ * a⁻¹ ∈ E := by
    have h := E.mul_mem he ((Subgroup.mem_normalizer_iff.mp haN e⁻¹).mp (E.inv_mem he))
    simpa [mul_assoc] using h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hl e he)
  have hk' : QuotientGroup.mk' N (e * a * e⁻¹ * a⁻¹) = QuotientGroup.mk' N (x ^ k) := by
    rw [map_zpow, hk]
    simp only [map_mul, map_inv, hal]
  have hmem : (x ^ k)⁻¹ * (e * a * e⁻¹ * a⁻¹) ∈ E ⊓ N := by
    refine Subgroup.mem_inf.mpr ⟨E.mul_mem (E.inv_mem (E.zpow_mem hxE k)) hd, ?_⟩
    have h1 : QuotientGroup.mk' N ((x ^ k)⁻¹ * (e * a * e⁻¹ * a⁻¹)) = 1 := by
      rw [map_mul, map_inv, hk', inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h1
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  rw [← hmem]
  exact Subgroup.zpow_mem_zpowers x k

end CFSG.StandardType.GGXInL

end
