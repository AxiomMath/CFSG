module

public import CFSG.Quasithin.Background.F918Z8Op0

public section

namespace CFSG.Quasithin

theorem opq4b_exists_inverts_of_index {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {T : Subgroup H} {w : H} (hw : w * w = 1) (hwT : ∀ t ∈ T, w * t * w⁻¹ = t⁻¹)
    (hT : ¬ p ∣ T.index) {P : Subgroup H} (hP : IsPGroup p P)
    (hm : ∃ m : ℕ, Nat.card H = Nat.card P * m ∧ ¬ p ∣ m) :
    ∃ τ : H, τ * τ = 1 ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹ := by
  obtain ⟨m, hcard, hpm⟩ := hm
  have hPidx : P.index = m := by
    have h1 := P.card_mul_index
    rw [hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  obtain ⟨S, hS⟩ : ∃ S : Sylow p H, (S : Subgroup H) = P :=
    ⟨hP.toSylow (by rw [hPidx]; exact hpm), IsPGroup.toSylow_coe _ _⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p T) := inferInstance
  have hQ : IsPGroup p ((Q : Subgroup T).map T.subtype) := Q.isPGroup'.map _
  have hidx : ¬ p ∣ ((Q : Subgroup T).map T.subtype).index := by
    rw [Subgroup.index_map_subtype, (Fact.out : p.Prime).dvd_mul, not_or]
    exact ⟨Q.not_dvd_index, hT⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S (hQ.toSylow hidx)
  refine ⟨g⁻¹ * w * g, ?_, fun x hx => ?_⟩
  · calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
      _ = 1 := by rw [hw]; group
  · have hmem : g * x * g⁻¹ ∈ ((hQ.toSylow hidx : Sylow p H) : Subgroup H) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (S : Subgroup H) (hS ▸ hx)
    rw [IsPGroup.toSylow_coe] at hmem
    obtain ⟨t, -, ht⟩ := hmem
    have htT : g * x * g⁻¹ ∈ T := by rw [← ht]; exact t.2
    calc g⁻¹ * w * g * x * (g⁻¹ * w * g)⁻¹ = g⁻¹ * (w * (g * x * g⁻¹) * w⁻¹) * g := by group
      _ = x⁻¹ := by rw [hwT _ htT]; group

theorem opq4b_invSylAll_of_equiv {G : Type*} [Group G] {L : Subgroup G} {H : Type*} [Group H]
    (e : ↥L ≃* H) {p : ℕ}
    (h : ∀ P : Subgroup H, IsPGroup p P → (∃ m : ℕ, Nat.card H = Nat.card P * m ∧ ¬ p ∣ m) →
      ∃ τ : H, τ * τ = 1 ∧ ∀ x ∈ P, τ * x * τ⁻¹ = x⁻¹) : InvSylAll L p := by
  intro P hPL hPp ⟨m, hm, hpm⟩
  have hPp' : IsPGroup p ((P.subgroupOf L).map e.toMonoidHom) := hPp.comap_subtype.map _
  have hcardP : Nat.card ((P.subgroupOf L).map e.toMonoidHom) = Nat.card P := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  obtain ⟨τ, hτ2, hτ⟩ := h _ hPp'
    ⟨m, by rw [hcardP, ← Nat.card_congr e.toEquiv, hm], hpm⟩
  refine ⟨(e.symm τ : G), (e.symm τ).2, ?_, fun x hx => ?_⟩
  · have := congrArg (fun a => (e.symm a : G)) hτ2
    simpa using this
  · have hxm : e ⟨x, hPL hx⟩ ∈ (P.subgroupOf L).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    have := congrArg (fun a => (e.symm a : G)) (hτ _ hxm)
    simpa using this

end CFSG.Quasithin
