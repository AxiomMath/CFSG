module

public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Defs

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits Module

private theorem eq_one_of_ne_zero_of_card_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {a : F} (ha : a ≠ 0) : a = 1 := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card a
  rw [← Nat.card_eq_fintype_card, hF] at h
  have h2 : a * (a - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 ha
  · exact sub_eq_zero.mp h3

section Card

variable {F : Type} [Field F]

local notation "ρ" => natRep (StatedSL 5 F)

theorem card_le_sixteen_of_finrank_four [Finite F] (hF : Nat.card F = 2)
    {U : Subgroup ↥(StatedSL 5 F)} (h1 : finrank F ↥(fixFlag ρ U 1) = 4) :
    Nat.card ↥U ≤ 16 := by
  classical
  have hfixU : ∀ u ∈ U, ∀ w ∈ fixFlag ρ U 1, ρ u w = w := by
    intro u hu w hw
    have h := (mem_fixFlag_succ ρ (k := 0)).1 hw u hu
    rw [fixFlag_zero, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  have hinv : ∀ u ∈ U, ∀ w ∈ fixFlag ρ U 1, ρ u⁻¹ w = w := fun u hu =>
    hfixU u⁻¹ (U.inv_mem hu)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ ∉ fixFlag ρ U 1 := by
    by_contra h
    push Not at h
    have htop : fixFlag ρ U 1 = ⊤ := eq_top_iff.2 fun v _ => h v
    have := congrArg (fun W : Submodule F (Fin 5 → F) => finrank F ↥W) htop
    simp only [h1, finrank_top, finrank_v5] at this
    omega
  have hsup : fixFlag ρ U 1 ⊔ F ∙ v₀ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hlt : fixFlag ρ U 1 < fixFlag ρ U 1 ⊔ F ∙ v₀ := lt_of_le_of_ne le_sup_left fun h =>
      hv₀ (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v₀))
    have h3 := Submodule.finrank_lt_finrank_of_lt hlt
    have h4 := finrank_le_five (fixFlag ρ U 1 ⊔ F ∙ v₀)
    rw [finrank_v5]
    omega
  have hmem : ∀ u ∈ U, ρ u v₀ - v₀ ∈ fixFlag ρ U 1 := by
    intro u hu
    have hv : ρ u v₀ ∈ fixFlag ρ U 1 ⊔ F ∙ v₀ := hsup ▸ Submodule.mem_top
    obtain ⟨c, hc, y, hy, hcy⟩ := Submodule.mem_sup.1 hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have ha : a ≠ 0 := by
      intro ha
      rw [ha, zero_smul, add_zero] at hcy
      apply hv₀
      have key : ρ u⁻¹ (ρ u v₀) = v₀ := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [← key, ← hcy, hinv u hu c hc]
      exact hc
    rw [eq_one_of_ne_zero_of_card_two hF ha, one_smul] at hcy
    rw [← hcy]
    simpa using hc
  let f : ↥U → ↥(fixFlag ρ U 1) := fun u => ⟨ρ u v₀ - v₀, hmem u u.2⟩
  have hf : Function.Injective f := by
    intro u u' huu'
    have h0 : ρ u v₀ = ρ u' v₀ := by
      have := congrArg Subtype.val huu'
      simpa [f] using this
    apply Subtype.ext
    apply natRep_injective (StatedSL 5 F)
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ fixFlag ρ U 1 ⊔ F ∙ v₀ := hsup ▸ Submodule.mem_top
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [map_add, map_add, map_smul, map_smul, hfixU u u.2 w hw, hfixU u' u'.2 w hw, h0]
  have hcard := Nat.card_le_card_of_injective f hf
  rw [card_eq_two_pow hF, h1] at hcard
  exact hcard.trans (by norm_num)

end Card

private theorem eq_sixteen_of_pow_two {m n : ℕ} (hm : m = 2 ^ n) (hmod : m ≡ 1 [MOD 5])
    (h4 : 4 ≤ m) (h16 : m ≤ 16) : m = 16 := by
  unfold Nat.ModEq at hmod
  have hn : n < 5 := by
    by_contra h
    push Not at h
    have h32 : 32 ≤ 2 ^ n :=
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases n <;> norm_num at hm <;> omega

theorem leafCardPCore_of (h2 : LeafFive) (h3 : LeafTwoElt) : LeafCardPCore := by
  intro F _ _ hF B _hB hiso
  set U := pCoreOf 2 B
  have hU2 : IsPGroup 2 ↥U := pCoreOf_isPGroup 2 B
  have hBU : B ≤ Subgroup.normalizer (U : Set ↥(StatedSL 5 F)) := le_normalizer_pCoreOf 2 B
  obtain ⟨x, hxB, hx5⟩ := h2 _ B hiso
  have hxU : x ∈ Subgroup.normalizer (U : Set ↥(StatedSL 5 F)) := hBU hxB
  have hcU : ∀ u ∈ U, u * x = x * u → u = 1 := by
    intro u hu hcomm
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    exact h3 F hF x u hx5 ⟨k, congrArg Subtype.val hk⟩ hcomm.symm
  have hmod : Nat.card ↥U ≡ 1 [MOD 5] := card_modEq_one hx5 hxU hcU
  obtain ⟨n, hn⟩ := hU2.exists_card_eq
  by_cases h1 : Nat.card ↥U = 1
  · exact Or.inl h1
  right
  have h4 : 4 ≤ Nat.card ↥U := by
    unfold Nat.ModEq at hmod
    by_contra hlt
    push Not at hlt
    have hn2 : n < 2 := by
      by_contra hn2
      push Not at hn2
      have h4n : 4 ≤ 2 ^ n :=
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    interval_cases n <;> simp only [pow_zero, pow_one] at hn <;> omega
  rcases finrank_fix_cases_theta hF hx5 hU2 hxU h4 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  ·
    have hle : Nat.card ↥(U.map theta.toMonoidHom) ≤ 16 :=
      card_le_sixteen_of_finrank_four hF h2'
    have hθ : Nat.card ↥(U.map theta.toMonoidHom) = Nat.card ↥U :=
      Subgroup.card_map_of_injective (f := theta.toMonoidHom) theta.injective
    have hle' : Nat.card ↥U ≤ 16 := by
      rw [← hθ]
      exact hle
    exact ⟨eq_sixteen_of_pow_two hn hmod h4 hle', by omega⟩
  ·
    have hle : Nat.card ↥U ≤ 16 := card_le_sixteen_of_finrank_four hF h1'
    exact ⟨eq_sixteen_of_pow_two hn hmod h4 hle, by omega⟩

end CFSG.Quasithin.H13.KG12617L52
