module

public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F6Solvable

public section

namespace CFSG.Quasithin.H13.L32A.T53

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {D : Type*} [Group D] [Finite D]

theorem goldschmidt_map_mk {G₁ G₂ N : Subgroup D} [N.Normal] (h : IsGoldschmidtTriple G₁ G₂)
    (h₁ : IsPGroup 2 ↥(G₁ ⊓ N)) (h₂ : IsPGroup 2 ↥(G₂ ⊓ N)) (hne : ¬ G₁ ≤ G₂ ⊔ N) :
    IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' N)) (G₂.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hT : G₁ ⊓ N ≤ G₁ ⊓ G₂ := by
    have hle : G₁ ⊓ N ≤ pCoreOf 2 G₁ := by
      have hn : (G₁ ⊓ N).subgroupOf G₁ ≤ Open.pCore 2 ↥G₁ := by
        rw [Subgroup.inf_subgroupOf_left]
        refine le_pCore 2 ((inferInstance : N.Normal).subgroupOf G₁) ?_
        rw [← Subgroup.inf_subgroupOf_left]
        exact h₁.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
      intro x hx
      exact ⟨⟨x, hx.1⟩, hn (show (⟨x, hx.1⟩ : ↥G₁) ∈ (G₁ ⊓ N).subgroupOf G₁ from hx), rfl⟩
    exact hle.trans (F6.pCoreOf_le_inf_left h)
  have hTN : (G₁ ⊓ G₂) ⊓ N = G₁ ⊓ N :=
    le_antisymm (inf_le_inf_right _ inf_le_left) (le_inf hT inf_le_right)
  have hc₁ : Nat.card ↥(G₁.map π) = 3 * Nat.card ↥((G₁ ⊓ G₂).map π) := by
    rw [F6.card_map_mk, F6.card_map_mk]
    have e1 := Subgroup.relIndex_mul_card (H := N) (K := G₁)
    have e2 := Subgroup.relIndex_mul_card (H := N) (K := G₁ ⊓ G₂)
    have e3 := Subgroup.relIndex_mul_card (H := G₁ ⊓ G₂) (K := G₁)
    rw [h.relIndex_inf_left, inf_eq_left.mpr inf_le_left] at e3
    rw [inf_comm N G₁] at e1
    rw [inf_comm N (G₁ ⊓ G₂), hTN] at e2
    have hpos : 0 < Nat.card ↥(G₁ ⊓ N) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [e1, mul_assoc, e2, e3]
  have hTle : (G₁ ⊓ G₂).map π ≤ G₁.map π ⊓ G₂.map π := Subgroup.map_inf_le _ _ _
  have hT0 : 0 < Nat.card ↥((G₁ ⊓ G₂).map π) := Nat.card_pos
  have hidx : ((G₁ ⊓ G₂).map π).relIndex (G₁.map π) = 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := (G₁ ⊓ G₂).map π) (K := G₁.map π)
    rw [inf_eq_left.mpr (hTle.trans inf_le_left), hc₁] at h1
    exact Nat.eq_of_mul_eq_mul_right hT0 h1
  have hsplit := Subgroup.relIndex_mul_relIndex ((G₁ ⊓ G₂).map π) (G₁.map π ⊓ G₂.map π)
    (G₁.map π) hTle inf_le_left
  rw [hidx] at hsplit
  have hcase : G₁.map π ⊓ G₂.map π = (G₁ ⊓ G₂).map π := by
    have h3 : ((G₁ ⊓ G₂).map π).relIndex (G₁.map π ⊓ G₂.map π) = 1 ∨
        (G₁.map π ⊓ G₂.map π).relIndex (G₁.map π) = 1 := by
      have hp3 : Nat.Prime 3 := Nat.prime_three
      rcases (Nat.dvd_prime hp3).mp (Dvd.intro _ hsplit) with h | h
      · exact Or.inl h
      · right
        rw [h] at hsplit
        omega
    rcases h3 with h3 | h3
    · exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) hTle
    · exfalso
      apply hne
      have h4 : G₁.map π ≤ G₂.map π := (Subgroup.relIndex_eq_one.mp h3).trans inf_le_right
      intro x hx
      have h5 : π x ∈ G₂.map π := h4 ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := h5
      have h6 : y⁻¹ * x ∈ N := by
        rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hyx,
          inv_mul_cancel]
      have := Subgroup.mul_mem_sup hy h6
      rwa [mul_inv_cancel_left] at this
  refine ⟨?_, F6.isoS3_map_mk h₁ h.quotient₁.some, F6.isoS3_map_mk h₂ h.quotient₂.some, ?_⟩
  · rw [← Subgroup.map_sup, h.gen, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hπs
  · obtain ⟨S, hS⟩ := h.sylow
    refine ⟨S.mapSurjective hπs, ?_⟩
    rw [Sylow.coe_mapSurjective, hS, hcase]

omit [Finite D] in
theorem twoResidual_le_of_pow_mem {K M : Subgroup D} (hMK : M ≤ K)
    (hKM : K ≤ Subgroup.normalizer (M : Set D)) (hpow : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ M) :
    twoResidual K ≤ M :=
  iInf₂_le M ⟨hMK, hKM, hpow⟩

theorem le_centralizer_opResidual {A : Subgroup D} (hO2 : Open.pCore 2 D = ⊥)
    (hA : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ a ∈ Open.pCore p D, ∀ x ∈ A, x * a = a * x) :
    A ≤ Subgroup.centralizer (opResidual 3 (genFittingFitting D) : Set D) := by
  have hFn : (genFittingFitting D).Normal := CFSG.fittingSubgroup_normal
  have hFnil : Group.IsNilpotent ↥(genFittingFitting D) := CFSG.fittingSubgroup_nilpotent
  set F := genFittingFitting D with hFdef
  have hFp : ∀ (p : ℕ) [Fact p.Prime], ∀ a ∈ F, (∃ e : ℕ, a ^ p ^ e = 1) → a ∈ Open.pCore p D := by
    intro p _ a ha ⟨e, he⟩
    have h1 : a ∈ pCoreOf p F := F6.mem_pCoreOf_of_isNilpotent ha he
    have h2 : pCoreOf p F ≤ Open.pCore p D := by
      refine le_pCore p ?_ (pCoreOf_isPGroup p F)
      rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff]
      exact (Subgroup.normalizer_eq_top_iff.mpr hFn).ge.trans
        (normalizer_le_normalizer_pCoreOf p F)
    exact h2 h1
  have key : ∀ n : ℕ, ∀ f ∈ F, orderOf f = n → (orderOf f).Coprime 3 → ∀ x ∈ A,
      x * f = f * x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn hc x hx
      by_cases h1 : orderOf f = 1
      · rw [orderOf_eq_one_iff.mp h1, mul_one, one_mul]
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab, -, ha, hb, haz, hbz⟩ := F6.exists_mul_eq_pPart hp f
      have haF : a ∈ F := (Subgroup.zpowers_le.mpr hf) haz
      have hbF : b ∈ F := (Subgroup.zpowers_le.mpr hf) hbz
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact absurd (Nat.Coprime.coprime_dvd_left hpd hc) (by norm_num)
      have hxa : x * a = a * x := by
        have haO := hFp p a haF ha
        by_cases h2 : p = 2
        · subst h2
          rw [hO2, Subgroup.mem_bot] at haO
          rw [haO, mul_one, one_mul]
        · have h4 : p ≠ 4 := by
            rintro rfl
            norm_num at hp
          have h5 : 5 ≤ p := by
            have := hp.two_le
            omega
          exact hA p hp h5 a haO x hx
      have hbo : orderOf b ∣ orderOf f := orderOf_dvd_of_mem_zpowers hbz
      have hblt : orderOf b < n := by
        rw [← hn]
        refine lt_of_le_of_ne (Nat.le_of_dvd (orderOf_pos f) hbo) fun heq => ?_
        rw [heq] at hb
        exact absurd (Nat.Coprime.coprime_dvd_left hpd hb) (by simp [hp.one_lt.ne'])
      have hxb : x * b = b * x :=
        ih _ hblt b hbF rfl (Nat.Coprime.coprime_dvd_left hbo hc) x hx
      rw [← hab]
      calc x * (a * b) = (x * a) * b := by group
        _ = a * (x * b) := by rw [hxa]; group
        _ = a * b * x := by rw [hxb]; group
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hle : opResidual 3 F ≤ Subgroup.centralizer ({x} : Set D) := by
    rw [opResidual, Subgroup.closure_le]
    rintro g ⟨hgF, hgc⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (key _ g hgF rfl hgc x hx).symm
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hf)
  exact this

end CFSG.Quasithin.H13.L32A.T53

end
