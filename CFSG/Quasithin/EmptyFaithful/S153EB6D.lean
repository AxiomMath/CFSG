module

public import CFSG.Quasithin.Background.G64ProofBasic

public section

namespace CFSG.Quasithin

namespace S153EB6

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

section Restrict

variable {W : Type} [CommGroup W]

theorem le_stabSub_of_inv {X : Subgroup (MulAut W)} {U : Subgroup W}
    (hU : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) : X ≤ stabSub U := by
  intro g hg u
  refine ⟨fun hu => ?_, fun hu => hU g hg u hu⟩
  have := hU g⁻¹ (X.inv_mem hg) (g u) hu
  simpa using this

theorem mem_stabSub_of_sq {U : Subgroup W} {a : MulAut W} (ha2 : a ^ 2 = 1)
    (haU : ∀ u ∈ U, a u ∈ U) : a ∈ stabSub U := by
  intro u
  refine ⟨fun hu => ?_, fun hu => haU u hu⟩
  have h1 : a (a u) = u := by
    have := congrArg (fun g : MulAut W => g u) ha2
    simpa [pow_two] using this
  rw [← h1]
  exact haU _ hu

theorem sup_zpowers_le_stabSub {K : Subgroup (MulAut W)} {U : Subgroup W} {a : MulAut W}
    (ha2 : a ^ 2 = 1) (hKU : ∀ k ∈ K, ∀ u ∈ U, k u ∈ U) (haU : ∀ u ∈ U, a u ∈ U) :
    K ⊔ Subgroup.zpowers a ≤ stabSub U :=
  sup_le (le_stabSub_of_inv hKU) (Subgroup.zpowers_le.2 (mem_stabSub_of_sq ha2 haU))

@[expose] def resX (X : Subgroup (MulAut W)) (U : Subgroup W) (hX : X ≤ stabSub U) :
    ↥X →* MulAut ↥U :=
  (resHom U).comp (Subgroup.inclusion hX)

theorem resX_eq_one_iff {X : Subgroup (MulAut W)} {U : Subgroup W} (hX : X ≤ stabSub U) {x : ↥X} :
    resX X U hX x = 1 ↔ ∀ u ∈ U, (x : MulAut W) u = u := by
  constructor
  · intro h u hu
    have h1 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : W)) h
    simp only [MulAut.one_apply] at h1
    exact h1
  · intro h
    ext u
    exact h u u.2

end Restrict

theorem isQuotientOfSQTKCat_of_surjective {B : Type} [Group B] {M : Type} [Group M]
    {H X : Subgroup M} (hXH : X ≤ H) (hH : G64.IsQuotientOfSQTKCat ↥H) (φ : ↥X →* B)
    (hφ : Function.Surjective φ) : G64.IsQuotientOfSQTKCat B := by
  obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := G64.isQuotientOfSQTKCat_of_le hXH hH
  let ψ : Y →* B := φ.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' N))
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨x, rfl⟩ := hφ b
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (e x)
    refine ⟨y, ?_⟩
    show φ (e.symm (QuotientGroup.mk' N y)) = φ x
    rw [hy]
    simp
  exact ⟨Y, inferInstance, inferInstance, ψ.ker, inferInstance, hY,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm⟩⟩

section PCore

variable {V : Type} [CommGroup V] [Finite V]

theorem pCoreOf_two_eq_bot_of_irr (hV : ∀ v : V, v ^ 2 = 1) {G Kb : Subgroup (MulAut V)}
    (hKG : Kb ≤ G)
    (hirr : ∀ B : Subgroup V, (∀ k ∈ Kb, ∀ b ∈ B, k b ∈ B) → B = ⊥ ∨ B = ⊤) :
    pCoreOf 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hne : ∃ v : V, v ≠ 1
  · let R : Subgroup (MulAut V) := pCoreOf 2 G
    have hRp : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 G
    have hnorm : ∀ g ∈ G, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 G hg) r).1 hr
    obtain ⟨v₀, hv₀, hfix⟩ := G64.exists_fixed_ne_one (A := V) (Q := ↥R) hRp hV
      (fun q => map_one (q : MulAut V)) hne
    have hBinv : ∀ k ∈ Kb, ∀ b ∈ fixV R, k b ∈ fixV R := by
      intro k hk b hb r hr
      have h1 : (k⁻¹ * r * k : MulAut V) ∈ R := by
        have := hnorm k⁻¹ (G.inv_mem (hKG hk)) r hr
        simpa using this
      have h2 := hb _ h1
      have h3 : (k⁻¹ * r * k : MulAut V) b = b := h2
      have h4 : r (k b) = k b := by
        have := congrArg k h3
        simpa [mul_assoc] using this
      exact h4
    have hB := hirr (fixV R) hBinv
    have hBtop : fixV R = ⊤ := by
      rcases hB with h | h
      · exfalso
        have : v₀ ∈ fixV R := fun r hr => hfix ⟨r, hr⟩
        rw [h] at this
        exact hv₀ (Subgroup.mem_bot.1 this)
      · exact h
    rw [eq_bot_iff]
    intro r hr
    rw [Subgroup.mem_bot]
    ext v
    have : v ∈ fixV R := by rw [hBtop]; exact Subgroup.mem_top v
    exact this r hr
  · push Not at hne
    rw [eq_bot_iff]
    intro r _
    rw [Subgroup.mem_bot]
    ext v
    rw [hne v]
    simp

end PCore

end S153EB6

end CFSG.Quasithin
