module

public import CFSG.RankThree.PartOne.KLR.Embedding
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR

theorem exists_gamma_of_model {X : Type} [Group X] {f : ℕ}
    (h : ReeTitsModel X .twistedF4 2 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧
      Nonempty (X ≃* ReeTag.F4.reeGamma K a) := by
  obtain ⟨hFin, -, -, -, ⟨a, ha, hfa⟩, hmodel⟩ := ReeTag.large_Ree_model_Schreier X 2 f h
  obtain ⟨-, a', hfa', hrel⟩ := h
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := hrel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K ReeTag.F4.prime := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  have haa : a' = a := by omega
  subst haa
  obtain ⟨e'⟩ := hmodel a' K hfa' hKcard ⟨e⟩
  exact ⟨a', K, inferInstance, inferInstance, hchar, ha, hfa', hKcard, ⟨e'⟩⟩

theorem exists_conj_le_of_card_dvd {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    (T : Subgroup Γ) (hT : p ^ (Nat.card Γ).factorization p ∣ Nat.card T) {A : Subgroup Γ}
    (hA : IsPGroup p A) : ∃ c : Γ, ∀ x ∈ A, c * x * c⁻¹ ∈ T := by
  classical
  have hTΓ : Nat.card T ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card T
  have hfac : (Nat.card T).factorization p = (Nat.card Γ).factorization p := by
    have h1 : (Nat.card T).factorization p ≤ (Nat.card Γ).factorization p :=
      ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).2 hTΓ) p
    have h2 : (Nat.card Γ).factorization p ≤ (Nat.card T).factorization p := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out (Nat.card_pos.ne')).1 hT
      exact this
    exact le_antisymm h1 h2
  obtain ⟨P⟩ : Nonempty (Sylow p T) := inferInstance
  set P' : Subgroup Γ := (P : Subgroup T).map T.subtype with hP'
  have hP'card : Nat.card P' = p ^ (Nat.card Γ).factorization p := by
    have h1 : Nat.card P' = Nat.card (P : Subgroup T) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).symm.toEquiv
    rw [h1, P.card_eq_multiplicity, hfac]
  let Q₀ : Sylow p Γ := Sylow.ofCard P' hP'card
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q₀ Q
  refine ⟨g⁻¹, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup Γ) := hQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have hQ₀ : ((Q₀ : Subgroup Γ)) = P' := rfl
  rw [hQ₀] at hxQ
  obtain ⟨t, -, ht⟩ := hxQ
  have h2 : g⁻¹ * x * g = (t : Γ) := by
    have : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      simp [MulAut.smul_def]
    rw [← this, ← ht]
    rfl
  rw [inv_inv, h2]
  exact t.2

section Embedding

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] (D : ReeFrameData K L a)

theorem exists_twisted_embedding {n g₀ : ModGL ReeTag.F4.tag L}
    (hg₀ : g₀ ∈ adjointGroup ReeTag.F4.tag L) (hFg₀ : Fext D.F g₀ = g₀ * n)
    (E : Subgroup (ModGL ReeTag.F4.tag L)) (hEF : E ≤ twistedFixed D.F n) :
    ∃ T : Subgroup (ReeTag.F4.reeGamma K a),
      (∀ γ, γ ∈ T ↔ g₀⁻¹ * thetaGamma L a γ * g₀ ∈ E) ∧
      (∀ e ∈ E, ∃ γ ∈ T, g₀⁻¹ * thetaGamma L a γ * g₀ = e) ∧ Nat.card T = Nat.card E := by
  classical
  let T : Subgroup (ReeTag.F4.reeGamma K a) :=
    E.comap ((MulAut.conj g₀⁻¹).toMonoidHom.comp (thetaGamma L a))
  have hmem : ∀ γ, γ ∈ T ↔ g₀⁻¹ * thetaGamma L a γ * g₀ ∈ E := fun γ => by
    show (MulAut.conj g₀⁻¹) (thetaGamma L a γ) ∈ E ↔ _
    simp
  have hsurj : ∀ e ∈ E, ∃ γ ∈ T, g₀⁻¹ * thetaGamma L a γ * g₀ = e := by
    intro e he
    have hfix : Fext D.F (g₀ * e * g₀⁻¹) = g₀ * e * g₀⁻¹ := by
      obtain ⟨hadj, hfx⟩ := hEF he
      have hFe : Fext D.F e = n⁻¹ * e * n := by
        have h1 : n * Fext D.F e * n⁻¹ = e := hfx
        calc Fext D.F e = n⁻¹ * (n * Fext D.F e * n⁻¹) * n := by group
          _ = n⁻¹ * e * n := by rw [h1]
      rw [Fext_conj D.F hg₀ hadj, hFg₀, hFe]
      group
    have hadj : g₀ * e * g₀⁻¹ ∈ adjointGroup ReeTag.F4.tag L :=
      mul_mem (mul_mem hg₀ (hEF he).1) (inv_mem hg₀)
    obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hadj hfix
    refine ⟨γ, (hmem γ).2 ?_, ?_⟩
    · rw [hγ]
      have : g₀⁻¹ * (g₀ * e * g₀⁻¹) * g₀ = e := by group
      rw [this]
      exact he
    · rw [hγ]
      group
  have hcard : Nat.card T = Nat.card E := by
    refine Nat.card_congr (Equiv.ofBijective (fun γ : T => (⟨g₀⁻¹ * thetaGamma L a γ.1 * g₀,
      (hmem γ.1).1 γ.2⟩ : E)) ⟨?_, ?_⟩)
    · intro γ₁ γ₂ h12
      have h3 := congrArg Subtype.val h12
      have h4 : thetaGamma L a γ₁.1 = thetaGamma L a γ₂.1 := by
        have := mul_left_cancel (mul_right_cancel h3)
        exact this
      exact Subtype.ext (thetaGamma_injective L h4)
    · rintro ⟨e, he⟩
      obtain ⟨γ, hγT, hγ⟩ := hsurj e he
      exact ⟨⟨γ, hγT⟩, Subtype.ext hγ⟩
  exact ⟨T, hmem, hsurj, hcard⟩

end Embedding

end CFSG.RankThree.PartOne.KEXC
