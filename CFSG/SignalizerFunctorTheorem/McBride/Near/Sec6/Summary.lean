module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux4
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.SummaryAux5

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thm61
    (h : Counterexample p A θ) :
    ∃ E ∈ signalizerFunctorEk p 1 A, ∃ (J : Type u) (_ : Group J), IsSimpleGroup J ∧
      (∃ a b : J, a * b ≠ b * a) ∧ Group.IsSolvable (thetaOf θ E) ∧
      (∀ f ∈ A, f ∉ E →
        Nonempty (↥(kOf (θ f)) ≃* (Fin p → J)) ∧
          E ⊔ Subgroup.zpowers f = A ⊓ khat (A ⊔ θ f) ∧ θ f = khat (θ f) ∧
          ∀ x ∈ θ f, ∃ m n : ℕ, x ^ (2 ^ m * 3 ^ n) ∈ kOf (θ f)) ∧
      (∀ f ∈ A, f ∉ E → ∀ X ∈ assoc p A θ, kOf (θ f) ≤ X → X ≤ θ f) ∧
      (IsFrobeniusWithKernel (dZero p A θ) (dOne p A θ) ∧
        IsFrobeniusWithKernel (dTwo p A θ) (dOne p A θ)) ∧
      (∀ B ∈ signalizerFunctorEk p 2 A, E ≤ B → ∀ F : Subgroup G, IsDirectPair E F B →
        IsDirectProduct {S | ∃ L ∈ lcal (thetaOf θ F), S = L ⊓ sThree p A θ ⊓ thetaOf θ E}
            (sThree p A θ ⊓ thetaOf θ B) ∧
          Nonempty (↥(sThree p A θ ⊓ thetaOf θ B) ≃* (Fin p → ↥(dTwo p A θ)))) := by
  obtain ⟨E, ⟨hE₁, hE₂⟩, -⟩ := h.thm617a
  have hE : Sec6S34.DistE p A θ E := ⟨hE₁, hE₂⟩
  obtain ⟨f₀, hf₀A, hf₀E⟩ := Sec6S34.exists_mem_not_mem h hE
  have d₀ : Sec6S34.Data h E f₀ := ⟨hE, hf₀A, hf₀E⟩
  obtain ⟨J₀, hJ₀⟩ := d₀.lcal_nonempty
  obtain ⟨-, -, hJs, hJnc⟩ := mem_lcal_iff.mp hJ₀
  refine ⟨E, hE₁, ↥J₀, inferInstance, hJs, exists_mul_ne_of_not_isMulCommutative hJnc,
    hE.isSolvable h, fun f hf hfE => ?_, hE.maximal h, ?_, hE.directProduct h⟩
  · have d : Sec6S34.Data h E f := ⟨hE, hf, hfE⟩
    exact ⟨d.nonempty_mulEquiv_pi d₀ hJ₀, h.thm617b hE₁ hE₂ hf hfE, d.eq_khat,
      h.lemma616 d.zpowers_mem_rSetN_one⟩
  · have d : Sec6S34.Data h E f₀ := d₀
    exact d.frobenius

theorem thm62
    (h : Counterexample p A θ) {E : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hEs : Group.IsSolvable (thetaOf θ E)) :
    ∃ r : ℕ, r.Prime ∧ (∃ a ∈ A, a ≠ 1 ∧ r ∣ Nat.card (θ a)) ∧
      ∃ V : Subgroup G, Maximal (fun X => X ∈ assoc p A θ ∧ IsPGroup r X) V ∧
        ¬ V ≤ ssol p A θ ∧ IsMulCommutative V ∧
        (∀ f ∈ A, f ∉ E → cenIn V {f} ≠ ⊥ ∧ IsPGroup r (cenIn V {f}) ∧
          ¬ r ∣ (cenIn V {f}).relIndex (θ f)) ∧
        (∀ f ∈ A, f ∉ E →
          cenIn V {f} ⊔ (thetaOf θ (E ⊔ Subgroup.zpowers f) ⊓ sThree p A θ) = kOf (θ f)) := by
  have hE' : Sec6S34.DistE p A θ E := Sec6S34.DistE.of_isSolvable h hE hEs
  obtain ⟨r, hr, hrp, hr2, hr3, hgood⟩ := Sec6S34.exists_good_prime h hE'
  obtain ⟨V, hV⟩ := Sec6S34.exists_srSubgroup h r
  have s : Sec6S34.SrData h E r V := ⟨hE', hr, hrp, hr2, hr3, hgood, hV⟩
  obtain ⟨f₀, hf₀A, hf₀E⟩ := Sec6S34.exists_mem_not_mem h hE'
  have d₀ : Sec6S34.Data h E f₀ := ⟨hE', hf₀A, hf₀E⟩
  exact ⟨r, hr, ⟨f₀, hf₀A, d₀.ne_one, s.dvd_card d₀⟩, V, hV, s.not_le_ssol d₀,
    s.isMulCommutative, fun f hf hfE => ⟨s.ne_bot ⟨hE', hf, hfE⟩, (s.sylow ⟨hE', hf, hfE⟩).2.1,
      ((Nat.Prime.coprime_iff_not_dvd hr).mp (s.sylow ⟨hE', hf, hfE⟩).2.2.symm)⟩,
    fun f hf hfE => s.sup_eq ⟨hE', hf, hfE⟩⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
