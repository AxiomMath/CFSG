module

public import CFSG.RankThree.PartOne.KE.E6TwThreeContra
public import CFSG.RankThree.PartOne.KE.E6TwThreeLayer

public noncomputable section

namespace CFSG.RankThree.PartOne.KETw3

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.E6
open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (diagE6)
open scoped Matrix MatrixGroups Pointwise commutatorElement

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {K : Type} [Field K] {σ : K →+* K} [Algebra K Ω]

theorem phi3_graph_contra [IsAlgClosure K Ω] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ (ℓ ^ f) ^ 2 + ℓ ^ f + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ phi3Torus Ω Fr) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2)
    {G₃ : ModGL Tag.E6 Ω} (hG₃ : G₃ ∈ adjointGroup Tag.E6 Ω)
    (hfix : (G₃ * diagE6 Ω) * x * (G₃ * diagE6 Ω)⁻¹ = x)
    (hP : ∀ u ∈ ⁅rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr,
        rootSpan Tag.E6 Ω (torusRootKernel x) ⊓ phi3FixedGroup Ω Fr⁆,
      (G₃ * diagE6 Ω) * u * (G₃ * diagE6 Ω)⁻¹ = u) : False := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  obtain ⟨hpΩ, ⟨ζ, hζ⟩, -⟩ := phi3_prime_setup (Ω := Ω) hf hp hpq
  have hp7 := (phi3_prime_facts hp hp3 hpq).2.2
  have hxH : x ∈ torusGroup Tag.E6 Ω := hx.1
  have hxp' : x ^ p = 1 := hxp ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨z, by rw [hFr, hz]⟩
  obtain ⟨w, k₂, h₁, h₂, hw, hk₂, hlayer⟩ := phi3_A2A2_layer hℓ hf hK hσ hFr hp hp3 hpq hx hxp hA2A2
  have hk₀card := natCard_eqLocusField hℓ hf hK hσ
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra h
    push Not at h
    have hcard : Nat.card (RingHom.eqLocusField σ (RingHom.id K)) = Nat.card K :=
      Nat.card_congr (Equiv.subtypeUnivEquiv (fun c => by
        rw [RingHom.mem_eqLocusField, RingHom.id_apply]
        exact h c))
    rw [hk₀card, hK] at hcard
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    nlinarith
  have htk : ∃ t ∈ k₂, Fr t ≠ t := by
    refine ⟨algebraMap K Ω c, (hk₂ _).2 ?_, ?_⟩
    · rw [← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
    · rw [hFr, ← map_pow, ← hσ]
      exact fun h => hc ((algebraMap K Ω).injective h)
  exact twoA2_graph_contra (by omega) hpΩ hζ ⟨Fr.injective, hFrs⟩ k₂ htk h₁ h₂ w hxH hxp' hx1 hw hG₃
    hfix (fun A => hP _ (hlayer A))

end CFSG.RankThree.PartOne.KETw3
