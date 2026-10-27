module

public import CFSG.RankThree.PartOne.KE6.Tw6Torus
public import CFSG.RankThree.PartOne.KE6.Tw6Arith
public import CFSG.RankThree.PartOne.KE.E6TwFourData

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Classical2 (twistE6)

theorem tw6_frame {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] [CharP K ℓ]
    (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ g0 : ModGL Tag.E6 L, g0 ∈ adjointGroup Tag.E6 L ∧
      twistE6 L (iterateFrobenius L ℓ f) g0 = g0 * tw6N L ∧
      (∀ P : Subgroup (ModGL Tag.E6 L), Finite P → P ≤ adjointGroup Tag.E6 L →
        (∀ x ∈ P, twistE6 L (iterateFrobenius L ℓ f) x = x) → ⁅P, P⁆ = P →
          P ≤ (twE6Emb K σ L).range) ∧
      ∀ Q : Subgroup (twistedE6RootGroup K σ), IsPGroup p Q →
        ∃ c : twistedE6RootGroup K σ, ∀ q ∈ Q, g0⁻¹ * twE6Emb K σ L (c * q * c⁻¹) * g0 ∈
          twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L ℓ f)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hq0 : (((ℓ ^ f : ℕ)) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hnC : tw6N L ∈ adjointGroup Tag.E6 L := canonicalRep_mem_adjointGroup _ L _
  obtain ⟨g0, hg0C, hg0'⟩ : ∃ g0 : ModGL Tag.E6 L, g0 ∈ adjointGroup Tag.E6 L ∧
      twistE6 L Fr g0 = g0 * tw6N L := lang_conjugator_twisted_gen K (ℓ := ℓ) (f := f) hf L _ hnC
  obtain ⟨kk, hrat, hordC⟩ := e6_tw_rational hℓ hf K hK σ hσ L Fr hFr
  obtain ⟨hTcard, -⟩ := natCard_tw6Torus (Ω := L) (Fr := Fr) hFr hq0
  have hN' : ((ℓ ^ f) ^ 2 - ℓ ^ f + 1) ^ 3 ≠ 0 := pow_ne_zero 3 (Nat.succ_ne_zero _)
  have hord : p ^ (Nat.card (twistedE6RootGroup K σ)).factorization p =
      p ^ (((ℓ ^ f) ^ 2 - ℓ ^ f + 1) ^ 3).factorization p := by
    rw [hordC p hp hp3]
    congr 1
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      padicValNat_twistedE6_order_six hp hp3 hq2 hpq, padicValNat.pow _ 3]
  obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen (3 ^ kk) (twE6Emb K σ L)
    twE6Emb_injective (twistE6 L Fr) (tw6N L) g0 hg0C hg0' hp hp3 hN'
    (fun X hX hXC hXF => ⟨(@hrat X hX hXC hXF).1, (@hrat X hX hXC hXF).2.1⟩)
    (twistedTorusOf (tw6N L) (twistE6 L Fr)) le_rfl hTcard hord
  refine ⟨g0, hg0C, hg0', fun P hPfin hPC hPF hPP => (@hrat P hPfin hPC hPF).2.2 P le_rfl hPP, ?_⟩
  intro Q hQ
  obtain ⟨c, hc⟩ := hconj Q hQ
  exact ⟨c, fun q hq => (mem_subtorusImage_iff _ _ _ _).1 (hc q hq)⟩

end CFSG.RankThree.PartOne.KE6
