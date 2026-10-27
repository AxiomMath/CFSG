module

public import CFSG.RankThree.PartOne.KGD.D4QTorus

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Polynomial

theorem d4Q_twistedTorus {L : Type} [Field L] [IsAlgClosed L] (Fr : L →+* L) :
    twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr) =
      (fixedCharTuples d4QM Fr).map (rootDiagUnitHom TwistTag.D4.tag L) :=
  twistedTorus_D4_eq_map_of_weylImage Fr trialityOpposition_mem_monomialSubgroup _ rfl d4QM
    d4Q_weylImage

theorem d4Q_frame {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ g0 : ModGL TwistTag.D4.tag L, g0 ∈ adjointGroup TwistTag.D4.tag L ∧
      twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * trialityOpposition L ∧
      (∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
        (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
          P ≤ (triEmb K σ L).range) ∧
      ∀ Q : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p Q →
        ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ Q,
          g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈
            twistedTorusOf (trialityOpposition L)
              (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  have hnC : trialityOpposition L ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' trialityOpposition_mem_monomialSubgroup
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L (trialityOpposition L) hnC
  have hT := d4Q_twistedTorus Fr
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨g0, hg0C, hg0, fun P hPC hPF => ?_, fun Q hQ => ?_⟩
  · rw [hrange]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  · have hN : (ℓ ^ f + 1) * ((ℓ ^ f) ^ 3 + 1) ≠ 0 := by positivity
    have hZcard : Nat.card ((fixedCharTuples d4QM Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) =
        (ℓ ^ f + 1) * ((ℓ ^ f) ^ 3 + 1) := by
      rw [Subgroup.card_map_of_injective rootDiagUnit_injective]
      exact d4Q_card hℓq hFr
    have hCcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
    have hord : p ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
        p ^ ((ℓ ^ f + 1) * ((ℓ ^ f) ^ 3 + 1)).factorization p := by
      rw [hCcard]
      exact d4Q_ordProj hp hp3 hq2 hpq
    obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (triEmb K σ L)
      triEmb_injective (twistHom TwistTag.D4 L Fr) (trialityOpposition L) g0 hg0C hg0 hp hp3 hN
      (fun X hX hXC hXF => triEmb_rational hℓ hf hK hσ Fr hFr X hXC hXF)
      ((fixedCharTuples d4QM Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) hT.symm.le hZcard hord
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => by rw [hT]; exact (mem_subtorusImage_iff _ _ _ _).1 (hc y hy)⟩

end CFSG.RankThree.PartOne.KGD
