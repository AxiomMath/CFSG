module

public import CFSG.RankThree.PartOne.KGD.D4QPerX
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Neg

variable (L : Type) [Field L]

@[expose] noncomputable def triNeg : ModGL TwistTag.D4.tag L :=
  canonicalRep (coxeterSystem TwistTag.D4.tag) L trialityOppositionWeyl

variable {L}

theorem triNeg_mem_monomial : triNeg L ∈ monomialSubgroup TwistTag.D4.tag L :=
  canonicalRep_mem_monomialSubgroup L trialityOppositionWeyl

theorem triNeg_mem_adjoint : triNeg L ∈ adjointGroup TwistTag.D4.tag L :=
  monomialSubgroup_le_adjointGroup' triNeg_mem_monomial

theorem weylQuotientHom_triNeg :
    weylQuotientHom TwistTag.D4.tag L ⟨triNeg L, triNeg_mem_monomial⟩ = trialityOppositionWeyl :=
  weylQuotientHom_eq (mapsRootLines_canonicalRep trialityOppositionWeyl)

theorem trialityOppositionWeyl_mem_rel : trialityOppositionWeyl ∈ relWeylTwist TwistTag.D4 := by
  have h0 := TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩
  have h1 := TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩
  exact mul_mem h0 (mul_mem (mul_mem (mul_mem h1 h0) h1) (inv_mem (mul_mem h1 h0)))

theorem triNeg_twistHom (Fr : L →+* L) :
    twistHom TwistTag.D4 L Fr (triNeg L) = triNeg L :=
  (d4Q_nw_facts Fr trialityOppositionWeyl_mem_rel).2.2

theorem triNeg_conj_pinnedX [CharP L 2] {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) (c : L) :
    triNeg L * pinnedX TwistTag.D4.tag L α c * (triNeg L)⁻¹ =
      pinnedX TwistTag.D4.tag L (-α) c := by
  have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
  rw [triNeg, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ hα, trialityOppositionWeyl_smul]

theorem triNeg_twistedTorus [IsAlgClosed L] (Fr : L →+* L) :
    twistedTorusOf (triNeg L) (twistHom TwistTag.D4 L Fr) =
      (fixedCharTuples d4QM Fr).map (rootDiagUnitHom TwistTag.D4.tag L) :=
  twistedTorus_D4_eq_map_of_weylImage Fr triNeg_mem_monomial _ weylQuotientHom_triNeg d4QM
    (fun x => by rw [d4QM_mulVec_permLattice]; exact trialityOppositionWeyl_smul x)

end Neg

section Frame

theorem tri_frame_e2 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] :
    ∃ g0 : ModGL TwistTag.D4.tag L, g0 ∈ adjointGroup TwistTag.D4.tag L ∧
      twistHom TwistTag.D4 L (iterateFrobenius L 2 f) g0 = g0 * triNeg L ∧
      (∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
        (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L 2 f) x = x) →
          P ≤ (triEmb K σ L).range) ∧
      ∀ Q : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p Q →
        ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ Q,
          g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈
            twistedTorusOf (triNeg L) (twistHom TwistTag.D4 L (iterateFrobenius L 2 f)) := by
  classical
  have hℓ : (2 : ℕ).Prime := Nat.prime_two
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hq2 : 2 ≤ 2 ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hℓq : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := 2) hf L (triNeg L) triNeg_mem_adjoint
  have hT := triNeg_twistedTorus Fr
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨g0, hg0C, hg0, fun P hPC hPF => ?_, fun Q hQ => ?_⟩
  · rw [hrange]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  · have hN : (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) ≠ 0 := by positivity
    have hZcard : Nat.card ((fixedCharTuples d4QM Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) =
        (2 ^ f + 1) * ((2 ^ f) ^ 3 + 1) := by
      rw [Subgroup.card_map_of_injective rootDiagUnit_injective]
      exact d4Q_card hℓq hFr
    have hCcard := (triality_both_orientations_exact_finite_order 2 f hℓ hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
    have hord : p ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
        p ^ ((2 ^ f + 1) * ((2 ^ f) ^ 3 + 1)).factorization p := by
      rw [hCcard]
      exact d4Q_ordProj hp hp3 hq2 hpq
    obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (triEmb K σ L)
      triEmb_injective (twistHom TwistTag.D4 L Fr) (triNeg L) g0 hg0C hg0 hp hp3 hN
      (fun X hX hXC hXF => triEmb_rational hℓ hf hK hσ Fr hFr X hXC hXF)
      ((fixedCharTuples d4QM Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) hT.symm.le hZcard
      hord
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => by rw [hT]; exact (mem_subtorusImage_iff _ _ _ _).1 (hc y hy)⟩

end Frame

end CFSG.RankThree.PartOne.TCX.Tri
