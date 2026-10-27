module

public import CFSG.RankThree.PartOne.KGD.D4T36Torus

public noncomputable section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice
open scoped Matrix Polynomial

section Weyl

theorem permLattice_permLattice_symm (y : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm (permLattice TwistTag.D4.perm.symm y) = y := by
  funext i
  change y (TwistTag.D4.perm (TwistTag.D4.perm.symm i)) = y i
  rw [Equiv.apply_symm_apply]

theorem d4T36_weyl {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ w : WeylGroup TwistTag.D4.tag,
      ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x := by
  obtain ⟨w, hw⟩ := exists_smul_trialityRho hε
  refine ⟨w, fun x => ?_⟩
  rw [d4T36M_eq]
  refine Eq.symm (Eq.trans (hw (permLattice TwistTag.D4.perm.symm x)) ?_)
  exact congrArg (fun y => w • y) (permLattice_permLattice_symm x)

end Weyl

section Frame

theorem d4T36_frame {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ (n : ModGL TwistTag.D4.tag L) (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
      (w : WeylGroup TwistTag.D4.tag),
      weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w ∧
      (∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x) ∧
      ∃ g0 : ModGL TwistTag.D4.tag L, g0 ∈ adjointGroup TwistTag.D4.tag L ∧
        twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n ∧
        (∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
          (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
            P ≤ (triEmb K σ L).range) ∧
        ∀ Q : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p Q →
          ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ Q,
            g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈
              twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hℓq : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
  obtain ⟨w, hw⟩ := d4T36_weyl hε
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hndef
  have hnM : n ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hnW : weylQuotientHom TwistTag.D4.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnC : n ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hnM
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L n hnC
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hnM w hnW (d4T36M ε) hw
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨n, hnM, w, hnW, hw, g0, hg0C, hg0, fun P hPC hPF => ?_, fun Q hQ => ?_⟩
  · rw [hrange]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  · have hN : d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f) ≠ 0 := by
      have : 0 < d4T36d ε (ℓ ^ f) := (d4T36d_odd hε (by omega)).pos
      positivity
    have hZcard : Nat.card ((fixedCharTuples (d4T36M ε) Fr).map
        (rootDiagUnitHom TwistTag.D4.tag L)) = d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f) := by
      rw [Subgroup.card_map_of_injective rootDiagUnit_injective]
      exact d4T36_card hε (by omega) hℓq hFr
    have hCcard := (triality_both_orientations_exact_finite_order ℓ f hℓ hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
    have hord : p ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
        p ^ (d4T36d ε (ℓ ^ f) * d4T36d ε (ℓ ^ f)).factorization p := by
      rw [hCcard]
      exact d4T36_ordProj hε hp hp3 hq2 hpd
    obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (triEmb K σ L)
      triEmb_injective (twistHom TwistTag.D4 L Fr) n g0 hg0C hg0 hp hp3 hN
      (fun X hX hXC hXF => triEmb_rational hℓ hf hK hσ Fr hFr X hXC hXF)
      ((fixedCharTuples (d4T36M ε) Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) hT.symm.le hZcard
      hord
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => by rw [hT]; exact (mem_subtorusImage_iff _ _ _ _).1 (hc y hy)⟩

end Frame

end CFSG.RankThree.PartOne.KGD
