module

public import CFSG.RankThree.PartOne.KGD.D4T36Frame
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Frame


theorem tri_frame_e36 {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ ((2 ^ f : ℕ) : ℤ) ^ 2 + ε * ((2 ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] :
    ∃ w : WeylGroup TwistTag.D4.tag,
      (∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x) ∧
      ∃ g0 : ModGL TwistTag.D4.tag L, g0 ∈ adjointGroup TwistTag.D4.tag L ∧
        twistHom TwistTag.D4 L (iterateFrobenius L 2 f) g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∧
        (∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
          (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L 2 f) x = x) →
            P ≤ (triEmb K σ L).range) ∧
        ∀ Q : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), IsPGroup p Q →
          ∃ c : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, ∀ y ∈ Q,
            g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈
              twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)
                (twistHom TwistTag.D4 L (iterateFrobenius L 2 f)) := by
  classical
  have hℓ : (2 : ℕ).Prime := Nat.prime_two
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hq2 : 2 ≤ 2 ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hℓq : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  obtain ⟨w, hw⟩ := d4T36_weyl hε
  refine ⟨w, hw, ?_⟩
  set n : ModGL TwistTag.D4.tag L := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hndef
  have hnM : n ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hnW : weylQuotientHom TwistTag.D4.tag L ⟨n, hnM⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hnC : n ∈ adjointGroup TwistTag.D4.tag L := monomialSubgroup_le_adjointGroup' hnM
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := 2) hf L n hnC
  have hT := twistedTorus_D4_eq_map_of_weylImage Fr hnM w hnW (d4T36M ε) hw
  have hrange := triEmb_range hℓ hf hK hσ Fr hFr
  refine ⟨g0, hg0C, hg0, fun P hPC hPF => ?_, fun Q hQ => ?_⟩
  · rw [hrange]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  · have hN : d4T36d ε (2 ^ f) * d4T36d ε (2 ^ f) ≠ 0 := by
      have : 0 < d4T36d ε (2 ^ f) := (d4T36d_odd hε (by omega)).pos
      positivity
    have hZcard : Nat.card ((fixedCharTuples (d4T36M ε) Fr).map
        (rootDiagUnitHom TwistTag.D4.tag L)) = d4T36d ε (2 ^ f) * d4T36d ε (2 ^ f) := by
      rw [Subgroup.card_map_of_injective rootDiagUnit_injective]
      exact d4T36_card hε (by omega) hℓq hFr
    have hCcard := (triality_both_orientations_exact_finite_order 2 f hℓ hf K hK 1 (Or.inl rfl)
      σ.toRingHom (fun c => by rw [pow_one]; exact hσ c)).1
    have hord : p ^ (Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).factorization p =
        p ^ (d4T36d ε (2 ^ f) * d4T36d ε (2 ^ f)).factorization p := by
      rw [hCcard]
      exact d4T36_ordProj hε hp hp3 hq2 hpd
    obtain ⟨-, -, -, hconj⟩ := sylow_conjugacy_of_subtorus_gen 1 (triEmb K σ L)
      triEmb_injective (twistHom TwistTag.D4 L Fr) n g0 hg0C hg0 hp hp3 hN
      (fun X hX hXC hXF => triEmb_rational hℓ hf hK hσ Fr hFr X hXC hXF)
      ((fixedCharTuples (d4T36M ε) Fr).map (rootDiagUnitHom TwistTag.D4.tag L)) hT.symm.le hZcard
      hord
    obtain ⟨c, hc⟩ := hconj Q hQ
    exact ⟨c, fun y hy => by rw [hT]; exact (mem_subtorusImage_iff _ _ _ _).1 (hc y hy)⟩

theorem tri_kernel_e36 {f : ℕ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {p : ℕ} (hp : p.Prime)
    (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] {w : WeylGroup TwistTag.D4.tag}
    (hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hbT : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)
        (twistHom TwistTag.D4 L (iterateFrobenius L 2 f)))
    (hbo : orderOf (rootDiagUnit TwistTag.D4.tag b) = p) :
    rootCharKernel b = ∅ ∨ ∃ i : Fin 4, rootCharKernel b = trialitySigma i := by
  have hnM : canonicalRep (coxeterSystem TwistTag.D4.tag) L w ∈
      monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L w
  have hnW : weylQuotientHom TwistTag.D4.tag L ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) L w,
      hnM⟩ = w := weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hb1 := ne_one_of_orderOf_rootDiagUnit hp hbo
  have hbfix : b ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L 2 f) := by
    have hh' := hbT
    rw [twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L 2 f) hnM w hnW (d4T36M ε) hw] at hh'
    obtain ⟨b', hb', hbb'⟩ := hh'
    have : b' = b := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) hbb'
    exact this ▸ hb'
  exact d4T36_rootCharKernel_cases hε hbfix hb1

end Frame

end CFSG.RankThree.PartOne.TCX.Tri
