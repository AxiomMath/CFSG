module

public import CFSG.Permutation.UnitaryThreeRecognition.Endgame
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport
public import CFSG.Permutation.UnitaryThreeRecognition.SMapMoufang

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1 CFSG.BenderSuzuki.PFchapter4section1
open CFSG.UnitaryThreeRecognition.Model

namespace IsRootSubgroup

theorem statedClassicalModel_of_sMap_eq_weyl {G Ω : Type} [Group G] [Finite G] [IsSimpleGroup G]
    [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω] (h2 : IsMultiplyPretransitive G Ω 2)
    {Q : Subgroup G} {a b : Ω} (hQ : IsRootSubgroup Q a) (hQ1 : Q ≠ ⊥) (hb : b ≠ a) {s : G}
    (hsa : s • a = b) (hs2 : s * s = 1) (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hK : Nat.card K = (p ^ f) ^ 2)
    (hfix : Nat.card {x : K // J.conj x = x} = p ^ f) (φ : Q ≃* Coord J)
    (hφ : ∀ u (hu : u ∈ Q), u ≠ 1 →
      s • (u • b) = ((φ.symm (weylCoord J (φ ⟨u, hu⟩)) : Q) : G) • b) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f := by
  classical
  have hsb := swap_smul_b hsa hs2
  have hs1 : s ≠ 1 := by rintro rfl; rw [one_smul] at hsa; exact hb hsa.symm
  have hφL : ∀ u (hu : u ∈ Q) (hu1 : u ≠ 1),
      φ ⟨sLeft Q a b s u, hQ.sLeft_mem hb hsa hs2 hu hu1⟩ = weylCoord J (φ ⟨u, hu⟩) := by
    intro u hu hu1
    have h1 : sLeft Q a b s u = ((φ.symm (weylCoord J (φ ⟨u, hu⟩)) : Q) : G) :=
      (hQ.sLeft_eq_iff hb hsa hs2 hu hu1 (φ.symm _).2).mpr (hφ u hu hu1)
    have h2' : (⟨sLeft Q a b s u, hQ.sLeft_mem hb hsa hs2 hu hu1⟩ : Q) =
        φ.symm (weylCoord J (φ ⟨u, hu⟩)) := Subtype.ext h1
    rw [h2', MulEquiv.apply_symm_apply]
  have hφR : ∀ u (hu : u ∈ Q) (hu1 : u ≠ 1),
      φ ⟨sRight Q a b s u, hQ.sRight_mem hb hsa hs2 hu hu1⟩ = weylCoordRight J (φ ⟨u, hu⟩) := by
    intro u hu hu1
    have hui : u⁻¹ ∈ Q := Q.inv_mem hu
    have hui1 : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
    have hR : sRight Q a b s u = (sLeft Q a b s u⁻¹)⁻¹ := by
      have := (hQ.sFactors_inv hb hsa hs2 hui hui1).2.2
      rw [inv_inv] at this
      exact this
    have h3 : (⟨sRight Q a b s u, hQ.sRight_mem hb hsa hs2 hu hu1⟩ : Q) =
        (⟨sLeft Q a b s u⁻¹, hQ.sLeft_mem hb hsa hs2 hui hui1⟩ : Q)⁻¹ := Subtype.ext hR
    rw [h3, map_inv, hφL u⁻¹ hui hui1]
    have h4 : (⟨u⁻¹, hui⟩ : Q) = (⟨u, hu⟩ : Q)⁻¹ := rfl
    rw [h4, map_inv, weylCoord_inv, inv_inv]
  set q := p ^ f with hqdef
  have := faithfulSMul_isoPoint J hJ q hK hfix
  have hD := pairStab_eq_inf_rightConjugate (G := G) hsa hs2
  let qIso : Q ≃* rootGroup J hJ := φ.trans (rootCoord J hJ)
  obtain ⟨e, -, heQ, het⟩ := exists_rankOnePointEquiv (stabilizer G a) Q
    (stabilizer G a ⊓ rightConjugate (stabilizer G a) s) s (sRight Q a b s) (sLeft Q a b s)
    (sTor Q a b s) a
    (stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)) (rootGroup J hJ)
    (stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) ⊓
      rightConjugate (stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ))
        (weyl J hJ))
    (weyl J hJ) (bruhatRight J hJ) (bruhatLeft J hJ) (bruhatTorus J hJ) (pinf J hJ)
    h2 rfl ⟨hs1, by rw [sq, hs2]⟩ (fun h => hb (hsa.symm.trans h)) rfl
    hQ.subgroupOf_stabilizer_normal (by rw [hD]; exact hQ.disjoint_pairStab hb)
    (by rw [hD]; exact hQ.sup_pairStab_eq_stabilizer hb)
    (fun x hx hx1 => ⟨hQ.sRight_mem hb hsa hs2 hx hx1, hQ.sRight_ne_one hb hsa hs2 hx hx1⟩)
    (fun x hx hx1 => ⟨hQ.sLeft_mem hb hsa hs2 hx hx1, hQ.sLeft_ne_one hb hsa hs2 hx hx1⟩)
    (fun x hx hx1 => by rw [hD]; exact hQ.sTor_mem hb hsa hs2 hx hx1)
    (fun x hx hx1 => hQ.conj_eq_bruhat hb hsa hs2 hx hx1)
    (isMultiplyPretransitive_two J hJ q hK hfix) rfl (isInvolution_weyl J hJ)
    (weyl_not_mem_stabilizer J hJ) rfl (rootGroup_subgroupOf_stabilizer_normal J hJ q hK hfix)
    (rootGroup_disjoint_inf_rightConjugate_weyl J hJ)
    (rootGroup_sup_inf_rightConjugate_weyl J hJ q hK hfix) (bruhatRight_mem J hJ)
    (bruhatLeft_mem J hJ) (bruhatTorus_mem J hJ) (weyl_mul_mul_weyl_eq_bruhat J hJ) qIso
    (fun x hx hx1 => by
      change root J hJ (φ ⟨sRight Q a b s x, _⟩) = bruhatRight J hJ (root J hJ (φ ⟨x, hx⟩))
      rw [bruhatRight_root, hφR x hx hx1])
  obtain ⟨E, -, -⟩ := rankOneGeneratedSubgroup_equiv Q s (rootGroup J hJ) (weyl J hJ) qIso e
    heQ het
  have htopG := hQ.closure_eq_top h2 hQ1 hb hsa hs2
  let eG : G ≃* Subgroup.closure ((Q : Set G) ∪ {s}) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htopG.symm)
  let eP := closureRootWeylEquiv J hJ q hK hfix (two_lt_prime_pow p f hp hpodd hf)
  exact statedClassicalModel_of_mulEquiv p f hp hpodd hf J hK hfix ((eG.trans E).trans eP)

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
