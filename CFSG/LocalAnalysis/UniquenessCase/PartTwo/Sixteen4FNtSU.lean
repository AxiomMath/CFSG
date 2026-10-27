module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtDual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUCoh
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUForm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtSUInd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem s16nt_su_h1_nat_le {K : Type} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    (hK : Nat.card K = 4) {n : ℕ} (hn : 4 ≤ n) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (s16ntNatRep (CFSG.LieType.Universal.Unitary.SUid (s16ntSuSigma K) n))) ≤ n := by
  obtain ⟨s, hs, hcomm⟩ := s16nt_su_exists_s hK hn
  obtain ⟨S, F, hS, hF, hSF⟩ := s16nt_su_cent hK hn hcomm
  obtain ⟨hodd, hfix⟩ := s16nt_su_torus_odd_fix (n := n) hK (by omega)
  exact (s16nt_h1_le_of_normalizer _ (s16ntSuTorus K n) hodd hfix s (s16nt_su_gen hK hn hs) S hS
    F hSF).trans hF

theorem s16nt_h1_su_le {K : Type} [Field K] [Finite K] [Algebra (ZMod 2) K] {n : ℕ}
    (hn : 4 ≤ n) (hK : Nat.card K = 4) :
    Module.finrank (ZMod 2) (CFSG.Quasithin.JonesParshall.H1
      (Representation.dual (s16ntNatRep (StatedSU n 2 K)))) ≤ n := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  obtain ⟨β, hβ, hinv⟩ := s16nt_su_form hK
  have h : CFSG.LieType.Universal.Unitary.SUid (s16ntSuSigma K) n = StatedSU n 2 K :=
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1) (by rw [hK]; norm_num) n
  rw [s16nt_h1_dual_natRep _ β hβ hinv, ← h]
  exact s16nt_su_h1_nat_le hK hn

theorem s16nt_cover_su {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 4 ≤ n)
    (hK : Nat.card K = 4) : S16BoundCover (FFModel.nat (StatedSU n 2 K)) n := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Fintype.card K = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hK]
    norm_num
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcard
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact s16nt_cover_of_h1 (StatedSU n 2 K) (s16nt_h1_su_le hn hK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
