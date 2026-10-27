module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WU3Nine
import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Red
import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Odd
import CFSG.RankThree.PartTwo.Sec14.Ronan148WFieldE27Even
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec6.Statements
import Certificates.Certificate43

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_two_local_model (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h9 : p ^ f % 9 = 1 ∨ p ^ f % 9 = 8) (h2 : ¬ (p = 2 ∧ p ^ f % 9 = 8))
    (E : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))))
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) :
    ∃ B : Subgroup (MulAut (projImage (slPi π 3 (p ^ f) K))), B ≤ E ∧ Nat.card B = 9 ∧
      ∃ T : Subgroup (projImage (slPi π 3 (p ^ f) K)), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        ∀ b ∈ B, ∀ t ∈ T, b t ∈ T := by
  have hp := hK.prime
  have hq2 : 2 < p ^ f := by
    have h1 : p ≤ p ^ f := Nat.le_self_pow (by have := hK.one_le; omega) p
    have h2' := hp.two_le
    omega
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := hK.charP
  refine exists_two_local_model_of hK hq hq2 ?_ E hE hE27
  intro τ hτ hτ1 ψ hψτ y hy hy3 hys hyψ
  by_cases hp2 : p = 2
  · subst hp2
    cases π
    · exfalso
      change 2 ^ f % 3 = 2 at hq
      have h8 : 2 ^ f % 9 = 1 := by
        rcases h9 with h | h
        · exact h
        · exact absurd ⟨rfl, h⟩ h2
      omega
    · have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      exact exists_two_subgroup_of_cube_two h2K hτ hτ1 hψτ hy3 hys hyψ
  · have h2K : (2 : K) ≠ 0 := by
      intro h
      apply hp2
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd
    exact exists_two_subgroup_of_cube_odd hπ hq' h2K (hK.three_ne_zero hq) hτ hτ1 hψτ hy hy3
      hys hyψ

theorem kF148FieldE27 : KF148FieldE27 := by
  intro X _ _ p f _ hf hiso h9 h2 E hE hE27
  obtain ⟨π, K, _, hK, hq, ⟨φX⟩⟩ := Sec13.exists_projImage_model hf hiso
  obtain ⟨B, hBE, hB9, T, hT, hT2, hBT⟩ := exists_two_local_model hK hq h9 h2
    (E.map (MulAut.congr φX).toMonoidHom) (hE.map _)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr φX).injective, hE27])
  refine ⟨B.map (MulAut.congr φX).symm.toMonoidHom, ?_, ?_, T.map φX.symm.toMonoidHom, ?_,
    hT2.map _, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hBE hb
    have hsa : (MulAut.congr φX).symm.toMonoidHom ((MulAut.congr φX).toMonoidHom a) = a :=
      (MulAut.congr φX).symm_apply_apply a
    rw [hsa]
    exact ha
  · rw [Subgroup.card_map_of_injective (MulAut.congr φX).symm.injective, hB9]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ φX.symm.injective]
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨t, ht, rfl⟩
    refine ⟨b t, hBT b hb t ht, ?_⟩
    simp [MulAut.congr_symm_apply]

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
