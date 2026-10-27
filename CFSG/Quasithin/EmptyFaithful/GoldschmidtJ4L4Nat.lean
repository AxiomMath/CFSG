module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Cases
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Hj

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint CFSG.Quasithin.J4Loc
open CFSG.Open CFSG.LieType.BorelTits

theorem innerOnModO2_of_overgroups
    (hO : J4TwoLocalOvergroups) {B : Subgroup J} (hPB : P0 ≤ Subgroup.normalizer (B : Set J))
    (hB : HasA8 B) : ∀ x ∈ P0, A38c8.InnerOnModO2 B x := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, hker⟩ := exists_hom_of_hasA8 hB
  have hker' : ∀ x : ↥B, f x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 ⟨x, by rw [← hker]; exact hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  by_cases hR : CFSG.Open.pCore 2 ↥B = ⊥
  ·
    exfalso
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 (hker.trans hR)
    exact false_of_card_normalizing (isPGroup_P0 hF) (by rw [card_P0 hM hF]; norm_num) hPB
      (MulEquiv.ofBijective f ⟨hinj, hf⟩) fun g hg K hK hKc => card_le_of_centralizes_five hg hK hKc
  ·
    have hRne : pCoreOf 2 B ≠ ⊥ := fun h =>
      hR ((Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).1 h)
    have hYn : B ⊔ P0 ≤ Subgroup.normalizer (pCoreOf 2 B : Set J) :=
      sup_le (le_normalizer_pCoreOf 2 B) (hPB.trans (normalizer_le_normalizer_pCoreOf 2 B))
    rcases overgroup_of_normal_two_subgroup hO (Y := B ⊔ P0) le_sup_right
      (pCoreOf_isPGroup 2 B) hRne (fun y hy x hx =>
        (Subgroup.mem_normalizer_iff.1 (hYn hy) x).1 hx) with h | h | h
    · exact innerOnModO2_of_le_Hj (le_sup_left.trans h) hPB f hf hker
    · exact (false_of_case_z0 (le_sup_right.trans h) (le_sup_left.trans h) f hf hker').elim
    · exact (false_of_case_V0 (le_sup_right.trans h) (le_sup_left.trans h) f hf hker').elim

end CFSG.Quasithin.J4L4
