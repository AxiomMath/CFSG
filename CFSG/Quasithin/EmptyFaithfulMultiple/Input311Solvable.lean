module

public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremE
public import CFSG.Quasithin.Background.C58Blocks
public import CFSG.Quasithin.Background.C58Global

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

@[expose] def Input311Solvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → CFSG.QuasithinUnique.quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M₀ H R : Subgroup G, InH T M₀ → InH T H → Group.IsSolvable H →
      (∃ N : Subgroup G, IsUniqueMaxOver H T N) →
      R ≠ ⊥ → R ≤ T → CFSG.QuasithinUnique.IsSylowTwoOf R (oTwoUpper H ⊔ R) →
      M₀ ≤ Subgroup.normalizer (R : Set G) →
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)

theorem input311Solvable_of (hG64 : C58.InputC512G64) : Input311Solvable := by
  intro G _ _ T hsimple hnonab hqtke hT M₀ H R hM₀ hH hsolv ⟨N, hN⟩ hR1 hRT hRsyl hM₀R
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hNC : C5.NoCommonNormal R H M₀ := fun X hXR hX1 hHX hM₀X =>
    hcon ⟨X, hX1, hXR, sup_le hM₀X hHX⟩
  have hT2 : IsPGroup 2 T := hT.1
  have hTH : T ≤ H := hH.1
  have hTsylH : IsSylowTwoOf T H :=
    ⟨hTH, hT2, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hTR : T ≤ normalizer (R : Set G) := hM₀.1.trans hM₀R
  set K := oTwoUpper H with hK
  have hKH : K ≤ H := oTwoUpper_le H
  have hKT : K ⊔ T = H := by
    rw [sup_comm, hK, ← F6.twoResidual_eq_oTwoUpper]; exact sup_twoResidual_eq hTsylH
  have hHKR : H ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) := by
    calc H = K ⊔ T := hKT.symm
      _ ≤ _ := sup_le (le_sup_left.trans Subgroup.le_normalizer)
        (fun t ht => C1.mem_normalizer_sup (le_normalizer_oTwoUpper H (hTH ht)) (hTR ht))
  by_cases hTn : H ≤ normalizer (T : Set G)
  ·
    have hle : T ⊓ (K ⊔ R) ≤ R := by
      refine IsSylowIn.le_of_normal (p := 2) hRsyl inf_le_right ?_ (hT2.to_le inf_le_left)
      refine (normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun y hy => ?_
      exact C5.mem_normalizer_inf (hTn ((sup_le hKH (hRT.trans hTH)) hy))
        (Subgroup.le_normalizer hy)
    have hReq : R = T ⊓ (K ⊔ R) := le_antisymm (le_inf hRT le_sup_right) hle
    refine hNC R le_rfl hR1 ?_ hM₀R
    rw [hReq]
    exact fun h hh => C5.mem_normalizer_inf (hTn hh) (hHKR hh)
  have hchar : CharTwo H := charTwo_of_inH hqtke.2.1 (hT2.toSylow hT.2) hH
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := fun p hp hp2 =>
    pRank_le_two_of_pCoreOf_ne_bot_cat hqtke hH.2 hp hp2
  obtain ⟨K₁, hcfg⟩ := C58.exists_blockConfig hT hTH hchar hN hTn hsolv hSQT hR1 hRT hRsyl hM₀.1
    hM₀R hNC
  obtain ⟨hns, x, -, hxN, hxU⟩ :=
    hcfg.exists_good_elt hNC hM₀.1 hM₀R hRT hTH hKT.ge hT
  obtain ⟨t, htT, htK⟩ := IsConcreteLE.not_le_iff_exists.mp hns
  exact (C58.GammaSetup.mk hcfg hT hqtke.2.1 hRT hTH htT htK hxN hxU).false_of_input hsimple
    hnonab hqtke hG64

end CFSG.Quasithin.EmptyFaithfulMultiple
