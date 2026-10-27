module

public import CFSG.Quasithin.Background.E1ElevenLift
public import CFSG.Quasithin.EmptyFaithful.E22PGen
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b

variable {G : Type} [Group G] [Finite G]

theorem inEFor_of_nParam_le_one {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTD : T ≤ D)
    (hD : nParam D ≤ 1) : InEFor 1 D T :=
  (nParam_le_iff (H := D) (n := 1) one_pos).mp (by exact_mod_cast hD) T
    (B6.isSylowTwoOf_mono hT hTD le_top)

theorem inEFor_top_of_coatom_nParam_conj {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hTD : T ≤ D) (hDn : nParam D ≤ 1) (hD : IsCoatom D)
    (hII : ∀ A : Subgroup G, A ≤ T → Nat.card A = 2 → IsE 1 ⊤ T A ⊤)
    (hK : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → 4 ≤ Nat.card A →
      ∃ g : G, A1b.conjSub g A ≤ T ∧ ∃ K : Subgroup G, IsE 1 ⊤ T (A1b.conjSub g A) K ∧
        ¬ K ≤ D) :
    InEFor 1 ⊤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine inEFor_top_of_noTwo hT hII ?_
  intro Ω hΩ h2
  by_cases h4 : ∃ A ∈ Ω, A ≤ T ∧ 4 ≤ Nat.card A
  · obtain ⟨A, hA, hAT, hA4⟩ := h4
    obtain ⟨g, hgT, K, hK1, hK2⟩ := hK A hAT (hΩ.isElemAbelian A hA) hA4
    have hA' : A1b.conjSub g A ∈ Ω := hΩ.conj A hA g (Subgroup.mem_top g)
    have hDX := le_eGen_sup_normalizer_of_inEFor hT hTD (inEFor_of_nParam_le_one hT hTD hDn) hΩ
    have hKX := (le_eGen hA' hgT hK1).trans (le_sup_left :
      eGen 1 ⊤ T Ω ≤ eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)))
    have hlt : D < eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) :=
      lt_of_le_of_ne hDX fun h => hK2 (h ▸ hKX)
    exact hD.2 _ hlt
  · push Not at h4
    have hW : weakClosure T Ω = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => ?_)
      have hp := isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA)
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have h4' := h4 A hA hAT
      have h2' := h2 A hA
      rcases k with _ | _ | k
      · exact le_bot_iff.mpr (Subgroup.card_eq_one.mp (by simpa using hk))
      · exact absurd (by simpa using hk) h2'
      · exfalso
        apply h4'.not_ge
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hW, Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq, sup_top_eq]

theorem nParam_le_one_of_quotient {N : Subgroup G} [N.Normal] (hN : Group.IsSolvable ↥N)
    (hQ : nParam (⊤ : Subgroup (G ⧸ N)) ≤ 1) : nParam (⊤ : Subgroup G) ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowIn_two (⊤ : Subgroup G)
  have hIH : InE 1 (⊤ : Subgroup (G ⧸ N)) :=
    (nParam_le_iff (H := (⊤ : Subgroup (G ⧸ N))) (n := 1) one_pos).mp (by exact_mod_cast hQ)
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hTs : Group.IsSolvable ↥T := by
    have := hT2.isNilpotent
    infer_instance
  have hNT : Group.IsSolvable ↥(N ⊔ T) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge) hN hTs
  have h := inEFor_of_quotient hIH hT fun Ω hΩ =>
    le_sup_left.trans (le_eGen_sup_normalizer_of_isSolvable hT le_sup_right hNT hΩ)
  have h' := (nParam_le_iff (H := (⊤ : Subgroup G)) (n := 1) one_pos).mpr
    ((inE_iff_inEFor hT).mpr h)
  simpa using h'

end CFSG.Quasithin.Vol2.Ch11.SecU1
