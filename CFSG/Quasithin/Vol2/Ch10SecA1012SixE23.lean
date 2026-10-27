module

public import CFSG.Quasithin.Vol2.Ch10SecA1012SixMin
public import CFSG.Quasithin.Background.E2Three
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem card_quot_of_cases12
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    ∃ n, 2 ≤ n ∧ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
  rcases h12 with ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨⟨eA⟩, -⟩
  · exact ⟨n, hn, by rw [Nat.card_congr e.toEquiv, card_SL_two_pow hK]⟩
  · exact ⟨2, le_rfl, by rw [Nat.card_congr eA.toEquiv, card_alt 5 (by norm_num)]; decide⟩

theorem fsuV_eq_of_cases12
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    fsuV T I = fsuVM T L I := by
  obtain ⟨hab, -, -, -, -, -, hc⟩ := hyp.three
  rcases hc with ⟨-, h⟩ | ⟨-, h, -⟩ | ⟨⟨e⟩, -, -⟩
  · exact h
  · exact h
  · exfalso
    have := Vol2Native.A312L.Seven.slThree_isSimple
    obtain ⟨e'⟩ := nonempty_quot_equiv_of_autOn h37 h38 hyp e
    obtain ⟨n, hn, hcard⟩ := card_quot_of_cases12 h12
    rw [Nat.card_congr e'.toEquiv, card_SL_three_zmod_two] at hcard
    have hodd : Odd (4 ^ n - 1) := odd_four_pow_sub_one (by omega)
    obtain ⟨rfl, h⟩ := two_pow_mul_odd_inj hodd (by decide : Odd 21)
      (hcard.symm.trans (by norm_num : (168 : ℕ) = 2 ^ 3 * 21))
    norm_num at h

theorem pCoreOf_L0T_ne_bot (hyp : Ch10.Hyp10 G T L I) : pCoreOf 2 (fsuL0 T L ⊔ T) ≠ ⊥ := by
  have hVH : fsuVM T L I ≤ fsuL0 T L ⊔ T := (fsuVM_le_T hyp).trans le_sup_right
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVH hHN (isPGroup_fsuVM hyp)
  intro h
  rw [h] at hle
  exact fsuVM_ne_bot hyp.fsu (le_bot_iff.mp hle)

theorem sqtkGroup_L0T (hyp : Ch10.Hyp10 G T L I) : SQTKGroup ↥(fsuL0 T L ⊔ T) := by
  have := hyp.fsu.simple
  exact InternalSec.sqtkGroup_of_localSQTK (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
    (pCoreOf_L0T_ne_bot hyp)

theorem charTwo_L0T (hyp : Ch10.Hyp10 G T L I) : CharTwo (fsuL0 T L ⊔ T) := by
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have h := charTwo_of_inH hyp.fsu.qtke.2.1 S
    (H := fsuL0 T L ⊔ T) ⟨hS ▸ le_sup_right, pCoreOf_L0T_ne_bot hyp⟩
  exact h

theorem isTwoReducedIn_L0T (h3228 : TmpL6_3_2_2_eight) (hyp : Ch10.Hyp10 G T L I)
    (hVV : fsuV T I = fsuVM T L I) : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuVM T L I) := by
  obtain ⟨h1, h2, -⟩ := h3228 G T L I hyp.fsu
  rw [hVV] at h1 h2
  exact isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨h1, h2⟩

theorem e23Concl_L0T
    (he23 : E2.E23Statement) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hshape : Stmt7_0_1_shape) (h3228 : TmpL6_3_2_2_eight)
    (hyp : Ch10.Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) :
    E2.E23Concl (fsuL0 T L ⊔ T) T (fsuVM T L I) (isElemAbelian_fsuVM hyp) :=
  he23 G (fsuL0 T L ⊔ T) T ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (T0 T L : Set G))
    (fsuVM T L I) (isElemAbelian_fsuVM hyp)
    (minParabolic_L0T h37 h38 hyp (exists_SL_two_of_cases12 hshape hyp h12))
    (sqtkGroup_L0T hyp) (charTwo_L0T hyp)
    (isTwoReducedIn_L0T h3228 hyp (fsuV_eq_of_cases12 h37 h38 hyp h12)) hJ

end CFSG.Quasithin.Vol2.Ch10.SecA
