module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoF
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoG
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2NTwoH

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

section Certified


theorem false_of_u3 (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {n' : ℕ}
    (hPSU : IsPSUGp (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) 3 n')
    (hRoot : IsUnitaryRootGroup (hatX Mo V) 3 n' (hatS Mo V)) : False := by
  have hcard := c.card_hatS h1 h5 h15 hS Mo
  have hn' : E3.mQuot V (U ⊔ V₀) = n' :=
    Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hRoot.1)
  haveI : Group.IsPerfect ↥(hatK Mo V) := c.isPerfect_hatK hn h1 h5 h15 hS Mo
  haveI : Group.IsPerfect (hatX Mo V) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(hatK Mo V)))
  have hZ : Subgroup.center (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (hatX Mo V)
  have hPSU' : IsPSUGp ((hatX Mo V ⧸ Subgroup.center (hatX Mo V)) ⧸
      Subgroup.center (hatX Mo V ⧸ Subgroup.center (hatX Mo V))) 3 n' :=
    CFSG.Blueprint.LieModel.quotient_center hZ hPSU
  refine c.false_of_rank hn h1 h5 h15 hS Mo ?_ ?_
  · intro E hE
    rw [hn']
    exact hK.rank_U3 _ n' (hn' ▸ hn) hPSU' (by rw [hZ]; simp) E hE
  · intro E hE hE'
    exact hK.rank_out_U3 _ n' (hn' ▸ hn) hPSU E hE hE'

theorem false_of_A6 (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) (h1 : W16One G)
    (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B)
    (Mo : ModDataE H (conjClosure (U ⊔ V₀) H))
    (hA6 : SevenElevenASixShape (hatX Mo V) (hatS Mo V)) : False := by
  obtain ⟨⟨e⟩, hc4, -⟩ := hA6
  have hcard := c.card_hatS h1 h5 h15 hS Mo
  have hn2 : E3.mQuot V (U ⊔ V₀) = 2 := by
    have : 2 ^ E3.mQuot V (U ⊔ V₀) = 2 ^ 2 := by
      rw [← hcard, hc4]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  refine c.false_of_rank hn h1 h5 h15 hS Mo ?_ ?_
  · intro E hE
    have := rank_transport e hK.rank_A6 E hE
    rw [hn2]
    exact this
  · exact out_transport e hK.rank_out_A6

theorem false_of_symplectic_root (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀))
    (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {m n' : ℕ}
    (hRoot : IsSymplecticRootGroup (hatX Mo V) m n' (hatS Mo V)) : False := by
  obtain ⟨hcS, k, hmk, F, hFfield, hFfin, hF, e, htr⟩ := hRoot
  have hcard := c.card_hatS h1 h5 h15 hS Mo
  have hnn : E3.mQuot V (U ⊔ V₀) = n' :=
    Nat.pow_right_injective (le_refl 2) (hcard.symm.trans hcS)
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · have h1S : 1 < Nat.card (hatS Mo V) := by
        rw [hcard]
        exact Nat.one_lt_two_pow (by omega)
      haveI : Nontrivial (hatS Mo V) := Finite.one_lt_card_iff_nontrivial.1 h1S
      obtain ⟨w, hw1⟩ := exists_ne (1 : hatS Mo V)
      have h0 := htr w w.2 (fun h => hw1 (Subtype.ext h))
      unfold SevenK.IsSymplecticTransvectionIn at h0
      have h2 := Matrix.rank_le_card_height
        ((((e (QuotientGroup.mk (w : hatX Mo V)) : ↥(StatedSp 0 F)) : GL (Fin 0 ⊕ Fin 0) F) :
          Matrix (Fin 0 ⊕ Fin 0) (Fin 0 ⊕ Fin 0) F) - 1)
      simp at h2
      omega
    · refine c.false_of_card_hatBar hK hnn (hnn ▸ hn) h1 h5 h15 hS Mo (Or.inl ?_)
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
      simp only [Finset.Icc_self, Finset.prod_singleton, one_pow, pow_one, mul_one]
      congr 2
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
  · exact c.false_of_sp_root hK hn h1 h5 h15 hS Mo (by omega)
      ⟨hcS, k, hmk, F, hFfield, hFfin, hF, e, htr⟩

theorem false_of_unitary_root (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀))
    (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {m n' : ℕ}
    (hPSU : IsPSUGp (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) m n')
    (hRoot : IsUnitaryRootGroup (hatX Mo V) m n' (hatS Mo V)) : False := by
  have hm3 : 3 ≤ m := by
    have := CFSG.Blueprint.LieModel.admissible hPSU
    simp only [StatedLieAdmissible] at this
    exact this.2.2.1
  rcases Nat.eq_or_lt_of_le hm3 with h | h
  · subst h
    exact c.false_of_u3 hK hn h1 h5 h15 hS Mo hPSU hRoot
  · exact c.false_of_su_root hK hn h1 h5 h15 hS Mo (by omega) hRoot

theorem false_of_suzuki_root (hK : KFacts1234) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀))
    (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (Mo : ModDataE H (conjClosure (U ⊔ V₀) H)) {n' : ℕ}
    (hSz : SevenK.IsSzGp (hatX Mo V ⧸ Subgroup.center (hatX Mo V)) n')
    (hRoot : IsSuzukiRootGroup (hatX Mo V) (hatS Mo V)) : False := by
  have hodd := c.odd_card_center_hatX hn h1 h5 h15 hS Mo
  have hcard := c.card_hatS h1 h5 h15 hS Mo
  have h1' := hK.card_suzukiRoot (hatX Mo V) n' (hatS Mo V) hodd hSz hRoot
  have hnn : E3.mQuot V (U ⊔ V₀) = n' :=
    Nat.pow_right_injective (le_refl 2) (hcard.symm.trans h1')
  refine c.false_of_card_hatBar hK hnn (hnn ▸ hn) h1 h5 h15 hS Mo (Or.inr ?_)
  exact hK.card_SzGp _ n' hSz

theorem false_of_two_le_mQuot (hTim : TimmesfeldTIRootInput)
    (hGen : SevenK.TwoConjugateGeneration) (hCore : OddTranspositionCoreInputSC)
    (hList : OddTranspListBundle) (hIn : OrthReflParabolic) (hK : KFacts1234)
    (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) (hn : 2 ≤ E3.mQuot V (U ⊔ V₀)) : False := by
  obtain ⟨Mo⟩ := exists_modDataE (Fam16Q.isElemAbelian c.cex c.mem)
    (le_normalizer_conjClosure (U ⊔ V₀) H)
  have hcard := c.card_hatS h1 h5 h15 hS Mo
  have hne2 : Nat.card (hatS Mo V) ≠ 2 := by
    rw [hcard]
    intro h
    have h' : (2 : ℕ) ^ E3.mQuot V (U ⊔ V₀) = 2 ^ 1 := by simpa using h
    have := Nat.pow_right_injective (le_refl 2) h'
    omega
  rcases c.sevenElevenAlt_hat hTim hGen hCore hList hIn h1 h5 h15 hS Mo with
    ⟨⟨n', hRoot⟩, -⟩ | hLin | ⟨-, hA6⟩ | ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨h2, -⟩
  · rcases hRoot with ⟨m, -, hSp⟩ | ⟨m, hPSU, hU⟩ | ⟨hSz, hSzR⟩
    · exact c.false_of_symplectic_root hK hn h1 h5 h15 hS Mo hSp
    · exact c.false_of_unitary_root hK hn h1 h5 h15 hS Mo hPSU hU
    · exact c.false_of_suzuki_root hK hn h1 h5 h15 hS Mo hSz hSzR
  · exact c.false_of_linear hK hn h1 h5 h15 hS Mo hLin
  · exact c.false_of_A6 hK hn h1 h5 h15 hS Mo hA6
  · exact hne2 h2
  · exact hne2 h2
  · exact hne2 h2

end Certified

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
