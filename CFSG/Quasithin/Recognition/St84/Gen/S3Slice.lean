module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceSolv

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique

section Small

open scoped MatrixGroups

private theorem card_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 := by
  open Polynomial in
  have : IsSplittingField (ZMod 2) (GaloisField 2 0) (X ^ 2 ^ 0 - X : (ZMod 2)[X]) :=
    inferInstanceAs (IsSplittingField (ZMod 2) (SplittingField (X ^ 2 ^ 0 - X : (ZMod 2)[X])) _)
  have hadj := Polynomial.IsSplittingField.adjoin_rootSet (GaloisField 2 0)
    (Polynomial.X ^ 2 ^ 0 - Polynomial.X : (ZMod 2)[X])
  have h : (Polynomial.X ^ 2 ^ 0 - Polynomial.X : (ZMod 2)[X]) = 0 := by simp
  rw [h, Polynomial.rootSet_zero, Algebra.adjoin_empty] at hadj
  have hsurj : Function.Surjective (algebraMap (ZMod 2) (GaloisField 2 0)) := fun x =>
    Algebra.mem_bot.mp (hadj ▸ Algebra.mem_top)
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨(algebraMap (ZMod 2) _).injective, hsurj⟩),
    Nat.card_zmod]

private theorem isSolvable_psl_galoisField_two_zero :
    Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 0)) := by
  classical
  let _ : Fintype (GaloisField 2 0) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 0) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_galoisField_two_zero
  have hcard : Nat.card (SL(2, GaloisField 2 0)) = 6 := by
    rw [Matrix.card_SL_field 2, hq]
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    norm_num
  have : IsZGroup (SL(2, GaloisField 2 0)) := IsZGroup.of_squarefree (by rw [hcard]; decide +kernel)
  exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)

theorem two_le_of_isL2Quot_of_vBig {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ}
    (hL : IsRankOneListed (oTwoQuot ↥L)) (hb : VBig L) (h : IsL2Quot n (oTwoQuot ↥L)) :
    2 ≤ n := by
  rcases n with _ | _ | n
  · obtain ⟨e⟩ := h
    have : Group.IsSolvable (oTwoQuot ↥L) :=
      have := isSolvable_psl_galoisField_two_zero
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact absurd (isSolvable_vertex_of_oTwoQuot this) (VBig.not_isSolvable hL hb)
  · exact absurd (Or.inl (isL2Quot_one_iff_perm3.1 h)) hb
  · omega

end Small


@[expose] def IdS3L8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VS3 L1 → IsL2Quot 3 (oTwoQuot ↥L2) →
      IsAmalgamOfGroup (f112Amalgam L2 L1 S) (IsLieOverTwo .trialityD4 0 1)

@[expose] def Y9D42 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → IsL2Quot 3 (oTwoQuot ↥L1) → VS3 L2 →
      IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 1) →
        (centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
            centerOf S ≤ Subgroup.centralizer (L1 : Set G)) ∧
          IsSpecialPow 2 (2 ^ 1) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
          Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ 1) ^ 11

@[expose] def NoS3L2Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G) (n : ℕ),
    F112Hyp L1 L2 S → VS3 L1 → 4 ≤ n → IsL2Quot n (oTwoQuot ↥L2) → False

theorem f112ConclC_of_S3L2 (hS : IdS3A5) (hU : Y9U42) (hJ : Y9J2) (hAJ : Y9AutJ2)
    (hD : IdS3L8) (hY : Y9D42) (hN : NoS3L2Big) {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (hb : VBig L2) {n : ℕ}
    (hn : IsL2Quot n (oTwoQuot ↥L2)) : F112ConclC L1 L2 S := by
  have h2 := two_le_of_isL2Quot_of_vBig hF.1.h2.listed hb hn
  rcases (by omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | h4
  · exact f112ConclC_of_S3A5 hS hU hJ hAJ G L1 L2 S hF h1 hn
  · have hA := hD G L1 L2 S hF h1 hn
    obtain ⟨hz, hs, hc⟩ := hY G L2 L1 S hF.symm hn h1 hA
    refine ⟨L2, L1, Or.inr ⟨rfl, rfl⟩, fun h' => h'.elim hz id, ?_, ?_⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨1, le_rfl, hA, hn, hs, isL2Quot_one_iff_perm3.2 h1, hc⟩)))
    · iterate 4 right
      exact Or.inl hA
  · exact (hN G L1 L2 S n hF h1 h4 hn).elim

theorem f112SliceS3L2_of_parts (hS : IdS3A5) (hU : Y9U42) (hJ : Y9J2) (hAJ : Y9AutJ2)
    (hD : IdS3L8) (hY : Y9D42) (hN : NoS3L2Big) : F112SliceS3L2 F112ConclPredC := by
  intro G _ _ L1 L2 S hF hp hL
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨n, hn⟩ := hL L2 (Or.inr rfl) h2
    exact f112ConclC_of_S3L2 hS hU hJ hAJ hD hY hN hF h1 h2 hn
  · obtain ⟨n, hn⟩ := hL L1 (Or.inl rfl) h1
    exact (f112ConclC_of_S3L2 hS hU hJ hAJ hD hY hN hF.symm h2 h1 hn).symm

end CFSG.Quasithin.F112R
