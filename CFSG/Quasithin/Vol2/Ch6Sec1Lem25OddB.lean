module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddA
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.Quasithin.Vol2.KGFactAutSylowA6
import CFSG.Quasithin.Vol2.KGFactAutSylowL2Sq
import CFSG.Quasithin.Vol2.Ch3Sec3FactAutL3Holds
import CFSG.LieType.SteinbergBROddSylowNormalizers
import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.Quasithin.H13

namespace OddSyl

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

variable {S : Type} [Group S]

theorem nonempty_psl_two_equiv_alt_five (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 4 ∨ Nat.card K = 5) :
    Nonempty (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega))
      (Or.inr (by omega))
  rcases hK with hK | hK
  · exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_four K hK)
  · exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (CFSG.ClassicalModels.projectiveSpecialLinear_two_card_of_card_five K hK)

theorem isPSL_two_two_two_of_alt_five {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 5)) :
    IsPSL 2 2 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e4⟩ := nonempty_psl_two_equiv_alt_five (GaloisField 2 2) (Or.inl (by rw [hc4]; norm_num))
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hc4,
    ⟨e.trans (e4.symm.trans (projectiveSpecialLinearGroupEquivStatedProj 2 (GaloisField 2 2)))⟩⟩

theorem isPSL_two_two_two_of_psl_two_five {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 5 1) : IsPSL 2 2 2 X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e5⟩ := nonempty_psl_two_equiv_alt_five K (Or.inr (by rw [hK, pow_one]))
  exact isPSL_two_two_two_of_alt_five
    (e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans e5))

theorem exists_projectiveSL_of_psl_two_one {n : ℕ} (hm : StatedClassicalModel S .PSL n 2 1) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ∧
      Nonempty (S ≃* LinearFlag.projectiveSL n k) := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := hm
  exact ⟨K, hF, hfin, by rw [hK, pow_one], ⟨e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K))⟩⟩

theorem false_of_small [Finite S] (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {P : Subgroup S} (hP : IsSylowTwoOf P ⊤) {d : MulAut S} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : orderOf d = r) (hdP : P.map d.toMonoidHom = P) (hx : ∃ x ∈ P, d x ≠ x)
    (hcase : (∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
      ∃ (n : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 3 ≤ n ∧ Nat.card k = 2 ∧
        Nonempty (S ≃* LinearFlag.projectiveSL n k)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  have hodd : Odd (orderOf d) := by
    rw [hd]
    exact hr.odd_of_ne_two hr2
  have h1 := (CFSG.LieType.small_alternating_and_binary_linear_odd_Sylow_normalizers_are_trivial
    S hS hna (hP.2.1.toSylow hidx) d hodd hdP hcase).2.2
  obtain ⟨x, -, hx⟩ := hx
  exact hx (by rw [h1]; rfl)

theorem mem_innAut_of_psl_two_one {p : ℕ} (hm : StatedClassicalModel S .PSL 2 p 1)
    {d : MulAut S} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hd : orderOf d = r) :
    d ∈ innAut S := by
  obtain ⟨⟨hp, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hout := (linear_two_outer_order_divisor hp K hK).2 S
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩
  refine mem_innAut_of_not_dvd hr hd fun h => hr2 ?_
  have h2 : r ∣ 2 := (h.trans hout).trans (by rw [one_mul]; exact Nat.gcd_dvd_left 2 _)
  exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2

theorem eq_three_and_mem_innAut_of_psl_two [Finite S] {p : ℕ} (hp : p.Prime)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (hm : StatedClassicalModel S .PSL 2 p 1) {P : Subgroup S}
    (hP : IsSylowTwoOf P ⊤) {d : MulAut S} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : orderOf d = r) (hdP : P.map d.toMonoidHom = P) (hx : ∃ x ∈ P, d x ≠ x) :
    r = 3 ∧ d ∈ innAut S :=
  ⟨eq_three_of_card_four (KGAutSyl.factL2pSylowFour_holds p hp h8 S hm P hP) hr hr2 hd hdP hx,
    mem_innAut_of_psl_two_one hm hr hr2 hd⟩

end OddSyl

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank OddSyl

theorem oddSylowNormalizerFact_of (hM11 : FactAutSylowM11) (hM12 : FactAutSylowM12)
    (hM22 : FactAutSylowM22) (hM23 : FactAutSylowM23) (hM24 : FactAutSylowM24)
    (hJ4 : FactAutSylowJ4) (hHS : FactAutSylowHS) (hRu : FactAutSylowRu)
    (hHe : ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .He Q → AutSylowSelfNorm Q)
    (hJ1 : OddSylowJ1) (hTits : OddSylowTits) (hJ2 : OddSylowJ2) (hD42 : OddSylowD42) :
    OddSylowNormalizerFact := by
  intro S _ _ hS hna hL P hP d r hr hr2 hd hdP hx hcent
  have hon : AutOddNormCent S → False := fun h =>
    false_of_autOddNormCent hS hna h hP hr hr2 hd hdP hx
  have hsn : AutSylowSelfNorm S → False := fun h => hon h.autOddNormCent
  have hlin : ∀ n, 3 ≤ n → StatedClassicalModel S .PSL n 2 1 → False := fun n hn hm => by
    obtain ⟨k, hk, hkf, hk2, he⟩ := exists_projectiveSL_of_psl_two_one hm
    exact false_of_small hS hna hP hr hr2 hd hdP hx (Or.inr ⟨n, k, hk, hkf, hn, hk2, he⟩)
  rcases hL with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p, hp, hp2, hL2⟩ | hc2 | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  ·
    rcases (by omega : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) with rfl | hn
    · exact Or.inl ⟨2, le_rfl, Or.inl (isPSL_two_two_two_of_alt_five e)⟩
    · exact (false_of_small hS hna hP hr hr2 hd hdP hx (Or.inl ⟨n, hn, ⟨e⟩⟩)).elim
  ·
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rcases hL2 with ⟨f, hf, hm⟩ | hm | hm
    · rcases hf with rfl | rfl
      · have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
        rcases h8 with h8 | h8 | h8 | h8
        · exact (hon (KGAutSyl.factAutOddL2pPlus_holds p hp (Or.inl h8) S hm)).elim
        · by_cases h3 : p = 3
          · subst h3
            exact (hm.1.2.2.2.2 (by norm_num)).elim
          · obtain ⟨h3', hinn⟩ :=
              eq_three_and_mem_innAut_of_psl_two hp (Or.inl h8) hm hP hr hr2 hd hdP hx
            exact Or.inr (Or.inr (Or.inr ⟨h3', hinn, p, hp, by omega, Or.inl h8, hm⟩))
        · by_cases h5 : p = 5
          · subst h5
            exact Or.inl ⟨2, le_rfl, Or.inl (isPSL_two_two_two_of_psl_two_five hm)⟩
          · obtain ⟨h3', hinn⟩ :=
              eq_three_and_mem_innAut_of_psl_two hp (Or.inr h8) hm hP hr hr2 hd hdP hx
            exact Or.inr (Or.inr (Or.inr ⟨h3', hinn, p, hp, by omega, Or.inr h8, hm⟩))
        · exact (hon (KGAutSyl.factAutOddL2pPlus_holds p hp (Or.inr h8) S hm)).elim
      · by_cases h3 : p = 3
        · subst h3
          exact (hsn (KGAutSyl.factAutSylowA6_holds S (Or.inr hm))).elim
        · exact (hsn (KGAutSyl.factAutSylowL2Sq_holds p hp (by omega) S hm)).elim
    · exact (hon (factAutL3Eps_holds S hS (Or.inr ⟨true, p, hp, by omega, hm⟩))).elim
    · exact (hon (factAutL3Eps_holds S hS (Or.inr ⟨false, p, hp, by omega, hm⟩))).elim
  ·
    rcases hc2 with ⟨f, h⟩ | hm
    · rcases h with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
        ⟨-, hf, hm⟩ | ⟨-, hf, hm⟩
      · exact Or.inl ⟨f, hf, Or.inl hm⟩
      · rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
        · exact (hlin 3 le_rfl hm).elim
        · exact Or.inl ⟨f, hf2, Or.inr (Or.inl hm)⟩
      · exact Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inl hm))⟩
      · exact Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inl hm)))⟩
      · exact Or.inl ⟨f, hf, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))⟩
      · rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
        · obtain ⟨h7, hinn⟩ := hD42 S hS hna hm P hP d r hr hr2 hd hdP hx hcent
          exact Or.inr (Or.inl ⟨h7, hinn, hm⟩)
        · exact Or.inl ⟨f, hf2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm)))))⟩
      · exact Or.inl ⟨f, by omega,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm))))))⟩
      · exact Or.inl ⟨f, by omega,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))))⟩
    · exact (hTits S hS hna hm P hP d r hr hr2 hd hdP hx hcent).elim
  ·
    exact (hlin n (by omega) hm).elim
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hsn (hM11 S ⟨e⟩)).elim
    · exact (hsn (hM12 S ⟨e⟩)).elim
    · exact (hsn (hM22 S ⟨e⟩)).elim
    · exact (hsn (hM23 S ⟨e⟩)).elim
    · exact (hsn (hM24 S ⟨e⟩)).elim
    · exact (hJ1 S hS hna ⟨e⟩ P hP d r hr hr2 hd hdP hx hcent).elim
    · obtain ⟨h3, hinn⟩ := hJ2 S hS hna ⟨e⟩ P hP d r hr hr2 hd hdP hx hcent
      exact Or.inr (Or.inr (Or.inl ⟨h3, hinn, ⟨e⟩⟩))
    · exact (hsn (hJ4 S ⟨e⟩)).elim
    · exact (hsn (hHS S ⟨e⟩)).elim
    · exact (hsn (hHe S ⟨e⟩)).elim
    · exact (hsn (hRu S ⟨e⟩)).elim

end CFSG.Quasithin.H13
