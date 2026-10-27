module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps63Main
public import CFSG.Walter.Cited.PSL2Small

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem exists_even_orderOf_ne_two_of_psl2 {W : Type} [Group W] {p e : ℕ} (hp : p ≠ 2)
    (hq : 7 ≤ p ^ e) (h : StatedClassicalModel W .PSL 2 p e) :
    ∃ x : W, Even (orderOf x) ∧ orderOf x ≠ 2 := by
  obtain ⟨hp', he, -⟩ := h.1
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eW⟩⟩ := h.2
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fact p.Prime := ⟨hp'⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : W ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    eW.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, e, hp', hp'.odd_of_ne_two hp, by omega, hKcard⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) 2
    (CFSG.Walter.Suzuki.two_dvd_card_psl2 K hKodd)
  obtain ⟨n, hn4, hneven, -, ⟨c⟩⟩ :=
    CFSG.Walter.psl2_centralizer_involution_dihedral (K := K) hKcard
      (hp'.odd_of_ne_two hp) (by omega) hq ht
  let C : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Subgroup.centralizer ({t} : Set _)
  let y : C := c.symm (DihedralGroup.r 1)
  have hy : orderOf (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = n := by
    simp only [y, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
  refine ⟨φ.symm (y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, hy]
    exact hneven
  · rw [MulEquiv.orderOf_eq, hy]
    omega

theorem asch6_3_mem_normalizer_of_psl2 {Q : Type} [Group Q] [Finite Q] {V : Type} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {ρ : Q →* MulAut V} (hρ : Function.Injective ρ) {a : Q}
    {L A : Subgroup Q} (ha : orderOf a = 2) (hL : IsComponentOf L ⊤) (hA : Nat.card A = 4)
    (hA2 : IsElemAbelian 2 A) (haA : a ∈ A)
    (hAV : ∀ b ∈ A, ∀ v : V, ρ b (ρ a v * v⁻¹) = ρ a v * v⁻¹)
    (hAL : A ⊓ centralizer (L : Set Q) = ⊥) {p e : ℕ} (hp : p ≠ 2) (hq : 7 ≤ p ^ e)
    (hLq : StatedClassicalModel (↥L ⧸ center ↥L) .PSL 2 p e) :
    a ∈ normalizer (L : Set Q) :=
  asch6_3Even_holds Q V hV ρ hρ a L A ha hL hA hA2 haA hAV hAL
    (exists_even_orderOf_ne_two_of_psl2 hp hq hLq)

end CFSG.LocalAnalysis.WeakClosure81

end
