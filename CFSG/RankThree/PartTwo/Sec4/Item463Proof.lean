module

public import CFSG.RankThree.PartTwo.Sec4.Item462Proof
public import CFSG.RankThree.PartTwo.Sec4.Item463ProofTools
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofThirteen
import CFSG.RankThree.PartTwo.Sec4.Item422Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Item463Proof

@[expose] def Alt423T
    {G : Type} [Group G] [Finite G]
    (A L : Subgroup G) : Prop :=
  (Sec8.IsZ3LThreePi (thetaImage (L ⊔ A)) ∧
      (Nonempty (autIn L A ≃* QuaternionGroup 2) ∨
        Nonempty (autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
    (Sec8.IsZ3PGLThreePi (thetaImage (L ⊔ A)) ∧
      Nonempty (autIn L A ≃* Multiplicative (ZMod 3)) ∧
      ∃ a ∈ A, a ≠ 1 ∧ InducesTypeOn L a 3) ∨
    (IsHeisCentral (thetaImage (L ⊔ A)) (L ⧸ aschbacherSolvableCore 3 L) ∧
      (IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
        IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22 ∨
        IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L)) ∧
      CFSG.Assembly.IsElemAbelian 3 (autIn L A) ∧ Nat.card (autIn L A) = 9) ∨
    (IsSLThreePiTwo (thetaImage (L ⊔ A)) ∧
      Nonempty (autIn L A ≃* Multiplicative (ZMod 3))) ∨
    ∃ a ∈ A, a ≠ 1 ∧
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField)

theorem nonempty_solvableRadical_mulEquiv {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* S) :
    haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
    Nonempty (L ⧸ solvableRadical L ≃* S) := by
  have : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1
  obtain ⟨eR⟩ := Sec10.Sec10XProof.nonempty_quotient_center_mulEquiv (Y := L) hL.2.2
  have hsL : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := by
    have := hS
    exact e.isSimpleGroup
  obtain ⟨-, -, x, y, hxy⟩ := hL.2.2
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
    rcases hsL.eq_bot_or_eq_top_of_normal (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))
      with h | h
    · exact h
    · exfalso
      apply hxy
      obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y') x']
  have e0 : (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)
      ≃* L ⧸ aschbacherSolvableCore 3 L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨(eR.symm.trans e0).trans e⟩

theorem list_or_alt423T_of_alt423
    {G : Type} [Group G] [Finite G] {A L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (h : Item462Proof.Alt423 A L) :
    (haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
      Nonempty (L ⧸ solvableRadical L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M12) ∨
        Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M22) ∨
        (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
          IsoLThreePi (L ⧸ solvableRadical L) p e) ∨
        Nonempty (L ⧸ solvableRadical L ≃* projSL 2 (GaloisField 3 3))) ∨
      Alt423T A L := by
  have hA7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  rcases h with h1 | h2 | h3 | h4 | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨hM | hJ, -⟩ | h8
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h4))))
  · obtain ⟨e'⟩ := Item462Proof.nonempty_mulEquiv_of_thetaImage hL hAL hA7 e
    exact Or.inl (Or.inl (nonempty_solvableRadical_mulEquiv hL hA7 e'))
  · have hS := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    obtain ⟨e'⟩ := Item462Proof.nonempty_mulEquiv_of_thetaImage hL hAL hS e
    exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (nonempty_solvableRadical_mulEquiv hL hS e')))))
  · obtain ⟨e⟩ := hM
    have hS := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    obtain ⟨e'⟩ := Item462Proof.nonempty_mulEquiv_of_thetaImage hL hAL hS e
    exact Or.inl (Or.inr (Or.inl (nonempty_solvableRadical_mulEquiv hL hS e')))
  · obtain ⟨e⟩ := hJ
    have hS := CFSG.Sporadic.J2.isSimpleGroup_J2
    obtain ⟨e'⟩ := Item462Proof.nonempty_mulEquiv_of_thetaImage hL hAL hS e
    exact Or.inl (Or.inr (Or.inr (Or.inl (nonempty_solvableRadical_mulEquiv hL hS e'))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h8))))

end Item463Proof

@[expose] noncomputable def Step463Alt :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    ∀ a ∈ A, a ∈ Subgroup.center G → a ≠ 1 → Odd (Nat.card (aschbacherSolvableCore 3 G)) →
    ∀ B : Subgroup G, a ∈ B → B ≤ A → Nat.card B = 9 →
    ∀ U : Subgroup G, IsPGroup 2 U → U ≠ ⊥ → A ≤ Subgroup.normalizer (U : Set G) →
      ⁅U, A⁆ = U →
      U ≤ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)), A⁆ →
    ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G) →
      U ≤ Subgroup.normalizer (L : Set G) → ⁅L, U⁆ = L → U ≤ L ⊔ thetaQuotCentralizer L →
      Nat.card (autThetaQuot A L) = 9 → Item463Proof.Alt423T A L →
      (∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e) →
      haveI : (solvableRadical L).Normal := Subgroup.normal_sSup _ fun _ hN => hN.1;
      Nonempty (L ⧸ solvableRadical L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M12) ∨
        Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ solvableRadical L ≃* Blueprint.NativeSporadic.M22) ∨
        (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
          IsoLThreePi (L ⧸ solvableRadical L) p e) ∨
        Nonempty (L ⧸ solvableRadical L ≃* projSL 2 (GaloisField 3 3))

section Main

theorem item463Inv_of (h45 : Item4_5) (h41 : Item4_1LargePrime)
    (hKF : KFacts.OutFixCentralThreeAbelian46Rank) (h49 : Item4_9) (h47 : Item4_7W)
    (h423 : Item4_23) (hAlt : Step463Alt) : Sec10.Item463Inv := by
  intro G _ _ hS4 A hmax h27 a haA haZ ha1 hodd B hBA hB9 hev
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  set H := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer (B : Set G)) with hHdef
  have hAB : A ≤ Subgroup.centralizer (B : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hBA hy⟩ ⟨x, hx⟩)
  have hAH : A ≤ Subgroup.normalizer (H : Set G) := hAB.trans (Sec6.le_normalizer_theta _)
  have h2 : 2 ∣ Nat.card (⁅H, A⁆ : Subgroup G) := even_iff_two_dvd.mp hev
  have haB : a ∈ B := by
    by_contra haB
    have hCA : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (A : Set G) :=
      (Item462Proof.centralizer_eq_of_not_mem hBA h27 hB9 haA haZ ha3 haB).le
    have hbot : ⁅H, A⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((Sec6.theta_le _).trans hCA)
    rw [hbot, Subgroup.card_bot] at h2
    norm_num at h2
  obtain ⟨b, hbB, hba, hCB⟩ := Item462Proof.exists_centralizer_eq hB9
    (fun x hx => hAe.2 x (hBA hx)) haB haZ ha3
  obtain ⟨hHs, hH3⟩ := Item422Proof.inSubgroup_theta_solvable_coprime
    (Subgroup.centralizer (B : Set G))
  obtain ⟨U, hUle, hU2, hU1, hAU, hUA⟩ :=
    Item463Proof.exists_isPGroup_two_le_commutator hAp hH3 hHs hAH h2
  have hUθ : ¬ U ≤ aschbacherSolvableCore 3 G := by
    intro hle
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hU1 (Subgroup.eq_bot_of_card_eq U hk)
    have hdvd : 2 ∣ Nat.card (aschbacherSolvableCore 3 G) :=
      (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hle)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hUle' : U ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({b} : Set G)), A⁆ := by
    rw [← hCB]
    exact hUle
  obtain ⟨L, hL, hAL, hUN, hUC, h9, hα, hCA⟩ :=
    Item462Proof.exists_thetaComponent_of_le_commutator
    h45 h41 hKF hS4 hmax h27 haA haZ ha1 (hBA hbB) hba hUle' hUθ
  have hLU : ⁅L, U⁆ = L := Sec6.commutator_eq_of_not_le_theta hL.1 hL.2.2 hUN
    (fun h => hUC ((Sec6.commutator_le_theta_iff hUN).mp h))
  have h3Z : 3 ∣ Nat.card (Subgroup.center G) := by
    have h : orderOf (⟨a, haZ⟩ : Subgroup.center G) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact ha3
    rw [← h]
    exact orderOf_dvd_natCard _
  have hfix : ∀ K ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (K : Set G) := fun K hK =>
    h45 G hS4 A hAp (Or.inr ⟨hAe, 3, le_rfl, by rw [h27]; norm_num⟩) K hK
  have hUinv : U ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hU2, hAU⟩
  have hUcomm : ⁅A, U⁆ = U := by
    rw [Subgroup.commutator_comm]
    exact hUA
  have hUs : U ≤ L ⊔ thetaQuotCentralizer L := h49 G hS4 h3Z L hL A hAp hfix U hUinv hUcomm
  have hAlt423 := Item462Proof.alt423_of h423 hS4 hmax h27 haA haZ ha1 hL h9 hα
  have h47' : ∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e :=
    fun e _ he3 hout => h47 G hS4 h3Z L hL e he3 hout
  have hlist := (Item463Proof.list_or_alt423T_of_alt423 hL hAL hAlt423).elim id fun hT =>
    hAlt G hS4 A hmax h27 a haA haZ ha1 hodd B haB hBA hB9 U hU2 hU1 hAU hUA hUle
      L hL hAL hUN hLU hUs h9 hT h47'
  obtain ⟨V, hV, hV1⟩ := Item463Proof.exists_invariant_twoSubgroup_of_le_sup hAp hAL hUN hU2
    hAU hUs hUC
  exact ⟨L, hL, hlist, V, hV, hV1⟩

end Main

end CFSG.RankThree.PartTwo.Sec4
