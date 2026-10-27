module

public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.RankThree.PartTwo.Sec4.Item462ProofNormal
public import CFSG.RankThree.PartTwo.Sec4.Item462ProofD
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Sporadic.J2
import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

namespace Item462Proof

@[expose] def Alt423
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
    (Nonempty (thetaImage (L ⊔ A) ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 7)) ∧
      Nonempty (autIn L A ≃* Multiplicative (ZMod 4))) ∨
    (Nonempty (thetaImage (L ⊔ A) ≃*
        Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M22) ∧
      Nonempty (autIn L A ≃* QuaternionGroup 2)) ∨
    ((Nonempty (thetaImage (L ⊔ A) ≃*
          Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
        Nonempty (thetaImage (L ⊔ A) ≃*
          Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
      Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
    ∃ a ∈ A, a ≠ 1 ∧
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField)

section Alt


theorem alt423_of (h423 : Item4_23) {G : Type} [Group G] [Finite G] (hS4 : SectionFourHyp G)
    {A : Subgroup G} (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) (h9 : Nat.card (autThetaQuot A L) = 9)
    (hα : thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥) :
    Alt423 A L :=
  h423 G hS4 A hmax h27 a haA haZ ha1 L hL h9 hα

@[expose] def Alt423R {G : Type} [Group G] [Finite G] (A L : Subgroup G) : Prop :=
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
    ((Nonempty (thetaImage (L ⊔ A) ≃*
          Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
        Nonempty (thetaImage (L ⊔ A) ≃*
          Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) ∧
      Nonempty (autIn L A ≃* Equiv.Perm (Fin 3))) ∨
    ∃ a ∈ A, a ≠ 1 ∧
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField)

theorem alt423R_of_alt423 {G : Type} [Group G] [Finite G] {A D L : Subgroup G} {a : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1) (hDA : D ≤ A) (hD3 : Nat.card D = 3)
    (haD : a ∉ D) (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    (h : Alt423 A L) : Alt423R A L := by
  have hno : ∀ {X : Type} [Group X] (g : X), g ^ 4 = 1 → g ^ 2 ≠ 1 →
      ¬ Nonempty (autIn L A ≃* X) := by
    rintro X _ g hg4 hg2 ⟨e⟩
    have hσ4 : (e.symm g) ^ 4 = 1 := by rw [← map_pow, hg4, map_one]
    have h2 := sq_eq_one_of_mem_autIn hAe h27 haA haZ ha1 hDA hD3 haD hND (e.symm g).2
      (by rw [← Subgroup.coe_pow, hσ4, Subgroup.coe_one])
    have hσ2 : (e.symm g) ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h2, Subgroup.coe_one])
    apply hg2
    rw [← e.apply_symm_apply g, ← map_pow, hσ2, map_one]
  have hQ := hno (QuaternionGroup.xa 0 : QuaternionGroup 2) (by decide) (by decide)
  have hS := hno (X := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ⟨!![0, 2; 1, 0], by decide⟩
    (by decide) (by decide)
  have hZ4 := hno (Multiplicative.ofAdd (1 : ZMod 4)) (by decide) (by decide)
  rcases h with ⟨-, hq | hs⟩ | h2 | h3 | h4 | ⟨-, h5⟩ | ⟨-, h6⟩ | h7 | h8
  · exact absurd hq hQ
  · exact absurd hs hS
  · exact Or.inl h2
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h4))
  · exact absurd h5 hZ4
  · exact absurd h6 hQ
  · exact Or.inr (Or.inr (Or.inr (Or.inl h7)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h8)))

@[expose] def Alt423S {G : Type} [Group G] [Finite G] (A L : Subgroup G) : Prop :=
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

theorem list_or_alt423S_of_alt423R
    {G : Type} [Group G] [Finite G] {A L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (h : Alt423R A L) :
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
      Alt423S A L := by
  rcases h with h2 | h3 | h4 | ⟨hM | hJ, -⟩ | h8
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
  · obtain ⟨e⟩ := hM
    exact Or.inl (Or.inr (nonempty_mulEquiv_of_thetaImage hL hAL
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2 e))
  · obtain ⟨e⟩ := hJ
    exact Or.inl (Or.inl (nonempty_mulEquiv_of_thetaImage hL hAL
      CFSG.Sporadic.J2.isSimpleGroup_J2 e))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h8)))

end Alt

end Item462Proof

@[expose] noncomputable def Step462Alt :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    ∀ a ∈ A, a ∈ Subgroup.center G → a ≠ 1 →
    ∀ B : Subgroup G, a ∈ B → B ≤ A → Nat.card B = 9 →
    ∀ U : Subgroup G, IsKleinFour U → ⁅U, A⁆ = U →
      U = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (B : Set G)) →
    ∀ D : Subgroup G, D ≤ A → B ⊓ D = ⊥ → B ⊔ D = A →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G) →
      CFSG.Open.pRank 3 (Subgroup.centralizer (A : Set G)) = 3 →
    ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G) →
      U ≤ Subgroup.normalizer (L : Set G) → ⁅L, U⁆ = L → U ≤ L ⊔ thetaQuotCentralizer L →
      Nat.card (autThetaQuot A L) = 9 → Item462Proof.Alt423S A L →
      (∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e) →
      (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
        (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∧
          ∃ e ∈ B, InducesOuterTheta e L)

@[expose] def Step462UAlpha : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ A : Subgroup G,
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A → Nat.card A = 27 →
    ∀ a ∈ A, a ∈ Subgroup.center G → a ≠ 1 →
    ∀ B : Subgroup G, a ∈ B → B ≤ A → Nat.card B = 9 →
    ∀ U : Subgroup G, IsKleinFour U → ⁅U, A⁆ = U →
      U = inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (B : Set G)) →
    ∀ D : Subgroup G, D ≤ A → B ⊓ D = ⊥ → B ⊔ D = A →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G) →
      CFSG.Open.pRank 3 (Subgroup.centralizer (A : Set G)) = 3 →
    ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G) → U ≤ L → ⁅L, U⁆ = L →
      (∀ g : G, g ∈ Subgroup.normalizer (L : Set G)) →
      (∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a) →
      ((Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
        (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∧
          ∃ e ∈ B, InducesOuterTheta e L)) →
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (U : Set G)) ≤
        U ⊔ thetaQuotCentralizer L

theorem Item462Proof.maximal_of_pRank_centralizer {G : Type} [Group G] [Finite G]
    {A : Subgroup G} (hA : Late.IsE27 A)
    (hrk : CFSG.Open.pRank 3 (Subgroup.centralizer (A : Set G)) = 3) :
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hA.1, fun E hE hAE => ?_⟩
  have hEC : E ≤ Subgroup.centralizer (A : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨y, hAE hy⟩ ⟨x, hx⟩)
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hk3 : k ≤ 3 := by
    rw [← hrk]
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEC, hE, hk⟩
    rintro _ ⟨F, -, -, hF⟩
    calc _ ≤ 3 ^ _ := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card F := hF.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group F
  have hcard : Nat.card E ≤ Nat.card A := by
    rw [hk, hA.2]
    calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 27 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hAE hcard).symm.le

section Main


theorem item4_62_of (h45 : Item4_5) (h41 : Item4_1LargePrime)
    (hKF : KFacts.OutFixCentralThreeAbelian46Rank) (h49 : Item4_9) (h47 : Item4_7W)
    (h423 : Item4_23) (hAlt : Step462Alt) (hUα : Step462UAlpha) : Item4_62 := by
  intro G _ _ hS4 A hA a haA haZ ha1 B hBA hB9 U hU hUA hUO D hDA hBD hBDA hND hrk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := hA.1
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hmax := Item462Proof.maximal_of_pRank_centralizer hA hrk
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  have hUB : U ≤ Subgroup.centralizer (B : Set G) := by
    rw [hUO]
    exact Subgroup.map_subtype_le _
  have hU4 : Nat.card U = 4 := @IsKleinFour.card_four _ _ hU
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU4
    norm_num at hU4
  have haB : a ∈ B := Item462Proof.mem_of_le_centralizer_of_commutator_eq hBA hA.2 hB9 haA haZ
    ha3 hUB hUA hU1
  obtain ⟨b, hbB, hba, hCB⟩ := Item462Proof.exists_centralizer_eq hB9
    (fun x hx => hAe.2 x (hBA hx)) haB haZ ha3
  by_cases hUθ : U ≤ aschbacherSolvableCore 3 G
  · exact Or.inl hUθ
  right
  have hUθb : U ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
    rw [hUO, hCB]
    exact Item462Proof.inSubgroup_pCore_two_le_theta _
  have hUle : U ≤ ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)),
      A⁆ :=
    calc U = ⁅U, A⁆ := hUA.symm
      _ ≤ _ := Subgroup.commutator_mono hUθb le_rfl
  obtain ⟨L, hL, hAL, hUN, hUC, h9, hα, hCA⟩ :=
    Item462Proof.exists_thetaComponent_of_le_commutator
    h45 h41 hKF hS4 hmax hA.2 haA haZ ha1 (hBA hbB) hba hUle hUθ
  have hLU : ⁅L, U⁆ = L := Sec6.commutator_eq_of_not_le_theta hL.1 hL.2.2 hUN
    (fun h => hUC ((Sec6.commutator_le_theta_iff hUN).mp h))
  have h3Z : 3 ∣ Nat.card (Subgroup.center G) := by
    have h : orderOf (⟨a, haZ⟩ : Subgroup.center G) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact ha3
    rw [← h]
    exact orderOf_dvd_natCard _
  have hfix : ∀ K ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (K : Set G) := fun K hK =>
    h45 G hS4 A hAp (Or.inr ⟨hAe, 3, le_rfl, by rw [hA.2]; norm_num⟩) K hK
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU4]; norm_num)
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    rw [← hUA]
    exact Sec6.le_normalizer_commutator_right U A
  have hUinv : U ∈ invariantPiSubgroups ⊤ A (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hU2, hAU⟩
  have hUcomm : ⁅A, U⁆ = U := by
    rw [Subgroup.commutator_comm]
    exact hUA
  have h49' : U ≤ L ⊔ thetaQuotCentralizer L := h49 G hS4 h3Z L hL A hAp hfix U hUinv hUcomm
  have hBDc : Nat.card (B ⊔ D : Subgroup G) = Nat.card B * Nat.card D := by
    refine GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B D ?_
      (disjoint_iff.mpr hBD)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxy : ∀ y ∈ B, x * y * x⁻¹ = y := fun y hy => by
      have hc : x * y = y * x := congrArg Subtype.val (hAe.1.1.comm ⟨x, hDA hx⟩ ⟨y, hBA hy⟩)
      rw [hc, mul_inv_cancel_right]
    constructor
    · intro hy
      rw [hxy y hy]
      exact hy
    · intro hy
      have hyA : y ∈ A := by
        have := A.mul_mem (A.mul_mem (A.inv_mem (hDA hx)) (hBA hy)) (hDA hx)
        rwa [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
      have hc : x * y = y * x := congrArg Subtype.val (hAe.1.1.comm ⟨x, hDA hx⟩ ⟨y, hyA⟩)
      rwa [hc, mul_inv_cancel_right] at hy
  have hD3 : Nat.card D = 3 := by
    rw [hBDA, hA.2, hB9] at hBDc
    omega
  have haD : a ∉ D := fun h => ha1 (by
    have hmem : a ∈ B ⊓ D := ⟨haB, h⟩
    rwa [hBD, Subgroup.mem_bot] at hmem)
  have hAlt423 := Item462Proof.alt423R_of_alt423 hAe hA.2 haA haZ ha1 hDA hD3 haD hND
    (Item462Proof.alt423_of h423 hS4 hmax hA.2 haA haZ ha1 hL h9 hα)
  have h47' : ∀ e ∈ A, orderOf e = 3 → InducesOuterTheta e L → Alt47W L e :=
    fun e _ he3 hout => h47 G hS4 h3Z L hL e he3 hout
  have hlist : (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
      (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 3)) ∧
        ∃ e ∈ B, InducesOuterTheta e L) := by
    rcases Item462Proof.list_or_alt423S_of_alt423R hL hAL hAlt423 with h7 | hS
    · exact Or.inl h7
    · exact hAlt G hS4 A hmax hA.2 a haA haZ ha1 B haB hBA hB9 U hU hUA hUO D hDA hBD hBDA hND hrk
        L hL hAL hUN hLU h49' h9 hS h47'
  have hUL' : U ≤ L := Item462Proof.le_of_list hmax haZ hBA hUB hUA hL hAL hUN hCA hlist
  have hLG : ∀ g : G, g ∈ Subgroup.normalizer (L : Set G) :=
    Item462Proof.mem_normalizer_of_list hS4 hmax hA.2 haA haZ ha1 hL hAL hUL' hU2 hAU hUθ hCA
      (hlist.imp_right And.left)
  have hYα := hUα G hS4 A hmax hA.2 a haA haZ ha1 B haB hBA hB9 U hU hUA hUO D hDA hBD hBDA
    hND hrk L hL hAL hUL' hLU hLG hCA hlist
  have hcent := Item462Proof.commutator_le_theta_of_le_sup hS4 hmax haZ ha3 hBA hUB hL hAL hUL'
    hCA hlist hYα
  refine ⟨L, hL, hUL', ?_, hcent⟩
  rcases hlist with (hJ | hM) | ⟨h27', -⟩
  · exact Or.inr (Or.inl hJ)
  · exact Or.inr (Or.inr hM)
  · exact Or.inl h27'

end Main

end CFSG.RankThree.PartTwo.Sec4
