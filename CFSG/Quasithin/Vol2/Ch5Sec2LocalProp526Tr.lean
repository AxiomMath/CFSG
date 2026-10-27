module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Am
public import CFSG.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Setting
public import CFSG.Quasithin.Vol2.Ch11SecSQuot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Entries

variable {G : Type} [Group G]

@[expose] def F112E3 (L1 L2 S : Subgroup G) : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
      (IsG2Over f) ∧
    IsL2Quot f (oTwoQuot ↥L1) ∧ IsL2Quot f (oTwoQuot ↥L2) ∧
    IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ S)) ∧ Nat.card (pCoreOf 2 (L2 ⊔ S)) = (2 ^ f) ^ 5

@[expose] def F112E4 (L1 L2 S : Subgroup G) : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
      (IsLieOverTwo .trialityD4 0 f) ∧
    IsL2Quot (3 * f) (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 L1) ∧
    IsL2Quot f (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 L2) = (2 ^ f) ^ 11

@[expose] def F112E6 (L1 L2 S : Subgroup G) : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧
    (IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
        (IsLieOverTwo .PSU 4 f) ∨
      IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))) ∧
    IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L1) ∧
    IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 f

@[expose] def F112E6Ext (L1 L2 S : Subgroup G) : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧
    IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) ∧
    IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L1) ∧
    IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧ IsOmega4MinusType L2 f

theorem F112E6Ext.e6 {L1 L2 S : Subgroup G} (h : F112E6Ext L1 L2 S) : F112E6 L1 L2 S := by
  obtain ⟨f, hf, hext, h1, h2, h3, h4, h5⟩ := h
  exact ⟨f, hf, Or.inr hext, h1, h2, h3, h4, h5⟩

theorem bigB_swap (L1 L2 S : Subgroup G) : bigB L2 L1 S = bigB L1 L2 S := by
  unfold bigB
  rw [sup_comm (borelOf L2 S)]

end Entries

@[expose] def Stmt5_2_6_orient : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → ¬ Group.IsSolvable ↥L2 →
    (F112E3 L1 L2 S ∨ F112E4 L1 L2 S ∨ F112E6 L1 L2 S) →
      centerOf S ≤ Subgroup.centralizer (L1 : Set G)

@[expose] def Stmt5_2_6_second : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → ¬ Group.IsSolvable ↥L2 →
    F112ListALegacyBare L1 L2 S → F112Second L1 L2 S →
      (perfectCore L1 = L1 ∧ perfectCore L2 = L2 ∧ S ≤ L1 ∧ S ≤ L2) ∨ F112E6Ext L1 L2 S

@[expose] def Stmt5_2_6_U4ext : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → 2 ≤ f → IsU4ExtTwo f (sec52Alpha M L H B D L₂) →
    IsL2Quot f (oTwoQuot ↥L₂) → IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L₂) →
    IsBlock2 L L → IsL2Quot (2 * f) (oTwoQuot ↥L) → IsOmega4MinusType L f →
      pCoreOf 2 (sec52G1 M L H B L₂) = pCoreOf 2 L ∧
      pCoreOf 2 (sec52G2 M H D L₂) = pCoreOf 2 L₂ ∧
      ∃ t : G, orderOf t = 2 ∧ t ∉ pCoreOf 2 L₂ ∧
        pCoreOf 2 (L₂ ⊔ sec52S M H) = pCoreOf 2 L₂ ⊔ Subgroup.zpowers t ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
          ∃ P : Subgroup ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F), IsMaxParabolic2 ⊤ P ∧
            Nonempty (↥(L₂ ⊓ Subgroup.centralizer ({t} : Set G)) ≃* ↥(perfectCore P))

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_sup_T_eq {T M L H : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n) :
    pCoreOf 2 (oTwoUpper H ⊔ T) = pCoreOf 2 (oTwoUpper H ⊔ sec52S M H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hTH
  set S := sec52S M H with hSdef
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKN : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hOT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hTH
  have hOS : pCoreOf 2 H ≤ S :=
    le_pCoreOf_of_le_normalizer 2 (le_inf (hOT.trans h.T_le) (pCoreOf_le 2 H))
      (inf_le_right.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    (le_inf h.T_le hTH.1).trans (le_normalizer_pCoreOf 2 (M ⊓ H))
  have hKSH : oTwoUpper H ⊔ S ≤ H := sup_le hKH hSH
  have hOKS : pCoreOf 2 H ≤ oTwoUpper H ⊔ S := hOS.trans le_sup_right
  have h1 : pCoreOf 2 H ≤ pCoreOf 2 (oTwoUpper H ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 hOKS (hKSH.trans (le_normalizer_pCoreOf 2 H))
      (pCoreOf_isPGroup 2 H)
  have hKn : oTwoUpper H ≤ Subgroup.normalizer
      ((pCoreOf 2 (oTwoUpper H ⊔ S) : Subgroup G) : Set G) :=
    (le_sup_left.trans Subgroup.le_normalizer).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hTn : T ≤ Subgroup.normalizer ((pCoreOf 2 (oTwoUpper H ⊔ S) : Subgroup G) : Set G) :=
    (F1.le_normalizer_sup (hTH.1.trans hKN) hTS).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hHn : H ≤ Subgroup.normalizer ((pCoreOf 2 (oTwoUpper H ⊔ S) : Subgroup G) : Set G) :=
    hKT.ge.trans (sup_le hKn hTn)
  have h2 : pCoreOf 2 (oTwoUpper H ⊔ S) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hKSH) hHn (pCoreOf_isPGroup 2 _)
  rw [hKT]
  exact le_antisymm h1 h2

theorem perfectCore_G2_eq (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hF : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2) (hbor : Stmt5_2_6_borel)
    {T M L V H B D L₂ : Subgroup G} {n : ℕ} (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    perfectCore (sec52G2 M H D L₂) = L₂ := by
  have h111 := Hyp111R.of_hyp111 hF (hF11 G T M L V H B D L₂ n hyp)
  obtain ⟨-, hG2, -⟩ := hyp.parabolics_eq h331 hR (hbor G T M L V H B D L₂ n hyp)
  have hL₂p : ⁅L₂, L₂⁆ = L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact hK₁.2.1
    · exact hL₂P.2.1
  rw [hG2]
  exact Vol2.Ch11.SecS.perfectCore_sup_eq hL₂p (F1.isSolvable_bigB h111)
    (F1.bigB_le_normalizer_left h111).2

namespace Hyp5_2_4

variable {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem f112_hyps (hF11 : StmtF11_5_2) (hbor : Stmt5_2_6_borel) (h524 : Stmt5_2_4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {L1' L2' : Subgroup G}
    (hor : (L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L)) :
    Hyp111 L1' L2' (sec52S M H) ∧ IsQuasithinSub (L1' ⊔ L2' ⊔ sec52S M H) ∧
      (((sec52S M H).subgroupOf (sec52S M H ⊔ borelOf L1' (sec52S M H))).Normal ∨
        ((sec52S M H).subgroupOf (sec52S M H ⊔ borelOf L2' (sec52S M H))).Normal) ∧
      ¬ Group.IsSolvable ↥L1' ∧ ¬ Group.IsSolvable ↥L2' := by
  have h := hyp.toHyp5_0_1
  set S := sec52S M H with hSdef
  have h111 := hF11 G T M L V H B D L₂ n hyp
  have hbor2 : S ⊔ borelOf L₂ S = S ⊔ (B ⊓ L₂) := hbor G T M L V H B D L₂ n hyp
  obtain ⟨-, -, ⟨hBS, -, -⟩, -⟩ := h524 G T M L V H B D L₂ n hyp
  have hSn : (S.subgroupOf (S ⊔ borelOf L₂ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left, hbor2]
    exact sup_le Subgroup.le_normalizer (inf_le_left.trans hBS)
  have hLns : ¬ Group.IsSolvable ↥L :=
    not_isSolvable_of_perfect h.commutator_eq h.maximal.1.2.1.1
  have hL₂ns : ¬ Group.IsSolvable ↥L₂ := by
    obtain ⟨K₁, hK₁, -, hcase⟩ := hyp.choice
    rcases hcase with ⟨-, rfl⟩ | ⟨-, -, P, -, hL₂P⟩
    · exact not_isSolvable_of_perfect hK₁.2.1 hK₁.1
    · exact not_isSolvable_of_perfect hL₂P.2.1 hL₂P.1
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst L1' L2'
    exact ⟨h111, isQuasithinSub_of_qtke h.qtke _, Or.inr hSn, hLns, hL₂ns⟩
  · subst L1' L2'
    exact ⟨h111.symm, isQuasithinSub_of_qtke h.qtke _, Or.inl hSn, hL₂ns, hLns⟩

theorem alpha_eq (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) (hbor : Stmt5_2_6_borel)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    RankTwoAmalgam.ofSubgroups (L ⊔ bigB L L₂ (sec52S M H)) (L₂ ⊔ bigB L L₂ (sec52S M H)) =
      sec52Alpha M L H B D L₂ := by
  obtain ⟨hG1, hG2, -⟩ := hyp.parabolics_eq h331 hR (hbor G T M L V H B D L₂ n hyp)
  rw [← hG1, ← hG2]

theorem isAmalgamOfGroup_of_orient (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hbor : Stmt5_2_6_borel) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {L1' L2' : Subgroup G}
    (hor : (L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L)) {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1' ⊔ bigB L1' L2' (sec52S M H))
      (L2' ⊔ bigB L1' L2' (sec52S M H))) P) :
    IsAmalgamOfGroup (sec52Alpha M L H B D L₂) P := by
  rw [← hyp.alpha_eq h331 hR hbor]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst L1' L2'
    exact h
  · subst L1' L2'
    rw [bigB_swap] at h
    exact isAmalgamOfGroup_ofSubgroups_swap h

theorem isU4ExtTwo_of_orient (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact)
    (hbor : Stmt5_2_6_borel) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {L1' L2' : Subgroup G}
    (hor : (L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L)) {f : ℕ}
    (h : IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups (L1' ⊔ bigB L1' L2' (sec52S M H))
      (L2' ⊔ bigB L1' L2' (sec52S M H)))) :
    IsU4ExtTwo f (sec52Alpha M L H B D L₂) := by
  rw [← hyp.alpha_eq h331 hR hbor]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst L1' L2'
    exact h
  · subst L1' L2'
    rw [bigB_swap] at h
    exact isU4ExtTwo_ofSubgroups_swap h

theorem isL2Quot_L (hyp : Hyp5_2_4 G T M L V H B D L₂ n) : IsL2Quot n (oTwoQuot ↥L) :=
  isL2Quot_oTwoQuot_of_lieModel (by have := hyp.toHyp5_0_1.two_le; omega) hyp.toHyp5_0_1.lie

theorem eq_of_isL2Quot_L (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {f : ℕ} (hf : 1 ≤ f)
    (h : IsL2Quot f (oTwoQuot ↥L)) : f = n :=
  eq_of_isL2Quot hf (by have := hyp.toHyp5_0_1.two_le; omega) h hyp.isL2Quot_L

theorem eq_of_isLin2Type_L (hyp : Hyp5_2_4 G T M L V H B D L₂ n) {f : ℕ}
    (h : IsLin2Type L f) : f = n := by
  have h1 := card_oTwoQuot_of_isLin2Type h
  rw [hyp.isL2Quot_L.card (by have := hyp.toHyp5_0_1.two_le; omega)] at h1
  exact (eq_of_two_pow_mul_four_pow_sub_one_eq h1).symm

end Hyp5_2_4

end CFSG.Quasithin.H13
