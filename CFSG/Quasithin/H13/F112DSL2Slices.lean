module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsDSSz
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DSSz
public import CFSG.Quasithin.Background.GoldschmidtListedSolv
public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def DSAL2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 → ¬ Group.IsSolvable ↥L2 →
    ((∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L1)) ∨ (∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2))) →
    ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
      (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
          centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
        centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
      F112ListA L1' L2' S ∧ F112Second L1' L2' S

@[expose] def DSSzL2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    (∃ a : ℕ, 1 ≤ a ∧ Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.Sz a)) → ¬ Group.IsSolvable ↥L2 →
    (∃ n : ℕ, IsL2Quot n (oTwoQuot ↥L2)) → S ≤ L1 ∧ S ≤ L2

theorem dsSzL2_of_dsAL2 (hA : DSAL2Statement) (hF : F112SecondNoSzFact) : DSSzL2Statement := by
  intro G _ _ L1 L2 S hyp hq hS hSz hns2 hL2
  obtain ⟨a, ha, ⟨e⟩⟩ := hSz
  have hns1 : ¬ Group.IsSolvable ↥L1 := by
    intro hs
    apply not_isSolvable_sz ha
    haveI := hs
    have hq1 : Group.IsSolvable (oTwoQuot ↥L1) :=
      Group.isSolvable_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    haveI := hq1
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨L1', L2', hsw, -, -, h2⟩ := hA G L1 L2 S hyp hq hS hns1 hns2 (Or.inr hL2)
  unfold F112Second at h2
  dsimp only at h2
  rcases h2 with ⟨-, -, hS1, hS2⟩ | halt
  · rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hS1, hS2⟩
    · exact ⟨hS2, hS1⟩
  · exfalso
    obtain ⟨h1, h2⟩ := hF _ halt a ha
    rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (h1 (L1'.subgroupOf (L1' ⊔ bigB L1' L2' S))).false
        ((oTwoQuotCongr (Subgroup.subgroupOfEquivOfLe le_sup_left)).trans e)
    · exact (h2 (L2'.subgroupOf (L2' ⊔ bigB L1' L2' S))).false
        ((oTwoQuotCongr (Subgroup.subgroupOfEquivOfLe le_sup_left)).trans e)

end CFSG.Quasithin.H13
