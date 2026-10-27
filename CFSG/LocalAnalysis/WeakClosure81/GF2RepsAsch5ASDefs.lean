module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveFam
public import CFSG.Quasithin.Background.RonanE111Core
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 Bar2 OInf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def InFForAS (j : ℕ) (H T : Subgroup G) : Prop :=
  ∀ Ω : Set (Subgroup G), E1.IsInvColl H Ω → Ω.Nonempty → (∀ A ∈ Ω, A ≠ ⊥) →
    ((E1.eGen j H T Ω : Subgroup G) : Set G) * (T : Set G) = (H : Set G)

@[expose] def InFAS (j : ℕ) (H : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsSylowIn 2 T H → InFForAS j H T

@[expose] def InFSqAS (j : ℕ) (H : Subgroup G) : Prop :=
  InFAS j (⊤ : Subgroup (Bar2 H))

theorem inFAS_of_inF {j : ℕ} {H : Subgroup G}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF j H) : InFAS j H := by
  intro T hT Ω hΩ hne hbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hprod := h T (CFSG.ABGLocalTools.isSylowOf_iff.mpr hT) Ω hΩ hne hbot
  have hle : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP j H T Ω ≤ E1.eGen j H T Ω :=
    iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK =>
      le_iSup₂_of_le A hA (le_iSup_of_le hAT
        (le_iSup₂_of_le K (isE_of_isEP hT hAT (hΩ.isElemAbelian A hA) hK) le_rfl))
  apply Set.Subset.antisymm
  · rintro _ ⟨e, he, t, ht, rfl⟩
    exact H.mul_mem (E1.eGen_le j H T Ω he) (hT.le ht)
  · rw [← hprod]
    exact Set.mul_subset_mul (fun x hx => hle hx) subset_rfl

theorem inFSqAS_of_inFSq {j : ℕ} {H : Subgroup G} (h : InFSq j H) : InFSqAS j H :=
  inFAS_of_inF h

@[expose] def CompFactorAutInEAS (j : ℕ) {G : Type} [Group G] (T : Subgroup G) : Prop :=
  ∀ (M N : Subgroup G) [(N.subgroupOf M).Normal], N ≤ M → N.IsSubnormal → M.IsSubnormal →
    IsSimpleGroup (↥M ⧸ N.subgroupOf M) →
    E1.InE j (RonanE111.innAutInduced T M N)

theorem asch4_3E_AS_holds :
    ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G) (j : ℕ), 1 ≤ j → IsSylowIn 2 T ⊤ →
      CompFactorAutInEAS j T → E1.InE j (⊤ : Subgroup G) := by
  intro G _ _ T j hj hT h
  have hHT : RonanE111.HypT j G T := by
    intro M N _ hNM hMsub _ hsimple _
    haveI : Finite (MulAut (↥M ⧸ N.subgroupOf M)) := MulEquiv.finite_left
    exact (E1.nParam_le_iff hj).2 (h M N hNM
      (Subgroup.IsSubnormal.trans hNM (Subgroup.Normal.isSubnormal ‹_›) hMsub) hMsub hsimple)
  exact (E1.nParam_le_iff hj).1
    (RonanE111.nParam_le_of_hypT RonanE111.e111CoreT hj hT hHT)

@[expose] def Asch5_11AS : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → T < H → ¬ HasCompFactor H IsCalL0 →
    H ≠ lGen IsCalL0 H T →
    (∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p H ≤ 3 ∨ CFSG.Open.pRank p (lGen IsCalL0 H T) ≤ 1) →
    (calNIn H T = {lGen IsCalL0 H T} ∧
      (IsSolvable ↥H ∨ ∃ L : Subgroup Q, IsComponentModN (OInf H) H L ∧ L ⊔ T = H)) ∧
    (InFSqAS 1 H ∨
      (InFSqAS 2 H ∧ ∃ L : Subgroup Q, IsComponentModN (OInf H) H L ∧ L ⊔ T = H ∧
        (HasQuotShape L (OInf H : Set Q) (fun X _ => IsL2 X 2) ∨
          HasQuotShape L (OInf H : Set Q) (fun X _ => IsU3 X 2) ∨
          ((HasQuotShape L (OInf H : Set Q) (fun X _ => IsL3 X 2) ∨
              HasQuotShape L (OInf H : Set Q) (fun X _ => IsSp4 X 2)) ∧
            ∃ t ∈ T, ActsOnDynkinMod (OInf H) L t))))

@[expose] def Asch5_13AS : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (H T : Subgroup Q),
    CFSG.Open.IsKGroup ↥H → IsSylowIn 2 T H → T < H → CFSG.Open.pRank 3 H ≤ 1 →
    ¬ HasCompFactor H IsCalL1 → H ≠ lGen IsCalL1 H T →
    calNIn H T = {lGen IsCalL1 H T} ∧
      (InFSqAS 1 H ∨ ∃ n : ℕ, 1 ≤ n ∧
        (HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
            (fun X _ => IsL2 X (2 * n)) ∨
          HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set Q)
            (fun X _ => IsU3 X (2 * n))))

end CFSG.LocalAnalysis.WeakClosure81
