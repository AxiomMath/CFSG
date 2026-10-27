module

public import CFSG.Quasithin.Background.F7TwoE1
public import CFSG.Quasithin.Background.F7TwoE2Main
public import CFSG.Quasithin.Background.F7TwoInvBridge
import CFSG.LocalAnalysis.SectionRank.SQTKTransport

public section

namespace CFSG.Quasithin.F7Two

theorem twoResidual_le_closure_nonTwoConj_of_top {G : Type*} [Group G] [Finite G]
    {H A : Subgroup G}
    (h : twoResidual (⊤ : Subgroup ↥H) ≤ Subgroup.closure (nonTwoConj (A.subgroupOf H) ⊤)) :
    twoResidual H ≤ Subgroup.closure (nonTwoConj A H) := by
  set M : Subgroup ↥H := twoResidual (⊤ : Subgroup ↥H) with hM
  have hMnorm : Subgroup.normalizer (M : Set ↥H) = ⊤ :=
    top_le_iff.mp (le_normalizer_twoResidual ⊤)
  have h1 : twoResidual H ≤ M.map H.subtype := by
    refine twoResidual_le_of_isTwoQuotient (Subgroup.map_subtype_le _) ?_ ?_
    · intro x hx
      exact Subgroup.le_normalizer_map H.subtype
        (Subgroup.mem_map_of_mem H.subtype
          (show (⟨x, hx⟩ : ↥H) ∈ Subgroup.normalizer (M : Set ↥H) from
            hMnorm ▸ Subgroup.mem_top _))
    · intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (⊤ : Subgroup ↥H) ⟨y, hy⟩ (Subgroup.mem_top _)
      exact ⟨k, ⟨_, hk, by simp⟩⟩
  have h2 : (Subgroup.closure (nonTwoConj (A.subgroupOf H) ⊤)).map H.subtype ≤
      Subgroup.closure (nonTwoConj A H) := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    refine Subgroup.subset_closure ⟨q.2, fun hP => ?_⟩
    rw [mem_nonTwoConj_top] at hq
    refine hq fun y => ?_
    have hle : A.subgroupOf H ⊔ conjSubgroup (A.subgroupOf H) q ≤
        (A ⊔ conjSubgroup A (q : G)).comap H.subtype := by
      refine sup_le (fun z hz => Subgroup.mem_sup_left hz) (fun z hz => ?_)
      rw [mem_conjSubgroup_iff] at hz
      exact Subgroup.mem_sup_right (by rw [mem_conjSubgroup_iff]; exact hz)
    obtain ⟨k, hk⟩ := pow_eq_one_of_mem_isPGroup hP (hle y.2)
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  exact h1.trans ((Subgroup.map_mono h).trans h2)

theorem isSQTKCat_of_le_f7 {G : Type} [Group G] [Finite G] {X H : Subgroup G} (hHX : H ≤ X)
    (hX : CFSG.SectionRank.IsSQTKCat ↥X) : CFSG.SectionRank.IsSQTKCat ↥H :=
  CFSG.SectionRank.IsSQTKCat.of_le hHX hX

theorem claimCE1_of_gen
    (hgen : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.SectionRank.IsSQTKCat Q → CompInvGen Q) :
    ClaimCE1 := by
  intro G _ _ X S A H hSQTK _ _ _ _ hE hAH
  obtain ⟨hHX, -, -, hcase⟩ := hE
  rcases hcase with ⟨h, -⟩ | ⟨h, hcard⟩
  · exact twoResidual_le_closure_nonTwoConj_of_eOne hAH h
  · exact twoResidual_le_closure_nonTwoConj_of_top
      (twoResidual_top_le_closure_of_eTwo_gen (hgen ↥H (isSQTKCat_of_le_f7 hHX hSQTK)) h
        (by simpa using hcard))

theorem claimCE1_of_invAutGenSQTK (hP : InvAutGenSQTK) : ClaimCE1 := by
  refine claimCE1_of_gen fun Q _ _ hQ L a hL ha2 haN hac => ?_
  have hrad : CFSG.solvableRadical (Q ⧸ CFSG.solvableRadical Q) = ⊥ :=
    A3.solvableRadical_quotient_eq_bot Q
  exact invGen_of_invAutGenSQTK hP hQ (CFSG.solvableRadical Q)
    (isSimpleGroup_of_isComponent hrad hL) (exists_mul_ne_of_isComponent hL) ha2 haN hac

end CFSG.Quasithin.F7Two
