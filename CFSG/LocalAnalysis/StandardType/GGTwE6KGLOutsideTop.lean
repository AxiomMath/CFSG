module

public import CFSG.LocalAnalysis.StandardType.GGNbrOutsideInndiag
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.Marking
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem largeEvenLabelAll_self (lab : LargeEvenLabel) :
    LargeEvenLabelAll lab fun R _ I F =>
      ∀ Φ : LargeEvenRawCont, Φ R I F → LargeEvenRawDatum lab Φ := by
  intro Q h
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h
       exact ⟨K, i1, i2, hK, b, c, hbc, hq, fun Φ hΦ => ⟨K, i1, i2, hK, b, c, hbc, hΦ⟩⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h
       exact ⟨K, i1, i2, hK, hq, fun Φ hΦ => ⟨K, i1, i2, hK, hΦ⟩⟩)

private theorem eq_bot_or_top_of_isSubnormal {R : Type} [Group R] [IsSimpleGroup R]
    {H K : Subgroup R} (h : IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => exact Or.inr
  | step hHM hN _ ih =>
    intro hK
    rcases ih hK with rfl | rfl
    · exact Or.inl (le_bot_iff.1 hHM)
    · have : Subgroup.Normal _ := ⟨fun n hn g => by
        simpa [Subgroup.mem_subgroupOf] using
          hN.conj_mem ⟨n, trivial⟩ (by simpa [Subgroup.mem_subgroupOf] using hn) ⟨g, trivial⟩⟩
      exact Subgroup.Normal.eq_bot_or_eq_top _

private theorem eq_top_of_isComponentOf_top {R : Type} [Group R] [IsSimpleGroup R]
    {J : Subgroup R} (hJ : IsComponentOf J ⊤) : J = ⊤ := by
  obtain ⟨-, hsub, hq⟩ := hJ
  refine (eq_bot_or_top_of_isSubnormal hsub rfl).resolve_left ?_
  rintro rfl
  have := hq.2.toNontrivial
  exact not_nontrivial_iff_subsingleton.2 inferInstance this

theorem largeEvenLabelAll_not_ggOutsideInndiag_top {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ t ∈ I, ¬ GGOutsideInndiag (⊤ : Subgroup R) t := by
  refine (largeEvenLabelAll_self lab).mono fun R _ I _ hself hR hna t ht hout => ?_
  haveI := hR
  haveI : IsSimpleGroup ↥(⊤ : Subgroup R) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup R) ≃* R).isSimpleGroup
  have hnc : ¬ IsMulCommutative ↥(⊤ : Subgroup R) := fun h => by
    obtain ⟨a, b, hab⟩ := hna
    exact hab (congrArg Subtype.val (h.is_comm.comm ⟨a, trivial⟩ ⟨b, trivial⟩))
  have hcen := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  let θ : ↥(⊤ : Subgroup R) ⧸ Subgroup.center ↥(⊤ : Subgroup R) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hθ : ∀ l : ↥(⊤ : Subgroup R), θ (QuotientGroup.mk l) = (l : R) := fun _ => rfl
  have hraw := hself (fun R' _ I' _ => IsSimpleGroup R' ∧ (∃ a b : R', a * b ≠ b * a) ∧
      ∃ θ' : ↥(⊤ : Subgroup R) ⧸ Subgroup.center ↥(⊤ : Subgroup R) ≃* R',
        ∃ φ ∈ Subgroup.closure I',
          LargeEvenInduces θ' (fun l l' : ↥(⊤ : Subgroup R) => (l' : R) = t l) φ)
    ⟨hR, hna, θ, t, Subgroup.subset_closure ht, fun l l' h => by rw [hθ, hθ, h]⟩
  have hM : LargeEvenMarking ↥(⊤ : Subgroup R) fun _ R' _ I' _ θ' =>
      ∃ φ ∈ Subgroup.closure I',
        LargeEvenInduces θ' (fun l l' : ↥(⊤ : Subgroup R) => (l' : R) = t l) φ :=
    ⟨(TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc).commutator_eq_top, lab, hlab,
      (largeEvenRawDatum_legacy _ _).1 hraw⟩
  obtain ⟨-, lab', -, hraw'⟩ := hout.2 _ hM
  obtain ⟨_, _, _, _, _, _, _, hPQ⟩ :=
    largeEvenRawDatum_exists ((largeEvenRawDatum_legacy _ _).2 hraw')
  exact hPQ.2 hPQ.1

theorem largeEvenLabelAll_not_ggOutsideInndiag_ggFix_one {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ t ∈ I, ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix (1 : MulAut R)) →
        ¬ GGOutsideInndiag J₁ t := by
  refine (largeEvenLabelAll_not_ggOutsideInndiag_top hlab).mono
    fun R _ I _ h hR hna t ht J₁ hJ₁ => ?_
  haveI := hR
  have h1 : ggFix (1 : MulAut R) = ⊤ := by
    ext x
    simp [mem_ggFix]
  rw [h1] at hJ₁
  rw [eq_top_of_isComponentOf_top hJ₁]
  exact h hR hna t ht

end CFSG.StandardType.SCFourCover

end
