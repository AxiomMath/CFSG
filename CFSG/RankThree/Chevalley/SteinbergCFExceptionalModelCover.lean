module

public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_central_surjection_of_equiv {L H : Type*} [Group L] [Group H]
    (e : L ⧸ Subgroup.center L ≃* H) :
    ∃ φ : (⊤ : Subgroup L) →* H, Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (⊤ : Subgroup L) := by
  refine ⟨e.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center L)).comp
    Subgroup.topEquiv.toMonoidHom), ?_, ?_⟩
  · exact e.surjective.comp ((QuotientGroup.mk'_surjective _).comp Subgroup.topEquiv.surjective)
  · intro g hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hg
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_center_iff.1 hg h)

theorem exists_central_surjection_of_equiv' {L H : Type*} [Group L] [Group H]
    (e : L ⧸ Subgroup.center L ≃* H) :
    ∃ φ : L →* H, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center L := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun g hg => ?_⟩
  rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg

@[expose] def adjointQuotientEquiv (τ : Tag) (K : Type) [Field K] [Finite K] :
    AdjointQuotient τ K ≃* adjointGroup τ K :=
  (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot

theorem exists_central_surjection_adjointGroup {L : Type*} [Group L] {τ : Tag} {K : Type}
    [Field K] [Finite K] (e : L ⧸ Subgroup.center L ≃* AdjointQuotient τ K) :
    ∃ φ : (⊤ : Subgroup L) →* adjointGroup τ K, Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (⊤ : Subgroup L) :=
  exists_central_surjection_of_equiv (e.trans (adjointQuotientEquiv τ K))

theorem nonempty_derivedCentralQuotient_equiv (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nonempty (DerivedCentralQuotient (twistedFixedGroup t K σ) ≃* graphFixedRootGroup t K σ) := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have hbij : Function.Bijective σ :=
    ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  set σE : K ≃+* K := RingEquiv.ofBijective σ hbij
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hZ : Subgroup.center (graphFixedRootGroup t K σ) = ⊥ := by
    rw [← hσE]
    exact exceptional_fixed_center_trivial t K σE
  obtain ⟨-, -, hΓ, -⟩ := finite_fixed_root_group_perfect t hp hf K hK σ hσ
  unfold DerivedCentralQuotient
  rw [hΓ]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot⟩

theorem exists_central_surjection_graphFixedRootGroup {L : Type*} [Group L] (t : TwistTag)
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (p ^ f) ^ t.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    (e : L ⧸ Subgroup.center L ≃* DerivedCentralQuotient (twistedFixedGroup t K σ)) :
    ∃ φ : (⊤ : Subgroup L) →* graphFixedRootGroup t K σ, Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (⊤ : Subgroup L) := by
  obtain ⟨e'⟩ := nonempty_derivedCentralQuotient_equiv t hp hf K hK σ hσ
  exact exists_central_surjection_of_equiv (e.trans e')

end CFSG.RankThree.Chevalley
