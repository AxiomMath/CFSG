module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L62b

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem exists_inPiTheta
    (h : Counterexample p A θ) : ∃ r, InPiTheta A θ r := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  have hcard : Nat.card (θ a) ≠ 1 := by
    intro h1
    obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp h1
    exact h.not_isSolvable_apply ha ha1 inferInstance
  obtain ⟨r, hr, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  exact ⟨r, hr, a, ha, ha1, hdvd⟩

theorem InPiTheta.ne_p (h : Counterexample p A θ) {r : ℕ} (hr : InPiTheta A θ r) : r ≠ p := by
  obtain ⟨-, a, ha, ha1, hdvd⟩ := hr
  rintro rfl
  exact h.prime.ne_one ((h.isFunctor.coprime a ha ha1).eq_one_of_dvd hdvd)

theorem exists_isSr (h : Counterexample p A θ) {r : ℕ} (hr : InPiTheta A θ r) :
    ∃ S, IsSr p A θ r S := by
  obtain ⟨-, a, ha, ha1, -⟩ := hr
  have hbot : (⊥ : Subgroup G) ∈ MsigR p A θ r := by
    refine ⟨⟨?_, ?_, fun b _ _ => inf_le_left.trans bot_le, ?_⟩, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    · simp
    · exact hypB_mono bot_le (h.hypC a ha ha1)
    · exact IsPGroup.of_bot
  obtain ⟨S, -, hS⟩ := Finite.exists_le_maximal (p := (· ∈ MsigR p A θ r)) hbot
  exact ⟨S, hS⟩

theorem isPGroup_of_isSr (hS : IsSr p A θ r S) : IsPGroup r S :=
  hS.1.2

theorem normalizes_of_isSr (hS : IsSr p A θ r S) : A ≤ Subgroup.normalizer (S : Set G) :=
  hS.1.1.1

theorem inf_centralizer_le_of_isSr (hS : IsSr p A θ r S) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) :
    S ⊓ Subgroup.centralizer {b} ≤ θ b :=
  hS.1.1.2.2.1 b hb hb1

theorem inf_centralizer_le_thetaOf_of_isSr (_h : Counterexample p A θ) (hS : IsSr p A θ r S)
    {B : Subgroup G} (hBA : B ≤ A) (_hB : B ≠ ⊥) :
    S ⊓ Subgroup.centralizer (B : Set G) ≤ thetaOf θ B := by
  exact inf_centralizer_le_thetaOf hS.1.1 hBA

theorem isSrSubgroupOf_of_isSr (h : Counterexample p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    IsSrSubgroupOf A r (θ a) (S ⊓ Subgroup.centralizer {a}) :=
  hS.isSrSubgroupOf_inf_centralizer h.prime h.elemAbelian h.rank_three_le h.isFunctor hr.1
    (InPiTheta.ne_p h hr)
    (fun _ hX => signalizerMcBrideHypothesisB_of_isPGroup h.prime hr.1 (InPiTheta.ne_p h hr) hX)
    ha ha1

theorem sylow_of_isSr (h : Counterexample p A θ) (hr : InPiTheta A θ r) (hS : IsSr p A θ r S)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    S ⊓ Subgroup.centralizer {a} ≤ θ a ∧ IsPGroup r ↥(S ⊓ Subgroup.centralizer {a}) ∧
      Nat.Coprime ((S ⊓ Subgroup.centralizer {a}).relIndex (θ a)) r ∧
      A ≤ Subgroup.normalizer ((S ⊓ Subgroup.centralizer {a} : Subgroup G) : Set G) := by
  have hSr := isSrSubgroupOf_of_isSr h hr hS ha ha1
  obtain ⟨hle, hp, hidx⟩ := isSylow_of_isSrSubgroupOf h.prime hr.1 (InPiTheta.ne_p h hr)
    h.elemAbelian (h.isFunctor.normalized a ha ha1) (h.isFunctor.coprime a ha ha1) hSr
  exact ⟨hle, hp, hidx, hSr.1.1⟩

theorem eq_iSup_inf_centralizer_of_isSr (h : Counterexample p A θ) (_hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) :
    S = ⨆ b ∈ B, ⨆ (_ : b ≠ 1), S ⊓ Subgroup.centralizer {b} := by
  exact (iSup_inf_centralizer h.prime (h.isElemAbelian_of_le hB.1) hB.2.ge
    (hB.1.trans (normalizes_of_isSr hS)) hS.1.1.2.1).symm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
