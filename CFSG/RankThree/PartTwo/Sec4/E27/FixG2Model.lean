module

public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec4.E27.Core

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.Open TauCeti
open CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof CFSG.AGLEmbeddingD2

namespace CFSG.RankThree.PartTwo.Sec4.E27

theorem center_eq_bot_of_mulEquiv_e27 {P Q : Type} [Group P] [Group Q] (e : P ≃* Q)
    (hZ : Subgroup.center Q = ⊥) : Subgroup.center P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : e z ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have := Subgroup.mem_center_iff.1 hz x
    rw [← map_mul, ← map_mul, this]
  rw [hZ, Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)


theorem catEquiv_g2 {k : Type} [Field k] [Finite k] (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) (hk : Nat.card k = q.card) :
    Nonempty (Cat ⟨LieTypeIndex.G2 q, hv⟩ ≃* adjointGroup .G2 k) := by
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv k hk
  have hZ : Subgroup.center ↥(adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
  exact ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)⟩

theorem g2_plane_closure {k : Type} [Field k] [Finite k] (q : PrimePower) (hq : q.p = 2)
    (hv : (LieTypeIndex.G2 q).Valid) (hk : Nat.card k = q.card)
    (A : Subgroup (adjointGroup .G2 k)) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 3 ^ 2) :
    Subgroup.closure {c : adjointGroup .G2 k | ∃ b ∈ A, b ≠ 1 ∧ c * b = b * c} = ⊤ := by
  obtain ⟨e⟩ := catEquiv_g2 (k := k) q hv hk
  have hZQ : Subgroup.center (adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
  have hZP : Subgroup.center (Cat ⟨LieTypeIndex.G2 q, hv⟩) = ⊥ := center_eq_bot_of_mulEquiv_e27 e hZQ
  have hinj := conj_injective_of_center_bot hZP
  set Ac : Subgroup (Cat ⟨LieTypeIndex.G2 q, hv⟩) := A.map e.symm.toMonoidHom with hAcdef
  have hAc' : IsElemAbelian 3 Ac := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hA _
  have hAcc : Nat.card Ac = 3 ^ 2 := by
    rw [hAcdef, Subgroup.card_map_of_injective e.symm.injective, hAc]
  set E : Subgroup (MulAut (Cat ⟨LieTypeIndex.G2 q, hv⟩)) :=
    Ac.map (MulAut.conj : Cat ⟨LieTypeIndex.G2 q, hv⟩ →* MulAut (Cat ⟨LieTypeIndex.G2 q, hv⟩)) with hEdef
  have hE : IsElemAbelian 3 E := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hAc' _
  have hEc : Nat.card E = 3 ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective hinj, hAcc]
  have hin : InnerPlane ⟨LieTypeIndex.G2 q, hv⟩ 3 E := fun x ⟨a, _, hx⟩ => ⟨a, hx⟩
  have hexc : ¬ IsD2SeitzException 3 (LieTypeIndex.G2 q) := by
    unfold IsD2SeitzException
    rintro (⟨-, ⟨_, -, -, h⟩ | ⟨_, -, -, h⟩ | ⟨_, -, -, h⟩ | ⟨_, -, -, h | h⟩ | h⟩ | ⟨h5, -⟩)
    all_goals first | (cases h) | omega
  have hchar : 3 ≠ (⟨LieTypeIndex.G2 q, hv⟩ : ValidLieTypeIndex).1.characteristic := by
    rw [show (⟨LieTypeIndex.G2 q, hv⟩ : ValidLieTypeIndex).1.characteristic = q.p from
      TauCeti.LieTypeIndex.characteristic_G2 q, hq]
    norm_num
  have hpg : PlaneGen E := seitzThreeG2Inner ⟨LieTypeIndex.G2 q, hv⟩ 3 Nat.prime_three
    (by norm_num) hchar hexc E hE hEc ⟨hin, rfl, q, rfl⟩
  set SP : Set (Cat ⟨LieTypeIndex.G2 q, hv⟩) := {x | ∃ b ∈ Ac, b ≠ 1 ∧ x * b = b * x} with hSP
  have hsub1 : {x | ∃ ε ∈ E, ε ≠ 1 ∧ ε x = x} ⊆ SP := by
    rintro x ⟨ε, ⟨b, hb, rfl⟩, hε1, hεx⟩
    refine ⟨b, hb, fun h => hε1 (by simp [h]), ?_⟩
    rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hεx
    exact hεx.symm
  have hP1 : Subgroup.closure SP = ⊤ := by
    have h1 : planeClosure E ≤ Subgroup.closure SP := Subgroup.closure_mono hsub1
    rw [show planeClosure E = ⊤ from hpg] at h1
    exact top_le_iff.1 h1
  set SQ : Set (adjointGroup .G2 k) := {c | ∃ b ∈ A, b ≠ 1 ∧ c * b = b * c} with hSQ
  have hsub2 : e.toMonoidHom '' SP ⊆ SQ := by
    rintro _ ⟨x, ⟨b, ⟨a, ha, rfl⟩, hb1, hxb⟩, rfl⟩
    refine ⟨a, ha, fun h => hb1 (by simp [h]), ?_⟩
    have := congrArg e hxb
    simpa [map_mul] using this
  rw [eq_top_iff]
  intro y _
  have hy : e.symm y ∈ Subgroup.closure SP := by rw [hP1]; trivial
  have h2 : e.toMonoidHom (e.symm y) ∈ (Subgroup.closure SP).map e.toMonoidHom := ⟨_, hy, rfl⟩
  rw [MonoidHom.map_closure] at h2
  simpa using (Subgroup.closure_mono hsub2) h2

end CFSG.RankThree.PartTwo.Sec4.E27
