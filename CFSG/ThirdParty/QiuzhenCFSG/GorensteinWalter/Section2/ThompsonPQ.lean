module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComplementConjugacy
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.ActionTriviality
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

namespace CFSG
end CFSG
open CFSG

/-!
# Thompson's P × Q lemma

An ambient-subgroup form of Kurzweil--Stellmacher 8.2.8.  A `p`-group `P`
and a group `Q` of order prime to `p` act by conjugation on the `p`-group
`B`.  If `P` and `Q` commute and every element of `B` fixed by `P` is also
fixed by `Q`, then `Q` centralizes `B`.

The proof is the standard induction on `|B|`.  It uses the properness of
`[B,P]`, the Three-Subgroups Lemma, and the coprime-action identity
`[B,Q,Q] = [B,Q]`.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

namespace ThompsonPQ

/-- If `Q` normalizes `B` and centralizes `P`, then it normalizes `[B,P]`. -/
private theorem normalizes_commutator_of_normalizes_left_of_commutes
    {G : Type u} [Group G] {B P Q : Subgroup G}
    (hBQ : Q ≤ Subgroup.normalizer (B : Set G))
    (hPQ : ⁅P, Q⁆ = ⊥) :
    Q ≤ Subgroup.normalizer ((⁅B, P⁆ : Subgroup G) : Set G) := by
  have hQP : ⁅Q, P⁆ = ⊥ := by
    simpa [Subgroup.commutator_comm] using hPQ
  have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQP
  have hQnormP : Q ≤ Subgroup.normalizer (P : Set G) :=
    hQcentP.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  apply subgroup_le_normalizer_of_conj_mem
  intro q x hx
  have hmapB : B.map (MulAut.conj (q : G)).toMonoidHom = B := by
    have h := map_conj_mul_right_eq_of_mem_normalizer (H := B) (g := (1 : G))
      ⟨q, hBQ q.property⟩
    have hid : B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
      ext y
      simp [MulAut.conj]
    simpa only [one_mul] using h.trans hid
  have hmapP : P.map (MulAut.conj (q : G)).toMonoidHom = P := by
    have h := map_conj_mul_right_eq_of_mem_normalizer (H := P) (g := (1 : G))
      ⟨q, hQnormP q.property⟩
    have hid : P.map (MulAut.conj (1 : G)).toMonoidHom = P := by
      ext y
      simp [MulAut.conj]
    simpa only [one_mul] using h.trans hid
  have hmapU : (⁅B, P⁆).map (MulAut.conj (q : G)).toMonoidHom = ⁅B, P⁆ := by
    rw [Subgroup.map_commutator, hmapB, hmapP]
  have hxmap : (MulAut.conj (q : G)).toMonoidHom x ∈
      (⁅B, P⁆).map (MulAut.conj (q : G)).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hmapU] at hxmap
  simpa [MulAut.conj] using hxmap

/-- An ambient equality `[[B,Q],Q] = 1` gives the corresponding
`commutatorAction₂` equality for the conjugation action of `Q` on `B`. -/
private theorem commutatorAction₂_eq_bot_of_ambient_double_commutator_eq_bot
    {G : Type u} [Group G] (B Q : Subgroup G)
    (hQB : Q ≤ Subgroup.normalizer (B : Set G))
    (hdouble : ⁅⁅B, Q⁆, Q⁆ = ⊥) :
    letI : Subgroup.Normalizes Q B := ⟨hQB⟩
    commutatorAction₂ (A := ↥Q) (G := ↥B) = ⊥ := by
  let : Subgroup.Normalizes Q B := ⟨hQB⟩
  change Subgroup.closure
      {x : B | ∃ q : Q, ∃ b : B,
        b ∈ commutatorAction (A := ↥Q) (G := ↥B) ∧ x = b⁻¹ * (q • b)} = ⊥
  rw [Subgroup.closure_eq_bot_iff]
  rintro x ⟨q, b, hb, rfl⟩
  have hbAmbient : (b : G) ∈ ⁅B, Q⁆ := by
    have hbMap : (b : G) ∈
        (commutatorAction (A := ↥Q) (G := ↥B)).map B.subtype :=
      Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    rw [commutatorAction_subgroup_conj_map_eq_commutator B Q hQB] at hbMap
    exact hbMap
  have hcent : ⁅B, Q⁆ ≤ Subgroup.centralizer (Q : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hdouble
  have hbCent : (b : G) ∈ Subgroup.centralizer (Q : Set G) := hcent hbAmbient
  have hmul : (q : G) * (b : G) = (b : G) * (q : G) :=
    Subgroup.mem_centralizer_iff.mp hbCent (q : G) q.property
  have hfix : q • b = b := by
    apply Subtype.ext
    rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    calc
      (q : G) * (b : G) * (q : G)⁻¹ =
          ((b : G) * (q : G)) * (q : G)⁻¹ := by rw [hmul]
      _ = (b : G) := by simp [mul_assoc]
  simp [hfix]

/-- **Thompson's P × Q lemma** (Kurzweil--Stellmacher 8.2.8), in the
ambient-subgroup form needed by Bender's Statement 1.1.

Here `P` and `B` are `p`-groups, `Q` has order prime to `p`, `P` and `Q`
commute, and both normalize `B`.  The fixed-point containment is written as
`C_B(P) ≤ C_G(Q)`. -/
public theorem thompson_p_times_q
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q B : Subgroup G)
    (hPp : IsPGroup p P) (hBp : IsPGroup p B)
    (hQcop : Nat.Coprime p (Nat.card Q))
    (hPB : P ≤ Subgroup.normalizer (B : Set G))
    (hQB : Q ≤ Subgroup.normalizer (B : Set G))
    (hPQ : ⁅P, Q⁆ = ⊥)
    (hfixed : B ⊓ Subgroup.centralizer (P : Set G) ≤
      Subgroup.centralizer (Q : Set G)) :
    ⁅B, Q⁆ = ⊥ := by
  classical
  induction hcard : Nat.card B using Nat.strong_induction_on generalizing B with
  | h n ih =>
      by_cases hBbot : B = ⊥
      · simp [hBbot]
      let U : Subgroup G := ⁅B, P⁆
      have hUleB : U ≤ B :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hPB
      have hUltB : U < B := by
        simpa [U] using
          (SchurZassenhaus.commutator_lt_of_pGroups B P hBp hPp hPB hBbot)
      have hUcard : Nat.card U < n := by
        rw [← hcard]
        exact natCard_lt_of_subgroup_lt hUltB
      have hUp : IsPGroup p U := hBp.to_le hUleB
      have hPnormU : P ≤ Subgroup.normalizer (U : Set G) := by
        simpa [U] using Subgroup.normalizer_commutator_ge_right B P
      have hQnormU : Q ≤ Subgroup.normalizer (U : Set G) := by
        simpa [U] using
          normalizes_commutator_of_normalizes_left_of_commutes hQB hPQ
      have hfixedU : U ⊓ Subgroup.centralizer (P : Set G) ≤
          Subgroup.centralizer (Q : Set G) := by
        intro x hx
        exact hfixed ⟨hUleB hx.1, hx.2⟩
      have hUQ : ⁅U, Q⁆ = ⊥ :=
        ih (Nat.card U) hUcard (B := U) hUp hPnormU hQnormU hfixedU rfl
      have hPQB : ⁅⁅P, Q⁆, B⁆ = ⊥ := by simp [hPQ]
      have hQBP : ⁅⁅Q, B⁆, P⁆ = ⊥ :=
        Subgroup.commutator_commutator_eq_bot_of_rotate hUQ hPQB
      have hBQcentP : ⁅B, Q⁆ ≤ Subgroup.centralizer (P : Set G) := by
        have h := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQBP
        simpa [Subgroup.commutator_comm] using h
      have hBQleB : ⁅B, Q⁆ ≤ B :=
        (Subgroup.le_normalizer_iff_commutator_le_left).mp hQB
      have hBQcentQ : ⁅B, Q⁆ ≤ Subgroup.centralizer (Q : Set G) :=
        (le_inf hBQleB hBQcentP).trans hfixed
      have hdouble : ⁅⁅B, Q⁆, Q⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hBQcentQ
      let : Subgroup.Normalizes Q B := ⟨hQB⟩
      have hactDouble : commutatorAction₂ (A := ↥Q) (G := ↥B) = ⊥ :=
        commutatorAction₂_eq_bot_of_ambient_double_commutator_eq_bot B Q hQB hdouble
      have hBnil : Group.IsNilpotent B := hBp.isNilpotent
      let : Group.IsNilpotent B := hBnil
      have hBsolv : Group.IsSolvable B := inferInstance
      obtain ⟨m, hm⟩ := hBp.exists_card_eq
      have hQcopB : Nat.Coprime (Nat.card Q) (Nat.card B) := by
        rw [hm]
        exact hQcop.symm.pow_right m
      have hdecomp := SchurZassenhaus.coprime_action_decomposition
        (A := ↥Q) (B := ↥B) hBsolv hQcopB
      have htriv : ActsTrivially (A := ↥Q) (G := ↥B) :=
        actsTrivially_of_commutatorAction₂_eq_bot_of_eq hdecomp.2 hactDouble
      simpa [Subgroup.commutator_comm] using
        (commutator_eq_bot_of_actsTrivially_subgroup_conj B Q hQB htriv)

end ThompsonPQ

end CFSG.GorensteinWalter
