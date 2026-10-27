module

public import CFSG.Timmesfeld.Bridge.SchurNarrowTransport
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.Timmesfeld.Bridge.Asc73
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import CFSG.Timmesfeld.Bridge.SchurNarrowCore

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.ProperTwoGeneratedCore.TheoremC

theorem sylowBorelData_of_bender {B : Type} [Group B] [Finite B]
    (hB : CFSG.BenderSuzuki.IsBenderGroup B) {q k : ℕ} (hq : 2 ≤ q) (hk : 2 ≤ k)
    (hfb : fusionBenderBorel B q k) (Q : Sylow 2 B) : SylowBorelData B Q := by
  have hBF := benderBorelFactsHold B hB Q
  obtain ⟨-, -, hZsq, hZcard, hQcard⟩ := hfb Q
  obtain ⟨D, hDodd, hDN, -, htrans, hforms⟩ := hBF.torus
  refine ⟨hBF.commutator_central, hBF.sq_central, ?_, ?_,
    ⟨D, hDodd, hDN, htrans, hforms⟩, hBF.center_card⟩
  · intro w hw
    have h := hZsq ⟨w, hw.1⟩ (Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (hw.2 g g.2).eq)
    have h' := congrArg Subtype.val h
    simpa [pow_two] using h'
  · by_contra hcon
    push Not at hcon
    have htop : Subgroup.center (Q : Subgroup B) = ⊤ := by
      rw [eq_top_iff]
      intro g _
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext ((hcon g g.2).2 h h.2).eq
    rw [htop, Subgroup.card_top] at hZcard
    rw [hZcard] at hQcard
    have hlt := Nat.pow_lt_pow_right (by omega : 1 < q) (by omega : 1 < k)
    rw [pow_one] at hlt
    omega

theorem schurNarrowInput : SchurNarrowInput := by
  intro E _ _ x _ hxZ hx2 hxE M N _ _ _ _ hM hN hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 E) := inferInstance
  refine exists_isConj_mul_of_borelData hxZ hx2 hxE S ?_
  have hBD : ∀ Q : Sylow 2 (N ⧸ M.subgroupOf N),
      SylowBorelData (N ⧸ M.subgroupOf N) (Q : Subgroup (N ⧸ M.subgroupOf N)) := by
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
      have hfb : fusionBenderBorel (N ⧸ M.subgroupOf N) (2 ^ f) 3 :=
        (bender_psu3_borel_full f hf).map_mulEquiv e.symm
      exact sylowBorelData_of_bender
        (isBenderGroup_of_fusionIsBenderGroup (Or.inr (Or.inl ⟨f, hf, ⟨e⟩⟩)))
        (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)) (by norm_num) hfb
    · have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
      have hfb : fusionBenderBorel (N ⧸ M.subgroupOf N) (2 ^ (2 * a + 1)) 2 :=
        (bender_suzuki_borel_full a ha).map_mulEquiv e.symm
      exact sylowBorelData_of_bender
        (isBenderGroup_of_fusionIsBenderGroup (Or.inr (Or.inr ⟨a, ha, ⟨e⟩⟩)))
        (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ 2 * a + 1)))
        le_rfl hfb
  have hS := sylowBorelData_of_section hM hN hBD
    (S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.zpowers x)))
  rwa [Sylow.coe_mapSurjective] at hS

theorem asc73Input_of_theoremTwo (h2 : TheoremTwoStatement) : Asc73Input :=
  asc73Input_of h2 schurNarrowInput

end CFSG.Timmesfeld.Bridge
