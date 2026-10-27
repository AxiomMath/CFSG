module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt
import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def FiveCore (M Q Z B Y : Subgroup G) : Prop :=
  ∃ U₁ : Subgroup G, Z ≤ U₁ ∧ B ≤ U₁ ∧ U₁ ≤ Q ∧ Nat.card Z ^ 4 ≤ Nat.card U₁ ∧
    ∀ u ∈ U₁, u ∉ Z → ∃ h ∈ M, conjSubgroup h Y = Y ∧ conjSubgroup h B ≤ U₁ ∧
      u ∈ (conjSubgroup h B ⊔ Z : Subgroup G)

theorem fiveConcl_of_core (hc : Ctx M Q Z B) {Y : Subgroup G}
    (h : FiveCore M Q Z B Y) : FiveConcl M Q Z B Y := by
  obtain ⟨U₁, hZU, hBU, hUQ, hcard, hcover⟩ := h
  refine ⟨U₁, hZU, hBU, hUQ, ?_, ?_, ?_, hcard⟩
  · intro u hu
    by_cases huZ : u ∈ Z
    · exact ⟨1, M.one_mem, 1, B.one_mem, by simpa using huZ⟩
    · obtain ⟨h, hhM, -, -, huh⟩ := hcover u hu huZ
      have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hhM
      obtain ⟨b', hb', z, hz, huz⟩ := sec8PointTI_mul_of_mem_sup
        (B := conjSubgroup h B) (Z := Z) (fun b hb z hz => sec8PointTI_central hc' hb hz) huh
      refine ⟨h, hhM, h⁻¹ * b' * h, ?_, ?_⟩
      · exact mem_conjSubgroup.mp hb'
      · have hbz : b' * z * b'⁻¹ = z := by
          rw [sec8PointTI_central hc' hb' hz]
          group
        have e : h * (h⁻¹ * b' * h) * h⁻¹ = b' := by group
        rw [huz, e, hbz]
        exact hz
  · intro m hm u hu huZ hum
    obtain ⟨h, hhM, hhY, -, huh⟩ := hcover u hu huZ
    have hsup : conjSubgroup m B ⊔ Z = conjSubgroup h B ⊔ Z :=
      sec8_point_eq (hc := hc) hm hhM hum huh huZ
    have hLB : LB M Q (conjSubgroup m B) = LB M Q (conjSubgroup h B) :=
      sec8_LB_eq_of_sup_eq (hc.conj_of_mem hm) (hc.conj_of_mem hhM) hsup
    refine ⟨h, hhM, hhY, ?_⟩
    rw [hLB, Ctx.LB_conj hc hhM]
  · intro m hm u hu huZ hum
    obtain ⟨h, hhM, -, hhBU, huh⟩ := hcover u hu huZ
    have hsup : conjSubgroup m B ⊔ Z = conjSubgroup h B ⊔ Z :=
      sec8_point_eq (hc := hc) hm hhM hum huh huZ
    intro x hx
    exact (sup_le hhBU hZU) (by
      rw [← hsup]
      exact Subgroup.mem_sup_left hx)

theorem card_conj_sup_Z (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    Nat.card ↥(conjSubgroup m B ⊔ Z) = Nat.card Z ^ 2 := by
  obtain ⟨g, hg⟩ := hc.conj
  have hmZ : conjSubgroup m Z = Z := conjSubgroup_eq_self_iff.mpr (hc.hyp.Z_normal.2 hm)
  calc Nat.card ↥(conjSubgroup m B ⊔ Z)
      = Nat.card ↥(conjSubgroup m (B ⊔ Z)) := by rw [conjSubgroup_sup', hmZ]
    _ = Nat.card Z ^ 2 := by
      rw [card_conjSubgroup, hc.card_sup_Z, hg, card_conjSubgroup, pow_two]

end HS9

@[expose] def Sec97VnStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ LB M Q B ⊓ hc.CN t, x ∉ Z0 → Vt M (LB M Q B) B Z x ≠ Vt M (LB M Q B) B Z t

@[expose] def Sec9CentreMprStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ LB M Q B, (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Z) → x ∈ Z0

theorem sec97Vn_of_centreMpr (h34 : Stroth34Statement) (hm : Sec9CentreMprStatement) :
    Sec97VnStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 x hx hxZ0 hVx
  obtain ⟨hxL, -⟩ := Subgroup.mem_inf.mp hx
  have hs5 := hs.toSec5
  have htL : t ∈ LB M Q B := hs5.mem
  have hxQ : x ∉ Q := fun hxq => hxZ0 (hc.Q_le_centre htL hZ0 hxq)
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hnot : ¬ Vt M (LB M Q B) B Z x ≤ QB B := by
    rw [hVx]
    exact sec9_notQB h34 hs
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  obtain ⟨-, hW⟩ := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 hxL hxQ hnot
  refine hxZ0 (hm G M Q Z B hc n t hs Z0 hZ0 x hxL ?_)
  intro w hw
  rw [← hVx, hW] at hw
  exact ((hc.mem_Q1_iff hxM).mp hw).2

end CFSG.RankThree.GF2n.Stroth80
