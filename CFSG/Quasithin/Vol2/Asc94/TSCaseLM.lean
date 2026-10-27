module

public import CFSG.Quasithin.Vol2.Asc94.TS39a
public import CFSG.Quasithin.Vol2.Asc94.TSFrame
public import CFSG.CGT.M24S.WCOfCentralizer
public import CFSG.CGT.M24S.Defs
public import CFSG.CGT.T75P.Inputs
public import CFSG.CGT.T75P.Ctx
public import CFSG.CGT.T75P.DecA
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec6Seven
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.CGT.M24S CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {z : G}

theorem Frame0.odd_index_normalizer (F : Frame0 G z) :
    Odd (Subgroup.normalizer (F.U : Set G)).index := by
  obtain ⟨P, hP⟩ := s39_2 F
  have hTM : F.T ≤ Subgroup.normalizer (F.U : Set G) :=
    F.T_le_H.trans F.le_normalizer_U
  have h1 : (Subgroup.normalizer (F.U : Set G)).index ∣ F.T.index := Subgroup.index_dvd_of_le hTM
  have h2 : ¬ 2 ∣ F.T.index := by
    rw [← hP]
    exact P.not_dvd_index
  rw [Nat.odd_iff]
  by_contra h
  have : 2 ∣ (Subgroup.normalizer (F.U : Set G)).index := by omega
  exact h2 (this.trans h1)

theorem Frame0.hyp_of_ne (F : Frame0 G z) (hne : Subgroup.normalizer (F.U : Set G) ≠ Cz z) :
    Hyp F.U (Subgroup.normalizer (F.U : Set G)) := by
  have hnat : NaturalSL F.U (Subgroup.normalizer (F.U : Set G)) 4 1 :=
    (s39_3 F).resolve_left hne
  refine ⟨Subgroup.le_normalizer, ?_, hnat, F.odd_index_normalizer⟩
  exact isWC_of_naturalSL Subgroup.le_normalizer hnat F.U_elem (fun x hx =>
    F.centralizer_U_le (fun u hu => ((Subgroup.mem_centralizer_iff.1 hx) u hu).symm)) F.z_mem_U
    F.z_ne_one F.le_normalizer_U


theorem Frame0.nonabelian [IsSimpleGroup G] (F : Frame0 G z) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hN : (Subgroup.zpowers z).Normal := ⟨fun n hn g => by
    rw [hcon g n, mul_inv_cancel_right]
    exact hn⟩
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers z) with h | h
  · exact F.z_ne_one (Subgroup.zpowers_eq_bot.1 h)
  · have h1 : Nat.card G = 2 := by
      have := Nat.card_zpowers z
      rw [h, Subgroup.card_top] at this
      rw [this, F.ord]
    have h2 : Nat.card (Cz z) ≤ Nat.card G := Subgroup.card_le_card_group _
    rw [F.card_H, h1] at h2
    omega

theorem caseLM_of_frame0 (hM : CFSG.CGT.T75P.M24SylowInput) [IsSimpleGroup G] (F : Frame0 G z)
    (hne : Subgroup.normalizer (F.U : Set G) ≠ Cz z) :
    LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24) := by
  have hH := F.hyp_of_ne hne
  rcases hM G F.nonabelian F.U (Subgroup.normalizer (F.U : Set G)) hH.le hH.wc hH.nat hH.odd with
    h | h
  · exact Or.inl (Or.inl ⟨by decide, h⟩)
  · exact Or.inr h


theorem caseLM (hM : CFSG.CGT.T75P.M24SylowInput) [IsSimpleGroup G] {e : ↥(Cz z) ≃* L52.Hc}
    (S : Setting G z e)
    (h : Subgroup.normalizer (tr e L52.U1 : Set G) ≠ Cz z ∨
      Subgroup.normalizer (tr e L52.U2 : Set G) ≠ Cz z) :
    LieModel G .PSL 5 2 1 ∨ Nonempty (G ≃* NativeSporadic.M24) := by
  rcases h with h | h
  · exact caseLM_of_frame0 hM (frame0 e S.ord) h
  · have h' : Subgroup.normalizer ((frame0 (swapIso e) S.ord).U : Set G) ≠ Cz z := by
      show Subgroup.normalizer (tr (swapIso e) L52.U1 : Set G) ≠ _
      rw [tr_swap_U1]
      exact h
    exact caseLM_of_frame0 hM (frame0 (swapIso e) S.ord) h'

end CFSG.Quasithin.A94
