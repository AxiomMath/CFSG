module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exp_eq_of_card_LB (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B) {k : ℕ}
    (hk : Nat.card ↥(LB M Q B) = Nat.card Q * Nat.card Z ^ k) : n - 1 = k := by
  have h2 := (stroth_3_5 h34 hc hw hn hno hgen).2.2.1
  have hq : 2 ≤ Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  exact Nat.pow_right_injective hq (Nat.eq_of_mul_eq_mul_left hQpos (h2.symm.trans hk))

theorem stroth_6_1 (h34 : Stroth34Statement) (hLB : Stroth6LBStatement)
    (hD : Stroth6SLDimStatement) : Stroth61Statement := by
  intro G _ _ M Q Z B hc n t hs ⟨m, hm, hsl⟩
  have h1 := exp_eq_of_card_LB h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2
    hs.toSec5.gen ((hLB G M Q Z B hc n t hs).1 m hm hsl)
  have h2 := hD G M Q Z B hc n t hs.toSec5 m hm hsl
  have h3 := hs.toSec5.n_gt
  omega

theorem stroth_6_2 (h34 : Stroth34Statement) (hLB : Stroth6LBStatement) : Stroth62Statement := by
  intro G _ _ M Q Z B hc n t hs hΩ
  have h1 := exp_eq_of_card_LB h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2
    hs.toSec5.gen ((hLB G M Q Z B hc n t hs).2 2 le_rfl hΩ)
  have h3 := hs.toSec5.n_gt
  omega

theorem stroth_6_3a (h34 : Stroth34Statement) (hLB : Stroth6LBStatement) :
    Stroth63aStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hΩ
  have h1 := exp_eq_of_card_LB h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2
    hs.toSec5.gen ((hLB G M Q Z B hc n t hs).2 m (by omega) hΩ)
  have h3 := hs.toSec5.n_gt
  omega


theorem Ctx.CN_eq_LB_of_Rt_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (hR : Rt M (LB M Q B) t = LB M Q B) : hc.CN t = LB M Q B := by
  have hV : Vt M (LB M Q B) B Z t ≤ CQtGrp hc (LB M Q B) := by
    refine sec39_Vt_le (fun z hz => ⟨hc.Z_le_Q hz, fun t' ht' => ?_⟩)
      (fun m hm htm u hu => ?_)
    · have h1 : t' * z * t'⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hc.LB_le_M ht')) z).mp hz
      rw [commutatorElement_def]
      exact Z.mul_mem h1 (Z.inv_mem hz)
    · have hcm := hc.conj_of_mem hm
      have hle : conjSubgroup m (LB M Q B) ≤ LB M Q B :=
        (le_iSup₂_of_le m hm (le_iSup_of_le htm le_rfl) : conjSubgroup m (LB M Q B) ≤
          Rt M (LB M Q B) t).trans hR.le
      have heq : conjSubgroup m (LB M Q B) = LB M Q B :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])
      refine ⟨hcm.le hu, fun t' ht' => hcm.comm_B_mem_Z ?_ hu⟩
      rw [hc.LB_conj hm, heq]
      exact ht'
  refine le_antisymm (fun x hx => hR ▸ (Ctx.mem_CN.mp hx).1) (fun l hl => ?_)
  exact Ctx.mem_CN.mpr ⟨hR ▸ le_Rt (M := M) (LB M Q B) ht hl, fun v hv => (hV hv).2 l hl⟩

theorem stroth_6_5 (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h54 : Stroth54Statement) (h61 : Stroth61Statement) (h62 : Stroth62Statement)
    (h63a : Stroth63aStatement) (hX : Stroth65XStatement) : Stroth65Statement := by
  intro G _ _ M Q Z B hc n t hs
  have s5 := hs.toSec5
  rcases h310 G M Q Z B hc n s5.width s5.n_gt s5.noA2 s5.gen t s5.mem s5.notQ with hRL |
      ⟨K, fK, finK, hK, hcase⟩
  · exfalso
    have hCN := hc.CN_eq_LB_of_Rt_eq s5.mem hRL
    have h1 := (stroth_3_5 h34 hc s5.width s5.n_gt s5.noA2 s5.gen).2.2.1
    have h2 := hs.cardN
    rw [hCN] at h2
    have hq : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    have h3 : Nat.card Z ^ (n - 1) = Nat.card Z ^ 1 :=
      Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Q)) (by rw [← h1, h2, pow_one])
    have := Nat.pow_right_injective hq h3
    have := s5.n_gt
    omega
  · rcases hcase with ⟨m, hm, hrep⟩ | ⟨m, hm, hrep⟩ | ⟨m, hm, hrep⟩ | ⟨m, b, c, hm, hbc, hrep⟩
    · exact absurd ⟨m, hm, Or.inl ⟨K, fK, finK, hK, hrep⟩⟩ (h61 G M Q Z B hc n t hs)
    · by_cases hm1 : m = 1
      · subst hm1
        exact absurd ⟨2, le_rfl, Or.inr ⟨rfl, K, fK, finK, hK, hrep⟩⟩ (h61 G M Q Z B hc n t hs)
      · exact absurd hs.cardN (h54 G M Q Z B hc n t s5 ⟨K, fK, finK, hK, m, by omega, hrep⟩)
    · have hP : OmegaPlusNat hc t m := ⟨K, fK, finK, hK, hrep⟩
      by_cases hm2 : m = 2
      · subst hm2
        exact Or.inl ⟨h62 G M Q Z B hc n t hs (Or.inl hP), Or.inl hP.quotSat⟩
      · have hn := h63a G M Q Z B hc n t hs m (by omega) (Or.inl hP)
        exact Or.inr ⟨m, by omega, hn, hX G M Q Z B hc n t hs m (by omega) hn (Or.inl hP)⟩
    · have hP : OmegaMinusNat hc t m := ⟨K, fK, finK, hK, b, c, hbc, hrep⟩
      by_cases hm2 : m = 2
      · subst hm2
        exact Or.inl ⟨h62 G M Q Z B hc n t hs (Or.inr hP), Or.inr hP.quotSat⟩
      · have hn := h63a G M Q Z B hc n t hs m (by omega) (Or.inr hP)
        exact Or.inr ⟨m, by omega, hn, hX G M Q Z B hc n t hs m (by omega) hn (Or.inr hP)⟩

end CFSG.RankThree.GF2n.Stroth80
