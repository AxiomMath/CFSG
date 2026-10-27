module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QW
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516QJ
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Lift

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

theorem fact516Quot : Fact516Quot := by
  intro G _ _ T L D R N n hS hn hNR hLTN hnat
  obtain ⟨F, _, _, _, hF, ψ, Y, hc⟩ := hnat.exists_qcoord hS.sylow
  have hNe : IsElemAbelian 2 N :=
    ⟨⟨⟨fun x y => Subtype.ext (by
      have h := congrArg Subtype.val
        (hS.reduced.2.2.1.1.is_comm.comm ⟨x, hNR x.2⟩ ⟨y, hNR y.2⟩)
      exact h)⟩⟩,
      fun x hx => hS.reduced.2.2.1.2 x (hNR hx)⟩
  have hl : ∀ y : F, ∃ p : ↥N,
      (p : G) ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) ∧
        Y p = Multiplicative.ofAdd ![y, 0] := by
    intro y
    obtain ⟨x, hx⟩ := hc.surj (Multiplicative.ofAdd ![y, 0])
    have hx1 : (Multiplicative.toAdd (Y x)) 1 = 0 := by
      rw [hx]
      simp
    obtain ⟨p, hpN, hpx, hpS⟩ := fact516Lift n G L N (T ⊓ L) hnat hNe hS.sylow x x.2
      ((hc.snd_eq_zero_iff inf_le_right x).mp hx1)
    refine ⟨⟨p, hpN⟩, hpS, ?_⟩
    have h1 : Y ⟨p, hpN⟩ * (Y x)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      exact (hc.ker _).mpr hpx
    rw [← hx]
    exact mul_inv_eq_one.mp h1
  have h : QuotCtx T L D R N n F ψ Y := ⟨hS, hn, hNR, hLTN, hnat, hF, hc, hl⟩
  exact ⟨h.W, h.W_le_N, h.hyp.isTDMod, fun hW hq => h.le_four hW hq,
    hS.thompsonJ_le_centralizer hNR hLTN hc (h.W_le_N.trans hNR)
      (h.W_le_P.trans inf_le_right)⟩

end CFSG.Quasithin.H13
