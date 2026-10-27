module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P514Lab

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fix_off (F : FanTree Γ G) (h40 : Fan40 F) (h54 : Fan54 F) (T : Track Γ G)
    {z : G} {a r : ℤ} (hz : z ∈ T.line.Zc) (hcore : T.line.IsCoreC z a (a + 2))
    (hr : Odd r) {e : G} (he : e ∉ T.fixer) (he0 : e • T.line.vert (a + 2) = T.line.vert (a + 2))
    (hcomm : ∀ j : ℤ, a + 2 - r ≤ a + 1 + 2 * j → a + 1 + 2 * j ≤ a + 2 + r →
      e * lab T z j = lab T z j * e) :
    ∀ i, a + 2 - r ≤ i → i ≤ a + 2 + r → e • T.line.vert i = T.line.vert i := by
  obtain ⟨tL, tR, hfix⟩ := exists_fixIdx_interval' F T he (i₀ := a + 2) he0
  obtain ⟨m, hm⟩ := hr
  have h2 : tL ≤ a + 2 ∧ a + 2 ≤ tR := (hfix (a + 2)).1 he0
  have hmov : ∀ i, i < tL ∨ tR < i → ¬ e • T.line.vert i = T.line.vert i := fun i hi h => by
    have := (hfix i).1 h
    omega
  have hfx : ∀ i, tL ≤ i → i ≤ tR → e • T.line.vert i = T.line.vert i := fun i h1 h2 =>
    (hfix i).2 ⟨h1, h2⟩
  have hR : a + 2 + r ≤ tR := by
    by_contra hlt
    push Not at hlt
    rcases Int.even_or_odd (tR - a) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hj := hcomm k (by omega) (by omega)
      refine h54 h40 T.line (lab T z k) (a + 2 * k) (a + 2 + 2 * k)
        (lab_mem_Zc F T hz k) (isCoreC_lab F T k hcore) tR (tR + 1)
        (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) e
        (MulAction.mem_stabilizer_iff.2 (hfx tR (by omega) le_rfl))
        (fun h => hmov (tR + 1) (Or.inr (by omega)) (MulAction.mem_stabilizer_iff.1 h)) hj
    · have hj := hcomm (k + 1) (by omega) (by omega)
      refine h54 h40 T.line (lab T z (k + 1)) (a + 2 * (k + 1)) (a + 2 + 2 * (k + 1))
        (lab_mem_Zc F T hz (k + 1)) (isCoreC_lab F T (k + 1) hcore) tR (tR + 1)
        (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))) e
        (MulAction.mem_stabilizer_iff.2 (hfx tR (by omega) le_rfl))
        (fun h => hmov (tR + 1) (Or.inr (by omega)) (MulAction.mem_stabilizer_iff.1 h)) hj
  have hL : tL ≤ a + 2 - r := by
    by_contra hlt
    push Not at hlt
    rcases Int.even_or_odd (tL - a) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hj := hcomm (k - 1) (by omega) (by omega)
      refine h54 h40 T.line (lab T z (k - 1)) (a + 2 * (k - 1)) (a + 2 + 2 * (k - 1))
        (lab_mem_Zc F T hz (k - 1)) (isCoreC_lab F T (k - 1) hcore) tL (tL - 1)
        (Or.inl ⟨by omega, by omega⟩) e
        (MulAction.mem_stabilizer_iff.2 (hfx tL le_rfl (by omega)))
        (fun h => hmov (tL - 1) (Or.inl (by omega)) (MulAction.mem_stabilizer_iff.1 h)) hj
    · have hj := hcomm (k - 1) (by omega) (by omega)
      refine h54 h40 T.line (lab T z (k - 1)) (a + 2 * (k - 1)) (a + 2 + 2 * (k - 1))
        (lab_mem_Zc F T hz (k - 1)) (isCoreC_lab F T (k - 1) hcore) tL (tL - 1)
        (Or.inr (Or.inl ⟨by omega, by omega⟩)) e
        (MulAction.mem_stabilizer_iff.2 (hfx tL le_rfl (by omega)))
        (fun h => hmov (tL - 1) (Or.inl (by omega)) (MulAction.mem_stabilizer_iff.1 h)) hj
  intro i h1 h2
  exact hfx i (by omega) (by omega)

end P514

end CFSG.Quasithin.Fan86
