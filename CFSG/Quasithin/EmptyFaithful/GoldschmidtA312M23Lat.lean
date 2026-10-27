
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Inputs
public import CFSG.Quasithin.Background.HSporLatM23Sg
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Core
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.A312Words

section

theorem m23_complete : ∀ Z : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23, m23Ctx.S ≤ Z →
    ∃ j ≤ 16, Z = memberOrTop 16 m23Ctx.Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := m23Ctx.complete Z hZ
  rw [m23_J] at hj ⊢
  exact ⟨j, hj, by simp⟩

theorem m23_S_sylow : IsSylowTwoOf m23Ctx.S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨m23Ctx.S_isPGroup, ?_⟩
  have hN : m23Ctx.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  have h1 := Subgroup.card_mul_index m23Ctx.S
  rw [m23Ctx.S_card, m23Ctx.hΓ, hN] at h1
  have h2 : m23Ctx.S.index = 79695 := by
    have : m23Ctx.k = 7 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

theorem m23_Om_size (j : ℕ) (hj : j < 16) :
    m23Ctx.D.Om[j]!.lbl.size =
      #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9][j]! := by
  rw [om_size_eq m23_lat_cert.2.2 (by simpa using hj)]

theorem m23_member_card (j : ℕ) (hj : j < 16) :
    Nat.card (m23Ctx.Y j) =
      #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9][j]! * 128 := by
  have h1 : j < m23Ctx.J := by rw [m23_J]; exact hj
  rw [m23Ctx.Y_card h1]
  show m23Ctx.D.Om[j]!.lbl.size * 2 ^ 7 = _
  rw [m23_Om_size j hj]
  norm_num

end

theorem m23_letters
    {j : ℕ} (hj : j < 16) :
    m23Ctx.D.sTabs ++ m23Ctx.D.mt[j]! = m23Letters j := by
  have hJ : j < m23Ctx.J := by rw [m23_J]; exact hj
  have hsT : m23Ctx.D.sTabs = m23STabs := by
    rw [← m23Ctx.hsg]
    exact m23_sGens.1
  have hmt : m23Ctx.D.mt[j]! =
      (m23MwLit[j]!).map (fun w => wordTabA #[m23ta.toArray, m23tb.toArray] 23 w) := by
    have h := (m23Ctx.membersOK.2.2.2.2 j hJ).2.1
    have hmw : m23Ctx.D.mw = m23MwLit := m23_mw
    rw [hmw] at h
    exact h
  rw [hsT, hmt]
  rfl

end CFSG.Quasithin.A312M23
