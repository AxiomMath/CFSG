module

public import CFSG.Quasithin.EmptyFaithful.S151S9TM23
import CFSG.Quasithin.Background.E2TwoProofSporM23
import CFSG.Quasithin.Background.HSporLatMathieu

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat

theorem m23CtxB_S_card :
    Nat.card m23CtxB.S = 2 ^ 7 :=
  m23CtxB.S_card

theorem m23_card_Y1 :
    Nat.card (m23CtxB.Y 1) = 443520 := by
  have hL : m23CtxB.D.Om.map (fun o => o.lbl.size) = S151S9T.m23Ls := m23_lat_cert.2.2
  rw [lat_card m23CtxB hL 1 (by decide)]
  rfl

theorem m23_centre_czv
    (h : S151S9T.m23CheckD) :
    ∃ z₀ : ↥CFSG.Blueprint.NativeSporadic.M23, orderOf z₀ = 2 ∧
      centerOf m23CtxB.S = Subgroup.zpowers z₀ ∧
      ∀ j < 16, (S151S9T.m23Wit.czv[j]! = true ↔
        m23CtxB.Y j ≤ Subgroup.centralizer ({z₀} : Set ↥CFSG.Blueprint.NativeSporadic.M23)) := by
  obtain ⟨z₀, hz2, hZ, hzT⟩ := S151S9T.m23B_centre
  have hok : S151S9T.m23Wit.Ok 23 m23CtxB.A.act m23CtxB.Δ m23CtxB.D (tab 23 z₀).toArray := by
    rw [hzT]
    exact h
  have hz₀ : z₀ ∈ centerOf m23CtxB.S := hZ ▸ Subgroup.mem_zpowers z₀
  have hL : m23CtxB.D.Om.map (fun o => o.lbl.size) = S151S9T.m23Ls := m23_lat_cert.2.2
  have hJ : m23CtxB.J = 16 := lat_J_eq m23CtxB hL
  refine ⟨z₀, hz2, hZ, fun j hj => ?_⟩
  exact (S151S9T.Idx3Wit.sound m23CtxB hz₀ S151S9T.m23Wit hok).2 j (by rw [hJ]; exact hj)

theorem m23_lat_cases
    {Y : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23}
    (hSY : m23CtxB.S ≤ Y) : (∃ j < 16, Y = m23CtxB.Y j) ∨ Y = ⊤ := by
  have hL : m23CtxB.D.Om.map (fun o => o.lbl.size) = S151S9T.m23Ls := m23_lat_cert.2.2
  rcases S151S9T.LatAux.lat_cases m23CtxB hL hSY with ⟨j, hjL, hj⟩ | htop
  · exact Or.inl ⟨j, hjL, hj⟩
  · exact Or.inr htop

end CFSG.Quasithin.S151S9U
