module

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.Background.E2TwoProofSporM23Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import Certificates.Certificate7123
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

namespace E2P

namespace SporB

section List

variable {Γ : Type} [Group Γ] {S : Subgroup Γ} {Y : ℕ → Subgroup Γ} {L : Array ℕ} {N k : ℕ}

theorem hasInvPair_of_list_incl (hS : IsSylowTwoOf S ⊤)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hSY : ∀ j < L.size, S ≤ Y j) (hcard : ∀ j < L.size, Nat.card (Y j) = L[j]! * 2 ^ k)
    (hΓ : Nat.card Γ = N * 2 ^ k) {a b : ℕ} (ha : a < L.size) (hb : b < L.size)
    (hua : ∀ j < L.size + 1, latSz L N j = latSz L N a → j = a)
    (hub : ∀ j < L.size + 1, latSz L N j = latSz L N b → j = b)
    (hmax : ∀ j < L.size, Y a ≤ Y j → j = a) (hnot : ¬ Y b ≤ Y a) : HasInvPair Γ := by
  refine hasInvPair_of_unique hS (list_S_le hSY a) (list_S_le hSY b)
    (list_ne_top hcard hΓ ha hua) (list_ne_top hcard hΓ hb hub) (list_unique hall hcard hΓ hua)
    (list_unique hall hcard hΓ hub) ?_
  obtain ⟨j, hj, hjZ⟩ := hall _ (le_sup_of_le_left (list_S_le hSY a) :
    S ≤ memberOrTop L.size Y a ⊔ memberOrTop L.size Y b)
  rw [hjZ]
  by_cases hjL : j < L.size
  · exfalso
    rw [list_member ha, list_member hb, list_member hjL] at hjZ
    have hja : j = a := hmax j hjL (le_sup_left.trans hjZ.le)
    rw [hja] at hjZ
    exact hnot (le_sup_right.trans hjZ.le)
  · unfold memberOrTop
    rw [ite_eq_right hjL]

end List

section M23

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23_card m23_eq_closure)

noncomputable abbrev m23CtxB :
    LatCtx ↥CFSG.Blueprint.NativeSporadic.M23 23 (List ℕ) :=
  m23Ctx

theorem m23_Y_le_iff
    {j jj : ℕ} (hj : j < 16)
    (hjj : jj < 16) : m23CtxB.Y j ≤ m23CtxB.Y jj ↔ jj ∈ m23Incl[j]! := by
  rw [m23Ctx_Y, m23Ctx_Y]
  exact Certificates.certificate7123 j hj jj hjj

theorem hasInvPair_M23 :
    HasInvPair ↥CFSG.Blueprint.NativeSporadic.M23 := by
  have hL : m23CtxB.D.Om.map (fun o => o.lbl.size) =
      #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] := m23_lat_cert.2.2
  have hN : m23CtxB.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  have hS : IsSylowTwoOf m23CtxB.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxB.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m23CtxB.S
    rw [m23CtxB.S_card, m23CtxB.hΓ, hN] at h1
    have h2 : m23CtxB.S.index = 79695 := by
      have : m23CtxB.k = 7 := rfl
      rw [this] at h1
      omega
    rw [h2]
    norm_num
  refine hasInvPair_of_list_incl hS (lat_all m23CtxB hL) (fun j _ => m23CtxB.S_le_Y j)
    (lat_card m23CtxB hL) (by rw [m23CtxB.hΓ, hN]) (a := 1) (b := 15) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (fun j hj h => ?_) ?_
  · have hj16 : j < 16 := by simpa using hj
    have h1 := (m23_Y_le_iff (j := 1) (jj := j) (by norm_num) hj16).mp h
    exact (by decide : ∀ i < 16, i ∈ m23Incl[1]! → i = 1) j hj16 h1
  · intro h
    have := (m23_Y_le_iff (j := 15) (jj := 1) (by norm_num) (by norm_num)).mp h
    exact absurd this (by decide)

theorem asc86bClauseB_M23 :
    Asc86bClauseB .M23 :=
  @asc86bClauseB_of_hasInvPair .M23 ↥CFSG.Blueprint.NativeSporadic.M23 inferInstance
    inferInstance (MulEquiv.refl _) hasInvPair_M23

end M23

end SporB

end E2P

end CFSG.Quasithin
