
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsMemBase

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsPCore
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312HsQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatIncl
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.Quasithin
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_Y_le_iff
    {j jj : ℕ} (hj : j < 5)
    (hjj : jj < 5) : hsCtx.Y j ≤ hsCtx.Y jj ↔ jj ∈ hsIncl[j]! :=
  hs_incl hj hjj

theorem hs_row_one :
    Nat.card (CFSG.pCore 2 ↥(hsCtx.Y 1)) = 2 ^ 6 ∧
      ∀ (N : Subgroup ↥(hsCtx.Y 1)) [N.Normal], IsPGroup 2 (↥(hsCtx.Y 1) ⧸ N) →
        Nat.card (↥(hsCtx.Y 1) ⧸ N) ≤ 2 := by
  obtain ⟨m, hm, h1, h2, h3⟩ := hs_row 1 (by norm_num)
  have hc : Nat.card (hsCtx.Y 1) = 7680 := by
    rw [hs_member_card 1 (by norm_num)]
    rfl
  simp only [hsMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (exfalso; simp only at h1; omega)
    | exact ⟨card_pCore_of_card_pCoreOf (by simpa using h2), fun N _ hp => h3 N hp⟩

theorem hs_row_two :
    Nat.card (CFSG.pCore 2 ↥(hsCtx.Y 2)) = 2 ^ 6 := by
  obtain ⟨m, hm, h1, h2, -⟩ := hs_row 2 (by norm_num)
  have hc : Nat.card (hsCtx.Y 2) = 10752 := by
    rw [hs_member_card 2 (by norm_num)]
    rfl
  simp only [hsMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (exfalso; simp only at h1; omega)
    | exact card_pCore_of_card_pCoreOf (by simpa using h2)

theorem hs_V1_struct :
    IsZ4StarExtra2 ↥(CFSG.pCore 2 ↥(hsCtx.Y 1)) :=
  (Certificates.certificate4102.2.2.2.1).1

theorem hs_V2_struct :
    IsZ4Cubed ↥(CFSG.pCore 2 ↥(hsCtx.Y 2)) :=
  (Certificates.certificate4102.2.2.2.1).2.1

end CFSG.Quasithin.A312Hs
