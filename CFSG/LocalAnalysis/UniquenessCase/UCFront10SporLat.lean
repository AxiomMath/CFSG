module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeCertificate

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
public import CFSG.Quasithin.H13.NQCatT513Lat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Model
public import CFSG.Sporadic.J2
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Sporadic.SmallF2

theorem k105SporAt_of_list {s : TauCeti.SporadicName} {Γ : Type} [Group Γ] [Finite Γ]
    {S₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) {Y : ℕ → Subgroup Γ} {L : Array ℕ}
    (hall : ∀ Z : Subgroup Γ, S₀ ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hcard : ∀ j < L.size, Nat.card ↥(Y j) = L[j]! * Nat.card ↥S₀)
    (hL : ∀ j < L.size, L[j]! = 1 ∨ 3 ∣ L[j]!) {N : ℕ} (hΓ : Nat.card Γ = N * Nat.card ↥S₀)
    (hN : 3 ∣ N) (e : CFSG.Blueprint.NativeSporadic.Carrier s ≃* Γ) : K105SporAt s := by
  refine k105SporAt_of_index hS₀ (fun Z hZ _ m hm => ?_) e
  rcases CFSG.Quasithin.H13.NQCat.T513P.index_of_list hall hcard hZ hm with ⟨j, hj, rfl⟩ | h
  · exact hL j hj
  · have hpos : 0 < Nat.card ↥S₀ := Nat.card_pos
    rw [hΓ] at h
    rw [← Nat.eq_of_mul_eq_mul_right hpos h]
    exact Or.inr hN

theorem k105SporAt_J2 :
    K105SporAt .J2 := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J2 ≃* ↥CFSG.Sporadic.J2.J :=
    CFSG.Sporadic.J2.nativeEquiv
  have hS : Nat.card ↥CFSG.Quasithin.A312J2.j2CtxA.S = 2 ^ 7 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top CFSG.Quasithin.A312J2.j2A_sylow
      (m := 4725) (by rw [CFSG.Sporadic.J2.card_J]; norm_num) (by decide)
  exact k105SporAt_of_list (s := .J2) CFSG.Quasithin.A312J2.j2A_sylow
    (CFSG.Quasithin.E2P.SporB.lat_all _ CFSG.Quasithin.A312J2.j2A_hL)
    (fun j hj => by rw [hS]; exact CFSG.Quasithin.A312J2.j2A_card hj) (by decide) (N := 4725)
    (by rw [CFSG.Sporadic.J2.card_J, hS]; norm_num) (by norm_num) e

open CFSG.QuasithinUnique.Ch1.SporLat.HS in
open CFSG.Sporadic.HS.Native (hsData) in
theorem k105SporAt_HS :
    K105SporAt .HS := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .HS ≃* ↥(J hsData) :=
    seedEquiv hs_facts.toBaseFacts
  exact k105SporAt_of_list (s := .HS) hs_S_sylow (L := #[1, 15, 21, 3, 3]) hs_complete
    (fun j hj => by rw [hs_card_S]; exact hs_member_card j hj) (by decide) (N := 86625)
    (by norm_num [hs_card, hs_card_S]) (by norm_num) e

open CFSG.QuasithinUnique.Ch1.SporLat.He in
theorem k105SporAt_He :
    K105SporAt .He := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .He ≃* ↥CFSG.Sporadic.He.J :=
    CFSG.Sporadic.He.heEquivJ
  exact k105SporAt_of_list (s := .He) he_S_sylow (L := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3])
    he_complete (fun j hj => by rw [he_card_S]; exact he_member_card j hj) (by decide)
    (N := 3935925) (by rw [he_card, he_card_S]; ring) (by norm_num) e

open CFSG.QuasithinUnique.Ch1.SporLat.Ru in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem k105SporAt_Ru :
    K105SporAt .Ru := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .Ru ≃* ↥(J ruData) :=
    seedEquiv ru_facts.toBaseFacts
  exact k105SporAt_of_list (s := .Ru) ru_S_sylow (L := #[1, 15, 21, 3, 3]) ru_complete
    (fun j hj => by rw [ru_card_S]; exact ru_member_card j hj) (by decide) (N := 8906625)
    (by norm_num [ru_card, ru_card_S]) (by norm_num) e

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
