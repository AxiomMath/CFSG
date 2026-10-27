module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactAutSylowM22
public import CFSG.Quasithin.Vol2.KGFactAutSylowM23
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Blueprint.NativeSporadic
open CFSG.Open (pCoreOf)

theorem noFiveOver_of_rows {W : Type} [Group W] [Finite W] (mems : List Mem) {k m : ℕ}
    (hW : Nat.card W = 2 ^ k * m) (hm : ¬ 2 ∣ m) (hm5 : m ≠ 5)
    (hrows : ∀ r ∈ mems, r.order ≠ 5 * 2 ^ k)
    (hover : ∀ S H : Subgroup W, IsSylowTwoOf S ⊤ → S ≤ H →
      H = ⊤ ∨ ∃ r ∈ mems, Nat.card H = r.order ∧ Nat.card (pCoreOf 2 H) = r.o2 ∧
        ∀ (N : Subgroup H) [N.Normal], IsPGroup 2 (H ⧸ N) → Nat.card (H ⧸ N) ≤ r.quot2) :
    NoFiveOver W := by
  intro S H hS hSH hcard
  rw [card_eq_of_isSylowTwoOf_top hS hW hm] at hcard
  rcases hover S H hS hSH with rfl | ⟨r, hr, hr1, -⟩
  · rw [Subgroup.card_top, hW, mul_comm 5] at hcard
    exact hm5 (Nat.eq_of_mul_eq_mul_left (by positivity) hcard)
  · exact hrows r hr (by rw [← hr1]; exact hcard)

theorem fiveRigid_M22 :
    FiveRigid (Carrier .M22) := by
  have : Finite (Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.1
  have : IsSimpleGroup (Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hcard0 : Nat.card (Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  have hcard : Nat.card (Carrier .M22) = 2 ^ 7 * 3465 := by
    rw [hcard0]
    norm_num
  have hZ := center_eq_bot_of_card_not_prime (W := Carrier .M22) (by rw [hcard]; norm_num)
  refine ⟨hZ, fiveInner_of_card_outer_le_two
    (CFSG.Quasithin.S152W.card_outer_le_two_of_card_aut hZ
      CFSG.Sporadic.Schreier.m22_mulAut_card), ?_⟩
  exact noFiveOver_of_rows CFSG.Quasithin.H13.KGSporLat.m22Mems hcard (by decide) (by decide)
    (by decide)
    (fun S H hS hSH => CFSG.Quasithin.H13.KGSporLat.m22_overgroups ⟨MulEquiv.refl _⟩ hS hSH)

theorem fiveRigid_M23 :
    FiveRigid (Carrier .M23) := by
  have : Finite (Carrier .M23) := CFSG.Sporadic.Mathieu.fam_m23_simplicity.1
  have : IsSimpleGroup (Carrier .M23) := CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
  have hcard0 : Nat.card (Carrier .M23) = 10200960 := CFSG.Sporadic.Schreier.m23_card
  have hcard : Nat.card (Carrier .M23) = 2 ^ 7 * 79695 := by
    rw [hcard0]
    norm_num
  have hZ := center_eq_bot_of_card_not_prime (W := Carrier .M23) (by rw [hcard]; norm_num)
  refine ⟨hZ, fiveInner_of_card_outer_le_two
    (CFSG.Quasithin.H13.KGAutSyl.card_outer_le_two_of_inner
      CFSG.QuasithinUnique.Ch1.m23_all_inner), ?_⟩
  exact noFiveOver_of_rows CFSG.Quasithin.H13.KGSporLat.m23Mems hcard (by decide) (by decide)
    (by decide)
    (fun S H hS hSH => CFSG.Quasithin.H13.KGSporLat.m23_overgroups ⟨MulEquiv.refl _⟩ hS hSH)

theorem fiveRigid_HS :
    FiveRigid (Carrier .HS) := by
  have hcard0 : Nat.card (Carrier .HS) = 44352000 := CFSG.Sporadic.HS.card_HS
  have : Finite (Carrier .HS) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have : IsSimpleGroup (Carrier .HS) := CFSG.Sporadic.HS.isSimpleGroup_HS
  have hcard : Nat.card (Carrier .HS) = 2 ^ 9 * 86625 := by
    rw [hcard0]
    norm_num
  have hZ := center_eq_bot_of_card_not_prime (W := Carrier .HS) (by rw [hcard]; norm_num)
  refine ⟨hZ, fiveInner_of_card_outer_le_two
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.hs_outer_card_le
      CFSG.Sporadic.Schreier.hsPermEquiv), ?_⟩
  exact noFiveOver_of_rows HS.hsMems hcard (by decide) (by decide) (by decide)
    (fun S H hS hSH => HS.hs_overgroups ⟨MulEquiv.refl _⟩ hS hSH)

theorem fiveRigid_Ru :
    FiveRigid (Carrier .Ru) := by
  have hcard0 : Nat.card (Carrier .Ru) = 145926144000 := CFSG.Sporadic.Ru.card_Ru
  have : Finite (Carrier .Ru) := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num)
  have : IsSimpleGroup (Carrier .Ru) := CFSG.Sporadic.Ru.isSimpleGroup_Ru
  have hcard : Nat.card (Carrier .Ru) = 2 ^ 14 * 8906625 := by
    rw [hcard0]
    norm_num
  have hZ := center_eq_bot_of_card_not_prime (W := Carrier .Ru) (by rw [hcard]; norm_num)
  have h1 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      CFSG.Sporadic.RuSchreier.ruP) ≤ 2 := by
    rw [CFSG.Sporadic.RuSchreier.card_outer_ruP]
    norm_num
  refine ⟨hZ, fiveInner_of_card_outer_le_two
    (CFSG.Sporadic.Schreier.outer_card_le_of_equiv h1 CFSG.Sporadic.RuSchreier.ruEquivP), ?_⟩
  exact noFiveOver_of_rows Ru.ruMems hcard (by decide) (by decide) (by decide)
    (fun S H hS hSH => Ru.ru_overgroups ⟨MulEquiv.refl _⟩ hS hSH)

end CFSG.Quasithin.H13.FiveNorm
