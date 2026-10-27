module

public import CFSG.Quasithin.Background.F7TwoInvSporModel
public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.Sporadic.SmallOddCore.HSAut
public import Certificates.Certificate7416

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Blueprint

section Check


theorem hsInvChk_spec :
    orderOf (tp 3850 (hsCentTbl 12) * hsGen 0 * (tp 3850 (hsCentTbl 12))⁻¹ * (hsGen 0)⁻¹) = 3 ∧
    orderOf (tp 3850 (hsCentTbl 12) * hsGen 1 * (tp 3850 (hsCentTbl 12))⁻¹ * (hsGen 1)⁻¹) = 6 ∧
    orderOf (tp 3850 (hsCentTbl 21) * hsGen 0 * (tp 3850 (hsCentTbl 21))⁻¹ * (hsGen 0)⁻¹) = 3 ∧
    orderOf (tp 3850 (hsCentTbl 21) * hsGen 1 * (tp 3850 (hsCentTbl 21))⁻¹ * (hsGen 1)⁻¹) = 3 ∧
    orderOf (tp 3850 (hsCentTbl 34) * hsGen 0 * (tp 3850 (hsCentTbl 34))⁻¹ * (hsGen 0)⁻¹) = 3 ∧
    orderOf (tp 3850 (hsCentTbl 34) * hsGen 1 * (tp 3850 (hsCentTbl 34))⁻¹ * (hsGen 1)⁻¹) = 10 := by
  have h := Certificates.certificate7416
  simp only [hsInvChk, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hp12, hp21, hp34, hi12, hi21, hi34, h12a, h12b, h21a, h21b, h34a, h34b⟩ := h
  have repA : Rep 3850 hsPGTbls[0]! (hsGen 0) := hs_groupData.rep 0 (by simp [hsPGTbls])
  have repB : Rep 3850 hsPGTbls[1]! (hsGen 1) := hs_groupData.rep 1 (by simp [hsPGTbls])
  obtain ⟨oa, ob, -, -⟩ := hs_word_orders
  have key : ∀ {T : Table} {r s my : ℕ} {j : ℕ} {y : Equiv.Perm (Fin 3850)},
      permOK 3850 T = true → involOK 3850 T = true → Rep 3850 hsPGTbls[j]! y →
      orderOf y = my → 0 < r → 0 < s → 0 < my →
      pairTest 3850 r s 2 my T hsPGTbls[j]! = true →
      orderOf (tp 3850 T * y * (tp 3850 T)⁻¹ * y⁻¹) = s := by
    intro T r s my j y hp hi hy hoy hr hs hmy hpt
    have hT := rep_tp hp
    exact ((pairTest_iff perm_faithful hT hy hr hs
      (orderOf_eq_two_of_involOK (by norm_num) hT hi) hoy (by norm_num) hmy).1 hpt).2
  exact ⟨key hp12 hi12 repA oa (by norm_num) (by norm_num) (by norm_num) h12a,
    key hp12 hi12 repB ob (by norm_num) (by norm_num) (by norm_num) h12b,
    key hp21 hi21 repA oa (by norm_num) (by norm_num) (by norm_num) h21a,
    key hp21 hi21 repB ob (by norm_num) (by norm_num) (by norm_num) h21b,
    key hp34 hi34 repA oa (by norm_num) (by norm_num) (by norm_num) h34a,
    key hp34 hi34 repB ob (by norm_num) (by norm_num) (by norm_num) h34b⟩

end Check

section Classes


theorem invAutGen_hsP :
    ∀ φ : MulAut hsP, φ * φ = 1 → φ ≠ 1 → InvAutGen hsP φ := by
  have hM := hs_autModel
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  have hgen : Subgroup.closure ({hsa0, hsa1} : Set hsP) = ⊤ :=
    CFSG.Sporadic.Mathieu.closure_pair_eq_top rfl _ _
  obtain ⟨c12a, c12b, c21a, c21b, c34a, c34b⟩ := hsInvChk_spec
  obtain ⟨-, -, -, c5b⟩ := hs_word_orders
  refine invAutGen_of_model hM.le hM.conj_mem hM.surj hM.inj hgen
    (hsRows.map fun r => tp 3850 r.rep) ?_ ?_
  · intro x hxR hx2 hx1
    have hord : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
    obtain ⟨r, hr, g, hg, hxg⟩ := hcover x hxR hord
    exact ⟨tp 3850 r.rep, List.mem_map_of_mem hr, g, hg, hxg⟩
  · intro ρ hρ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hρ
    refine ⟨(hrows r hr).1, 1, one_mem _, ?_⟩
    simp only [one_mul, inv_one, mul_one]
    simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · dsimp only
      have hb5 := forall_pow_two_pow_ne_one_of_orderOf (s := 0) (m := 5) (by decide)
        (by norm_num) (c5b.trans (by norm_num))
      rw [hs_tp_rep_a]
      exact seedOK_pair (Or.inr rfl) (Or.inl hb5) (Or.inr hb5)
    · dsimp only
      have ha := forall_pow_two_pow_ne_one_of_orderOf (s := 0) (m := 3) (by decide)
        (by norm_num) (c12a.trans (by norm_num))
      have hb := forall_pow_two_pow_ne_one_of_orderOf (s := 1) (m := 3) (by decide)
        (by norm_num) (c12b.trans (by norm_num))
      exact seedOK_pair (Or.inl ha) (Or.inl hb) (Or.inl ha)
    · dsimp only
      have ha := forall_pow_two_pow_ne_one_of_orderOf (s := 0) (m := 3) (by decide)
        (by norm_num) (c21a.trans (by norm_num))
      have hb := forall_pow_two_pow_ne_one_of_orderOf (s := 0) (m := 3) (by decide)
        (by norm_num) (c21b.trans (by norm_num))
      exact seedOK_pair (Or.inl ha) (Or.inl hb) (Or.inl ha)
    · dsimp only
      have ha := forall_pow_two_pow_ne_one_of_orderOf (s := 0) (m := 3) (by decide)
        (by norm_num) (c34a.trans (by norm_num))
      have hb := forall_pow_two_pow_ne_one_of_orderOf (s := 1) (m := 5) (by decide)
        (by norm_num) (c34b.trans (by norm_num))
      exact seedOK_pair (Or.inl ha) (Or.inl hb) (Or.inl ha)

theorem invAutGen_carrier_HS :
    ∀ φ : MulAut (NativeSporadic.Carrier .HS), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .HS) φ :=
  invAutGen_of_mulEquiv_forall hsPermEquiv invAutGen_hsP

end Classes

end CFSG.Quasithin.F7Two
