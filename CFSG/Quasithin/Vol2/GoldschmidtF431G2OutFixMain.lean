module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixAbsMain
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixCount

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.QuasithinUnique

section G2

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem U_stable (σ₁ : K ≃+* K) (k : ℕ) (x : C K) : (fieldAut K σ₁ ^ k) x ∈ U K ↔ x ∈ U K := by
  have h : ∀ s : C K, s ∈ U K ↔ fieldAut K (σ₁ ^ k) s ∈ U K :=
    fieldAut_mem_autStab_U (σ₁ ^ k)
  have := (h x).symm
  rwa [map_pow] at this

theorem card_fixSub {r : ℕ} {σ : K ≃+* K} (hr2 : 2 ≤ r) (hK : Nat.card K = r ^ 2)
    (hσ : ∀ x, σ x = x ^ r) : Nat.card ↥(fixSub (fieldAut K σ) (U K)) = r ^ 6 := by
  have h1 : ((fixSub (fieldAut K σ) (U K) : Subgroup (C K)) : Set (C K)) = twFix σ 1 := by
    ext x
    simp [fixSub, twFix]
  have e : (fixK σ).ncard = r := by
    rw [← Nat.card_coe_set_eq]
    exact card_fixK_frobenius σ hr2 hK hσ
  calc Nat.card ↥(fixSub (fieldAut K σ) (U K))
      = ((fixSub (fieldAut K σ) (U K) : Subgroup (C K)) : Set (C K)).ncard :=
        Nat.card_coe_set_eq _
    _ = (twFix σ 1).ncard := by rw [h1]
    _ = (fixK σ).ncard ^ 6 := ncard_twFix_one σ
    _ = r ^ 6 := by rw [e]

theorem ncard_twistFix_le {r : ℕ} {σ : K ≃+* K} (hr2 : 2 ≤ r) (hK : Nat.card K = r ^ 2)
    (hσ : ∀ x, σ x = x ^ r) {u : C K} (hu : u ∈ U K) :
    (twistFix (fieldAut K σ) (U K) u).ncard ≤ r ^ 6 := by
  have e : (fixK σ).ncard = r := by
    rw [← Nat.card_coe_set_eq]
    exact card_fixK_frobenius σ hr2 hK hσ
  have h := ncard_twFix_le σ hu
  rw [e] at h
  exact h

theorem pow_six_lt_of_four_le {r : ℕ} (hr2 : 2 ≤ r) (hK : Nat.card K = r ^ 2) {c : ℕ}
    (hc : Nat.card K ^ 4 ≤ c) : r ^ 6 < c := by
  rw [hK, ← pow_mul] at hc
  exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) (by norm_num)) hc

theorem pow_four_le_card_centralizer_root {y : C K}
    (hy : y = xa 1 ∨ y = xu 1 ∨ y = xv 1 ∨ y = xb 1 ∨ y = xc 1) :
    Nat.card K ^ 4 ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({y} : Set (C K))) := by
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact pow_four_le_card_centralizer_xa
  · exact pow_four_le_card_centralizer_xu
  · exact pow_four_le_card_centralizer_xv
  · exact pow_four_le_card_centralizer_xb
  · exact pow_four_le_card_centralizer_xc

theorem fieldAut_root_fixed (σ : K ≃+* K) {y : C K}
    (hy : y = xa 1 ∨ y = xu 1 ∨ y = xv 1 ∨ y = xb 1 ∨ y = xc 1) : fieldAut K σ y = y := by
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · exact fieldAut_xa_one σ
  · exact fieldAut_xu_one σ
  · exact fieldAut_xv_one σ
  · exact fieldAut_xb_one σ
  · exact fieldAut_xc_one σ

variable {H : Type} [Group H] [Finite H] {Φ : C K →* H} {ψ : H} {σ₁ : K ≃+* K}

theorem OutProps.g2_isSylowTwoOf_Tf (P : OutProps Φ ψ (fieldAut K σ₁)) (ha : 1 ≤ twoExp ψ)
    {r : ℕ} {σ : K ≃+* K} (hr2 : 2 ≤ r) (hK : Nat.card K = r ^ 2) (hσ : ∀ x, σ x = x ^ r)
    (hδ : involAut ψ (fieldAut K σ₁) = fieldAut K σ) (hUS : IsSylowTwoOf (U K) ⊤)
    {N : Subgroup H} (hTN : spT Φ ψ (U K) ≤ N) :
    IsSylowTwoOf (spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H))
      (Subgroup.centralizer ({invol ψ} : Set H) ⊓ N) := by
  have : Finite (C K) := Subtype.finite
  refine P.isSylowTwoOf_inf_centralizer_invol ha (U_stable σ₁) hUS hTN (m := r ^ 6) ?_ ?_
  · rw [hδ, card_fixSub hr2 hK hσ]
  · intro u hu
    rw [hδ]
    exact ncard_twistFix_le hr2 hK hσ hu

theorem OutProps.g2_card_Tf_lt (P : OutProps Φ ψ (fieldAut K σ₁))
    {r : ℕ} {σ : K ≃+* K} (hr2 : 2 ≤ r) (hK : Nat.card K = r ^ 2)
    (hσ : ∀ x, σ x = x ^ r) (hδ : involAut ψ (fieldAut K σ₁) = fieldAut K σ) {y : C K}
    (hy : y = xa 1 ∨ y = xu 1 ∨ y = xv 1 ∨ y = xb 1 ∨ y = xc 1) :
    Nat.card ↥(spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H)) <
      Nat.card ↥(spT Φ ψ (U K) ⊓ Subgroup.centralizer ({Φ y} : Set H)) := by
  refine P.card_inf_centralizer_invol_lt (U_stable σ₁) (m := r ^ 6) ?_
    (fieldAut_root_fixed σ₁ hy)
    (pow_six_lt_of_four_le hr2 hK (pow_four_le_card_centralizer_root hy))
  rw [hδ, card_fixSub hr2 hK hσ]

theorem OutProps.g2_W_le (P : OutProps Φ ψ (fieldAut K σ₁)) :
    centerOf (spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H)) ⊓
        ⁅spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H),
          spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H)⁆ ≤
      centerOf ((U K).map Φ) :=
  P.spW_le_centerOf (U_stable σ₁) (xa_mem_U 1) (xr_mem_U 1) (fieldAut_xa_one σ₁)
    (fieldAut_xr_one σ₁) fun _ hx ha hr _ hw => central_of_comm_xa_xr hx ha hr hw

theorem OutProps.g2_W_mem (P : OutProps Φ ψ (fieldAut K σ₁)) :
    Φ (xc 1) ∈ centerOf (spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H)) ⊓
        ⁅spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H),
          spT Φ ψ (U K) ⊓ Subgroup.centralizer ({invol ψ} : Set H)⁆ ∧ Φ (xc 1) ≠ 1 := by
  refine ⟨P.map_mem_spW (U_stable σ₁) (xa_mem_U 1) (xb_mem_U 1) (fieldAut_xa_one σ₁)
    (fieldAut_xb_one σ₁) (fieldAut_xc_one σ₁) xa_one_comm_xb_one
    fun w hw => xc_comm_of_mem_U hw 1, fun h => ?_⟩
  have h1 : xc (1 : K) = 1 := P.inj (h.trans (map_one Φ).symm)
  exact one_ne_zero (xc_eq_one_iff.1 h1)

end G2

end CFSG.Quasithin.H13.F431.G2.OutK
