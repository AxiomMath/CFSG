module

public import CFSG.Quasithin.H13.U3L1312P
public import CFSG.Quasithin.H13.U3G2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G]

theorem conjugate_eq_cjSub' (A : Subgroup G) (g : G) : CFSG.conjugate A g = cjSub g⁻¹ A := rfl

theorem cjSub_eq_self {V : Subgroup G} {n : G} (hn : n ∈ normalizer (V : Set G)) :
    cjSub n V = V :=
  B2F.mem_normalizer_iff_cjSub_eq.1 hn

theorem cjSub_eq_bot_iff' (n : G) {X : Subgroup G} : cjSub n X = ⊥ ↔ X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective X (MulAut.conj n).injective

theorem cjSub_inf_centralizer_self {V Y : Subgroup G} {n : G}
    (hn : n ∈ normalizer (V : Set G)) :
    cjSub n Y ⊓ centralizer (V : Set G) = cjSub n (Y ⊓ centralizer (V : Set G)) := by
  rw [B2F.cjSub_inf, B2F.cjSub_centralizer, cjSub_eq_self hn]

theorem commutator_cjSub_mul {V : Subgroup G} {n : G} (hn : n ∈ normalizer (V : Set G)) (x : G) :
    ⁅V, cjSub (n * x) V⁆ = cjSub n ⁅V, cjSub x V⁆ := by
  rw [cjSub_mul, cjSub_commutator_eq, cjSub_eq_self hn]

@[expose] def PairHyp (V : Subgroup G) (x : G) : Prop :=
  ⁅V, cjSub x V⁆ ≠ ⊥ ∧ ⁅V, cjSub x V⁆ ≤ V ⊓ cjSub x V

theorem PairHyp.mul {V : Subgroup G} {x n : G} (h : PairHyp V x)
    (hn : n ∈ normalizer (V : Set G)) : PairHyp V (n * x) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [commutator_cjSub_mul hn, Ne, cjSub_eq_bot_iff']
    exact h1
  · rw [commutator_cjSub_mul hn, cjSub_mul]
    calc cjSub n ⁅V, cjSub x V⁆ ≤ cjSub n (V ⊓ cjSub x V) := cjSub_mono h2
      _ = V ⊓ cjSub n (cjSub x V) := by rw [B2F.cjSub_inf, cjSub_eq_self hn]

theorem PairHyp.inv {V : Subgroup G} {x : G} (h : PairHyp V x) : PairHyp V x⁻¹ := by
  obtain ⟨h1, h2⟩ := h
  have e : ⁅V, cjSub x⁻¹ V⁆ = cjSub x⁻¹ ⁅V, cjSub x V⁆ := by
    rw [cjSub_commutator_eq, cjSub_inv_cjSub, commutator_comm]
  refine ⟨?_, ?_⟩
  · rw [e, Ne, cjSub_eq_bot_iff']
    exact h1
  · rw [e]
    calc cjSub x⁻¹ ⁅V, cjSub x V⁆ ≤ cjSub x⁻¹ (V ⊓ cjSub x V) := cjSub_mono h2
      _ = V ⊓ cjSub x⁻¹ V := by rw [B2F.cjSub_inf, cjSub_inv_cjSub, inf_comm]

namespace HullSetting

variable [Finite G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem exists_isA1
    (S : HullSetting G T L V z) {x : G} (h : PairHyp V x)
    (hO : Nat.card ↥(cjSub x V ⊓ centralizer (V : Set G)) ≤
      Nat.card ↥(V ⊓ centralizer (cjSub x V : Set G))) :
    ∃ n ∈ normalizer (V : Set G), IsA1 (S.imgL (cjSub (n * x) V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := h
  have hVab := isElemAbelian_of_isElementaryAbelian' V
  have hXN : cjSub x V ≤ normalizer (V : Set G) :=
    le_normalizer_of_commutator_le (h2.trans inf_le_left)
  have hXab : IsElemAbelian 2 (cjSub x V) := isElemAbelian_cjSub hVab
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.hH.sylow
  obtain ⟨c, hcN, hcT⟩ := exists_cjSub_le_of_sylow P (by rw [hP]; exact S.hTV) hXN
    (B2F.isPGroup_of_isElemAbelian hXab)
  rw [hP, ← cjSub_mul] at hcT
  have hX₁N : cjSub (c * x) V ≤ normalizer (V : Set G) := hcT.trans S.hTV
  have hX₁ab : IsElemAbelian 2 (cjSub (c * x) V) := isElemAbelian_cjSub hVab
  have hc1 : Nat.card ↥(cjSub (c * x) V ⊓ centralizer (V : Set G)) =
      Nat.card ↥(cjSub x V ⊓ centralizer (V : Set G)) := by
    rw [cjSub_mul, cjSub_inf_centralizer_self hcN, card_cjSub]
  have hc2 : Nat.card ↥(V ⊓ centralizer (cjSub (c * x) V : Set G)) =
      Nat.card ↥(V ⊓ centralizer (cjSub x V : Set G)) := by
    rw [cjSub_mul, inf_centralizer_cjSub hcN, card_cjSub]
  have h64 : Nat.card (S.imgL (cjSub (c * x) V)) *
      Nat.card (linFix (S.imgL (cjSub (c * x) V))) = 64 := by
    rw [S.card_imgL hX₁N, ← S.card_inf_centralizer hX₁N]
    refine le_antisymm (S.card_mul_card_le hcT hX₁ab) ?_
    have h3 := relIndex_mul_card (cjSub (c * x) V ⊓ centralizer (V : Set G)) (cjSub (c * x) V)
    rw [inf_eq_left.2 (inf_le_left : cjSub (c * x) V ⊓ centralizer (V : Set G) ≤
      cjSub (c * x) V), card_cjSub, S.hV64, hc1] at h3
    rw [hc2]
    calc 64 = _ := h3.symm
      _ ≤ _ := Nat.mul_le_mul_left _ hO
  obtain ⟨m, hmE, hm⟩ :=
    exists_mask_of_eq64 (S.imgL_le_S0L hcT) (S.isElementaryAbelian_imgL hX₁ab) h64
  rcases hm with rfl | rfl | rfl | rfl
  ·
    exfalso
    have hbot : S.imgL (cjSub (c * x) V) = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      obtain ⟨k, hk, rfl⟩ := (mem_iff_IE (S.imgL_le_S0L hcT)).1 he
      rw [← hmE, ofMask_one, Finset.mem_singleton] at hk
      rw [hk, s0L_zero]
      exact Subgroup.one_mem _
    have hC := (S.imgL_eq_bot_iff hX₁N).1 hbot
    have h4 : ⁅V, cjSub (c * x) V⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.2 hC
    rw [commutator_cjSub_mul hcN, cjSub_eq_bot_iff'] at h4
    exact h1 h4
  ·
    obtain ⟨l, -, hlN, hlspec⟩ := S.exists_lift yGL_mem
    have hρ : S.rho ⟨l, hlN⟩ = yGL := S.rho_eq_of_spec hlN hlspec
    refine ⟨l * c, mul_mem hlN hcN, ?_⟩
    rw [mul_assoc, cjSub_mul l (c * x) V, S.imgL_cjSub hlN, hρ]
    exact isA1_map_conj (S.imgL_le_S0L hcT) hmE card_g13_codes.1 coe_yGL coe_yGL_inv
      conj_g1_codes
  · exact ⟨c, hcN, S.imgL_le_S0L hcT, hmE⟩
  ·
    obtain ⟨l, -, hlN, hlspec⟩ := S.exists_lift yaGL_mem
    have hρ : S.rho ⟨l, hlN⟩ = yaGL := S.rho_eq_of_spec hlN hlspec
    refine ⟨l * c, mul_mem hlN hcN, ?_⟩
    rw [mul_assoc, cjSub_mul l (c * x) V, S.imgL_cjSub hlN, hρ]
    exact isA1_map_conj (S.imgL_le_S0L hcT) hmE card_g13_codes.2 coe_yaGL coe_yaGL_inv
      conj_g3_codes

theorem exists_pairEq_of_le
    (S : HullSetting G T L V z) {x : G} (h : PairHyp V x)
    (hO : Nat.card ↥(cjSub x V ⊓ centralizer (V : Set G)) ≤
      Nat.card ↥(V ⊓ centralizer (cjSub x V : Set G))) :
    ∃ n ∈ normalizer (V : Set G),
      PairEq V (cjSub (n * x) V) S.V₃ ∧ v1Of V (cjSub (n * x) V) = S.V₁ := by
  obtain ⟨n, hn, hA⟩ := S.exists_isA1 h hO
  obtain ⟨-, h2⟩ := h.mul hn
  have hXN : cjSub (n * x) V ≤ normalizer (V : Set G) :=
    le_normalizer_of_commutator_le (h2.trans inf_le_left)
  have hP := S.pairEq_of_isA1 hXN (isElemAbelian_cjSub (isElemAbelian_of_isElementaryAbelian' V))
    (by rw [card_cjSub, S.hV64]) h2 hA
  exact ⟨n, hn, hP, S.v1Of_eq_of_isA1 hXN hP hA⟩

theorem exists_pairEq
    (S : HullSetting G T L V z) {x : G} (h : PairHyp V x) :
    ∃ n ∈ normalizer (V : Set G),
      PairEq V (cjSub (n * x) V) S.V₃ ∧ v1Of V (cjSub (n * x) V) = S.V₁ := by
  refine S.exists_pairEq_of_le h ?_
  by_contra hlt
  push Not at hlt
  have e1 := card_inf_centralizer_cjSub V x
  have e2 := card_inf_centralizer_cjSub V x⁻¹
  rw [inv_inv] at e2
  obtain ⟨n, hn, hP, -⟩ := S.exists_pairEq_of_le h.inv (by rw [e2, ← e1]; exact hlt.le)
  have e3 : Nat.card ↥(V ⊓ centralizer (cjSub (n * x⁻¹) V : Set G)) =
      Nat.card ↥(V ⊓ centralizer (cjSub x⁻¹ V : Set G)) := by
    rw [cjSub_mul, inf_centralizer_cjSub hn, card_cjSub]
  have e4 : Nat.card ↥(cjSub (n * x⁻¹) V ⊓ centralizer (V : Set G)) =
      Nat.card ↥(cjSub x⁻¹ V ⊓ centralizer (V : Set G)) := by
    rw [cjSub_mul, cjSub_inf_centralizer_self hn, card_cjSub]
  rw [hP.2.2.1, S.card_V₃] at e3
  rw [hP.2.2.2, S.card_V₃] at e4
  omega

theorem pairEq_cjSub_and_not_le
    (S : HullSetting G T L V z) {x : G} (h : PairHyp V x) :
    (∃ n : G, PairEq V (cjSub x V) (cjSub n S.V₃)) ∧
      ¬ centralizer (S.V₃ : Set G) ≤ normalizer (L : Set G) := by
  have hVab := isElemAbelian_of_isElementaryAbelian' V
  obtain ⟨n₁, hn₁, hP₁, hv₁⟩ := S.exists_pairEq h
  refine ⟨⟨n₁⁻¹, ?_⟩, fun hCM => ?_⟩
  · have := hP₁.cjSub n₁⁻¹
    rwa [cjSub_eq_self (inv_mem hn₁), ← cjSub_mul, inv_mul_cancel_left] at this
  obtain ⟨n₂, hn₂, hP₂, hv₂⟩ := S.exists_pairEq h.inv
  obtain ⟨h₀, hh₀⟩ : ∃ h₀ : G, h₀ = n₂ * (n₁ * x)⁻¹ := ⟨_, rfl⟩
  have hA : cjSub h₀ V = cjSub (n₂ * x⁻¹) V := by
    rw [hh₀, mul_inv_rev, ← mul_assoc, cjSub_mul _ n₁⁻¹, cjSub_eq_self (inv_mem hn₁)]
  have hB : cjSub h₀ (cjSub (n₁ * x) V) = V := by
    rw [← cjSub_mul, hh₀, inv_mul_cancel_right, cjSub_eq_self hn₂]
  have hP₃ := hP₁.cjSub h₀
  rw [hA, hB] at hP₃
  have hv₃ := v1Of_cjSub h₀ V (cjSub (n₁ * x) V)
  rw [hA, hB, hv₁, v1Of_comm, hv₂] at hv₃
  have h3 : h₀ ∈ normalizer (S.V₃ : Set G) :=
    B2F.mem_normalizer_iff_cjSub_eq.2 (hP₃.1.symm.trans hP₂.symm.1)
  have h1 : h₀ ∈ S.H := by
    rw [← S.normalizer_V₁]
    exact B2F.mem_normalizer_iff_cjSub_eq.2 hv₃.symm
  have hV₃ : S.V₃ ≠ ⊥ := fun hb => by
    have := S.card_V₃
    rw [hb, card_bot] at this
    omega
  have hN : h₀ ∉ normalizer (V : Set G) := fun hN => by
    have h4 := hP₂.2.1
    rw [← hA, cjSub_eq_self hN,
      commutator_eq_bot_iff_le_centralizer.2 (B2F.le_centralizer_self hVab)] at h4
    exact hV₃ h4.symm
  have hB' : centralizer (S.V₃ : Set G) ≤ normalizer (V : Set G) := by
    obtain ⟨-, -, hTI, -, -⟩ := u3_selected_local_normalizer_and_TI_of_1332 S.h1332 S.hH S.hF
    intro c hc
    rcases hTI c (hCM hc) with h' | h'
    · rw [conjugate_eq_cjSub'] at h'
      have := inv_mem (B2F.mem_normalizer_iff_cjSub_eq.2 h')
      rwa [inv_inv] at this
    · exfalso
      have hle : S.V₃ ≤ V ⊓ CFSG.conjugate V c := by
        intro v hv
        refine mem_inf.2 ⟨S.le3 hv, ?_⟩
        rw [conjugate_eq_cjSub', mem_cjSub, inv_inv,
          ← (mem_centralizer_iff.1 hc) v hv, mul_inv_cancel_right]
        exact S.le3 hv
      rw [h', le_bot_iff] at hle
      exact hV₃ hle
  exact hN (S.H_inf_normalizer_V₃_le hB' (mem_inf.2 ⟨h1, h3⟩))

end HullSetting

theorem u3Stmt13_3_12_4_of
    (h1332 : Stmt13_3_2) : U3Stmt13_3_12_4 := by
  intro G _ _ T L V z hH hU3 hF V₂ V₃ h12 h23 h3V hT2 hT3 hc2 hc3 g hne hle
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted h1332 hH hU3 hF
  let S : HullSetting G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  have hV2 : V₂ = pullSub S.Φ V2sub :=
    S.V2_eq ⟨by rw [fsuV1_eq hF]; exact h12, h23.trans h3V, hT2, hc2⟩
  have hV3 : V₃ = S.V₃ := by
    rw [S.V₃_eq_pullSub]
    exact S.V3_eq (by rw [← hV2]; exact h23) h3V hT3 hc3
  simp only [conjugate_eq_cjSub'] at hne hle ⊢
  obtain ⟨⟨n, h1, h2, h3, -⟩, hC⟩ := S.pairEq_cjSub_and_not_le ⟨hne, hle⟩
  refine ⟨h1.trans h2.symm, h2.trans h3.symm, ⟨n⁻¹, by rw [h2, hV3, inv_inv]⟩, ?_⟩
  rw [hV3]
  exact hC

end CFSG.Quasithin.H13.U3
