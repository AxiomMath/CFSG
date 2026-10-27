module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwo2
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoFlag2
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoWeights2
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoKb
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTorus
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNatZ2
public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefFixed2
public import CFSG.Goldschmidt75.Sig32Core
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaTwoSections

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_two_false
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : Z1 L1 L2 S ≤ Q2 L1 L2 S)
    (hc : IsChiefSeriesFrom (L2 ⊔ S) (str86U L1 L2 S) (str86U L1 L2 S) 2) : False := by
  classical
  have hm2 : 2 ≤ m := CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hm
  let H : Subgroup G := L2 ⊔ S
  let U : Subgroup G := str86U L1 L2 S
  have hq : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ k) :=
    str86_isSzU3Quot_of_statedSU hk hFc hU3
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S := str86_q2_le_s hF.toW hSB hm2 hm
  have hQ2H : H ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    str86_l2sup_le_normalizer_q2 (L1 := L1) (L2 := L2) (S := S)
  have hUe : IsElemAbelian 2 U :=
    isElemAbelian_str86U_of_caseII hF hSB hq hm2 hm hII hZ
  have hUH : U ≤ H := by
    have hZ1H : Z1 L1 L2 S ≤ H :=
      (omegaOneCenterOf_le (Q1 L1 L2 S)).trans (hQ1S.trans (le_sup_right : S ≤ H))
    refine conjClosure_le fun h hh z hz => ?_
    exact H.mul_mem (H.mul_mem hh (hZ1H hz)) (H.inv_mem hh)
  have hUHnormU : H ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure (Z1 L1 L2 S) (L2 ⊔ S)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨m, hm2, hm⟩))
  have hSylH : IsSylowTwoOf S H :=
    isSylowTwoOf_sup_Q2 hF.1 hS2
  obtain ⟨N, hNe, hNZ, hNne, hNP1, hNS, hNat⟩ :=
    str86_natural_in_Z1 hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc
  let p : Subgroup G := N ⊓ Subgroup.centralizer (S : Set G)
  let P : Subgroup G := ⁅N, S⁆
  have hflag := str86_caseIIa_two_flag hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc
    hNe hNZ hNne hNP1 hNS hNat
  obtain ⟨Kb, hKb, hKbB, hKbcyc, hKbcard, hKbdisj, hNβ, hKbodd⟩ :=
    str86_caseIIa_two_Kb hF hSB hm2 hm
  obtain ⟨K, hK, hKfin, hKcard, χ₂, χ₃, hrel, hpow, hχ2triv, hχ2fpf, hχ3triv, hχ3fpf,
    hrelP⟩ :=
    str86_caseIIa_two_weights hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hNe hNZ hNne hNP1 hNS hNat
      hflag rfl hKb hKbB hKbcyc hKbcard
  let U_N : Subgroup G := str86UN N L2 S
  let U₁ : Subgroup G := str86U1 P L2 S
  let U₂ : Subgroup G := str86U2 p p L2 S
  let Y₁ : Subgroup G := N ⊔ U₁
  let Y₂ : Subgroup G := U₂ ⊔ P
  have hSleP1 : S ≤ P1 L1 L2 S :=
    (le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
  have hPN : P ≤ N := CFSG.Quasithin.F112W.commutator_le_self_of_le_normalizer
    (hSleP1.trans hNP1)
  have hpN : p ≤ N := inf_le_left
  have hpP : p ≤ P := hflag.2.2.2
  have hpZ1 : p ≤ Z1 L1 L2 S := hpN.trans hNZ
  have hPZ1 : P ≤ Z1 L1 L2 S := hPN.trans hNZ
  have hpU₂ : p ≤ U₂ := le_conjClosure p H
  have hPleU₁ : P ≤ U₁ := le_conjClosure P H
  have hU₂U₁ : U₂ ≤ U₁ := str86U2_le_str86U1 hpP
  have hU₁UN : U₁ ≤ U_N := str86U1_le_str86UN hPN
  have hUNU : U_N ≤ U := str86UN_le_str86U hNZ
  have hU₂U : U₂ ≤ U := str86U2_le_str86U hpZ1
  have hU₁U : U₁ ≤ U := str86U1_le_str86U hPZ1
  have hU₂n : IsNormalIn H U U₂ := by
    simpa [H, U] using str86U2_isNormalIn (L1 := L1) (L2 := L2) (S := S) (p := p) hpZ1
  have hU₁n : IsNormalIn H U U₁ := by
    simpa [H, U] using str86U1_isNormalIn (L1 := L1) (L2 := L2) (S := S) (P := P) hPZ1
  have hUNn : IsNormalIn H U U_N := by
    simpa [H, U] using str86UN_isNormalIn (L1 := L1) (L2 := L2) (S := S) (N := N) hNZ
  have hUn : IsNormalIn H U U :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hUHnormU hg) x).mp hx⟩
  have hU2leZ2 : U₂ ≤ Z2 L1 L2 S :=
    str86U2_le_z2 hNe hNZ rfl hQ2S hQ2H hZ
  have hHleZ2 : H ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
    have hsup2 : H = L2 ⊔ Q2 L1 L2 S := by
      rw [show H = L2 ⊔ S from rfl, sup_eq_of_S_eq_right hS2]
    rwa [hsup2]
  have hcentral : H ≤ Subgroup.centralizer (U₂ : Set G) :=
    hHleZ2.trans (Subgroup.centralizer_le hU2leZ2)
  have hZ2C : Z2 L1 L2 S ≤ Subgroup.centralizer (S : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hSle : S ≤ L2 ⊔ Q2 L1 L2 S :=
      (le_of_eq hS2).trans (sup_le (inf_le_right.trans (le_sup_left : L2 ≤ L2 ⊔ Q2 L1 L2 S))
        (le_sup_right : Q2 L1 L2 S ≤ L2 ⊔ Q2 L1 L2 S))
    exact (Subgroup.mem_centralizer_iff.mp (hIIa (hSle hs)) z hz).symm
  have hU₂C : U₂ ≤ Subgroup.centralizer (S : Set G) := hU2leZ2.trans hZ2C
  have hHT : oTwoUpper H ⊔ S = H := by
    simpa [H] using str86H_eq_oTwoUpper_sup_s hF hSB hm2 hm
  have hUNp : IsPGroup 2 U_N := (hUe.isPGroup).to_le hUNU
  have hUNnoncentral : ¬ IsChiefSeriesFrom H U U_N 0 := by
    intro hzero
    exact str86UN_noncentral hF hNe hNne hNZ hNP1 hHT hUNp
      (isChiefSeriesFrom_of_le_module hUNU le_rfl hzero)
  obtain ⟨n₀, n₁, hser₀, hser₁, hge, hle⟩ :=
    str86_two_section_bookkeeping hUH hU₂U₁ hU₁UN hUNU hU₂n hU₁n hUNn hUn hcentral hc
      hUNnoncentral
  have hNnotU₁ : ¬ N ≤ U₁ := by
    have hnot : ¬ (N ⊔ U₁ ≤ U₁) := by
      intro hle'
      have hforall : ∀ y ∈ N ⊔ U₁,
          (1 : G) * y * (1 : G)⁻¹ * y⁻¹ ∈ U₁ → y ∈ U₁ := fun y hy _ => hle' hy
      have hχ : (χ₃ (1 : ↥Kb) : K) ≠ 1 := (hχ3fpf 1).mp hforall
      exact hχ (by simp)
    exact fun hle' => hnot (sup_le hle' le_rfl)
  obtain ⟨hinf, hrelU₂, hlt₁, hlt₂⟩ :=
    str86_two_section_indices (S := S) hk hUe hU₂U (hPleU₁.trans hU₁U) hU₂C rfl hPN hpP hpU₂
      hrelP hNnotU₁
  have hY₁gt : U₁ < Y₁ := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro heq
    have hYeq : Y₁ = U₁ := heq.symm
    have : U₁.relIndex (N ⊔ U₁) = 1 := by
      rw [show N ⊔ U₁ = Y₁ from rfl, hYeq, Subgroup.relIndex_self]
    omega
  have hY₂gt : U₂ < Y₂ := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hYeq : Y₂ = U₂ := heq.symm
    have hsup : P ⊔ U₂ = Y₂ := by rw [sup_comm]
    have : U₂.relIndex (P ⊔ U₂) = 1 := by
      rw [hsup, hYeq, Subgroup.relIndex_self]
    omega
  have hHnormU₁ : H ≤ Subgroup.normalizer (U₁ : Set G) :=
    CFSG.Quasithin.D14.le_normalizer_of_isNormalIn hU₁n
  have hNH : N ≤ H :=
    hNZ.trans ((omegaOneCenterOf_le (Q1 L1 L2 S)).trans
      (hQ1S.trans (le_sup_right : S ≤ H)))
  have hNnormU₁ : N ≤ Subgroup.normalizer (U₁ : Set G) := hNH.trans hHnormU₁
  have hU₁S : ⁅U₁, S⁆ ≤ U₁ :=
    CFSG.Quasithin.F112W.commutator_le_self_of_le_normalizer
      ((le_sup_right : S ≤ H).trans hHnormU₁)
  have hY₁S : ∀ s ∈ S, ∀ y ∈ Y₁, s * y * s⁻¹ * y⁻¹ ∈ U₁ := by
    have hcomm : ⁅Y₁, S⁆ ≤ U₁ := by
      change ⁅N ⊔ U₁, S⁆ ≤ U₁
      exact CFSG.Quasithin.D14.commutator_sup_le_of
        (W := N) (V := U₁) (Q := S) (M := U₁) hNnormU₁ hNnormU₁ hU₁S hPleU₁
    intro s hs y hy
    have hmem : ⁅y, s⁆ ∈ ⁅Y₁, S⁆ := Subgroup.commutator_mem_commutator hy hs
    have h1 : ⁅s, y⁆ = ⁅y, s⁆⁻¹ := by
      rw [← commutatorElement_inv (g₁ := s) (g₂ := y), inv_inv]
    change ⁅s, y⁆ ∈ U₁
    rw [h1]
    exact U₁.inv_mem (hcomm hmem)

  have hKbN : Kb ≤ Subgroup.normalizer (N : Set G) :=
    hKbB.trans ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans hNP1)
  have hKbS : Kb ≤ Subgroup.normalizer (S : Set G) := hKb.trans inf_le_right
  have hKbP : Kb ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.Goldschmidt75.le_normalizer_commutator hKbN hKbS
  have hHnormU₂ : H ≤ Subgroup.normalizer (U₂ : Set G) :=
    CFSG.Quasithin.D14.le_normalizer_of_isNormalIn hU₂n
  have hKbU₁ : Kb ≤ Subgroup.normalizer (U₁ : Set G) :=
    (hKb.trans inf_le_left).trans hHnormU₁
  have hKbY₁ : Kb ≤ Subgroup.normalizer (Y₁ : Set G) := by
    change Kb ≤ Subgroup.normalizer ((N ⊔ U₁ : Subgroup G) : Set G)
    exact fun d hd =>
      Subgroup.inf_normalizer_le_normalizer_sup N U₁ ⟨hKbN hd, hKbU₁ hd⟩
  have hKbU₂ : Kb ≤ Subgroup.normalizer (U₂ : Set G) :=
    (hKb.trans inf_le_left).trans hHnormU₂
  have hKbY₂ : Kb ≤ Subgroup.normalizer (Y₂ : Set G) := by
    change Kb ≤ Subgroup.normalizer ((U₂ ⊔ P : Subgroup G) : Set G)
    exact fun d hd =>
      Subgroup.inf_normalizer_le_normalizer_sup U₂ P ⟨hKbU₂ hd, hKbP hd⟩
  have hPSle : ⁅P, S⁆ ≤ U₂ := by
    rw [hflag.2.2.1]
    exact hpU₂
  have hU₂C_P : U₂ ≤ Subgroup.centralizer (P : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (congrArg Subtype.val (hUe.1.is_comm.comm ⟨y, hU₂U hy⟩
      ⟨x, hU₁U (hPleU₁ hx)⟩)).symm
  have hU₂normP : U₂ ≤ Subgroup.normalizer (P : Set G) :=
    hU₂C_P.trans (Subgroup.centralizer_le_normalizer (P : Set G))
  have hU₂S : ⁅U₂, S⁆ ≤ U₂ :=
    CFSG.Quasithin.F112W.commutator_le_self_of_le_normalizer
      ((le_sup_right : S ≤ H).trans hHnormU₂)
  have hY₂S : ∀ s ∈ S, ∀ y ∈ Y₂, s * y * s⁻¹ * y⁻¹ ∈ U₂ := by
    have hcomm : ⁅Y₂, S⁆ ≤ U₂ := by
      change ⁅U₂ ⊔ P, S⁆ ≤ U₂
      exact CFSG.Quasithin.D14.commutator_sup_le_of
        (W := U₂) (V := P) (Q := S) (M := U₂) hU₂normP Subgroup.le_normalizer hPSle hU₂S
    intro s hs y hy
    have hmem : ⁅y, s⁆ ∈ ⁅Y₂, S⁆ := Subgroup.commutator_mem_commutator hy hs
    have h1 : ⁅s, y⁆ = ⁅y, s⁆⁻¹ := by
      rw [← commutatorElement_inv (g₁ := s) (g₂ := y), inv_inv]
    change ⁅s, y⁆ ∈ U₂
    rw [h1]
    exact U₂.inv_mem (hcomm hmem)
  have hY₂leU₁ : Y₂ ≤ U₁ := sup_le hU₂U₁ hPleU₁
  have hY₁leUN : Y₁ ≤ U_N :=
    sup_le (le_conjClosure N H) hU₁UN
  have hX₁ : (∀ d : ↥Kb, (χ₃ d : K) = 1) →
      ∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), ∀ x ∈ N,
        n * x * n⁻¹ * x⁻¹ ∈ U₁ := by
    intro hchi3
    have hSX : ∀ s ∈ S, ∀ x ∈ N, s * x * s⁻¹ * x⁻¹ ∈ U₁ :=
      fun s hs x hx => hY₁S s hs x ((le_sup_left : N ≤ N ⊔ U₁) hx)
    have hKX : ∀ k ∈ Kb, ∀ x ∈ N, k * x * k⁻¹ * x⁻¹ ∈ U₁ := by
      intro k hk x hx
      have hval : (χ₃ ⟨k, hk⟩ : K) = 1 := hchi3 ⟨k, hk⟩
      exact (hχ3triv ⟨k, hk⟩).mpr hval x ((le_sup_left : N ≤ N ⊔ U₁) hx)
    exact str86_commutator_mem_of_mem_sup (Nβ := H ⊓ Subgroup.normalizer (S : Set G))
      (S := S) (K := Kb) (H := H) (X := N) (Lo := U₁) hNβ inf_le_right
      (le_sup_right : S ≤ H) (hKb.trans inf_le_left) hSX hKX
      (fun h hh y hy => hU₁n.2 h hh y hy)
  have hX₂ : (∀ d : ↥Kb, (χ₂ d : K) = 1) →
      ∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), ∀ x ∈ P,
        n * x * n⁻¹ * x⁻¹ ∈ U₂ := by
    intro hchi2
    have hSX : ∀ s ∈ S, ∀ x ∈ P, s * x * s⁻¹ * x⁻¹ ∈ U₂ := by
      intro s hs x hx
      have hSP : ⁅S, P⁆ ≤ U₂ := by rwa [Subgroup.commutator_comm]
      exact hSP (Subgroup.commutator_mem_commutator hs hx)
    have hKX : ∀ k ∈ Kb, ∀ x ∈ P, k * x * k⁻¹ * x⁻¹ ∈ U₂ := by
      intro k hk x hx
      have hval : (χ₂ ⟨k, hk⟩ : K) = 1 := hchi2 ⟨k, hk⟩
      exact (hχ2triv ⟨k, hk⟩).mpr hval x ((le_sup_right : P ≤ U₂ ⊔ P) hx)
    exact str86_commutator_mem_of_mem_sup (Nβ := H ⊓ Subgroup.normalizer (S : Set G))
      (S := S) (K := Kb) (H := H) (X := P) (Lo := U₂) hNβ inf_le_right
      (le_sup_right : S ≤ H) (hKb.trans inf_le_left) hSX hKX
      (fun h hh y hy => hU₂n.2 h hh y hy)
  have htor₁ : ∀ {d' : G}, d' ∈ Kb → d' ≠ 1 → ∀ Lo' Hi', U₁ ≤ Lo' → Hi' ≤ U_N →
      IsChiefStep H U Lo' Hi' → ¬ IsCentralStep H Lo' Hi' → ∀ x ∈ Hi',
        (∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Lo') →
          d' * x * d'⁻¹ * x⁻¹ ∈ Lo' → x ∈ Lo' := by
    intro d' hd' hne' Lo' Hi' _ _ hstep hnc x hx hxS hxd
    exact str86_natural_factor_torus hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
      (hKb hd') (hKbodd d' hd') hne' hx hxS hxd
  have htor₂ : ∀ {d' : G}, d' ∈ Kb → d' ≠ 1 → ∀ Lo' Hi', U₂ ≤ Lo' → Hi' ≤ U₁ →
      IsChiefStep H U Lo' Hi' → ¬ IsCentralStep H Lo' Hi' → ∀ x ∈ Hi',
        (∀ s ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Lo') →
          d' * x * d'⁻¹ * x⁻¹ ∈ Lo' → x ∈ Lo' := by
    intro d' hd' hne' Lo' Hi' _ _ hstep hnc x hx hxS hxd
    exact str86_natural_factor_torus hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
      (hKb hd') (hKbodd d' hd') hne' hx hxS hxd
  have hgen₁ : U_N = U₁ ⊔ conjClosure N H := (str86U1_sup_un hPN).symm
  have hgen₂ : U₁ = U₂ ⊔ conjClosure P H := (str86U2_sup_u1 hpP).symm
  obtain ⟨d₀, hd₀Kb, hd₀ne⟩ :=
    (Subgroup.bot_or_exists_ne_one Kb).resolve_left (by
      intro hbot
      have hcard1 : Nat.card ↥Kb = 1 := by rw [hbot]; exact Subgroup.card_bot
      rw [hKbcard] at hcard1
      have h4 : 4 ≤ 2 ^ m := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      omega)
  have hd₀Nβ : (d₀ : G) ∈ H ⊓ Subgroup.normalizer (S : Set G) := hKb hd₀Kb
  have hfix₁ : ∀ Lo' Hi', U₁ ≤ Lo' → Hi' ≤ U_N → IsChiefStep H U Lo' Hi' →
      ¬ IsCentralStep H Lo' Hi' → ∀ x ∈ Hi',
        (∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), n * x * n⁻¹ * x⁻¹ ∈ Lo') → x ∈ Lo' := by
    intro Lo' Hi' _ _ hstep hnc x hx hxN
    exact str86_natural_factor_torus hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
      hd₀Nβ (hKbodd d₀ hd₀Kb) hd₀ne hx
      (fun s hs => hxN s ⟨(le_sup_right : S ≤ H) hs, Subgroup.le_normalizer hs⟩)
      (hxN d₀ hd₀Nβ)
  have hfix₂ : ∀ Lo' Hi', U₂ ≤ Lo' → Hi' ≤ U₁ → IsChiefStep H U Lo' Hi' →
      ¬ IsCentralStep H Lo' Hi' → ∀ x ∈ Hi',
        (∀ n ∈ H ⊓ Subgroup.normalizer (S : Set G), n * x * n⁻¹ * x⁻¹ ∈ Lo') → x ∈ Lo' := by
    intro Lo' Hi' _ _ hstep hnc x hx hxN
    exact str86_natural_factor_torus hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc hstep hnc
      hd₀Nβ (hKbodd d₀ hd₀Kb) hd₀ne hx
      (fun s hs => hxN s ⟨(le_sup_right : S ≤ H) hs, Subgroup.le_normalizer hs⟩)
      (hxN d₀ hd₀Nβ)
  have hnat : ∀ Lo' Hi' : Subgroup G, IsChiefStep H U Lo' Hi' →
      ¬ IsCentralStep H Lo' Hi' → ∀ X : Subgroup G, Lo' ≤ X → X ≤ Hi' →
        (∀ s ∈ S, ∀ x ∈ X, s * x * s⁻¹ * x⁻¹ ∈ Lo') → Lo'.relIndex X ≤ 2 ^ m := by
    intro Lo' Hi' hstep hnc X hXLo hXHi hXS
    exact ((str86_caseIIa_two_equality hF hSB hk hFc hU3 hB2 hm hII hIIa hZ hc).2.2
      Lo' Hi' hstep hnc).2 X hXLo hXHi hXS
  by_cases hchi2_all : ∀ d : ↥Kb, (χ₂ d : K) = 1
  ·
    have hchi3_all : ∀ d : ↥Kb, (χ₃ d : K) = 1 := by
      intro d
      rw [hrel d, hchi2_all d]
      simp
    have hW₁ : F112W.IsChiefSeriesBetween H U U₁ U_N 0 :=
      isChiefSeriesBetween_zero_of_gen_fixed hSylH hUe hUH hUHnormU hU₁n hUNn hU₁UN
        hfix₁ (hX₁ hchi3_all) hgen₁
    have hW₂ : F112W.IsChiefSeriesBetween H U U₂ U₁ 0 :=
      isChiefSeriesBetween_zero_of_gen_fixed hSylH hUe hUH hUHnormU hU₂n hU₁n hU₂U₁
        hfix₂ (hX₂ hchi2_all) hgen₂
    have hz₀ : n₀ = 0 := F112W.isChiefSeriesBetween_unique hUH hU₁n hser₀ hW₁
    have hz₁ : n₁ = 0 := F112W.isChiefSeriesBetween_unique hUH hU₂n hser₁ hW₂
    omega
  ·
    have hchi2_notall : ∃ d : ↥Kb, (χ₂ d : K) ≠ 1 := by
      by_contra h
      apply hchi2_all
      intro d
      by_contra hd
      exact h ⟨d, hd⟩
    obtain ⟨d₂, hd₂⟩ := hchi2_notall
    have hY₂norm_d₂ : ∀ y ∈ Y₂, (d₂ : G) * y * (d₂ : G)⁻¹ ∈ Y₂ :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp (hKbY₂ d₂.2) y).mp hy
    have hfpf₂ : ∀ y ∈ Y₂, (d₂ : G) * y * (d₂ : G)⁻¹ * y⁻¹ ∈ U₂ → y ∈ U₂ :=
      (hχ2fpf d₂).mpr hd₂
    have hK₂a : U₂.relIndex Y₂ ≤ (2 ^ m) ^ n₁ :=
      relIndex_le_pow_of_fixedPointFree (H := H) (S := S) (U := U) (Lo := U₂)
        (Hi := U₁) (Y := Y₂) (r := 2 ^ m) (n := n₁) (d := (d₂ : G))
        hUe hUH hUHnormU (le_sup_right : S ≤ H) hser₁
        (fun Lo' Hi' _ _ hstep hnc => hnat Lo' Hi' hstep hnc) le_sup_left hY₂leU₁
        hY₂S ((hKb d₂.2).1) (hKbodd d₂ d₂.2) hY₂norm_d₂ hfpf₂
    have hq2le : (2 ^ k) ^ 2 ≤ (2 ^ m) ^ n₁ := by
      rw [← hrelU₂]
      exact hK₂a
    have hq2gt : 1 < (2 ^ k) ^ 2 := by
      have hk4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      nlinarith
    have hn₁pos : 1 ≤ n₁ := by
      by_contra h
      have h0 : n₁ = 0 := by omega
      rw [h0, pow_zero] at hq2le
      omega
    have hinj₂ : Function.Injective χ₂ := by
      rw [injective_iff_map_eq_one]
      intro d hd
      by_contra hne
      have hdval : (χ₂ d : K) = 1 := by
        have := congrArg (fun u : Kˣ => (u : K)) hd
        simpa using this
      have hd'ne : (d : G) ≠ 1 := by simpa using hne
      obtain ⟨y, hyY, hycomm⟩ :=
        exists_not_fixed_of_fixedPointFree (H := H) (S := S) (U := U) (Lo := U₂)
          (Hi := U₁) (Y := Y₂) (n := n₁) (d := (d₂ : G)) (d' := (d : G))
          hUe hUH hUHnormU (le_sup_right : S ≤ H) hser₁ (htor₂ d.2 hd'ne)
          le_sup_left hY₂leU₁ hY₂gt hY₂S ((hKb d₂.2).1) (hKbodd d₂ d₂.2)
          hY₂norm_d₂ hfpf₂
          (fun y hy => (Subgroup.mem_normalizer_iff.mp (hKbY₂ d.2) y).mp hy)
      exact hycomm ((hχ2triv d).mpr hdval y hyY)
    obtain ⟨g₂, hg₂⟩ := IsCyclic.exists_generator (α := ↥Kb)
    have hg₂ord : orderOf g₂ = 2 ^ m - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg₂, hKbcard]
    have hord₂ : orderOf (χ₂ g₂) = 2 ^ m - 1 := by
      rw [orderOf_injective χ₂ hinj₂ g₂, hg₂ord]
    by_cases hchi3_all : ∀ d : ↥Kb, (χ₃ d : K) = 1
    ·
      have hW₁ : F112W.IsChiefSeriesBetween H U U₁ U_N 0 :=
        isChiefSeriesBetween_zero_of_gen_fixed hSylH hUe hUH hUHnormU hU₁n hUNn hU₁UN
          hfix₁ (hX₁ hchi3_all) hgen₁
      have hz₀ : n₀ = 0 := F112W.isChiefSeriesBetween_unique hUH hU₁n hser₀ hW₁
      have hn₁le : n₁ ≤ 2 := by omega
      have hq2le_r2 : (2 ^ k) ^ 2 ≤ (2 ^ m) ^ 2 := by
        calc (2 ^ k) ^ 2 ≤ (2 ^ m) ^ n₁ := hq2le
          _ ≤ (2 ^ m) ^ 2 := pow_le_pow_right₀ (Nat.one_le_pow m 2 (by norm_num)) hn₁le
      have hqr : 2 ^ k ≤ 2 ^ m :=
        (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hq2le_r2
      have hpow₂ : (χ₂ g₂) ^ (2 ^ k + 1) = 1 := by
        apply Units.ext
        have hrelg := hrel g₂
        rw [hchi3_all g₂] at hrelg
        rw [Units.val_pow_eq_pow_val]
        exact hrelg.symm
      have hdvd₂ : 2 ^ m - 1 ∣ 2 ^ k + 1 := by
        rw [← hord₂]
        exact orderOf_dvd_iff_pow_eq_one.mpr hpow₂
      have hlt : 2 ^ m < 2 * 2 ^ k := by
        have hq4 : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        have hpos : 0 < 2 ^ m - 1 := by
          have hm4 : 4 ≤ 2 ^ m := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
          omega
        have hrle : 2 ^ m ≤ 2 ^ k + 2 := by
          have := Nat.le_of_dvd (by omega : 0 < 2 ^ k + 1) hdvd₂
          omega
        omega
      exact str86_two_dvd_add_one hk hdvd₂ hqr hlt
    ·
      have hchi3_notall : ∃ d : ↥Kb, (χ₃ d : K) ≠ 1 := by
        by_contra h
        apply hchi3_all
        intro d
        by_contra hd
        exact h ⟨d, hd⟩
      obtain ⟨d₃, hd₃⟩ := hchi3_notall
      have hY₁norm_d₃ : ∀ y ∈ Y₁, (d₃ : G) * y * (d₃ : G)⁻¹ ∈ Y₁ :=
        fun y hy => (Subgroup.mem_normalizer_iff.mp (hKbY₁ d₃.2) y).mp hy
      have hfpf₁ : ∀ y ∈ Y₁, (d₃ : G) * y * (d₃ : G)⁻¹ * y⁻¹ ∈ U₁ → y ∈ U₁ :=
        (hχ3fpf d₃).mpr hd₃
      have hK₁a : U₁.relIndex Y₁ ≤ (2 ^ m) ^ n₀ :=
        relIndex_le_pow_of_fixedPointFree (H := H) (S := S) (U := U) (Lo := U₁)
          (Hi := U_N) (Y := Y₁) (r := 2 ^ m) (n := n₀) (d := (d₃ : G))
          hUe hUH hUHnormU (le_sup_right : S ≤ H) hser₀
          (fun Lo' Hi' _ _ hstep hnc => hnat Lo' Hi' hstep hnc) le_sup_right hY₁leUN
          hY₁S ((hKb d₃.2).1) (hKbodd d₃ d₃.2) hY₁norm_d₃ hfpf₁
      have hn₀pos : 1 ≤ n₀ := by
        by_contra h
        have h0 : n₀ = 0 := by omega
        rw [h0, pow_zero] at hK₁a
        have hgt : 1 < U₁.relIndex Y₁ := hlt₁
        omega
      have hn₁eq : n₁ = 1 := by omega
      have hq2le_r : (2 ^ k) ^ 2 ≤ 2 ^ m := by
        have h := hq2le
        rw [hn₁eq] at h
        simpa using h
      have hinj₃ : Function.Injective χ₃ := by
        rw [injective_iff_map_eq_one]
        intro d hd
        by_contra hne
        have hdval : (χ₃ d : K) = 1 := by
          have := congrArg (fun u : Kˣ => (u : K)) hd
          simpa using this
        have hd'ne : (d : G) ≠ 1 := by simpa using hne
        obtain ⟨y, hyY, hycomm⟩ :=
          exists_not_fixed_of_fixedPointFree (H := H) (S := S) (U := U) (Lo := U₁)
            (Hi := U_N) (Y := Y₁) (n := n₀) (d := (d₃ : G)) (d' := (d : G))
            hUe hUH hUHnormU (le_sup_right : S ≤ H) hser₀ (htor₁ d.2 hd'ne)
            le_sup_right hY₁leUN hY₁gt hY₁S ((hKb d₃.2).1) (hKbodd d₃ d₃.2)
            hY₁norm_d₃ hfpf₁
            (fun y hy => (Subgroup.mem_normalizer_iff.mp (hKbY₁ d.2) y).mp hy)
        exact hycomm ((hχ3triv d).mpr hdval y hyY)
      obtain ⟨g₃, hg₃⟩ := IsCyclic.exists_generator (α := ↥Kb)
      have hg₃ord : orderOf g₃ = 2 ^ m - 1 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg₃, hKbcard]
      have hord₃ : orderOf (χ₃ g₃) = 2 ^ m - 1 := by
        rw [orderOf_injective χ₃ hinj₃ g₃, hg₃ord]
      have hpow₃ : (χ₃ g₃) ^ (2 ^ k - 1) = 1 := by
        have hq1 : 1 ≤ 2 ^ k := by
          have hk2 : 2 ≤ 2 ^ k := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ k)
          omega
        have hunit : (χ₃ g₃) ^ (2 ^ k) = χ₃ g₃ := by
          apply Units.ext
          simpa using hpow g₃
        rw [show 2 ^ k = (2 ^ k - 1) + 1 by omega, pow_succ] at hunit
        have h2 : (χ₃ g₃) ^ (2 ^ k - 1) * (χ₃ g₃) = 1 * (χ₃ g₃) := by
          rw [hunit, one_mul]
        exact mul_right_cancel h2
      have hdvd₃ : 2 ^ m - 1 ∣ 2 ^ k - 1 := by
        rw [← hord₃]
        exact orderOf_dvd_iff_pow_eq_one.mpr hpow₃
      exact str86_two_dvd_sub_one hk hdvd₃ hq2le_r

end CFSG.Quasithin.Stroth
