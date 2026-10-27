module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Goldschmidt
public import CFSG.Quasithin.Recognition.St84.Gen.NatL2
public import CFSG.Quasithin.Recognition.St84.Gen.PushZL2

import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Class
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.GroupTheory.GroupAction.PGroupFixedPoints
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5 CFSG.QuasithinUnique.Setup.Campbell
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section Lift

variable {H : Type*} [Group H]

private theorem isPGroup_zpowers_of_pow_two {x : H} {m : ℕ} (hm : x ^ 2 ^ m = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have hd : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  refine IsPGroup.of_card (n := k) ?_
  rw [Nat.card_zpowers, hk]

private theorem exists_lift_of_fixed_order_two {P N : Subgroup H}
    [hNnormal : (P.subgroupOf N).Normal] {t : H} (α : Subgroup.zpowers t →* MulAut ↥N)
    (hα : ∀ (a : Subgroup.zpowers t) (n : ↥N),
      ((α a n : ↥N) : H) = (a : H) * (n : H) * (a : H)⁻¹)
    (β : Subgroup.zpowers t →* MulAut (↥N ⧸ P.subgroupOf N))
    (hβ : ∀ (a : Subgroup.zpowers t) (n : ↥N),
      β a (QuotientGroup.mk n) = QuotientGroup.mk (α a n))
    {w : ↥N ⧸ P.subgroupOf N}
    (hwfix : ∀ a : Subgroup.zpowers t, β a w = w) (hworder : orderOf w = 2) :
    ∃ n : ↥N, (n : H) ∉ P ∧ (n : H) * (n : H) ∈ P ∧ ⁅t, (n : H)⁆ ∈ P ∧
      QuotientGroup.mk n = w := by
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_surjective w
  have hnP : (n : H) ∉ P := by
    intro hnP'
    have h1 : QuotientGroup.mk (s := P.subgroupOf N) n = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hnP'
    rw [hn_eq] at h1
    have h2 : orderOf w = 1 := by
      rw [h1]
      simp
    omega
  have hn2P : (n : H) * (n : H) ∈ P := by
    have h1 : (QuotientGroup.mk (s := P.subgroupOf N) n) ^ 2 = 1 := by
      rw [hn_eq]
      exact orderOf_dvd_iff_pow_eq_one.mp (hworder.symm ▸ dvd_refl 2)
    have h2 : QuotientGroup.mk (s := P.subgroupOf N) (n ^ 2) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact h1
    rw [QuotientGroup.eq_one_iff] at h2
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa [pow_two] using h3
  have hcommP : ⁅t, (n : H)⁆ ∈ P := by
    have hfixA' : QuotientGroup.mk (s := P.subgroupOf N)
        (α ⟨t, Subgroup.mem_zpowers t⟩ n) =
        QuotientGroup.mk (s := P.subgroupOf N) n := by
      rw [← hβ ⟨t, Subgroup.mem_zpowers t⟩ n, hn_eq]
      exact hwfix _
    have h1 : QuotientGroup.mk (s := P.subgroupOf N)
        (α ⟨t, Subgroup.mem_zpowers t⟩ n * n⁻¹) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hfixA']
      simp
    rw [QuotientGroup.eq_one_iff] at h1
    have h2 : (((α ⟨t, Subgroup.mem_zpowers t⟩ n * n⁻¹ : ↥N)) : H) ∈ P :=
      Subgroup.mem_subgroupOf.mp h1
    have hcomm : ⁅t, (n : H)⁆ =
        ((α ⟨t, Subgroup.mem_zpowers t⟩ n : ↥N) : H) * (n : H)⁻¹ := by
      rw [hα, commutatorElement_def]
    rwa [hcomm]
  exact ⟨n, hnP, hn2P, hcommP, hn_eq⟩

end Lift

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S) {X : Subgroup G}

open CFSG.Quasithin.F53Push CFSG.Quasithin.St84

private theorem Gw_zero_one_eq : t.Gw 0 1 = t.Gv 0 ⊓ t.Gv 1 := by
  simpa using t.Gw_add_one 0

private theorem Gw_neg_one_one_eq : t.Gw (-1) 1 = t.Gv (-1) ⊓ t.Gv 0 ⊓ t.Gv 1 := by
  simpa using t.Gw_sub_one_add_one 0

private theorem EX_le_pX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) :
    t.EX X 1 ≤ t.PX X := by
  have h2 : IsPGroup 2 (t.EX X 1) := (t.isPGroup_Qv 1).to_le inf_le_left
  have hGw : t.EX X 1 ≤ t.Gw (-1) 1 := by
    have hmem : t.EX X 1 ≤ normIn X (t.Gw 0 1) := by
      refine le_inf inf_le_right ?_
      rw [Gw_zero_one_eq t]
      exact le_inf (inf_le_left.trans (t.Qv_le_Gv hfr 1).1)
        (inf_le_left.trans (t.Qv_le_Gv_self 1))
    rw [hX.normIn_Gw_zero_one] at hmem
    exact hmem.trans inf_le_right
  have hQ0 : t.EX X 1 ≤ t.Qv 0 :=
    t.le_Qv_of_le_Gw hfr (u := -1) (w := 1) (j := 0) (by omega) (by omega) h2 hGw
  exact le_inf hQ0 (le_inf inf_le_right (inf_le_left.trans (t.Qv_le_Gv_self 1)))

private theorem bigB_le_Gv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : bigB L1 L2 S ≤ t.Gv 0 := by
  have h : bigB L1 L2 S = t.Gv 0 ⊓ t.Gv 1 := by
    rw [← t.Gw_zero_one hfr.hF, Gw_zero_one_eq t]
  rw [h]
  exact inf_le_left

private theorem bigB_le_Gv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : bigB L1 L2 S ≤ t.Gv 1 := by
  have h : bigB L1 L2 S = t.Gv 0 ⊓ t.Gv 1 := by
    rw [← t.Gw_zero_one hfr.hF, Gw_zero_one_eq t]
  rw [h]
  exact inf_le_right

private theorem odd_relIndex_bigB {a f : ℕ}
    (hfr : Frame L1 L2 S a f) :
    Odd ((bigB L1 L2 S).relIndex (t.Gv 0)) := by
  have hBnormL : bigB L1 L2 S ≤ normalizer (L1 : Set G) := by
    unfold bigB
    exact sup_le (sup_le ((F1.borelOf_le L1 S).trans Subgroup.le_normalizer)
      hfr.hF.1.h1.borel_le) hfr.hF.1.h1.normalizes
  have hrel : (bigB L1 L2 S).relIndex (t.Gv 0) =
      (L1 ⊓ bigB L1 L2 S).relIndex L1 := by
    rw [t.Gv_zero, show P1 L1 L2 S = L1 ⊔ bigB L1 L2 S from rfl]
    exact F112W.relIndex_sup_eq_relIndex_inf hBnormL
  rw [hrel]
  refine Odd.of_dvd_nat (n := (S ⊓ L1).relIndex L1) ?_ ?_
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact F7.isSylowTwoOf_odd_relIndex hfr.hF.1.h1.sylow
  · exact Subgroup.relIndex_dvd_of_le_left (H := S ⊓ L1) (K := L1 ⊓ bigB L1 L2 S)
      (L := L1) (le_inf inf_le_right (inf_le_left.trans (le_sup_right : S ≤ bigB L1 L2 S)))

private theorem EX_eq_of_pX_eq_Qv {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) (hPeq : t.PX X = t.Qv 0) :
    t.EX X 1 = t.Qv 1 ⊓ t.Qv 0 := by
  have hEXlePX := EX_le_pX t hfr hX
  have hPleNX : t.PX X ≤ normalizer (X : Set G) := inf_le_right.trans inf_le_left
  have hQ0leNX : t.Qv 0 ≤ normalizer (X : Set G) := hPeq ▸ hPleNX
  exact le_antisymm (le_inf inf_le_left (hPeq ▸ hEXlePX))
    (le_inf inf_le_left (inf_le_right.trans hQ0leNX))

private theorem odd_relIndex_normalizer_EX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcL X) (hPeq : t.PX X = t.Qv 0) :
    Odd ((normalizer (t.EX X 1 : Set G) ⊓ t.Gv 0).relIndex (t.Gv 0)) := by
  have hEXeq := EX_eq_of_pX_eq_Qv t hfr hX hPeq
  have hBnorm : bigB L1 L2 S ≤ normalizer (t.EX X 1 : Set G) := by
    rw [hEXeq]
    have hB1 : bigB L1 L2 S ≤ normalizer (t.Qv 1 : Set G) :=
      (bigB_le_Gv_one t hfr).trans (t.Gv_le_normalizer_Qv 1)
    have hB0 : bigB L1 L2 S ≤ normalizer (t.Qv 0 : Set G) :=
      (bigB_le_Gv_zero t hfr).trans (t.Gv_le_normalizer_Qv 0)
    exact (le_inf hB1 hB0).trans Subgroup.inf_normalizer_le_normalizer_inf
  exact Odd.of_dvd_nat (odd_relIndex_bigB t hfr)
    (Subgroup.relIndex_dvd_of_le_left (L := t.Gv 0)
      (le_inf hBnorm (bigB_le_Gv_zero t hfr)))

theorem ArcLMax.pX_ne_Qv_zero {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hP : IsSylowTwoOf (t.PX X) (t.LX X 1)) (hnc : NoCharNormal (t.PX X) (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hcov : L2 ≤ t.LX X 1 ⊔ t.Qv 1) :
    t.PX X ≠ t.Qv 0 := by
  intro hPeq
  have hEXeq := EX_eq_of_pX_eq_Qv t hfr hX.1 hPeq
  have hodd : Odd ((normalizer (pCoreOf 2 (t.LX X 1) : Set G) ⊓ t.Gv 0).relIndex
      (t.Gv 0)) := by
    rw [hE]
    exact odd_relIndex_normalizer_EX t hfr hX.1 hPeq
  have hPush : PushHyp (t.LX X 1) (t.PX X) (pushZ (t.LX X 1) (t.PX X)) :=
    pushHyp_pushZ_L2 (n := f) (by have hf2 : 2 ≤ f := hfr.hf; omega) hc hq hP hnc
  have hJ : ¬ thompsonJ (t.PX X) ≤ pCoreOf 2 (t.LX X 1) :=
    not_thompsonJ_le_pCoreOf_L2 hq hP hnc
  have hH0 : t.Gv 0 ≤ normalizer (t.PX X : Set G) := by
    rw [hPeq]
    exact t.Gv_le_normalizer_Qv 0
  have hcor := cor42_of_isL2Quot hPush (n := f) hfr.hf hq hJ hnc hH0 hodd
  set Z : Subgroup G := pushZ (t.LX X 1) (t.PX X) with hZdef
  set N : Subgroup G := conjJoinOf (t.Gv 0) Z with hNdef
  have hNleE : N ≤ t.EX X 1 := by
    rw [hE] at hcor
    exact hcor.2.1
  have hNn : t.LX X 1 ≤ normalizer (N : Set G) := by
    apply hcor.2.2
    rw [hNdef, hZdef]
    exact le_normalizer_conjJoinOf_pushZ hP.1 hH0
  have hNne : N ≠ ⊥ := by
    have hZne : Z ≠ ⊥ := pushZ_ne_bot_L2 hq hP
    have hZle : Z ≤ N := by
      rw [hNdef]
      exact F53Push.le_conjJoin (X := t.Gv 0) (J := Z)
    exact fun hbot => hZne (le_bot_iff.mp (hbot ▸ hZle))
  have hNGv0 : t.Gv 0 ≤ normalizer (N : Set G) := by
    rw [hNdef]
    exact F53Push.le_normalizer_conjJoin (t.Gv 0) Z
  have hNle : N ≤ t.Gv 0 ⊓ t.Gv 1 := by
    refine le_inf ?_ ?_
    · exact (hNleE.trans (hEXeq.le.trans inf_le_right)).trans (t.Qv_le_Gv_self 0)
    · exact (hNleE.trans (hEXeq.le.trans inf_le_left)).trans (t.Qv_le_Gv_self 1)
  have h0 : CosetTrans (normalizer (N : Set G)) (t.Gv 0) (t.Gv 1) :=
    (cosetTrans_self (t.Gv 0) (t.Gv 1)).mono hNGv0
  have h1 : CosetTrans (normalizer (N : Set G)) (t.Gv 1) (t.Gv 0) := by
    have hH : normalizer (N : Set G) ⊓ t.Gv 1 ≤ t.Gv 1 := inf_le_right
    have hL : L2 ≤ (normalizer (N : Set G) ⊓ t.Gv 1) ⊔ t.Qv 1 := by
      refine hcov.trans (sup_le ?_ le_sup_right)
      exact (le_inf hNn ((oTwoPrime_le (t.MX X 1)).trans inf_le_right)).trans le_sup_left
    exact (cosetTrans_one_of_le_sup t hfr hH hL).mono inf_le_left
  exact hNne (eq_bot_of_cosetTrans t hfr hNle h0 h1)

private theorem exists_lift_of_sq_mem {s : G} {P N : Subgroup G}
    (hP2 : IsPGroup 2 P) (hPN : P < N) (hNleQ : N ≤ t.Qv 0)
    (hNnorm : N ≤ normalizer (P : Set G))
    (hsP : s ∈ normalizer (P : Set G)) (hsN : s ∈ normalizer (N : Set G))
    (hs2 : s * s ∈ P) :
    ∃ n : ↥N, (n : G) ∉ P ∧ (n : G) * (n : G) ∈ P ∧ ⁅s, (n : G)⁆ ∈ P := by
  obtain ⟨k, hk⟩ := hP2 ⟨s * s, hs2⟩
  have hk' : (s ^ 2) ^ 2 ^ k = 1 := by simpa [pow_two] using congrArg Subtype.val hk
  have hspow : s ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul]
    exact hk'
  let A : Subgroup G := Subgroup.zpowers s
  have hA2 : IsPGroup 2 A := isPGroup_zpowers_of_pow_two hspow
  have hAN : A ≤ normalizer (N : Set G) := Subgroup.zpowers_le.mpr hsN
  let α : A →* MulAut ↥N :=
    (Subgroup.normalizerMonoidHom (H := N)).comp (Subgroup.inclusion hAN)
  have hPNnormal : (P.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNnorm
  have hPNinv : ∀ a : A, ∀ n ∈ P.subgroupOf N, α a n ∈ P.subgroupOf N := by
    intro a n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have ha : (a : G) ∈ normalizer (P : Set G) :=
      (Subgroup.zpowers_le.mpr hsP) a.2
    have hconj : (a : G) * (n : G) * (a : G)⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp ha (n : G)).mp hn
    have hval : ((α a n : ↥N) : G) = (a : G) * (n : G) * (a : G)⁻¹ := by
      simp [α]
    rwa [hval]
  let Q := ↥N ⧸ P.subgroupOf N
  let β : A →* MulAut Q :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α (P.subgroupOf N) hPNinv
  let : MulDistribMulAction A Q := MulDistribMulAction.compHom Q β
  have hN2 : IsPGroup 2 N := (t.isPGroup_Qv 0).to_le hNleQ
  have hQ2 : IsPGroup 2 Q :=
    hN2.of_surjective (QuotientGroup.mk' (P.subgroupOf N)) (QuotientGroup.mk'_surjective _)
  haveI : Finite Q := Finite.of_surjective (QuotientGroup.mk' (P.subgroupOf N))
    (QuotientGroup.mk'_surjective _)
  have hQne : Nontrivial Q := by
    obtain ⟨x, hxN, hxP⟩ := SetLike.exists_of_lt hPN
    refine ⟨⟨QuotientGroup.mk (s := P.subgroupOf N) ⟨x, hxN⟩, 1, ?_⟩⟩
    intro h
    apply hxP
    have hx1 : QuotientGroup.mk (s := P.subgroupOf N) ⟨x, hxN⟩ = 1 := h
    rw [QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_subgroupOf.mp hx1
  haveI : Nontrivial Q := hQne
  obtain ⟨w, hworder, hwfix⟩ :=
    CFSG.GroupTheory.exists_orderOf_eq_forall_smul_eq (A := A) (p := 2) hA2 hQ2
  have hwfixβ : ∀ a : Subgroup.zpowers s, β a w = w := fun a => hwfix a
  obtain ⟨n, hnP, hn2P, hcommP, -⟩ :=
    exists_lift_of_fixed_order_two (t := s) α (by intro a n; simp [α]) β
      (fun a n => CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk α
        (P.subgroupOf N) hPNinv a n) hwfixβ hworder
  exact ⟨n, hnP, hn2P, hcommP⟩

theorem exists_t' (hP0 : t.PX X ≠ t.Qv 0) {s : G} (hs0 : s ∈ t.Gv 0)
    (hsP : s ∈ normalizer (t.PX X : Set G)) (hs2 : s * s ∈ t.PX X) :
    ∃ t' ∈ t.Qv 0, t' ∉ t.PX X ∧ t' ∈ normalizer (t.PX X : Set G) ∧ t' * t' ∈ t.PX X ∧
      ⁅s, t'⁆ ∈ t.PX X := by
  let P : Subgroup G := t.PX X
  let N : Subgroup G := normalizer (P : Set G) ⊓ t.Qv 0
  have hP2 : IsPGroup 2 P := (t.isPGroup_Qv 0).to_le inf_le_left
  have hPleQ : P ≤ t.Qv 0 := inf_le_left
  have hPleN : P ≤ N := le_inf Subgroup.le_normalizer hPleQ
  have hPN : P < N := by
    have hlt : P < t.Qv 0 := lt_of_le_of_ne hPleQ hP0
    have h := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 2) (P := t.Qv 0) (S := P)
      (t.isPGroup_Qv 0) hlt
    simpa [N, inf_comm] using h
  have hsQ : s ∈ normalizer (t.Qv 0 : Set G) := t.Gv_le_normalizer_Qv 0 hs0
  have hsN : s ∈ normalizer (N : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := normalizer (P : Set G)) (K := t.Qv 0)
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer (H := normalizer (P : Set G)) hsP, hsQ⟩)
  obtain ⟨n, hnP, hn2P, hcommP⟩ :=
    exists_lift_of_sq_mem t hP2 hPN (inf_le_right : N ≤ t.Qv 0) inf_le_left hsP hsN hs2
  exact ⟨(n : G), (inf_le_right : N ≤ t.Qv 0) n.2, hnP,
    (inf_le_left : N ≤ normalizer (P : Set G)) n.2, hn2P, hcommP⟩

private theorem PX_le_Gw {a f : ℕ}
    (hfr : Frame L1 L2 S a f) : t.PX X ≤ t.Gw (-1) 1 := by
  rw [Gw_neg_one_one_eq t]
  refine le_inf (le_inf ?_ ?_) ?_
  · exact inf_le_left.trans (t.Qv_le_Gv hfr 0).1
  · exact inf_le_left.trans (t.Qv_le_Gv_self 0)
  · exact inf_le_right.trans inf_le_right

theorem ArcLMax.not_mem_normalizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hX : t.ArcLMax X) {R : Subgroup G} (hR : R ≠ ⊥)
    (hRE : R ≤ t.EX X 1) (hM : t.MX X 1 ≤ normalizer (R : Set G))
    (hK : t.K ≤ normalizer (R : Set G)) {s : G} (hs0 : s ∈ t.MX X 0)
    (hs : t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) (hsR : s ∈ normalizer (R : Set G))
    (hpair : (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0)
    {t' : G} (ht' : t' ∈ t.Qv 0) (ht'X : t' ∉ normalizer (X : Set G)) :
    t' ∉ normalizer (R : Set G) := by
  have hRarc : t.ArcL R := ArcL.arcL_of_le (t := t) hfr hX.1 hR
    (hRE.trans ((EX_le_pX t hfr hX.1).trans (PX_le_Gw t hfr))) hM hK hs0 hs hsR hpair
  have hR2 : IsPGroup 2 R := (t.isPGroup_Qv 1).to_le (hRE.trans inf_le_left)
  have hle : t.MX X 1 ≤ t.MX R 1 := le_inf hM inf_le_right
  have hMXeq : t.MX R 1 = t.MX X 1 := le_antisymm (hX.2.2 R hRarc hR2 hle) hle
  intro ht'R
  have ht'MX : t' ∈ t.MX R 1 :=
    Subgroup.mem_inf.mpr ⟨ht'R, (t.Qv_le_Gv hfr 0).2 ht'⟩
  rw [hMXeq] at ht'MX
  exact ht'X ht'MX.1

end Track

end CFSG.Quasithin.Stroth.Rq

end
