module

public import CFSG.Quasithin.H13.A6S1372L76G
public import CFSG.Quasithin.H13.A6S1372L24b
public import CFSG.Quasithin.H13.A6S1372L76E

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L76H

theorem e9_of_perm {n : ℕ} {a b : (FFModel.altDn n).Gam}
    (h : A6L76B.E9Pair (A6L76C.permOf a) (A6L76C.permOf b)) : A6L76B.E9Pair a b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨A6L76C.permOf_injective h1, A6L76C.permOf_injective (by
      rw [show A6L76C.permOf (a ^ 3) = A6L76C.permOf a ^ 3 from rfl, h2]; rfl),
    A6L76C.permOf_injective (by
      rw [show A6L76C.permOf (b ^ 3) = A6L76C.permOf b ^ 3 from rfl, h3]; rfl),
    fun e => h4 (by rw [e]; rfl), fun e => h5 (by rw [e]; rfl), fun e => h6 (by rw [e]),
    fun e => h7 (by rw [e]; rfl)⟩

theorem fixCls_conj {n : ℕ} {σ : Perm (Fin n)} {m : G6.PermMod n} (h : A6L76C.FixCls n σ m)
    (τ : Perm (Fin n)) : A6L76C.FixCls n (τ * σ * τ⁻¹) (G6.permAct n τ m) := by
  have e1 : G6.permAct n (τ * σ * τ⁻¹) (G6.permAct n τ m) = G6.permAct n τ (G6.permAct n σ m) := by
    rw [CFSG.Quasithin.permAct_mul_act, CFSG.Quasithin.permAct_mul_act,
      ← CFSG.Quasithin.permAct_mul_act n τ⁻¹ τ, inv_mul_cancel, map_one, MulAut.one_apply]
  rcases h with h | h
  · have h1 : G6.permAct n σ m = m := mul_inv_eq_one.1 h
    left
    rw [e1, h1]
    exact mul_inv_cancel _
  · have h1 : G6.permAct n σ m = G6.allOnes n * m := mul_inv_eq_iff_eq_mul.1 h
    right
    rw [e1, h1, map_mul, CFSG.Quasithin.permAct_allOnes]
    exact mul_inv_cancel_right _ _

instance (n : ℕ) : Finite (FFModel.altDn n).Gam :=
  inferInstanceAs (Finite ↥(alternatingGroup (Fin n)))

theorem sum_one_five : (∑ _i : Fin 5, (1 : ZMod 2)) ≠ 0 := by decide

theorem sum_one_seven : (∑ _i : Fin 7, (1 : ZMod 2)) ≠ 0 := by decide

theorem pRank_alt5_le_one : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin 5))) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 _ g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hdvd : 3 ^ k ∣ 60 := by
    rw [← hk, ← h60]
    exact Subgroup.card_subgroup_dvd_card E
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have h9 : 3 ^ 2 ∣ 60 := (pow_dvd_pow 3 h).trans hdvd
    norm_num at h9
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk1

end A6L76H

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem v2_mul_self : S.v2 * S.v2 = 1 := by
  have h : (⟨S.v2, S.v2_mem_V⟩ : ↥V) * ⟨S.v2, S.v2_mem_V⟩ = 1 := by
    apply S.frame.ψ.injective
    rw [map_mul, S.psi_v2, map_one]
    exact Subtype.ext (G6.permMod_mul_self _)
  exact congrArg Subtype.val h

theorem comm_v2_not_mem_V1 {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    (g : G) * S.v2 * (g : G)⁻¹ * S.v2⁻¹ ∉ fsuV1 T V := by
  obtain ⟨-, -, -, h3, -, -, -, h01, h12, -, -, -⟩ := A6L76G.w4_facts
  have hv : S.v2⁻¹ = S.v2 := inv_eq_of_mul_eq_one_right S.v2_mul_self
  rw [hv]
  have hm : (g : G) * S.v2 * (g : G)⁻¹ * S.v2 ∈ V := V.mul_mem (S.conj_v2_mem_V g) S.v2_mem_V
  rw [S.mem_V1_iff_inV1 hm]
  have e : (⟨(g : G) * S.v2 * (g : G)⁻¹ * S.v2, hm⟩ : ↥V) =
      ⟨_, S.conj_v2_mem_V g⟩ * ⟨S.v2, S.v2_mem_V⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul, S.psi_conj_v2, S.psi_v2, hg, h01, h12]
  have key : A6L76G.InV1 (dv 1 2 * dv 0 1) → False := by decide
  exact key

variable {S}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)] {D : FFModel}
  (C : S.Ctx76 H K D)
include C

theorem βU_V1 {w : G} (hw : w ∈ fsuV1 T V) (hwU : w ∈ conjClosure S.V3 H) :
    C.βU ⟨w, hwU⟩ = 1 := by
  rw [C.βU_eq_one_iff]
  intro k hk
  rw [S.conj_V1_of_mem C.hH (C.hKH hk) hw, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem βU_v2_ne_one : C.βU ⟨S.v2, S.v2_mem_UH H⟩ ≠ 1 := by
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  intro h
  exact S.comm_v2_not_mem_V1 hg ((C.βU_eq_one_iff _).1 h g (C.hL1K hgL))

end Ctx76

theorem conj_v2_mem_V3 {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2) : (g : G) * S.v2 * (g : G)⁻¹ ∈ S.V3 := by
  obtain ⟨-, -, -, -, -, h12, -, h01, h12', -, -, -⟩ := A6L76G.w4_facts
  refine S.mem_pre.2 ⟨S.conj_v2_mem_V g, ?_⟩
  show InW3 ((S.frame.ψ ⟨_, S.conj_v2_mem_V g⟩ : ↥W4) : P6)
  rw [S.psi_conj_v2, hg, h01, h12']
  exact h12

theorem v2_mem_V3 : S.v2 ∈ S.V3 := S.V2_le_V3 S.v2_mem_V2

end Setting4

namespace A6L76H

theorem ker_altDn_odd {n : ℕ} (hn : (∑ _i : Fin n, (1 : ZMod 2)) ≠ 0) :
    (FFModel.altDn n).ker.subgroupOf (FFModel.altDn n).sec = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Subgroup.mem_subgroupOf] at hm
  have hm' : (show G6.PermMod n from m.1) ∈ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n := hm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rcases (A6L76C.mem_zpowers_allOnes_iff _).1 hm'.1 with h | h
  · exact h
  · exfalso
    have h2 := G6.mem_coreMod.1 hm'.2
    rw [h] at h2
    exact hn h2

theorem eq_of_mk_eq {n : ℕ} (hn : (∑ _i : Fin n, (1 : ZMod 2)) ≠ 0) {x y : ↥(FFModel.altDn n).sec}
    (h : (QuotientGroup.mk x : (FFModel.altDn n).Mod) = QuotientGroup.mk y) : x = y := by
  rw [QuotientGroup.eq, ker_altDn_odd hn, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h

end A6L76H

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]

theorem false_eight (h13314 : Stmt13_3_14)
    (C : S.Ctx76 H K (FFModel.altDn 8)) : False := by
  obtain ⟨⟨m, hm⟩, hxm⟩ := QuotientGroup.mk_surjective (C.βU ⟨S.v2, S.v2_mem_UH H⟩)
  obtain ⟨hE, ha, hb⟩ := A6L76E.check8 m (G6.mem_coreMod.1 hm)
  obtain ⟨hs1, hs2⟩ := A6L76E.sign_wit 8 m
  exact C.not_e9 h13314 hm hxm.symm (a := ⟨_, Perm.mem_alternatingGroup.2 hs1⟩)
    (b := ⟨_, Perm.mem_alternatingGroup.2 hs2⟩) (A6L76H.e9_of_perm hE)
    ((A6L76C.act_mul_inv_mem_ker_iff hm _).2 ha) ((A6L76C.act_mul_inv_mem_ker_iff hm _).2 hb)

theorem false_ge_nine {n : ℕ} (hn : 9 ≤ n)
    (C : S.Ctx76 H K (FFModel.altDn n)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (FFModel.altDn n).Gam) :=
    A6L76E.three_le_pRank_alt hn
  have h2 : (⊤ : Subgroup ↥K).map C.α = ⊤ := Subgroup.map_top_of_surjective _ C.α_surj
  have h3 := A6L76B.pRank_map_le C.α C.not_three_dvd_ker ⊤
  rw [h2] at h3
  have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = CFSG.Open.pRank 3 K :=
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup K).symm
  have h5 : CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 H :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) C.hKH
  have h6 := pRank_le_two_of_pCoreOf_ne_bot S.h13.qtke C.hH.1.2 Nat.prime_three (by norm_num)
  omega

theorem exists_rep {n : ℕ} (C : S.Ctx76 H K (FFModel.altDn n)) :
    ∃ (m : G6.PermMod n) (hm : m ∈ (FFModel.altDn n).sec),
      C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩ := by
  obtain ⟨⟨m, hm⟩, hxm⟩ := QuotientGroup.mk_surjective (C.βU ⟨S.v2, S.v2_mem_UH H⟩)
  exact ⟨m, hm, hxm.symm⟩

theorem classes_odd {n : ℕ} (hodd : (∑ _i : Fin n, (1 : ZMod 2)) ≠ 0)
    (C : S.Ctx76 H K (FFModel.altDn n)) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2)
    {m : G6.PermMod n} (hm : m ∈ (FFModel.altDn n).sec)
    (hxm : C.βU ⟨S.v2, S.v2_mem_UH H⟩ = QuotientGroup.mk ⟨m, hm⟩) :
    m ≠ 1 ∧ m * G6.permAct n (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m =
      G6.permAct n (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩) ^ 2) m := by
  have hgK : (g : G) ∈ K := C.hL1K hgL
  have hgU : (g : G) * S.v2 * (g : G)⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hKH hgK)) _).mp
      (S.v2_mem_UH H)
  have hg2K : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ K := by
    rw [Subgroup.coe_pow]
    exact K.pow_mem hgK 2
  have hg2U : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
      ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hKH hg2K)) _).mp
      (S.v2_mem_UH H)
  have hy := C.βU_equiv ⟨g, hgK⟩ ⟨S.v2, S.v2_mem_UH H⟩ hgU hm hxm
  have hz := C.βU_equiv ⟨_, hg2K⟩ ⟨S.v2, S.v2_mem_UH H⟩ hg2U hm hxm
  have hα2 : C.α ⟨_, hg2K⟩ = C.α ⟨g, hgK⟩ ^ 2 := by
    rw [← map_pow]
    congr 1
  have hprod : (⟨_, hg2U⟩ : ↥(conjClosure S.V3 H)) = ⟨S.v2, S.v2_mem_UH H⟩ * ⟨_, hgU⟩ :=
    Subtype.ext (S.v2_mul_conj hg).symm
  rw [hprod, map_mul, hxm, hy, ← QuotientGroup.mk_mul] at hz
  have hz' := congrArg Subtype.val (A6L76H.eq_of_mk_eq hodd hz)
  simp only [Subgroup.coe_mul] at hz'
  rw [hα2] at hz'
  refine ⟨fun h => C.βU_v2_ne_one ?_, hz'⟩
  rw [hxm]
  have e : (⟨m, hm⟩ : ↥(FFModel.altDn n).sec) = 1 := Subtype.ext h
  rw [e, QuotientGroup.mk_one]

theorem fix_O2L1 {n : ℕ}
    (hodd : (∑ _i : Fin n, (1 : ZMod 2)) ≠ 0) (C : S.Ctx76 H K (FFModel.altDn n)) {x : G}
    (hx : x ∈ pCoreOf 2 S.L1) {u : G} (hu3 : u ∈ S.V3) (huU : u ∈ conjClosure S.V3 H)
    {w : G6.PermMod n} (hw : w ∈ (FFModel.altDn n).sec)
    (hu : C.βU ⟨u, huU⟩ = QuotientGroup.mk ⟨w, hw⟩) :
    G6.permAct n (A6L76C.permOf (C.α ⟨x, C.hL1K (pCoreOf_le 2 S.L1 hx)⟩)) w = w := by
  have hxK : x ∈ K := C.hL1K (pCoreOf_le 2 S.L1 hx)
  have hxu : x * u * x⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hKH hxK)) u).mp huU
  have h1 := C.βU_equiv ⟨x, hxK⟩ ⟨u, huU⟩ hxu hw hu
  have hcU : x * u * x⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
    (conjClosure S.V3 H).mul_mem hxu ((conjClosure S.V3 H).inv_mem huU)
  have e : (⟨x * u * x⁻¹, hxu⟩ : ↥(conjClosure S.V3 H)) = ⟨_, hcU⟩ * ⟨u, huU⟩ :=
    Subtype.ext (inv_mul_cancel_right (x * u * x⁻¹) u).symm
  have h0 : C.βU ⟨x * u * x⁻¹, hxu⟩ = QuotientGroup.mk ⟨w, hw⟩ := by
    rw [e, map_mul, C.βU_V1 (S.comm_O2L1_V3 hx hu3) hcU, one_mul, hu]
  have h2 := congrArg Subtype.val (A6L76H.eq_of_mk_eq hodd (h0.symm.trans h1))
  exact (A6L76C.act_eq _ _).symm.trans h2.symm

theorem permOf_α_pow {n : ℕ} (C : S.Ctx76 H K (FFModel.altDn n)) {x : G} (hx : x ∈ K) {k : ℕ}
    (hk : x ^ k = 1) : A6L76C.permOf (C.α ⟨x, hx⟩) ^ k = 1 := by
  have h1 : (⟨x, hx⟩ : ↥K) ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [show A6L76C.permOf (C.α ⟨x, hx⟩) ^ k = A6L76C.permOf (C.α ⟨x, hx⟩ ^ k) from rfl,
    ← map_pow, h1, map_one]
  rfl

theorem permOf_α_ne_one {n : ℕ}
    (C : S.Ctx76 H K (FFModel.altDn n)) {x : G} (hx : x ∈ K) (hxQ : x ∉ pCoreOf 2 H) :
    A6L76C.permOf (C.α ⟨x, hx⟩) ≠ 1 := by
  intro h
  apply hxQ
  show ((⟨x, hx⟩ : ↥K) : G) ∈ pCoreOf 2 H
  rw [← C.α_eq_one_iff]
  exact A6L76C.permOf_injective h

theorem not_hat_of_five (C : S.Ctx76 H K (FFModel.altDn 5)) :
    ¬ IsHatA6 L := by
  intro hhat
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := S.two_le_pRank_L1_of_hat hhat
  have h2 : CFSG.Open.pRank 3 S.L1 ≤ CFSG.Open.pRank 3 K :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) C.hL1K
  have h3 : CFSG.Open.pRank 3 K = CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K
  have h4 := A6L76F.pRank_le_map_of_not_dvd C.α C.not_three_dvd_ker ⊤
  have h5 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥K).map C.α) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (FFModel.altDn 5).Gam) :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top
  have h6 : CFSG.Open.pRank 3 (⊤ : Subgroup (FFModel.altDn 5).Gam) ≤ 1 :=
    A6L76H.pRank_alt5_le_one
  omega

theorem isKl_of_conj (C : S.Ctx76 H K (FFModel.altDn 5))
    {c : G} (hcL : c ∈ S.L1) (hc3 : c ^ 3 = 1) (hcQ : c ∉ pCoreOf 2 H) {o₁ : G}
    (ho₁ : o₁ ∈ pCoreOf 2 S.L1) (ho₁Q : o₁ ∉ pCoreOf 2 H)
    (ho₂ : c * o₁ * c⁻¹ ∈ pCoreOf 2 S.L1) :
    A6L19.IsKl (A6L76C.permOf (C.α ⟨o₁, C.hL1K (pCoreOf_le 2 S.L1 ho₁)⟩))
      (A6L76C.permOf (C.α ⟨c * o₁ * c⁻¹, C.hL1K (pCoreOf_le 2 S.L1 ho₂)⟩)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK : ∀ x ∈ pCoreOf 2 S.L1, x ∈ K := fun x hx => C.hL1K (pCoreOf_le 2 S.L1 hx)
  have hpow : ∀ x (hx : x ∈ pCoreOf 2 S.L1), ∃ k : ℕ,
      A6L76C.permOf (C.α ⟨x, hOK x hx⟩) ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨x, hx⟩
    exact ⟨k, C.permOf_α_pow (hOK x hx) (by simpa using congrArg Subtype.val hk)⟩
  have hsq : ∀ x (hx : x ∈ pCoreOf 2 S.L1),
      A6L76C.permOf (C.α ⟨x, hOK x hx⟩) * A6L76C.permOf (C.α ⟨x, hOK x hx⟩) = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hpow x hx
    exact A6L19.sq_check _ (A6L19.pow_eight_of_pow hk) (A6L76C.permOf_sign _)
  have ha1 := C.permOf_α_ne_one (hOK _ ho₁) ho₁Q
  have hb1 : A6L76C.permOf (C.α ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) ≠ 1 := by
    refine C.permOf_α_ne_one _ fun h => ho₁Q ?_
    have e : o₁ = c⁻¹ * (c * o₁ * c⁻¹) * c⁻¹⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 H (H.inv_mem (C.hL1H hcL))) _).mp h
  have hba : A6L76C.permOf (C.α ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) =
      A6L76C.permOf (C.α ⟨c, C.hL1K hcL⟩) * A6L76C.permOf (C.α ⟨o₁, hOK _ ho₁⟩) *
        (A6L76C.permOf (C.α ⟨c, C.hL1K hcL⟩))⁻¹ := by
    have e : (⟨c * o₁ * c⁻¹, hOK _ ho₂⟩ : ↥K) =
        ⟨c, C.hL1K hcL⟩ * ⟨o₁, hOK _ ho₁⟩ * (⟨c, C.hL1K hcL⟩ : ↥K)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hab : A6L76C.permOf (C.α ⟨o₁, hOK _ ho₁⟩) ≠
      A6L76C.permOf (C.α ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) := by
    intro h
    rw [hba] at h
    have hcomm : A6L76C.permOf (C.α ⟨o₁, hOK _ ho₁⟩) * A6L76C.permOf (C.α ⟨c, C.hL1K hcL⟩) =
        A6L76C.permOf (C.α ⟨c, C.hL1K hcL⟩) * A6L76C.permOf (C.α ⟨o₁, hOK _ ho₁⟩) := by
      conv_lhs => rw [h]
      group
    obtain ⟨k, hk⟩ := hpow _ ho₁
    exact ha1 (A6L24.eq_one_of_commute5 (C.permOf_α_pow _ hc3) (C.permOf_α_ne_one _ hcQ)
      (C.α ⟨o₁, hOK _ ho₁⟩).2 hcomm hk)
  have hmem : o₁ * (c * o₁ * c⁻¹) ∈ pCoreOf 2 S.L1 := (pCoreOf 2 S.L1).mul_mem ho₁ ho₂
  have hab8 : (A6L76C.permOf (C.α ⟨o₁, hOK _ ho₁⟩) *
      A6L76C.permOf (C.α ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩)) ^ 8 = 1 := by
    obtain ⟨k, hk⟩ := hpow _ hmem
    have e : A6L76C.permOf (C.α ⟨o₁ * (c * o₁ * c⁻¹), hOK _ hmem⟩) =
        A6L76C.permOf (C.α ⟨o₁, hOK _ ho₁⟩) * A6L76C.permOf (C.α ⟨c * o₁ * c⁻¹, hOK _ ho₂⟩) := by
      rw [← A6L76C.permOf_mul, ← map_mul]
      rfl
    rw [e] at hk
    exact A6L19.pow_eight_of_pow hk
  exact ⟨hsq _ ho₁, hsq _ ho₂, A6L76E.comm5 _ _ (A6L76C.permOf_sign _) (A6L76C.permOf_sign _)
    (hsq _ ho₁) (hsq _ ho₂) hab8, ha1, hb1, hab, A6L76C.permOf_sign _, A6L76C.permOf_sign _⟩

theorem exists_kl5 (C : S.Ctx76 H K (FFModel.altDn 5))
    (hhat : ¬ IsHatA6 L) : ∃ (x₁ : G) (h₁ : x₁ ∈ pCoreOf 2 S.L1) (x₂ : G)
      (h₂ : x₂ ∈ pCoreOf 2 S.L1),
      A6L19.IsKl (A6L76C.permOf (C.α ⟨x₁, C.hL1K (pCoreOf_le 2 S.L1 h₁)⟩))
        (A6L76C.permOf (C.α ⟨x₂, C.hL1K (pCoreOf_le 2 S.L1 h₂)⟩)) := by
  have hcL : (S.cL1 hhat : G) ∈ S.L1 := S.cL1_mem hhat
  have hcQ : (S.cL1 hhat : G) ∉ pCoreOf 2 H :=
    S.not_mem_QH_of_L1 C.hNS C.h13315 C.h1356two C.hH hcL (S.cL1_not_mem hhat)
  obtain ⟨o, ho, hoQ⟩ := S.exists_comm_not_mem_A5 hhat C.hH C.hKH C.hHK C.hL1K
    (α := C.α) C.α_surj C.α_eq_one_iff hcL (S.cL1_cube hhat) hcQ
  have hcN := le_normalizer_pCoreOf 2 S.L1 hcL
  have ho₁ : (S.cL1 hhat : G) * o * (S.cL1 hhat : G)⁻¹ * o⁻¹ ∈ pCoreOf 2 S.L1 :=
    (pCoreOf 2 S.L1).mul_mem ((Subgroup.mem_normalizer_iff.mp hcN o).mp ho)
      ((pCoreOf 2 S.L1).inv_mem ho)
  have ho₂ := (Subgroup.mem_normalizer_iff.mp hcN _).mp ho₁
  exact ⟨_, ho₁, _, ho₂, C.isKl_of_conj hcL (S.cL1_cube hhat) hcQ ho₁ hoQ ho₂⟩

theorem false_five (C : S.Ctx76 H K (FFModel.altDn 5)) :
    False := by
  have hodd := A6L76H.sum_one_five
  obtain ⟨x₁, h₁, x₂, h₂, hKl⟩ := C.exists_kl5 C.not_hat_of_five
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  obtain ⟨m, hm, hxm⟩ := C.exists_rep
  obtain ⟨hm1, hmz⟩ := C.classes_odd hodd hgL hg hm hxm
  have hgU : (g : G) * S.v2 * (g : G)⁻¹ ∈ conjClosure S.V3 H :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H (C.hL1H hgL)) _).mp
      (S.v2_mem_UH H)
  have hy := C.βU_equiv ⟨g, C.hL1K hgL⟩ ⟨S.v2, S.v2_mem_UH H⟩ hgU hm hxm
  have hym : G6.permAct 5 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m ∈ (FFModel.altDn 5).sec :=
    G6.permAct_mem_coreMod _ hm
  have hy1 : G6.permAct 5 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m ≠ 1 := fun h =>
    hm1 ((MulEquiv.map_eq_one_iff _).1 h)
  have hmy : m ≠ G6.permAct 5 (A6L76C.permOf (C.α ⟨g, C.hL1K hgL⟩)) m := fun h => by
    rw [← h, G6.permMod_mul_self] at hmz
    exact hm1 ((MulEquiv.map_eq_one_iff _).1 hmz.symm)
  exact hmy (A6L76E.kl5_eq hKl (G6.mem_coreMod.1 hm) (G6.mem_coreMod.1 hym) hm1 hy1
    (C.fix_O2L1 hodd h₁ S.v2_mem_V3 (S.v2_mem_UH H) hm hxm)
    (C.fix_O2L1 hodd h₂ S.v2_mem_V3 (S.v2_mem_UH H) hm hxm)
    (C.fix_O2L1 hodd h₁ (S.conj_v2_mem_V3 hg) hgU hym hy)
    (C.fix_O2L1 hodd h₂ (S.conj_v2_mem_V3 hg) hgU hym hy))

end Ctx76

end Setting4

end CFSG.Quasithin.H13.A6
