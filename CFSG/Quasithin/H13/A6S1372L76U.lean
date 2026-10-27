module

public import CFSG.Quasithin.H13.A6S1372L76T

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge Matrix
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_w (hhat : IsHatA6 L) :
    ∃ w : ↥L, (w : G) ∈ S.L1 ∧ (w : G) ∈ Subgroup.centralizer (V : Set G) ∧ w ^ 3 = 1 ∧
      (w : ↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := hhat.2.1
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) 3 (by rw [hZ3])
  have hφζ : S.phiQ (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
    have hcomm : ∀ σ ∈ alternatingGroup (Fin 6),
        S.phiQ (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) * σ = σ * S.phiQ (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) := by
      intro σ hσ
      rw [← S.phiQ_range] at hσ
      obtain ⟨q, rfl⟩ := hσ
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ζ.2 q]
    exact A6L76F.center_alt6 _ (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
      (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
      (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
      (hcomm _ (Perm.mem_alternatingGroup.2 (by decide)))
  obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) (ζ : ↥L ⧸ CFSG.pCore 2 ↥L)
  have hwC : (w : G) ∈ Subgroup.centralizer (V : Set G) := by
    rw [← S.rho_eq_one_iff ⟨w, S.frame.L_le w.2⟩, ← S.phiQ_mk]
    rw [← hw] at hφζ
    exact hφζ
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hw'm : (w ^ (2 ^ a)) ^ m = 1 := by rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hw'L1 : ((w ^ (2 ^ a) : ↥L) : G) ∈ S.L1 := by
    refine Subgroup.subset_closure ⟨⟨(w ^ (2 ^ a)).2, ?_⟩, m, hm, ?_⟩
    · show ((w ^ (2 ^ a) : ↥L) : G) ∈ Subgroup.normalizer (fsuV1 T V : Set G)
      rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
      have hwz : (w : G) * S.z = S.z * w :=
        (Subgroup.mem_centralizer_iff.mp hwC S.z S.z_mem_V).symm
      rw [Subgroup.coe_pow]
      exact (Commute.pow_left hwz _).eq
    · simpa using congrArg Subtype.val hw'm
  have hζ3 : (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rw [hζ] at this
    simpa using congrArg Subtype.val this
  have hwq : ((w ^ (2 ^ a) : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) =
      (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) ^ (2 ^ a) := by
    rw [QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, hw]
  have hwq1 : (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) ^ (2 ^ a) ≠ 1 := by
    intro h
    have h1 : orderOf (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
    have h2 : orderOf (ζ : ↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
      rw [← hζ]
      exact Subgroup.orderOf_coe ζ
    rw [h2] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hw3 : (w ^ (2 ^ a)) ^ 3 = 1 := by
    have hxN : (w ^ (2 ^ a)) ^ 3 ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hwq, ← pow_mul, mul_comm, pow_mul,
        hζ3, one_pow]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)) ⟨_, hxN⟩
    have hk' : ((w ^ (2 ^ a)) ^ 3) ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hm' : ((w ^ (2 ^ a)) ^ 3) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hw'm, one_pow]
    have hcop : Nat.Coprime (2 ^ k) m := (Odd.coprime_two_left hm).pow_left k
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  refine ⟨w ^ (2 ^ a), hw'L1, ?_, hw3, by rw [hwq]; exact hwq1⟩
  rw [Subgroup.coe_pow]
  exact Subgroup.pow_mem _ hwC _

theorem exists_comm_T (hhat : IsHatA6 L) {w : ↥L}
    (hwV : (w : G) ∈ Subgroup.centralizer (V : Set G)) (hw3 : w ^ 3 = 1)
    (hwQ : (w : ↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1) :
    ∃ n : ↥(Subgroup.normalizer (V : Set G)), (n : G) ∈ T ∧
      S.frame.ρ n = swap 0 1 * swap 4 5 ∧ (n : G) * w = w * n := by
  have := S.perfect_Q
  have hnorm : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  obtain ⟨t, htT, htρ⟩ := S.frame.DA_T (swap 0 1 * swap 4 5) (by decide)
    (Perm.mem_alternatingGroup.2 (by decide))
  have htL : (t : G) ∈ Subgroup.normalizer (L : Set G) := S.T_le_NL htT
  have hwZ := S.mk_mem_center hwV
  have hα : ∀ q, S.phiQ (conjQ htL q) =
      (swap 0 1 * swap 4 5) * S.phiQ q * (swap 0 1 * swap 4 5)⁻¹ := by
    intro q
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective q
    rw [conjQ_mk, S.phiQ_mk, S.phiQ_mk]
    have e : (⟨((conjL htL w' : ↥L) : G), S.frame.L_le (conjL htL w').2⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = t * ⟨w', S.frame.L_le w'.2⟩ * t⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, htρ]
  have hfix := A6L76T.Hat3.fix_of_cover hhat.2.1 S.phiQ S.phiQ_ker S.phiQ_range (conjQ htL)
    (Perm.mem_alternatingGroup.2 (by decide)) hα hwZ
  rw [conjQ_mk] at hfix
  set E : Subgroup ↥L := (Subgroup.zpowers (w : ↥L ⧸ CFSG.pCore 2 ↥L)).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) with hE
  have hxE : conjL htL w ∈ E := by
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L) (conjL htL w) ∈ Subgroup.zpowers _
    rw [QuotientGroup.mk'_apply, hfix]
    exact Subgroup.mem_zpowers _
  have hwE : w ∈ E := by
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L) w ∈ Subgroup.zpowers _
    rw [QuotientGroup.mk'_apply]
    exact Subgroup.mem_zpowers _
  set N : Subgroup ↥E := (CFSG.pCore 2 ↥L).subgroupOf E with hN
  have : N.Normal := hnorm.subgroupOf E
  have hNp : IsPGroup 2 N :=
    (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L)).comap_of_injective E.subtype
      E.subtype_injective
  have hoq : orderOf (w : ↥L ⧸ CFSG.pCore 2 ↥L) = 3 :=
    orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hw3, QuotientGroup.mk_one]) hwQ
  have hidx : N.index = 3 := by
    let f : ↥E →* ↥L ⧸ CFSG.pCore 2 ↥L := (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp E.subtype
    have hker : f.ker = N := by
      ext x
      rw [MonoidHom.mem_ker, hN, Subgroup.mem_subgroupOf]
      exact QuotientGroup.eq_one_iff _
    have hrange : f.range = Subgroup.zpowers (w : ↥L ⧸ CFSG.pCore 2 ↥L) := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact x.2
      · rw [Subgroup.zpowers_le]
        exact ⟨⟨w, hwE⟩, rfl⟩
    rw [← hker, Subgroup.index_ker, hrange, Nat.card_zpowers, hoq]
  have hmemN : ∀ x : ↥E, x ∈ N ↔ ((x : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
    intro x
    rw [hN, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
  have hx3 : (⟨conjL htL w, hxE⟩ : ↥E) ^ 3 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, ← map_pow, hw3, map_one]; rfl)
  have hy3 : (⟨w, hwE⟩ : ↥E) ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hw3]; rfl)
  have hxN : (⟨conjL htL w, hxE⟩ : ↥E) ∉ N := by
    rw [hmemN]
    show ((conjL htL w : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ≠ 1
    rw [hfix]
    exact hwQ
  have hxy : (⟨conjL htL w, hxE⟩ : ↥E)⁻¹ * ⟨w, hwE⟩ ∈ N := by
    rw [hmemN]
    show (((conjL htL w)⁻¹ * w : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hfix, inv_mul_cancel]
  obtain ⟨d, hdN, hd⟩ := A6L76T.exists_conj_of_three hNp hidx hx3 hy3 hxN hxy
  have hdO : (((d : ↥E) : ↥L) : G) ∈ pCoreOf 2 L := by
    rw [← mem_pCore_iff]
    exact hdN
  refine ⟨⟨_, S.frame.L_le ((d : ↥E) : ↥L).2⟩ * t, T.mul_mem (S.pCoreOf_L_le_T hdO) htT, ?_, ?_⟩
  · rw [map_mul, htρ, (S.rho_eq_one_iff _).2 (S.pCoreOf_L_le_centralizer hdO), one_mul]
  · have h1 := congrArg (fun x : ↥E => ((x : ↥L) : G)) hd
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have e : ((conjL htL w : ↥L) : G) = (t : G) * w * (t : G)⁻¹ := rfl
    rw [e] at h1
    show (((d : ↥E) : ↥L) : G) * t * w = w * ((((d : ↥E) : ↥L) : G) * t)
    calc (((d : ↥E) : ↥L) : G) * t * w
        = ((((d : ↥E) : ↥L) : G) * ((t : G) * w * (t : G)⁻¹) * (((d : ↥E) : ↥L) : G)⁻¹) *
          ((((d : ↥E) : ↥L) : G) * t) := by group
      _ = w * ((((d : ↥E) : ↥L) : G) * t) := by rw [h1]

variable {S}

namespace Ctx76

variable {H K : Subgroup G} [IsMulCommutative ↥(conjClosure S.V3 H)]
  {α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2)}

theorem false_hat_a7 (C : S.Ctx76 H K (FFModel.a7Four α))
    (hfix : fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) = ⊥) (hhat : IsHatA6 L) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 C.hH
  obtain ⟨w, hwL1, hwV, hw3, hwQ⟩ := S.exists_w hhat
  obtain ⟨n, hnT, hnρ, hnw⟩ := S.exists_comm_T hhat hwV hw3 hwQ
  have hnH : (n : G) ∈ H := C.hTH hnT
  have hmem : A6Mod.secAct hHU hHV ⟨n, hnH⟩ ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)) := by
    rw [← C.tilde_eq_a7 hfix]
    exact (A6Mod.mem_autSec_iff hHU hHV le_rfl).2 ⟨⟨n, hnH⟩, hnH, rfl⟩
  obtain ⟨⟨k₀, hk₀H⟩, hk₀K, hk₀⟩ := (A6Mod.mem_autSec_iff hHU hHV C.hKH).1 hmem
  set k : ↥K := ⟨k₀, hk₀K⟩ with hkdef
  have hk : ((C.κ k : ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) : MulAut _) =
      A6Mod.secAct hHU hHV ⟨n, hnH⟩ := by
    rw [C.κ_coe]
    exact hk₀
  set wK : ↥K := ⟨w, C.hL1K hwL1⟩ with hwK
  have hκ : C.κ k * C.κ wK = C.κ wK * C.κ k := by
    apply Subtype.ext
    have e : (⟨n, hnH⟩ : ↥H) * ⟨w, C.hKH wK.2⟩ = ⟨w, C.hKH wK.2⟩ * ⟨n, hnH⟩ := Subtype.ext hnw
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hk, C.κ_coe, ← map_mul, e, map_mul]
  have hσb' : C.α k * C.α wK = C.α wK * C.α k := by
    show C.eπ.symm (C.κ k) * C.eπ.symm (C.κ wK) = C.eπ.symm (C.κ wK) * C.eπ.symm (C.κ k)
    rw [← map_mul, hκ, map_mul]
  have hwK3 : wK ^ 3 = 1 := Subtype.ext (by
    have := congrArg Subtype.val hw3
    simpa using this)
  have hb3' : C.α wK ^ 3 = 1 := by rw [← map_pow, hwK3, map_one]
  have hb1' : C.α wK ≠ 1 := by
    intro h
    have hwK1 : wK ≠ 1 := by
      intro h1
      apply hwQ
      have h2 : ((wK : ↥K) : G) = 1 := congrArg Subtype.val h1
      have : w = 1 := Subtype.ext h2
      rw [this, QuotientGroup.mk_one]
    have hker : wK ∈ C.α.ker := h
    have ho : orderOf (⟨wK, hker⟩ : ↥C.α.ker) = 3 :=
      orderOf_eq_prime (Subtype.ext (by simpa using hwK3))
        (fun h1 => hwK1 (congrArg Subtype.val h1))
    exact C.not_three_dvd_ker (ho ▸ orderOf_dvd_natCard _)
  have hbfix' : A6L76T.mat7 α (C.α wK) *ᵥ C.cls7 ⟨S.v2, S.v2_mem_UH H⟩ =
      C.cls7 ⟨S.v2, S.v2_mem_UH H⟩ := by
    have hku := C.conj_mem_UH wK.2 (S.v2_mem_UH H)
    rw [← C.cls7_equiv wK _ hku]
    congr 1
    apply Subtype.ext
    show (w : G) * S.v2 * (w : G)⁻¹ = S.v2
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp hwV S.v2 S.v2_mem_V).symm
  obtain ⟨e, he⟩ := S.h13.sylow.1 ⟨n, hnT⟩
  have hne : (⟨n, hnH⟩ : ↥H) ^ (2 ^ e) = 1 := Subtype.ext (by
    have := congrArg Subtype.val he
    simpa using this)
  have h1 : C.κ k ^ (2 ^ e) = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, hk, ← map_pow, hne, map_one]
    rfl
  have hσe' : C.α k ^ (2 ^ e) = 1 := by
    show C.eπ.symm (C.κ k) ^ (2 ^ e) = 1
    rw [← map_pow, h1, map_one]
  obtain ⟨b, hb⟩ : ∃ b : ↥(alternatingGroup (Fin 7)), b = C.α wK := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ↥(alternatingGroup (Fin 7)), σ = C.α k := ⟨_, rfl⟩
  have hσb : σ * b = b * σ := by rw [hσ, hb]; exact hσb'
  have hb3 : b ^ 3 = 1 := by rw [hb]; exact hb3'
  have hb1 : b ≠ 1 := by rw [hb]; exact hb1'
  have hbfix : A6L76T.mat7 α b *ᵥ C.cls7 ⟨S.v2, S.v2_mem_UH H⟩ =
      C.cls7 ⟨S.v2, S.v2_mem_UH H⟩ := by rw [hb]; exact hbfix'
  have hb3c : ¬ (b : Perm (Fin 7)).IsThreeCycle := by
    intro hc
    have h0 := A6L76S.fpf_of_isThreeCycle α hc _ hbfix
    exact C.βU_v2_ne_one ((C.cls7_eq_zero_iff _).1 h0)
  have hσe : σ ^ (2 ^ e) = 1 := by rw [hσ]; exact hσe'
  have hσ8 : σ ^ 8 = 1 := by
    obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hσe)
    have hd : orderOf σ ∣ 2520 := by
      have := orderOf_dvd_natCard σ
      rwa [nat_card_alternatingGroup, Nat.card_fin] at this
    have hj3 : j ≤ 3 := by
      by_contra hj3
      push Not at hj3
      have h16 : 2 ^ 4 ∣ 2520 := (Nat.pow_dvd_pow 2 hj3).trans (hjo ▸ hd)
      norm_num at h16
    rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← orderOf_dvd_iff_pow_eq_one, hjo]
    exact Nat.pow_dvd_pow 2 hj3
  have hσ1 : (σ : Perm (Fin 7)) = 1 :=
    A6L76S.eq_one_of_comm_order_three
      (by rw [← Subgroup.coe_pow, hb3]; rfl)
      (fun h => hb1 (Subtype.ext h)) hb3c (congrArg Subtype.val hσb)
      (Perm.mem_alternatingGroup.1 σ.2)
      (by rw [← Subgroup.coe_pow, hσ8]; rfl)
  have hκ1 : C.κ k = 1 := by
    have h2 : σ = 1 := Subtype.ext hσ1
    have h3 : C.eπ.symm (C.κ k) = 1 := hσ.symm.trans h2
    rwa [MulEquiv.map_eq_one_iff] at h3
  have hsec1 : A6Mod.secAct hHU hHV ⟨n, hnH⟩ = 1 := by
    rw [← hk, hκ1]
    rfl
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have h1 := (A6Mod.secAct_eq_one_iff hHU hHV _).1 hsec1 _
    (C.conj_mem_UH (C.hL1K hgL) (S.v2_mem_UH H))
  have hng : (n : G) * ((g : G) * S.v2 * (g : G)⁻¹) * (n : G)⁻¹ =
      ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
        ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ := by
    have e1 : (n : G) * ((g : G) * S.v2 * (g : G)⁻¹) * (n : G)⁻¹ =
        ((n * g : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
          ((n * g : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ := by
      rw [Subgroup.coe_mul]
      group
    rw [e1]
    have h2 : S.frame.ψ ⟨_, S.conj_v2_mem_V (n * g)⟩ = S.frame.ψ ⟨_, S.conj_v2_mem_V (g ^ 2)⟩ := by
      apply Subtype.ext
      rw [S.psi_conj_v2, S.psi_conj_v2, map_mul, map_pow, hnρ, hg]
      decide
    exact congrArg Subtype.val (S.frame.ψ.injective h2)
  rw [hng, ← S.v2_mul_conj hg, mul_inv_cancel_right] at h1
  exact S.v2_not_mem_V1 h1

end Ctx76

variable (S)
include S

theorem lem1376_four (hB : Lem1376L1K) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h1337 : Stmt13_3_7)
    (hNS : ¬ LieModel G .PSp 3 2 1) (hNU : ¬ LieModel G .PSU 4 3 1) {H : Subgroup G}
    (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)] {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ A7Four (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) := by
  intro hA
  have hL1K := hB G T L V S hNS hNU H hH hab K hK
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA)))))
  obtain ⟨α, π, hπ⟩ := id hA
  have : IsSimpleGroup (FFModel.a7Four α).Gam := A6L76A.isSimpleGroup_alt (n := 7) (by norm_num)
  obtain ⟨C⟩ := S.exists_ctx h37 h38 h13315 h1356two hNS hH hab hK hL1K
    (A6L76A.not_isSolvable_alt (n := 7) (by norm_num)) ⟨π, hπ⟩
  have hfix := A6L76R.fixV_eq_bot_of_a7Four _ _ (fun v => (sq v).symm.trans (C.sq_tildeU v))
    C.top hA
  exact C.false_hat_a7 hfix (C.hat_of_a7 h1337 hfix)

end Setting4

end CFSG.Quasithin.H13.A6
