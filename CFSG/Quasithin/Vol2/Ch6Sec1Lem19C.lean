module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19M
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace Cfg619

variable (h : Hyp6116 G T M L V n) {H : Subgroup G} (c : Cfg619 T L V H n y)
include h c

theorem commutator_inf_K2_mem {z : G} (hz : Z619 T L V H y z) {Y : Subgroup G}
    (hY : IsY619 T L V z Y) :
    ∀ x ∈ conjClosure (conjSub y V) Y ⊓ ch619K2 T L V z, ∀ p ∈ conjClosure (conjSub y V) Y,
      x * p * x⁻¹ * p⁻¹ ∈ pCoreOf 2 (conjClosure (conjSub y V) Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := conjClosure (conjSub y V) Y with hX
  have hXI : X ≤ ch619I T L V := c.conjClosure_E_le_I hY
  have hXK1 := c.commutator_conjClosure_K1_mem h hz.ne_one hz.eq_inf hz.eq_comm
    hY.le_normalizer_I hY.le_normalizer_K1
  have hcen := commutator_inf_K1_mem hXI hXK1
  have hle := inf_K2_le_sup h hz.mem_ZS hXI hXK1
  have hXO : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  intro x hx p hp
  have hx' : x ∈ (((X ⊓ ch619K1 T L V z) ⊔ pCoreOf 2 X : Subgroup G) : Set G) := hle hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, ?_⟩))] at hx'
  · obtain ⟨k, hk, o, ho, rfl⟩ := hx'
    have h1 := hcen k hk p hp
    have h2 : o * p * o⁻¹ * p⁻¹ ∈ pCoreOf 2 X := by
      have : p * o⁻¹ * p⁻¹ ∈ pCoreOf 2 X :=
        (Subgroup.mem_normalizer_iff.mp (hXO hp) _).mp (Subgroup.inv_mem _ ho)
      have e : o * p * o⁻¹ * p⁻¹ = o * (p * o⁻¹ * p⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ ho this
    have h3 : k * (o * p * o⁻¹ * p⁻¹) * k⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp (hXO hk.1) _).mp h2
    have e : k * o * p * (k * o)⁻¹ * p⁻¹ =
        k * (o * p * o⁻¹ * p⁻¹) * k⁻¹ * (k * p * k⁻¹ * p⁻¹) := by group
    show k * o * p * (k * o)⁻¹ * p⁻¹ ∈ pCoreOf 2 X
    rw [e]
    exact Subgroup.mul_mem _ h3 h1
  ·
    have hIz : ch619I T L V ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
      L619.le_normalizer_zpowers (L619.centralizer_le_centralizer_singleton hz.mem_ZS)
    exact le_normalizer_centralizerMod hIz Subgroup.le_normalizer
      (centralizer_ZS_le_normalizer_W hz.mem_ZS) (hXI hg)

theorem inf_K2_le_pCoreOf (h432 : Stmt4_3_2) {z : G} (hz : Z619 T L V H y z) {Y : Subgroup G}
    (hY : IsY619 T L V z Y) (hW : IsElemAbelian 2 (ch619W T L V z))
    (hcyc : ∀ p [Fact p.Prime], p ≠ 2 →
      ∀ Q : Sylow p ↥(L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) Y)), IsCyclic Q) :
    conjClosure (conjSub y V) Y ⊓ ch619K2 T L V z ≤ pCoreOf 2 (conjClosure (conjSub y V) Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := conjClosure (conjSub y V) Y with hX
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) X with hN
  set K := L619.img0 hW (ch6ZS T L V) X with hK
  have hXI : X ≤ ch619I T L V := c.conjClosure_E_le_I hY
  have hXN : X ≤ N := c.conjClosure_E_le_normWZX hY
  have hIX : ch619I T L V ≤ Subgroup.normalizer (X : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  let φ₀ : ↥X →* MulAut ↥(L619.V0 hW (ch6ZS T L V) X) :=
    (L619.act0 hW (ch6ZS T L V) X).comp (Subgroup.inclusion hXN)
  have hφ₀ : ∀ x, φ₀ x ∈ K := fun x => L619.act0_mem_img0 hW _ X (g := ⟨x, hXN x.2⟩) x.2
  let φ : ↥X →* ↥K := φ₀.codRestrict K hφ₀
  have hφ1 : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := ⟨x, hXN x.2⟩) x.2
  set O := (pCoreOf 2 X).subgroupOf X with hO
  have hOn : O.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (CFSG.LieType.BorelTits.pCoreOf_le 2 X)).mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  have hOker : O ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ1]
    have hxO : (x : G) ∈ pCoreOf 2 X := hx
    exact pCoreOf_I_le_K2 h h432 z (F7.pCoreOf_mono_of_le_normalizer hXI hIX hxO)
  let η : ↥X ⧸ O →* ↥K := QuotientGroup.lift O φ hOker
  have hηs : Function.Surjective η := by
    rintro ⟨k, hk⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
    rw [Subgroup.mem_subgroupOf] at hx
    exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩
  have hηk : ∀ x : ↥X, η (QuotientGroup.mk x) = 1 ↔ (x : G) ∈ ch619K2 T L V z := fun x => hφ1 x
  have hcentral : η.ker ≤ Subgroup.center (↥X ⧸ O) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hxK : (x : G) ∈ ch619K2 T L V z := (hηk x).mp hq
    rw [Subgroup.mem_center_iff]
    intro r
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective r
    have hcomm := c.commutator_inf_K2_mem h hz hY (x : G) ⟨x.2, hxK⟩ (p : G) p.2
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hmem : (x * p * x⁻¹ * p⁻¹ : ↥X) ∈ O := hcomm
    have e : (p * x)⁻¹ * (x * p) = (p * x)⁻¹ * (x * p * x⁻¹ * p⁻¹) * ((p * x)⁻¹)⁻¹ := by group
    rw [e]
    exact hOn.conj_mem _ hmem _
  have hodd : Odd (Nat.card η.ker) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := η.ker) 2 (even_iff_two_dvd.mp hev)
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (q : ↥X ⧸ O)
    have hq1 : (q : ↥X ⧸ O) ≠ 1 := by
      intro h1
      have : q = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hq
      omega
    let R : Subgroup ↥X := (Subgroup.zpowers (q : ↥X ⧸ O)).comap (QuotientGroup.mk' O)
    have hR2 : IsPGroup 2 R := by
      refine IsPGroup.comap_of_ker_isPGroup ?_ _ ?_
      · apply IsPGroup.of_card (n := 1)
        rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_coe, hq]
      · rw [QuotientGroup.ker_mk']
        exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_of_ker_isPGroup X.subtype
          (IsPGroup.ker_isPGroup_of_injective X.subtype_injective))
    have hRn : R.Normal := by
      refine Subgroup.Normal.comap ?_ _
      refine ⟨fun a ha g => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hz' := Subgroup.mem_center_iff.mp
        ((Subgroup.center (↥X ⧸ O)).zpow_mem (hcentral q.2) k) g
      rw [hz', mul_inv_cancel_right]
      exact Subgroup.zpow_mem_zpowers _ k
    have hRG : R.map X.subtype ≤ pCoreOf 2 X := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (Subgroup.map_subtype_le R) ?_ (hR2.map _)
      intro g hg
      refine mem_normalizer_of_forall_conj_mem_of_le fun u hu => ?_
      obtain ⟨r, hr, rfl⟩ := hu
      exact ⟨⟨g, hg⟩ * r * ⟨g, hg⟩⁻¹, hRn.conj_mem r hr ⟨g, hg⟩, rfl⟩
    have hxR : x ∈ R := by
      show QuotientGroup.mk' O x ∈ Subgroup.zpowers (q : ↥X ⧸ O)
      rw [QuotientGroup.mk'_apply, hx]
      exact Subgroup.mem_zpowers _
    have hxO : (x : G) ∈ pCoreOf 2 X := hRG ⟨x, hxR, rfl⟩
    apply hq1
    rw [← hx]
    exact (QuotientGroup.eq_one_iff x).mpr hxO
  have hgen : Subgroup.closure {u : ↥X ⧸ O | ∃ k : ℕ, u ^ 2 ^ k = 1} = ⊤ := by
    have h2 : ∀ g ∈ Y, ∀ e ∈ conjSub y V, (g * e * g⁻¹) ^ 2 = 1 := by
      intro g hg e he
      have he2 : e ^ 2 = 1 := by
        obtain ⟨v, hv, rfl⟩ := he
        have : v ^ 2 = 1 := h.toHyp611.isElemAbelian.2 v hv
        rw [← map_pow, this, map_one]
      rw [conj_pow, he2, mul_one, mul_inv_cancel]
    have hXcl : Subgroup.closure (((↑) : ↥X → G) ⁻¹'
        {u | ∃ g ∈ Y, ∃ e ∈ conjSub y V, g * e * g⁻¹ = u}) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [eq_top_iff]
    rintro u -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    have hx : x ∈ Subgroup.closure (((↑) : ↥X → G) ⁻¹'
        {u | ∃ g ∈ Y, ∃ e ∈ conjSub y V, g * e * g⁻¹ = u}) := by rw [hXcl]; trivial
    have hle : Subgroup.closure (((↑) : ↥X → G) ⁻¹'
        {u | ∃ g ∈ Y, ∃ e ∈ conjSub y V, g * e * g⁻¹ = u}) ≤
        (Subgroup.closure {u : ↥X ⧸ O | ∃ k : ℕ, u ^ 2 ^ k = 1}).comap (QuotientGroup.mk' O) := by
      rw [Subgroup.closure_le]
      rintro w ⟨g, hg, e, he, hw⟩
      refine Subgroup.subset_closure ⟨1, ?_⟩
      show (QuotientGroup.mk' O w) ^ 2 ^ 1 = 1
      rw [← map_pow, pow_one]
      have : w ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, ← hw]; exact h2 g hg e he)
      rw [this, map_one]
    exact hle hx
  have hbot := L619.central_ker_eq_bot_of_cyclic η hηs hcentral hodd hgen hcyc
  intro x hx
  have h1 : η (QuotientGroup.mk ⟨x, hx.1⟩) = 1 := (hηk ⟨x, hx.1⟩).mpr hx.2
  have h2 : (QuotientGroup.mk ⟨x, hx.1⟩ : ↥X ⧸ O) ∈ η.ker := h1
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h2
  exact h2

end Cfg619

end CFSG.Quasithin.H13
