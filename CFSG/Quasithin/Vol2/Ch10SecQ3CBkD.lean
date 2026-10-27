module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkC
public import CFSG.Quasithin.Vol2.Ch10SecQ4S4
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.Quasithin.Vol2.Ch11SecHInputs
public import CFSG.Quasithin.Vol2.Ch10SecQ3CBkB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

section CZ

theorem isQuasisimple_map_equiv {Y : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) (f : G ≃* G) :
    CFSG.IsQuasisimple (↥(Y.map f.toMonoidHom) ⧸ CFSG.pCore 2 ↥(Y.map f.toMonoidHom)) := by
  let φ : Y ≃* (Y.map f.toMonoidHom : Subgroup G) :=
    Subgroup.equivMapOfInjective Y f.toMonoidHom f.injective
  let e := QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mp hq

theorem inf_centralizer_eq_bot [Finite G] {T X Y : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTX : T ≤ X) (hY : Y ∈ cComp X) (hYs : IsShort2 Y)
    (hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y)) (hQT : blockQ Y ≤ T)
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, (∀ s ∈ T, z ∈ Subgroup.centralizer
      ((Y.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G)) → z = 1) :
    blockQ Y ⊓ Subgroup.centralizer (Y : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := blockQ Y ⊓ Subgroup.centralizer (Y : Set G) with hR
  by_contra hR1
  set R' := conjClosure R T with hR'
  have hR'T : R' ≤ T := by
    rw [hR', conjClosure, Subgroup.closure_le]
    rintro _ ⟨h, hh, r, hr, rfl⟩
    exact T.mul_mem (T.mul_mem hh (hQT hr.1)) (T.inv_mem hh)
  have hTR' : T ≤ Subgroup.normalizer (R' : Set G) := le_normalizer_conjClosure R T
  have hRR' : R ≤ R' := fun r hr => Subgroup.subset_closure ⟨1, T.one_mem, r, hr, by simp⟩
  have hR'1 : R' ≠ ⊥ := fun h => hR1 (le_bot_iff.mp (h ▸ hRR'))
  have hYc : ∀ s ∈ T, Y.map (MulAut.conj s).toMonoidHom ∈ cComp X := fun s hs =>
    H13.LocDbl.map_conj_mem_cComp hY (Subgroup.le_normalizer (hTX hs))
  have hYs' : ∀ s : G, IsShort2 (Y.map (MulAut.conj s).toMonoidHom) := fun s =>
    (Lin2.isShort2_map_equiv_iff (MulAut.conj s) Y).mpr hYs
  have hR'C : ∀ s ∈ T, R' ≤ Subgroup.centralizer
      ((Y.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
    intro s hs
    rw [hR', conjClosure, Subgroup.closure_le]
    rintro _ ⟨h, hh, r, hr, rfl⟩
    by_cases heq : Y.map (MulAut.conj h).toMonoidHom = Y.map (MulAut.conj s).toMonoidHom
    · rw [← heq, SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hr.2 y hy
      change h * y * h⁻¹ * (h * r * h⁻¹) = h * r * h⁻¹ * (h * y * h⁻¹)
      calc h * y * h⁻¹ * (h * r * h⁻¹) = h * (y * r) * h⁻¹ := by group
        _ = h * (r * y) * h⁻¹ := by rw [h1]
        _ = h * r * h⁻¹ * (h * y * h⁻¹) := by group
    · have hc := SecF.C10P4F.commutator_eq_bot_of_mem_cComp (hYc h hh) (hYc s hs) (hYs' h)
        (hYs' s) (isQuasisimple_map_equiv hYq (MulAut.conj h)) heq
      have hrY : h * r * h⁻¹ ∈ Y.map (MulAut.conj h).toMonoidHom :=
        ⟨r, C1.blockQ_le Y hr.1, by simp [MulAut.conj_apply]⟩
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hrY
  obtain ⟨v, hv, hv1, hvT⟩ := SecA.exists_ne_one_mem_centralizer hT2 hR'T hTR' hR'1
  set C := R' ⊓ Subgroup.centralizer (T : Set G) with hC
  have hC2 : IsPGroup 2 C := hT2.to_le (inf_le_left.trans hR'T)
  obtain ⟨k, hk⟩ := hC2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hk
    have : v ∈ C := ⟨hv, hvT⟩
    rw [hk, Subgroup.mem_bot] at this
    exact hv1 this
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hw2 : (w : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw] at this
    exact congrArg Subtype.val this
  have hw1 : (w : G) ≠ 1 := by
    intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at hw
    exact absurd hw (by norm_num)
  have hwZ : (w : G) ∈ quasithinOmegaOneCenter T :=
    Subgroup.subset_closure ⟨⟨hR'T w.2.1, w.2.2⟩, hw2⟩
  exact hw1 (hZ w hwZ fun s hs => hR'C s hs w.2.1)

end CZ

section Steps

variable {X V : Subgroup G} {F : Type} [Field F] {n : ℕ}

theorem card_blockQ (X : Subgroup G) : Nat.card (blockQ X) = Nat.card (CFSG.pCore 2 ↥X) := by
  rw [blockQ, pCoreOf]
  exact Subgroup.card_map_of_injective X.subtype_injective

theorem card_eq_card_map_mul' {A B : Type*} [Group A] [Group B] (f : A →* B) {H : Subgroup A}
    (hH : f.ker ≤ H) : Nat.card H = Nat.card (H.map f) * Nat.card f.ker := by
  set g := f.comp H.subtype with hg
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hg, MonoidHom.range_comp,
    Subgroup.range_subtype] at h1
  have h2 : (f.comp H.subtype).ker = f.ker.subgroupOf H := rfl
  rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv] at h1
  exact h1

theorem blockQ_eq_or [Finite G] [Fintype F] (hAS : Ch11.SecH.AS_I_1_3_L2) (hn : 2 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (hperf : ⁅X, X⁆ = X)
    (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥X) :
    blockQ X = blockU X ∨ (n = 2 ∧ Nat.card (blockQ X) = 2 * Nat.card (blockU X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUQ : blockU X ≤ blockQ X :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (C1.le_normalizer_blockQ X)
  have hUX : blockU X ≤ X := hUQ.trans (C1.blockQ_le X)
  set N := (blockU X).subgroupOf X with hN
  have hNn : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUX).mpr (C1.le_normalizer_blockU X)
  set Q := CFSG.pCore 2 ↥X with hQ
  have hNQ : N ≤ Q := fun x hx => (mem_blockQ_iff x).mp (hUQ hx)
  set Zq := Q.map (QuotientGroup.mk' N) with hZq
  have hZn : Zq.Normal := (CFSG.pCore_normal (p := 2) (G := ↥X)).map _
    (QuotientGroup.mk'_surjective N)
  have hZc : Zq ≤ Subgroup.center (↥X ⧸ N) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    change ((y : G) * q)⁻¹ * (q * y) ∈ blockU X
    have e : ((y : G) * q)⁻¹ * (q * y) = ⁅(q : G)⁻¹, (y : G)⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator (inv_mem ((mem_blockQ_iff q).mpr hq)) (inv_mem y.2)
  have e : (↥X ⧸ N) ⧸ Zq ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientQuotientEquivQuotient N Q hNQ).trans
      ((QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs))
  have hperf' : Group.IsPerfect (↥X ⧸ N) := by
    have : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hperf
    infer_instance
  rcases hAS n hn F (by rw [Nat.card_eq_fintype_card, hF]) (↥X ⧸ N) hperf' Zq hZc ⟨e⟩ with
    h | ⟨h2, hcard, -⟩
  · left
    have hQN : Q ≤ N := by
      intro q hq
      have : QuotientGroup.mk' N q ∈ Zq := ⟨q, hq, rfl⟩
      rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    refine le_antisymm (fun x hx => ?_) hUQ
    exact hQN ((mem_blockQ_iff ⟨x, C1.blockQ_le X hx⟩).mp hx)
  · right
    refine ⟨h2, ?_⟩
    have hker : (QuotientGroup.mk' N).ker ≤ Q := by rw [QuotientGroup.ker_mk']; exact hNQ
    have h1 := card_eq_card_map_mul' (QuotientGroup.mk' N) hker
    rw [← hZq, hcard, QuotientGroup.ker_mk'] at h1
    rw [card_blockQ, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv]

theorem commutator_eq_inf [CharP F 2] (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαk : α.ker = CFSG.pCore 2 ↥X) (h : NatData X V n) (hQV : blockQ X = V) {b : G}
    (hb : b ∈ X) (hsq : α ⟨b, hb⟩ ^ 2 ≠ 1) (hbo : Odd (orderOf b)) (hb1 : orderOf b ≠ 1)
    [Finite G] {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSX : S ≤ Subgroup.normalizer (X : Set G)) (hbS : b ∈ Subgroup.normalizer (S : Set G)) :
    ⁅S, Subgroup.zpowers b⁆ = S ⊓ X := by
  refine le_antisymm (le_inf (commutator_zpowers_le hbS) ?_) ?_
  · exact (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hb)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hSX)
  · refine le_commutator_of_fix inf_le_left
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨hbS, Subgroup.le_normalizer hb⟩) ?_
    intro x hx hxb
    obtain ⟨k, hk⟩ := hS2 ⟨x, hx.1⟩
    have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hxV : x ∈ V := hQV ▸ mem_blockQ_of_commute α hαk hb hsq hx.2 hxk hxb
    exact h.eq_one_of_fix hb hb1 hbo hxV (by rw [← hxb, mul_inv_cancel_right])

theorem card_inf_eq [Fintype F] (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥X) (h : NatData X V n) (hQV : blockQ X = V) [Finite G]
    {S : Subgroup G} (hSyl : IsSylowTwoOf (S ⊓ X) X) : Nat.card ↥(S ⊓ X) = 2 ^ n * 4 ^ n := by
  have hle : blockQ X ≤ S ⊓ X := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSyl
  rw [card_eq_mul α hαk inf_le_right, card_map_sylow hn hF α hαs hSyl, inf_eq_right.mpr hle, hQV,
    h.card]

theorem commutator_blockQ_le [Finite G] [Fintype F] [CharP F 2] (hn : 1 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (α : ↥X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥X) (h : NatData X V n) {b : G}
    (hb : b ∈ X) (hsq : α ⟨b, hb⟩ ^ 2 ≠ 1) (hbo : Odd (orderOf b)) (hb1 : orderOf b ≠ 1)
    {P : Subgroup G} (hP : IsSylowTwoOf P X) (hbP : b ∈ Subgroup.normalizer (P : Set G))
    (hcard : Nat.card ↥(⁅P, Subgroup.zpowers b⁆ : Subgroup G) ≤ 2 ^ n * 4 ^ n) :
    ⁅blockQ X, Subgroup.zpowers b⁆ ≤ V := by
  have h1 := card_commutator_le hn hF α hαs hαk hb hsq hP hbP
  have h2 : Nat.card ↥(⁅blockQ X, Subgroup.zpowers b⁆ : Subgroup G) ≤ Nat.card V := by
    rw [h.card]
    have := h1.trans hcard
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have hVle : V ≤ ⁅blockQ X, Subgroup.zpowers b⁆ := by
    refine le_commutator_of_fix h.le (h.norm hb) fun x hx hxb => ?_
    exact h.eq_one_of_fix hb hb1 hbo hx (by rw [← hxb, mul_inv_cancel_right])
  exact (Subgroup.eq_of_le_of_card_ge hVle h2).symm.le

end Steps

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS
