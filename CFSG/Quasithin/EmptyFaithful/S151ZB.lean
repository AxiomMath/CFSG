module

public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg
import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
public import CFSG.Quasithin.EmptyFaithful.S151YC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem zb_mem_sup {P S : Subgroup G} (hSP : S ≤ Subgroup.normalizer (P : Set G)) {x : G}
    (hx : x ∈ P ⊔ S) : ∃ p ∈ P, ∃ s ∈ S, x = p * s := by
  have h : ((P ⊔ S : Subgroup G) : Set G) = (P : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P S hSP
  have hx' : x ∈ ((P ⊔ S : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨p, hp, s, hs, rfl⟩ := hx'
  exact ⟨p, hp, s, hs, rfl⟩

theorem zb_relIndex_sup {P S : Subgroup G} (hSP : S ≤ Subgroup.normalizer (P : Set G)) :
    P.relIndex (P ⊔ S) = P.relIndex S := by
  set A : Subgroup G := P ⊔ S with hA
  have hPA : P ≤ A := le_sup_left
  have hSA : S ≤ A := le_sup_right
  have hAN : A ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hSP
  have hKn : (P.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPA).mpr hAN
  have h1 := Subgroup.relIndex_sup_right (S.subgroupOf A) (P.subgroupOf A)
  have htop : S.subgroupOf A ⊔ P.subgroupOf A = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨p, hp, s, hs, hg⟩ := zb_mem_sup hSP g.2
    have : g = ⟨p, hPA hp⟩ * ⟨s, hSA hs⟩ := Subtype.ext hg
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hp))
      (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hs))
  rw [htop, Subgroup.relIndex_top_right, Subgroup.relIndex_subgroupOf hSA] at h1
  exact h1

theorem zb_mul_pow_mem {N : Subgroup G} {p s : G} (hs : s ∈ Subgroup.normalizer (N : Set G))
    (hp : p ∈ N) (n : ℕ) : ∃ q ∈ N, (p * s) ^ n = q * s ^ n := by
  induction n with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, hqe⟩ := ih
    have hsn : s ^ n ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hs n
    have h1 : s ^ n * p * (s ^ n)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hsn p).mp hp
    refine ⟨q * (s ^ n * p * (s ^ n)⁻¹), N.mul_mem hq h1, ?_⟩
    rw [pow_succ, hqe, pow_succ]
    group

theorem zb_normalizes_pCoreOf {L : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    s ∈ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hs

structure Par2 (L S P : Subgroup G) : Prop where
  s2 : IsPGroup 2 ↥S
  sN : S ≤ Subgroup.normalizer (L : Set G)
  syl : IsSylowTwoOf (S ⊓ L) L
  le : P ≤ L
  sl : S ⊓ L ≤ P
  sP : S ≤ Subgroup.normalizer (P : Set G)
  idx : Nat.card ↥P = 3 * Nat.card ↥(S ⊓ L)
  nn : ¬ P ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)

variable {L S P : Subgroup G}

theorem Par2.inf_eq (h : Par2 L S P) : P ⊓ S = S ⊓ L := by
  apply le_antisymm
  · intro x hx
    exact ⟨hx.2, h.le hx.1⟩
  · intro x hx
    exact ⟨h.sl hx, hx.1⟩

theorem Par2.card_S [Finite G] (h : Par2 L S P) :
    Nat.card ↥S = P.relIndex S * Nat.card ↥(S ⊓ L) := by
  have := Subgroup.relIndex_mul_card P S
  rw [h.inf_eq] at this
  exact this.symm

theorem Par2.card_H [Finite G] (h : Par2 L S P) : Nat.card ↥(P ⊔ S) = 3 * Nat.card ↥S := by
  have h1 := Subgroup.relIndex_mul_card P (P ⊔ S)
  have h2 : P ⊓ (P ⊔ S) = P := inf_eq_left.mpr le_sup_left
  rw [h2, zb_relIndex_sup h.sP] at h1
  rw [← h1, h.idx, h.card_S]
  ring

theorem Par2.relIndex_S [Finite G] (h : Par2 L S P) : S.relIndex (P ⊔ S) = 3 := by
  have h1 := Subgroup.relIndex_mul_card S (P ⊔ S)
  have h2 : S ⊓ (P ⊔ S) = S := inf_eq_left.mpr le_sup_right
  rw [h2, h.card_H] at h1
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem Par2.sylow [Finite G] (h : Par2 L S P) : IsSylowTwoOf S (P ⊔ S) := by
  refine ⟨le_sup_right, h.s2, ?_⟩
  have h3 : (S.subgroupOf (P ⊔ S)).index = 3 := h.relIndex_S
  rw [h3]
  omega

theorem Par2.S_maximal [Finite G] (h : Par2 L S P) {K : Subgroup G} (hSK : S ≤ K)
    (hKH : K ≤ P ⊔ S) : K = S ∨ K = P ⊔ S := by
  have h1 := Subgroup.relIndex_mul_relIndex S K (P ⊔ S) hSK hKH
  rw [h.relIndex_S] at h1
  have hd : S.relIndex K ∣ 3 := ⟨K.relIndex (P ⊔ S), h1.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h2 | h2
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hSK
  · right
    rw [h2] at h1
    have h3 : K.relIndex (P ⊔ S) = 1 := by omega
    exact le_antisymm hKH (Subgroup.relIndex_eq_one.mp h3)

theorem Par2.S_not_normal (h : Par2 L S P) : ¬ (P ⊔ S ≤ Subgroup.normalizer (S : Set G)) := by
  intro hH
  apply h.nn
  intro x hx
  have hxS : x ∈ Subgroup.normalizer (S : Set G) := hH (Subgroup.mem_sup_left hx)
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer (h.le hx)
  rw [Subgroup.mem_normalizer_iff] at hxS hxL ⊢
  intro y
  constructor
  · intro hy
    rw [Subgroup.mem_inf] at hy ⊢
    exact ⟨(hxS y).mp hy.1, (hxL y).mp hy.2⟩
  · intro hy
    rw [Subgroup.mem_inf] at hy ⊢
    exact ⟨(hxS y).mpr hy.1, (hxL y).mpr hy.2⟩

theorem Par2.isMinParabolic [Finite G] (h : Par2 L S P) : IsMinParabolicOf (P ⊔ S) (P ⊔ S) := by
  have hlt : S < P ⊔ S := by
    refine lt_of_le_of_ne le_sup_right fun he => h.S_not_normal ?_
    rw [← he]
    exact Subgroup.le_normalizer
  have hmax : IsMaxSubgroupIn (P ⊔ S) S := by
    refine ⟨hlt, fun K hSK hKH => ?_⟩
    rcases h.S_maximal hSK.le hKH with h' | h'
    · exact absurd h' (ne_of_gt hSK)
    · exact h'
  have huniq : IsUniqueMaxOver (P ⊔ S) S S := by
    unfold IsUniqueMaxOver
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨⟨hmax, le_rfl⟩, fun N hN => ?_⟩
    rcases h.S_maximal hN.2 hN.1.1.le with h' | h'
    · exact h'
    · exact absurd h' (ne_of_lt hN.1.1)
  exact (minParabolic_iff.mp ⟨h.sylow, h.S_not_normal, huniq⟩).1

theorem Par2.two_pow (h : Par2 L S P) : ∀ x ∈ P ⊔ S, ∃ k : ℕ, x ^ 2 ^ k ∈ P := by
  intro x hx
  obtain ⟨p, hp, s, hs, rfl⟩ := zb_mem_sup h.sP hx
  obtain ⟨k, hk⟩ := h.s2 ⟨s, hs⟩
  refine ⟨k, ?_⟩
  obtain ⟨q, hq, hqe⟩ := zb_mul_pow_mem (h.sP hs) hp (2 ^ k)
  have hsk : s ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [hqe, hsk, mul_one]
  exact hq

theorem Par2.H_le_normalizer (h : Par2 L S P) : P ⊔ S ≤ Subgroup.normalizer (P : Set G) :=
  sup_le Subgroup.le_normalizer h.sP

theorem Par2.charTwo [Finite G] (h : Par2 L S P) (hL : CharTwo L) : CharTwo (P ⊔ S) := by
  set H : Subgroup G := P ⊔ S with hHdef
  have hPH : P ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  set R : Subgroup G := pCoreOf 2 L with hRdef
  have hRP : R ≤ P := (h.syl.pCoreOf_le).trans h.sl
  have hRp : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hHN : H ≤ Subgroup.normalizer (R : Set G) := by
    refine sup_le ?_ ?_
    · exact (h.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
    · exact fun s hs => zb_normalizes_pCoreOf (h.sN hs)
  have hRO : R ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hRP.trans hPH) hHN hRp
  set C : Subgroup G := H ⊓ Subgroup.centralizer (R : Set G) with hCdef
  have hCp : IsPGroup 2 ↥C := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := h.two_pow c hc.1
    have hck : c ^ 2 ^ k ∈ P ⊓ Subgroup.centralizer (R : Set G) :=
      ⟨hk, Subgroup.pow_mem _ hc.2 _⟩
    have hckR : c ^ 2 ^ k ∈ R :=
      hL ⟨h.le hck.1, hck.2⟩
    obtain ⟨j, hj⟩ := hRp ⟨c ^ 2 ^ k, hckR⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul, this]
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ H, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
      intro g hg c hc
      refine ⟨H.mul_mem (H.mul_mem hg hc.1) (H.inv_mem hg), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro r hr
      have hr' : g⁻¹ * r * g ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg)) r).mp hr
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hr'
      calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * r := by group
    intro x
    constructor
    · exact key g hg x
    · intro hx
      have := key g⁻¹ (H.inv_mem hg) _ hx
      simpa [mul_assoc] using this
  have hCO : C ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hHC hCp
  intro x hx
  exact hCO ⟨hx.1, Subgroup.centralizer_le hRO hx.2⟩

theorem zb_isSolvable_of_card {Y : Type*} [Group Y] [Finite Y] {n : ℕ}
    (h : Nat.card Y = 2 ^ n * 3) : Group.IsSolvable Y := by
  let _ : Fintype Y := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := n) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h, pow_one])

theorem Par2.isSolvable [Finite G] (h : Par2 L S P) : Group.IsSolvable ↥(P ⊔ S) := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp h.s2
  refine zb_isSolvable_of_card (n := n) ?_
  rw [h.card_H, hn]
  ring

theorem zb_not_mem_of_orderOf_three {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q) {y : G} (hy : y ∈ Q)
    (h3 : orderOf y = 3) : False := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨y, hy⟩
  rw [Subgroup.orderOf_mk, h3] at hk
  have h1 : 3 ∣ 2 ^ k := hk ▸ dvd_refl 3
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow h1)
  omega

theorem zb_exists_orderOf_three [Finite G] {K : Subgroup G} (h : IsAltType K 3) :
    ∃ b ∈ K, orderOf b = 3 := by
  obtain ⟨α₃, hs, -⟩ := h
  have hdvd := Subgroup.card_dvd_of_surjective hs
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' 3 (hcard ▸ hdvd)
  exact ⟨(b₀ : G), b₀.2, by rw [Subgroup.orderOf_coe, hb₀]⟩

theorem zb_card_evenWeight_three : Nat.card ↥(evenWeight 3) = 4 := by
  have h : ∀ x : Fin 3 → ZMod 2, x ∈ evenWeight 3 ↔ x 0 + x 1 + x 2 = 0 := by
    intro x
    simp [evenWeight, Fin.sum_univ_three]
  have e : ↥(evenWeight 3) ≃ {x : Fin 3 → ZMod 2 // x 0 + x 1 + x 2 = 0} :=
    Equiv.subtypeEquivRight h
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

open CFSG in
theorem zb_commutator_double_eq_self [Finite G] (P K : Subgroup G)
    (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card P) (Nat.card (↥K))) (hsolv : Group.IsSolvable K) :
    ⁅⁅K, P⁆, P⁆ = ⁅K, P⁆ :=
  GL83.commutator_double_eq_self P K hPK hcop hsolv

theorem zb_card_ge_four [Finite G] {x : G} {W : Subgroup G} (hWp : IsPGroup 2 ↥W)
    (hWx : x ∈ Subgroup.normalizer (W : Set G)) (hW0 : W ≠ ⊥)
    (hWC : W ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) = ⊥) : 4 ≤ Nat.card ↥W := by
  by_contra hlt
  push Not at hlt
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hWp
  have hm1 : m ≤ 1 := by
    by_contra hm2
    push Not at hm2
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW0
  interval_cases m
  · have : Nat.card ↥W = 1 := by simpa using hm
    have : Subsingleton ↥W := Nat.card_eq_one_iff_unique.mp this |>.1
    exact hw1 (Subsingleton.elim _ _)
  · have h2 : Nat.card ↥W = 2 := by simpa using hm
    obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥W)).mp h2
    have hxw : x * (w : G) * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hWx (w : G)).mp w.2
    have hne : (⟨x * (w : G) * x⁻¹, hxw⟩ : ↥W) ≠ 1 := by
      intro h
      apply hw1
      apply Subtype.ext
      have h' : x * (w : G) * x⁻¹ = 1 := congrArg Subtype.val h
      have : (w : G) = 1 := by
        have := congrArg (fun z => x⁻¹ * z * x) h'
        simpa [mul_assoc] using this
      exact this
    have h1 := huniq _ hne
    have h2' := huniq w hw1
    have heq : (⟨x * (w : G) * x⁻¹, hxw⟩ : ↥W) = w := h1.trans h2'.symm
    have hcomm : x * (w : G) = (w : G) * x := by
      have h' : x * (w : G) * x⁻¹ = (w : G) := congrArg Subtype.val heq
      calc x * (w : G) = x * (w : G) * x⁻¹ * x := by group
        _ = (w : G) * x := by rw [h']
    have hwC : (w : G) ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      exact (Commute.zpow_left (show Commute x (w : G) from hcomm) k).eq
    have : (w : G) ∈ W ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G) := ⟨w.2, hwC⟩
    rw [hWC] at this
    exact hw1 (Subtype.ext (Subgroup.mem_bot.mp this))

theorem zb_commutator_card_le [Finite G] {U Kt : Subgroup G} {x : G} (hUp : IsPGroup 2 ↥U)
    (hKU : Kt ≤ Subgroup.normalizer (U : Set G)) (hUK : U ≤ Subgroup.normalizer (Kt : Set G))
    (hshort : IsShort2 Kt) (hA3 : IsAltType Kt 3) (hxK : x ∈ Kt) (hx3 : orderOf x = 3) :
    Nat.card ↥⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ≤ 4 ∧
      ⁅⁅⁅U, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆, Subgroup.zpowers x⁆ ⊓
        Subgroup.centralizer (Subgroup.zpowers x : Set G) = ⊥ := by
  classical
  set P : Subgroup G := Subgroup.zpowers x with hPdef
  have hPK : P ≤ Kt := by rw [hPdef, Subgroup.zpowers_le]; exact hxK
  have hPN : P ≤ Subgroup.normalizer (U : Set G) := hPK.trans hKU
  set W₁ : Subgroup G := ⁅U, P⁆ with hW₁def
  set W₂ : Subgroup G := ⁅W₁, P⁆ with hW₂def
  set W₃ : Subgroup G := ⁅W₂, P⁆ with hW₃def
  have hW₁U : W₁ ≤ U := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPN
  have hPW₁ : P ≤ Subgroup.normalizer (W₁ : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPN
  have hW₂W₁ : W₂ ≤ W₁ := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPW₁
  have hPW₂ : P ≤ Subgroup.normalizer (W₂ : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPW₁
  have hW₃W₂ : W₃ ≤ W₂ := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPW₂
  have hW₂U : W₂ ≤ U := hW₂W₁.trans hW₁U
  have hN_le_Kt : ⁅U, Kt⁆ ≤ Kt := by
    refine Subgroup.commutator_le.2 fun u hu k hk => ?_
    have h1 : u * k * u⁻¹ ∈ Kt := (Subgroup.mem_normalizer_iff.mp (hUK hu) k).mp hk
    have e : ⁅u, k⁆ = (u * k * u⁻¹) * k⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact Kt.mul_mem h1 (Kt.inv_mem hk)
  have hN_le_U : ⁅U, Kt⁆ ≤ U := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hKU
  have hN_norm : Kt ≤ Subgroup.normalizer ((⁅U, Kt⁆ : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hKU
  have hN_p : IsPGroup 2 ↥(⁅U, Kt⁆ : Subgroup G) := hUp.to_le hN_le_U
  have hN_O2 : ⁅U, Kt⁆ ≤ pCoreOf 2 Kt :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN_le_Kt hN_norm hN_p
  have hW₁N : W₁ ≤ ⁅U, Kt⁆ := Subgroup.commutator_mono le_rfl hPK
  have hW₂UK : W₂ ≤ blockU Kt := Subgroup.commutator_mono (hW₁N.trans hN_O2) hPK
  have hab : ∀ a b : ↥W₂, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have ha := hshort.2.2.1.1 (hW₂UK a.2)
    have hb := hshort.2.2.1.1 (hW₂UK b.2)
    exact (Subgroup.mem_centralizer_iff.mp ha.2 (b : G) hb.1).symm
  have hcopU : Nat.Coprime (Nat.card ↥P) (Nat.card ↥U) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUp
    rw [hPdef, Nat.card_zpowers, hx3, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hcopW : Nat.Coprime (Nat.card ↥P) (Nat.card ↥W₂) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hW₂U) hcopU
  obtain ⟨-, hdisj⟩ := CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp W₂ P hPW₂ hab hcopW
  have hWC : W₃ ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
    refine le_bot_iff.mp (le_trans ?_ (hdisj.le_bot))
    exact le_inf (le_inf (hW₃W₂.trans' inf_le_left) inf_le_right) inf_le_left
  refine ⟨?_, hWC⟩
  obtain ⟨α₃, -, -, β₃, -, hβ₃k, -⟩ := hA3
  have hW₃UK : W₃ ≤ blockU Kt := hW₃W₂.trans hW₂UK
  let f : ↥W₃ →* Multiplicative ↥(evenWeight 3) := β₃.comp (Subgroup.inclusion hW₃UK)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : (Subgroup.inclusion hW₃UK w) ∈ β₃.ker := hw
    rw [hβ₃k] at h1
    have h2 : (w : G) ∈ blockZ Kt := Subgroup.mem_subgroupOf.mp h1
    have h3 : (w : G) ∈ Subgroup.centralizer (Kt : Set G) := h2.2
    have h4 : (w : G) ∈ W₃ ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨w.2, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPK) h3⟩
    rw [hWC] at h4
    exact Subtype.ext (Subgroup.mem_bot.mp h4)
  calc Nat.card ↥W₃ ≤ Nat.card (Multiplicative ↥(evenWeight 3)) := Nat.card_le_card_of_injective f hf
    _ = Nat.card ↥(evenWeight 3) := Nat.card_congr Multiplicative.toAdd
    _ = 4 := zb_card_evenWeight_three

theorem zb_mem_zpowers_of_comm [Finite G] {H : Subgroup G} {n : ℕ} (hH : Nat.card ↥H = 2 ^ n * 3)
    {x₀ x₁ : G} (h0 : x₀ ∈ H) (h1 : x₁ ∈ H) (o0 : orderOf x₀ = 3) (o1 : orderOf x₁ = 3)
    (hc : x₀ * x₁ = x₁ * x₀) : x₁ ∈ Subgroup.zpowers x₀ := by
  set A : Subgroup G := Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ with hA
  have hAH : A ≤ H := sup_le (Subgroup.zpowers_le.mpr h0) (Subgroup.zpowers_le.mpr h1)
  have hx0C : x₀ ∈ Subgroup.centralizer (Subgroup.zpowers x₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (show Commute x₁ x₀ from hc.symm) k).eq
  have hz0C : Subgroup.zpowers x₀ ≤ Subgroup.centralizer (Subgroup.zpowers x₁ : Set G) :=
    Subgroup.zpowers_le.mpr hx0C
  have hn : Subgroup.zpowers x₀ ≤ Subgroup.normalizer ((Subgroup.zpowers x₁ : Subgroup G) : Set G) :=
    hz0C.trans (Subgroup.centralizer_le_normalizer _)
  have hx03 : x₀ ^ 3 = 1 := by simpa [o0] using pow_orderOf_eq_one x₀
  have hx13 : x₁ ^ 3 = 1 := by simpa [o1] using pow_orderOf_eq_one x₁
  have hcube : ∀ (y : G) (hy : y ∈ A), y ^ 3 = 1 := by
    intro y hy
    have hy' : y ∈ ((Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ : Subgroup G) : Set G) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hy'
    obtain ⟨p, hp, q, hq, rfl⟩ := hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have hcom : Commute (x₀ ^ i) (x₁ ^ j) := by
      have := Subgroup.mem_centralizer_iff.mp (hz0C hp) (x₁ ^ j) hq
      exact this.symm
    rw [hcom.mul_pow]
    have e0 : (x₀ ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx03, one_zpow]
    have e1 : (x₁ ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx13, one_zpow]
    rw [e0, e1, one_mul]
  have hAp : IsPGroup 3 ↥A := by
    intro a
    exact ⟨1, Subtype.ext (by simpa using hcube a a.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAp
  have hdvd : 3 ^ m ∣ 2 ^ n * 3 := by
    rw [← hm, ← hH]
    exact Subgroup.card_dvd_of_le hAH
  have hm1 : m ≤ 1 := by
    have hcop : Nat.Coprime (3 ^ m) (2 ^ n) :=
      Nat.Coprime.pow _ _ (by norm_num)
    have h3 : 3 ^ m ∣ 3 := hcop.dvd_of_dvd_mul_left hdvd
    have h4 : 3 ^ m ∣ 3 ^ 1 := by simpa using h3
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h4
  have hz0A : Subgroup.zpowers x₀ ≤ A := le_sup_left
  have hz0c : Nat.card ↥(Subgroup.zpowers x₀) = 3 := by rw [Nat.card_zpowers, o0]
  have hle : 3 ≤ Nat.card ↥A := hz0c ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hz0A)
  have hAc : Nat.card ↥A = 3 := by
    interval_cases m
    · omega
    · simpa using hm
  have heq : Subgroup.zpowers x₀ = A :=
    Subgroup.eq_of_le_of_card_ge hz0A (by rw [hAc, hz0c])
  rw [heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x₁)

@[expose] def ParBig (L P : Subgroup G) : Prop :=
  ∀ x ∈ P, orderOf x = 3 → ¬ ⁅pCoreOf 2 P, Subgroup.zpowers x⁆ ≤ pCoreOf 2 L

theorem Par2.not_C126Third [Finite G] (h : Par2 L S P) (hL : CharTwo L) (hbig : ParBig L P) :
    ¬ C126Third (P ⊔ S) S := by
  rintro ⟨r, K, hr, hK, hcomm, hres, -, -⟩
  have hsolv := h.isSolvable
  have hA3 : ∀ i, IsAltType (K i) 3 := fun i =>
    CFSG.Quasithin.C1Pack.isAltType_three_of_isBlock2_of_solvable (hK i).1.1 hsolv
  have hshort : ∀ i, IsShort2 (K i) := fun i => (hK i).1.1.1
  have hTR : twoResidual (P ⊔ S) ≤ P :=
    twoResidual_le_of_isTwoQuotient le_sup_left h.H_le_normalizer h.two_pow
  have hKP : ∀ i, K i ≤ P := fun i =>
    calc K i ≤ ⨆ j, K j := le_iSup K i
      _ = twoResidual (P ⊔ S) := hres.symm
      _ ≤ P := hTR
  have hx3 : ∀ i, ∃ y ∈ K i, orderOf y = 3 := fun i => zb_exists_orderOf_three (hA3 i)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.s2
  have hcardH : Nat.card ↥(P ⊔ S) = 2 ^ n * 3 := by rw [h.card_H, hn]; ring
  have hr1 : r = 1 := by
    by_contra hne
    have hr2 : 2 ≤ r := by omega
    let i0 : Fin r := ⟨0, by omega⟩
    let j0 : Fin r := ⟨1, by omega⟩
    have hij : i0 ≠ j0 := by simp [i0, j0, Fin.ext_iff]
    obtain ⟨x₀, hx₀K, hx₀3⟩ := hx3 i0
    obtain ⟨x₁, hx₁K, hx₁3⟩ := hx3 j0
    have hcomm0 := hcomm i0 j0 hij
    have hcom : x₀ * x₁ = x₁ * x₀ := by
      have h1 : ⁅x₀, x₁⁆ ∈ ⁅K i0, K j0⁆ := Subgroup.commutator_mem_commutator hx₀K hx₁K
      rw [hcomm0] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
    have hx₁eq : x₁ ∈ K i0 := by
      have h1 : x₁ ∈ Subgroup.zpowers x₀ :=
        zb_mem_zpowers_of_comm hcardH (Subgroup.mem_sup_left (hKP i0 hx₀K))
          (Subgroup.mem_sup_left (hKP j0 hx₁K)) hx₀3 hx₁3 hcom
      exact (Subgroup.zpowers_le.mpr hx₀K) h1
    have hx₁C : x₁ ∈ Subgroup.centralizer (pCoreOf 2 (K j0) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hkK : k ∈ K j0 := CFSG.LieType.BorelTits.pCoreOf_le 2 (K j0) hk
      have h1 : ⁅x₁, k⁆ ∈ ⁅K i0, K j0⁆ := Subgroup.commutator_mem_commutator hx₁eq hkK
      rw [hcomm0] at h1
      have := commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      exact this.symm
    have hx₁O : x₁ ∈ pCoreOf 2 (K j0) := (hshort j0).2.1 ⟨hx₁K, hx₁C⟩
    exact zb_not_mem_of_orderOf_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K j0)) hx₁O hx₁3
  subst hr1
  have hK0 : twoResidual (P ⊔ S) = K 0 := by
    rw [hres]
    exact iSup_unique K
  have hKN : P ⊔ S ≤ Subgroup.normalizer (K 0 : Set G) := by
    rw [← hK0]
    exact le_normalizer_twoResidual _
  obtain ⟨x, hxK, hx3'⟩ := hx3 0
  have hxP : x ∈ P := hKP 0 hxK
  set X : Subgroup G := pCoreOf 2 P with hXdef
  have hXp : IsPGroup 2 ↥X := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hXP : X ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hHX : P ⊔ S ≤ Subgroup.normalizer (X : Set G) := by
    refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P) ?_
    exact fun s hs => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 P (h.sP hs)
  have hKU : K 0 ≤ Subgroup.normalizer (X : Set G) := (hKP 0).trans (le_sup_left.trans hHX)
  have hUK : X ≤ Subgroup.normalizer (K 0 : Set G) := hXP.trans (le_sup_left.trans hKN)
  obtain ⟨hcard, hdisj⟩ := zb_commutator_card_le hXp hKU hUK (hshort 0) (hA3 0) hxK hx3'
  set Px : Subgroup G := Subgroup.zpowers x with hPx
  have hPxK : Px ≤ K 0 := by rw [hPx, Subgroup.zpowers_le]; exact hxK
  have hPxN : Px ≤ Subgroup.normalizer (X : Set G) := hPxK.trans hKU
  have hcop : Nat.Coprime (Nat.card ↥Px) (Nat.card ↥X) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
    rw [hPx, Nat.card_zpowers, hx3', hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hXsolv : Group.IsSolvable ↥X := by
    have hnil : Group.IsNilpotent ↥X := hXp.isNilpotent
    infer_instance
  have e1 : ⁅⁅X, Px⁆, Px⁆ = ⁅X, Px⁆ := zb_commutator_double_eq_self Px X hPxN hcop hXsolv
  have hW : ⁅⁅⁅X, Px⁆, Px⁆, Px⁆ = ⁅X, Px⁆ := by rw [e1, e1]
  rw [hW] at hcard hdisj
  set QL : Subgroup G := pCoreOf 2 L with hQLdef
  have hQLp : IsPGroup 2 ↥QL := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hQLP : QL ≤ P := (h.syl.pCoreOf_le).trans h.sl
  have hPQL : P ≤ Subgroup.normalizer (QL : Set G) :=
    h.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  have hQLX : QL ≤ X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQLP hPQL hQLp
  have hPxQL : Px ≤ Subgroup.normalizer (QL : Set G) := (hPxK.trans (hKP 0)).trans hPQL
  set Y : Subgroup G := ⁅QL, Px⁆ with hYdef
  have hYQL : Y ≤ QL := CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hPxQL
  have hYX : Y ≤ ⁅X, Px⁆ := Subgroup.commutator_mono hQLX le_rfl
  have hYp : IsPGroup 2 ↥Y := hQLp.to_le hYQL
  have hxL : x ∈ L := h.le hxP
  have hY0 : Y ≠ ⊥ := by
    intro hY
    have hxC : x ∈ Subgroup.centralizer (QL : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : ⁅q, x⁆ ∈ Y := Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers x)
      rw [hY] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
    exact zb_not_mem_of_orderOf_three hQLp (hL ⟨hxL, hxC⟩) hx3'
  have hYx : x ∈ Subgroup.normalizer (Y : Set G) :=
    CFSG.QuasithinUnique.Setup.Layer.le_normalizer_commutator hPxQL (Subgroup.mem_zpowers x)
  have hYC : Y ⊓ Subgroup.centralizer (Px : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hYX).trans hdisj.le)
  have hY4 : 4 ≤ Nat.card ↥Y := zb_card_ge_four hYp hYx hY0 hYC
  have hYeq : Y = ⁅X, Px⁆ := Subgroup.eq_of_le_of_card_ge hYX (hcard.trans hY4)
  apply hbig x hxP hx3'
  rw [← hXdef, ← hPx, ← hYeq]
  exact hYQL

theorem zb_mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) : x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  constructor
  · intro hy
    rw [Subgroup.mem_inf] at hy ⊢
    exact ⟨(hA y).mp hy.1, (hB y).mp hy.2⟩
  · intro hy
    rw [Subgroup.mem_inf] at hy ⊢
    exact ⟨(hA y).mpr hy.1, (hB y).mpr hy.2⟩

theorem zb_isMax_conj {L P : Subgroup G} {s : G} (hs : s ∈ Subgroup.normalizer (L : Set G))
    (h : IsMaxSubgroupIn L P) : IsMaxSubgroupIn L (B6.conjSub s P) := by
  have hL : B6.conjSub s L = L := B6.conjSub_eq_self hs
  refine ⟨?_, fun K hK hKL => ?_⟩
  · have := (B6.conjSub s).lt_iff_lt.mpr h.1
    rwa [hL] at this
  · have h1 : P < B6.conjSub s⁻¹ K := by
      have := (B6.conjSub s⁻¹).lt_iff_lt.mpr hK
      rwa [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at this
    have h2 : B6.conjSub s⁻¹ K ≤ L := by
      have := (B6.conjSub s⁻¹).le_iff_le.mpr hKL
      rwa [B6.conjSub_eq_self (inv_mem hs)] at this
    have h3 := h.2 _ h1 h2
    have := congrArg (B6.conjSub s) h3
    rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one, hL] at this

theorem zb_normalizes_oPrime {p : ℕ} {P : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g ∈ Subgroup.normalizer ((oPrimeResidualOf p P : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (P : Set G), ∀ x ∈ oPrimeResidualOf p P,
      g * x * g⁻¹ ∈ oPrimeResidualOf p P := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
      obtain ⟨k, hk⟩ := hx.2
      refine ⟨k, ?_⟩
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      simpa [MulAut.conj_apply, hk] using this
    | one => simp
    | mul x y _ _ ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ ih
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem zb_oPrime_le {p : ℕ} {P : Subgroup G} : oPrimeResidualOf p P ≤ P :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem zb_oPrime_sup_eq [Finite G] {B P : Subgroup G} (hBP : B ≤ P) (hcard : Nat.card ↥P = 3 * Nat.card ↥B)
    (hB2 : IsPGroup 2 ↥B) : oPrimeResidualOf 3 P ⊔ B = P := by
  have h3 : 3 ∣ Nat.card ↥P := ⟨Nat.card ↥B, hcard⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hy3 : orderOf (y₀ : G) = 3 := by rw [Subgroup.orderOf_coe, hy₀]
  have hyX : (y₀ : G) ∈ oPrimeResidualOf 3 P :=
    Subgroup.subset_closure ⟨y₀.2, 1, by simpa using hy3⟩
  have hXP : oPrimeResidualOf 3 P ⊔ B ≤ P := sup_le zb_oPrime_le hBP
  have hrel : B.relIndex P = 3 := by
    have h1 := Subgroup.relIndex_mul_card B P
    rw [inf_eq_left.mpr hBP] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    have h2 : B.relIndex P * Nat.card ↥B = 3 * Nat.card ↥B := by rw [h1, hcard]
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have h1 := Subgroup.relIndex_mul_relIndex B (oPrimeResidualOf 3 P ⊔ B) P le_sup_right hXP
  rw [hrel] at h1
  have hd : B.relIndex (oPrimeResidualOf 3 P ⊔ B) ∣ 3 := ⟨_, h1.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h2 | h2
  · exfalso
    have hle : oPrimeResidualOf 3 P ⊔ B ≤ B := Subgroup.relIndex_eq_one.mp h2
    exact zb_not_mem_of_orderOf_three hB2 (hle (Subgroup.mem_sup_left hyX)) hy3
  · rw [h2] at h1
    have h4 : (oPrimeResidualOf 3 P ⊔ B).relIndex P = 1 := by omega
    exact le_antisymm hXP (Subgroup.relIndex_eq_one.mp h4)

theorem zb_omega_le_center (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hy => hy.1

theorem zb_omega_sq (T : Subgroup G) : ∀ z ∈ quasithinOmegaOneCenter T, z ^ 2 = 1 := by
  intro z hz
  induction hz using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxT : x ∈ T := (zb_omega_le_center T hx).1
    have hyC : y ∈ Subgroup.centralizer (T : Set G) := (zb_omega_le_center T hy).2
    have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hyC x hxT).symm
    calc (x * y) ^ 2 = (x * y) * (x * y) := pow_two _
      _ = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by simp only [mul_assoc]
      _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x _ ih => rw [inv_pow, ih, inv_one]

end CFSG.Quasithin
