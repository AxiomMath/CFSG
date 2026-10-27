module

public import CFSG.Quasithin.Vol2.KGFactJ4M3Core
public import CFSG.Quasithin.Vol2.KGFactC31E16
public import CFSG.Quasithin.Vol2.KGFactC31E8
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.Ordering
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMaxBase

public section

namespace CFSG.Quasithin.J4M3

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.F134.J4E9
  CFSG.Quasithin.KGC31 CFSG.Quasithin.Special2 CFSG.Quasithin.J4Fam CFSG.Quasithin.J4Rad
open CFSG.Open (pCoreOf IsSubnormal)
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped commutatorElement

theorem eq_bot_or_eq_top_of_subnormal {S : Type*} [Group S] [IsSimpleGroup S] {H : Subgroup S}
    (h : IsSubnormal H ⊤) : H = ⊥ ∨ H = ⊤ := by
  by_cases htop : H = ⊤
  · exact Or.inr htop
  obtain ⟨P, hPlt, hPn, hHP⟩ := A3.subnormal_exists_normal_of_lt h (lt_top_iff_ne_top.mpr htop)
  have hP : P.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hPn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with hb | ht
  · exact Or.inl (le_bot_iff.mp (hb ▸ hHP))
  · exact absurd ht hPlt.ne

theorem commutator_top_statedSL3 :
    ⁅(⊤ : Subgroup ↥(StatedSL 3 (ZMod 2))), (⊤ : Subgroup ↥(StatedSL 3 (ZMod 2)))⁆ = ⊤ := by
  have := E8.isSimpleGroup_statedSL3
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ⁅(⊤ : Subgroup ↥(StatedSL 3 (ZMod 2))), (⊤ : Subgroup ↥(StatedSL 3 (ZMod 2)))⁆ with h | h
  · exfalso
    have hcomm : ∀ a b : ↥(StatedSL 3 (ZMod 2)), a * b = b * a := by
      intro a b
      have h1 : ⁅a, b⁆ ∈
          ⁅(⊤ : Subgroup ↥(StatedSL 3 (ZMod 2))), (⊤ : Subgroup ↥(StatedSL 3 (ZMod 2)))⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(StatedSL 3 (ZMod 2))) 2
      (by rw [E8.card_statedSL3]; norm_num)
    have hn : (Subgroup.zpowers g).Normal :=
      ⟨fun x hx y => by rw [hcomm y x, mul_inv_cancel_right]; exact hx⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h1 | h1
    · rw [Subgroup.zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at hg
      norm_num at hg
    · have h2 := Nat.card_zpowers g
      rw [h1, Subgroup.card_top, hg, E8.card_statedSL3] at h2
      norm_num at h2
  · exact h

noncomputable abbrev KL : Subgroup J := M3 ⊓ fixingSubgroup J X5

theorem KL_le_M3 : KL ≤ M3 := inf_le_left

theorem M3_le_normalizer_KL : M3 ≤ Subgroup.normalizer (KL : Set J) := by
  intro m hm
  refine CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun k hk => Subgroup.mem_inf.mpr
    ⟨M3.mul_mem (M3.mul_mem hm (Subgroup.mem_inf.mp hk).1) (M3.inv_mem hm), ?_⟩
  rw [mem_fixingSubgroup_iff]
  intro w hw
  have h1 := (mem_fixingSubgroup_iff J).mp (Subgroup.mem_inf.mp hk).2 _
    (X5_smul_mem (M3.inv_mem hm) hw)
  rw [mul_smul, mul_smul, h1, smul_inv_smul]

theorem K3_le_KL : K3 ≤ KL := fun _ hk =>
  Subgroup.mem_inf.mpr ⟨D_le_M3 (Subgroup.mem_inf.mp hk).1, (Subgroup.mem_inf.mp hk).2⟩

theorem KL_inf_centralizer_eq_K3 : KL ⊓ Subgroup.centralizer (V0 : Set J) = K3 := by
  refine le_antisymm (fun k hk => ?_) (le_inf K3_le_KL inf_le_left)
  obtain ⟨hkL, hkC⟩ := Subgroup.mem_inf.mp hk
  exact Subgroup.mem_inf.mpr ⟨hkC, (Subgroup.mem_inf.mp hkL).2⟩

section Basis


theorem M3_le_eNorm : M3 ≤ eNorm hv0 := by
  show M3 ≤ Subgroup.normalizer (eSub hv0 : Set J)
  rw [eSub_v0]

theorem KL_le_eNorm : KL ≤ eNorm hv0 := KL_le_M3.trans M3_le_eNorm

end Basis

local notation "eM3" => E16.eNHom hv0 M3_le_eNorm

section Comm


theorem eM3_eq_one_iff (m : ↥M3) : eM3 m = 1 ↔ (m : J) ∈ Subgroup.centralizer (V0 : Set J) := by
  rw [E16.eNHom_eq_one_iff, eSub_v0]


theorem commutatorElement_mul_V0 {a b c d : J} (ha : a ∈ Qg) (hb : b ∈ V0) (hc : c ∈ Qg)
    (hd : d ∈ V0) : ⁅a * b, c * d⁆ = ⁅a, c⁆ := by
  have hb' : b ∈ eSub hv0 := by rw [eSub_v0]; exact hb
  have hd' : d ∈ eSub hv0 := by rw [eSub_v0]; exact hd
  have h1 : ⁅b, c * d⁆ = 1 :=
    qTable.commutatorElement_eq_one_of_mem_left hb' (Qg.mul_mem hc (V0_le_Q hd))
  have h2 : ⁅a, d⁆ = 1 := qTable.commutatorElement_eq_one_of_mem_right hd' ha
  rw [commutatorElement_mul_left_of_commute (by rw [h1, one_mul, mul_one]), h1, one_mul,
    commutatorElement_mul_right_of_commute (by rw [h2, one_mul, mul_one]), h2, mul_one]

end Comm

section Core


theorem rho3_eq_one_iff (m : ↥M3) : rho3 j4Facts m = 1 ↔ (m : J) ∈ KL := by
  refine ⟨fun h => Subgroup.mem_inf.mpr ⟨m.2, (mem_fixingSubgroup_iff J).mpr fun w hw => ?_⟩,
    fun h => rho3_eq_one_of_fix ((mem_fixingSubgroup_iff J).mp (Subgroup.mem_inf.mp h).2)⟩
  have hw' : w ∈ OrbM3 := by
    show w ∈ MulAction.orbit ↥M3 (basePt : J ⧸ Hj)
    rw [orbit_M3_eq]
    exact hw
  have h1 := rho3_apply j4Facts m ⟨w, hw'⟩
  rw [h, Equiv.Perm.one_apply] at h1
  exact (congrArg Subtype.val ((eOrb j4Facts).injective h1)).symm


theorem xM_mem_KL : xM ∈ KL := Subgroup.mem_inf.mpr ⟨xM_mem_normalizer, xM_mem_fix⟩

theorem Q_le_KL : Qg ≤ KL := K3_eq_Q ▸ K3_le_KL

theorem Q_le_M3 : Qg ≤ M3 := Q_le_KL.trans KL_le_M3

theorem pJ_mem_Q {i : ℕ} (hi : i < 12) : pJ i ∈ Qg :=
  K3_eq_Q ▸ Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_iff.mpr fun v hv => (pJ_centralizes hi v hv).symm, pJ_mem_fix hi⟩

theorem pCoreOf_le_KL : pCoreOf 2 M3 ≤ KL :=
  pCoreOf_M3_eq ▸ Q_le_KL

theorem KL_inf_centralizer :
    KL ⊓ Subgroup.centralizer (V0 : Set J) = pCoreOf 2 M3 := by
  rw [KL_inf_centralizer_eq_K3, K3_eq_Q, pCoreOf_M3_eq]

theorem card_range_rho3 : Nat.card (rho3 j4Facts).range = 120 := by
  have hcDm : (⟨cJ, cJ_mem_M3⟩ : ↥M3) ∈ Dm := Subgroup.mem_subgroupOf.mpr cJ_mem_centralizer
  have h120 := card_eq_120_of_odd (sixty_dvd_card_rho3 j4Facts)
    ⟨_, ⟨⟨⟨cJ, cJ_mem_M3⟩, hcDm⟩, rfl⟩, sign_rho3_cJ⟩
  have hle : ((rho3 j4Facts).comp Dm.subtype).range ≤ (rho3 j4Facts).range := by
    rintro _ ⟨d, rfl⟩
    exact ⟨d, rfl⟩
  have h1 := Subgroup.card_le_of_le hle
  have h2 := Subgroup.card_le_card_group (rho3 j4Facts).range
  rw [Nat.card_perm, Nat.card_fin] at h2
  rw [h120] at h1
  have h5 : Nat.factorial 5 = 120 := rfl
  omega

theorem card_KL : Nat.card ↥KL = 2 ^ 15 * 168 := by
  have hker : (rho3 j4Facts).ker = KL.subgroupOf M3 := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, rho3_eq_one_iff]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (rho3 j4Facts).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, card_range_rho3,
    card_M3 j4Facts, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe KL_le_M3).toEquiv] at h
  rw [show (2 : ℕ) ^ 15 * 168 = 5505024 by norm_num]
  omega

theorem surjective_eNHom_KL : Function.Surjective (E16.eNHom hv0 KL_le_eNorm) := by
  have hker : (E16.eNHom hv0 KL_le_eNorm).ker = Qg.subgroupOf KL := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, E16.eNHom_eq_one_iff, eSub_v0, ← K3_eq_Q,
      ← KL_inf_centralizer_eq_K3]
    exact ⟨fun h => Subgroup.mem_inf.mpr ⟨x.2, h⟩, fun h => (Subgroup.mem_inf.mp h).2⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (E16.eNHom hv0 KL_le_eNorm).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q_le_KL).toEquiv, card_Q, card_KL] at h1
  have h2 : Nat.card (E16.eNHom hv0 KL_le_eNorm).range = 168 := by
    rw [show (2 : ℕ) ^ 15 * 168 = 168 * 2 ^ 15 by norm_num] at h1
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [h2, E8.card_statedSL3]

theorem eM3_surjective : Function.Surjective eM3 := by
  intro s
  obtain ⟨k, hk⟩ := surjective_eNHom_KL s
  exact ⟨⟨k, KL_le_M3 k.2⟩, Subtype.ext (Units.ext (by rw [← hk]; rfl))⟩

theorem Q_le_of_normal {Y : Subgroup J} (hYM : Y ≤ M3)
    (hY : M3 ≤ Subgroup.normalizer (Y : Set J)) {y : J} (hy : y ∈ Y) (hyx : y⁻¹ * xM ∈ Qg) :
    Qg ≤ Y := by
  obtain ⟨q₀, hq₀, hx⟩ : ∃ q₀ ∈ Qg, xM = y * q₀ := ⟨y⁻¹ * xM, hyx, by group⟩
  have hdec : ∀ i : Fin 12, ∃ a ∈ Y, ∃ b ∈ V0, qF i = a * b := by
    intro i
    have hp : pJ i ∈ Qg := pJ_mem_Q i.2
    refine ⟨⁅pJ i, y⁆, ?_, y * ⁅pJ i, q₀⁆ * y⁻¹, ?_, ?_⟩
    · rw [commutatorElement_def]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY (Q_le_M3 hp)) y).mp hy) (Y.inv_mem hy)
    · have hc : ⁅pJ i, q₀⁆ ∈ V0 := by
        rw [← eSub_v0]
        exact qTable.comm_mem hp q₀ hq₀
      exact (Subgroup.mem_normalizer_iff.mp (hYM hy) _).mp hc
    · show qJ i = _
      rw [qJ, hx, commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
  choose a ha b hb hab using hdec
  have haQ : ∀ i, a i ∈ Qg := fun i => by
    have e : a i = qF i * (b i)⁻¹ := by rw [hab i]; group
    rw [e]
    exact Qg.mul_mem (mem_tabGroup i) (Qg.inv_mem (V0_le_Q (hb i)))
  have hcomm : ∀ i j, ⁅qF i, qF j⁆ ∈ Y := by
    intro i j
    rw [hab i, hab j, commutatorElement_mul_V0 (haQ i) (hb i) (haQ j) (hb j),
      commutatorElement_def]
    exact Y.mul_mem (Y.mul_mem (Y.mul_mem (ha i) (ha j)) (Y.inv_mem (ha i))) (Y.inv_mem (ha j))
  have hV0 : eSub hv0 ≤ Y := by
    rw [eSub_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    obtain ⟨i, j, e⟩ := v0_comm k
    rw [e]
    exact hcomm i j
  have hV0' : V0 ≤ Y := eSub_v0 ▸ hV0
  refine sup_le ((Subgroup.closure_le _).mpr ?_) hV0
  rintro _ ⟨i, rfl⟩
  rw [hab i]
  exact Y.mul_mem (ha i) (hV0' (hb i))

theorem exists_inv_mul_mem_Q {L : Subgroup J} (hLK : L ≤ KL)
    (htop : (L.subgroupOf M3).map eM3 = ⊤) {k : J} (hk : k ∈ KL) : ∃ l ∈ L, l⁻¹ * k ∈ Qg := by
  have hkM : k ∈ M3 := (Subgroup.mem_inf.mp hk).1
  obtain ⟨l, hl, hle⟩ : eM3 ⟨k, hkM⟩ ∈ (L.subgroupOf M3).map eM3 := htop ▸ Subgroup.mem_top _
  refine ⟨(l : J), Subgroup.mem_subgroupOf.mp hl, ?_⟩
  have h1 : eM3 (l⁻¹ * ⟨k, hkM⟩) = 1 := by rw [map_mul, map_inv, hle, inv_mul_cancel]
  rw [eM3_eq_one_iff] at h1
  have hmem : (l : J)⁻¹ * k ∈ KL ⊓ Subgroup.centralizer (V0 : Set J) :=
    Subgroup.mem_inf.mpr ⟨KL.mul_mem (KL.inv_mem (hLK (Subgroup.mem_subgroupOf.mp hl))) hk, h1⟩
  rw [KL_inf_centralizer_eq_K3, K3_eq_Q] at hmem
  exact hmem

theorem conjClosure_eq_KL {L : Subgroup J} (hLK : L ≤ KL)
    (htop : (L.subgroupOf M3).map eM3 = ⊤) : conjClosure L M3 = KL := by
  have hYK : conjClosure L M3 ≤ KL := conjClosure_le fun m hm l hl =>
    (Subgroup.mem_normalizer_iff.mp (M3_le_normalizer_KL hm) l).mp (hLK hl)
  have hLY : L ≤ conjClosure L M3 := le_conjClosure L M3
  obtain ⟨l, hl, hlx⟩ := exists_inv_mul_mem_Q hLK htop xM_mem_KL
  have hQY : Qg ≤ conjClosure L M3 :=
    Q_le_of_normal (hYK.trans KL_le_M3) (le_normalizer_conjClosure L M3) (hLY hl) hlx
  refine le_antisymm hYK fun k hk => ?_
  obtain ⟨l', hl', hl'k⟩ := exists_inv_mul_mem_Q hLK htop hk
  have e : k = l' * (l'⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hLY hl') (hQY hl'k)

theorem le_KL_of_map_eq_top {L : Subgroup J} (hL : L ∈ cComp M3)
    (htop : (L.subgroupOf M3).map eM3 = ⊤) : L ≤ KL := by
  have hLM : L ≤ M3 := le_of_mem_cComp hL
  have hNL : ((L ⊓ KL).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro l hl
    have h1 : l ∈ Subgroup.normalizer (L : Set J) := Subgroup.le_normalizer hl
    have h2 : l ∈ Subgroup.normalizer (KL : Set J) := M3_le_normalizer_KL (hLM hl)
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro x
    constructor
    · intro hx
      exact Subgroup.mem_inf.mpr
        ⟨(h1 x).mp (Subgroup.mem_inf.mp hx).1, (h2 x).mp (Subgroup.mem_inf.mp hx).2⟩
    · intro hx
      exact Subgroup.mem_inf.mpr
        ⟨(h1 x).mpr (Subgroup.mem_inf.mp hx).1, (h2 x).mpr (Subgroup.mem_inf.mp hx).2⟩
  have hKsub : IsSubnormal (perfectCore (L ⊓ KL)) M3 :=
    A3.subnormal_trans (A3.subnormal_perfectCore (A3.subnormal_of_normal inf_le_left hNL))
      (subnormal_of_mem_cComp hL)
  have hKL : perfectCore (L ⊓ KL) ≤ L := (perfectCore_le _).trans inf_le_left
  by_cases hKeq : perfectCore (L ⊓ KL) = L
  · rw [← hKeq]
    exact (perfectCore_le _).trans inf_le_right
  by_cases hKbot : perfectCore (L ⊓ KL) = ⊥
  swap
  · exact absurd hKsub (not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hKL hKeq) hKbot
      (perfectCore_perfect _))
  exfalso
  have hNM : L ⊓ KL ≤ M3 := inf_le_left.trans hLM
  have hN'n : (((L ⊓ KL).subgroupOf M3).map eM3).Normal := by
    constructor
    intro s hs t
    obtain ⟨l, hl, rfl⟩ : t ∈ (L.subgroupOf M3).map eM3 := htop ▸ Subgroup.mem_top t
    obtain ⟨n, hn, rfl⟩ := hs
    refine ⟨l * n * l⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hlL : (l : J) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hnN : (n : J) ∈ L ⊓ KL := Subgroup.mem_subgroupOf.mp hn
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hNL hlL) n).mp hnN
    simpa using this
  have := E8.isSimpleGroup_statedSL3
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((L ⊓ KL).subgroupOf M3).map eM3) with hb | ht
  ·
    have hNQ : L ⊓ KL ≤ Qg := by
      intro n hn
      have h1 : eM3 ⟨n, hNM hn⟩ ∈ ((L ⊓ KL).subgroupOf M3).map eM3 :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn)
      rw [hb, Subgroup.mem_bot, eM3_eq_one_iff] at h1
      have hmem : n ∈ KL ⊓ Subgroup.centralizer (V0 : Set J) :=
        Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hn).2, h1⟩
      rwa [KL_inf_centralizer_eq_K3, K3_eq_Q] at hmem
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥(StatedSL 3 (ZMod 2))) 7
      (by rw [E8.card_statedSL3]; norm_num)
    obtain ⟨l, hl, hls⟩ : s ∈ (L.subgroupOf M3).map eM3 := htop ▸ Subgroup.mem_top s
    have h120 : rho3 j4Facts (l ^ 120) = 1 := by
      have h := pow_card_eq_one' (G := Equiv.Perm (Fin 5)) (x := rho3 j4Facts l)
      rw [Nat.card_perm, Nat.card_fin] at h
      rw [map_pow]
      exact h
    rw [rho3_eq_one_iff] at h120
    have hlN : ((l ^ 120 : ↥M3) : J) ∈ L ⊓ KL :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp (Subgroup.pow_mem _ hl 120), h120⟩
    have hpow : (l ^ 120) ^ (2 ^ 15) = 1 := by
      have h := pow_card_eq_one' (G := ↥Qg) (x := ⟨_, hNQ hlN⟩)
      rw [card_Q] at h
      apply Subtype.ext
      simpa using congrArg Subtype.val h
    have hs1 : s ^ (120 * 2 ^ 15) = 1 := by
      rw [← hls, ← map_pow, pow_mul, hpow, map_one]
    have h7 := orderOf_dvd_of_pow_eq_one hs1
    rw [hs] at h7
    norm_num at h7
  ·
    have h1 : (perfectCore ((L ⊓ KL).subgroupOf M3)).map eM3 = ⊤ := by
      rw [map_perfectCore, ht, perfectCore_eq_self_of_perfect commutator_top_statedSL3]
    have h2 : perfectCore ((L ⊓ KL).subgroupOf M3) = ⊥ := by
      have h3 := map_perfectCore M3.subtype ((L ⊓ KL).subgroupOf M3)
      rw [Subgroup.map_subgroupOf_eq_of_le hNM, hKbot] at h3
      exact (Subgroup.map_eq_bot_iff_of_injective _ M3.subtype_injective).mp h3
    rw [h2, Subgroup.map_bot] at h1
    exact bot_ne_top h1

theorem cComp_M3 : ∀ L ∈ cComp M3, conjClosure L M3 = KL ∨
    L ≤ Subgroup.centralizer (V0 : Set J) := by
  intro L hL
  have hLM : L ≤ M3 := le_of_mem_cComp hL
  have hsub : IsSubnormal ((L.subgroupOf M3).map eM3) ⊤ := by
    have h1 : IsSubnormal ((L.subgroupOf M3).map eM3) ((M3.subgroupOf M3).map eM3) :=
      A3.subnormal_map eM3 (A3.subnormal_comap M3.subtype (subnormal_of_mem_cComp hL))
    rwa [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ eM3_surjective] at h1
  have := E8.isSimpleGroup_statedSL3
  rcases eq_bot_or_eq_top_of_subnormal hsub with hb | ht
  · right
    intro l hl
    have h1 : eM3 ⟨l, hLM hl⟩ ∈ (L.subgroupOf M3).map eM3 :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
    rw [hb, Subgroup.mem_bot, eM3_eq_one_iff] at h1
    exact h1
  · left
    exact conjClosure_eq_KL (le_KL_of_map_eq_top hL ht) ht

end Core

end CFSG.Quasithin.J4M3
