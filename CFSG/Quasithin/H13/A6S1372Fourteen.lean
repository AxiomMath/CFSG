module

public import CFSG.Quasithin.H13.A6S1372Mod
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.H13.LocDblCComp

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.B19 CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6Fourteen

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem exists_apply_eq_mul {t : MulAut V} {w : V} (htw : IsTransvectionWith t w) (ht1 : t ≠ 1) :
    ∃ v : V, t v = v * w := by
  by_contra h
  push Not at h
  apply ht1
  refine MulEquiv.ext fun v => ?_
  rcases htw.2 v with h1 | h1
  · exact h1
  · exact absurd h1 (h v)

theorem eq_of_mem_GOf (hV : ∀ v : V, v ^ 2 = 1) {X Φ P : Subgroup (MulAut V)}
    (hS : Setting X Φ) {t t' : MulAut V} (ht : t ∈ tvSet X Φ) (hP : IsPGroup 2 P)
    (htP : t ∈ P) (ht'P : t' ∈ P) (ht'G : t' ∈ GOf Φ t) (ht'1 : t' ≠ 1) : t' = t := by
  set Q₀ := P ⊓ GOf Φ t with hQ₀
  have hsq := hS.sq_tv hV ht
  have hord : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two]; exact hsq
    · obtain ⟨-, ⟨ht1, -⟩, -⟩ := ht
      exact ht1
  have hcardt : Nat.card (Subgroup.zpowers t) = 2 := by rw [Nat.card_zpowers, hord]
  have htQ : Subgroup.zpowers t ≤ Q₀ :=
    Subgroup.zpowers_le.2 ⟨htP, mem_GOf⟩
  have hdvd : Nat.card Q₀ ∣ 6 := by
    rw [← hS.card_GOf hV ht]
    exact Subgroup.card_dvd_of_le inf_le_right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hP.to_le (inf_le_left : Q₀ ≤ P))
  have hk1 : k ≤ 1 := by
    by_contra hk1
    push Not at hk1
    have h4 : 4 ∣ 6 := by
      rw [hk] at hdvd
      exact (pow_dvd_pow 2 hk1).trans hdvd
    norm_num at h4
  have hle : Nat.card Q₀ ≤ Nat.card (Subgroup.zpowers t) := by
    rw [hk, hcardt]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := by norm_num
  have heq := Subgroup.eq_of_le_of_card_ge htQ hle
  have ht'Q : t' ∈ Subgroup.zpowers t := heq ▸ (⟨ht'P, ht'G⟩ : t' ∈ Q₀)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht'Q
  rw [← zpow_mod_orderOf, hord] at ht'1 ⊢
  have hn : n % (2 : ℕ) = 0 ∨ n % (2 : ℕ) = 1 := by omega
  rcases hn with hn | hn
  · rw [hn, zpow_zero] at ht'1
    exact absurd rfl ht'1
  · rw [hn, zpow_one]

theorem comm_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {X Φ B P : Subgroup (MulAut V)}
    {W : Subgroup V} (hS : Setting X Φ) (hB : IsFFStarMin X B) (hBP : B ≤ P) (hP : IsPGroup 2 P)
    (hBW : commV B ≤ W) {c : MulAut V} (hcX : c ∈ X) (hcP : ∀ p ∈ P, c * p * c⁻¹ ∈ P)
    (hcP' : ∀ p ∈ P, c⁻¹ * p * c ∈ P) (hc3 : c ^ 3 = 1) (hcW : ∀ w ∈ W, c w ∈ W)
    (hfix : ∀ w ∈ W, c w = w → w = 1) : ⁅Φ, B⁆ = ⊥ := by
  by_contra hne
  obtain ⟨t, ht, hBt⟩ := hS.exists_tv_of_isFFStarMin hV hB hne
  obtain ⟨x, w, h⟩ := hS.exists_tvBlock hV ht
  have htB : t ∈ B := hBt ▸ Subgroup.mem_zpowers t
  have htP : t ∈ P := hBP htB
  have hwW : w ∈ W := by
    obtain ⟨v, hv⟩ := exists_apply_eq_mul h.tw h.t1
    have hmem : t v * v⁻¹ ∈ commV B := Subgroup.subset_closure ⟨t, htB, v, rfl⟩
    rw [hv, mul_comm v w, mul_inv_cancel_right] at hmem
    exact hBW hmem
  have hcc : ∀ u : V, c (c (c u)) = u := fun u => by
    have := congrArg (fun φ : MulAut V => φ u) hc3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hcinv : ∀ u : V, c⁻¹ u = c (c u) := fun u => by
    apply c.injective
    rw [hcc, MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hcW' : ∀ u ∈ W, c⁻¹ u ∈ W := fun u hu => by rw [hcinv]; exact hcW _ (hcW u hu)
  have key : ∀ d : MulAut V, d ∈ X → (∀ p ∈ P, d * p * d⁻¹ ∈ P) →
      (∀ u ∈ W, d u = u → u = 1) → FOf Φ t ≠ FOf Φ (d * t * d⁻¹) := by
    intro d hdX hdP hdfix heq
    have ht' := hS.conj_mem_tvSet hdX ht
    obtain ⟨x', w', h'⟩ := hS.exists_tvBlock hV ht'
    have hmem := h.mem_G_of_eq h' hV (by rw [← h.FOf_eq, ← h'.FOf_eq, heq])
    have ht'1 : d * t * d⁻¹ ≠ 1 := by
      intro h1
      apply h.t1
      have : t = d⁻¹ * (d * t * d⁻¹) * d := by group
      rw [this, h1]
      group
    have hte := eq_of_mem_GOf hV hS ht hP htP (hdP t htP) (by rw [← h.GOf_eq] at hmem; exact hmem)
      ht'1
    have hdt : d * t = t * d := by
      calc d * t = d * t * d⁻¹ * d := by group
        _ = t * d := by rw [hte]
    obtain ⟨v, hv⟩ := exists_apply_eq_mul h.tw h.t1
    have h1 : t (d v) = d v * d w := by
      have := congrArg (fun φ : MulAut V => φ v) hdt
      simp only [MulAut.mul_apply] at this
      rw [← this, hv, map_mul]
    rcases h.tw.2 (d v) with h2 | h2
    · rw [h2] at h1
      have h3 : d w = 1 := by
        have := congrArg (fun z => (d v)⁻¹ * z) h1
        simpa using this.symm
      exact h.tw.1 (by rw [← map_one d] at h3; exact d.injective h3)
    · rw [h2] at h1
      have h3 : d w = w := (mul_left_cancel h1).symm
      exact h.tw.1 (hdfix w hwW h3)
  have hne1 := key c hcX hcP hfix
  have hne2 := key c⁻¹ (X.inv_mem hcX) (fun p hp => by rw [inv_inv]; exact hcP' p hp)
    (fun u hu hu' => hfix u hu (by
      have := congrArg c hu'
      rwa [MulAut.inv_apply, MulEquiv.apply_symm_apply, eq_comm] at this))
  have hw1 : c w ∈ commV (FOf Φ (c * t * c⁻¹)) := by
    rw [← hS.FOf_conj hcX, commV_map_conj, h.FOf_eq]
    exact ⟨w, h.w_mem, rfl⟩
  have hw2 : c⁻¹ w ∈ commV (FOf Φ (c⁻¹ * t * c⁻¹⁻¹)) := by
    rw [← hS.FOf_conj (X.inv_mem hcX), commV_map_conj, h.FOf_eq]
    exact ⟨w, h.w_mem, rfl⟩
  have hf1 := hS.pair_fixV hV ht (hS.conj_mem_tvSet hcX ht) hne1 hw1
  have hf2 := hS.pair_fixV hV ht (hS.conj_mem_tvSet (X.inv_mem hcX) ht) hne2 hw2
  have hsum : w * c w * c⁻¹ w = 1 := by
    have hu : c (w * c w * c⁻¹ w) = w * c w * c⁻¹ w := by
      rw [map_mul, map_mul, hcinv, hcc]
      ac_rfl
    exact hfix _ (W.mul_mem (W.mul_mem hwW (hcW w hwW)) (hcW' w hwW)) hu
  have hwfix : w ∈ fixV (FOf Φ t) := by
    have e : w = (c w * c⁻¹ w)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact hsum
    rw [e]
    exact (fixV _).inv_mem ((fixV _).mul_mem hf1 hf2)
  rw [h.FOf_eq] at hwfix
  have hw0 : w ∈ fixV (Subgroup.zpowers x) ⊓ commV (Subgroup.zpowers x) := ⟨hwfix, h.w_mem⟩
  rw [(h.decomp hV).2] at hw0
  exact h.tw.1 hw0

section General

variable {Y M : Type} [Group Y] [Group M]

theorem pCoreOf_range_eq_bot [Finite Y] [Finite M] (φ : Y →* M)
    (hker : φ.ker = CFSG.Open.pCore 2 Y) : pCoreOf 2 φ.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 φ.range with hP
  set P' : Subgroup Y := P.comap φ with hP'
  have hP'n : P'.Normal := ⟨fun y hy g => by
    show φ (g * y * g⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 φ.range ⟨g, rfl⟩) _).mp hy⟩
  have hP'2 : IsPGroup 2 P' := by
    intro y
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 φ.range ⟨φ y, y.2⟩
    have h1 : (y : Y) ^ 2 ^ a ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      simpa using congrArg Subtype.val ha
    rw [hker] at h1
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := Y) ⟨_, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((y : Y) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simpa [pow_add, pow_mul] using hb'
  have hle : P' ≤ CFSG.Open.pCore 2 Y := CFSG.LieType.BorelTits.le_pCore 2 hP'n hP'2
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨y, rfl⟩ := pCoreOf_le 2 φ.range hm
  have hy : y ∈ φ.ker := hker ▸ hle (show φ y ∈ P from hm)
  rw [MonoidHom.mem_ker] at hy
  rw [hy]
  exact Subgroup.one_mem _

theorem setting_of_nilpotent {V : Type} [CommGroup V] [Finite V] {X N : Subgroup (MulAut V)}
    (hNX : N ≤ X) (hN : (N.subgroupOf X).Normal) (hnil : Group.IsNilpotent N)
    (hO2 : pCoreOf 2 X = ⊥) : Setting X N := by
  have hn : ∀ g ∈ X, ∀ f ∈ N, g * f * g⁻¹ ∈ N := fun g hg f hf =>
    (Subgroup.normal_subgroupOf_iff hNX).mp hN f g hf hg
  refine ⟨hNX, hn, ?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hodd := B1Red.odd_orderOf_of_nilpotent_normal hNX hn hO2
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
    have h := hodd y y.2
    rw [Subgroup.orderOf_coe, hy] at h
    exact (by decide : ¬ Odd 2) h
  · exact inferInstance

theorem quasisimple_normal {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    exact eq_top_iff.mpr (hp ▸ hcomm)

theorem mem_cComp_of_isComponentOf [Finite M] {K X : Subgroup M}
    (hK : CFSG.Open.IsComponentOf K X) : K ∈ cComp X := by
  obtain ⟨hKX, hsub, hq⟩ := hK
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hq.1)
  refine ⟨?_, hperf, hsub, ?_⟩
  · intro hbot
    have := hq.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
    apply hab
    have h1 : ∀ x : ↥K, x = 1 := fun x => Subtype.ext (by
      have : (x : M) ∈ (⊥ : Subgroup M) := hbot ▸ x.2
      exact Subgroup.mem_bot.mp this)
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y => rw [h1 x, h1 y]
  · intro K' hlt hK'1 hK'p hK'sub
    have h1 := A3.subnormal_of_le_of_le hK'sub hlt.le hKX
    obtain ⟨P, hPK, hPn, hK'P⟩ := A3.subnormal_exists_normal_of_lt h1 hlt
    rcases quasisimple_normal hq hPn with h | h
    · apply hPK.ne
      apply le_antisymm hPK.le
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ P.subgroupOf K := h ▸ Subgroup.mem_top _
      exact this
    · apply hK'1
      have hab : ⁅K', K'⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        have hbc := Subgroup.mem_center_iff.mp (h (show (⟨b, hlt.le hb⟩ : ↥K) ∈ P.subgroupOf K
          from hK'P hb)) ⟨a, hlt.le ha⟩
        exact (congrArg Subtype.val hbc).symm
      rw [← hK'p, hab]


theorem exists_component_not_le [Finite M] {X B : Subgroup M} (hBX : B ≤ X) (hB : B ≠ ⊥)
    (hBsq : ∀ b ∈ B, b ^ 2 = 1) (hO2 : pCoreOf 2 X = ⊥)
    (hN : ∀ N : Subgroup M, N ≤ X → (N.subgroupOf X).Normal → Group.IsNilpotent N →
      B ≤ Subgroup.centralizer (N : Set M)) :
    ∃ K, CFSG.Open.IsComponentOf K X ∧ ¬ B ≤ Subgroup.centralizer (K : Set M) := by
  by_contra hno
  push Not at hno
  set F := CFSG.Open.quasithinGenFitting X with hF
  have hBF : B ≤ Subgroup.centralizer (F : Set M) := by
    rw [← Subgroup.le_centralizer_iff]
    refine sup_le (sSup_le fun N hN' => ?_) (sSup_le fun K hK => ?_)
    · obtain ⟨hNX, hNn, hnil⟩ := hN'
      rw [Subgroup.le_centralizer_iff]
      exact hN N hNX hNn hnil
    · rw [Subgroup.le_centralizer_iff]
      exact hno K hK
  have hBFle : B ≤ F := fun b hb => centralizer_quasithinGenFitting_le X ⟨hBX hb, hBF hb⟩
  set Z := F ⊓ Subgroup.centralizer (F : Set M) with hZ
  have hXZ : X ≤ Subgroup.normalizer (Z : Set M) := fun x hx =>
    F7.mem_normalizer_inf (le_normalizer_quasithinGenFitting X hx)
      (InternalSec.le_normalizer_centralizer (le_normalizer_quasithinGenFitting X) hx)
  have hJZ : conjClosure B X ≤ Z := conjClosure_le fun x hx b hb =>
    (Subgroup.mem_normalizer_iff.mp (hXZ hx) b).mp ⟨hBFle hb, hBF hb⟩
  have hJX : conjClosure B X ≤ X := hJZ.trans (inf_le_left.trans (quasithinGenFitting_le X))
  have hJe : IsElemAbelian 2 (conjClosure B X) := by
    refine F7.isElemAbelian_closure _ (fun x hx y hy => ?_) (fun x hx => ?_)
    · have hxZ : x ∈ Z := hJZ (Subgroup.subset_closure hx)
      have hyZ : y ∈ Z := hJZ (Subgroup.subset_closure hy)
      exact Subgroup.mem_centralizer_iff.mp hyZ.2 x hxZ.1
    · obtain ⟨h, -, b, hb, rfl⟩ := hx
      rw [conj_pow, hBsq b hb]
      group
  have hJ2 : IsPGroup 2 (conjClosure B X) := fun g =>
    ⟨1, Subtype.ext (by simpa using hJe.2 g g.2)⟩
  have hJle := le_pCoreOf_of_le_normalizer 2 hJX (le_normalizer_conjClosure B X) hJ2
  rw [hO2] at hJle
  exact hB (le_bot_iff.1 ((le_conjClosure B X).trans hJle))

theorem exists_cComp_of_range [Finite Y] [Finite M] (f : Y →* M) (hf : Group.IsSolvable f.ker)
    {K' : Subgroup M} (hK' : K' ∈ cComp f.range) : ∃ K ∈ cComp (⊤ : Subgroup Y), K.map f = K' := by
  have h := LocDbl.map_surjOn_cComp f hf ⊤
  rw [← MonoidHom.range_eq_map] at h
  exact h hK'

end General

theorem c012_fix_W3 : ∀ x : P6, InW34 x →
    (act4f (swap 0 1 * swap 1 2) x * x⁻¹ = 1 ∨ act4f (swap 0 1 * swap 1 2) x * x⁻¹ = e0123) →
      x = 1 ∨ x = e0123 := by
  decide +kernel

end A6Fourteen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem mem_V1_of_c012 {c : ↥(Subgroup.normalizer (V : Set G))}
    (hc : S.frame.ρ c = swap 0 1 * swap 1 2) {w : G} (hw : w ∈ S.V3)
    (hfix : (c : G) * w * (c : G)⁻¹ * w⁻¹ ∈ fsuV1 T V) : w ∈ fsuV1 T V := by
  obtain ⟨hwV, hw3⟩ := S.mem_pre.1 hw
  have hm : (c : G) * w * (c : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp c.2 w).mp hwV
  have hcw : (c : G) * w * (c : G)⁻¹ * w⁻¹ ∈ V := V.mul_mem hm (V.inv_mem hwV)
  have hψ : ((S.frame.ψ ⟨_, hcw⟩ : ↥W4) : P6) =
      act4f (S.frame.ρ c) (S.frame.ψ ⟨w, hwV⟩ : P6) * (S.frame.ψ ⟨w, hwV⟩ : P6)⁻¹ := by
    have e : (⟨_, hcw⟩ : ↥V) = ⟨_, hm⟩ * (⟨w, hwV⟩ : ↥V)⁻¹ := rfl
    rw [e, map_mul, map_inv, S.psi_conj c ⟨w, hwV⟩]
    rfl
  have h1 : act4f (swap 0 1 * swap 1 2) (S.frame.ψ ⟨w, hwV⟩ : P6) *
        (S.frame.ψ ⟨w, hwV⟩ : P6)⁻¹ = 1 ∨
      act4f (swap 0 1 * swap 1 2) (S.frame.ψ ⟨w, hwV⟩ : P6) *
        (S.frame.ψ ⟨w, hwV⟩ : P6)⁻¹ = e0123 := by
    rw [← hc, ← hψ]
    rcases S.mem_V1_iff.1 hfix with h | h
    · left
      have : (⟨_, hcw⟩ : ↥V) = 1 := Subtype.ext h
      rw [this, map_one]
      rfl
    · right
      have : (⟨_, hcw⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext h
      rw [this, S.psi_z]
  rw [S.mem_V1_iff]
  rcases A6Fourteen.c012_fix_W3 _ ⟨(S.frame.ψ ⟨w, hwV⟩).2, hw3⟩ h1 with h | h
  · left
    have : (⟨w, hwV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h)
    exact congrArg Subtype.val this
  · right
    have : (⟨w, hwV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ :=
      S.frame.ψ.injective (by rw [S.psi_z]; exact Subtype.ext h)
    exact congrArg Subtype.val this

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

omit hNS h13315 h1356two hH hab in
theorem range_secAct_plus [IsMulCommutative ↥(conjClosure S.V3 H)] :
    (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H))).range =
      autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) := by
  ext ψ
  rw [MonoidHom.mem_range, A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
    S.le_normalizer_U0 le_rfl]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, rfl⟩
  · rintro ⟨h, -, rfl⟩
    exact ⟨h, rfl⟩

theorem ker_secAct_plus (hNU : ¬ LieModel G .PSU 4 3 1)
    (hhat : ¬ IsHatA6 L) (hLem : Lem1374One) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) (S.le_normalizer_U0 (H := H))).ker =
      CFSG.Open.pCore 2 ↥H := by
  ext h
  rw [MonoidHom.mem_ker, A6Mod.secAct_eq_one_iff,
    ← S.mem_QH_iff_plus hNS h13315 h1356two hH hab hNU hhat hLem h.2]
  constructor
  · rintro ⟨x, hx, hxh⟩
    rwa [Subtype.ext hxh] at hx
  · intro hh
    exact ⟨h, hh, rfl⟩

theorem pCoreOf_plus_eq_bot (hNU : ¬ LieModel G .PSU 4 3 1)
    (hhat : ¬ IsHatA6 L) (hLem : Lem1374One) [IsMulCommutative ↥(conjClosure S.V3 H)] :
    pCoreOf 2 (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) = ⊥ := by
  rw [← S.range_secAct_plus]
  exact A6Fourteen.pCoreOf_range_eq_bot _
    (S.ker_secAct_plus hNS h13315 h1356two hH hab hNU hhat hLem)

omit hab in
theorem Q_le_H (hhat : ¬ IsHatA6 L) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ H :=
  (S.cLT_le_T hhat).trans (S.hypF91 hNS h13315 h1356two hH).T_le_H

namespace Conf

variable (C : S.Conf H)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

omit hNS h13315 h1356two hH hab in
theorem isPGroup_Q_plus [IsMulCommutative ↥(conjClosure S.V3 H)]
    (hQH : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ H) :
    IsPGroup 2 (autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (conjClosure S.V3 H))
      ⊤ ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨q, hqQ, rfl⟩ := (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
    S.le_normalizer_U0 hQH).1 hψ
  obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨q, S.cLT_le_T hhat hqQ⟩
  refine ⟨k, Subtype.ext ?_⟩
  have hq : q ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  show (A6Mod.secAct (le_normalizer_conjClosure S.V3 H) S.le_normalizer_U0 q) ^ 2 ^ k = 1
  rw [← map_pow, hq, map_one]

omit hNS h13315 h1356two hH hab hhat in
theorem commV_A_plus_le [IsMulCommutative ↥(conjClosure S.V3 H)] (hUH : conjClosure S.V3 H ≤ H)
    (hAH : C.A ≤ H) (hcomm : ∀ u ∈ conjClosure S.V3 H, ∀ a ∈ C.A, a * u * a⁻¹ * u⁻¹ ∈
      S.V3 ⊔ (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))) :
    commV (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ≤
      (S.V3.subgroupOf (conjClosure S.V3 H)).map
        (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
          (conjClosure S.V3 H))) := by
  have hV3N : S.V3 ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    ((le_conjClosure S.V3 H).trans hUH).trans S.le_normalizer_U0
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨ψ, hψ, v, rfl⟩
  obtain ⟨a, haA, rfl⟩ := (A6Mod.mem_autSec_iff (le_normalizer_conjClosure S.V3 H)
    S.le_normalizer_U0 hAH).1 hψ
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective _ v
  rw [A6Mod.secAct_secMk, ← map_inv, ← map_mul]
  have hc := hcomm u u.2 a haA
  have hc' : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈
      ((S.V3 : Set G) * ((conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :
        Subgroup G) : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hV3N]
    exact hc
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hc'
  have hxU : x ∈ conjClosure S.V3 H := le_conjClosure S.V3 H hx
  have e : (Setup.rho (conjClosure S.V3 H) H (le_normalizer_conjClosure S.V3 H) a u * u⁻¹ :
      ↥(conjClosure S.V3 H)) = ⟨x, hxU⟩ * ⟨y, hy.1⟩ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv, Subgroup.coe_mul, ← hxy]
  rw [e, map_mul]
  have hy1 : InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
      (conjClosure S.V3 H)) ⟨y, hy.1⟩ = 1 := (A6Mod.secMk_eq_one_iff _).2 hy.2
  rw [hy1, mul_one]
  exact ⟨⟨x, hxU⟩, hx, rfl⟩

include C in
theorem exists_c_plus [IsMulCommutative ↥(conjClosure S.V3 H)]
    (h13314 : Stmt13_3_14) :
    ∃ c ∈ autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)),
      c ^ 3 = 1 ∧
      (∀ p ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)),
        c * p * c⁻¹ ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
          (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
      (∀ p ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)),
        c⁻¹ * p * c ∈ autSec (autOn ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
          (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
      (∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H))),
        c w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H)))) ∧
      (∀ w ∈ (S.V3.subgroupOf (conjClosure S.V3 H)).map
          (InternalSec.secMk ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf
            (conjClosure S.V3 H))), c w = w → w = 1) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hQH := S.Q_le_H hNS h13315 h1356two hH hhat
  obtain ⟨c₁, hc₁L, hc₁3, hρ, -⟩ := C.exists_c1 hNS h13315 h1356two hH hab hhat
  have hc₁H : (c₁ : G) ∈ H := S.L1_le_of_mem_Hz hNS h13315 h1356two hH hc₁L
  have hc₁LT : (c₁ : G) ∈ L ⊔ T := le_sup_left (a := L) (S.L1_le_L hc₁L)
  have hcN := S.le_normalizer_cLT hc₁LT
  set c₀ : ↥H := ⟨c₁, hc₁H⟩ with hc₀
  refine ⟨A6Mod.secAct hHU hHC c₀, (A6Mod.mem_autSec_iff hHU hHC le_rfl).2 ⟨c₀, hc₁H, rfl⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · have : c₀ ^ 3 = 1 := Subtype.ext (by simpa using hc₁3)
    rw [← map_pow, this, map_one]
  · intro p hp
    obtain ⟨q, hqQ, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hQH).1 hp
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (A6Mod.mem_autSec_iff hHU hHC hQH).2 ⟨_,
      (Subgroup.mem_normalizer_iff.mp hcN _).mp hqQ, rfl⟩
  · intro p hp
    obtain ⟨q, hqQ, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHC hQH).1 hp
    rw [← map_inv, ← map_mul, ← map_mul]
    have hcN' := Subgroup.inv_mem _ hcN
    refine (A6Mod.mem_autSec_iff hHU hHC hQH).2 ⟨_, ?_, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp hcN' (q : G)).mp hqQ
    simpa using this
  · rintro _ ⟨u, hu, rfl⟩
    rw [A6Mod.secAct_secMk]
    refine ⟨_, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Setup.rho_apply_coe]
    exact (Subgroup.mem_normalizer_iff.mp (S.L1T_le_NV3 (le_sup_left (a := S.L1) hc₁L))
      (u : G)).mp hu
  · rintro _ ⟨u, hu, rfl⟩ hfix
    rw [A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6Mod.secMk_eq_one_iff] at hfix
    rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv] at hfix
    have hu' : (u : G) ∈ S.V3 := hu
    have hcu : (c₁ : G) * u * (c₁ : G)⁻¹ ∈ S.V3 :=
      (Subgroup.mem_normalizer_iff.mp (S.L1T_le_NV3 (le_sup_left (a := S.L1) hc₁L))
        (u : G)).mp hu'
    have h1 : (c₁ : G) * u * (c₁ : G)⁻¹ * (u : G)⁻¹ ∈ fsuV1 T V := by
      rw [← S.V3_inf_U0 hNS h13315 h1356two hH h13314]
      refine ⟨S.V3.mul_mem hcu (S.V3.inv_mem hu'), ?_, hfix⟩
      exact (conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp
        (hHU hc₁H) (u : G)).mp u.2) ((conjClosure S.V3 H).inv_mem u.2)
    have h2 := S.mem_V1_of_c012 hρ hu' h1
    exact (A6Mod.secMk_eq_one_iff _).2 (S.V1_le_centralizer_QH hNS h13315 h1356two hH h2)

theorem le_centralizer_nilpotent
    (hNU : ¬ LieModel G .PSU 4 3 1) (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) (hLem : Lem1374One) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {B N : Subgroup (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))))}
    (hB : IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B)
    (hBA : B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
    (hNX : N ≤ autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
    (hN : (N.subgroupOf (autSec (autOn H (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))).Normal)
    (hnil : Group.IsNilpotent N) : B ≤ Subgroup.centralizer (N : Set _) := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hV : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  have hS := A6Fourteen.setting_of_nilpotent hNX hN hnil
    (S.pCoreOf_plus_eq_bot hNS h13315 h1356two hH hab hNU hhat hLem)
  obtain ⟨c, hcX, hc3, hcP, hcP', hcW, hfix⟩ :=
    exists_c_plus hNS h13315 h1356two hH hab C hhat h13314
  have hAH := C.A_le_H hNS h13315 h1356two hH hab hhat
  have hQH := S.Q_le_H hNS h13315 h1356two hH hhat
  have hAQ : C.A ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := fun a ha =>
    ⟨C.VHg_le_LT hNS h13315 h1356two hH hab ha.1, ha.2⟩
  have hBP := hBA.trans (autSec_mono (InternalSec.autOn_le_autOn_of_le hAQ) _ _)
  have hUH : conjClosure S.V3 H ≤ H := hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hmono : commV B ≤ commV (autSec (autOn C.A (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) := by
    unfold commV
    refine Subgroup.closure_mono fun w hw => ?_
    obtain ⟨x, hx, v, hv⟩ := hw
    exact ⟨x, hBA hx, v, hv⟩
  have hBW := hmono.trans (C.commV_A_plus_le hUH hAH fun u hu a ha =>
    C.comm_UH_A_mem hNS h13315 h1356two hH hab hhat hna h13314 hu ha)
  have h := A6Fourteen.comm_eq_bot (Bridge.sec_sq_eq_one hV _ _) hS hB hBP
    (isPGroup_Q_plus hhat hQH) hBW hcX hcP hcP' hc3 hcW hfix
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  exact Subgroup.le_centralizer_iff.mp h

theorem exists_K (hNU : ¬ LieModel G .PSU 4 3 1)
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) (h13314 : Stmt13_3_14) (hLem : Lem1374One)
    [IsMulCommutative ↥(conjClosure S.V3 H)] :
    ∃ B, IsFFStarMin (autSec (autOn H (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) B ∧
      B ≤ autSec (autOn C.A (conjClosure S.V3 H)) ⊤
        ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) ∧
      ∃ K ∈ cComp H, CFSG.Open.IsComponentOf (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)))
          (autSec (autOn H (conjClosure S.V3 H)) ⊤
            ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H))) ∧
        B ≤ Subgroup.normalizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) ∧
        ¬ B ≤ Subgroup.centralizer ((autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) :
            Subgroup _) : Set _) := by
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHC := S.le_normalizer_U0 (H := H)
  have hV : ∀ v : ↥(conjClosure S.V3 H), v ^ 2 = 1 := fun v =>
    Subtype.ext (by simpa using hab.2 v v.2)
  obtain ⟨B, hB, hBA⟩ := C.exists_isFFStarMin_A_plus hNS h13315 h1356two hH hab hhat hNU hna
    h13314 hLem
  refine ⟨B, hB, hBA, ?_⟩
  have hO2 := S.pCoreOf_plus_eq_bot hNS h13315 h1356two hH hab hNU hhat hLem
  obtain ⟨K', hK', hnot⟩ := A6Fourteen.exists_component_not_le hB.1.1 hB.1.2.1 hB.1.2.2.1.2 hO2
    fun N hNX hN hnil => C.le_centralizer_nilpotent hNS h13315 h1356two hH hab hhat hNU hna
      h13314 hLem hB hBA hNX hN hnil
  have hBN := B15P4.asB15Part4 _ (Bridge.sec_sq_eq_one hV _ _) _ B hB.1 K' hK'
  have hK'c := A6Fourteen.mem_cComp_of_isComponentOf hK'
  rw [← S.range_secAct_plus] at hK'c
  have hsolv : Group.IsSolvable (A6Mod.secAct hHU hHC).ker := by
    rw [S.ker_secAct_plus hNS h13315 h1356two hH hab hNU hhat hLem]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)).isNilpotent
    infer_instance
  obtain ⟨K₀, hK₀, hK₀map⟩ := A6Fourteen.exists_cComp_of_range _ hsolv hK'c
  have hK₀H := LocDbl.map_mem_cComp_of_ker H.subtype
    (LocDbl.isSolvable_ker_of_injective _ H.subtype_injective) hK₀
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at hK₀H
  have hKeq : autSec (autOn (K₀.map H.subtype) (conjClosure S.V3 H)) ⊤
      ((Subgroup.centralizer (pCoreOf 2 H : Set G)).subgroupOf (conjClosure S.V3 H)) = K' := by
    rw [← hK₀map]
    ext ψ
    rw [A6Mod.mem_autSec_iff hHU hHC (Subgroup.map_subtype_le K₀), Subgroup.mem_map]
    constructor
    · rintro ⟨h, ⟨k, hk, hkh⟩, rfl⟩
      have : k = h := Subtype.ext hkh
      exact ⟨k, hk, by rw [this]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, ⟨k, hk, rfl⟩, rfl⟩
  exact ⟨K₀.map H.subtype, hK₀H, hKeq ▸ hK', hKeq ▸ hBN, hKeq ▸ hnot⟩

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
