module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Z

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

omit [Finite G] in
theorem sq_eq_one_of_mem_zpowers {z a : G} (hz2 : z ^ 2 = 1) (ha : a ∈ Subgroup.zpowers z) :
    a ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hzz : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz2]
  rw [pow_two, ← zpow_add, ← two_mul, zpow_mul, hzz, one_zpow]

omit [Finite G] in
theorem zpowers_le_pCoreOf_centralizer {z : G} (hz2 : z ^ 2 = 1) :
    Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · rw [← centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  · exact isPGroup_of_forall_pow fun a ha =>
      ⟨1, by rw [pow_one]; exact sq_eq_one_of_mem_zpowers hz2 ha⟩

namespace Hyp611Nat

theorem charTwo_centralizer_z (h : Hyp611Nat G T M L V n) {z : G} (hz : z ∈ ch6ZS T L V)
    (hz1 : z ≠ 1) :
    ∃ d ∈ L ⊓ Subgroup.normalizer (ch6ZS T L V : Set G),
      IsSylowTwoOf (conjSub d⁻¹ T) (Subgroup.centralizer ({z} : Set G)) ∧
      CharTwo (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, hle⟩ := h.exists_conjSub_T_le_centralizer hz hz1
  have hz2 : z ^ 2 = 1 := h.toHyp611.isElemAbelian.2 z hz.1
  have hT' : quasithinIsSylowTwo (conjSub d⁻¹ T) :=
    ⟨h.sylow.1.map _, by
      unfold conjSub
      rw [show (MulAut.conj d⁻¹).toMonoidHom = ((MulAut.conj d⁻¹ : G ≃* G) : G →* G) from rfl,
        Subgroup.index_map_equiv]
      exact h.sylow.2⟩
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hT'
  have hsyl : IsSylowTwoOf (conjSub d⁻¹ T) (Subgroup.centralizer ({z} : Set G)) :=
    E6.isSylowIn_of_le ⟨le_top, hT'.1, by rw [Subgroup.relIndex_top_right]; exact hT'.2⟩
      hle le_top
  refine ⟨d, hd, hsyl, ?_⟩
  have hO : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
    intro h0
    have := zpowers_le_pCoreOf_centralizer hz2 (Subgroup.mem_zpowers z)
    rw [h0, Subgroup.mem_bot] at this
    exact hz1 this
  have hInH : InH (P : Subgroup G) (Subgroup.centralizer ({z} : Set G)) := by
    rw [hP]
    exact ⟨hle, hO⟩
  exact CFSG.Quasithin.charTwo_of_inH h.qtke.2.1 P hInH

theorem ZS_le_pCoreOf_centralizer_z (h : Hyp611Nat G T M L V n) (hn : n = 2) {z : G}
    (hz : z ∈ ch6ZS T L V) (hz1 : z ≠ 1) :
    ch6ZS T L V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd, hsyl, hchar⟩ := h.charTwo_centralizer_z hz hz1
  have hz2 : z ^ 2 = 1 := h.toHyp611.isElemAbelian.2 z hz.1
  have hTN : conjSub d⁻¹ T ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    have h1 := conjSub_mono d⁻¹ h.T_le_normalizer_ZS
    rwa [← conjSub_normalizer, conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ hd.2)] at h1
  have hOT := F7.isSylowTwoOf_pCoreOf_le hsyl
  have hZcard : Nat.card (ch6ZS T L V) = 4 := by rw [h.card_ZS, hn]; norm_num
  have hzle : Subgroup.zpowers z ≤ ch6ZS T L V := Subgroup.zpowers_le.mpr hz
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz1
  have hidx : (Subgroup.zpowers z).relIndex (ch6ZS T L V) = 2 := by
    have := card_mul_relIndex_of_le hzle
    rw [hzcard, hZcard] at this
    omega
  have hZab : ∀ a ∈ ch6ZS T L V, ∀ b ∈ ch6ZS T L V, a * b = b * a := by
    intro a ha b hb
    have := h.toHyp611.isElemAbelian.1
    exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha.1⟩ ⟨b, hb.1⟩)
  intro x hx
  refine mem_pCoreOf_of_commutator_mem hchar le_rfl hz2
    (Subgroup.mem_centralizer_singleton_iff.mpr (hZab x hx z hz)) fun q hq => ?_
  have hqT := hOT hq
  have hqN := hTN hqT
  have hqz : q * z = z * q :=
    Subgroup.mem_centralizer_singleton_iff.mp (hsyl.1 hqT)
  have hw : q * x * q⁻¹ ∈ ch6ZS T L V := (Subgroup.mem_normalizer_iff.mp hqN x).mp hx
  have hcomm : x * q * x⁻¹ * q⁻¹ = (x⁻¹ * (q * x * q⁻¹))⁻¹ := by
    have := hZab x hx (q * x * q⁻¹) hw
    calc x * q * x⁻¹ * q⁻¹ = x * (q * x * q⁻¹)⁻¹ := by group
      _ = (q * x * q⁻¹)⁻¹ * x := by
        have h2 := hZab x hx _ (Subgroup.inv_mem _ hw)
        exact h2
      _ = (x⁻¹ * (q * x * q⁻¹))⁻¹ := by group
  rw [hcomm]
  refine Subgroup.inv_mem _ ?_
  by_cases hxz : x ∈ Subgroup.zpowers z
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have : q * z ^ k * q⁻¹ = z ^ k := by
      rw [(Commute.zpow_right (show Commute q z from hqz) k).eq, mul_inv_cancel_right]
    rw [this, inv_mul_cancel]
    exact Subgroup.one_mem _
  · have hwz : q * x * q⁻¹ ∉ Subgroup.zpowers z := by
      intro hw'
      apply hxz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have : x = z ^ k := by
        have h3 : x = q⁻¹ * (q * x * q⁻¹) * q := by group
        have hc := (Commute.zpow_right (show Commute q z from hqz) k).eq
        rw [h3, ← hk]
        calc q⁻¹ * z ^ k * q = q⁻¹ * (z ^ k * q) := by group
          _ = q⁻¹ * (q * z ^ k) := by rw [hc]
          _ = z ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem_zpowers z k
    exact inv_mul_mem_of_relIndex_two hidx hx hw hxz hwz

end Hyp611Nat

namespace Cfg619

variable (h : Hyp6116 G T M L V n) (c : Cfg619 T L V H n y)
include h c

theorem qz {z : G} (hz1 : z ≠ 1)
    (hzZ : Subgroup.zpowers z = ch6ZS T L V ⊓ conjSub y (ch6ZS T L V)) :
    CharTwo (Subgroup.centralizer ({z} : Set G)) ∧
      conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)) ≤
        pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
      conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)) ≤
        Subgroup.normalizer (V : Set G) ∧
      conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)) ≤
        Subgroup.normalizer (conjSub y V : Set G) ∧
      conjSub y (ch6ZS T L V) ≤
        conjClosure (ch6ZS T L V) (Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem : z ∈ ch6ZS T L V ⊓ conjSub y (ch6ZS T L V) := hzZ ▸ Subgroup.mem_zpowers z
  have hzS := hzmem.1
  obtain ⟨d, hd, hsyl, hchar⟩ := h.toHyp611Nat.charTwo_centralizer_z hzS hz1
  have hZO := h.toHyp611Nat.ZS_le_pCoreOf_centralizer_z c.n_eq hzS hz1
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  have hQO : conjClosure (ch6ZS T L V) Gz ≤ pCoreOf 2 Gz := by
    refine CFSG.Quasithin.conjClosure_le fun g hg x hx => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Gz hg) x).mp (hZO hx)
  have hTV : conjSub d⁻¹ T ≤ Subgroup.normalizer (V : Set G) := by
    have h1 := conjSub_mono d⁻¹ h.toHyp611.T_le_normalizer
    rwa [← conjSub_normalizer, conjSub_eq_of_mem_normalizer'
      (Subgroup.inv_mem _ (h.toHyp611.L_le_normalizer hd.1))] at h1
  have hQV : conjClosure (ch6ZS T L V) Gz ≤ Subgroup.normalizer (V : Set G) :=
    (hQO.trans (F7.isSylowTwoOf_pCoreOf_le hsyl)).trans hTV
  have hzE : z ∈ conjSub y V := conjSub_mono y inf_le_left hzmem.2
  obtain ⟨c', hc', hEc⟩ := exists_centralizer_conjSub_eq h.toHyp611Nat.transitive_V hzS.1 hz1 hzE
  obtain ⟨c'', hc'', hZc⟩ :=
    exists_centralizer_conjSub_eq h.toHyp611Nat.transitive_ZS hzS hz1 hzmem.2
  refine ⟨hchar, hQO, hQV, ?_, ?_⟩
  · rw [hEc, conjSub_normalizer, ← conjSub_eq_of_mem_normalizer'
      (le_normalizer_conjClosure (ch6ZS T L V) Gz hc')]
    exact conjSub_mono _ hQV
  · rw [hZc]
    exact Hyp6116.conjSub_le_conjClosure hc''

end Cfg619

end CFSG.Quasithin.H13
