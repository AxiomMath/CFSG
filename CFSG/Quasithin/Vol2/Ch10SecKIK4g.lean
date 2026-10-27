module

public import CFSG.Quasithin.Vol2.Ch10SecKIK4f
public import CFSG.Quasithin.Background.G64Linear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique MulAction
open scoped commutatorElement IsMulCommutative

theorem card_fixV_modEq {M : Type} [CommGroup M] [Finite M] (σ : MulAut M) (hσ : σ ^ 5 = 1) :
    Nat.card M ≡ Nat.card ↥(fixV (Subgroup.zpowers σ)) [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 (Subgroup.zpowers σ) := by
    intro g
    obtain ⟨k, hk⟩ := g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
  have h := hp.card_modEq_card_fixedPoints M
  have hset : fixedPoints (Subgroup.zpowers σ) M = (fixV (Subgroup.zpowers σ) : Set M) := by
    ext x
    rw [SetLike.mem_coe, G64.fixV_zpowers_iff]
    constructor
    · intro hx
      exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g
      obtain ⟨g, hg⟩ := g
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      show (σ ^ i) x = x
      clear hg
      induction i using Int.induction_on with
      | zero => simp
      | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hx, ih]
      | pred n ih =>
        rw [zpow_sub_one, MulAut.mul_apply]
        have : σ⁻¹ x = x := by rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hx]
        rw [this, ih]
  rw [hset] at h
  exact h

theorem eq_of_modEq_five {c n : ℕ} (hn : n ∣ 16) (hc : c ∣ n) (h : n ≡ c [MOD 5]) :
    c = n ∨ (c = 1 ∧ n = 16) := by
  have hn16 : n ≤ 16 := Nat.le_of_dvd (by norm_num) hn
  have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hn (by norm_num)
  have hcn : c ≤ n := Nat.le_of_dvd hn0 hc
  unfold Nat.ModEq at h
  interval_cases n <;> interval_cases c <;> simp_all

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_not_le_pCore {L : Subgroup G} (hperf : ⁅L, L⁆ = L)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {K : Subgroup ↥L} [K.Normal]
    (hnot : ¬ K ≤ CFSG.pCore 2 ↥L) : K = ⊤ := by
  let Kbar : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have : Kbar.Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Kbar with h | h
  · exfalso
    apply hnot
    intro x hx
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ Kbar := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · have hall : ∀ x : ↥L, ∃ n ∈ K, ∃ p ∈ CFSG.pCore 2 ↥L, x = n * p := by
      intro x
      have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ∈ Kbar := by rw [h]; trivial
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, n⁻¹ * x, ?_, by simp⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hnx
      exact QuotientGroup.eq.1 hnx
    have hpg : IsPGroup 2 (↥L ⧸ K) := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨n, hn, p, hp, rfl⟩ := hall x
        obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨p, hp⟩
        refine ⟨k, ?_⟩
        have hp1 : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have hn1 : (QuotientGroup.mk n : ↥L ⧸ K) = 1 := (QuotientGroup.eq_one_iff n).2 hn
        rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hp1]
        rfl
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hperfL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hperf
    have hperfQ : Group.IsPerfect (↥L ⧸ K) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    have hsub : Subsingleton (↥L ⧸ K) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isNilpotent _ hpg.isNilpotent
    rw [eq_top_iff]
    intro x _
    exact (QuotientGroup.eq_one_iff x).1 (Subsingleton.elim _ _)

theorem irrG_of_card_sixteen {L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hcard : Nat.card ↥V = 16) (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G)) (hperf : ⁅L, L⁆ = L)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (h5 : 5 ∣ Nat.card ↥L) : IrrG L V := by
  have : IsMulCommutative ↥V := hV.1
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hsV : (s : G) ∉ Subgroup.centralizer (V : Set G) := by
    intro hsC
    apply hLV
    have hK : ((L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L).Normal := by
      refine ⟨fun k hk l => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      refine ⟨L.mul_mem (L.mul_mem l.2 hk.1) (L.inv_mem l.2), ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hk.2
      have hmem : (l : G) * k * (l : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hlN : ((l : G))⁻¹ ∈ Subgroup.normalizer (V : Set G) := hLN (L.inv_mem l.2)
        have hv' : (l : G)⁻¹ * v * ((l : G))⁻¹⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.mp hlN v).mp hv
        rw [inv_inv] at hv'
        have hc := h1 _ hv'
        calc v * ((l : G) * k * (l : G)⁻¹)
            = l * (((l : G)⁻¹ * v * l) * k) * (l : G)⁻¹ := by group
          _ = l * (k * ((l : G)⁻¹ * v * l)) * (l : G)⁻¹ := by rw [hc]
          _ = (l : G) * k * (l : G)⁻¹ * v := by group
      simpa using hmem
    have hnot : ¬ (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L ≤ CFSG.pCore 2 ↥L := by
      intro hle
      have hsK : s ∈ (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L :=
        Subgroup.mem_subgroupOf.2 ⟨s.2, hsC⟩
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨s, hle hsK⟩
      have h1 : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hs] at h2
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).1
        ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h2))
      omega
    have htop := eq_top_of_not_le_pCore hperf hsimple hnot
    intro l hl
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1
      (htop ▸ Subgroup.mem_top (⟨l, hl⟩ : ↥L)))).2
  set σ := conjAct V ⟨s, hLN s.2⟩ with hσ
  have hσ5 : σ ^ 5 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨s, hLN s.2⟩ : Subgroup.normalizer (V : Set G)) ^ 5 = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one s
      rw [hs] at this
      simpa using congrArg Subtype.val this
    rw [this, map_one]
  have hfixσ : ∀ v : ↥V, σ v = v → v = 1 := by
    have hmod := card_fixV_modEq σ hσ5
    rw [hcard] at hmod
    have hdvd : Nat.card ↥(fixV (Subgroup.zpowers σ)) ∣ 16 :=
      hcard ▸ Subgroup.card_subgroup_dvd_card _
    have hne : Nat.card ↥(fixV (Subgroup.zpowers σ)) ≠ 16 := by
      intro h16
      apply hsV
      have htop : fixV (Subgroup.zpowers σ) = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [h16, hcard]
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : (⟨v, hv⟩ : ↥V) ∈ fixV (Subgroup.zpowers σ) := htop ▸ Subgroup.mem_top _
      rw [G64.fixV_zpowers_iff, hσ] at hv'
      have := congrArg Subtype.val hv'
      rw [InternalSec.coe_conjAct_apply] at this
      calc v * (s : G) = (s : G) * v * (s : G)⁻¹ * s := by rw [this]
        _ = s * v := by group
    rcases eq_of_modEq_five (by norm_num) hdvd hmod with h | ⟨h, -⟩
    · exact absurd h hne
    · intro v hv
      have hmem : v ∈ fixV (Subgroup.zpowers σ) := G64.fixV_zpowers_iff.2 hv
      have := Subgroup.card_eq_one.1 h
      rw [this] at hmem
      exact (Subgroup.mem_bot).1 hmem
  refine ⟨fun hb => ?_, fun X hXV hLX => ?_⟩
  · rw [hb, Subgroup.card_bot] at hcard
    omega
  · by_contra hne
    push Not at hne
    obtain ⟨hX1, hXV'⟩ := hne
    have : IsMulCommutative ↥X := (isElemAbelian_of_le hXV hV).1
    set τ := conjAct X ⟨s, hLX s.2⟩ with hτ
    have hτ5 : τ ^ 5 = 1 := by
      rw [hτ, ← map_pow]
      have : (⟨s, hLX s.2⟩ : Subgroup.normalizer (X : Set G)) ^ 5 = 1 := by
        apply Subtype.ext
        have := pow_orderOf_eq_one s
        rw [hs] at this
        simpa using congrArg Subtype.val this
      rw [this, map_one]
    have hmod := card_fixV_modEq τ hτ5
    have hXd : Nat.card ↥X ∣ 16 := hcard ▸ Subgroup.card_dvd_of_le hXV
    have hX16 : Nat.card ↥X ≠ 16 := fun h =>
      hXV' (Subgroup.eq_of_le_of_card_ge hXV (by rw [h, hcard]))
    have hXne1 : Nat.card ↥X ≠ 1 := fun h => hX1 (Subgroup.card_eq_one.1 h)
    rcases eq_of_modEq_five hXd (Subgroup.card_subgroup_dvd_card _) hmod with h | ⟨-, h⟩
    ·
      obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hX1
      have hxX : (y : G) ∈ X := y.2
      have hx1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
      have htop : fixV (Subgroup.zpowers τ) = ⊤ := Subgroup.eq_top_of_card_eq _ h
      have hx' : (⟨(y : G), hxX⟩ : ↥X) ∈ fixV (Subgroup.zpowers τ) := htop ▸ Subgroup.mem_top _
      rw [G64.fixV_zpowers_iff, hτ] at hx'
      have hxs := congrArg Subtype.val hx'
      rw [InternalSec.coe_conjAct_apply] at hxs
      have hv := hfixσ ⟨(y : G), hXV hxX⟩ (by
        apply Subtype.ext
        rw [hσ, InternalSec.coe_conjAct_apply]
        exact hxs)
      exact hx1 (congrArg Subtype.val hv)
    · exact hX16 h

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
