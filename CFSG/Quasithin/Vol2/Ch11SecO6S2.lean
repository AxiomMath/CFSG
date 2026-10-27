module

public import CFSG.Quasithin.Vol2.Ch11SecO6S1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD.O6S

open CFSG.Open
open scoped MatrixGroups

section Struct

open SecG.Bar CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {K L₁ : Subgroup G} {p : ℕ} [Fact p.Prime]

omit [Finite G] in
theorem two_ne_zero_zmod (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h')
  omega

theorem range_spec (hp5 : 5 ≤ p) {φ : KBar K →* SL(2, ZMod p)}
    (hφk : φ.ker = CFSG.oddCore (KBar K)) (hL : L₁ ≤ K) (hperf : ⁅L₁, L₁⁆ = L₁)
    (h60 : (CFSG.pCore 2 ↥L₁).index = 60) :
    (-1 : SL(2, ZMod p)) ∈ (φ.comp (l1Map hL)).range ∧
      Nat.card (φ.comp (l1Map hL)).range = 120 := by
  obtain ⟨-, hcard⟩ := chi_spec hp5 hφk hL hperf h60
  have h2 := two_ne_zero_zmod hp5
  set Z := Subgroup.center SL(2, ZMod p) with hZ
  set Bm := (φ.comp (l1Map hL)).range with hBm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (chi hL φ).range) 2
    (by rw [hcard]; norm_num)
  obtain ⟨l, hl⟩ := y.2
  have hb : orderOf (QuotientGroup.mk' Z (φ (l1Map hL l))) = 2 := by
    rw [← chi_apply, hl, Subgroup.orderOf_coe, hy]
  set b := φ (l1Map hL l) with hbdef
  have hb2 : b ^ 2 ∈ Z := by
    rw [← QuotientGroup.eq_one_iff (N := Z), QuotientGroup.mk_pow]
    have := pow_orderOf_eq_one (QuotientGroup.mk' Z b)
    rwa [hb] at this
  have hbZ : b ∉ Z := by
    intro h
    have h1 : QuotientGroup.mk' Z b = 1 := (QuotientGroup.eq_one_iff _).mpr h
    rw [h1, orderOf_one] at hb
    norm_num at hb
  have hneg : (-1 : SL(2, ZMod p)) ∈ Bm := by
    rcases (mem_center_iff h2).mp hb2 with h | h
    · exfalso
      rcases ABGLocalTools.sl2_eq_one_or_neg_one_of_sq_eq_one h2 h with h' | h'
      · exact hbZ (h' ▸ Z.one_mem)
      · exact hbZ (h' ▸ (mem_center_iff h2).mpr (Or.inr rfl))
    · rw [← h]
      exact ⟨l ^ 2, by rw [MonoidHom.comp_apply, map_pow, map_pow]⟩
  refine ⟨hneg, ?_⟩
  have hZB : Z ≤ Bm := fun z hz => by
    rcases (mem_center_iff h2).mp hz with rfl | rfl
    · exact Bm.one_mem
    · exact hneg
  let f : ↥Bm →* PSL(2, ZMod p) := (QuotientGroup.mk' Z).comp Bm.subtype
  have hfr : f.range = (chi hL φ).range := by
    ext y
    constructor
    · rintro ⟨⟨_, l', rfl⟩, rfl⟩
      exact ⟨l', rfl⟩
    · rintro ⟨l', rfl⟩
      exact ⟨⟨_, l', rfl⟩, rfl⟩
  have hfk : f.ker = Z.subgroupOf Bm := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hfr, hcard, hfk,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZB).toEquiv, card_center h2] at h1
  rw [← h1]

theorem l1Bar_inf_oddCore (hp5 : 5 ≤ p) {φ : KBar K →* SL(2, ZMod p)}
    (hφk : φ.ker = CFSG.oddCore (KBar K)) (hL : L₁ ≤ K) (hperf : ⁅L₁, L₁⁆ = L₁)
    (h60 : (CFSG.pCore 2 ↥L₁).index = 60) :
    l1Bar K L₁ ⊓ CFSG.oddCore (KBar K) = ⊥ := by
  obtain ⟨hker, -⟩ := chi_spec hp5 hφk hL hperf h60
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxO⟩ := Subgroup.mem_inf.mp hx
  rw [← range_l1Map hL] at hxL
  obtain ⟨l, rfl⟩ := hxL
  have hφx : φ (l1Map hL l) = 1 := by rw [← MonoidHom.mem_ker, hφk]; exact hxO
  have hl : l ∈ CFSG.pCore 2 ↥L₁ := by
    rw [← hker, MonoidHom.mem_ker, chi_apply, hφx, map_one]
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (⟨l, hl⟩ : ↥(CFSG.pCore 2 ↥L₁))
  have h1 : (l1Map hL l) ^ 2 ^ n = 1 := by
    rw [← map_pow]
    have : l ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [this, map_one]
  have h2 : (l1Map hL l) ^ Nat.card (CFSG.oddCore (KBar K)) = 1 := by
    have := pow_card_eq_one' (G := ↥(CFSG.oddCore (KBar K))) (x := ⟨_, hxO⟩)
    have h3 := congrArg Subtype.val this
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h3
  have hcop : Nat.Coprime (2 ^ n) (Nat.card (CFSG.oddCore (KBar K))) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (Quasithin.A312.odd_card_oddCore _))
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hcop.gcd_eq_one, pow_one] at this
  exact Subgroup.mem_bot.mpr this

theorem eq_of_phi_eq (hp5 : 5 ≤ p) {φ : KBar K →* SL(2, ZMod p)}
    (hφk : φ.ker = CFSG.oddCore (KBar K)) (hL : L₁ ≤ K) (hperf : ⁅L₁, L₁⁆ = L₁)
    (h60 : (CFSG.pCore 2 ↥L₁).index = 60) {a b : KBar K} (ha : a ∈ l1Bar K L₁)
    (hb : b ∈ l1Bar K L₁) (hab : φ a = φ b) : a = b := by
  have hm : a⁻¹ * b ∈ l1Bar K L₁ ⊓ CFSG.oddCore (KBar K) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
    rw [← hφk, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  rw [l1Bar_inf_oddCore hp5 hφk hL hperf h60, Subgroup.mem_bot] at hm
  exact (inv_mul_eq_one.mp hm)

theorem exists_s (hp5 : 5 ≤ p) {φ : KBar K →* SL(2, ZMod p)}
    (hφk : φ.ker = CFSG.oddCore (KBar K)) (hL : L₁ ≤ K) (hperf : ⁅L₁, L₁⁆ = L₁)
    (h60 : (CFSG.pCore 2 ↥L₁).index = 60) :
    ∃ s ∈ l1Bar K L₁, φ s = -1 ∧ (∀ x ∈ l1Bar K L₁, s * x = x * s) ∧
      ∀ l : ↥L₁, l ∈ CFSG.pCore 2 ↥L₁ → l1Map hL l = 1 ∨ l1Map hL l = s := by
  obtain ⟨hker, -⟩ := chi_spec hp5 hφk hL hperf h60
  obtain ⟨hneg, -⟩ := range_spec hp5 hφk hL hperf h60
  have h2 := two_ne_zero_zmod hp5
  obtain ⟨l₀, hl₀⟩ := hneg
  have hl₀' : φ (l1Map hL l₀) = -1 := hl₀
  refine ⟨l1Map hL l₀, l1Map_mem hL l₀, hl₀', fun x hx => ?_, fun l hl => ?_⟩
  · apply eq_of_phi_eq hp5 hφk hL hperf h60 (mul_mem (l1Map_mem hL l₀) hx)
      (mul_mem hx (l1Map_mem hL l₀))
    rw [map_mul, map_mul, hl₀', neg_one_mul, mul_neg_one]
  · have hc : φ (l1Map hL l) ∈ Subgroup.center SL(2, ZMod p) := by
      have : chi hL φ l = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hl
      rw [chi_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    rcases (mem_center_iff h2).mp hc with h | h
    · left
      apply eq_of_phi_eq hp5 hφk hL hperf h60 (l1Map_mem hL l) (one_mem _)
      rw [h, map_one]
    · right
      apply eq_of_phi_eq hp5 hφk hL hperf h60 (l1Map_mem hL l) (l1Map_mem hL l₀)
      rw [h, hl₀']

theorem aut_eq_self_of_comm (hp5 : 5 ≤ p) {φ : KBar K →* SL(2, ZMod p)}
    (hφk : φ.ker = CFSG.oddCore (KBar K)) (hL : L₁ ≤ K) (hperf : ⁅L₁, L₁⁆ = L₁)
    (h60 : (CFSG.pCore 2 ↥L₁).index = 60) {r : G} (hrK : r ∈ Subgroup.normalizer (K : Set G))
    (hr : ∀ l ∈ L₁, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁) :
    ∀ x ∈ l1Bar K L₁, aut K ⟨r, hrK⟩ x = x := by
  obtain ⟨s, -, -, hsc, hO⟩ := exists_s hp5 hφk hL hperf h60
  set α := aut K ⟨r, hrK⟩ with hα
  have key : ∀ l : ↥L₁, ∃ c : ↥L₁, c ∈ CFSG.pCore 2 ↥L₁ ∧
      α (l1Map hL l) = l1Map hL c * l1Map hL l := by
    intro l
    have hmem := hr l l.2
    refine ⟨⟨_, Subgroup.map_subtype_le _ hmem⟩, ?_, ?_⟩
    · exact (Subgroup.mem_map_iff_mem L₁.subtype_injective).1 hmem
    · rw [l1Map_apply, l1Map_apply, hα, aut_mk, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [SecG.conjK_apply_coe, Subgroup.coe_mul]
      group
  have hmap : ∀ x ∈ l1Bar K L₁, α x ∈ l1Bar K L₁ := by
    intro x hx
    rw [← range_l1Map hL] at hx
    obtain ⟨l, rfl⟩ := hx
    obtain ⟨c, -, hc⟩ := key l
    rw [hc]
    exact mul_mem (l1Map_mem hL c) (l1Map_mem hL l)
  have heq : (l1Bar K L₁).map α.toMonoidHom = l1Bar K L₁ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hmap x hx
    · exact (Subgroup.card_map_of_injective
        (show Function.Injective α.toMonoidHom from α.injective)).ge
  let β : MulAut ↥(l1Bar K L₁) := (α.subgroupMap (l1Bar K L₁)).trans (MulEquiv.subgroupCongr heq)
  have hβ : ∀ y : ↥(l1Bar K L₁), ((β y : ↥(l1Bar K L₁)) : KBar K) = α y := fun y => rfl
  have hL₁p : Group.IsPerfect ↥L₁ := Subgroup.isPerfect_iff.mpr hperf
  have hperfL : ⁅l1Bar K L₁, l1Bar K L₁⁆ = l1Bar K L₁ := by
    have : Group.IsPerfect ↥(l1Map hL).range :=
      Group.IsPerfect.ofSurjective (l1Map hL).rangeRestrict_surjective
    have h := Subgroup.isPerfect_iff.mp this
    rwa [range_l1Map hL] at h
  have : Group.IsPerfect ↥(l1Bar K L₁) := Subgroup.isPerfect_iff.mpr hperfL
  have hβ1 : β = 1 := by
    refine O5.eq_one_of_mul_inv_mem_center β fun y => ?_
    obtain ⟨x, hx⟩ := y
    have hx' := hx
    rw [← range_l1Map hL] at hx'
    obtain ⟨l, rfl⟩ := hx'
    obtain ⟨c, hc, hce⟩ := key l
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hβ, hce, mul_inv_cancel_right]
    rcases hO c hc with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact (hsc z z.2).symm
  intro x hx
  have := congrArg (fun γ : MulAut ↥(l1Bar K L₁) => ((γ ⟨x, hx⟩ : ↥(l1Bar K L₁)) : KBar K)) hβ1
  simpa [hβ] using this

end Struct

section Sec

open SecG.Bar

variable {G : Type} [Group G] {K : Subgroup G}

theorem mem_sectionCentralizer_of_aut {a : G} (ha : a ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ x : KBar K, aut K ⟨a, ha⟩ x = x) : a ∈ sectionCentralizer K (pCoreOf 2 K) := by
  refine ⟨ha, LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K ha, fun x hx => ?_⟩
  have h1 := comm_mem_of_aut_eq_one (MulEquiv.ext h) x hx
  show _ ∈ (CFSG.Open.pCore 2 ↥K).map K.subtype
  assumption

theorem mem_center_of_mem_sectionCentralizer {y : G} (hyK : y ∈ K)
    (hy : y ∈ sectionCentralizer K (pCoreOf 2 K)) :
    ((⟨y, hyK⟩ : ↥K) : KBar K) ∈ Subgroup.center (KBar K) := by
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 := hy.2.2 x x.2
  have h2 : y * x * y⁻¹ * (x : G)⁻¹ ∈ (CFSG.pCore 2 ↥K).map K.subtype := by
    have : pCoreOf 2 K = (CFSG.Open.pCore 2 ↥K).map K.subtype := rfl
    rw [this] at h1
    exact h1
  obtain ⟨c, hc, hce⟩ := h2
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have : (x * ⟨y, hyK⟩)⁻¹ * (⟨y, hyK⟩ * x) =
      (⟨y, hyK⟩ * x)⁻¹ * c * ((⟨y, hyK⟩ * x)⁻¹)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [show ((c : ↥K) : G) = y * x * y⁻¹ * (x : G)⁻¹ from hce]
    group
  rw [this]
  exact (CFSG.pCore_normal).conj_mem _ hc _

end Sec

end CFSG.Quasithin.Vol2.Ch11.SecD.O6S
