module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.C124Dict
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem valHom_range {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    (valHom hV).range = V := by
  ext g
  constructor
  · rintro ⟨w, rfl⟩
    exact w.val_mem
  · intro hg
    exact ⟨⟨g, hg⟩, rfl⟩

theorem toG_top {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    toG hV (⊤ : Subgroup (IntMod V hV)) = V := by
  rw [toG, Subgroup.map_top, valHom_range hV]

theorem toG_comap {V : Subgroup G} (hV : IsElemAbelian 2 V) {H : Subgroup G} (hH : H ≤ V) :
    toG hV (H.comap (valHom hV)) = H := by
  rw [toG, Subgroup.map_comap_eq_self]
  rw [valHom_range hV]
  exact hH

end CFSG.Quasithin.C124

namespace CFSG.Quasithin

namespace E3

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_twoElement_convI_eq {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {t : MulAut (IntMod V hV)} (ht : t ∈ autI hV ⊤) (ht2 : orderOf t = 2) :
    ∃ (x : G) (hx : x ∈ Subgroup.normalizer (V : Set G)),
      (∃ k : ℕ, orderOf x = 2 ^ k) ∧ convI hV ⟨x, hx⟩ = t := by
  obtain ⟨g, -, hgt⟩ := (mem_autI hV).1 ht
  have hg0 : orderOf (g : G) ≠ 0 := (orderOf_pos (g : G)).ne'
  obtain ⟨a, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hg0 2 Nat.prime_two.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hm_odd : Odd m :=
    Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  let x : G := (g : G) ^ m
  have hxN : x ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.pow_mem (Subgroup.normalizer (V : Set G)) g.2 m
  have hx2 : ∃ k : ℕ, orderOf x = 2 ^ k := by
    refine ⟨a, ?_⟩
    have hgcd : Nat.gcd (orderOf (g : G)) m = m := by
      rw [he]
      exact Nat.gcd_eq_right (Nat.dvd_mul_left m (2 ^ a))
    have hpow := orderOf_pow (x := (g : G)) (n := m)
    rw [hgcd] at hpow
    rw [show orderOf x = orderOf ((g : G) ^ m) from rfl, hpow, he]
    exact Nat.mul_div_left (2 ^ a) (Nat.pos_of_ne_zero hm0)
  refine ⟨x, hxN, hx2, ?_⟩
  have hsub : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) = g ^ m := by
    ext
    rfl
  rw [hsub, map_pow, hgt]
  have ht2pow : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  obtain ⟨c, hc⟩ := hm_odd
  rw [hc, pow_add, pow_mul, ht2pow, one_pow, one_mul, pow_one]

theorem pRank_le_rk {H : Subgroup G} (hH : IsElemAbelian 2 H) :
    CFSG.Open.pRank 2 H ≤ CFSG.Quasithin.rk ↥H := by
  have hcard : Nat.card ↥H = 2 ^ CFSG.Quasithin.rk ↥H :=
    CFSG.Quasithin.card_eq_two_pow_of_isPGroup
      (CFSG.Open.IsElemAbelian.isPGroup hH)
  refine CFSG.SectionRank.pRank_le (p := 2) (by norm_num) fun E hEH hE => ?_
  have hcardE : Nat.card ↥E = 2 ^ CFSG.Quasithin.rk ↥E :=
    CFSG.Quasithin.card_eq_two_pow_of_isPGroup
      (CFSG.Open.IsElemAbelian.isPGroup hE)
  have hle : Nat.card ↥E ≤ Nat.card ↥H := Subgroup.card_le_of_le hEH
  have hpow : 2 ^ CFSG.Quasithin.rk ↥E ≤ 2 ^ CFSG.Quasithin.rk ↥H :=
    calc 2 ^ CFSG.Quasithin.rk ↥E = Nat.card ↥E := hcardE.symm
      _ ≤ Nat.card ↥H := hle
      _ = 2 ^ CFSG.Quasithin.rk ↥H := hcard
  rw [hcardE]
  exact hpow

private theorem le_mParam_of_tiFamily_mod {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {ι : Type*} [Nonempty ι] (Y : ι → Subgroup (IntMod V hV))
    (hspan : (⊤ : Subgroup (IntMod V hV)) = ⨆ i, Y i)
    (hTI : ∀ (i : ι) (g : G),
      (CFSG.Quasithin.C124.toG hV (Y i)) ⊓
          CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.C124.toG hV (Y i)) g ≠ ⊥ →
        CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.C124.toG hV (Y i)) g =
          (CFSG.Quasithin.C124.toG hV (Y i)))
    (hCN : ∀ (i : ι) (x : G),
      x ∈ Subgroup.normalizer ((CFSG.Quasithin.C124.toG hV (Y i)) : Set G) →
      (∃ k : ℕ, orderOf x = 2 ^ k) →
      ∀ y ∈ (CFSG.Quasithin.C124.toG hV (Y i)), x * y * x⁻¹ = y)
    (k : ℕ) (hk : ∀ i, k ≤ rk ↥(Y i)) :
    k ≤ mParam (autI hV ⊤) := by
  unfold mParam
  split_ifs with heven
  · obtain ⟨t₀, ht₀⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(autI hV ⊤)) 2 (even_iff_two_dvd.1 heven)
    have ht₀2 : orderOf (t₀ : MulAut (IntMod V hV)) = 2 := by
      rw [Subgroup.orderOf_coe, ht₀]
    refine le_csInf ⟨_, (t₀ : MulAut (IntMod V hV)), t₀.2, ht₀2, rfl⟩ ?_
    rintro n ⟨t, ht, ht2, rfl⟩
    obtain ⟨x, hxN, ⟨j, hxj⟩, hxt⟩ := exists_twoElement_convI_eq hV ht ht2
    have hsub : (Subgroup.zpowers x).subgroupOf (Subgroup.normalizer (V : Set G)) =
        Subgroup.zpowers ⟨x, hxN⟩ := by
      ext y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hAeq : autI hV (Subgroup.zpowers x) = Subgroup.zpowers t := by
      rw [autI, hsub, MonoidHom.map_zpowers, hxt]
    have hfix_iff : ∀ v : IntMod V hV,
        v ∈ fixV (Subgroup.zpowers t) ↔
          v.val ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
      intro v
      rw [← hAeq, mem_fixV_autI hV (Subgroup.zpowers_le.mpr hxN)]
    have hex : ∃ i, ¬ Y i ≤ fixV (Subgroup.zpowers t) := by
      by_contra h
      push Not at h
      have hle : (⊤ : Subgroup (IntMod V hV)) ≤ fixV (Subgroup.zpowers t) := by
        rw [hspan]
        exact iSup_le h
      have htop : fixV (Subgroup.zpowers t) = ⊤ := top_le_iff.mp hle
      have ht1 : t = 1 := by
        ext v
        have hv : v ∈ fixV (Subgroup.zpowers t) := htop ▸ Subgroup.mem_top v
        exact (mem_fixV.mp hv) t (Subgroup.mem_zpowers t)
      rw [ht1, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    obtain ⟨i, hi⟩ := hex
    have hxnot : x ∉ Subgroup.normalizer ((CFSG.Quasithin.C124.toG hV (Y i)) : Set G) := by
      intro hxnorm
      apply hi
      intro v hv
      rw [hfix_iff]
      have hvG : v.val ∈ CFSG.Quasithin.C124.toG hV (Y i) :=
        (CFSG.Quasithin.C124.mem_toG_iff_of_mem hV v).2 hv
      have hcomm := hCN i x hxnorm ⟨j, hxj⟩ v.val hvG
      have hxcent : x ∈ Subgroup.centralizer ({v.val} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x * v.val = (x * v.val * x⁻¹) * x := by group
          _ = v.val * x := by rw [hcomm]
      have hcommx : v.val * x = x * v.val :=
        (Subgroup.mem_centralizer_iff.mp hxcent) v.val rfl
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      change a ∈ Subgroup.zpowers x at ha
      rw [Subgroup.mem_zpowers_iff] at ha
      obtain ⟨n, rfl⟩ := ha
      have hcommute : Commute x v.val := by
        rw [commute_iff_eq]
        exact hcommx.symm
      exact (hcommute.zpow_left n).eq
    have hne : (CFSG.Quasithin.C124.toG hV (Y i)) ⊓
        CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.C124.toG hV (Y i)) x = ⊥ := by
      by_contra hne
      exact hxnot (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mp (hTI i x hne))
    have hinf : Y i ⊓ fixV (Subgroup.zpowers t) = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have hvG : v.val ∈ CFSG.Quasithin.C124.toG hV (Y i) :=
        (CFSG.Quasithin.C124.mem_toG_iff_of_mem hV v).2 hv.1
      have hvc : v.val ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
        (hfix_iff v).mp hv.2
      have hmem : v.val ∈ (CFSG.Quasithin.C124.toG hV (Y i)) ⊓
          CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.C124.toG hV (Y i)) x := by
        refine ⟨hvG, ?_⟩
        change v.val ∈ CFSG.Quasithin.conjSubgroup
          (CFSG.Quasithin.C124.toG hV (Y i)) x
        rw [CFSG.Quasithin.mem_conjSubgroup_iff]
        have hxc : x * v.val = v.val * x := by
          have h0 := (Subgroup.mem_centralizer_iff.mp hvc) x (Subgroup.mem_zpowers x)
          exact h0
        have hxcv : x * v.val * x⁻¹ = v.val := by
          calc x * v.val * x⁻¹ = v.val * x * x⁻¹ := by rw [hxc]
            _ = v.val := by group
        rw [hxcv]
        exact hvG
      rw [hne] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    have hdim : rk ↥(Y i) ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
      have hsup := rk_sup_add_rk_inf (Y i) (fixV (Subgroup.zpowers t))
      rw [hinf, rk_bot, add_zero] at hsup
      have htop : rk (⊤ : Subgroup (IntMod V hV)) = rk (IntMod V hV) := rk_top
      have hle : rk ↥(Y i ⊔ fixV (Subgroup.zpowers t)) ≤ rk (IntMod V hV) := by
        have h1 : rk ↥(Y i ⊔ fixV (Subgroup.zpowers t)) ≤
            rk (⊤ : Subgroup (IntMod V hV)) := rk_mono le_top
        rwa [htop] at h1
      have hY : rk ↥(Y i) + rk (fixV (Subgroup.zpowers t)) ≤ rk (IntMod V hV) := by
        rw [← hsup]
        exact hle
      have hC : rkIdx (fixV (Subgroup.zpowers t)) =
          rk (IntMod V hV) - rk (fixV (Subgroup.zpowers t)) := by
        have := rk_add_rkIdx (fixV (Subgroup.zpowers t))
        omega
      omega
    exact (hk i).trans hdim
  · obtain ⟨i⟩ := ‹Nonempty ι›
    have htop : rk (⊤ : Subgroup (IntMod V hV)) = rk (IntMod V hV) := rk_top
    have hle : rk ↥(Y i) ≤ rk (IntMod V hV) := by
      have h1 : rk ↥(Y i) ≤ rk (⊤ : Subgroup (IntMod V hV)) :=
        rk_mono (le_top : Y i ≤ ⊤)
      rwa [htop] at h1
    exact (hk i).trans hle

theorem le_mParam_of_tiFamily {V : Subgroup G} (hV : IsElemAbelian 2 V)
    {ι : Type*} [Nonempty ι] (Y : ι → Subgroup G)
    (hYle : ∀ i, Y i ≤ V)
    (hspan : V = ⨆ i, Y i)
    (hTI : ∀ (i : ι) (g : G), Y i ⊓ CFSG.Quasithin.conjSubgroup (Y i) g ≠ ⊥ →
      CFSG.Quasithin.conjSubgroup (Y i) g = Y i)
    (hCN : ∀ (i : ι) (x : G), x ∈ Subgroup.normalizer (Y i : Set G) →
      (∃ k : ℕ, orderOf x = 2 ^ k) → ∀ y ∈ Y i, x * y * x⁻¹ = y)
    (k : ℕ) (hk : ∀ i, k ≤ CFSG.Open.pRank 2 (Y i)) :
    k ≤ mParam (autI hV ⊤) := by
  let Ymod : ι → Subgroup (IntMod V hV) := fun i => (Y i).comap (CFSG.Quasithin.C124.valHom hV)
  have hYmod : ∀ i, CFSG.Quasithin.C124.toG hV (Ymod i) = Y i :=
    fun i => CFSG.Quasithin.C124.toG_comap hV (hYle i)
  have hspanMod : (⊤ : Subgroup (IntMod V hV)) = ⨆ i, Ymod i := by
    apply Subgroup.map_injective (CFSG.Quasithin.C124.valHom_injective hV)
    rw [Subgroup.map_iSup]
    simp_rw [show ∀ i, (Ymod i).map (CFSG.Quasithin.C124.valHom hV) = Y i from hYmod]
    have htop : (⊤ : Subgroup (IntMod V hV)).map (CFSG.Quasithin.C124.valHom hV) = V :=
      CFSG.Quasithin.C124.toG_top hV
    rw [htop]
    exact hspan
  have hTImod : ∀ (i : ι) (g : G),
      CFSG.Quasithin.C124.toG hV (Ymod i) ⊓
          CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.C124.toG hV (Ymod i)) g ≠ ⊥ →
        CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.C124.toG hV (Ymod i)) g =
          CFSG.Quasithin.C124.toG hV (Ymod i) := by
    intro i g hne
    rw [hYmod i] at hne ⊢
    exact hTI i g hne
  have hCNmod : ∀ (i : ι) (x : G),
      x ∈ Subgroup.normalizer (CFSG.Quasithin.C124.toG hV (Ymod i) : Set G) →
      (∃ k : ℕ, orderOf x = 2 ^ k) →
      ∀ y ∈ CFSG.Quasithin.C124.toG hV (Ymod i), x * y * x⁻¹ = y := by
    intro i x hxN hx2
    rw [hYmod i] at hxN ⊢
    exact hCN i x hxN hx2
  have hkmod : ∀ i, k ≤ rk ↥(Ymod i) := by
    intro i
    have hYel : IsElemAbelian 2 (Y i) := CFSG.Open.IsElemAbelian.mono hV (hYle i)
    have hcard : Nat.card ↥(Ymod i) = Nat.card ↥(Y i) := by
      have h := Subgroup.card_map_of_injective (K := Ymod i)
        (CFSG.Quasithin.C124.valHom_injective hV)
      rw [show (Ymod i).map (CFSG.Quasithin.C124.valHom hV) = Y i from hYmod i] at h
      exact h.symm
    have hrk : rk ↥(Ymod i) = rk ↥(Y i) := by
      unfold rk
      rw [hcard]
    rw [hrk]
    exact (hk i).trans (pRank_le_rk hYel)
  exact le_mParam_of_tiFamily_mod hV Ymod hspanMod hTImod hCNmod k hkmod

end E3

end CFSG.Quasithin
