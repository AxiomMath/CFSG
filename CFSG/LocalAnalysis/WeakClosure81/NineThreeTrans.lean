module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nineThree_dihedral_mid {Γ : Type*} [Group Γ] {f g' : Γ} (hf : f * f = 1)
    (hg : g' * g' = 1) (hodd : Odd (orderOf (f * g'))) :
    ∃ s : ℕ, 2 * s = orderOf (f * g') + 1 ∧ (f * (f * g') ^ s) * (f * (f * g') ^ s) = 1 ∧
      (f * (f * g') ^ s) * f * (f * (f * g') ^ s) = g' := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k + 1, by omega, ?_⟩
  set t := f * g' with ht
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have hgi : g'⁻¹ = g' := inv_eq_of_mul_eq_one_right hg
  have hft : f * t * f = t⁻¹ := by
    rw [ht, mul_inv_rev, hfi, hgi]
    calc f * (f * g') * f = (f * f) * g' * f := by group
      _ = g' * f := by rw [hf, one_mul]
  have hftn : ∀ n : ℕ, f * t ^ n * f = (t ^ n)⁻¹ := by
    intro n
    have h1 : f * t ^ n * f⁻¹ = (f * t * f⁻¹) ^ n := conj_pow.symm
    rw [hfi] at h1
    rw [h1, hft, inv_pow]
  have h2 : t ^ (2 * (k + 1)) = t := by
    rw [show 2 * (k + 1) = orderOf t + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  have h3 : t ^ (2 * (k + 1)) = t ^ (k + 1) * t ^ (k + 1) := by rw [two_mul, pow_add]
  constructor
  · calc (f * t ^ (k + 1)) * (f * t ^ (k + 1)) = (f * t ^ (k + 1) * f) * t ^ (k + 1) := by group
      _ = 1 := by rw [hftn, inv_mul_cancel]
  · calc (f * t ^ (k + 1)) * f * (f * t ^ (k + 1))
        = f * (t ^ (k + 1) * (f * f) * t ^ (k + 1)) := by group
      _ = f * (t ^ (k + 1) * t ^ (k + 1)) := by rw [hf, mul_one]
      _ = f * t := by rw [← h3, h2]
      _ = g' := by rw [ht, ← mul_assoc, hf, one_mul]

theorem nineThree_core_calc {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
    {b b' x β β' f t : Γ} (hb : b * b = 1) (hbb' : b * b' ∈ N)
    (hbx : b * x * b⁻¹ * x ∈ N) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hxN : x ∉ N)
    (hxp : x ^ p ∈ N)
    (hβ : β = x * b * x⁻¹) (hβ' : β' = x * b' * x⁻¹) (hf : f = b * β * b) (ht : t = f * β') :
    (∀ k : ℕ, t ^ (2 ^ k) ≠ 1) ∧
      ∀ m s : ℕ, t ^ m = 1 → 2 * s = m + 1 → b * (f * t ^ s) ∈ N := by
  classical
  let π : Γ →* Γ ⧸ N := QuotientGroup.mk' N
  have ha2 : π b * π b = 1 := by rw [← map_mul, hb, map_one]
  have hai : (π b)⁻¹ = π b := inv_eq_of_mul_eq_one_right ha2
  have ha' : π b' = π b := by
    have h1 : π b * π b' = 1 := by
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr hbb'
    rw [eq_inv_of_mul_eq_one_right h1, hai]
  have hay : π b * π x * π b = (π x)⁻¹ := by
    have h : π (b * x * b⁻¹ * x) = 1 := (QuotientGroup.eq_one_iff _).mpr hbx
    rw [map_mul, map_mul, map_mul, map_inv, hai] at h
    exact mul_eq_one_iff_eq_inv.mp h
  have hay' : π b * (π x)⁻¹ * π b = π x := by
    have h := congrArg (fun z => z⁻¹) hay
    simp only [mul_inv_rev, hai, inv_inv] at h
    simpa [mul_assoc] using h
  subst hβ hβ' hf ht
  have hπt : π (b * (x * b * x⁻¹) * b * (x * b' * x⁻¹)) = (π x ^ 4)⁻¹ := by
    simp only [map_mul, map_inv, ha']
    calc π b * (π x * π b * (π x)⁻¹) * π b * (π x * π b * (π x)⁻¹)
        = (π b * π x * π b) * (π x)⁻¹ * (π b * π x * π b) * (π x)⁻¹ := by group
      _ = (π x)⁻¹ * (π x)⁻¹ * (π x)⁻¹ * (π x)⁻¹ := by rw [hay]
      _ = (π x ^ 4)⁻¹ := by group
  have hx1 : π x ≠ 1 := fun h1 => hxN ((QuotientGroup.eq_one_iff _).mp h1)
  have hodd : Odd (orderOf (π x)) := by
    have hpx : (π x) ^ p = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hxp
    haveI : Fact p.Prime := ⟨hp⟩
    rw [orderOf_eq_prime hpx hx1]
    exact hp.odd_of_ne_two hp2
  have hodd2 : Nat.Coprime (orderOf (π x)) 2 := Nat.coprime_two_right.2 hodd
  refine ⟨fun k hk => ?_, fun m s hm hs => ?_⟩
  · have h1 : ((π x ^ 4)⁻¹) ^ (2 ^ k) = 1 := by rw [← hπt, ← map_pow, hk, map_one]
    have h2 : π x ^ (4 * 2 ^ k) = 1 := by
      have h3 : (((π x ^ 4)⁻¹) ^ (2 ^ k))⁻¹ = 1 := by rw [h1, inv_one]
      rwa [inv_pow, inv_inv, ← pow_mul] at h3
    have h3 : orderOf (π x) ∣ 4 * 2 ^ k := orderOf_dvd_of_pow_eq_one h2
    have h4 : Nat.Coprime (orderOf (π x)) (4 * 2 ^ k) := by
      have : (4 : ℕ) * 2 ^ k = 2 ^ (k + 2) := by ring
      rw [this]
      exact hodd2.pow_right _
    exact hx1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h4 h3))
  · have hm' : ((π x ^ 4)⁻¹) ^ m = 1 := by rw [← hπt, ← map_pow, hm, map_one]
    have hy4 : π x ^ (4 * m) = 1 := by
      have h3 : (((π x ^ 4)⁻¹) ^ m)⁻¹ = 1 := by rw [hm', inv_one]
      rwa [inv_pow, inv_inv, ← pow_mul] at h3
    have hym : π x ^ m = 1 := by
      have h3 : orderOf (π x) ∣ 4 * m := orderOf_dvd_of_pow_eq_one hy4
      have h4 : Nat.Coprime (orderOf (π x)) 4 := by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]
        exact hodd2.pow_right _
      exact orderOf_dvd_iff_pow_eq_one.mp (h4.dvd_of_dvd_mul_left h3)
    have hf' : π b * (π b * (π x * π b * (π x)⁻¹) * π b) = π x ^ 2 := by
      calc π b * (π b * (π x * π b * (π x)⁻¹) * π b)
          = (π b * π b) * (π x * (π b * (π x)⁻¹ * π b)) := by group
        _ = π x * π x := by rw [ha2, hay', one_mul]
        _ = π x ^ 2 := (pow_two _).symm
    have e1 : π (b * (b * (x * b * x⁻¹) * b * (b * (x * b * x⁻¹) * b * (x * b' * x⁻¹)) ^ s)) =
        π x ^ 2 * ((π x ^ 4)⁻¹) ^ s := by
      rw [map_mul, map_mul, map_pow, hπt]
      simp only [map_mul, map_inv, ha'] at hf' ⊢
      rw [← mul_assoc, hf']
    have e2 : π x ^ 2 * ((π x ^ 4)⁻¹) ^ s = 1 := by
      have h4s : 4 * s = 2 + 2 * m := by omega
      have h2m : π x ^ (2 * m) = 1 := by rw [pow_mul', hym, one_pow]
      rw [inv_pow, ← pow_mul, h4s, pow_add, h2m, mul_one, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp (e1.trans e2)

private theorem nineThree_inv_mul_mem_of_relIndex_two {L K' : Subgroup G}
    (hrel : L.relIndex K' = 2) {a b : G} (ha : a ∈ K') (hb : b ∈ K') (haL : a ∉ L)
    (hbL : b ∉ L) : a⁻¹ * b ∈ L := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf K') hrel
    (a := (⟨a, ha⟩ : K')⁻¹) (b := ⟨b, hb⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haL hbL)
  exact Subgroup.mem_subgroupOf.1 key

theorem nineThree_pCoreOf_subgroupOf_normal (K : Subgroup G) :
    ((pCoreOf 2 K).subgroupOf K).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 K)]
  intro r k hr hk
  exact (Nine3Core.mem_pCoreOf_conj_iff K hk).mp hr

namespace Nine3Core

theorem nineOmegaIn_le_K (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) : B ≤ K :=
  hB.2.trans h.S_le_K

theorem nineOmegaIn_isElemAbelian (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) : IsElemAbelian 2 B := by
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hB.1
  exact isElemAbelian_conjSubgroup' h.hyp7.1 g

theorem exists_not_mem_pCoreOf (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) : ∃ b ∈ B, b ∉ pCoreOf 2 K := by
  by_contra hcon
  have hle : B ≤ pCoreOf 2 K := fun b hb => by
    by_contra hbR
    exact hcon ⟨b, hb, hbR⟩
  have h1 : (pCoreOf 2 K).relIndex B = 1 := Subgroup.relIndex_eq_one.2 hle
  have h2 := nine_two_relIndex h.hyp7 h.rk_gt h.hyp hB
  omega

theorem nineOmegaIn_inv_mul_mem (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) {b₁ b₂ : G} (h1 : b₁ ∈ B) (h2 : b₂ ∈ B)
    (h1R : b₁ ∉ pCoreOf 2 K) (h2R : b₂ ∉ pCoreOf 2 K) : b₁⁻¹ * b₂ ∈ pCoreOf 2 K :=
  nineThree_inv_mul_mem_of_relIndex_two (nine_two_relIndex h.hyp7 h.rk_gt h.hyp hB) h1 h2 h1R h2R

theorem nineOmegaIn_inv_mul_mem_cross (h : Nine3Core V T A K S X p) {B B' : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) (hB' : B' ∈ nineOmegaIn V K S) {b b' : G} (hb : b ∈ B)
    (hb' : b' ∈ B') (hbR : b ∉ pCoreOf 2 K) (hb'R : b' ∉ pCoreOf 2 K) :
    b⁻¹ * b' ∈ pCoreOf 2 K := by
  obtain ⟨r, hr, rfl⟩ := nine_two_two_R h.hyp7 h.rk_gt h.hyp hB hB'
  have hb'' : r * b' * r⁻¹ ∈ B := mem_conjSubgroup_iff.mp hb'
  have hrK : r ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hr
  have hb'K : b' ∈ K := by
    have h2 : r⁻¹ * (r * b' * r⁻¹) * r ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem hrK) (h.nineOmegaIn_le_K hB hb'')) hrK
    simpa [mul_assoc] using h2
  have hnot : r * b' * r⁻¹ ∉ pCoreOf 2 K := fun hh => hb'R (by
    have := (pCoreOf 2 K).mul_mem ((pCoreOf 2 K).mul_mem ((pCoreOf 2 K).inv_mem hr) hh) hr
    simpa [mul_assoc] using this)
  have h1 := h.nineOmegaIn_inv_mul_mem hB hb hb'' hbR hnot
  have h3 : b'⁻¹ * r⁻¹ * b' ∈ pCoreOf 2 K := by
    have := (mem_pCoreOf_conj_iff K (K.inv_mem hb'K)).mp ((pCoreOf 2 K).inv_mem hr)
    simpa using this
  have h2 : r * b'⁻¹ * r⁻¹ * b' ∈ pCoreOf 2 K := by
    have := (pCoreOf 2 K).mul_mem hr h3
    simpa [mul_assoc] using this
  have e : b⁻¹ * b' = (b⁻¹ * (r * b' * r⁻¹)) * (r * b'⁻¹ * r⁻¹ * b') := by group
  rw [e]
  exact (pCoreOf 2 K).mul_mem h1 h2

theorem conj_inv_mul_mem (h : Nine3Core V T A K S X p) {B : Subgroup G}
    (hB : B ∈ nineOmegaIn V K S) {g : G} (hg : g ∈ K) {u v : G}
    (hu : u ∈ conjSubgroup B g) (hv : v ∈ conjSubgroup B g)
    (huR : u ∉ pCoreOf 2 K) (hvR : v ∉ pCoreOf 2 K) : u⁻¹ * v ∈ pCoreOf 2 K := by
  have hu' : g * u * g⁻¹ ∈ B := mem_conjSubgroup_iff.mp hu
  have hv' : g * v * g⁻¹ ∈ B := mem_conjSubgroup_iff.mp hv
  have hmem : ∀ w : G, g * w * g⁻¹ ∈ pCoreOf 2 K ↔ w ∈ pCoreOf 2 K := fun w =>
    (mem_pCoreOf_conj_iff K hg).symm
  have h1 := h.nineOmegaIn_inv_mul_mem hB hu' hv' (fun hh => huR ((hmem u).mp hh))
    (fun hh => hvR ((hmem v).mp hh))
  have e : (g * u * g⁻¹)⁻¹ * (g * v * g⁻¹) = g * (u⁻¹ * v) * g⁻¹ := by group
  rw [e] at h1
  exact (hmem _).mp h1

theorem nineD_transitive (h : Nine3Core V T A K S X p) (hx : x ∈ X) (hx1 : x ≠ 1)
    {B B' : Subgroup G} (hB : B ∈ nineOmegaIn V K S) (hB' : B' ∈ nineOmegaIn V K S) :
    ∃ d ∈ nineD K A x, B' = conjSubgroup B d := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2p := h.hyp.base.toTwoPTwo
  have hxK : x ∈ K := h2p.sylowP.le hx
  have hEK : nineE V K ≤ K :=
    (nineE_le_pCoreOf V K).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hxR : x ∉ pCoreOf 2 K := by
    intro hxR
    have hbot : X ⊓ pCoreOf 2 K = ⊥ :=
      TwoPTwo.sylowP_inf_pCoreOf h.hyp.base.toTwoPTwoIrred.toTwoPTwo
    have hmem : x ∈ X ⊓ pCoreOf 2 K := ⟨hx, hxR⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hxp : x ^ p = 1 := by
    have h1 : (⟨x, hx⟩ : ↥X) ^ Nat.card ↥X = 1 := pow_card_eq_one'
    rw [h.card] at h1
    simpa using congrArg Subtype.val h1
  obtain ⟨b, hbB, hbR⟩ := h.exists_not_mem_pCoreOf hB
  obtain ⟨b', hb'B', hb'R⟩ := h.exists_not_mem_pCoreOf hB'
  have hbK : b ∈ K := h.nineOmegaIn_le_K hB hbB
  have hb'K : b' ∈ K := h.nineOmegaIn_le_K hB' hb'B'
  have hbb : b * b = 1 := by
    have := (h.nineOmegaIn_isElemAbelian hB).2 b hbB
    rwa [pow_two] at this
  have hb'b' : b' * b' = 1 := by
    have := (h.nineOmegaIn_isElemAbelian hB').2 b' hb'B'
    rwa [pow_two] at this
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hb'i : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hb'b'
  have hbb' : b * b' ∈ pCoreOf 2 K := by
    have := h.nineOmegaIn_inv_mul_mem_cross hB hB' hbB hb'B' hbR hb'R
    rwa [hbi] at this
  have hinv : b * x * b⁻¹ * x ∈ pCoreOf 2 K :=
    nine_two_inv h.hyp7 h.rk_gt h.hyp hB hbB hbR hx
  haveI hN : ((pCoreOf 2 K).subgroupOf K).Normal := nineThree_pCoreOf_subgroupOf_normal K
  let bΓ : ↥K := ⟨b, hbK⟩
  let b'Γ : ↥K := ⟨b', hb'K⟩
  let xΓ : ↥K := ⟨x, hxK⟩
  have hcalc := nineThree_core_calc ((pCoreOf 2 K).subgroupOf K) (b := bΓ) (b' := b'Γ) (x := xΓ)
    (β := xΓ * bΓ * xΓ⁻¹) (β' := xΓ * b'Γ * xΓ⁻¹) (f := bΓ * (xΓ * bΓ * xΓ⁻¹) * bΓ)
    (t := bΓ * (xΓ * bΓ * xΓ⁻¹) * bΓ * (xΓ * b'Γ * xΓ⁻¹))
    (Subtype.ext hbb) (Subgroup.mem_subgroupOf.mpr hbb') (Subgroup.mem_subgroupOf.mpr hinv)
    h2p.prime h2p.odd (fun hh => hxR (Subgroup.mem_subgroupOf.mp hh))
    (Subgroup.mem_subgroupOf.mpr (by
      show ((xΓ ^ p : ↥K) : G) ∈ pCoreOf 2 K
      rw [Subgroup.coe_pow]
      show x ^ p ∈ pCoreOf 2 K
      rw [hxp]
      exact Subgroup.one_mem _)) rfl rfl rfl rfl
  obtain ⟨hno2, hmid2⟩ := hcalc
  set β : G := x * b * x⁻¹ with hβ
  set β' : G := x * b' * x⁻¹ with hβ'
  set f : G := b * β * b with hf
  set t : G := f * β' with ht
  have hno : ∀ k : ℕ, t ^ (2 ^ k) ≠ 1 := fun k hk =>
    hno2 k (Subtype.ext (by rw [Subgroup.coe_pow]; exact hk))
  have hmid : ∀ m s : ℕ, t ^ m = 1 → 2 * s = m + 1 → b * (f * t ^ s) ∈ pCoreOf 2 K :=
    fun m s hm hs => Subgroup.mem_subgroupOf.mp
      (hmid2 m s (Subtype.ext (by rw [Subgroup.coe_pow]; exact hm)) hs)
  have hββ : β * β = 1 := by
    calc β * β = x * (b * b) * x⁻¹ := by rw [hβ]; group
      _ = 1 := by rw [hbb]; group
  have hβ'β' : β' * β' = 1 := by
    calc β' * β' = x * (b' * b') * x⁻¹ := by rw [hβ']; group
      _ = 1 := by rw [hb'b']; group
  have hff : f * f = 1 := by
    calc f * f = b * (β * (b * b) * β) * b := by rw [hf]; group
      _ = 1 := by rw [hbb, mul_one, hββ, mul_one, hbb]
  have hU₁ : conjSubgroup B x⁻¹ ∈ omegaSet V K (nineE V K) :=
    conjSubgroup_mem_omegaSet hEK (nineE_subgroupOf_normal V K) hB.1 (K.inv_mem hxK)
  have hU₂ : conjSubgroup (conjSubgroup B x⁻¹) b ∈ omegaSet V K (nineE V K) :=
    conjSubgroup_mem_omegaSet hEK (nineE_subgroupOf_normal V K) hU₁ hbK
  have hU₃ : conjSubgroup B' x⁻¹ ∈ omegaSet V K (nineE V K) :=
    conjSubgroup_mem_omegaSet hEK (nineE_subgroupOf_normal V K) hB'.1 (K.inv_mem hxK)
  have hβmem : β ∈ conjSubgroup B x⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have : x⁻¹ * β * x⁻¹⁻¹ = b := by rw [hβ]; group
    rw [this]
    exact hbB
  have hβ'mem : β' ∈ conjSubgroup B' x⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have : x⁻¹ * β' * x⁻¹⁻¹ = b' := by rw [hβ']; group
    rw [this]
    exact hb'B'
  have hfmem : f ∈ conjSubgroup (conjSubgroup B x⁻¹) b := by
    rw [mem_conjSubgroup_iff]
    have : b * f * b⁻¹ = β := by
      rw [hf, hbi]
      calc b * (b * β * b) * b = (b * b) * β * (b * b) := by group
        _ = β := by rw [hbb, one_mul, mul_one]
    rw [this]
    exact hβmem
  have hβK : β ∈ K := K.mul_mem (K.mul_mem hxK hbK) (K.inv_mem hxK)
  have hβ'K : β' ∈ K := K.mul_mem (K.mul_mem hxK hb'K) (K.inv_mem hxK)
  have hfK : f ∈ K := K.mul_mem (K.mul_mem hbK hβK) hbK
  have hnot : ¬ IsPGroup 2 (Subgroup.closure ({f, β'} : Set G)) := by
    intro hP
    have htmem : t ∈ Subgroup.closure ({f, β'} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    obtain ⟨k, hk⟩ := hP ⟨t, htmem⟩
    exact hno k (by simpa using congrArg Subtype.val hk)
  have hodd : Odd (orderOf (f * β')) :=
    seven_three_A h.hyp7.1 h.hyp7.2.2 (isElemAbelian_nineE V K).1 hU₂ hU₃ hfmem hβ'mem hnot
  obtain ⟨s, hs, hc2, hcf⟩ := nineThree_dihedral_mid hff hβ'β' hodd
  set c₀ : G := f * (f * β') ^ s with hc₀
  have htK : t ∈ K := K.mul_mem hfK hβ'K
  have hc₀K : c₀ ∈ K := K.mul_mem hfK (K.pow_mem htK s)
  have hfc : Odd (orderOf (f * c₀)) := by
    have e : f * c₀ = (f * β') ^ s := by rw [hc₀, ← mul_assoc, hff, one_mul]
    rw [e]
    exact Odd.of_dvd_nat hodd (orderOf_pow_dvd s)
  obtain ⟨z, hz, hzf⟩ := exists_conj_inv_mul_of_involutions_odd hff hc2 hfc
  have hzK : z ∈ K := by
    have hcl : Subgroup.closure ({f, c₀} : Set G) ≤ K := by
      rw [Subgroup.closure_le]
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact hfK
      · exact hc₀K
    exact hcl hz
  set g₀ : G := x⁻¹ * b * z with hg₀
  have hg₀K : g₀ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hxK) hbK) hzK
  have hB₀conj : conjSubgroup (conjSubgroup (conjSubgroup B x⁻¹) b) z = conjSubgroup B g₀ := by
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, CFSG.Quasithin.conjSubgroup_conjSubgroup,
      hg₀, mul_assoc]
  have hc₀mem : c₀ ∈ conjSubgroup B g₀ := by
    rw [← hB₀conj, mem_conjSubgroup_iff]
    have e : z * c₀ * z⁻¹ = f := by rw [← hzf]; group
    rw [e]
    exact hfmem
  have hB₀Ω : conjSubgroup B g₀ ∈ omegaSet V K (nineE V K) :=
    conjSubgroup_mem_omegaSet hEK (nineE_subgroupOf_normal V K) hB.1 hg₀K
  have hbc₀ : b * c₀ ∈ pCoreOf 2 K := hmid (orderOf t) s (pow_orderOf_eq_one t) hs
  have hc₀R : c₀ ∉ pCoreOf 2 K := by
    intro hc
    apply hbR
    have e : b = (b * c₀) * c₀⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 K).mul_mem hbc₀ ((pCoreOf 2 K).inv_mem hc)
  have hc₀S : c₀ ∈ S := by
    have hbS : b ∈ S := hB.2 hbB
    have hbc₀S : b * c₀ ∈ S := h.pCoreOf_le_S hbc₀
    have e : c₀ = b⁻¹ * (b * c₀) := by group
    rw [e]
    exact S.mul_mem (S.inv_mem hbS) hbc₀S
  have hB₀S : conjSubgroup B g₀ ≤ S := by
    intro w hw
    by_cases hwR : w ∈ pCoreOf 2 K
    · exact h.pCoreOf_le_S hwR
    · have h1 : c₀⁻¹ * w ∈ pCoreOf 2 K := h.conj_inv_mul_mem hB hg₀K hc₀mem hw hc₀R hwR
      have e : w = c₀ * (c₀⁻¹ * w) := by group
      rw [e]
      exact S.mul_mem hc₀S (h.pCoreOf_le_S h1)
  have hB₀ : conjSubgroup B g₀ ∈ nineOmegaIn V K S := ⟨hB₀Ω, hB₀S⟩
  have hBZ : B ≤ nineZ V K S := le_iSup₂_of_le B hB le_rfl
  have hB₀Z : conjSubgroup B g₀ ≤ nineZ V K S := le_iSup₂_of_le (conjSubgroup B g₀) hB₀ le_rfl
  set d : G := x⁻¹ * (b * c₀) * x with hd
  have hdR : d ∈ pCoreOf 2 K := by
    have := (mem_pCoreOf_conj_iff K (K.inv_mem hxK)).mp hbc₀
    simpa [hd] using this
  have hdD : d ∈ nineD K A x := by
    rw [h.nineD_eq hx]
    refine ⟨mem_conjSubgroup_iff.mpr ?_, hdR⟩
    have e : x * d * x⁻¹ = b * c₀ := by rw [hd]; group
    rw [e]
    exact (nineZ V K S).mul_mem (hBZ hbB) (hB₀Z hc₀mem)
  refine ⟨d, hdD, ?_⟩
  have hc₀i : c₀⁻¹ = c₀ := inv_eq_of_mul_eq_one_right hc2
  have e1 : d * b' * d⁻¹ = x⁻¹ * ((b * c₀) * β' * (c₀ * b)) * x := by
    have e : (x⁻¹ * (b * c₀) * x)⁻¹ = x⁻¹ * (c₀⁻¹ * b⁻¹) * x := by group
    rw [hd, e, hc₀i, hbi, hβ']
    group
  have e2 : (b * c₀) * β' * (c₀ * b) = β := by
    rw [← hcf]
    calc b * c₀ * (c₀ * f * c₀) * (c₀ * b) = b * (c₀ * c₀) * f * (c₀ * c₀) * b := by group
      _ = b * f * b := by rw [hc2]; group
      _ = β := by
        rw [hf]
        calc b * (b * β * b) * b = (b * b) * β * (b * b) := by group
          _ = β := by rw [hbb]; group
  have e3 : x⁻¹ * β * x = b := by rw [hβ]; group
  have hconj : d * b' * d⁻¹ = b := by rw [e1, e2, e3]
  have hb'mem : b' ∈ conjSubgroup B d := by
    rw [mem_conjSubgroup_iff, hconj]
    exact hbB
  have hBd : conjSubgroup B d ∈ nineOmegaIn V K S := conjSubgroup_mem_nineOmegaIn h hB hdR
  obtain ⟨g₁, hg₁, -, -⟩ := mem_omegaSet.mp hB'.1
  obtain ⟨g₂, hg₂, -, -⟩ := mem_omegaSet.mp hB.1
  have hBd' : conjSubgroup B d = conjSubgroup V (g₂ * d) := by
    rw [hg₂, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  rcases inf_conjSubgroup_eq_bot_or_eq h.hyp7.2.2 g₁ (g₂ * d) with hbot | heq
  · exfalso
    have hmem : b' ∈ conjSubgroup V g₁ ⊓ conjSubgroup V (g₂ * d) :=
      ⟨by rw [← hg₁]; exact hb'B', by rw [← hBd']; exact hb'mem⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hb'R (hmem ▸ (pCoreOf 2 K).one_mem)
  · rw [hg₁, hBd', heq]

end Nine3Core

end CFSG.LocalAnalysis.WeakClosure81
