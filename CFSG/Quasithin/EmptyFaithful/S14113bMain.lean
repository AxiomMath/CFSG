module

public import CFSG.Quasithin.EmptyFaithful.S14113bFStar
public import CFSG.Quasithin.EmptyFaithful.S14113bBlocks
public import CFSG.Quasithin.EmptyFaithful.S14113Case

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S14110 Subgroup
open scoped commutatorElement

section Cyclic

variable {B : Type*} [Group B]

private theorem eq_bot_or_eq_zpowers_of_pow_three {c : B} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {Y : Subgroup B} (hY : Y ≤ Subgroup.zpowers c) : Y = ⊥ ∨ Y = Subgroup.zpowers c := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hY y.2)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hmod : c ^ (k % 3) = c ^ k := by
    have := zpow_mod_orderOf c k
    rw [hord] at this
    simpa using this
  have hc4 : c ^ (4 : ℤ) = c := by
    rw [show (4 : ℤ) = 3 + 1 by norm_num, zpow_add, zpow_one,
      show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3, one_mul]
  have hcY : c ∈ Y := by
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      apply hy1
      apply Subtype.ext
      rw [← hk, ← hmod, h0]; simp
    · have : c = (y : B) := by rw [← hk, ← hmod, h1]; simp
      rw [this]; exact y.2
    · have hy2 : (y : B) = c ^ (2 : ℤ) := by rw [← hk, ← hmod, h2]
      have : c = (y : B) ^ 2 := by
        rw [hy2, ← zpow_natCast, ← zpow_mul]
        simpa using hc4.symm
      rw [this]; exact Y.pow_mem y.2 2
  exact le_antisymm hY (Subgroup.zpowers_le.mpr hcY)

private theorem isPGroup_zpowers_of_pow_eq_one {x : B} {n : ℕ} (h : x ^ 2 ^ n = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨n, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h, one_zpow]

end Cyclic

section Quot

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem mem_oTwoFIn_iff_mk (x : ↥M) :
    (x : G) ∈ oTwoFIn M ↔
      (QuotientGroup.mk x : OTwoQuot M) ∈ CFSG.fittingSubgroup (OTwoQuot M) := by
  rw [oTwoFIn_eq_map_O2F]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : z = x := Subtype.ext hzx
    subst this
    exact hz
  · intro h
    exact ⟨x, h, rfl⟩

omit [Finite G] in
private theorem mem_oTwoEIn_iff_mk (x : ↥M) :
    (x : G) ∈ oTwoEIn M ↔ (QuotientGroup.mk x : OTwoQuot M) ∈ CFSG.layer (OTwoQuot M) := by
  rw [oTwoEIn_eq_map_O2E]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : z = x := Subtype.ext hzx
    subst this
    exact hz
  · intro h
    exact ⟨x, h, rfl⟩

omit [Finite G] in
private theorem image_le_normalizer_of_le {X Y : Subgroup G}
    (h : X ≤ Subgroup.normalizer (Y : Set G)) :
    imageOTwoQuot M X ≤ Subgroup.normalizer (imageOTwoQuot M Y : Set (OTwoQuot M)) := by
  have key : ∀ x ∈ X, ∀ (hx : x ∈ M), ∀ v ∈ imageOTwoQuot M Y,
      (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M) * v * (QuotientGroup.mk ⟨x, hx⟩)⁻¹ ∈
        imageOTwoQuot M Y := by
    intro x hxX hx v hv
    obtain ⟨y, hy, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
    exact mem_imageOTwoQuot_iff.mpr ⟨x * y * x⁻¹, M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx),
      (Subgroup.mem_normalizer_iff.mp (h hxX) y).mp hyY, rfl⟩
  intro u hu
  obtain ⟨x, hx, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key x hxX hx v, fun hv => ?_⟩
  have h1 := key x⁻¹ (X.inv_mem hxX) (M.inv_mem hx) _ hv
  have e : (QuotientGroup.mk ⟨x⁻¹, M.inv_mem hx⟩ : OTwoQuot M) =
      (QuotientGroup.mk ⟨x, hx⟩)⁻¹ := rfl
  rw [e] at h1
  have e2 : (QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M)⁻¹ *
      ((QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M) * v * (QuotientGroup.mk ⟨x, hx⟩)⁻¹) *
      ((QuotientGroup.mk ⟨x, hx⟩ : OTwoQuot M)⁻¹)⁻¹ = v := by group
  rwa [e2] at h1

omit [Finite G] in
private theorem normal_image_of_normalizes {K : Subgroup G} (hKM : K ≤ M)
    (hK : M ≤ Subgroup.normalizer (K : Set G)) : (imageOTwoQuot M K).Normal := by
  have : (K.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hK
  exact Subgroup.Normal.map this (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

omit [Finite G] in
private theorem isPGroup_image_of_le {X : Subgroup G} (hXM : X ≤ M) (hX : IsPGroup 2 X) :
    IsPGroup 2 (imageOTwoQuot M X) :=
  (A4.isPGroup_subgroupOf_of_le hXM hX).map _

omit [Finite G] in
private theorem image_eq_zpowers {X W : Subgroup G} {c : G} (hA : A4Data X W c) (hXM : X ≤ M)
    (hWQ : W ≤ pCoreOf 2 M) :
    imageOTwoQuot M X =
      Subgroup.zpowers (QuotientGroup.mk (⟨c, hXM hA.mem_X⟩ : ↥M) : OTwoQuot M) := by
  apply le_antisymm
  · intro u hu
    obtain ⟨x, hx, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    obtain ⟨w, hw, k, rfl⟩ := hA.mem_decomp hxX
    refine ⟨k, ?_⟩
    have hwM : w ∈ M := hXM (hA.le hw)
    have hw1 : (QuotientGroup.mk (⟨w, hwM⟩ : ↥M) : OTwoQuot M) = 1 :=
      (mk_eq_one_iff_mem_pCoreOf _).mpr (hWQ hw)
    have e1 : (⟨w * c ^ k, hx⟩ : ↥M) = ⟨w, hwM⟩ * ⟨c, hXM hA.mem_X⟩ ^ k := by
      apply Subtype.ext
      simp
    simp only [e1, QuotientGroup.mk_mul, hw1, one_mul, QuotientGroup.mk_zpow]
  · exact Subgroup.zpowers_le.mpr (mem_imageOTwoQuot_iff.mpr ⟨c, hXM hA.mem_X, hA.mem_X, rfl⟩)

omit [Finite G] in
private theorem mk_c_pow_three_ne_one {X W : Subgroup G} {c : G} (hA : A4Data X W c)
    (hXM : X ≤ M) (hQ2 : IsPGroup 2 (pCoreOf 2 M)) :
    (QuotientGroup.mk (⟨c, hXM hA.mem_X⟩ : ↥M) : OTwoQuot M) ^ 3 = 1 ∧
      (QuotientGroup.mk (⟨c, hXM hA.mem_X⟩ : ↥M) : OTwoQuot M) ≠ 1 := by
  constructor
  · rw [← QuotientGroup.mk_pow]
    have : (⟨c, hXM hA.mem_X⟩ : ↥M) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hA.c_pow_three
    rw [this]; rfl
  · intro h1
    have hcQ : c ∈ pCoreOf 2 M := (mk_eq_one_iff_mem_pCoreOf _).mp h1
    obtain ⟨n, hn⟩ := hQ2 ⟨c, hcQ⟩
    have hcn : c ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hord : orderOf c = 3 := hA.order_c
    have hd : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hcn
    rw [hord] at hd
    have h3' : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) hd
    omega

private theorem mem_pCoreOf_of_mem_oTwoFIn_of_pow {x : G} (hx : x ∈ oTwoFIn M) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1) : x ∈ pCoreOf 2 M := by
  have hxM : x ∈ M := C2Six.oTwoFIn_le hx
  have hfit := (mem_oTwoFIn_iff_mk ⟨x, hxM⟩).mp hx
  set y : OTwoQuot M := QuotientGroup.mk ⟨x, hxM⟩ with hy
  have hyn : y ^ 2 ^ n = 1 := by
    rw [hy, ← QuotientGroup.mk_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hxn)
    rw [this]; rfl
  have hS := isPGroup_zpowers_of_pow_eq_one hyn
  have hbot := eq_bot_of_isPGroup_of_le_fitting (pCore_two_quot_eq_bot M) hS
    (Subgroup.zpowers_le.mpr hfit)
  have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
  rw [hbot, Subgroup.mem_bot] at this
  exact (mk_eq_one_iff_mem_pCoreOf ⟨x, hxM⟩).mp this

end Quot

section Blocks

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem center_biSup_eq_one {ι : Type*} [DecidableEq ι] (X : ι → Subgroup G)
    (hcen : ∀ i, ∀ z ∈ X i, (∀ l ∈ X i, z * l = l * z) → z = 1)
    (hcomm : ∀ i k, X i = X k ∨ ∀ x ∈ X i, ∀ y ∈ X k, x * y = y * x) (S : Finset ι) :
    ∀ z ∈ (⨆ i ∈ S, X i : Subgroup G), (∀ l ∈ (⨆ i ∈ S, X i : Subgroup G), z * l = l * z) →
      z = 1 := by
  induction S using Finset.induction_on with
  | empty =>
    intro z hz _
    simpa using hz
  | insert a S haS ih =>
    intro z hz hzc
    rw [Finset.iSup_insert] at hz hzc
    by_cases hle : X a ≤ ⨆ i ∈ S, X i
    · rw [sup_eq_right.mpr hle] at hz hzc
      exact ih z hz hzc
    · have hcomm' : ∀ x ∈ X a, ∀ y ∈ (⨆ i ∈ S, X i : Subgroup G), x * y = y * x := by
        intro x hx y hy
        have hle' : (⨆ i ∈ S, X i : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
          refine iSup₂_le fun i hi y' hy' => ?_
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hne : X a ≠ X i := fun e =>
            hle (e.le.trans (le_iSup₂ (f := fun i (_ : i ∈ S) => X i) i hi))
          exact ((hcomm a i).resolve_left hne x hx y' hy').symm
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hle' hy)).symm
      exact center_sup_eq_one (hcen a) ih hcomm' z hz hzc

private theorem inf_image_blockCentralizer_eq_bot (hcharM : CharTwo M) {r : ℕ}
    (Lb : Fin r → Subgroup G) (hblk : ∀ i, IsA4Blk M (Lb i)) (hLF : ∀ i, Lb i ≤ oTwoFIn M) :
    (⨆ i, imageOTwoQuot M (Lb i)) ⊓ imageOTwoQuot M (blockCentralizer M) = ⊥ := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  set D : Subgroup G := ⨆ i, Lb i with hD
  have hZD : ∀ z ∈ D, (∀ l ∈ D, z * l = l * z) → z = 1 := by
    have := center_biSup_eq_one Lb
      (fun i z hz hzc => by
        obtain ⟨-, -, W, c, hA⟩ := hblk i
        exact hA.center z hz hzc)
      (fun i k => by
        by_cases hik : Lb i = Lb k
        · exact Or.inl hik
        · exact Or.inr (IsA4Blk.commute_of_ne hcharM (hblk i) (hblk k) hik))
      Finset.univ
    simpa using this
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨huV, huK⟩ := hu
  obtain ⟨k, hkM, hkK, hku⟩ := mem_imageOTwoQuot_iff.mp huK
  obtain ⟨d, hdM, hdD, hdu⟩ : ∃ d, ∃ hd : d ∈ M, d ∈ D ∧
      (QuotientGroup.mk ⟨d, hd⟩ : OTwoQuot M) = u := by
    refine Subgroup.iSup_induction (fun i => imageOTwoQuot M (Lb i))
      (C := fun u => ∃ d, ∃ hd : d ∈ M, d ∈ D ∧ (QuotientGroup.mk ⟨d, hd⟩ : OTwoQuot M) = u)
      huV (fun i x hx => ?_) ⟨1, M.one_mem, D.one_mem, rfl⟩
      (fun x y hx hy => ?_)
    · obtain ⟨l, hl, hlL, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
      exact ⟨l, hl, (le_iSup Lb i) hlL, rfl⟩
    · obtain ⟨d₁, h₁, hd₁, e₁⟩ := hx
      obtain ⟨d₂, h₂, hd₂, e₂⟩ := hy
      exact ⟨d₁ * d₂, M.mul_mem h₁ h₂, D.mul_mem hd₁ hd₂, by rw [← e₁, ← e₂]; rfl⟩
  have hkcomm : ∀ y ∈ D, y * k = k * y := by
    intro y hy
    refine Subgroup.iSup_induction Lb (C := fun y => y * k = k * y) hy (fun i x hx => ?_)
      (by simp) (fun x y hx hy => ?_)
    · exact (mem_blockCentralizer.mp hkK).2 (Lb i) (hblk i) x hx
    · calc x * y * k = x * (y * k) := by group
        _ = x * (k * y) := by rw [hy]
        _ = (x * k) * y := by group
        _ = (k * x) * y := by rw [hx]
        _ = k * (x * y) := by group
  have hq : d⁻¹ * k ∈ pCoreOf 2 M := by
    have h1 : (⟨d, hdM⟩ : ↥M)⁻¹ * ⟨k, hkM⟩ ∈ CFSG.Open.pCore 2 ↥M :=
      QuotientGroup.eq.mp (hdu.trans hku.symm)
    exact ⟨_, h1, rfl⟩
  obtain ⟨N, hN⟩ := hQ2 ⟨_, hq⟩
  have hqN : (d⁻¹ * k) ^ 2 ^ N = 1 := by simpa using congrArg Subtype.val hN
  have hdq : Commute d (d⁻¹ * k) := by
    show d * (d⁻¹ * k) = (d⁻¹ * k) * d
    have := hkcomm d hdD
    calc d * (d⁻¹ * k) = k := by group
      _ = d⁻¹ * (d * k) := by group
      _ = d⁻¹ * (k * d) := by rw [this]
      _ = (d⁻¹ * k) * d := by group
  have hk2 : k ^ 2 ^ N = d ^ 2 ^ N := by
    have : k = d * (d⁻¹ * k) := by group
    calc k ^ 2 ^ N = (d * (d⁻¹ * k)) ^ 2 ^ N := by rw [← this]
      _ = d ^ 2 ^ N * (d⁻¹ * k) ^ 2 ^ N := hdq.mul_pow _
      _ = d ^ 2 ^ N := by rw [hqN, mul_one]
  have hdN : d ^ 2 ^ N = 1 := by
    refine hZD _ (D.pow_mem hdD _) fun l hl => ?_
    rw [← hk2]
    exact (Commute.pow_left (show Commute k l from (hkcomm l hl).symm) _).eq
  have hdF : d ∈ oTwoFIn M := (iSup_le hLF : D ≤ oTwoFIn M) hdD
  have hdQ : d ∈ pCoreOf 2 M := mem_pCoreOf_of_mem_oTwoFIn_of_pow hdF hdN
  have hkQ : k ∈ pCoreOf 2 M := by
    have : k = d * (d⁻¹ * k) := by group
    rw [this]
    exact (pCoreOf 2 M).mul_mem hdQ hq
  rw [← hku]
  exact Subgroup.mem_bot.mpr ((mk_eq_one_iff_mem_pCoreOf ⟨k, hkM⟩).mpr hkQ)

omit [Finite G] in
private theorem image_fixed_eq_one {X W J : Subgroup G} {c : G} (hA : A4Data X W c)
    (hXM : X ≤ M) (hJM : J ≤ M) (hWQ : W ≤ pCoreOf 2 M) (hQ2 : IsPGroup 2 (pCoreOf 2 M))
    (hJX : ⁅X, J⁆ = X) :
    ∀ x ∈ imageOTwoQuot M X, (∀ j ∈ imageOTwoQuot M J, j * x = x * j) → x = 1 := by
  intro x hx hfix
  by_contra hx1
  have hJN : J ≤ Subgroup.normalizer (X : Set G) := le_normalizer_of_commutator_eq hJX
  obtain ⟨h3, h1⟩ := mk_c_pow_three_ne_one hA hXM hQ2
  have himg := image_eq_zpowers hA hXM hWQ
  set ĉ : OTwoQuot M := QuotientGroup.mk (⟨c, hXM hA.mem_X⟩ : ↥M) with hĉ
  have hxz : Subgroup.zpowers x = Subgroup.zpowers ĉ := by
    rcases eq_bot_or_eq_zpowers_of_pow_three h3 h1 (Y := Subgroup.zpowers x)
      (Subgroup.zpowers_le.mpr (himg ▸ hx)) with h | h
    · exfalso
      exact hx1 (Subgroup.zpowers_eq_bot.mp h)
    · exact h
  have hĉx : ĉ ∈ Subgroup.zpowers x := hxz ▸ Subgroup.mem_zpowers ĉ
  have hcomm : ∀ j ∈ imageOTwoQuot M J, ∀ u ∈ imageOTwoQuot M X, j * u = u * j := by
    intro j hj u hu
    have hjx : Commute j x := hfix j hj
    have hjc : Commute j ĉ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hĉx
      rw [← hk]; exact hjx.zpow_right k
    rw [himg] at hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← hk]; exact (hjc.zpow_right k).eq
  have hXJ : ⁅X, J⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro l hl j hj
    have hlM : l ∈ M := hXM hl
    have hjM : j ∈ M := hJM hj
    have hmem : l * j * l⁻¹ * j⁻¹ ∈ pCoreOf 2 M := by
      have := hcomm (QuotientGroup.mk ⟨j, hjM⟩) (mem_imageOTwoQuot_iff.mpr ⟨j, hjM, hj, rfl⟩)
        (QuotientGroup.mk ⟨l, hlM⟩) (mem_imageOTwoQuot_iff.mpr ⟨l, hlM, hl, rfl⟩)
      exact (mk_commute_iff ⟨l, hlM⟩ ⟨j, hjM⟩).mp this.symm
    have hlX : l * j * l⁻¹ * j⁻¹ ∈ X := by
      have : l * j * l⁻¹ * j⁻¹ = l * (j * l⁻¹ * j⁻¹) := by group
      rw [this]
      exact X.mul_mem hl ((Subgroup.mem_normalizer_iff.mp (hJN hj) l⁻¹).mp (X.inv_mem hl))
    obtain ⟨n, hn⟩ := hQ2 ⟨_, hmem⟩
    rw [commutatorElement_def]
    exact hA.mem_W_of_two_pow hlX (by simpa using congrArg Subtype.val hn)
  have hXW : X ≤ W := by
    calc X = ⁅X, J⁆ := hJX.symm
      _ ≤ W := hXJ
  have := hA.finite_W
  have := Subgroup.card_le_of_le hXW
  rw [hA.card_X, hA.card_W] at this
  omega

private theorem image_comm_of_blocks (hcharM : CharTwo M) {X Y : Subgroup G}
    (hX : IsA4Blk M X) (hY : IsA4Blk M Y) :
    ∀ x ∈ imageOTwoQuot M X, ∀ y ∈ imageOTwoQuot M Y, x * y = y * x := by
  intro x hx y hy
  by_cases hXY : X = Y
  · subst hXY
    obtain ⟨hXM, hXs, W, c, hA⟩ := hX
    have hWQ := S14110.A4Data.W_le_pCoreOf hA hXM hXs
    rw [image_eq_zpowers hA hXM hWQ] at hx hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.refl _).zpow_zpow a b).eq
  · obtain ⟨x', hx'M, hx'X, rfl⟩ := mem_imageOTwoQuot_iff.mp hx
    obtain ⟨y', hy'M, hy'Y, rfl⟩ := mem_imageOTwoQuot_iff.mp hy
    have hc := IsA4Blk.commute_of_ne hcharM hX hY hXY x' hx'X y' hy'Y
    refine (mk_commute_iff ⟨x', hx'M⟩ ⟨y', hy'M⟩).mpr ?_
    have : (⟨x', hx'M⟩ * ⟨y', hy'M⟩ * ⟨x', hx'M⟩⁻¹ * ⟨y', hy'M⟩⁻¹ : ↥M) = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
      rw [hc]; group
    rw [this]
    exact (pCoreOf 2 M).one_mem

private theorem le_normalizer_iSup_of {B : Type*} [Group B] {ι : Type*} (J : Subgroup B)
    (X : ι → Subgroup B) (h : ∀ i, J ≤ Subgroup.normalizer (X i : Set B)) :
    J ≤ Subgroup.normalizer ((⨆ i, X i : Subgroup B) : Set B) := by
  have key : ∀ j ∈ J, ∀ v ∈ (⨆ i, X i : Subgroup B), j * v * j⁻¹ ∈ (⨆ i, X i : Subgroup B) := by
    intro j hj v hv
    refine Subgroup.iSup_induction X (C := fun v => j * v * j⁻¹ ∈ (⨆ i, X i : Subgroup B)) hv
      (fun i x hx => ?_) (by simp) (fun x y hx hy => ?_)
    · exact Subgroup.mem_iSup_of_mem i ((Subgroup.mem_normalizer_iff.mp (h i hj) x).mp hx)
    · have : j * (x * y) * j⁻¹ = (j * x * j⁻¹) * (j * y * j⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ hx hy
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key j hj v, fun hv => ?_⟩
  have := key j⁻¹ (J.inv_mem hj) _ hv
  simpa [mul_assoc] using this

end Blocks

section Main

variable {G : Type} [Group G] [Finite G]

theorem blockCentralizer_le_of_blocks {T Mc M H : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hHM : H ≤ M) (hR : pCoreOf 2 H ≠ ⊥)
    (hC : cgsIn M (pCoreOf 2 H) ≤ H) (hE : oTwoEIn M ≤ H) {r : ℕ} (Lb : Fin r → Subgroup G)
    (hLb : ∀ i, IsBlock2 (oTwoFIn M) (Lb i) ∧ IsAltType (Lb i) 3 ∧
      ⁅Lb i, thompsonJ (pCoreOf 2 H)⁆ = Lb i)
    (hprod : ∀ x ∈ oTwoFIn M, ∃ m ∈ H ⊓ oTwoFIn M, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧
      x = m * (List.ofFn y).prod) :
    blockCentralizer M ≤ H := by
  classical
  have hcharM : CharTwo M := charTwo_of_inM h hM
  have hyp : HypC23 M (pCoreOf 2 H) H := hypC23_of_cgs h hM hHM hR hC
  have hQR : pCoreOf 2 M ≤ pCoreOf 2 H := c2_1_pCore_le hyp.radical
  have hRH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hRM : pCoreOf 2 H ≤ M := hRH.trans hHM
  have hJR : thompsonJ (pCoreOf 2 H) ≤ pCoreOf 2 H := thompsonJ_le_self _
  have hJM : thompsonJ (pCoreOf 2 H) ≤ M := hJR.trans hRM
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := pCoreOf_isPGroup 2 M
  have hAs : ∀ i, ∃ c, A4Data (Lb i) (blockU (Lb i)) c := fun i =>
    A4Data.of_isShort2 (hLb i).1.1 (hLb i).2.1
  choose c hA using hAs
  have hLF : ∀ i, Lb i ≤ oTwoFIn M := fun i => (hLb i).1.2.1
  have hLM : ∀ i, Lb i ≤ M := fun i => (hLF i).trans C2Six.oTwoFIn_le
  have hLs : ∀ i, ((Lb i).subgroupOf M).IsSubnormal := fun i =>
    (isBlock2_of_oTwoFIn (hLb i).1).2.2
  have hblk : ∀ i, IsA4Blk M (Lb i) := fun i => ⟨hLM i, hLs i, blockU (Lb i), c i, hA i⟩
  have hWQ : ∀ i, blockU (Lb i) ≤ pCoreOf 2 M := fun i =>
    S14110.A4Data.W_le_pCoreOf (hA i) (hLM i) (hLs i)
  have hJN : ∀ i, thompsonJ (pCoreOf 2 H) ≤ Subgroup.normalizer (Lb i : Set G) := fun i =>
    le_normalizer_of_commutator_eq (hLb i).2.2
  have hB : CFSG.pCore 2 (OTwoQuot M) = ⊥ := pCore_two_quot_eq_bot M
  have hKnorm : (imageOTwoQuot M (blockCentralizer M)).Normal :=
    normal_image_of_normalizes blockCentralizer_le (le_normalizer_blockCentralizer M)
  have hVfix : ∀ v ∈ (⨆ i, imageOTwoQuot M (Lb i) : Subgroup (OTwoQuot M)),
      (∀ j ∈ imageOTwoQuot M (thompsonJ (pCoreOf 2 H)), j * v = v * j) → v = 1 := by
    have := fixed_eq_one_of_biSup (imageOTwoQuot M (thompsonJ (pCoreOf 2 H)))
      (fun i => imageOTwoQuot M (Lb i))
      (fun i => image_le_normalizer_of_le (hJN i))
      (fun i k => image_comm_of_blocks hcharM (hblk i) (hblk k))
      (fun i Y hY => by
        obtain ⟨h3, h1⟩ := mk_c_pow_three_ne_one (hA i) (hLM i) hQ2
        have hY' : Y ≤ imageOTwoQuot M (Lb i) := hY
        rw [image_eq_zpowers (hA i) (hLM i) (hWQ i)] at hY'
        have := eq_bot_or_eq_zpowers_of_pow_three h3 h1 hY'
        rw [← image_eq_zpowers (hA i) (hLM i) (hWQ i)] at this
        exact this)
      (fun i x hx hfix => image_fixed_eq_one (hA i) (hLM i) hJM (hWQ i) hQ2 (hLb i).2.2 x hx hfix)
      Finset.univ
    simpa using this
  have hF : ∀ f ∈ CFSG.fittingSubgroup (OTwoQuot M),
      ∃ a ∈ CFSG.fittingSubgroup (OTwoQuot M) ⊓ imageOTwoQuot M H,
        ∃ v ∈ (⨆ i, imageOTwoQuot M (Lb i) : Subgroup (OTwoQuot M)), f = a * v := by
    intro f hf
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective f
    have hx : (x : G) ∈ oTwoFIn M := (mem_oTwoFIn_iff_mk x).mpr hf
    obtain ⟨m, hm, y, hy, hxm⟩ := hprod (x : G) hx
    have hlist : ∀ l : List G, (∀ z ∈ l, ∃ i, z ∈ Lb i) →
        ∃ p : ↥M, (p : G) = l.prod ∧
          (QuotientGroup.mk p : OTwoQuot M) ∈
            (⨆ i, imageOTwoQuot M (Lb i) : Subgroup (OTwoQuot M)) := by
      intro l
      induction l with
      | nil =>
        intro _
        exact ⟨1, by simp, by simp⟩
      | cons a t ih =>
        intro hl
        obtain ⟨i, hi⟩ := hl a List.mem_cons_self
        obtain ⟨p, hp, hpV⟩ := ih fun z hz => hl z (List.mem_cons_of_mem a hz)
        have haM : a ∈ M := hLM i hi
        refine ⟨⟨a, haM⟩ * p, by simp [hp], ?_⟩
        rw [QuotientGroup.mk_mul]
        refine Subgroup.mul_mem _ ?_ hpV
        exact Subgroup.mem_iSup_of_mem i (mem_imageOTwoQuot_iff.mpr ⟨a, haM, hi, rfl⟩)
    obtain ⟨p, hp, hpV⟩ := hlist (List.ofFn y) fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact ⟨i, hy i⟩
    have hmM : m ∈ M := hHM hm.1
    have hxeq : x = ⟨m, hmM⟩ * p := by
      apply Subtype.ext
      simp [hxm, hp]
    refine ⟨QuotientGroup.mk ⟨m, hmM⟩, ⟨?_, ?_⟩, QuotientGroup.mk p, hpV, ?_⟩
    · exact (mem_oTwoFIn_iff_mk ⟨m, hmM⟩).mp hm.2
    · exact mem_imageOTwoQuot_iff.mpr ⟨m, hmM, hm.1, rfl⟩
    · rw [hxeq, QuotientGroup.mk_mul]
  have hcen := le_centralizer_of_fixed hB
    (Kb := imageOTwoQuot M (blockCentralizer M)) (Rb := imageOTwoQuot M (pCoreOf 2 H))
    (Hb := imageOTwoQuot M H) (Jb := imageOTwoQuot M (thompsonJ (pCoreOf 2 H)))
    (Vb := ⨆ i, imageOTwoQuot M (Lb i))
    (isPGroup_image_of_le hRM (pCoreOf_isPGroup 2 H))
    (image_le_normalizer_of_le (le_normalizer_pCoreOf 2 H))
    (fun u hu => by
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
      exact mem_imageOTwoQuot_iff.mpr ⟨z.1, z.2, hE ((mem_oTwoEIn_iff_mk z).mpr hu), rfl⟩)
    (imageOTwoQuot_mono hJR)
    (le_normalizer_iSup_of _ _ fun i => image_le_normalizer_of_le (hJN i))
    (inf_image_blockCentralizer_eq_bot hcharM Lb hblk hLF) hVfix hF
  intro k hk
  have hkM : k ∈ M := blockCentralizer_le hk
  have hkey : ∀ k' ∈ blockCentralizer M, ∀ y ∈ pCoreOf 2 H, k' * y * k'⁻¹ ∈ pCoreOf 2 H := by
    intro k' hk' y hy
    have hk'M := blockCentralizer_le hk'
    have hyM := hRM hy
    have h1 := hcen (mem_imageOTwoQuot_iff.mpr ⟨y, hyM, hy, rfl⟩)
    have h2 := Subgroup.mem_centralizer_iff.mp h1 (QuotientGroup.mk ⟨k', hk'M⟩)
      (mem_imageOTwoQuot_iff.mpr ⟨k', hk'M, hk', rfl⟩)
    have h3 : k' * y * k'⁻¹ * y⁻¹ ∈ pCoreOf 2 M := (mk_commute_iff ⟨k', hk'M⟩ ⟨y, hyM⟩).mp h2
    have : k' * y * k'⁻¹ = (k' * y * k'⁻¹ * y⁻¹) * y := by group
    rw [this]
    exact (pCoreOf 2 H).mul_mem (hQR h3) hy
  have hkR : k ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hkey k hk y, fun hy => ?_⟩
    have := hkey k⁻¹ ((blockCentralizer M).inv_mem hk) _ hy
    simpa [mul_assoc] using this
  exact hC ((inf_normalizer_le_cgsIn hR) ⟨hkM, hkR⟩)

theorem stage14113CaseTwo : Stage14113CaseTwo := by
  intro G _ _ T Mc h M H hM hTH hHM hR hC hE hMc _ r Lb hLb hprod _
  have hK : blockCentralizer M ≤ H :=
    blockCentralizer_le_of_blocks h hM hHM hR hC hE Lb
      (fun i => ⟨(hLb i).1, (hLb i).2.1, (hLb i).2.2.2⟩) hprod
  have hCM : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M := by
    rw [hMc]; exact h.centralizer_le_mc
  intro g hg
  obtain ⟨k, hk, t, ht, rfl⟩ := exists_mul_blockCentralizer_of_mem_centralizer h hM hCM g hg
  exact H.mul_mem (hK hk) (hTH ht)

end Main

end CFSG.Quasithin
