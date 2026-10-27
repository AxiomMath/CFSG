module

public import CFSG.Quasithin.EmptyFaithful.S14110AuxA4
public import CFSG.Quasithin.H13.A5S1327s

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.S14110
open scoped Pointwise

section A4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem A4Data.of_fpf {W : Subgroup G} {c : G} (hW4 : Nat.card W = 4)
    (hsq : ∀ w ∈ W, w ^ 2 = 1) (hcomm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u)
    (hc3 : orderOf c = 3) (hcN : c ∈ Subgroup.normalizer (W : Set G))
    (hfp : ∀ w ∈ W, w ≠ 1 → c * w * c⁻¹ ≠ w) :
    A4Data (W ⊔ Subgroup.zpowers c) W c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc3' : c ^ 3 = 1 := hc3 ▸ pow_orderOf_eq_one c
  have hcN' : Subgroup.zpowers c ≤ Subgroup.normalizer (W : Set G) :=
    (Subgroup.zpowers_le).2 hcN
  have hset : ((W ⊔ Subgroup.zpowers c : Subgroup G) : Set G) =
      (W : Set G) * (Subgroup.zpowers c : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W (Subgroup.zpowers c) hcN'
  have hinf : W ⊓ Subgroup.zpowers c = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxW, hxc⟩ := hx
    have h2 : x ^ 2 = 1 := hsq x hxW
    obtain ⟨k, rfl⟩ := hxc
    have h3 : (c ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3', one_zpow]
    exact Subgroup.mem_bot.mpr (eq_one_of_pow_coprime h2 h3 (by norm_num))
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w ∈ W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : W = ⊥ := eq_bot_iff.mpr fun w hw => Subgroup.mem_bot.mpr (hcon w hw)
    rw [this, Subgroup.card_bot] at hW4
    omega
  have hcent : ∀ k : ℤ, (∀ u ∈ W, c ^ k * u * (c ^ k)⁻¹ = u) → c ^ k = 1 := by
    intro k hk
    have hk3 : c ^ k = c ^ (k % 3) := by
      rw [← zpow_mod_orderOf, hc3]; rfl
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h | h | h
    · rw [hk3, h, zpow_zero]
    · exfalso
      rw [hk3, h, zpow_one] at hk
      exact hfp w₀ hw₀ hw₀1 (hk w₀ hw₀)
    · exfalso
      rw [hk3, h] at hk
      have h1 := hk (c * w₀ * c⁻¹) ((Subgroup.mem_normalizer_iff.mp hcN w₀).mp hw₀)
      apply hfp w₀ hw₀ hw₀1
      have e : c ^ (2 : ℤ) * (c * w₀ * c⁻¹) * (c ^ (2 : ℤ))⁻¹ = w₀ := by
        rw [zpow_two]
        calc c * c * (c * w₀ * c⁻¹) * (c * c)⁻¹ = (c * (c * c)) * w₀ * (c * (c * c))⁻¹ := by
              group
          _ = w₀ := by rw [← pow_three, hc3']; group
      rw [e] at h1
      exact h1.symm
  refine ⟨le_sup_left, hW4, hsq, hcomm, Subgroup.mem_sup_right (Subgroup.mem_zpowers c), hc3, hcN,
    hfp, rfl, ?_, ?_⟩
  ·
    have h1 := B2F.relIndex_sup_eq_of_le_normalizer' hcN'
    have h2 : W.relIndex (Subgroup.zpowers c) = 3 := by
      rw [Subgroup.relIndex, show W.subgroupOf (Subgroup.zpowers c) = ⊥ from ?_,
        Subgroup.index_bot, Nat.card_zpowers, hc3]
      rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, hinf]
    have h3 := Subgroup.relIndex_mul_card W (Subgroup.zpowers c ⊔ W)
    rw [inf_of_le_left le_sup_right, h1, h2, sup_comm, hW4] at h3
    rw [← h3]
  ·
    intro g hg hcg
    have hg' : g ∈ ((W ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨w, hw, _, ⟨k, rfl⟩, rfl⟩ := hg'
    simp only at hcg ⊢
    have hck : c ^ k = 1 := by
      refine hcent k fun u hu => ?_
      have h1 := hcg u (Subgroup.mem_sup_left hu)
      have h2 : w * u = u * w := hcomm w hw u hu
      calc c ^ k * u * (c ^ k)⁻¹ = w⁻¹ * (w * c ^ k * u) * (c ^ k)⁻¹ := by group
        _ = w⁻¹ * (u * (w * c ^ k)) * (c ^ k)⁻¹ := by rw [h1]
        _ = w⁻¹ * (u * w) := by group
        _ = w⁻¹ * (w * u) := by rw [h2]
        _ = u := by group
    rw [hck, mul_one] at hcg ⊢
    by_contra hw1
    apply hfp w hw hw1
    have := hcg c (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    calc c * w * c⁻¹ = (w * c) * c⁻¹ := by rw [this]
      _ = w := by group

end A4

section Blk

variable {G : Type} [Group G] {U : Subgroup G} (hU : IsElemAbelian 2 U)

@[expose] def ival : IntMod U hU →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem ival_injective : Function.Injective (ival hU) := IntMod.val_injective

@[expose] def blk (K : Subgroup (MulAut (IntMod U hU))) : Subgroup G := (commV K).map (ival hU)

variable {hU}

theorem mem_blk {K : Subgroup (MulAut (IntMod U hU))} {g : G} :
    g ∈ blk hU K ↔ ∃ h : g ∈ U, IntMod.mk hU ⟨g, h⟩ ∈ commV K := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.val_mem, hv⟩
  · rintro ⟨h, hv⟩
    exact ⟨IntMod.mk hU ⟨g, h⟩, hv, rfl⟩

theorem blk_le (K : Subgroup (MulAut (IntMod U hU))) : blk hU K ≤ U := fun _ hg =>
  (mem_blk.1 hg).1

theorem card_blk (K : Subgroup (MulAut (IntMod U hU))) :
    Nat.card ↥(blk hU K) = Nat.card ↥(commV K) :=
  Subgroup.card_map_of_injective (ival_injective hU)

theorem conj_mem_blk {K : Subgroup (MulAut (IntMod U hU))} {x : G}
    (hx : x ∈ Subgroup.normalizer (U : Set G)) {g : G} (hg : g ∈ blk hU K) :
    x * g * x⁻¹ ∈ blk hU (B1.conjAut (convI hU ⟨x, hx⟩) K) := by
  obtain ⟨hgU, hgK⟩ := mem_blk.1 hg
  have hxg : x * g * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hx g).mp hgU
  refine mem_blk.2 ⟨hxg, ?_⟩
  rw [← commV_map_conjAut]
  refine ⟨IntMod.mk hU ⟨g, hgU⟩, hgK, ?_⟩
  apply IntMod.val_injective
  show (convI hU ⟨x, hx⟩ (IntMod.mk hU ⟨g, hgU⟩)).val = x * g * x⁻¹
  rw [convI_apply_val]
  rfl

theorem blk_autI_le {X : Subgroup G} (hXU : U ≤ Subgroup.normalizer (X : Set G)) :
    blk hU (autI hU X) ≤ X := by
  rintro _ ⟨v, hv, rfl⟩
  show v.val ∈ X
  refine Subgroup.closure_induction (p := fun w _ => w.val ∈ X) ?_ (by simp [X.one_mem])
    (fun a b _ _ ha hb => by rw [IntMod.val_mul]; exact X.mul_mem ha hb)
    (fun a _ ha => by rw [IntMod.val_inv]; exact X.inv_mem ha) hv
  rintro _ ⟨φ, hφ, w, rfl⟩
  obtain ⟨x, hxX, rfl⟩ := (mem_autI hU).1 hφ
  rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]
  have hw : w.val * (x : G)⁻¹ * (w.val)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hXU w.val_mem) _).mp (X.inv_mem hxX)
  have e : (x : G) * w.val * (x : G)⁻¹ * (w.val)⁻¹ = x * (w.val * (x : G)⁻¹ * (w.val)⁻¹) := by
    group
  rw [e]
  exact X.mul_mem hxX hw

end Blk

namespace TwoBlocks

variable {G : Type} [Group G] [Finite G] {U : Subgroup G} {hU : IsElemAbelian 2 U}
  {H T : Subgroup G} {K₁ K₂ : Subgroup (MulAut (IntMod U hU))}

omit [Finite G] in
theorem conjAut_K1 (B : TwoBlocks hU H T K₁ K₂) {φ : MulAut (IntMod U hU)} (hφ : φ ∈ K₁ ⊔ K₂) :
    B1.conjAut φ K₁ = K₁ := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute B.comm hφ
  have hk₂K : B1.conjAut k₂ K₁ = K₁ :=
    S1417.conjAut_eq_iff_mem_normalizer.2 (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun x hx => B.comm x hx k₂ hk₂))
  rw [S1417.conjAut_mul, hk₂K, S1417.conjAut_eq_of_mem hk₁]

variable (B : TwoBlocks hU H T K₁ K₂)
include B

omit [Finite G] in
theorem norm_eq_one {φ : MulAut (IntMod U hU)} (hφ : φ ∈ K₁) (hφ3 : φ ^ 3 = 1) (hφ1 : φ ≠ 1)
    {u : IntMod U hU} (hu : u ∈ commV K₁) : u * φ u * φ (φ u) = 1 := by
  have hst : ∀ l ∈ K₁, ∀ u ∈ commV K₁, l u ∈ commV K₁ := fun l hl u hu => commV_stable K₁ hl hu
  have h3 : φ (φ (φ u)) = u := by
    have : (φ ^ 3) u = u := by rw [hφ3, MulAut.one_apply]
    rwa [pow_succ, pow_two, MulAut.mul_apply, MulAut.mul_apply] at this
  refine natL2_fix_eq_one B.nat₁ hst hφ hφ3 hφ1
    ((commV K₁).mul_mem ((commV K₁).mul_mem hu (hst φ hφ u hu)) (hst φ hφ _ (hst φ hφ u hu))) ?_
  rw [map_mul, map_mul, h3]
  rw [mul_comm (φ u * φ (φ u)) u, ← mul_assoc]

theorem exists_c (hCU : H ⊓ Subgroup.centralizer (U : Set G) ≤ U) :
    ∃ c ∈ twoResidual H, ∃ hc : c ∈ Subgroup.normalizer (U : Set G),
      c ^ 3 = 1 ∧ convI hU ⟨c, hc⟩ ∈ K₁ ∧ convI hU ⟨c, hc⟩ ≠ 1 := by
  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨y₂, hy₂, hy₂3, hy₂1⟩ := S1417.exists_orderThree B.nat₂
  have hL := B.autI_twoResidual_eq hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  have hy₁L : y₁ ∈ autI hU (twoResidual H) := by
    rw [hL]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
  obtain ⟨x, hxL, hxy⟩ := (mem_autI hU).1 hy₁L
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : G)).ne'
  set c := (x : G) ^ 2 ^ a with hcdef
  have hcN : c ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ x.2 _
  have hcv : convI hU ⟨c, hcN⟩ = y₁ ^ 2 ^ a := by
    rw [← hxy, ← map_pow]
    rfl
  have hc1 : convI hU ⟨c, hcN⟩ ≠ 1 := by
    rw [hcv]
    intro h
    have h3 : orderOf y₁ = 3 := orderOf_eq_prime hy₁3 hy₁1
    have hdvd : orderOf y₁ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h
    rw [h3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  have hcodd : Odd (orderOf c) := by
    have h2a : (2 ^ a : ℕ) ≠ 0 := by positivity
    rw [hcdef, orderOf_pow' _ h2a, ham, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hcH : c ∈ H := (twoResidual_le H) (Subgroup.pow_mem _ hxL _)
  have hc3U : c ^ 3 ∈ U := by
    refine hCU ⟨H.pow_mem hcH 3, ?_⟩
    have h1 : convI hU ⟨c ^ 3, Subgroup.pow_mem _ hcN 3⟩ = 1 := by
      rw [show (⟨c ^ 3, Subgroup.pow_mem _ hcN 3⟩ : ↥(Subgroup.normalizer (U : Set G))) =
        ⟨c, hcN⟩ ^ 3 from rfl, map_pow, hcv, ← pow_mul, mul_comm, pow_mul, hy₁3, one_pow]
    exact (convI_eq_one_iff hU _).1 h1
  have hc3 : c ^ 3 = 1 := by
    have h2 : (c ^ 3) ^ 2 = 1 := hU.2 _ hc3U
    have hm' : (c ^ 3) ^ orderOf c = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    exact eq_one_of_pow_coprime h2 hm' (Nat.coprime_two_left.mpr hcodd)
  exact ⟨c, Subgroup.pow_mem _ hxL _, hcN, hc3, by rw [hcv]; exact K₁.pow_mem hy₁ _, hc1⟩

end TwoBlocks

namespace TwoBlocks

variable {G : Type} [Group G] [Finite G] {U : Subgroup G} {hU : IsElemAbelian 2 U}
  {H T : Subgroup G} {K₁ K₂ : Subgroup (MulAut (IntMod U hU))}

omit [Finite G] in
theorem mem_sup_zpowers_iff {W : Subgroup G} {c : G} (hcN : c ∈ Subgroup.normalizer (W : Set G))
    {g : G} : g ∈ W ⊔ Subgroup.zpowers c ↔ ∃ w ∈ W, ∃ k : ℤ, g = w * c ^ k := by
  have hset : ((W ⊔ Subgroup.zpowers c : Subgroup G) : Set G) =
      (W : Set G) * (Subgroup.zpowers c : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W (Subgroup.zpowers c)
      ((Subgroup.zpowers_le).2 hcN)
  constructor
  · intro hg
    have hg' : g ∈ ((W ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := hg
    rw [hset] at hg'
    obtain ⟨w, hw, _, ⟨k, rfl⟩, rfl⟩ := hg'
    exact ⟨w, hw, k, rfl⟩
  · rintro ⟨w, hw, k, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hw)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers c k))

omit [Finite G] in
theorem mem_normalizer_blk {c : G} (hcN : c ∈ Subgroup.normalizer (U : Set G))
    (hcK : convI hU ⟨c, hcN⟩ ∈ K₁) : c ∈ Subgroup.normalizer (blk hU K₁ : Set G) := by
  refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
  · have := conj_mem_blk hcN hx
    rwa [S1417.conjAut_eq_of_mem hcK] at this
  · have hcN' : c⁻¹ ∈ Subgroup.normalizer (U : Set G) := Subgroup.inv_mem _ hcN
    have := conj_mem_blk hcN' hx
    have hK : convI hU ⟨c⁻¹, hcN'⟩ ∈ K₁ := by
      rw [show (⟨c⁻¹, hcN'⟩ : ↥(Subgroup.normalizer (U : Set G))) = (⟨c, hcN⟩)⁻¹ from rfl,
        map_inv]
      exact K₁.inv_mem hcK
    rw [S1417.conjAut_eq_of_mem hK, inv_inv] at this
    exact this

variable (B : TwoBlocks hU H T K₁ K₂)
include B

omit [Finite G] in
theorem a4Data {c₁ : G} (hc₁N : c₁ ∈ Subgroup.normalizer (U : Set G)) (hc₁3 : c₁ ^ 3 = 1)
    (hc₁K : convI hU ⟨c₁, hc₁N⟩ ∈ K₁) (hc₁1 : convI hU ⟨c₁, hc₁N⟩ ≠ 1) :
    A4Data (blk hU K₁ ⊔ Subgroup.zpowers c₁) (blk hU K₁) c₁ := by
  have hφ3 : convI hU ⟨c₁, hc₁N⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c₁, hc₁N⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 3 = 1 := Subtype.ext hc₁3
    rw [this, map_one]
  have hst : ∀ l ∈ K₁, ∀ u ∈ commV K₁, l u ∈ commV K₁ := fun l hl u hu => commV_stable K₁ hl hu
  have hc1 : c₁ ≠ 1 := by
    rintro rfl
    exact hc₁1 ((convI_eq_one_iff hU _).2 (Subgroup.one_mem _))
  refine A4Data.of_fpf ?_ (fun w hw => hU.2 w (blk_le K₁ hw))
    (fun u hu v hv => B2F.isElemAbelian_comm hU (blk_le K₁ hu) (blk_le K₁ hv))
    (orderOf_eq_prime hc₁3 hc1) (mem_normalizer_blk hc₁N hc₁K) ?_
  · rw [card_blk]
    exact (S1417.card_of_actsAsNaturalL2 B.nat₁).2
  · intro w hw hw1 hfix
    obtain ⟨hwU, hwK⟩ := mem_blk.1 hw
    apply hw1
    have h1 : convI hU ⟨c₁, hc₁N⟩ (IntMod.mk hU ⟨w, hwU⟩) = IntMod.mk hU ⟨w, hwU⟩ := by
      apply IntMod.val_injective
      rw [convI_apply_val]
      exact hfix
    have := natL2_fix_eq_one B.nat₁ hst hc₁K hφ3 hc₁1 hwK h1
    exact congrArg IntMod.val this

omit [Finite G] in
theorem mem_blockX (htop : commV K₁ ⊔ commV K₂ = ⊤)
    (hCU : H ⊓ Subgroup.centralizer (U : Set G) ≤ U) {c₁ : G} (hc₁L : c₁ ∈ twoResidual H)
    (hc₁N : c₁ ∈ Subgroup.normalizer (U : Set G)) (hc₁3 : c₁ ^ 3 = 1)
    (hc₁K : convI hU ⟨c₁, hc₁N⟩ ∈ K₁) (hc₁1 : convI hU ⟨c₁, hc₁N⟩ ≠ 1) {c : G} (hcH : c ∈ H)
    (hcN : c ∈ Subgroup.normalizer (U : Set G)) (hc3 : c ^ 3 = 1)
    (hcK : convI hU ⟨c, hcN⟩ ∈ K₁) : c ∈ blk hU K₁ ⊔ Subgroup.zpowers c₁ := by
  have hφ3 : ∀ (d : G) (hd : d ∈ Subgroup.normalizer (U : Set G)), d ^ 3 = 1 →
      convI hU ⟨d, hd⟩ ^ 3 = 1 := fun d hd hd3 => by
    rw [← map_pow]
    have : (⟨d, hd⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 3 = 1 := Subtype.ext hd3
    rw [this, map_one]
  have hc₁H : c₁ ∈ H := twoResidual_le H hc₁L
  have hN := mem_normalizer_blk hc₁N hc₁K
  by_cases hc1 : convI hU ⟨c, hcN⟩ = 1
  · have hcU : c ∈ U := hCU ⟨hcH, (convI_eq_one_iff hU _).1 hc1⟩
    have h2 : c ^ 2 = 1 := hU.2 c hcU
    have : c = 1 := eq_one_of_pow_coprime h2 hc3 (by norm_num)
    rw [this]; exact Subgroup.one_mem _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1
    (natL2_mem_zpowers B.nat₁ hc₁K (hφ3 c₁ hc₁N hc₁3) hc₁1 hcK (hφ3 c hcN hc3))
  set d := c₁ ^ k with hd
  have hdN : d ∈ Subgroup.normalizer (U : Set G) := Subgroup.zpow_mem _ hc₁N k
  have hdv : convI hU ⟨d, hdN⟩ = convI hU ⟨c₁, hc₁N⟩ ^ k := by
    rw [← map_zpow]; rfl
  set u := c * d⁻¹ with hu
  have huN : u ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ hcN (Subgroup.inv_mem _ hdN)
  have huv : convI hU ⟨u, huN⟩ = 1 := by
    rw [show (⟨u, huN⟩ : ↥(Subgroup.normalizer (U : Set G))) = ⟨c, hcN⟩ * (⟨d, hdN⟩)⁻¹ from rfl,
      map_mul, map_inv, hdv, hk, mul_inv_cancel]
  have huU : u ∈ U := hCU ⟨H.mul_mem hcH (H.inv_mem (H.zpow_mem hc₁H k)),
    (convI_eq_one_iff hU _).1 huv⟩
  have hcud : c = u * d := by rw [hu]; group
  have huTop : IntMod.mk hU ⟨u, huU⟩ ∈ commV K₁ ⊔ commV K₂ := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨u₁, hu₁, u₂, hu₂, hu12⟩ := Subgroup.mem_sup.mp huTop
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = convI hU ⟨d, hdN⟩ := ⟨_, rfl⟩
  have hφv : φ = convI hU ⟨c, hcN⟩ := by rw [hφ, hdv, hk]
  have hφK : φ ∈ K₁ := hφv ▸ hcK
  have hφ1 : φ ≠ 1 := hφv ▸ hc1
  have hφ3' : φ ^ 3 = 1 := hφv ▸ hφ3 c hcN hc3
  have hd3 : d ^ 3 = 1 := by
    rw [hd, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc₁3, one_zpow]
  have hexp : c ^ 3 = u * (d * u * d⁻¹) * (d ^ 2 * u * (d ^ 2)⁻¹) * d ^ 3 := by
    rw [hcud, pow_three, pow_three, sq]; group
  rw [hc3, hd3, mul_one] at hexp
  have hφu : φ (IntMod.mk hU ⟨u, huU⟩) = IntMod.mk hU ⟨d * u * d⁻¹,
      (Subgroup.mem_normalizer_iff.mp hdN u).mp huU⟩ := by
    rw [hφ]
    apply IntMod.val_injective
    rw [convI_apply_val]; rfl
  have hd2N : d ^ 2 ∈ Subgroup.normalizer (U : Set G) := Subgroup.pow_mem _ hdN 2
  have hφφu : φ (φ (IntMod.mk hU ⟨u, huU⟩)) = IntMod.mk hU ⟨d ^ 2 * u * (d ^ 2)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hd2N u).mp huU⟩ := by
    rw [hφ]
    apply IntMod.val_injective
    rw [convI_apply_val, convI_apply_val]
    show d * (d * u * d⁻¹) * d⁻¹ = d ^ 2 * u * (d ^ 2)⁻¹
    rw [sq]; group
  have hprod : IntMod.mk hU ⟨u, huU⟩ * φ (IntMod.mk hU ⟨u, huU⟩) *
      φ (φ (IntMod.mk hU ⟨u, huU⟩)) = 1 := by
    rw [hφφu, hφu]
    apply IntMod.val_injective
    simp only [IntMod.val_mul, IntMod.val_one]
    exact hexp.symm
  have hfix₂ : φ u₂ = u₂ := B.apply_eq₁ hφK hu₂
  rw [← hu12, map_mul, map_mul, hfix₂, hfix₂] at hprod
  have hn₁ := B.norm_eq_one hφK hφ3' hφ1 hu₁
  have hu₂1 : u₂ = 1 := by
    have e : u₁ * u₂ * (φ u₁ * u₂) * (φ (φ u₁) * u₂) =
        (u₁ * φ u₁ * φ (φ u₁)) * (u₂ * u₂) * u₂ := by
      simp only [mul_comm, mul_assoc, mul_left_comm]
    rw [e, hn₁, ← sq, IntMod.sq_eq_one, one_mul, one_mul] at hprod
    exact hprod
  rw [hu₂1, mul_one] at hu12
  have hub : u ∈ blk hU K₁ := mem_blk.2 ⟨huU, hu12 ▸ hu₁⟩
  rw [mem_sup_zpowers_iff hN]
  exact ⟨u, hub, k, hcud⟩

omit [Finite G] B in
theorem convI_mem_of_mem_blockX {c₁ : G} (hc₁N : c₁ ∈ Subgroup.normalizer (U : Set G))
    (hc₁K : convI hU ⟨c₁, hc₁N⟩ ∈ K₁) {g : G} (hg : g ∈ blk hU K₁ ⊔ Subgroup.zpowers c₁)
    (hgN : g ∈ Subgroup.normalizer (U : Set G)) : convI hU ⟨g, hgN⟩ ∈ K₁ := by
  obtain ⟨w, hw, k, rfl⟩ := (mem_sup_zpowers_iff (mem_normalizer_blk hc₁N hc₁K)).1 hg
  have hwN : w ∈ Subgroup.normalizer (U : Set G) := Subgroup.le_normalizer (blk_le K₁ hw)
  have hw1 : convI hU ⟨w, hwN⟩ = 1 :=
    (convI_eq_one_iff hU _).2 (Subgroup.mem_centralizer_iff.2 fun v hv =>
      (B2F.isElemAbelian_comm hU hv (blk_le K₁ hw)))
  rw [show (⟨w * c₁ ^ k, hgN⟩ : ↥(Subgroup.normalizer (U : Set G))) =
    ⟨w, hwN⟩ * ⟨c₁, hc₁N⟩ ^ k from rfl, map_mul, map_zpow, hw1, one_mul]
  exact K₁.zpow_mem hc₁K k

omit [Finite G] B in
theorem mem_blk_of_mem_blockX {c₁ : G} (hc₁N : c₁ ∈ Subgroup.normalizer (U : Set G))
    (hc₁3 : c₁ ^ 3 = 1) (hc₁K : convI hU ⟨c₁, hc₁N⟩ ∈ K₁) {g : G}
    (hg : g ∈ blk hU K₁ ⊔ Subgroup.zpowers c₁) (hgU : g ∈ U) : g ∈ blk hU K₁ := by
  obtain ⟨w, hw, k, rfl⟩ := (mem_sup_zpowers_iff (mem_normalizer_blk hc₁N hc₁K)).1 hg
  have hck : c₁ ^ k ∈ U := by
    have e : c₁ ^ k = w⁻¹ * (w * c₁ ^ k) := by group
    rw [e]; exact U.mul_mem (U.inv_mem (blk_le K₁ hw)) hgU
  have h2 : (c₁ ^ k) ^ 2 = 1 := hU.2 _ hck
  have h3 : (c₁ ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc₁3, one_zpow]
  rw [eq_one_of_pow_coprime h2 h3 (by norm_num), mul_one]
  exact hw

theorem blockX_le_twoResidual (hUH : U ≤ H) {c₁ : G} (hc₁L : c₁ ∈ twoResidual H)
    (hc₁N : c₁ ∈ Subgroup.normalizer (U : Set G)) (hc₁3 : c₁ ^ 3 = 1)
    (hc₁K : convI hU ⟨c₁, hc₁N⟩ ∈ K₁) (hc₁1 : convI hU ⟨c₁, hc₁N⟩ ≠ 1) :
    blk hU K₁ ⊔ Subgroup.zpowers c₁ ≤ twoResidual H := by
  have hφ3 : convI hU ⟨c₁, hc₁N⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨c₁, hc₁N⟩ : ↥(Subgroup.normalizer (U : Set G))) ^ 3 = 1 := Subtype.ext hc₁3
    rw [this, map_one]
  refine sup_le ?_ ((Subgroup.zpowers_le).2 hc₁L)
  have hUN : U ≤ Subgroup.normalizer (twoResidual H : Set G) :=
    hUH.trans (le_normalizer_twoResidual H)
  have hle : commV K₁ ≤ commV (autI hU (twoResidual H)) := by
    rw [← commV_zpowers_eq B.nat₁ hc₁K hφ3 hc₁1]
    exact commV_mono' ((Subgroup.zpowers_le).2 (convI_mem_autI hU hc₁L hc₁N))
  exact (Subgroup.map_mono hle).trans (blk_autI_le hUN)

omit [Finite G] in
theorem conj_mem_blockX (htop : commV K₁ ⊔ commV K₂ = ⊤)
    (hCU : H ⊓ Subgroup.centralizer (U : Set G) ≤ U) {c₁ : G} (hc₁L : c₁ ∈ twoResidual H)
    (hc₁N : c₁ ∈ Subgroup.normalizer (U : Set G)) (hc₁3 : c₁ ^ 3 = 1)
    (hc₁K : convI hU ⟨c₁, hc₁N⟩ ∈ K₁) (hc₁1 : convI hU ⟨c₁, hc₁N⟩ ≠ 1) {g : G}
    (hg : g ∈ twoResidual H) {x : G} (hx : x ∈ blk hU K₁ ⊔ Subgroup.zpowers c₁) :
    g * x * g⁻¹ ∈ blk hU K₁ ⊔ Subgroup.zpowers c₁ := by
  have hgH : g ∈ H := twoResidual_le H hg
  have hgN : g ∈ Subgroup.normalizer (U : Set G) := B.le_norm hgH
  have hgK : B1.conjAut (convI hU ⟨g, hgN⟩) K₁ = K₁ :=
    B.conjAut_K1 (B.autI_twoResidual_le (convI_mem_autI hU hg hgN))
  have hN := mem_normalizer_blk hc₁N hc₁K
  obtain ⟨w, hw, k, rfl⟩ := (mem_sup_zpowers_iff hN).1 hx
  have e : g * (w * c₁ ^ k) * g⁻¹ = (g * w * g⁻¹) * (g * c₁ * g⁻¹) ^ k := by
    rw [conj_zpow]; group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.zpow_mem _ ?_ k)
  · have := conj_mem_blk hgN hw
    rwa [hgK] at this
  ·
    have hc₁H : c₁ ∈ H := twoResidual_le H hc₁L
    have hcN' : g * c₁ * g⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hc₁N) (Subgroup.inv_mem _ hgN)
    refine B.mem_blockX htop hCU hc₁L hc₁N hc₁3 hc₁K hc₁1
      (H.mul_mem (H.mul_mem hgH hc₁H) (H.inv_mem hgH)) hcN' ?_ ?_
    · rw [conj_pow, hc₁3]; group
    · have hv : convI hU ⟨g * c₁ * g⁻¹, hcN'⟩ =
          convI hU ⟨g, hgN⟩ * convI hU ⟨c₁, hc₁N⟩ * (convI hU ⟨g, hgN⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [hv, ← hgK, B1.mem_conjAut]
      simpa [mul_assoc] using hc₁K

end TwoBlocks

end CFSG.Quasithin.H13.A5
