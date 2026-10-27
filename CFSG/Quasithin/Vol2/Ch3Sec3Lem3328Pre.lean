module

public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

namespace Lem3328

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_pow_odd {N : Subgroup G} {x : G} {b e : ℕ} (hb : Odd b) (hxb : x ^ b ∈ N)
    (hxe : x ^ 2 ^ e ∈ N) : x ∈ N := by
  have hcop : Nat.Coprime b (2 ^ e) :=
    Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hb)
  have hgcd := Nat.gcd_eq_gcd_ab b (2 ^ e)
  rw [hcop, Nat.cast_one] at hgcd
  have hx1 : x = (x ^ b) ^ (Nat.gcdA b (2 ^ e)) * (x ^ 2 ^ e) ^ (Nat.gcdB b (2 ^ e)) := by
    rw [← zpow_natCast, ← zpow_natCast (x) (2 ^ e), ← zpow_mul, ← zpow_mul, ← zpow_add,
      ← hgcd, zpow_one]
  rw [hx1]
  exact N.mul_mem (N.zpow_mem hxb _) (N.zpow_mem hxe _)

theorem le_of_two_mod_of_isShort2 {L K N : Subgroup G} (hL : IsShort2 L)
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) (hO : pCoreOf 2 L ≤ N) (hKL : K ≤ L)
    (hLK : L ≤ Subgroup.normalizer (K : Set G))
    (h2 : ∀ k ∈ K, ∃ e : ℕ, k ^ 2 ^ e ∈ N) : K ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPO : ∀ p : ↥L, p ∈ CFSG.pCore 2 ↥L → (p : G) ∈ N := by
    intro p hp
    refine hO ⟨p, ?_, rfl⟩
    exact hp
  rcases hL.2.2.2.1 with hq | h3
  · have hKn : (K.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr hLK
    have hKn' : ((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
      hKn.map _ (QuotientGroup.mk'_surjective _)
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
        (B1Red.isQuasisimple_to_open hq)
        ((K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with hc | ht
    · intro k hk
      set kL : ↥L := ⟨k, hKL hk⟩ with hkL
      set y := QuotientGroup.mk' (CFSG.pCore 2 ↥L) kL with hy
      have hz : y ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
        hc ⟨kL, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
      have hyb : (y ^ b) ^ 2 ^ a = 1 := by
        rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
      have hzb : Subgroup.zpowers (y ^ b) ≤ CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) := by
        refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup ⟨fun n hn g => ?_⟩
          (isPGroup_zpowers_of_pow hyb)
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
        have hcz : (y ^ b) ^ i ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
          Subgroup.zpow_mem _ (Subgroup.pow_mem _ hz b) i
        rw [Subgroup.mem_center_iff.mp hcz g, mul_inv_cancel_right]
        exact Subgroup.zpow_mem_zpowers _ i
      rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hzb
      have hyb1 : y ^ b = 1 := Subgroup.mem_bot.mp (hzb (Subgroup.mem_zpowers _))
      have hkb : k ^ b ∈ N := by
        have : kL ^ b ∈ CFSG.pCore 2 ↥L := by
          rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
          exact hyb1
        have := hPO _ this
        simpa [hkL] using this
      obtain ⟨e, he⟩ := h2 k hk
      exact mem_of_pow_odd hb hkb he
    · have hn : (N.subgroupOf L).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr fun l hl =>
          mem_normalizer_inf (hLN hl) (Subgroup.le_normalizer hl)
      have hp : IsPGroup 2 (↥L ⧸ N.subgroupOf L) := by
        intro q
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
        have hl : QuotientGroup.mk' (CFSG.pCore 2 ↥L) l ∈
            (K.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := ht ▸ Subgroup.mem_top _
        obtain ⟨k, hk, hkl⟩ := hl
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
        obtain ⟨e, he⟩ := h2 k (Subgroup.mem_subgroupOf.mp hk)
        refine ⟨e, ?_⟩
        have hq' : (l : ↥L ⧸ N.subgroupOf L) = (k : ↥L ⧸ N.subgroupOf L) := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have := Subgroup.inv_mem _ (hPO _ hkl)
          simpa using this
        rw [hq', ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using he
      have htop := hL.1 (N.subgroupOf L) hp
      intro k hk
      have : (⟨k, hKL hk⟩ : ↥L) ∈ N.subgroupOf L := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  ·
    intro k hk
    have hk3 : k ^ 3 ∈ N := by
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨k, hKL hk⟩) ^ 3 = 1 := by
        rw [← h3]
        exact pow_card_eq_one'
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      have := hPO _ h1
      simpa using this
    obtain ⟨e, he⟩ := h2 k hk
    exact mem_of_pow_odd (by decide) hk3 he

theorem not_hasNoncentralTwoChief_two_of_isShort2 {L : Subgroup G} (hL : IsShort2 L) :
    ¬ HasNoncentralTwoChief L 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨A, B, hAB, hle⟩
  have hQL : blockQ L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) := fun x hx =>
    mem_normalizer_commutator (hLQ hx) (Subgroup.le_normalizer hx)
  have hLZ : L ≤ Subgroup.normalizer (blockZ L : Set G) := fun x hx =>
    mem_normalizer_inf (hLU hx)
      (B2F.normalizer_le_normalizer_centralizer L (Subgroup.le_normalizer hx))
  have hUL : blockU L ≤ L := commutator_le_right_of_le_normalizer
    (hQL.trans Subgroup.le_normalizer)
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hZC : blockZ L ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  obtain ⟨hZlt, hirr⟩ := hL.2.2.2.2
  have key : ∀ A B : Subgroup G, IsTwoChiefFactor L A B → ¬ ⁅A, L⁆ ≤ B →
      B ⊓ blockU L ≤ blockZ L ∧ (A ⊓ blockU L) ⊔ blockZ L = blockU L := by
    intro A B hc hnc
    obtain ⟨hBA, hAL, hLA, hLB, hmin, h2⟩ := hc
    have hZB : blockZ L ≤ Subgroup.normalizer (B : Set G) := (hZU.trans hUL).trans hLB
    have hBZ : ⁅A, L⁆ ≤ B ⊔ blockZ L → False := by
      intro hle'
      set Y := A ⊓ (B ⊔ blockZ L) with hY
      have hBY : B ≤ Y := le_inf hBA.le le_sup_left
      have hLY : L ≤ Subgroup.normalizer (Y : Set G) := fun x hx =>
        mem_normalizer_inf (hLA hx) (mem_normalizer_sup (hLB hx) (hLZ hx))
      by_cases hYB : Y = B
      · apply hnc
        have : ⁅A, L⁆ ≤ Y := le_inf (commutator_le_left_of_le_normalizer hLA) hle'
        rwa [hYB] at this
      · by_cases hYA : Y = A
        · apply hnc
          rw [Subgroup.commutator_le]
          intro a ha l hl
          have haY : a ∈ B ⊔ blockZ L := by
            have : a ∈ Y := hYA ▸ ha
            exact this.2
          obtain ⟨b, hb, z, hz, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hZB).mp haY
          have hzl : z * l = l * z := (Subgroup.mem_centralizer_iff.mp (hZC hz) l hl).symm
          have e : ⁅b * z, l⁆ = b * (l * b⁻¹ * l⁻¹) := by
            rw [commutatorElement_def]
            calc b * z * l * (b * z)⁻¹ * l⁻¹ = b * (z * l) * z⁻¹ * b⁻¹ * l⁻¹ := by group
              _ = b * (l * z) * z⁻¹ * b⁻¹ * l⁻¹ := by rw [hzl]
              _ = b * (l * b⁻¹ * l⁻¹) := by group
          rw [e]
          exact B.mul_mem hb ((Subgroup.mem_normalizer_iff.mp (hLB hl) _).mp (B.inv_mem hb))
        · exact hmin Y (lt_of_le_of_ne hBY (Ne.symm hYB)) (lt_of_le_of_ne inf_le_left hYA) hLY
    have hAQ : A ≤ B ⊔ blockQ L :=
      le_of_two_mod_of_isShort2 hL (fun x hx => mem_normalizer_sup (hLB hx) (hLQ hx))
        le_sup_right hAL hLA fun a ha => by
          obtain ⟨k, hk⟩ := h2 a ha
          exact ⟨k, Subgroup.mem_sup_left hk⟩
    have hAU : ⁅A, L⁆ ≤ B ⊔ blockU L := by
      rw [Subgroup.commutator_le]
      intro a ha l hl
      obtain ⟨b, hb, q, hq, rfl⟩ :=
        (B19Aux.mem_sup_iff_of_le_normalizer (hQL.trans hLB)).mp (hAQ ha)
      have e : ⁅b * q, l⁆ = b * ⁅q, l⁆ * (l * b⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hb)
        (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hq hl)))
        (Subgroup.mem_sup_left ?_)
      exact (Subgroup.mem_normalizer_iff.mp (hLB hl) _).mp (B.inv_mem hb)
    refine ⟨?_, ?_⟩
    · rcases hirr ((B ⊓ blockU L) ⊔ blockZ L) le_sup_right (sup_le inf_le_right hZU)
          (fun x hx => mem_normalizer_sup (mem_normalizer_inf (hLB hx) (hLU hx)) (hLZ hx))
        with h | h
      · exact le_sup_left.trans h.le
      · exfalso
        apply hBZ
        refine hAU.trans (sup_le le_sup_left ?_)
        rw [← h]
        exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
    · rcases hirr ((A ⊓ blockU L) ⊔ blockZ L) le_sup_right (sup_le inf_le_right hZU)
          (fun x hx => mem_normalizer_sup (mem_normalizer_inf (hLA hx) (hLU hx)) (hLZ hx))
        with h | h
      · exfalso
        apply hBZ
        intro x hx
        have hxA : x ∈ A := commutator_le_left_of_le_normalizer hLA hx
        obtain ⟨b, hb, u, hu, rfl⟩ :=
          (B19Aux.mem_sup_iff_of_le_normalizer (hUL.trans hLB)).mp (hAU hx)
        have huA : u ∈ A := by
          have := A.mul_mem (A.inv_mem (hBA.le hb)) hxA
          simpa using this
        have huZ : u ∈ blockZ L := h ▸ Subgroup.mem_sup_left ⟨huA, hu⟩
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right huZ)
      · exact h
  obtain ⟨-, h1⟩ := key (A 0) (B 0) (hAB 0).1 (hAB 0).2
  obtain ⟨h2, -⟩ := key (A 1) (B 1) (hAB 1).1 (hAB 1).2
  have h01 := hle 0 1 (by decide)
  apply hZlt.not_ge
  rw [← h1]
  refine sup_le ?_ le_rfl
  intro x hx
  exact h2 ⟨h01 hx.1, hx.2⟩

omit [Finite G] in
theorem mem_centralizer_of_commutator_mem_blockZ {L : Subgroup G} (hL : IsShort2 L) {x : G}
    (hx : ∀ ℓ ∈ L, ⁅x, ℓ⁆ ∈ blockZ L) : x ∈ Subgroup.centralizer (L : Set G) := by
  have hcen : ∀ ℓ ∈ L, ∀ m ∈ L, m * ⁅x, ℓ⁆ = ⁅x, ℓ⁆ * m := fun ℓ hℓ m hm =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hx ℓ hℓ)).2 m hm
  let φ : ↥L →* G :=
    { toFun := fun ℓ => ⁅x, (ℓ : G)⁆
      map_one' := by simp [commutatorElement_def]
      map_mul' := by
        intro a b
        have e : ⁅x, (a : G) * b⁆ = ⁅x, (a : G)⁆ * ((a : G) * ⁅x, (b : G)⁆ * (a : G)⁻¹) := by
          simp only [commutatorElement_def]
          group
        simp only [Subgroup.coe_mul]
        rw [e, hcen b b.2 a a.2, mul_inv_cancel_right] }
  have hp : IsPGroup 2 (↥L ⧸ φ.ker) := by
    intro q
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨1, ?_⟩
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
    exact hL.2.2.1.2 _ (Subgroup.mem_inf.mp (hx ℓ ℓ.2)).1
  have htop := hL.1 φ.ker hp
  rw [Subgroup.mem_centralizer_iff]
  intro ℓ hℓ
  have h1 : (⟨ℓ, hℓ⟩ : ↥L) ∈ φ.ker := htop ▸ Subgroup.mem_top _
  have h2 : ⁅x, ℓ⁆ = 1 := h1
  rw [commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2.symm

omit [Finite G] in
theorem inf_centralizer_le_of_isLnBlock {L V : Subgroup G} (hL : IsLnBlock L 3)
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (V : Set G)) :
    L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
  obtain ⟨-, α, hαs, hαk, -⟩ := hL
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Vol2Native.A312L.Seven.slThree_isSimple
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm.isSimpleGroup
  set N := (L ⊓ Subgroup.centralizer (V : Set G)).subgroupOf L with hN
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
    fun l hl => mem_normalizer_inf (Subgroup.le_normalizer hl)
      (B2F.normalizer_le_normalizer_centralizer V (hLV hl))
  have hNn' : (N.map α).Normal := hNn.map _ hαs
  have hPO : ∀ p : ↥L, p ∈ CFSG.pCore 2 ↥L → (p : G) ∈ pCoreOf 2 L := by
    intro p hp
    refine ⟨p, ?_, rfl⟩
    exact hp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map α) with hb | ht
  · intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥L) ∈ N := Subgroup.mem_subgroupOf.mpr hx
    have h1 : α ⟨x, hx.1⟩ = 1 := by
      have : α ⟨x, hx.1⟩ ∈ N.map α := ⟨_, hxN, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact this
    have h2 : (⟨x, hx.1⟩ : ↥L) ∈ α.ker := h1
    rw [hαk] at h2
    exact hPO _ h2
  · exfalso
    apply hnt
    intro l hl
    have hl' : α ⟨l, hl⟩ ∈ N.map α := ht ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnl⟩ := hl'
    have hk : n⁻¹ * ⟨l, hl⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnl, inv_mul_cancel]
    rw [hαk] at hk
    have h1 := hO (hPO _ hk)
    have h2 : (n : G) ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_subgroupOf.mp hn).2
    have := Subgroup.mul_mem _ h2 h1
    simpa using this

omit [Finite G] in
theorem exists_pow_mul {L : Subgroup G} {t : G} (ht : t ∈ Subgroup.normalizer (L : Set G))
    {l : G} (hl : l ∈ L) : ∀ n : ℕ, ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
  intro n
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', he⟩ := ih
    refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' ?_, ?_⟩
    · have htn : t ^ n ∈ Subgroup.normalizer (L : Set G) := Subgroup.pow_mem _ ht n
      exact (Subgroup.mem_normalizer_iff.mp htn l).mp hl
    · rw [pow_succ, he, pow_succ]
      group

omit [Finite G] in
theorem sup_inf_centralizer_le_pCoreOf {L T V : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hV : L ⊔ T ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx)
      (B2F.normalizer_le_normalizer_centralizer V (hV hx))) ?_
  intro x
  obtain ⟨l, hl, t, ht, hx⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp (Subgroup.mem_inf.mp x.2).1
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨l', hl', he⟩ := exists_pow_mul (hTL ht) hl (2 ^ k)
  rw [htk, mul_one] at he
  have hxL : (x : G) ^ 2 ^ k ∈ L := by rw [hx, he]; exact hl'
  have hxC : (x : G) ^ 2 ^ k ∈ Subgroup.centralizer (V : Set G) :=
    Subgroup.pow_mem _ (Subgroup.mem_inf.mp x.2).2 _
  obtain ⟨m, hm⟩ := hC ⟨_, Subgroup.mem_inf.mpr ⟨hxL, hxC⟩⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have := congrArg Subtype.val hm
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
  rw [pow_add, pow_mul]
  exact this

theorem isElemAbelian_of_frattini_eq_bot {T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (h : frattini ↥T = ⊥) : IsElemAbelian 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 ↥T) := ⟨hT⟩
  have hF := CFSG.frattini_eq_closure_commutator_union_powers (R := ↥T) (p := 2)
  rw [h] at hF
  have hsq : ∀ y : ↥T, y ^ 2 = 1 := fun y => by
    have : y ^ 2 ∈ (⊥ : Subgroup ↥T) := hF ▸ Subgroup.subset_closure (Or.inr ⟨y, rfl⟩)
    rwa [Subgroup.mem_bot] at this
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => by simpa using congrArg Subtype.val (hsq ⟨x, hx⟩)⟩
  have hc : ⁅a, b⁆ ∈ (⊥ : Subgroup ↥T) :=
    hF ▸ Subgroup.subset_closure (Or.inl (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top a) (Subgroup.mem_top b)))
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem frattini_eq_bot_of_isElemAbelian {T : Subgroup G} (hT : IsElemAbelian 2 T) :
    frattini ↥T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 ↥T := fun x =>
    ⟨1, Subtype.ext (by simpa using hT.2 x x.2)⟩
  have : Fact (IsPGroup 2 ↥T) := ⟨hT2⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥T) (p := 2), eq_bot_iff,
    Subgroup.closure_le]
  rintro x (hx | ⟨y, rfl⟩)
  · have hle : _root_.commutator ↥T ≤ ⊥ := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro a _ b _
      have hab : a * b = b * a := Subtype.ext (by
        have := hT.1
        exact setLike_mul_comm a.2 b.2)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab
    exact hle hx
  · show y ^ 2 ∈ (⊥ : Subgroup ↥T)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa using hT.2 y y.2)

end Lem3328

end CFSG.Quasithin.H13
