module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3314F
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122ASimple
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319A
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319B

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ins314

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open CFSG.Quasithin.H13.L3319
open CFSG.QuasithinUnique.Vol2Native.L122A (isSimpleGroup_of_a38Types)
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

omit [Finite G] in
theorem conjSub_autOn {V X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G)) (x : ↥X)
    (K : Subgroup G) :
    conjSub (conjOf V X hX x) (autOn K V) = autOn (conjSub (x : G) K) V :=
  (autOn_map_conj (hX x.2)).symm

omit [Finite G] in
theorem conjOf_mem_autOn {V X K : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    {x : ↥X} (hx : (x : G) ∈ K) : conjOf V X hX x ∈ autOn K V :=
  ⟨Subgroup.inclusion hX x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

omit [Finite G] in
theorem exists_conjOf_eq {V X K : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hKX : K ≤ X) {a : MulAut ↥V} (ha : a ∈ autOn K V) :
    ∃ x : ↥X, (x : G) ∈ K ∧ conjOf V X hX x = a := by
  rw [← map_conjOf hX hKX] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩

omit [Finite G] in
theorem inf_centralizer_le_pCore {V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (h38T : A38Types (↥L ⧸ CFSG.pCore 2 ↥L))
    (h2 : ¬ IsPGroup 2 ↥(autOn L V)) {x : G} (hxL : x ∈ L)
    (hxC : x ∈ Subgroup.centralizer (V : Set G)) : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := isSimpleGroup_of_a38Types h38T
  set f := conjOf V L hLV with hf
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hq
  have hN : (f.ker.map q).Normal :=
    (MonoidHom.normal_ker f).map q (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (f.ker.map q) with h | h
  · have hk : (⟨x, hxL⟩ : ↥L) ∈ f.ker := (conjOf_eq_one_iff hLV _).mpr hxC
    have h1 : q ⟨x, hxL⟩ = 1 := by
      have := Subgroup.mem_map_of_mem q hk
      rw [h] at this
      exact this
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    apply h2
    have hP : IsPGroup 2 ((CFSG.pCore 2 ↥L).map f) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map f
    refine hP.to_le ?_
    rw [← range_conjOf hLV]
    rintro _ ⟨l, rfl⟩
    have hl : q l ∈ f.ker.map q := h ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnl⟩ := hl
    have ho : n⁻¹ * l ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq]
      exact hnl
    refine ⟨n⁻¹ * l, ho, ?_⟩
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]

omit [Finite G] in
theorem exists_two_pow_mem {K : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ T ⊔ K) :
    ∃ b : ℕ, x ^ 2 ^ b ∈ K := by
  have hx' : x ∈ ((T ⊔ K : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right T K hTK] at hx'
  obtain ⟨τ, hτ, m, hm, rfl⟩ := hx'
  have key : ∀ n : ℕ, ∃ m' ∈ K, (τ * m) ^ n = τ ^ n * m' := by
    intro n
    induction n with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨m', hm', e⟩ := ih
      refine ⟨τ⁻¹ * m' * τ * m, K.mul_mem ?_ hm, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hTK (T.inv_mem hτ)) m').mp hm'
        simpa using this
      · rw [pow_succ, e, pow_succ]
        group
  obtain ⟨b, hb⟩ := hT2 ⟨τ, hτ⟩
  have hb' : τ ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  obtain ⟨m', hm', e⟩ := key (2 ^ b)
  exact ⟨b, by rw [e, hb', one_mul]; exact hm'⟩

omit [Finite G] in
theorem mem_subgroupOf_iff_conj {W A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) (hA : conjSub x A = A) (v : ↥W) :
    v ∈ A.subgroupOf W ↔ conjAct W ⟨x, hx⟩ v ∈ A.subgroupOf W := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAct_coe]
  constructor
  · intro h
    rw [← hA]
    exact mul_mem_conjSub h
  · intro h
    rw [← hA, mem_conjSub] at h
    simpa [mul_assoc] using h

omit [Finite G] in
theorem iff_sup_of_iff {W : Type} [Group W] (φ : MulAut W) {B₁ B₂ : Subgroup W}
    (h₁ : ∀ v, v ∈ B₁ ↔ φ v ∈ B₁) (h₂ : ∀ v, v ∈ B₂ ↔ φ v ∈ B₂) :
    ∀ v, v ∈ B₁ ⊔ B₂ ↔ φ v ∈ B₁ ⊔ B₂ := by
  have hm : ∀ {B : Subgroup W}, (∀ v, v ∈ B ↔ φ v ∈ B) → B.map φ.toMonoidHom = B := by
    intro B h
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (h v).mp hv
    · intro hw
      refine ⟨φ⁻¹ w, (h _).mpr ?_, ?_⟩
      · simpa using hw
      · simp
  have hsup : (B₁ ⊔ B₂).map φ.toMonoidHom = B₁ ⊔ B₂ := by
    rw [Subgroup.map_sup, hm h₁, hm h₂]
  intro v
  constructor
  · intro hv
    rw [← hsup]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← hsup] at hv
    obtain ⟨w, hw, e⟩ := hv
    have : w = v := φ.injective e
    rwa [← this]

variable (T M L) in
structure Sett (t : G) : Prop where
  s : Setup331 G T M L
  ht : t ∈ T
  htn : t ∉ Subgroup.normalizer (L : Set G)
  hM : mPlus L T = L ⊔ CFSG.conjugate L t
  comm : ∀ a ∈ autOn L (vPlus L T), ∀ b ∈ autOn (CFSG.conjugate L t) (vPlus L T), a * b = b * a
  hbot : autOn L (vPlus L T) ⊓ autOn (CFSG.conjugate L t) (vPlus L T) = ⊥
  h37 : A37ForSQTKCat
  h38 : A38ForSQTKCat
  card : Nat.card ↥(autOn L (vPlus L T)) = 168

namespace Sett

variable {t : G} (e : Sett T M L t)
include e

theorem hT : ¬ T ≤ Subgroup.normalizer (L : Set G) := fun h => e.htn (h e.ht)

theorem hX : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) :=
  (Hyp331.vPlus_reduced e.s).2.2.2.1

theorem tinv_mem : t⁻¹ ∈ L ⊔ T := (L ⊔ T).inv_mem (Subgroup.mem_sup_right e.ht)

theorem L2_le : CFSG.conjugate L t ≤ L ⊔ T := by
  rintro _ ⟨l, hl, rfl⟩
  have h := (L ⊔ T).mul_mem ((L ⊔ T).mul_mem e.tinv_mem (Subgroup.mem_sup_left hl))
    ((L ⊔ T).inv_mem e.tinv_mem)
  simpa [MulAut.conj_apply] using h

theorem not_isPGroup : ¬ IsPGroup 2 ↥(autOn L (vPlus L T)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h
  rw [e.card] at hn
  have h1 : n ≤ 7 := by
    by_contra h1
    have : 2 ^ 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hn] at this
    norm_num at this
  interval_cases n <;> norm_num at hn

theorem ne_bot : autOn L (vPlus L T) ≠ ⊥ := by
  intro h
  have := e.card
  rw [h, Subgroup.card_bot] at this
  omega

theorem dich (x : ↥(L ⊔ T)) :
    conjSub (conjOf (vPlus L T) (L ⊔ T) e.hX x) (autOn L (vPlus L T)) = autOn L (vPlus L T) ∨
      conjSub (conjOf (vPlus L T) (L ⊔ T) e.hX x) (autOn L (vPlus L T)) =
        autOn (CFSG.conjugate L t) (vPlus L T) := by
  rw [conjSub_autOn]
  rcases map_conj_of_setup e.s e.h37 e.h38 e.hT e.ht e.htn x.2 with h | h
  · exact Or.inl (congrArg (fun K => autOn K (vPlus L T)) h)
  · exact Or.inr (congrArg (fun K => autOn K (vPlus L T)) h)

theorem conjSub_tinv :
    conjSub (conjOf (vPlus L T) (L ⊔ T) e.hX ⟨t⁻¹, e.tinv_mem⟩) (autOn L (vPlus L T)) =
      autOn (CFSG.conjugate L t) (vPlus L T) := by
  rw [conjSub_autOn]
  rfl

theorem conjSub_L_eq {x : ↥(L ⊔ T)}
    (hx : conjSub (conjOf (vPlus L T) (L ⊔ T) e.hX x) (autOn L (vPlus L T)) =
      autOn L (vPlus L T)) : conjSub (x : G) L = L := by
  rcases map_conj_of_setup e.s e.h37 e.h38 e.hT e.ht e.htn x.2 with h | h
  · exact h
  · exfalso
    rw [conjSub_autOn] at hx
    have h1 : autOn (CFSG.conjugate L t) (vPlus L T) = autOn L (vPlus L T) := by
      rw [← hx]
      exact congrArg (fun K => autOn K (vPlus L T)) h.symm
    apply e.ne_bot
    rw [← e.hbot, h1, inf_idem]

theorem L2_mem_cComp : CFSG.conjugate L t ∈ cComp (L ⊔ T) :=
  map_conj_mem_cComp e.s.mem_cComp e.tinv_mem

theorem coe_mPlus :
    ((mPlus L T : Subgroup G) : Set G) = (CFSG.conjugate L t : Set G) * (L : Set G) := by
  rw [e.hM, sup_comm]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (le_normalizer_of_mem_cComp e.s.mem_cComp e.L2_mem_cComp)

theorem exists_two_pow_mem_mPlus (x : G) (hx : x ∈ L ⊔ T) : ∃ b : ℕ, x ^ 2 ^ b ∈ mPlus L T := by
  refine exists_two_pow_mem e.s.sylow.1 (le_normalizer_conjClosure_right L T) ?_
  rw [sup_comm, conjClosure_sup_eq]
  exact hx

theorem exists_pow_eq_one (x : ↥(L ⊔ T))
    (hx : conjOf (vPlus L T) (L ⊔ T) e.hX x = 1) : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := vPlus L T
  obtain ⟨b, hb⟩ := e.exists_two_pow_mem_mPlus x x.2
  have hb' : (x : G) ^ 2 ^ b ∈ ((CFSG.conjugate L t : Subgroup G) : Set G) * (L : Set G) := by
    rw [← e.coe_mPlus]
    exact hb
  obtain ⟨l₂, hl₂, l, hl, hll⟩ := hb'
  have hl₂X : l₂ ∈ L ⊔ T := e.L2_le hl₂
  have hlX : l ∈ L ⊔ T := Subgroup.mem_sup_left hl
  have hρ : conjOf V (L ⊔ T) e.hX ⟨l₂, hl₂X⟩ * conjOf V (L ⊔ T) e.hX ⟨l, hlX⟩ = 1 := by
    rw [← map_mul]
    have : (⟨l₂, hl₂X⟩ * ⟨l, hlX⟩ : ↥(L ⊔ T)) = x ^ 2 ^ b := Subtype.ext (by simpa using hll)
    rw [this, map_pow, hx, one_pow]
  have hmem : conjOf V (L ⊔ T) e.hX ⟨l, hlX⟩ ∈
      autOn L V ⊓ autOn (CFSG.conjugate L t) V := by
    refine ⟨conjOf_mem_autOn e.hX hl, ?_⟩
    have : conjOf V (L ⊔ T) e.hX ⟨l, hlX⟩ = (conjOf V (L ⊔ T) e.hX ⟨l₂, hl₂X⟩)⁻¹ :=
      eq_inv_of_mul_eq_one_right hρ
    rw [this]
    exact Subgroup.inv_mem _ (conjOf_mem_autOn e.hX hl₂)
  rw [e.hbot, Subgroup.mem_bot] at hmem
  have hmem₂ : conjOf V (L ⊔ T) e.hX ⟨l₂, hl₂X⟩ = 1 := by
    rw [hmem, mul_one] at hρ
    exact hρ
  have hlC : l ∈ Subgroup.centralizer (V : Set G) :=
    (conjOf_eq_one_iff e.hX ⟨l, hlX⟩).mp hmem
  have hl₂C : l₂ ∈ Subgroup.centralizer (V : Set G) :=
    (conjOf_eq_one_iff e.hX ⟨l₂, hl₂X⟩).mp hmem₂
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans e.hX
  have h38T := a38Types_of_setup e.s e.h37 e.h38 e.hT
  have hsub : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp e.s.mem_cComp)
  have hO : ∀ y ∈ L, y ∈ Subgroup.centralizer (V : Set G) → y ∈ pCoreOf 2 (L ⊔ T) := by
    intro y hy hyC
    apply hsub
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    exact inf_centralizer_le_pCore hLV h38T e.not_isPGroup hy hyC
  have hl₂' : l₂ ∈ pCoreOf 2 (L ⊔ T) := by
    obtain ⟨l₀, hl₀, rfl⟩ := hl₂
    have hl₀C : l₀ ∈ Subgroup.centralizer (V : Set G) := by
      have htV : t ∈ Subgroup.normalizer (V : Set G) := e.hX (Subgroup.mem_sup_right e.ht)
      have h1 := Subgroup.mem_centralizer_iff.mp hl₂C
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hv' : t⁻¹ * v * t ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htV) v).mp hv
        simpa using this
      have h2 := h1 _ hv'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h2
      have h3 : t * (t⁻¹ * v * t * (t⁻¹ * l₀ * t)) * t⁻¹ =
          t * (t⁻¹ * l₀ * t * (t⁻¹ * v * t)) * t⁻¹ := by rw [h2]
      simpa [mul_assoc] using h3
    have h1 := hO l₀ hl₀ hl₀C
    have h2 := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) e.tinv_mem) l₀).mp h1
    simpa [MulAut.conj_apply] using h2
  have hll' : (x : G) ^ 2 ^ b ∈ pCoreOf 2 (L ⊔ T) := by
    rw [← hll]
    exact Subgroup.mul_mem _ hl₂' (hO l hl hlC)
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨_, hll'⟩
  refine ⟨b + m, Subtype.ext ?_⟩
  have := congrArg Subtype.val hm
  simp only [SubmonoidClass.mk_pow, OneMemClass.coe_one] at this
  simpa [pow_add, pow_mul] using this

theorem exists_pow_eq_mul (x : ↥(L ⊔ T)) :
    ∃ n : ℕ, ∃ a ∈ autOn L (vPlus L T), ∃ b ∈ autOn (CFSG.conjugate L t) (vPlus L T),
      conjOf (vPlus L T) (L ⊔ T) e.hX x ^ 2 ^ n = a * b := by
  obtain ⟨n, hn⟩ := e.exists_two_pow_mem_mPlus x x.2
  have hn' : (x : G) ^ 2 ^ n ∈ ((CFSG.conjugate L t : Subgroup G) : Set G) * (L : Set G) := by
    rw [← e.coe_mPlus]
    exact hn
  obtain ⟨l₂, hl₂, l, hl, hll⟩ := hn'
  have hl₂X : l₂ ∈ L ⊔ T := e.L2_le hl₂
  have hlX : l ∈ L ⊔ T := Subgroup.mem_sup_left hl
  refine ⟨n, conjOf (vPlus L T) (L ⊔ T) e.hX ⟨l, hlX⟩, conjOf_mem_autOn e.hX hl,
    conjOf (vPlus L T) (L ⊔ T) e.hX ⟨l₂, hl₂X⟩, conjOf_mem_autOn e.hX hl₂, ?_⟩
  have h1 : x ^ 2 ^ n = (⟨l₂, hl₂X⟩ * ⟨l, hlX⟩ : ↥(L ⊔ T)) := Subtype.ext (by simpa using hll.symm)
  rw [← map_pow, h1, map_mul]
  exact e.comm _ (conjOf_mem_autOn e.hX hl) _ (conjOf_mem_autOn e.hX hl₂) |>.symm

end Sett

end CFSG.Quasithin.H13.Ins314
