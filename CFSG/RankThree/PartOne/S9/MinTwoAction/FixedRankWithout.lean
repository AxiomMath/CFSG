module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankTwoAction
public import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

open scoped commutatorElement IsMulCommutative

namespace CFSG.RankThree.PartOne.FixedRank36

open CFSG SemidirectProduct CFSG.RankThree.GroupTheory

section Helpers

variable {G : Type*} [Group G]

theorem conjHom_compat (A R X : Subgroup G) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (a : ↥A) : (conjHom R X hRX).comp (conjHom A R hAR a).toMonoidHom =
      (MulAut.conj (conjHom A X hAX a)).toMonoidHom.comp (conjHom R X hRX) := by
  refine MonoidHom.ext fun r => MulEquiv.ext fun x => Subtype.ext ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply]
  simp only [coe_conjHom, coe_conjHom_inv]
  group

theorem isExtraspecialPGroup_of_equiv {p : ℕ} {M N : Type*} [Group M] [Group N] (e : M ≃* N)
    (h : IsExtraspecialPGroup p M) : IsExtraspecialPGroup p N := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hcen : (Subgroup.center M).map e.toMonoidHom = Subgroup.center N := by
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro hx g
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact hx (e.symm g)
    · intro hx g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx (e g)
  have hc : (commutator M).map e.toMonoidHom = commutator N := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hf : (frattini M).map e.toMonoidHom = frattini N :=
    OrderIso.map_radical (MulEquiv.mapSubgroup e)
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, hcen]
  · rw [← hf, hfrat, hcen]
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hcard]

end Helpers


section Minus

open SemidirectProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {S : Type*} [Group S] [Finite S] {H : Type*} [Group H] {φ : H →* MulAut S}

theorem inl_mul_comm_of_center (hS : IsExtraspecialPGroup 2 S) {z : S}
    (hz : Subgroup.center S = Subgroup.zpowers z) (x : S ⋊[φ] H) : inl z * x = x * inl z := by
  have h1 : (inl z : S ⋊[φ] H) * inl x.left = inl x.left * inl z := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact (Subgroup.mem_center_iff.1 (hz ▸ Subgroup.mem_zpowers z) x.left).symm
  have h2 : (inl z : S ⋊[φ] H) * inr x.right = inr x.right * inl z := by
    have := inl_aut (φ := φ) x.right z
    rw [center_fixed φ hS hz x.right] at this
    conv_lhs => rw [this]
    rw [mul_assoc, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  calc inl z * x = inl z * (inl x.left * inr x.right) := by rw [inl_left_mul_inr_right]
    _ = (inl z * inl x.left) * inr x.right := by rw [mul_assoc]
    _ = (inl x.left * inl z) * inr x.right := by rw [h1]
    _ = inl x.left * (inl z * inr x.right) := by rw [mul_assoc]
    _ = inl x.left * (inr x.right * inl z) := by rw [h2]
    _ = (inl x.left * inr x.right) * inl z := by rw [mul_assoc]
    _ = x * inl z := by rw [inl_left_mul_inr_right]

theorem minus_of_irreducible [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hS : IsExtraspecialPGroup 2 S) (hS32 : Nat.card S = 32) {z : S}
    (hz : Subgroup.center S = Subgroup.zpowers z) (hzz : z * z = 1)
    (ρ : Representation K (S ⋊[φ] H) V) (hirr : IsMinInv ρ ⊤) (hz' : ρ (inl z) ≠ 1) :
    ρ (inl z) = -1 ∧ 4 ≤ Module.finrank K V := by
  have hT2 : ∀ v, ρ (inl z) (ρ (inl z) v) = v := by
    intro v
    have h : (inl z : S ⋊[φ] H) * inl z = 1 := by rw [← map_mul, hzz, map_one]
    calc ρ (inl z) (ρ (inl z) v) = ρ (inl z * inl z) v := by rw [map_mul]; rfl
      _ = v := by rw [h, map_one]; rfl
  have hTc : ∀ g v, ρ (inl z) (ρ g v) = ρ g (ρ (inl z) v) := by
    intro g v
    calc ρ (inl z) (ρ g v) = ρ (inl z * g) v := by rw [map_mul]; rfl
      _ = ρ (g * inl z) v := by rw [inl_mul_comm_of_center hS hz g]
      _ = ρ g (ρ (inl z) v) := by rw [map_mul]; rfl
  rcases eq_or_neg_of_isMinInv hirr (T := ρ (inl z)) hT2 hTc (fun y _ => Submodule.mem_top) with
    h | h
  · exact absurd (LinearMap.ext fun v => h v Submodule.mem_top) hz'
  · have hneg : ρ (inl z) = -1 := LinearMap.ext fun v => by rw [h v Submodule.mem_top]; simp
    obtain ⟨y, -, hy⟩ := (Submodule.ne_bot_iff _).1 hirr.2.1
    have : Nontrivial V := ⟨⟨y, 0, hy⟩⟩
    have hb := extraspecial_two_minus_module_bound (n := 2) hS (by rw [hS32]; norm_num) hz h2
      (ρ.comp inl) (by simpa using hneg)
    exact ⟨hneg, by simpa using hb.1⟩

end Minus

section Rank

variable {q : ℕ} [hq : Fact q.Prime] {P : Type*} [Group P] [Finite P]

theorem three_le_pRank_of_finrank [IsElementaryAbelian q (P ⧸ frattini P)] (hPq : IsPGroup q P)
    (hexp : ∀ x : P, x ^ q = 1) (hclass : commutator P ≤ Subgroup.center P)
    (hdim : 4 ≤ Module.finrank (ZMod q) (Additive (P ⧸ frattini P))) : 3 ≤ CFSG.pRank q P := by
  have : Fact (IsPGroup q P) := ⟨hPq⟩
  by_contra h
  push Not at h
  have hr := (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hPq hexp hclass).1
    (by omega)
  obtain ⟨k, hk⟩ := (hPq.to_quotient (commutator P)).exists_card_eq
  have hk' := (CFSG.RankThree.PartTwo.quotient_commutator_rank hq.out hexp hk).2
  have hΦ : commutator P ≤ frattini P := CFSG.commutator_le_frattini_of_isPGroup (p := q)
  have hdvd : Nat.card (P ⧸ frattini P) ∣ Nat.card (P ⧸ commutator P) :=
    Subgroup.index_dvd_of_le hΦ
  have hle : Nat.card (P ⧸ frattini P) ≤ q ^ k := by
    rw [← hk]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have hcard : Nat.card (P ⧸ frattini P) =
      q ^ Module.finrank (ZMod q) (Additive (P ⧸ frattini P)) := by
    have : Fintype (Additive (P ⧸ frattini P)) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod q) (V := Additive (P ⧸ frattini P))
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    exact hpow
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hq.out.one_lt).1 hle
  omega

end Rank


section Irreducible

variable {q : ℕ} [hq : Fact q.Prime] {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isMinInv_top_of_frattiniIrreducible (X R A : Subgroup G)
    [IsElementaryAbelian q (↥X ⧸ frattini ↥X)] (hirr : IsFrattiniIrreducibleFor (R ⊔ A) X)
    {H : Type*} [Group H] (ρ : H →* MulAut ↥X)
    (hR : ∀ g ∈ R, ∃ h : H, ∀ x : ↥X, ((ρ h x : ↥X) : G) = g * x * g⁻¹)
    (hA : ∀ g ∈ A, ∃ h : H, ∀ x : ↥X, ((ρ h x : ↥X) : G) = g * x * g⁻¹) :
    IsMinInv (frattiniRep q ρ) ⊤ := by
  obtain ⟨hnorm, hlt, hmin⟩ := hirr
  refine ⟨isInv_top, ?_, fun W' _ hW' => ?_⟩
  ·
    intro h
    obtain ⟨x, hxX, hxΦ⟩ := IsConcreteLE.exists_of_lt hlt
    have hmem : Additive.ofMul ((⟨x, hxX⟩ : ↥X) : ↥X ⧸ frattini ↥X) ∈ (⊤ : Submodule (ZMod q)
        (Additive (↥X ⧸ frattini ↥X))) := Submodule.mem_top
    rw [h, Submodule.mem_bot] at hmem
    apply hxΦ
    have h1 : (((⟨x, hxX⟩ : ↥X)) : ↥X ⧸ frattini ↥X) = 1 := hmem
    exact Subgroup.mem_map.2 ⟨⟨x, hxX⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  ·
    let Y₀ : Subgroup ↥X :=
      { carrier := {x | Additive.ofMul (x : ↥X ⧸ frattini ↥X) ∈ W'}
        one_mem' := by
          show Additive.ofMul ((1 : ↥X) : ↥X ⧸ frattini ↥X) ∈ W'
          rw [QuotientGroup.mk_one, ofMul_one]
          exact W'.zero_mem
        mul_mem' := by
          intro x y hx hy
          show Additive.ofMul ((x * y : ↥X) : ↥X ⧸ frattini ↥X) ∈ W'
          rw [QuotientGroup.mk_mul, ofMul_mul]
          exact W'.add_mem hx hy
        inv_mem' := by
          intro x hx
          show Additive.ofMul ((x⁻¹ : ↥X) : ↥X ⧸ frattini ↥X) ∈ W'
          rw [QuotientGroup.mk_inv, ofMul_inv]
          exact W'.neg_mem hx }
    set Y : Subgroup G := Y₀.map X.subtype with hY
    have hΦY : inSubgroup frattini X ≤ Y := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, ?_, rfl⟩
      show Additive.ofMul ((x : ↥X) : ↥X ⧸ frattini ↥X) ∈ W'
      rw [(QuotientGroup.eq_one_iff x).2 hx, ofMul_one]
      exact W'.zero_mem
    have hYX : Y ≤ X := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hinv : ∀ g : G, (∃ h : H, ∀ x : ↥X, ((ρ h x : ↥X) : G) = g * x * g⁻¹) →
        ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := by
      rintro g ⟨h, hh⟩ _ ⟨x, hx, rfl⟩
      refine ⟨ρ h x, ?_, (hh x)⟩
      have h1 := hW' h (Additive.ofMul (x : ↥X ⧸ frattini ↥X)) hx
      rw [frattiniRep_apply] at h1
      exact h1
    have hnormY : ∀ g : G, (g ∈ R ∨ g ∈ A) → g ∈ Subgroup.normalizer (Y : Set G) := by
      intro g hg
      have hgen : ∀ g : G, (g ∈ R ∨ g ∈ A) →
          ∃ h : H, ∀ x : ↥X, ((ρ h x : ↥X) : G) = g * x * g⁻¹ := by
        rintro g (hg | hg)
        · exact hR g hg
        · exact hA g hg
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact hinv g (hgen g hg) y
      · intro hy
        have hg' : g⁻¹ ∈ R ∨ g⁻¹ ∈ A := hg.imp R.inv_mem A.inv_mem
        have := hinv g⁻¹ (hgen g⁻¹ hg') _ hy
        simpa [mul_assoc] using this
    have hLY : R ⊔ A ≤ Subgroup.normalizer (Y : Set G) :=
      sup_le (fun g hg => hnormY g (Or.inl hg)) (fun g hg => hnormY g (Or.inr hg))
    have hsurj : ∀ v : Additive (↥X ⧸ frattini ↥X),
        ∃ x : ↥X, v = Additive.ofMul (x : ↥X ⧸ frattini ↥X) := by
      intro v
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      exact ⟨x, by rw [hx]; rfl⟩
    rcases hmin Y hΦY hYX hLY with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨x, hx⟩ := hsurj v
      have hxY : (x : G) ∈ Y := ⟨x, by rw [hx] at hv; exact hv, rfl⟩
      rw [h] at hxY
      obtain ⟨x', hx', hxx'⟩ := hxY
      have hx'x : x' = x := Subtype.ext hxx'
      rw [hx, Submodule.mem_bot]
      show ((x : ↥X ⧸ frattini ↥X)) = 1
      rw [← hx'x]
      exact (QuotientGroup.eq_one_iff _).2 hx'
    · right
      rw [eq_top_iff]
      intro v _
      obtain ⟨x, hx⟩ := hsurj v
      have hxY : (x : G) ∈ Y := by rw [h]; exact x.2
      obtain ⟨x', hx', hxx'⟩ := hxY
      have : x' = x := Subtype.ext hxx'
      rw [hx, ← this]
      exact hx'

end Irreducible


section Fpf

variable {G : Type*} [Group G]

theorem conj_mem_inSubgroup_frattini (R : Subgroup G) {b : G}
    (hb : b ∈ Subgroup.normalizer (R : Set G)) {s : G} (hs : s ∈ inSubgroup frattini R) :
    b * s * b⁻¹ ∈ inSubgroup frattini R := by
  obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.1 hs
  exact Subgroup.mem_map.2 ⟨Subgroup.normalizerMonoidHom R ⟨b, hb⟩ s',
    (mem_iff_of_characteristic _ _ s').1 hs', rfl⟩

theorem exists_fixedPointFree (A R : Subgroup G) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hirr : ∀ Y : Subgroup G, inSubgroup frattini R ≤ Y → Y ≤ R →
      A ≤ Subgroup.normalizer (Y : Set G) → Y = inSubgroup frattini R ∨ Y = R)
    (hnt : ∃ a ∈ A, ∃ r ∈ R, ⁅a, r⁆ ∉ inSubgroup frattini R) :
    ∃ a ∈ A, ∀ r ∈ R, ⁅a, r⁆ ∈ inSubgroup frattini R → r ∈ inSubgroup frattini R := by
  obtain ⟨a, haA, r₀, hr₀R, hr₀⟩ := hnt
  refine ⟨a, haA, ?_⟩
  have hΦR : inSubgroup frattini R ≤ R := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hnΦ : ∀ b ∈ Subgroup.normalizer (R : Set G), ∀ s ∈ inSubgroup frattini R,
      b * s * b⁻¹ ∈ inSubgroup frattini R := fun b hb s hs => conj_mem_inSubgroup_frattini R hb hs
  have hRn : ∀ r ∈ R, r ∈ Subgroup.normalizer (R : Set G) := fun r hr => Subgroup.le_normalizer hr
  let Y : Subgroup G :=
    { carrier := {r | r ∈ R ∧ ⁅a, r⁆ ∈ inSubgroup frattini R}
      one_mem' := ⟨R.one_mem, by rw [commutatorElement_one_right]; exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro r s ⟨hrR, hr⟩ ⟨hsR, hs⟩
        refine ⟨R.mul_mem hrR hsR, ?_⟩
        have h : ⁅a, r * s⁆ = ⁅a, r⁆ * (r * ⁅a, s⁆ * r⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [h]
        exact Subgroup.mul_mem _ hr (hnΦ r (hRn r hrR) _ hs)
      inv_mem' := by
        rintro r ⟨hrR, hr⟩
        refine ⟨R.inv_mem hrR, ?_⟩
        have h : ⁅a, r⁻¹⁆ = r⁻¹ * ⁅a, r⁆⁻¹ * r := by
          simp only [commutatorElement_def]
          group
        rw [h]
        have := hnΦ r⁻¹ (hRn r⁻¹ (R.inv_mem hrR)) _ (Subgroup.inv_mem _ hr)
        simpa [mul_assoc] using this }
  have hΦY : inSubgroup frattini R ≤ Y := by
    intro s hs
    refine ⟨hΦR hs, ?_⟩
    have h := hnΦ a (hAR haA) s hs
    have h' : ⁅a, s⁆ = (a * s * a⁻¹) * s⁻¹ := by simp only [commutatorElement_def]
    rw [h']
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hs)
  have hYR : Y ≤ R := fun r hr => hr.1
  have hAinv : ∀ b ∈ A, ∀ r ∈ Y, b * r * b⁻¹ ∈ Y := by
    rintro b hb r ⟨hrR, hr⟩
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (hAR hb) r).1 hrR
    · have hab : a * b = b * a := hAc a haA b hb
      have hba : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hab]
      have h : ⁅a, b * r * b⁻¹⁆ = b * ⁅a, r⁆ * b⁻¹ := by
        simp only [commutatorElement_def]
        calc a * (b * r * b⁻¹) * a⁻¹ * (b * r * b⁻¹)⁻¹
            = (a * b) * r * (b⁻¹ * a⁻¹) * b * r⁻¹ * b⁻¹ := by group
          _ = (b * a) * r * (a⁻¹ * b⁻¹) * b * r⁻¹ * b⁻¹ := by rw [hab, hba]
          _ = b * (a * r * a⁻¹ * r⁻¹) * b⁻¹ := by group
      rw [h]
      exact hnΦ b (hAR hb) _ hr
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hAinv g hg y
    · intro hy
      have := hAinv g⁻¹ (A.inv_mem hg) _ hy
      simpa [mul_assoc] using this
  rcases hirr Y hΦY hYR hAY with h | h
  · intro r hr hcomm
    have hrY : r ∈ Y := ⟨hr, hcomm⟩
    rw [h] at hrY
    exact hrY
  · exfalso
    have hr₀Y : r₀ ∈ Y := by rw [h]; exact hr₀R
    exact hr₀ hr₀Y.2

end Fpf


section Kernel

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker_conjHom (R X : Subgroup G) (h : R ≤ Subgroup.normalizer (X : Set G)) :
    (conjHom R X h).ker = (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R := by
  ext r
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hr
    refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    have h1 := congrArg (fun f : MulAut ↥X => ((f ⟨x, hx⟩ : ↥X) : G)) hr
    simp only [coe_conjHom, MulAut.one_apply] at h1
    calc x * (r : G) = ((r : G) * x * (r : G)⁻¹) * r := by rw [h1]
      _ = r * x := by group
  · rintro ⟨-, hr⟩
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [coe_conjHom, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.1 hr x x.2
    calc (r : G) * x * (r : G)⁻¹ = (x * r) * (r : G)⁻¹ := by rw [this]
      _ = x := by group

end Kernel


section Kernel2

variable {G : Type} [Group G] [Finite G]

theorem kernel_trivial_of_QD32 {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) {A D R X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hDq : IsPGroup q D)
    (hDexp : ∀ x ∈ D, x ^ q = 1) (hDclass : ⁅⁅D, D⁆, D⁆ = ⊥) (hXD : X ≤ D)
    (hXirr : IsFrattiniIrreducibleFor (R ⊔ A) X)
    (hrank2 : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2)
    (φQ : ↥R →* QD32) (hφsurj : Function.Surjective φQ)
    (hφker : φQ.ker = (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R) :
    R ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
  have h2 : (2 : ZMod q) ≠ 0 := by
    have := natCast_ne_zero_zmod hq.out Nat.prime_two hq2
    exact_mod_cast this
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := le_sup_left.trans hXirr.1
  have hAN : A ≤ Subgroup.normalizer (X : Set G) := le_sup_right.trans hXirr.1
  have hXq : IsPGroup q ↥X := hDq.to_le hXD
  have hXexp : ∀ x : ↥X, x ^ q = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hDexp x (hXD x.2))
  have hXclass : commutator ↥X ≤ Subgroup.center ↥X := by
    intro x hx
    have hx' : (x : G) ∈ ⁅X, X⁆ := by
      rw [← map_commutator_subtype]
      exact Subgroup.mem_map_of_mem _ hx
    have hx'' : (x : G) ∈ ⁅D, D⁆ := Subgroup.commutator_mono hXD hXD hx'
    have hDc : (x : G) ∈ Subgroup.centralizer (D : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hDclass hx''
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hDc g (hXD g.2))
  set ρR : ↥R →* MulAut ↥X := conjHom R X hRN with hρR
  set ρA : ↥A →* MulAut ↥X := conjHom A X hAN with hρA
  set Γ : Subgroup (MulAut ↥X) := ρR.range with hΓ
  have hkereq : ρR.ker = φQ.ker := by rw [hρR, ker_conjHom, hφker]
  let eΓ : Γ ≃* QD32 :=
    (QuotientGroup.quotientKerEquivRange ρR).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
        (QuotientGroup.quotientKerEquivOfSurjective φQ hφsurj))
  obtain ⟨hQD32, hQDext, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
  have hΓext : IsExtraspecialPGroup 2 Γ := isExtraspecialPGroup_of_equiv eΓ.symm hQDext
  have hΓ32 : Nat.card Γ = 32 := (Nat.card_congr eΓ.toEquiv).trans hQD32
  have hnorm : ∀ a : ↥A, ρA a ∈ Subgroup.normalizer (Γ : Set (MulAut ↥X)) := by
    have key : ∀ (a : ↥A) (γ : MulAut ↥X), γ ∈ Γ → ρA a * γ * (ρA a)⁻¹ ∈ Γ := by
      rintro a _ ⟨r, rfl⟩
      refine ⟨conjHom A R hAR a r, ?_⟩
      have h := conjHom_compat A R X hAR hRN hAN a
      have h' := congrArg (fun f : ↥R →* MulAut ↥X => f r) h
      simpa [MulAut.conj_apply] using h'
    intro a
    rw [Subgroup.mem_normalizer_iff]
    intro γ
    refine ⟨key a γ, fun hγ => ?_⟩
    have := key a⁻¹ _ hγ
    rw [map_inv] at this
    simpa [mul_assoc] using this
  let φΓ : ↥A →* MulAut ↥Γ :=
    (Subgroup.normalizerMonoidHom Γ).comp (ρA.codRestrict (Subgroup.normalizer (Γ : Set _)) hnorm)
  have hcompat : ∀ a : ↥A, Γ.subtype.comp (φΓ a).toMonoidHom =
      (MulAut.conj (ρA a)).toMonoidHom.comp Γ.subtype := by
    intro a
    refine MonoidHom.ext fun γ => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rfl
  let ρΓ : Γ ⋊[φΓ] ↥A →* MulAut ↥X := SemidirectProduct.lift Γ.subtype ρA hcompat
  obtain ⟨-, -, hVexp, hVelem, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hXq
  have hirrV : IsMinInv (frattiniRep q ρΓ) ⊤ := by
    refine isMinInv_top_of_frattiniIrreducible X R A hXirr ρΓ ?_ ?_
    · intro g hg
      refine ⟨inl ⟨ρR ⟨g, hg⟩, ⟨_, rfl⟩⟩, fun x => ?_⟩
      have h : ρΓ (inl (⟨ρR ⟨g, hg⟩, ⟨_, rfl⟩⟩ : Γ)) = ρR ⟨g, hg⟩ :=
        SemidirectProduct.lift_inl _ _ _ _
      rw [h, hρR, coe_conjHom]
    · intro g hg
      refine ⟨inr ⟨g, hg⟩, fun x => ?_⟩
      have h : ρΓ (inr (⟨g, hg⟩ : ↥A)) = ρA ⟨g, hg⟩ := SemidirectProduct.lift_inr _ _ _ _
      rw [h, hρA, coe_conjHom]
  obtain ⟨z, hz, hz1, hzz⟩ := exists_center_generator hΓext
  have hz' : frattiniRep q ρΓ (inl z) ≠ 1 := by
    intro h
    have h1 := frattiniRep_eq_one hXq hq2 ρΓ (inl z)
      (isPGroup_zpowers_map hΓext.1 (ρΓ.comp inl) z) h
    apply hz1
    have h2' : ρΓ (inl z) = (z : MulAut ↥X) := SemidirectProduct.lift_inl _ _ _ z
    exact Subtype.ext (h2'.symm.trans h1)
  have : FiniteDimensional (ZMod q) (Additive (↥X ⧸ frattini ↥X)) := Module.Finite.of_finite
  obtain ⟨-, hdim⟩ := minus_of_irreducible h2 hΓext hΓ32 hz hzz (frattiniRep q ρΓ) hirrV hz'
  have h3 := three_le_pRank_of_finrank hXq hXexp hXclass hdim
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  by_contra hr1
  have hXle : X ≤ D ⊓ Subgroup.centralizer ({r} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hXD hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hr).2 x hx)
  have h4 : CFSG.pRank q ↥X ≤ CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) :=
    pRank_le_of_injective (Subgroup.inclusion hXle) (Subgroup.inclusion_injective hXle)
  have h5 := hrank2 r (Subgroup.mem_inf.1 hr).1 hr1
  omega

end Kernel2


section FrattiniLe

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_frattini_le_two {R K : Subgroup G} (hR : IsPGroup 2 R) (hcomm : ⁅R, R⁆ ≤ K)
    (hpow : ∀ r ∈ R, r ^ 2 ∈ K) : inSubgroup frattini R ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 R) := ⟨hR⟩
  have h : frattini R ≤ K.comap R.subtype := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · have hx' : R.subtype x ∈ ⁅R, R⁆ := by
        have : R.subtype x ∈ (commutator R).map R.subtype := Subgroup.mem_map_of_mem _ hx
        rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at this
      exact hcomm hx'
    · exact hpow y y.2
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h hy

end FrattiniLe

end CFSG.RankThree.PartOne.FixedRank36

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.FixedRank36 SemidirectProduct CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem minimalTwoActionWithoutRankThreeFixedGroup_of
    (hMTASFQ : MinimalTwoActionSmallFaithfulQuotient)
    (hEFQKE : ElementaryFaithfulQuotientKernelElimination) :
    MinimalTwoActionWithoutRankThreeFixedGroup := by
  intro G _ _ p q A D R hS hrank2
  have : Fact q.Prime := ⟨hS.prime_q⟩
  have hrank3 : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3 := fun r hr hr1 =>
    (hrank2 r hr hr1).trans (by norm_num)
  obtain ⟨X, hXD, hXR, hXirr, hXΦ, hKΦ, hnt, hAirr, hAΦ, hshape, hB, hker1, hker2, hrankX⟩ :=
    hMTASFQ G p q A D R hS hrank3
  have helem : ∀ d : ℕ, ((p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) →
      ⁅R, R⁆ ≤ R ⊓ Subgroup.centralizer (X : Set G) →
      (∀ r ∈ R, r ^ 2 ∈ R ⊓ Subgroup.centralizer (X : Set G)) →
      (R ⊓ Subgroup.centralizer (X : Set G)).relIndex R = 2 ^ d → False := by
    intro d hd hcomm hsq hrel
    have hKeq : R ⊓ Subgroup.centralizer (X : Set G) = inSubgroup frattini R :=
      le_antisymm hKΦ (inSubgroup_frattini_le_two hS.R_two hcomm hsq)
    obtain ⟨-, -, -, -, -, ⟨r, hrR, hr1, -, hr3⟩, -, -, -⟩ := hEFQKE G p q d A D R X hS.prime_p
      hS.prime_q hS.three_lt_p hS.q_ne_two hS.p_ne_q hd hS.A_elem hS.A_card hS.R_two hS.R_inv
      hS.D_inv hS.D_pgroup hS.D_exp hS.D_class hrank3 hXD hXirr hcomm hsq hrel
      (fun Y hKY hYR hAY => by
        rw [hKeq] at hKY ⊢
        exact hAirr Y hKY hYR hAY) hB
    have := hrank2 r hrR hr1
    omega
  rcases hshape with ⟨hp7, hcomm, hsq, hrel⟩ | ⟨hp5, hcomm, hsq, hrel⟩ |
    ⟨hp5, φQ, hφsurj, hφker⟩
  · exact (helem 3 (Or.inl ⟨hp7, rfl⟩) hcomm hsq (by rw [hrel]; norm_num)).elim
  · exact (helem 4 (Or.inr ⟨hp5, rfl⟩) hcomm hsq (by rw [hrel]; norm_num)).elim
  · subst hp5
    have hK0 := kernel_trivial_of_QD32 hS.q_ne_two hS.R_inv hS.D_pgroup hS.D_exp hS.D_class hXD
      hXirr hrank2 φQ hφsurj hφker
    have hinj : Function.Injective φQ := by
      rw [← MonoidHom.ker_eq_bot_iff, hφker, hK0, Subgroup.bot_subgroupOf]
    let eR : ↥R ≃* QD32 := MulEquiv.ofBijective φQ ⟨hinj, hφsurj⟩
    obtain ⟨hQD32, hQDext, -⟩ :=
      CFSG.RankThree.GroupTheory.SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
    have hq5 : q ≠ 5 := fun h => hS.p_ne_q h.symm
    have hRext : IsExtraspecialPGroup 2 ↥R := isExtraspecialPGroup_of_equiv eR.symm hQDext
    have hR32 : Nat.card ↥R = 32 := (Nat.card_congr eR.toEquiv).trans hQD32
    have hΦZ : inSubgroup frattini R = inSubgroup Subgroup.center R := by
      unfold inSubgroup
      rw [hRext.2.2.1]
    obtain ⟨a, haA, hafp⟩ := exists_fixedPointFree A R hS.R_inv
      (fun a ha b hb => congrArg Subtype.val
        (hS.A_elem.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hAirr hnt
    have hfpf : ∃ a ∈ A, ∀ r ∈ R, r ∉ inSubgroup Subgroup.center R →
        ⁅a, r⁆ ∉ inSubgroup Subgroup.center R :=
      ⟨a, haA, fun r hr hrc hcomm => hrc (hΦZ ▸ hafp r hr (hΦZ ▸ hcomm))⟩
    have hfaith : R ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
      rw [eq_bot_iff]
      intro r hr
      have hrK : r ∈ R ⊓ Subgroup.centralizer (X : Set G) :=
        Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hr).1, Subgroup.centralizer_le hXD
          (Subgroup.mem_inf.1 hr).2⟩
      rw [hK0] at hrK
      exact hrK
    have hmain := extraspecialThirtyTwoFixedRankTwoAction G q A R D hS.prime_q hS.q_ne_two hq5
      hS.A_elem (by simpa using hS.A_card) hS.R_inv hRext hR32 hfpf hS.D_inv hS.D_pgroup hS.D_exp
      hS.D_class hfaith hrank2
    exact ⟨rfl, ⟨eR⟩, hmain.1, hmain.2.2⟩

end CFSG.RankThree.PartOne
