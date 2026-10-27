module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndX
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG Subgroup
open scoped commutatorElement IsMulCommutative

theorem pow_val_add_of_mul_self {M : Type*} [Monoid M] {g : M} (hg : g * g = 1)
    (a b : ZMod 2) : g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ (by rw [sq]; exact hg), pow_add]

theorem three_le_pRank_of_involutions {G : Type*} [Group G] [Finite G] {x y c : G}
    (hx : x * x = 1) (hy : y * y = 1) (hc : c * c = 1) (hxy : x * y = y * x)
    (hxc : x * c = c * x) (hyc : y * c = c * y)
    (hind : ∀ a b d : ZMod 2, x ^ a.val * y ^ b.val * c ^ d.val = 1 → a = 0 ∧ b = 0 ∧ d = 0) :
    3 ≤ CFSG.pRank 2 G := by
  set T := closure ({x, y, c} : Set G) with hT
  have hTc : IsMulCommutative T := by
    refine isMulCommutative_closure ?_
    rintro u (rfl | rfl | rfl) v (rfl | rfl | rfl) - <;>
      first
        | exact Commute.refl _
        | exact hxy
        | exact hxy.symm
        | exact hxc
        | exact hxc.symm
        | exact hyc
        | exact hyc.symm
  set x' : T := ⟨x, subset_closure (by simp)⟩
  set y' : T := ⟨y, subset_closure (by simp)⟩
  set c' : T := ⟨c, subset_closure (by simp)⟩
  have hx' : x' * x' = 1 := Subtype.ext hx
  have hy' : y' * y' = 1 := Subtype.ext hy
  have hc' : c' * c' = 1 := Subtype.ext hc
  let f : Multiplicative (Fin 3 → ZMod 2) →* T :=
    { toFun := fun v => x' ^ (Multiplicative.toAdd v 0).val * y' ^ (Multiplicative.toAdd v 1).val *
        c' ^ (Multiplicative.toAdd v 2).val
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, pow_val_add_of_mul_self hx',
          pow_val_add_of_mul_self hy', pow_val_add_of_mul_self hc']
        rw [mul_mul_mul_comm (x' ^ _ * y' ^ _), mul_mul_mul_comm (x' ^ _) (y' ^ _)] }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h := hind (Multiplicative.toAdd v 0) (Multiplicative.toAdd v 1) (Multiplicative.toAdd v 2)
      (congrArg Subtype.val hv)
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  set E := (T.subtype.comp f).range with hE
  have hinj : Function.Injective (T.subtype.comp f) := Subtype.val_injective.comp hf
  have hcard : Nat.card E = 2 ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hEl : CFSG.Open.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, v, rfl⟩ := a
      obtain ⟨_, w, rfl⟩ := b
      apply Subtype.ext
      change (T.subtype.comp f) v * (T.subtype.comp f) w =
        (T.subtype.comp f) w * (T.subtype.comp f) v
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨v, rfl⟩
      rw [← map_pow]
      have : v ^ 2 = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
        generalize Multiplicative.toAdd v i = t
        fin_cases t <;> rfl
      rw [this, map_one]
  have h3 := CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) le_top hEl hcard
  rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h3

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem commute_of_odd_of_centralizes_involutions {A : Subgroup X} (hA2 : IsPGroup 2 A)
    (hAc : IsMulCommutative A) {g : X} (hg : Odd (orderOf g))
    (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hinv : ∀ a ∈ A, a * a = 1 → g * a = a * g) :
    ∀ a ∈ A, g * a = a * g := by
  have key : ∀ n, ∀ a ∈ A, orderOf a = n → g * a = a * g := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro a ha hn
    by_cases haa : a * a = 1
    · exact hinv a ha haa
    have ha1 : a ≠ 1 := fun h => haa (by rw [h, one_mul])
    obtain ⟨j, hj⟩ := exists_orderOf_eq_two_pow hA2 ⟨a, ha⟩
    rw [Subgroup.orderOf_mk] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact ha1 hj
    have hlt : orderOf (a * a) < n := by
      rw [← sq, orderOf_pow' a two_ne_zero, hj, Nat.gcd_eq_right (dvd_pow_self 2 hj0), ← hn,
        hj]
      exact Nat.div_lt_self (by positivity) (by norm_num)
    have hga2 := ih _ hlt (a * a) (mul_mem ha ha) rfl
    set c := a⁻¹ * (g * a * g⁻¹) with hcdef
    have hcA : c ∈ A := mul_mem (inv_mem ha) (hgA a ha)
    have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
      congrArg Subtype.val (hAc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
    have hcc : c * c = 1 := by
      have h1 : g * (a * a) * g⁻¹ = a * a := by rw [hga2, mul_inv_cancel_right]
      have h2 : (g * a * g⁻¹) * (g * a * g⁻¹) = a * a := by
        rw [← h1]
        group
      have h3 := hcomm a⁻¹ (inv_mem ha) (g * a * g⁻¹) (hgA a ha)
      calc c * c = a⁻¹ * a⁻¹ * ((g * a * g⁻¹) * (g * a * g⁻¹)) := by
            rw [hcdef, mul_assoc, ← mul_assoc (g * a * g⁻¹) a⁻¹, ← h3]
            group
        _ = 1 := by rw [h2]; group
    have hgc : g * c = c * g := hinv c hcA hcc
    have hgac : g * a * g⁻¹ = a * c := by rw [hcdef]; group
    have hpow : ∀ m : ℕ, g ^ m * a * (g ^ m)⁻¹ = a * c ^ m := by
      intro m
      induction m with
      | zero => simp
      | succ m ihm =>
        have hcm : g * c ^ m * g⁻¹ = c ^ m := by
          rw [(Commute.pow_right hgc m).eq, mul_inv_cancel_right]
        calc g ^ (m + 1) * a * (g ^ (m + 1))⁻¹ = g * (g ^ m * a * (g ^ m)⁻¹) * g⁻¹ := by
              group
          _ = (g * a * g⁻¹) * (g * c ^ m * g⁻¹) := by rw [ihm]; group
          _ = a * c ^ (m + 1) := by rw [hgac, hcm, pow_succ', mul_assoc]
    obtain ⟨k, hk⟩ := hg
    have h1 := hpow (orderOf g)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, hk, pow_succ, pow_mul, sq, hcc,
      one_pow, one_mul] at h1
    have hc1 : c = 1 := by
      calc c = a⁻¹ * (a * c) := by group
        _ = 1 := by rw [← h1, inv_mul_cancel]
    rw [hcdef, inv_mul_eq_one] at hc1
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [← hc1]
  exact fun a ha => key _ a ha rfl

theorem le_center_of_pRank_le_two [Group.IsPerfect X] (hRank : CFSG.pRank 2 X ≤ 2)
    (A : Subgroup X) (hA : A.Normal) (hA2 : IsPGroup 2 A) (hAc : IsMulCommutative A) :
    A ≤ center X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  let Ω : Subgroup X :=
    { carrier := {a | a ∈ A ∧ a * a = 1}
      one_mem' := ⟨one_mem A, mul_one 1⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        calc a * b * (a * b) = a * a * (b * b) := by
              rw [mul_assoc, ← mul_assoc b a b, ← hcomm a ha.1 b hb.1]; group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hΩn : Ω.Normal := ⟨fun a ha g => ⟨hA.conj_mem a ha.1 g, by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha.2]; group⟩⟩
  have hΩcard : Nat.card Ω ≤ 4 := by
    have hΩ2 : IsPGroup 2 Ω := hA2.to_le (fun a ha => ha.1)
    obtain ⟨k, hk⟩ := hΩ2.exists_card_eq
    have hel : CFSG.Open.IsElemAbelian 2 Ω := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2.1 _ b.2.1)⟩⟩, fun a ha => ?_⟩
      rw [sq]
      exact ha.2
    have hle := CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) le_top hel hk
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at hle
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hle.trans hRank)
      _ = 4 := by norm_num
  have hsol : Group.IsSolvable (Equiv.Perm Ω) := Equiv.Perm.isSolvable hΩcard
  have hΩc : ∀ g : X, ∀ a ∈ Ω, g * a = a * g := by
    intro g a ha
    have h1 := map_eq_one_of_isPerfect ((MulAut.toPerm _).comp
      (MulAut.conjNormal : X →* MulAut Ω)) g
    have h2 : g * a * g⁻¹ = a := congrArg (fun π : Equiv.Perm Ω => ((π ⟨a, ha⟩ : Ω) : X)) h1
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h2]
  have hodd : ∀ g : X, Odd (orderOf g) → ∀ a ∈ A, g * a = a * g := fun g hg =>
    commute_of_odd_of_centralizes_involutions hA2 hAc hg (fun a ha => hA.conj_mem a ha g)
      (fun a ha haa => hΩc g a ⟨ha, haa⟩)
  set φ : X →* MulAut A := MulAut.conjNormal with hφ
  have hφ2 : IsPGroup 2 φ.range := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, Subtype.ext ?_⟩
    have hy : Odd (orderOf (x ^ 2 ^ k)) := by
      rw [orderOf_pow' x (pow_ne_zero _ two_ne_zero), hkm,
        Nat.gcd_eq_right (Dvd.intro m rfl), Nat.mul_div_cancel_left m (by positivity)]
      exact hm
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow]
    ext a
    simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply]
    rw [hodd _ hy a a.2, mul_inv_cancel_right]
  have hφ1 : φ.range = ⊥ := by
    by_contra hne
    have : Nontrivial φ.range := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
    exact Group.IsPerfect.not_isNilpotent φ.range hφ2.isNilpotent
  intro a ha
  rw [mem_center_iff]
  intro g
  have h1 : φ g = 1 := by
    have : φ g ∈ φ.range := ⟨g, rfl⟩
    rwa [hφ1, mem_bot] at this
  have h2 := congrArg (fun σ : MulAut A => ((σ ⟨a, ha⟩ : A) : X)) h1
  simp only [hφ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [h2]

theorem exists_sq_eq_of_center_ne {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcyc : IsCyclic (center P)) {z : P} (hzc : z ∈ center P) (hz1 : z ≠ 1)
    (hinv : ∀ t ∈ center P, t * t = 1 → t = 1 ∨ t = z) (hne : center P ≠ zpowers z) :
    ∃ i ∈ center P, i * i = z := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hic : (g : P) ∈ center P := g.2
  have hZ : center P = zpowers (g : P) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      exact mem_zpowers_iff.mpr ⟨n, by rw [← Subgroup.coe_zpow, hn]⟩
    · exact zpowers_le.mpr hic
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hP (g : P)
  have hk2 : 2 ≤ k := by
    by_contra hlt
    apply hne
    have hgg : (g : P) * g = 1 := by
      rw [← sq]
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hk]
      simpa using Nat.pow_dvd_pow 2 (show k ≤ 1 by omega)
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (hZ ▸ hzc)
    have h2 : (g : P) ^ (2 : ℤ) = 1 := by rw [zpow_two, hgg]
    have hn' : (g : P) ^ n = (g : P) ^ (n % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
      rw [zpow_add, zpow_mul, h2, one_zpow, mul_one]
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · rw [hn', h0, zpow_zero] at hn
      exact absurd hn.symm hz1
    · rw [hn', h1, zpow_one] at hn
      rw [hZ, hn]
  refine ⟨(g : P) ^ 2 ^ (k - 2), pow_mem hic _, ?_⟩
  have hsq : (g : P) ^ 2 ^ (k - 2) * (g : P) ^ 2 ^ (k - 2) = (g : P) ^ 2 ^ (k - 1) := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    congr 2
    omega
  rw [hsq]
  have hinv' : (g : P) ^ 2 ^ (k - 1) * (g : P) ^ 2 ^ (k - 1) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', show k - 1 + 1 = k by omega, ← hk,
      pow_orderOf_eq_one]
  rcases hinv _ (pow_mem hic _) hinv' with h | h
  · exfalso
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero) ?_ h
    rw [hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exact h

section Core

variable [Group.IsPerfect X] {K : Subgroup X} [K.Normal] [IsSimpleGroup (X ⧸ K)]

theorem commB_pow_left {P : Type*} [Group P] {z : P} (h : CommData P z)
    (ε : zpowers z ≃* Multiplicative (ZMod 2)) (q t : P ⧸ center P) (n : ℕ) :
    commB h ε (q ^ n) t = n • commB h ε q t := by
  induction n with
  | zero =>
    have := commB_mul_left h ε 1 1 t
    rw [mul_one] at this
    rw [pow_zero, zero_smul]
    linear_combination -this
  | succ n ih => rw [pow_succ, commB_mul_left, ih, succ_nsmul]

include K in
theorem eq_two_of_pRank_le_two (hRank : CFSG.pRank 2 X ≤ 2) {z₀ : X} (hz : z₀ ∈ pCore 2 X)
    (h : CommData (pCore 2 X) ⟨z₀, hz⟩) (hcyc : IsCyclic (center (pCore 2 X)))
    (hinvS : ∀ t ∈ center (pCore 2 X), t * t = 1 → t = 1 ∨ t = ⟨z₀, hz⟩)
    {E : Subgroup (pCore 2 X)} (hEZ : E ⊔ center (pCore 2 X) = ⊤)
    (hEZ' : E ⊓ center (pCore 2 X) = zpowers ⟨z₀, hz⟩) {w : ℕ}
    (hcard : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) = 2 ^ (2 * w))
    (hC2 : (quotConj (pCore 2 X)).ker ≤ pCore 2 X) :
    w = 2 ∧ center (pCore 2 X) = zpowers ⟨z₀, hz⟩ := by
  set z : pCore 2 X := ⟨z₀, hz⟩ with hzdef
  have : IsElementaryAbelian 2 (pCore 2 X ⧸ center (pCore 2 X)) := isElementaryAbelian_quot h
  obtain ⟨ε⟩ := h.nonempty_mulEquiv
  set b := commB h ε with hbdef
  have hlift := exists_lift_of_sup hEZ
  have hsq : ∀ e ∈ E, e * e = 1 ∨ e * e = z := fun e he => sq_eq_of_mem h hEZ' he
  have hrel0 : ∀ x y : pCore 2 X, b x y = 0 → x * y = y * x := fun x y hxy =>
    mul_comm_of_commB_eq_zero h ε hxy
  have hsymm := symm_of_alt b (commB_mul_left h ε) (commB_mul_right h ε) (commB_self h ε)
  have hbl : ∀ u v t, b (u * v) t = b u t + b v t := commB_mul_left h ε
  have hbr : ∀ u v t, b u (v * t) = b u v + b u t := commB_mul_right h ε
  have hb1 : ∀ t, b 1 t = 0 := by
    intro t
    have := hbl 1 1 t
    rw [mul_one] at this
    linear_combination -this
  have hE8 : ∀ u₁ u₂ : pCore 2 X, u₁ * u₁ = 1 → u₂ * u₂ = 1 → u₁ * u₂ = u₂ * u₁ →
      ∀ t₁ t₂ : pCore 2 X ⧸ center (pCore 2 X), b u₁ t₁ = 1 → b u₂ t₁ = 0 → b u₁ t₂ = 0 →
        b u₂ t₂ = 1 → False := by
    intro u₁ u₂ h1 h2 h12 t₁ t₂ h11 h21 h12' h22
    have hzu : ∀ u : pCore 2 X, z₀ * u = u * z₀ := fun u =>
      (congrArg Subtype.val (mem_center_iff.mp h.mem_center u)).symm
    have h3 := three_le_pRank_of_involutions (x := z₀) (y := (u₁ : X)) (c := (u₂ : X))
      (congrArg Subtype.val h.sq_eq_one) (congrArg Subtype.val h1) (congrArg Subtype.val h2)
      (hzu u₁) (hzu u₂) (congrArg Subtype.val h12) (by
        intro α β δ hαβδ
        have hS : z ^ α.val * u₁ ^ β.val * u₂ ^ δ.val = 1 := Subtype.ext (by simpa using hαβδ)
        have hQ : ((u₁ : pCore 2 X ⧸ center (pCore 2 X)) ^ β.val *
            (u₂ : pCore 2 X ⧸ center (pCore 2 X)) ^ δ.val) = 1 := by
          have := congrArg (fun s : pCore 2 X => (s : pCore 2 X ⧸ center (pCore 2 X))) hS
          simp only [QuotientGroup.mk_mul, QuotientGroup.mk_pow, QuotientGroup.mk_one] at this
          rwa [(QuotientGroup.eq_one_iff z).mpr h.mem_center, one_pow, one_mul] at this
        have hval : ∀ c : ZMod 2, (c.val : ZMod 2) = c := ZMod.natCast_zmod_val
        have e₁ := congrArg (fun q => b q t₁) hQ
        have e₂ := congrArg (fun q => b q t₂) hQ
        simp only [hbdef, commB_mul_left, commB_pow_left] at e₁ e₂
        rw [← hbdef, h11, h21, hb1, nsmul_zero, add_zero, nsmul_eq_mul, mul_one, hval] at e₁
        rw [← hbdef, h12', h22, hb1, nsmul_zero, zero_add, nsmul_eq_mul, mul_one, hval] at e₂
        refine ⟨?_, e₁, e₂⟩
        simp only [e₁, e₂, ZMod.val_zero, pow_zero, mul_one] at hS
        by_contra hα
        have hα1 : α = 1 :=
          ((by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) α).resolve_left hα
        rw [hα1, show (1 : ZMod 2).val = 1 from rfl, pow_one] at hS
        exact h.ne_one hS)
    omega
  obtain ⟨e, f, hee, hff, hef⟩ := exists_symplectic_pairs hcard b (commB_mul_left h ε)
    (commB_mul_right h ε) (commB_self h ε) (eq_one_of_commB h ε)
  choose eL heLE heL using fun i => hlift (e i)
  choose fL hfLE hfL using fun i => hlift (f i)
  have hEE : ∀ i j, b (eL i) (eL j) = 0 := fun i j => by rw [heL, heL]; exact hee i j
  have hFF : ∀ i j, b (fL i) (fL j) = 0 := fun i j => by rw [hfL, hfL]; exact hff i j
  have hEF : ∀ i j, b (eL i) (fL j) = if i = j then 1 else 0 := fun i j => by
    rw [heL, hfL]; exact hef i j
  have hFE : ∀ i j, b (fL i) (eL j) = if i = j then 1 else 0 := fun i j => by
    rw [hsymm, hEF]; simp only [eq_comm]
  have hEFd : ∀ i, b (eL i) (fL i) = 1 := fun i => by rw [hEF]; simp
  have hEFo : ∀ i j, i ≠ j → b (eL i) (fL j) = 0 := fun i j hij => by rw [hEF]; simp [hij]
  have hFEd : ∀ i, b (fL i) (eL i) = 1 := fun i => by rw [hFE]; simp
  have hFEo : ∀ i j, i ≠ j → b (fL i) (eL j) = 0 := fun i j hij => by rw [hFE]; simp [hij]
  have hw2 : 2 ≤ w := by
    by_contra hlt
    have hcard4 : Nat.card (pCore 2 X ⧸ center (pCore 2 X)) ≤ 4 := by
      rw [hcard]
      interval_cases w <;> norm_num
    have : Group.IsSolvable (Equiv.Perm (pCore 2 X ⧸ center (pCore 2 X))) :=
      Equiv.Perm.isSolvable hcard4
    apply pCore_two_ne_top (K := K)
    refine eq_top_iff.mpr fun x _ => hC2 (MonoidHom.mem_ker.mpr ?_)
    have h1 := map_eq_one_of_isPerfect ((MulAut.toPerm _).comp (quotConj (pCore 2 X))) x
    ext q
    exact congrArg (fun π : Equiv.Perm _ => π q) h1
  set i₀ : Fin w := ⟨0, by omega⟩
  set i₁ : Fin w := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h' => by simpa [i₀, i₁] using congrArg Fin.val h'
  have hZ : center (pCore 2 X) = zpowers z := by
    by_contra hne
    obtain ⟨i, hic, hii⟩ := exists_sq_eq_of_center_ne pCore_isPGroup hcyc h.mem_center h.ne_one
      hinvS hne
    have hinv1 : ∀ x ∈ E, ∃ u : pCore 2 X, (u : pCore 2 X ⧸ center (pCore 2 X)) = x ∧
        u * u = 1 := by
      intro x hx
      rcases hsq x hx with h1 | h1
      · exact ⟨x, rfl, h1⟩
      · refine ⟨x * i, ?_, ?_⟩
        · rw [QuotientGroup.eq]
          simpa using hic
        · have hc := mem_center_iff.mp hic x
          calc x * i * (x * i) = x * (i * x) * i := by group
            _ = x * x * (i * i) := by rw [← hc]; group
            _ = 1 := by rw [h1, hii, h.sq_eq_one]
    obtain ⟨u₁, hu₁, hu₁1⟩ := hinv1 _ (heLE i₀)
    obtain ⟨u₂, hu₂, hu₂1⟩ := hinv1 _ (heLE i₁)
    refine hE8 u₁ u₂ hu₁1 hu₂1 (hrel0 _ _ (by rw [hu₁, hu₂]; exact hEE i₀ i₁)) (fL i₀) (fL i₁)
      (by rw [hu₁, hEFd]) (by rw [hu₂, hEFo _ _ h01.symm])
      (by rw [hu₁, hEFo _ _ h01]) (by rw [hu₂, hEFd])
  refine ⟨?_, hZ⟩
  by_contra hne
  set i₂ : Fin w := ⟨2, by omega⟩
  have h02 : i₀ ≠ i₂ := fun h' => by simpa [i₀, i₂] using congrArg Fin.val h'
  have h12 : i₁ ≠ i₂ := fun h' => by simpa [i₁, i₂] using congrArg Fin.val h'
  have hpair : ∀ j k : Fin w, j ≠ k →
      ((eL j * eL j = 1 ∨ fL j * fL j = 1) ↔ (eL k * eL k = 1 ∨ fL k * fL k = 1)) → False := by
    intro j k hjk hiff
    by_cases hj : eL j * eL j = 1 ∨ fL j * fL j = 1
    · have hk := hiff.mp hj
      have hsel : ∀ m : Fin w, (eL m * eL m = 1 ∨ fL m * fL m = 1) →
          ∃ u t : pCore 2 X, u * u = 1 ∧ (u = eL m ∨ u = fL m) ∧ (t = eL m ∨ t = fL m) ∧
            b u t = 1 := by
        intro m hm
        rcases hm with hm | hm
        · exact ⟨eL m, fL m, hm, Or.inl rfl, Or.inr rfl, hEFd m⟩
        · exact ⟨fL m, eL m, hm, Or.inr rfl, Or.inl rfl, hFEd m⟩
      obtain ⟨u₁, t₁, hu₁, hu₁m, ht₁m, hb₁⟩ := hsel j hj
      obtain ⟨u₂, t₂, hu₂, hu₂m, ht₂m, hb₂⟩ := hsel k hk
      have hcross : ∀ x y : pCore 2 X, (x = eL j ∨ x = fL j) → (y = eL k ∨ y = fL k) →
          b x y = 0 ∧ b y x = 0 := by
        rintro x y (rfl | rfl) (rfl | rfl)
        · exact ⟨hEE j k, hEE k j⟩
        · exact ⟨hEFo _ _ hjk, hFEo _ _ hjk.symm⟩
        · exact ⟨hFEo _ _ hjk, hEFo _ _ hjk.symm⟩
        · exact ⟨hFF j k, hFF k j⟩
      exact hE8 u₁ u₂ hu₁ hu₂ (hrel0 _ _ (hcross u₁ u₂ hu₁m hu₂m).1) t₁ t₂ hb₁
        (hcross t₁ u₂ ht₁m hu₂m).2 (hcross u₁ t₂ hu₁m ht₂m).1 hb₂
    · have hk : ¬ (eL k * eL k = 1 ∨ fL k * fL k = 1) := fun h' => hj (hiff.mpr h')
      push Not at hj hk
      have hsqz : ∀ m : Fin w, eL m * eL m ≠ 1 → fL m * fL m ≠ 1 →
          eL m * eL m = z ∧ fL m * fL m = z := fun m h1 h2 =>
        ⟨(hsq _ (heLE m)).resolve_left h1, (hsq _ (hfLE m)).resolve_left h2⟩
      obtain ⟨hej, hfj⟩ := hsqz j hj.1 hj.2
      obtain ⟨hek, hfk⟩ := hsqz k hk.1 hk.2
      have hcz : ∀ s : pCore 2 X, z * s = s * z := fun s =>
        (mem_center_iff.mp h.mem_center s).symm
      have hc1 : eL j * eL k = eL k * eL j := hrel0 _ _ (hEE j k)
      have hc2 : fL j * fL k = fL k * fL j := hrel0 _ _ (hFF j k)
      have huu : eL j * eL k * (eL j * eL k) = 1 := by
        calc eL j * eL k * (eL j * eL k) = eL j * (eL k * eL j) * eL k := by group
          _ = eL j * eL j * (eL k * eL k) := by rw [← hc1]; group
          _ = 1 := by rw [hej, hek, h.sq_eq_one]
      have hvv : fL j * fL k * (fL j * fL k) = 1 := by
        calc fL j * fL k * (fL j * fL k) = fL j * (fL k * fL j) * fL k := by group
          _ = fL j * fL j * (fL k * fL k) := by rw [← hc2]; group
          _ = 1 := by rw [hfj, hfk, h.sq_eq_one]
      have hbuv : b (eL j * eL k : pCore 2 X) (fL j * fL k : pCore 2 X) = 0 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hbl, hbr, hbr, hEFd, hEFo _ _ hjk,
          hEFo _ _ hjk.symm, hEFd]
        decide
      refine hE8 _ _ huu hvv (hrel0 _ _ hbuv) (fL j) (eL j) ?_ ?_ ?_ ?_
      · rw [QuotientGroup.mk_mul, hbl, hEFd, hEFo _ _ hjk.symm, add_zero]
      · rw [QuotientGroup.mk_mul, hbl, hFF, hFF, add_zero]
      · rw [QuotientGroup.mk_mul, hbl, hEE, hEE, add_zero]
      · rw [QuotientGroup.mk_mul, hbl, hFEd, hFEo _ _ hjk.symm, add_zero]
  by_cases hd₀ : eL i₀ * eL i₀ = 1 ∨ fL i₀ * fL i₀ = 1 <;>
    by_cases hd₁ : eL i₁ * eL i₁ = 1 ∨ fL i₁ * fL i₁ = 1 <;>
    by_cases hd₂ : eL i₂ * eL i₂ = 1 ∨ fL i₂ * fL i₂ = 1
  · exact hpair i₀ i₁ h01 (iff_of_true hd₀ hd₁)
  · exact hpair i₀ i₁ h01 (iff_of_true hd₀ hd₁)
  · exact hpair i₀ i₂ h02 (iff_of_true hd₀ hd₂)
  · exact hpair i₁ i₂ h12 (iff_of_false hd₁ hd₂)
  · exact hpair i₁ i₂ h12 (iff_of_true hd₁ hd₂)
  · exact hpair i₀ i₂ h02 (iff_of_false hd₀ hd₂)
  · exact hpair i₀ i₁ h01 (iff_of_false hd₀ hd₁)
  · exact hpair i₀ i₁ h01 (iff_of_false hd₀ hd₁)

end Core

end CFSG.RankThree.PartTwo.Sec4.Census
