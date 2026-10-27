module

public import CFSG.Walter.ReeOrder.WardLocal.CY

public section

open scoped BigOperators Classical MatrixGroups Pointwise commutatorElement

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

section General

variable {G : Type} [Group G]

@[expose] def cenMod (P N : Subgroup G) (x : G) (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ = n) :
    Subgroup G where
  carrier := {g | g ∈ P ∧ g * x * g⁻¹ * x⁻¹ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨P.mul_mem ha hb, ?_⟩
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e, hN a ha _ hb']
    exact N.mul_mem hb' ha'
  one_mem' := ⟨P.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨P.inv_mem ha, ?_⟩
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e, hN _ (P.inv_mem ha) _ (N.inv_mem ha')]
    exact N.inv_mem ha'

theorem mem_cenMod {P N : Subgroup G} {x : G} {hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ = n} {g : G} :
    g ∈ cenMod P N x hN ↔ g ∈ P ∧ g * x * g⁻¹ * x⁻¹ ∈ N := Iff.rfl

theorem card_cenMod [Finite G] {P N : Subgroup G} {x : G}
    (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ = n) (hNc : ∀ u ∈ N, ∀ v ∈ N, u * v = v * u)
    (hsurj : ∀ c ∈ N, ∃ g ∈ P, g * x * g⁻¹ * x⁻¹ = c) :
    Nat.card (cenMod P N x hN) =
      Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) * Nat.card N := by
  let φ : cenMod P N x hN →* N :=
    { toFun := fun g => ⟨g * x * (g : G)⁻¹ * x⁻¹, g.2.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, mul_inv_rev]
        have e : (a : G) * b * x * ((b : G)⁻¹ * (a : G)⁻¹) * x⁻¹ =
            a * (b * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹ * (a * x * (a : G)⁻¹ * x⁻¹) := by group
        rw [e, hN a a.2.1 _ b.2.2]
        exact hNc _ b.2.2 _ a.2.2 }
  have hsurjφ : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    obtain ⟨g, hg, hgc⟩ := hsurj c hc
    exact ⟨⟨g, hg, by rw [hgc]; exact hc⟩, Subtype.ext hgc⟩
  have hle : P ⊓ Subgroup.centralizer ({x} : Set G) ≤ cenMod P N x hN := fun g hg => by
    refine ⟨hg.1, ?_⟩
    rw [show g * x * g⁻¹ * x⁻¹ = 1 by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hg.2]; group]
    exact N.one_mem
  have hker : φ.ker = (P ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (cenMod P N x hN) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h' : (g : G) * x * (g : G)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨g.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (g : G) * x = (g : G) * x * (g : G)⁻¹ * x⁻¹ * x * g := by group
        _ = x * g := by rw [h']; group
    · intro h
      apply Subtype.ext
      show (g : G) * x * (g : G)⁻¹ * x⁻¹ = 1
      rw [Subgroup.mem_centralizer_singleton_iff.mp h.2]; group
  have h1 := φ.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hsurjφ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  rw [h1, mul_comm]

theorem exp3_comm {x y : G} (hy : y ^ 3 = 1) (h1 : (x * y⁻¹) ^ 3 = 1) (h2 : (y * x) ^ 3 = 1) :
    x * (y⁻¹ * x * y) = (y⁻¹ * x * y) * x := by
  have e1 : x * y⁻¹ * x = y * x⁻¹ * y := by
    have h : x * y⁻¹ * x * y⁻¹ * x * y⁻¹ = 1 := by rw [← h1, pow_three]; group
    calc x * y⁻¹ * x = (x * y⁻¹ * x * y⁻¹ * x * y⁻¹) * (y * x⁻¹ * y) := by group
      _ = y * x⁻¹ * y := by rw [h, one_mul]
  have e2 : x * y * x = y⁻¹ * x⁻¹ * y⁻¹ := by
    have h : y * x * y * x * y * x = 1 := by rw [← h2, pow_three]; group
    calc x * y * x = y⁻¹ * (y * x * y * x * y * x) * x⁻¹ * y⁻¹ := by group
      _ = y⁻¹ * x⁻¹ * y⁻¹ := by rw [h]; group
  have hy2 : y ^ 2 = y⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, hy]
  have hy1 : y = y⁻¹ * y⁻¹ := by
    calc y = (y ^ 2)⁻¹ := by rw [hy2, inv_inv]
      _ = y⁻¹ * y⁻¹ := by group
  calc x * (y⁻¹ * x * y) = (x * y⁻¹ * x) * y := by group
    _ = y * x⁻¹ * y * y := by rw [e1]
    _ = y * x⁻¹ * y ^ 2 := by rw [sq]; group
    _ = y * x⁻¹ * y⁻¹ := by rw [hy2]
    _ = (y⁻¹ * y⁻¹) * x⁻¹ * y⁻¹ := by rw [← hy1]
    _ = y⁻¹ * (x * y * x) := by rw [e2]; group
    _ = (y⁻¹ * x * y) * x := by group

end General

theorem zcen_central {G : Type} [Group G] (P : Subgroup G) :
    ∀ g ∈ P, ∀ c ∈ zcen P, g * c * g⁻¹ = c := fun _ hg _ hc => by
  rw [← (mem_zcen.mp hc).2 _ hg]; group

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  {P : Subgroup G} (hP1P : PP1 S ≤ P) (hPc : Nat.card P = q ^ 3)
  (hPn : ∀ n ∈ NN1 S, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hN1c : Nat.card (NN1 S) = q ^ 3 * (q - 1))

namespace Block

include B hq hK hG hP1P hPc in
theorem exists_outer : ∃ x ∈ P, x ∉ PP1 S := by
  by_contra h
  push Not at h
  exact B.PP1_ne_P hq hK hG hPc (le_antisymm hP1P fun x hx => h x hx)

include B hq hK hG hP1P hPc in
theorem mem_PP1_of_J {y : G} (hy : y ∈ P) (hyJ : y⁻¹ * (S.J * y * S.J) ∈ PP1 S) :
    y ∈ PP1 S := by
  have hcT := B.hcT hq hK hG
  set a := y⁻¹ * (S.J * y * S.J) with ha
  have ha3 : a ^ 3 = 1 := PP1_pow_three hq hK hcT hG hyJ
  have hJy : S.J * y * S.J = y * a := by rw [ha]; group
  have hJa : S.J * a * S.J = a⁻¹ := by
    rw [ha]
    calc S.J * (y⁻¹ * (S.J * y * S.J)) * S.J = S.J * y⁻¹ * S.J * y * (S.J * S.J) := by group
      _ = (y⁻¹ * (S.J * y * S.J))⁻¹ := by
          rw [S.J_mul, mul_one]; simp only [mul_inv_rev, inv_inv, S.J_inv]; group
  have h2 : a⁻¹ = a ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', ha3]
  have e1 : (S.J * y * S.J) * (S.J * a * S.J) * (S.J * a * S.J) = S.J * (y * a ^ 2) * S.J := by
    rw [show (S.J * y * S.J) * (S.J * a * S.J) * (S.J * a * S.J) =
      S.J * y * (S.J * S.J) * a * (S.J * S.J) * a * S.J by group, S.J_mul, sq]
    group
  have hfix : S.J * (y * a ^ 2) * S.J = y * a ^ 2 := by
    rw [← e1, hJy, hJa, show y * a * a⁻¹ * a⁻¹ = y * a⁻¹ by group, h2]
  have hFF : y * a ^ 2 ∈ FF S := by
    rw [← inf_centralizer_J hq hK hcT hP1P hPc]
    refine ⟨P.mul_mem hy (P.pow_mem (hP1P hyJ) 2), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc y * a ^ 2 * S.J = (S.J * (y * a ^ 2) * S.J) * S.J := by rw [hfix]
      _ = S.J * (y * a ^ 2) * (S.J * S.J) := by group
      _ = S.J * (y * a ^ 2) := by rw [S.J_mul, mul_one]
  have hy' : y = (y * a ^ 2) * (a ^ 2)⁻¹ := by group
  rw [hy']
  exact (PP1 S).mul_mem (FF_le_PP1 hq hcT hFF) ((PP1 S).inv_mem ((PP1 S).pow_mem hyJ 2))

include B hq hK hG hPn in
theorem J_conj_mem {y : G} (hy : y ∈ P) : S.J * y * S.J ∈ P := by
  have := (Subgroup.mem_normalizer_iff.mp (B.J_mem_normalizer hq hK hG hPn) y).mp hy
  rwa [S.J_inv] at this

include B hq hK hG hP1P hPc hPn hN1c in
theorem mul_J_mem_PP1 {y : G} (hy : y ∈ P) : y * (S.J * y * S.J) ∈ PP1 S := by
  have hJy := B.J_conj_mem hq hK hG hPn hy
  apply B.mem_PP1_of_J hq hK hG hP1P hPc (P.mul_mem hy hJy)
  have h := B.comm_mem_PP1 hq hK hG hP1P hPc hPn hN1c (P.inv_mem hJy) (P.inv_mem hy)
  have e : (y * (S.J * y * S.J))⁻¹ * (S.J * (y * (S.J * y * S.J)) * S.J) =
      (S.J * y * S.J)⁻¹ * y⁻¹ * (S.J * y * S.J)⁻¹⁻¹ * y⁻¹⁻¹ := by
    rw [show S.J * (y * (S.J * y * S.J)) * S.J = (S.J * y * S.J) * y * (S.J * S.J) by group,
      S.J_mul, mul_one]
    group
  rw [e]; exact h

include B hq hK hG hP1P hPc hPn hN1c in
theorem exists_J_inv_coset {y : G} (hy : y ∈ P) :
    ∃ Y ∈ P, S.J * Y * S.J = Y⁻¹ ∧ y⁻¹ * Y ∈ PP1 S := by
  have hJy := B.J_conj_mem hq hK hG hPn hy
  have hv := B.mul_J_mem_PP1 hq hK hG hP1P hPc hPn hN1c hy
  refine ⟨y⁻¹ * (S.J * y * S.J), P.mul_mem (P.inv_mem hy) hJy, ?_, ?_⟩
  · calc S.J * (y⁻¹ * (S.J * y * S.J)) * S.J = S.J * y⁻¹ * S.J * y * (S.J * S.J) := by group
      _ = (y⁻¹ * (S.J * y * S.J))⁻¹ := by
          rw [S.J_mul, mul_one]; simp only [mul_inv_rev, inv_inv, S.J_inv]; group
  · have e : y⁻¹ * (y⁻¹ * (S.J * y * S.J)) = (y ^ 3)⁻¹ * (y * (S.J * y * S.J)) := by group
    rw [e]
    exact (PP1 S).mul_mem ((PP1 S).inv_mem (B.cube_mem_PP1 hq hK hG hP1P hPc hPn hN1c hy)) hv

include B hq hK hG hP1P hPc hPn in
theorem card_cenMod_outer {x : G} (hx : x ∈ P) (hxP1 : x ∉ PP1 S) :
    Nat.card (cenMod P (zcen P) x (zcen_central P)) =
      Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) * q := by
  rw [← B.card_zcen hq hK hG hP1P hPc hPn]
  exact card_cenMod (zcen_central P) (fun u hu v hv => (mem_zcen.mp hu).2 v (mem_zcen.mp hv).1)
    (fun c hc => by
      obtain ⟨a, ha, hac⟩ := B.exists_conj_outer hq hK hG hP1P hPc hPn hx hxP1 hc
      exact ⟨a, hP1P ha, by rw [hac]; exact zcen_conj hx hc⟩)

include B hq hK hG hP1P hPc hPn hN1c in
theorem card_inf_centralizer_outer (hm : q = 3 * m ^ 2) {x : G} (hx : x ∈ P)
    (hxP1 : x ∉ PP1 S) :
    Nat.card (P ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) = 3 * q := by
  obtain ⟨Y, hYP, hYJ, hxY⟩ := B.exists_J_inv_coset hq hK hG hP1P hPc hPn hN1c hx
  have hYP1 : Y ∉ PP1 S := fun h => hxP1 (by
    rw [show x = Y * (x⁻¹ * Y)⁻¹ by group]
    exact (PP1 S).mul_mem h ((PP1 S).inv_mem hxY))
  have hcY := (B.centralizer_inv_outer hq hK hG hP1P hPc hPn hN1c hm hYP hYP1 hYJ).1
  have hCY := B.centralizer_outer_le hq hK hG hP1P hPc hPn hN1c hYP hYP1
  have hD : cenMod P (zcen P) x (zcen_central P) = cenMod P (zcen P) Y (zcen_central P) := by
    ext g
    rw [mem_cenMod, mem_cenMod]
    refine and_congr_right fun hg => ?_
    have hb := B.comm_PP1_mem_zcen hq hK hG hP1P hPc hPn hg hxY
    have e : g * Y * g⁻¹ * Y⁻¹ =
        (g * x * g⁻¹ * x⁻¹) * (g * (x⁻¹ * Y) * g⁻¹ * (x⁻¹ * Y)⁻¹) := by
      rw [← zcen_conj hx hb]; group
    rw [e, Subgroup.mul_mem_cancel_right _ hb]
  have h1 := B.card_cenMod_outer hq hK hG hP1P hPc hPn hx hxP1
  have h2 := B.card_cenMod_outer hq hK hG hP1P hPc hPn hYP hYP1
  rw [hD, h2, inf_eq_right.mpr hCY, hcY] at h1
  have hq0 : 0 < q := by rw [hq]; positivity
  exact (Nat.eq_of_mul_eq_mul_right hq0 h1).symm

include B hq hK hG hP1P hPc hPn hN1c in
theorem centralizer_outer (hm : q = 3 * m ^ 2) {x : G} (hx : x ∈ P) (hxP1 : x ∉ PP1 S) :
    Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers x ⊔ zcen P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCP := B.centralizer_outer_le hq hK hG hP1P hPc hPn hN1c hx hxP1
  have hc := B.card_inf_centralizer_outer hq hK hG hP1P hPc hPn hN1c hm hx hxP1
  rw [inf_eq_right.mpr hCP] at hc
  have hle : Subgroup.zpowers x ⊔ zcen P ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ?_
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((mem_zcen.mp hc).2 x hx)
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hc]
  have hHP : Subgroup.zpowers x ⊔ zcen P ≤ P := hle.trans hCP
  have hHp : IsPGroup 3 (Subgroup.zpowers x ⊔ zcen P : Subgroup G) :=
    (isPGroup_P hq hPc).to_le hHP
  obtain ⟨n, hn⟩ := hHp.exists_card_eq
  have hZH : zcen P < Subgroup.zpowers x ⊔ zcen P := lt_of_le_of_ne le_sup_right fun h =>
    hxP1 (B.zcen_le_PP1 hq hK hG hP1P hPc hPn (by
      rw [h]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
  have hlt := Subgroup.card_lt_of_lt hZH
  rw [B.card_zcen hq hK hG hP1P hPc hPn, hn, hq] at hlt
  rw [hn, hq]
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  calc 3 * 3 ^ (2 * k + 1) = 3 ^ (2 * k + 1 + 1) := by ring
    _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) this

include B hq hK hG hP1P hPc hPn hN1c in
theorem exists_comm_not_mem_zcen (hm : q = 3 * m ^ 2) {x : G} (hx : x ∈ P) (hxP1 : x ∉ PP1 S) :
    ∃ g ∈ P, g * x * g⁻¹ * x⁻¹ ∉ zcen P := by
  by_contra hall
  push Not at hall
  have heq : cenMod P (zcen P) x (zcen_central P) = P := by
    ext g; exact ⟨fun h => h.1, fun h => ⟨h, hall g h⟩⟩
  have hcard := B.card_cenMod_outer hq hK hG hP1P hPc hPn hx hxP1
  rw [heq, hPc, B.card_inf_centralizer_outer hq hK hG hP1P hPc hPn hN1c hm hx hxP1] at hcard
  have hq27 : 27 ≤ q := S.q_ge
  nlinarith

include B hq hK hG hP1P hPc hPn in
theorem zcen_le_commutator_PP1 : zcen P ≤ ⁅PP1 S, P⁆ := by
  have hcT := B.hcT hq hK hG
  have hq27 : 27 ≤ q := S.q_ge
  intro c hc
  obtain ⟨a, ha, haZ⟩ : ∃ a ∈ PP1 S, a ∉ zcen P := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show PP1 S ≤ zcen P from fun a ha => h a ha)
    rw [card_PP1 hq hK hcT hG, B.card_zcen hq hK hG hP1P hPc hPn] at this
    nlinarith
  obtain ⟨g, hg, hga⟩ := B.exists_conj_PP1 hq hK hG hP1P hPc hPn ha haZ hc
  have h1 : ⁅a⁻¹, g⁆ = c := by
    rw [commutatorElement_def, inv_inv]
    calc a⁻¹ * g * a * g⁻¹ = a⁻¹ * (g * a * g⁻¹) := by group
      _ = a⁻¹ * (a * c) := by rw [hga]
      _ = c := by group
  rw [← h1]
  exact Subgroup.commutator_mem_commutator ((PP1 S).inv_mem ha) hg

include B hq hK hG hP1P hPc hPn in
theorem commutator_PP1_eq_zcen : ⁅PP1 S, P⁆ = zcen P := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha g hg => ?_)
    (B.zcen_le_commutator_PP1 hq hK hG hP1P hPc hPn)
  have h := B.comm_PP1_mem_zcen hq hK hG hP1P hPc hPn hg ha
  rw [commutatorElement_def]
  have e : a * g * a⁻¹ * g⁻¹ = (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
  rw [e]
  exact (zcen P).inv_mem h

include B hq hK hG hP1P hPc hPn hN1c in
theorem commutator_eq_PP1 (hm : q = 3 * m ^ 2) : ⁅P, P⁆ = PP1 S := by
  have hcT := B.hcT hq hK hG
  have hq27 : 27 ≤ q := S.q_ge
  have hle : ⁅P, P⁆ ≤ PP1 S := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]; exact B.comm_mem_PP1 hq hK hG hP1P hPc hPn hN1c ha hb
  have hZle : zcen P ≤ ⁅P, P⁆ := (B.zcen_le_commutator_PP1 hq hK hG hP1P hPc hPn).trans
    (Subgroup.commutator_mono hP1P le_rfl)
  obtain ⟨x, hx, hxP1⟩ := B.exists_outer hq hK hG hP1P hPc
  obtain ⟨g, hg, hgx⟩ := B.exists_comm_not_mem_zcen hq hK hG hP1P hPc hPn hN1c hm hx hxP1
  have hgxm : g * x * g⁻¹ * x⁻¹ ∈ ⁅P, P⁆ := by
    rw [← commutatorElement_def]; exact Subgroup.commutator_mem_commutator hg hx
  have hR : ∀ r ∈ RR S, ∀ u ∈ ⁅P, P⁆, r * u * r⁻¹ ∈ ⁅P, P⁆ := by
    intro r hr u hu
    have hPmap : P.map (MulAut.conj r).toMonoidHom ≤ P := by
      rintro _ ⟨v, hv, rfl⟩
      exact B.RR_conj_P hq hK hG hPn hr hv
    have h1 : (MulAut.conj r).toMonoidHom u ∈ (⁅P, P⁆).map (MulAut.conj r).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rw [Subgroup.map_commutator] at h1
    exact Subgroup.commutator_mono hPmap hPmap h1
  obtain ⟨t, ht3, ht⟩ := card_RR_inv hq hK hPc (hle.trans hP1P) hR
  have hlt : q < Nat.card (⁅P, P⁆ : Subgroup G) := by
    rw [← B.card_zcen hq hK hG hP1P hPc hPn]
    exact Subgroup.card_lt_of_lt (lt_of_le_of_ne hZle fun h => hgx (by rw [h]; exact hgxm))
  have hle2 := Subgroup.card_le_of_le hle
  rw [card_PP1 hq hK hcT hG] at hle2
  rw [ht] at hlt hle2
  have ht2 : t = 2 := by
    rcases (show t ≤ 1 ∨ t = 2 ∨ t = 3 by omega) with h | h | h
    · exfalso
      have : q ^ t ≤ q ^ 1 := Nat.pow_le_pow_right (by omega) h
      rw [pow_one] at this; omega
    · exact h
    · exfalso
      rw [h] at hle2
      have : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_PP1 hq hK hcT hG, ht, ht2])

include B hq hK hG hP1P hPc hPn in
theorem cube_mul_PP1 {x a : G} (hx : x ∈ P) (ha : a ∈ PP1 S) : (x * a) ^ 3 = x ^ 3 := by
  have hcT := B.hcT hq hK hG
  have hwZ : x⁻¹ * a * x * a⁻¹ ∈ zcen P := by
    have := B.comm_PP1_mem_zcen hq hK hG hP1P hPc hPn (P.inv_mem hx) ha
    rwa [inv_inv] at this
  set w := x⁻¹ * a * x * a⁻¹ with hw
  have hw3 : w ^ 3 = 1 :=
    PP1_pow_three hq hK hcT hG (B.zcen_le_PP1 hq hK hG hP1P hPc hPn hwZ)
  have ha3 : a ^ 3 = 1 := PP1_pow_three hq hK hcT hG ha
  have hwa : w * a = a * w := (mem_zcen.mp hwZ).2 a (hP1P ha)
  have hxw : x⁻¹ * w * x = w := by
    have := zcen_conj (P.inv_mem hx) hwZ
    rwa [inv_inv] at this
  have h1 : x⁻¹ * a * x = w * a := by rw [hw]; group
  have h2 : x⁻¹ * (x⁻¹ * a * x) * x = w * (w * a) := by
    rw [h1, show x⁻¹ * (w * a) * x = (x⁻¹ * w * x) * (x⁻¹ * a * x) by group, hxw, h1]
  calc (x * a) ^ 3 = x ^ 3 * (x⁻¹ * (x⁻¹ * a * x) * x) * (x⁻¹ * a * x) * a := by
        rw [pow_three, pow_three]; group
    _ = x ^ 3 * (w * (w * a) * (w * a) * a) := by rw [h2, h1]; group
    _ = x ^ 3 * (w * w * (a * w) * a * a) := by group
    _ = x ^ 3 * (w * w * (w * a) * a * a) := by rw [hwa]
    _ = x ^ 3 * (w ^ 3 * a ^ 3) := by simp only [pow_three]; group
    _ = x ^ 3 := by rw [hw3, ha3, mul_one, mul_one]

include B hq hK hG hP1P hPc in
theorem eq_one_of_conj_coset {w x : G} (hw : w ∈ WW S) (hx : x ∈ P) (hxP1 : x ∉ PP1 S)
    (h : x⁻¹ * (w * x * w⁻¹) ∈ PP1 S) : w = 1 := by
  have hcT := B.hcT hq hK hG
  by_contra hw1
  by_cases hwJ : w = S.J
  · subst hwJ
    apply hxP1
    refine B.mem_PP1_of_J hq hK hG hP1P hPc hx ?_
    rwa [S.J_inv] at h
  · have hwN := WW_le_normalizer_PP1 hq hcT hw
    have hconj : ∀ b ∈ PP1 S, w * b * w⁻¹ ∈ PP1 S := fun b hb =>
      (Subgroup.mem_normalizer_iff.mp hwN b).mp hb
    have hbot := inf_centralizer_WW hq hK hPc hw hw1 hwJ
    let f : PP1 S → PP1 S := fun b => ⟨b * (w * b * w⁻¹)⁻¹,
      (PP1 S).mul_mem b.2 ((PP1 S).inv_mem (hconj b b.2))⟩
    have hinj : Function.Injective f := by
      intro b b' hbb'
      have e : (b : G) * (w * b * w⁻¹)⁻¹ = b' * (w * b' * w⁻¹)⁻¹ := congrArg Subtype.val hbb'
      have e2 : (b' : G)⁻¹ * b = (w * b' * w⁻¹)⁻¹ * (w * b * w⁻¹) := by
        calc (b' : G)⁻¹ * b = (b' : G)⁻¹ * ((b : G) * (w * b * w⁻¹)⁻¹) * (w * b * w⁻¹) := by
              group
          _ = (b' : G)⁻¹ * ((b' : G) * (w * b' * w⁻¹)⁻¹) * (w * b * w⁻¹) := by rw [e]
          _ = (w * b' * w⁻¹)⁻¹ * (w * b * w⁻¹) := by group
      have hu1 : w * ((b' : G)⁻¹ * b) * w⁻¹ = (b' : G)⁻¹ * b := by
        calc w * ((b' : G)⁻¹ * b) * w⁻¹ = (w * b' * w⁻¹)⁻¹ * (w * b * w⁻¹) := by group
          _ = (b' : G)⁻¹ * b := e2.symm
      have hmem : (b' : G)⁻¹ * b ∈ P ⊓ Subgroup.centralizer ({w} : Set G) := by
        refine ⟨P.mul_mem (P.inv_mem (hP1P b'.2)) (hP1P b.2),
          Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc (b' : G)⁻¹ * b * w = (w * ((b' : G)⁻¹ * b) * w⁻¹) * w := by rw [hu1]
          _ = w * ((b' : G)⁻¹ * b) := by group
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext (inv_mul_eq_one.mp hmem).symm
    obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨x⁻¹ * (w * x * w⁻¹), h⟩
    have hb' : (b : G) * (w * b * w⁻¹)⁻¹ = x⁻¹ * (w * x * w⁻¹) := congrArg Subtype.val hb
    have hfix : w * (x * b) * w⁻¹ = x * b := by
      calc w * (x * b) * w⁻¹ = x * (x⁻¹ * (w * x * w⁻¹)) * (w * b * w⁻¹) := by group
        _ = x * ((b : G) * (w * b * w⁻¹)⁻¹) * (w * b * w⁻¹) := by rw [hb']
        _ = x * b := by group
    have hmem : x * b ∈ P ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine ⟨P.mul_mem hx (hP1P b.2), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * b * w = (w * (x * b) * w⁻¹) * w := by rw [hfix]
        _ = w * (x * b) := by group
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hxP1
    rw [eq_inv_of_mul_eq_one_left hmem]
    exact (PP1 S).inv_mem b.2

include B hq hK hG hP1P hPc hPn hN1c in
theorem exists_WW_conj {x y : G} (hx : x ∈ P) (hxP1 : x ∉ PP1 S) (hy : y ∈ P)
    (hyP1 : y ∉ PP1 S) : ∃ w ∈ WW S, (w * x * w⁻¹)⁻¹ * y ∈ PP1 S := by
  have hcT := B.hcT hq hK hG
  have hWN := WW_le_normalizer hq hK hcT hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c
  have hWN1 : ∀ w ∈ WW S, w ∈ Subgroup.normalizer (PP1 S : Set G) := fun w hw =>
    WW_le_normalizer_PP1 hq hcT hw
  have : ((PP1 S).subgroupOf P).Normal := ⟨fun n hn g => by
    show ((g * n * g⁻¹ : P) : G) ∈ PP1 S
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact B.PP1_normal hq hK hG hP1P hPc hPn hN1c g.2 hn⟩
  have : Fintype (P ⧸ (PP1 S).subgroupOf P) := Fintype.ofFinite _
  have hconjP : ∀ w ∈ WW S, w * x * w⁻¹ ∈ P := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hWN hw) x).mp hx
  let φ : WW S → P ⧸ (PP1 S).subgroupOf P := fun w =>
    QuotientGroup.mk (⟨w * x * (w : G)⁻¹, hconjP w w.2⟩ : P)
  have hmk : ∀ u v : P, (QuotientGroup.mk u : P ⧸ (PP1 S).subgroupOf P) = QuotientGroup.mk v ↔
      (u : G)⁻¹ * v ∈ PP1 S := fun u v => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]; rfl
  have hinj : Function.Injective φ := by
    intro w w' hww'
    have h1 : (w * x * (w : G)⁻¹)⁻¹ * (w' * x * (w' : G)⁻¹) ∈ PP1 S := (hmk _ _).mp hww'
    have h2 : x⁻¹ * (((w : G)⁻¹ * w') * x * ((w : G)⁻¹ * w')⁻¹) ∈ PP1 S := by
      have := (Subgroup.mem_normalizer_iff.mp (hWN1 _ ((WW S).inv_mem w.2)) _).mp h1
      rw [show x⁻¹ * (((w : G)⁻¹ * w') * x * ((w : G)⁻¹ * w')⁻¹) =
        (w : G)⁻¹ * ((w * x * (w : G)⁻¹)⁻¹ * (w' * x * (w' : G)⁻¹)) * (w : G)⁻¹⁻¹ by group]
      exact this
    have h3 := B.eq_one_of_conj_coset hq hK hG hP1P hPc
      ((WW S).mul_mem ((WW S).inv_mem w.2) w'.2) hx hxP1 h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have hne1 : ∀ w, φ w ≠ 1 := by
    intro w hw
    have h1 : w * x * (w : G)⁻¹ ∈ PP1 S :=
      (QuotientGroup.eq_one_iff (N := (PP1 S).subgroupOf P) _).mp hw
    apply hxP1
    have := (Subgroup.mem_normalizer_iff.mp (hWN1 _ ((WW S).inv_mem w.2)) _).mp h1
    rwa [show (w : G)⁻¹ * (w * x * (w : G)⁻¹) * (w : G)⁻¹⁻¹ = x by group] at this
  have hcardQ : Nat.card (P ⧸ (PP1 S).subgroupOf P) = q := by
    have h := ((PP1 S).subgroupOf P).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP1P).toEquiv, card_PP1 hq hK hcT hG,
      hPc] at h
    have hq0 : 0 < q ^ 2 := by rw [hq]; positivity
    exact Nat.eq_of_mul_eq_mul_right hq0 (h.symm.trans (by ring))
  have hsub : Finset.univ.image φ ⊆ Finset.univ.erase 1 := by
    intro z hz
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_erase.mpr ⟨hne1 w, Finset.mem_univ _⟩
  have hcard : (Finset.univ.erase (1 : P ⧸ (PP1 S).subgroupOf P)).card ≤
      (Finset.univ.image φ).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hcardQ, card_WW hq hK]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hyQ : (QuotientGroup.mk (⟨y, hy⟩ : P) : P ⧸ (PP1 S).subgroupOf P) ∈
      Finset.univ.erase 1 := by
    refine Finset.mem_erase.mpr ⟨fun h1 => hyP1 ?_, Finset.mem_univ _⟩
    exact (QuotientGroup.eq_one_iff (N := (PP1 S).subgroupOf P) _).mp h1
  rw [← heq] at hyQ
  obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hyQ
  exact ⟨w, w.2, (hmk _ _).mp hw⟩

include B hq hK hG hP1P hPc hPn hN1c in
theorem cube_ne_one_outer (hm : q = 3 * m ^ 2) {x : G} (hx : x ∈ P) (hxP1 : x ∉ PP1 S) :
    x ^ 3 ≠ 1 := by
  intro h3
  have hcT := B.hcT hq hK hG
  have hWN := WW_le_normalizer hq hK hcT hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c
  have hall : ∀ y ∈ P, y ^ 3 = 1 := by
    intro y hy
    by_cases hyP1 : y ∈ PP1 S
    · exact PP1_pow_three hq hK hcT hG hyP1
    · obtain ⟨w, hw, hwy⟩ := B.exists_WW_conj hq hK hG hP1P hPc hPn hN1c hx hxP1 hy hyP1
      have hwx : w * x * w⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hWN hw) x).mp hx
      have e : y = (w * x * w⁻¹) * ((w * x * w⁻¹)⁻¹ * y) := by group
      rw [e, B.cube_mul_PP1 hq hK hG hP1P hPc hPn hwx hwy, conj_pow, h3]
      group
  obtain ⟨g, hg, hgx⟩ := B.exists_comm_not_mem_zcen hq hK hG hP1P hPc hPn hN1c hm hx hxP1
  apply hgx
  have hc := exp3_comm (x := x) (y := g⁻¹) (by rw [inv_pow, hall g hg, inv_one])
    (hall _ (P.mul_mem hx (P.inv_mem (P.inv_mem hg)))) (hall _ (P.mul_mem (P.inv_mem hg) hx))
  simp only [inv_inv] at hc
  have hb : x⁻¹ * (g * x * g⁻¹) ∈ PP1 S := by
    have := B.comm_mem_PP1 hq hK hG hP1P hPc hPn hN1c (P.inv_mem hx) hg
    rw [inv_inv] at this
    rw [show x⁻¹ * (g * x * g⁻¹) = x⁻¹ * g * x * g⁻¹ by group]
    exact this
  have hbx : (x⁻¹ * (g * x * g⁻¹)) * x = x * (x⁻¹ * (g * x * g⁻¹)) := by
    calc (x⁻¹ * (g * x * g⁻¹)) * x = x⁻¹ * ((g * x * g⁻¹) * x) := by group
      _ = x⁻¹ * (x * (g * x * g⁻¹)) := by rw [hc]
      _ = x * (x⁻¹ * (g * x * g⁻¹)) := by group
  have hbZ := B.mem_zcen_of_commute_outer hq hK hG hP1P hPc hPn hx hxP1 hb hbx
  have e : g * x * g⁻¹ * x⁻¹ = x * (x⁻¹ * (g * x * g⁻¹)) * x⁻¹ := by group
  rw [e, zcen_conj hx hbZ]
  exact hbZ

include B hq hK hG hP1P hPc hPn hN1c in
theorem orderOf_outer (hm : q = 3 * m ^ 2) {x : G} (hx : x ∈ P) (hxP1 : x ∉ PP1 S) :
    orderOf x = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := B.cube_ne_one_outer hq hK hG hP1P hPc hPn hN1c hm hx hxP1
  have hZ := B.cube_mem_zcen hq hK hG hP1P hPc hPn hN1c hx hxP1
  have h9 : x ^ 9 = 1 := by
    rw [show 9 = 3 * 3 by rfl, pow_mul, PP1_pow_three hq hK (B.hcT hq hK hG) hG
      (B.zcen_le_PP1 hq hK hG hP1P hPc hPn hZ)]
  have := orderOf_eq_prime_pow (p := 3) (n := 1) (x := x) (by simpa using h3)
    (by simpa using h9)
  simpa using this

include B hq hK hG hP1P hPc hPn hN1c in
theorem exists_cube_eq (hm : q = 3 * m ^ 2) {c : G} (hc : c ∈ zcen P) (hc1 : c ≠ 1) :
    ∃ x ∈ P, x ∉ PP1 S ∧ x ^ 3 = c := by
  have hcT := B.hcT hq hK hG
  have hWN := WW_le_normalizer hq hK hcT hG (B.card_AA hq hK hG)
    (fun _ hx h3 => B.card_centralizer_dvd hq hG hx h3) hP1P hPc hPn hN1c
  obtain ⟨x₀, hx₀, hx₀P1⟩ := B.exists_outer hq hK hG hP1P hPc
  have hZ := B.cube_mem_zcen hq hK hG hP1P hPc hPn hN1c hx₀ hx₀P1
  have h1 := B.cube_ne_one_outer hq hK hG hP1P hPc hPn hN1c hm hx₀ hx₀P1
  obtain ⟨w, hw, hwc⟩ := AA_transitive hq hK hcT hG (B.card_AA hq hK hG)
    (B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hZ h1) (B.mem_AA_of_zcen hq hK hG hP1P hPc hPn hc hc1)
  refine ⟨w * x₀ * w⁻¹, (Subgroup.mem_normalizer_iff.mp (hWN hw) x₀).mp hx₀, fun h => hx₀P1 ?_,
    by rw [conj_pow, hwc]⟩
  have := (Subgroup.mem_normalizer_iff.mp
    (WW_le_normalizer_PP1 hq hcT ((WW S).inv_mem hw)) _).mp h
  rwa [show w⁻¹ * (w * x₀ * w⁻¹) * w⁻¹⁻¹ = x₀ by group] at this

include B hq hK hG hP1P hPc hPn in
theorem exists_zcen_mul_FF {a : G} (ha : a ∈ PP1 S) : ∃ c ∈ zcen P, ∃ f ∈ FF S, c * f = a := by
  by_contra hne
  push Not at hne
  have h := B.sum_PP1 hq hK hG hP1P hPc hPn (fun x => if x = a then (1 : ℂ) else 0)
  have hL : ∑ x ∈ Finset.univ.filter (· ∈ PP1 S), (if x = a then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_ite_eq']; simp [ha]
  have hR : ∑ c ∈ Finset.univ.filter (· ∈ zcen P), ∑ b ∈ Finset.univ.filter (· ∈ FF S),
      (if c * b = a then (1 : ℂ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun c hc => Finset.sum_eq_zero fun b hb => ?_
    exact ite_eq_right_iff.mpr fun h =>
      absurd h (hne c (Finset.mem_filter.mp hc).2 b (Finset.mem_filter.mp hb).2)
  rw [hL, hR] at h
  exact one_ne_zero h

include B hq hK hG hP1P hPc hPn in
theorem PP1_eq_sup : PP1 S = zcen P ⊔ FF S := by
  apply le_antisymm
  · intro a ha
    obtain ⟨c, hc, f, hf, rfl⟩ := B.exists_zcen_mul_FF hq hK hG hP1P hPc hPn ha
    exact Subgroup.mul_mem_sup hc hf
  · exact sup_le (B.zcen_le_PP1 hq hK hG hP1P hPc hPn) (FF_le_PP1 hq (B.hcT hq hK hG))

end Block

end CFSG.Walter.WardLocal
