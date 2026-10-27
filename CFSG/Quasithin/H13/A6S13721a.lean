module

public import CFSG.Quasithin.H13.A6Nu
public import CFSG.Quasithin.Background.F9Dual

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G]

theorem two_pow_mod_three_of_odd {d : ℕ} (hd : Odd d) : 2 ^ d % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hd
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_two_pow_sub_eq_four_pow {a b : ℕ} (hba : b ≤ a) (h : 2 ^ a % 3 = 2 ^ b % 3) :
    ∃ k : ℕ, 2 ^ (a - b) = 4 ^ k := by
  obtain ⟨m, hm⟩ | hodd := Nat.even_or_odd (a - b)
  · exact ⟨m, by rw [hm, ← two_mul, pow_mul]; norm_num⟩
  · exfalso
    have e : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← pow_add, Nat.add_sub_cancel' hba]
    have hb : 2 ^ b % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ 2 ^ b := Nat.dvd_of_mod_eq_zero h0
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    rw [e, Nat.mul_mod, two_pow_mod_three_of_odd hodd] at h
    have hlt : 2 ^ b % 3 < 3 := Nat.mod_lt _ (by norm_num)
    generalize 2 ^ b % 3 = r at h hb hlt
    omega

theorem exists_nu_eq_four_pow {c : G} (hc : c ^ 3 = 1) {X : Subgroup G} (hX : IsPGroup 2 X)
    (hcX : c ∈ Subgroup.normalizer (X : Set G)) : ∃ k : ℕ, nu c X = 4 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End ↥X := fun x => ⟨c * x * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcX x).mp x.2⟩
  have hfn : ∀ k : ℕ, ∀ x : ↥X, (((f ^ k) x : ↥X) : G) = c ^ k * x * (c ^ k)⁻¹ := by
    intro k
    induction k with
    | zero =>
      intro x
      simp only [pow_zero, one_mul, inv_one, mul_one]
      rfl
    | succ k ih =>
      intro x
      have e : (f ^ (k + 1)) x = f ((f ^ k) x) := by rw [pow_succ']; rfl
      rw [e]
      show c * ((f ^ k) x : G) * c⁻¹ = _
      rw [ih, pow_succ']
      group
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [pow_one, hfn, hc, one_mul, inv_one, mul_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf3
  have hfix : Fintype.card (Function.fixedPoints f) = Nat.card (cfix c X) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), mem_cfix.2 ⟨x.1.2, ?_⟩⟩
        invFun := fun y => ⟨⟨y.1, (mem_cfix.1 y.2).1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have h := congrArg Subtype.val (show f x.1 = x.1 from x.2)
      change c * (x.1 : G) * c⁻¹ = x.1 at h
      calc c * (x.1 : G) = c * (x.1 : G) * c⁻¹ * c := by group
        _ = x.1 * c := by rw [h]
    · show f _ = _
      apply Subtype.ext
      show c * (y.1 : G) * c⁻¹ = y.1
      rw [(mem_cfix.1 y.2).2]
      group
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  have hcX' : cfix c X ≤ X := inf_le_left
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hX
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hX.to_le hcX')
  have hrel := Subgroup.relIndex_mul_card (cfix c X) X
  rw [inf_eq_left.2 hcX'] at hrel
  rw [ha, hb] at hmod
  rw [ha, hb] at hrel
  have hne : (cfix c X).relIndex X ≠ 0 := by
    show ((cfix c X).subgroupOf X).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have hba : b ≤ a := by
    by_contra hlt
    push Not at hlt
    have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hlt
    have h2 : 2 ^ b ≤ (cfix c X).relIndex X * 2 ^ b :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hne)
    have h3 : 2 ^ b ≤ 2 ^ a := h2.trans hrel.le
    exact absurd h1 (not_lt.mpr h3)
  obtain ⟨k, hk⟩ := exists_two_pow_sub_eq_four_pow hba hmod
  refine ⟨k, ?_⟩
  have e : 2 ^ a = 2 ^ (a - b) * 2 ^ b := by rw [← pow_add, Nat.sub_add_cancel hba]
  rw [e] at hrel
  have := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2 ^ b) hrel
  rw [nu, this, hk]

theorem nu_le_nu {c : G} {X Y : Subgroup G} (hYX : Y ≤ X)
    (hN : cfix c X ≤ Subgroup.normalizer (Y : Set G)) : nu c Y ≤ nu c X := by
  rw [nu_mul c hYX hN]
  have : (cfix c X ⊔ Y).relIndex X ≠ 0 := by
    show ((cfix c X ⊔ Y).subgroupOf X).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero this)

theorem four_mul_nu_le {c : G} (hc : c ^ 3 = 1) {X Y : Subgroup G} (hX : IsPGroup 2 X)
    (hYX : Y ≤ X) (hcX : c ∈ Subgroup.normalizer (X : Set G))
    (hcY : c ∈ Subgroup.normalizer (Y : Set G)) (hN : cfix c X ≤ Subgroup.normalizer (Y : Set G))
    (hne : ∃ x ∈ X, c * x * c⁻¹ * x⁻¹ ∉ Y) : 4 * nu c Y ≤ nu c X := by
  have hmul := nu_mul c hYX hN
  set m := (cfix c X ⊔ Y).relIndex X with hm
  have hm1 : m ≠ 1 := by
    intro h1
    obtain ⟨x, hx, hxY⟩ := hne
    have hxs : x ∈ ((cfix c X ⊔ Y : Subgroup G) : Set G) := Subgroup.relIndex_eq_one.mp h1 hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hxs
    obtain ⟨f, hf, y, hy, rfl⟩ := Set.mem_mul.mp hxs
    obtain ⟨-, hfc⟩ := mem_cfix.1 hf
    apply hxY
    have hcy : c * y * c⁻¹ * y⁻¹ ∈ Y :=
      Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hcY y).mp hy) (Y.inv_mem hy)
    have e : c * (f * y) * c⁻¹ * (f * y)⁻¹ = f * (c * y * c⁻¹ * y⁻¹) * f⁻¹ := by
      calc c * (f * y) * c⁻¹ * (f * y)⁻¹ = (c * f) * y * c⁻¹ * y⁻¹ * f⁻¹ := by group
        _ = (f * c) * y * c⁻¹ * y⁻¹ * f⁻¹ := by rw [hfc]
        _ = f * (c * y * c⁻¹ * y⁻¹) * f⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hN hf) _).mp hcy
  obtain ⟨k, hk⟩ := exists_nu_eq_four_pow hc hX hcX
  obtain ⟨j, hj⟩ := exists_nu_eq_four_pow hc (hX.to_le hYX) hcY
  rw [hk, hj] at hmul
  rw [hk, hj]
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact absurd hmul (by positivity)
  have hjk : j < k := by
    by_contra hle
    push Not at hle
    have h1 : 4 ^ k ≤ 4 ^ j := Nat.pow_le_pow_right (by norm_num) hle
    have h2 : m * 4 ^ j ≤ 1 * 4 ^ j := by rw [one_mul, ← hmul]; exact h1
    have h3 : m ≤ 1 := Nat.le_of_mul_le_mul_right h2 (by positivity)
    omega
  calc 4 * 4 ^ j = 4 ^ (j + 1) := by ring
    _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hjk

section F97

variable {T V L V₁ Vp H : Subgroup G}

omit [Finite G] in
theorem normalizes_of_conj_mem {X Y : Subgroup G} (h : ∀ l ∈ X, ∀ y ∈ Y, l * y * l⁻¹ ∈ Y) :
    X ≤ Subgroup.normalizer (Y : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h l hl y, fun hy => ?_⟩
  have := h l⁻¹ (X.inv_mem hl) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_inf_of {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (hA y) (hB y)

omit [Finite G] in
theorem conj_centralizer_mem {V : Subgroup G} {l y : G}
    (hl : l ∈ Subgroup.normalizer (V : Set G)) (hy : y ∈ Subgroup.centralizer (V : Set G)) :
    l * y * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro v hv
  have hv' : l⁻¹ * v * l ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hl) v).mp hv
    simpa using this
  have key := hy _ hv'
  calc v * (l * y * l⁻¹) = l * ((l⁻¹ * v * l) * y) * l⁻¹ := by group
    _ = l * (y * (l⁻¹ * v * l)) * l⁻¹ := by rw [key]
    _ = l * y * l⁻¹ * v := by group

theorem commF91_conj_right (h : HypF91 T V L V₁ Vp H) {k x u : G} (hk : k ∈ H)
    (hx : x ∈ pCoreOf 2 H) (hu : u ∈ conjClosure Vp H) (hkx : k * x * k⁻¹ = x) :
    x * (k * u * k⁻¹) * x⁻¹ * (k * u * k⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ := by
  have := h.commutator_conj hk hx hu
  rwa [hkx] at this

theorem commF91_conj_left (h : HypF91 T V L V₁ Vp H) {k x u : G} (hk : k ∈ H)
    (hx : x ∈ pCoreOf 2 H) (hu : u ∈ conjClosure Vp H) (hku : k * u * k⁻¹ = u) :
    (k * x * k⁻¹) * u * (k * x * k⁻¹)⁻¹ * u⁻¹ = x * u * x⁻¹ * u⁻¹ := by
  have := h.commutator_conj hk hx hu
  rwa [hku] at this

omit [Finite G] in
theorem mul_self_eq_inv_of_cube {c : G} (hc : c ^ 3 = 1) : c * c = c⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_three', hc]

theorem nu_dual_F97 (h : HypF91 T V L V₁ Vp H) (hU : IsElemAbelian 2 (conjClosure Vp H)) {c : G}
    (hcH : c ∈ H) (hc : c ^ 3 = 1) :
    (cfix c (pCoreOf 2 H) ⊔
        (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure Vp H : Set G))).relIndex (pCoreOf 2 H) =
      (cfix c (conjClosure Vp H) ⊔
        (conjClosure Vp H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))).relIndex
          (conjClosure Vp H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQdef
  set U := conjClosure Vp H with hUdef
  set QC := Q ⊓ Subgroup.centralizer (U : Set G) with hQCdef
  set Z := U ⊓ Subgroup.centralizer (Q : Set G) with hZdef
  set A' := cfix c Q with hA'def
  set B' := cfix c U with hB'def
  have hUQ : U ≤ Q := h.conjClosure_Vp_le_pCoreOf
  have hQH : Q ≤ H := pCoreOf_le 2 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure Vp H
  have hc2 := mul_self_eq_inv_of_cube hc
  have hcinvH : c⁻¹ ∈ H := H.inv_mem hcH
  have hV₁ : IsElemAbelian 2 V₁ := isElemAbelian_mono h.elemAbelian h.V₁_le_V
  have hV₁3 : ∀ w ∈ V₁, w * w * w = w := by
    intro w hw
    have h2 := hV₁.2 w hw
    rw [sq] at h2
    rw [h2, one_mul]
  have hHQC : H ≤ Subgroup.normalizer (QC : Set G) :=
    normalizes_of_conj_mem fun k hk x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hHQ hk) x).mp hx.1,
        conj_centralizer_mem (hHU hk) hx.2⟩
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) :=
    normalizes_of_conj_mem fun k hk x hx =>
      ⟨(Subgroup.mem_normalizer_iff.mp (hHU hk) x).mp hx.1,
        conj_centralizer_mem (hHQ hk) hx.2⟩
  have hA'QC : A' ≤ Subgroup.normalizer (QC : Set G) := fun a ha =>
    hHQC (hQH (mem_cfix.1 ha).1)
  have hB'Z : B' ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    hHZ (hQH (hUQ (mem_cfix.1 hb).1))
  have hcomm : ∀ x u : G, x * u * x⁻¹ * u⁻¹ = 1 ↔ x * u = u * x := fun x u => by
    constructor
    · intro e
      calc x * u = (x * u * x⁻¹ * u⁻¹) * u * x := by group
        _ = u * x := by rw [e]; group
    · intro e
      calc x * u * x⁻¹ * u⁻¹ = (u * x) * x⁻¹ * u⁻¹ := by rw [e]
        _ = 1 := by group
  let _ : CommGroup ↥B' := commGroupOfElemAbelian (isElemAbelian_mono hU inf_le_left)
  let _ : CommGroup ↥V₁ := commGroupOfElemAbelian hV₁
  have hB : ∀ b : ↥B', b ^ 2 = 1 := fun b => Subtype.ext (by
    simpa using hU.2 b (mem_cfix.1 b.2).1)
  let β : ↥A' → ↥B' → ↥V₁ := fun a b =>
    ⟨a * b * a⁻¹ * b⁻¹, h.commutator_mem_V₁ (mem_cfix.1 a.2).1 (mem_cfix.1 b.2).1⟩
  have h1 : ∀ a₁ a₂ b, β (a₁ * a₂) b = β a₁ b * β a₂ b := fun a₁ a₂ b =>
    Subtype.ext (h.commutator_mul_left (mem_cfix.1 a₁.2).1 (mem_cfix.1 a₂.2).1
      (mem_cfix.1 b.2).1)
  have h2 : ∀ a b₁ b₂, β a (b₁ * b₂) = β a b₁ * β a b₂ := fun a b₁ b₂ =>
    Subtype.ext (h.commutator_mul_right (mem_cfix.1 a.2).1 (mem_cfix.1 b₁.2).1
      (mem_cfix.1 b₂.2).1)
  have key := card_mul_card_radical_eq hB h.card_V₁ β h1 h2
  have radA : Nat.card {a : ↥A' // ∀ b, β a b = 1} = Nat.card ↥(A' ⊓ QC) := by
    have hcent : ∀ a : ↥A', (∀ b, β a b = 1) → ∀ u ∈ U, (a : G) * u = u * a := by
      intro a ha u hu
      have haQ := (mem_cfix.1 a.2).1
      have hac : c * (a : G) * c⁻¹ = a := by rw [(mem_cfix.1 a.2).2]; group
      have hac' : c⁻¹ * (a : G) * c⁻¹⁻¹ = a := by
        calc c⁻¹ * (a : G) * c⁻¹⁻¹ = c⁻¹ * (c * (a : G) * c⁻¹) * c⁻¹⁻¹ := by rw [hac]
          _ = a := by group
      have hu1 : c * u * c⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hHU hcH) u).mp hu
      have hu2 : c⁻¹ * u * c⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hHU hcinvH) u).mp hu
      obtain ⟨f, hfdef⟩ : ∃ f : G, f = u * (c * u * c⁻¹) * (c⁻¹ * u * c⁻¹⁻¹) := ⟨_, rfl⟩
      have hfU : f ∈ U := by rw [hfdef]; exact U.mul_mem (U.mul_mem hu hu1) hu2
      have hfc : c * f = f * c := by
        have e1 : c * (c⁻¹ * u * c⁻¹⁻¹) * c⁻¹ = u := by group
        have e2 : c * (c * u * c⁻¹) * c⁻¹ = c⁻¹ * u * c⁻¹⁻¹ := by
          calc c * (c * u * c⁻¹) * c⁻¹ = (c * c) * u * (c * c)⁻¹ := by group
            _ = c⁻¹ * u * c⁻¹⁻¹ := by rw [hc2]
        have hcf : c * f * c⁻¹ = (c * u * c⁻¹) * (c⁻¹ * u * c⁻¹⁻¹) * u := by
          rw [hfdef]
          calc c * (u * (c * u * c⁻¹) * (c⁻¹ * u * c⁻¹⁻¹)) * c⁻¹ =
              (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) * (c * (c⁻¹ * u * c⁻¹⁻¹) * c⁻¹) := by
                group
            _ = (c * u * c⁻¹) * (c⁻¹ * u * c⁻¹⁻¹) * u := by rw [e1, e2]
        have hab := isElemAbelian_comm hU (U.mul_mem hu1 hu2) hu
        calc c * f = (c * f * c⁻¹) * c := by group
          _ = (c * u * c⁻¹) * (c⁻¹ * u * c⁻¹⁻¹) * u * c := by rw [hcf]
          _ = f * c := by rw [hab, hfdef]; group
      have hfB : f ∈ B' := mem_cfix.2 ⟨hfU, hfc⟩
      have hval := congrArg Subtype.val (ha ⟨f, hfB⟩)
      change (a : G) * f * (a : G)⁻¹ * f⁻¹ = 1 at hval
      have hm1 := h.commutator_mul_right haQ (U.mul_mem hu hu1) hu2
      have hm2 := h.commutator_mul_right haQ hu hu1
      rw [← hfdef, hval, hm2, commF91_conj_right h hcH haQ hu hac,
        commF91_conj_right h hcinvH haQ hu hac', hV₁3 _ (h.commutator_mem_V₁ haQ hu)] at hm1
      exact (hcomm _ _).mp hm1.symm
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), a.1.2, (mem_cfix.1 a.1.2).1,
          Subgroup.mem_centralizer_iff.mpr fun u hu => (hcent a.1 a.2 u hu).symm⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, fun b => Subtype.ext (by
          show (a.1 : G) * b * (a.1 : G)⁻¹ * (b : G)⁻¹ = 1
          exact (hcomm _ _).mpr (Subgroup.mem_centralizer_iff.mp a.2.2.2 b
            (mem_cfix.1 b.2).1).symm)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  have hQC3 : ¬ 3 ∣ Nat.card QC := by
    obtain ⟨e, he⟩ := IsPGroup.iff_card.mp ((pCoreOf_isPGroup 2 H).to_le
      (inf_le_left : QC ≤ Q))
    rw [he]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have radB : Nat.card {b : ↥B' // ∀ a, β a b = 1} = Nat.card ↥(B' ⊓ Z) := by
    have hcent : ∀ b : ↥B', (∀ a, β a b = 1) → ∀ x ∈ Q, x * (b : G) = b * x := by
      intro b hb x hx
      have hbU := (mem_cfix.1 b.2).1
      have hbc : c * (b : G) * c⁻¹ = b := by rw [(mem_cfix.1 b.2).2]; group
      have hbc' : c⁻¹ * (b : G) * c⁻¹⁻¹ = b := by
        calc c⁻¹ * (b : G) * c⁻¹⁻¹ = c⁻¹ * (c * (b : G) * c⁻¹) * c⁻¹⁻¹ := by rw [hbc]
          _ = b := by group
      have hx1 : c * x * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHQ hcH) x).mp hx
      have hx2 : c⁻¹ * x * c⁻¹⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHQ hcinvH) x).mp hx
      obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : G, a₀ = x * (c * x * c⁻¹) * (c⁻¹ * x * c⁻¹⁻¹) := ⟨_, rfl⟩
      have ha₀Q : a₀ ∈ Q := by rw [ha₀def]; exact Q.mul_mem (Q.mul_mem hx hx1) hx2
      have hpair : ∀ y ∈ Q, ∀ u ∈ U,
          (y * (c * y * c⁻¹) * (c⁻¹ * y * c⁻¹⁻¹)) * u *
              (y * (c * y * c⁻¹) * (c⁻¹ * y * c⁻¹⁻¹))⁻¹ * u⁻¹ =
            (y * u * y⁻¹ * u⁻¹) * ((c * y * c⁻¹) * u * (c * y * c⁻¹)⁻¹ * u⁻¹) *
              ((c⁻¹ * y * c⁻¹⁻¹) * u * (c⁻¹ * y * c⁻¹⁻¹)⁻¹ * u⁻¹) := by
        intro y hy u hu
        have hy1 : c * y * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHQ hcH) y).mp hy
        have hy2 : c⁻¹ * y * c⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp (hHQ hcinvH) y).mp hy
        rw [h.commutator_mul_left (Q.mul_mem hy hy1) hy2 hu, h.commutator_mul_left hy hy1 hu]
      have hcfix : a₀⁻¹ * (c * a₀ * c⁻¹) ∈ QC := by
        have hca₀ : c * a₀ * c⁻¹ = (c * x * c⁻¹) * (c⁻¹ * x * c⁻¹⁻¹) * x := by
          have e1 : c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹ = x := by group
          have e2 : c * (c * x * c⁻¹) * c⁻¹ = c⁻¹ * x * c⁻¹⁻¹ := by
            calc c * (c * x * c⁻¹) * c⁻¹ = (c * c) * x * (c * c)⁻¹ := by group
              _ = c⁻¹ * x * c⁻¹⁻¹ := by rw [hc2]
          rw [ha₀def]
          calc c * (x * (c * x * c⁻¹) * (c⁻¹ * x * c⁻¹⁻¹)) * c⁻¹ =
              (c * x * c⁻¹) * (c * (c * x * c⁻¹) * c⁻¹) * (c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹) := by
                group
            _ = (c * x * c⁻¹) * (c⁻¹ * x * c⁻¹⁻¹) * x := by rw [e1, e2]
        have hca₀Q : c * a₀ * c⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hHQ hcH) a₀).mp ha₀Q
        refine ⟨Q.mul_mem (Q.inv_mem ha₀Q) hca₀Q, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro u hu
        have hp1 := hpair x hx u hu
        have hp2 : (c * a₀ * c⁻¹) * u * (c * a₀ * c⁻¹)⁻¹ * u⁻¹ =
            ((c * x * c⁻¹) * u * (c * x * c⁻¹)⁻¹ * u⁻¹) *
              ((c⁻¹ * x * c⁻¹⁻¹) * u * (c⁻¹ * x * c⁻¹⁻¹)⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹) := by
          rw [hca₀, h.commutator_mul_left (Q.mul_mem hx1 hx2) hx hu,
            h.commutator_mul_left hx1 hx2 hu]
        have w1 := h.commutator_mem_V₁ hx hu
        have w2 := h.commutator_mem_V₁ hx1 hu
        have w3 := h.commutator_mem_V₁ hx2 hu
        have hc12 := isElemAbelian_comm hV₁ w1 (V₁.mul_mem w2 w3)
        have heq : (c * a₀ * c⁻¹) * u * (c * a₀ * c⁻¹)⁻¹ * u⁻¹ = a₀ * u * a₀⁻¹ * u⁻¹ := by
          rw [hp2, ha₀def, hp1, mul_assoc (x * u * x⁻¹ * u⁻¹), hc12]
        have hm := h.commutator_mul_left (Q.inv_mem ha₀Q) hca₀Q hu
        have hinv : a₀⁻¹ * u * a₀⁻¹⁻¹ * u⁻¹ = (a₀ * u * a₀⁻¹ * u⁻¹)⁻¹ := by
          have hm' := h.commutator_mul_left (Q.inv_mem ha₀Q) ha₀Q hu
          rw [inv_mul_cancel] at hm'
          have hone : (1 : G) * u * (1 : G)⁻¹ * u⁻¹ = 1 := by group
          rw [hone] at hm'
          exact eq_inv_of_mul_eq_one_left hm'.symm
        rw [heq, hinv, inv_mul_cancel] at hm
        exact ((hcomm _ _).mp hm).symm
      have hcQC : ∀ n ∈ QC, c * n * c⁻¹ ∈ QC := fun n hn =>
        (Subgroup.mem_normalizer_iff.mp (hHQC hcH) n).mp hn
      obtain ⟨n, hn, hfix⟩ := exists_comm_mul_of_conj_mem hc hQC3 hcQC hcfix
      have ha'Q : a₀ * n ∈ Q := Q.mul_mem ha₀Q hn.1
      have ha'c : c * (a₀ * n) = (a₀ * n) * c := by
        calc c * (a₀ * n) = c * (a₀ * n) * c⁻¹ * c := by group
          _ = (a₀ * n) * c := by rw [hfix]
      have hval := congrArg Subtype.val (hb ⟨a₀ * n, mem_cfix.2 ⟨ha'Q, ha'c⟩⟩)
      change (a₀ * n) * (b : G) * (a₀ * n)⁻¹ * (b : G)⁻¹ = 1 at hval
      have hnb : n * (b : G) * n⁻¹ * (b : G)⁻¹ = 1 :=
        (hcomm _ _).mpr (Subgroup.mem_centralizer_iff.mp hn.2 b hbU).symm
      rw [h.commutator_mul_left ha₀Q hn.1 hbU, hnb, mul_one, ha₀def, hpair x hx b hbU,
        commF91_conj_left h hcH hx hbU hbc, commF91_conj_left h hcinvH hx hbU hbc',
        hV₁3 _ (h.commutator_mem_V₁ hx hbU)] at hval
      exact (hcomm _ _).mp hval
    refine Nat.card_congr
      { toFun := fun b => ⟨(b.1 : G), b.1.2, (mem_cfix.1 b.1.2).1,
          Subgroup.mem_centralizer_iff.mpr fun x hx => hcent b.1 b.2 x hx⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, fun a => Subtype.ext (by
          show (a : G) * b.1 * (a : G)⁻¹ * (b.1 : G)⁻¹ = 1
          exact (hcomm _ _).mpr (Subgroup.mem_centralizer_iff.mp b.2.2.2 a
            (mem_cfix.1 a.2).1))⟩
        left_inv := fun b => rfl
        right_inv := fun b => rfl }
  rw [radA, radB] at key
  have e1 := card_sup_mul_card_inf' hA'QC
  have e2 := card_sup_mul_card_inf' hB'Z
  have e3 : Nat.card Q * Nat.card Z = Nat.card U * Nat.card QC := h.F97_card_mul hU
  have r1 := Subgroup.relIndex_mul_card (A' ⊔ QC) Q
  have r2 := Subgroup.relIndex_mul_card (B' ⊔ Z) U
  have hA'Q : A' ≤ Q := inf_le_left
  have hQCQ : QC ≤ Q := inf_le_left
  have hB'U : B' ≤ U := inf_le_left
  have hZU : Z ≤ U := inf_le_left
  rw [inf_eq_left.2 (sup_le hA'Q hQCQ)] at r1
  rw [inf_eq_left.2 (sup_le hB'U hZU)] at r2
  have hP : 0 < Nat.card ↥(A' ⊔ QC) := Nat.card_pos
  have ha : 0 < Nat.card ↥(A' ⊓ QC) := Nat.card_pos
  have hR : 0 < Nat.card ↥(B' ⊔ Z) := Nat.card_pos
  have hb : 0 < Nat.card ↥(B' ⊓ Z) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hP ha) hR) hb) ?_
  calc (A' ⊔ QC).relIndex Q *
        (Nat.card ↥(A' ⊔ QC) * Nat.card ↥(A' ⊓ QC) * Nat.card ↥(B' ⊔ Z) * Nat.card ↥(B' ⊓ Z))
      = ((A' ⊔ QC).relIndex Q * Nat.card ↥(A' ⊔ QC)) * Nat.card ↥(A' ⊓ QC) *
          (Nat.card ↥(B' ⊔ Z) * Nat.card ↥(B' ⊓ Z)) := by ring
    _ = Nat.card Q * Nat.card ↥(A' ⊓ QC) * (Nat.card B' * Nat.card Z) := by rw [r1, e2]
    _ = (Nat.card Q * Nat.card Z) * (Nat.card B' * Nat.card ↥(A' ⊓ QC)) := by ring
    _ = (Nat.card U * Nat.card QC) * (Nat.card A' * Nat.card ↥(B' ⊓ Z)) := by rw [e3, key]
    _ = ((B' ⊔ Z).relIndex U * Nat.card ↥(B' ⊔ Z)) * (Nat.card A' * Nat.card QC) *
          Nat.card ↥(B' ⊓ Z) := by rw [r2]; ring
    _ = ((B' ⊔ Z).relIndex U * Nat.card ↥(B' ⊔ Z)) *
          (Nat.card ↥(A' ⊔ QC) * Nat.card ↥(A' ⊓ QC)) * Nat.card ↥(B' ⊓ Z) := by rw [e1]
    _ = (B' ⊔ Z).relIndex U *
        (Nat.card ↥(A' ⊔ QC) * Nat.card ↥(A' ⊓ QC) * Nat.card ↥(B' ⊔ Z) *
          Nat.card ↥(B' ⊓ Z)) := by ring

end F97

end CFSG.Quasithin.H13.A6
