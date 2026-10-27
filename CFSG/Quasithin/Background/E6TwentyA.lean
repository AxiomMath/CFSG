module

public import CFSG.Quasithin.Background.E6TwentyTwo
public import CFSG.SignalizerFunctorTheorem.SolvableTheorem

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique

section Tools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_sup_eq (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (show (A : Set G) ⊆ (A ⊔ B : Subgroup G) from
      fun _ hx => Subgroup.mem_sup_left hx))
      (Subgroup.centralizer_le (show (B : Set G) ⊆ (A ⊔ B : Subgroup G) from
      fun _ hx => Subgroup.mem_sup_right hx))
  · rintro x ⟨hA, hB⟩
    have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hA a ha)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hB b hb)
    exact Subgroup.mem_centralizer_iff.2 fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

omit [Finite G] in
theorem centralizer_zpowers_eq (e : G) :
    Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) =
      Subgroup.centralizer ({e} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite G] in
theorem exists_compl_of_le {V U₀ : Subgroup G} (hV : IsElemAbelian 2 V) (hU₀V : U₀ ≤ V) :
    ∃ E : Subgroup G, E ≤ V ∧ U₀ ⊓ E = ⊥ ∧ U₀ ⊔ E = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := hV.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hV.2 x x.2) }
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 ↥V (U₀.subgroupOf V)
  have hU₀ : (U₀.subgroupOf V).map V.subtype = U₀ := Subgroup.map_subgroupOf_eq_of_le hU₀V
  refine ⟨C.map V.subtype, Subgroup.map_subtype_le C, ?_, ?_⟩
  · rw [← hU₀, ← Subgroup.map_inf_eq _ _ V.subtype V.subtype_injective,
      disjoint_iff.1 hC.disjoint, Subgroup.map_bot]
  · rw [← hU₀, ← Subgroup.map_sup, codisjoint_iff.1 hC.codisjoint, Subgroup.map_top,
      Subgroup.range_subtype]

theorem exists_hyperplane_not_mem {V M' : Subgroup G} (hV : IsElemAbelian 2 V) (hM'V : M' ≤ V)
    {c : G} (hcV : c ∈ V) (hcM : c ∉ M') :
    ∃ N : Subgroup G, M' ≤ N ∧ N ≤ V ∧ c ∉ N ∧ E3.mQuot V N = 1 := by
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV ha hb
  have hZV : Subgroup.zpowers c ≤ V := Subgroup.zpowers_le.2 hcV
  obtain ⟨C, hCV, hC1, hC2⟩ := exists_compl_of_le hV (sup_le hM'V hZV)
  set N := M' ⊔ C with hNdef
  have hNV : N ≤ V := sup_le hM'V hCV
  have hCN : C ≤ Subgroup.normalizer (M' : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun m hm =>
      hVc _ (hM'V hm) _ (hCV hk))
  have hcN : c ∉ N := by
    intro hc
    rw [← SetLike.mem_coe, hNdef, Subgroup.coe_mul_of_right_le_normalizer_left M' C hCN] at hc
    obtain ⟨m, hm, k, hk, hmk⟩ := hc
    simp only at hmk
    have hk' : k = m⁻¹ * c := by rw [← hmk]; group
    have hkMc : k ∈ M' ⊔ Subgroup.zpowers c := by
      rw [hk']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (M'.inv_mem hm))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    have hk1 : k = 1 := by
      have : k ∈ (M' ⊔ Subgroup.zpowers c) ⊓ C := ⟨hkMc, hk⟩
      rw [hC1] at this
      exact this
    apply hcM
    have : c = m := by rw [← hmk, hk1, mul_one]
    rw [this]
    exact hm
  have hsup : N ⊔ Subgroup.zpowers c = V := by
    refine le_antisymm (sup_le hNV hZV) ?_
    rw [← hC2]
    refine sup_le (sup_le (fun x hx => Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
      (fun x hx => Subgroup.mem_sup_right hx)) (fun x hx => Subgroup.mem_sup_left
        (Subgroup.mem_sup_right hx))
  have hinf : N ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxN, hxc⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxc
    have hc2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq]; exact hV.2 c hcV
    rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
    · rw [zpow_mul, hc2, one_zpow]
      exact Subgroup.one_mem _
    · exfalso
      apply hcN
      have hc' : c ^ (2 * n + 1) = c := by
        rw [zpow_add_one, zpow_mul, hc2, one_zpow, one_mul]
      rw [hc'] at hxN
      exact hxN
  have hcomm : ∀ a ∈ N, ∀ b ∈ Subgroup.zpowers c, a * b = b * a := fun a ha b hb =>
    hVc _ (hNV ha) _ (hZV hb)
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hsup, hinf, Subgroup.card_bot, mul_one] at hcard
  have hc1 : c ≠ 1 := fun h1 => hcM (h1 ▸ M'.one_mem)
  have hcz : Nat.card (Subgroup.zpowers c) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hV.2 c hcV) hc1
  refine ⟨N, le_sup_left, hNV, hcN, ?_⟩
  have h1 := Subgroup.relIndex_mul_card N V
  rw [inf_eq_left.2 hNV, hcard, hcz] at h1
  have h2 : N.relIndex V = 2 := Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (mul_comm _ _))
  unfold E3.mQuot
  rw [h2]
  exact padicValNat_self (p := 2)

end Tools

@[expose] noncomputable def e620Theta {G : Type} [Group G] (U₀ : Subgroup G) (e : G) :
    Subgroup G :=
  oddCoreIn (Subgroup.centralizer ((U₀ ⊔ Subgroup.zpowers e : Subgroup G) : Set G))

section Functor

variable {G : Type} [Group G] [Finite G] {T M V U₀ E : Subgroup G}

omit [Finite G] in
theorem mem_sup_zpowers_iff {V B : Subgroup G} (hV : IsElemAbelian 2 V) (hBV : B ≤ V)
    {x : G} (hxV : x ∈ V) {y : G} (hy : y ∈ B ⊔ Subgroup.zpowers x) :
    ∃ b ∈ B, y = b ∨ y = b * x := by
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (B : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun m hm =>
      B2F.isElemAbelian_comm hV (hBV hm) ((Subgroup.zpowers_le.2 hxV) hk))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left B _ hxN] at hy
  obtain ⟨b, hb, k, hk, rfl⟩ := hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq]; exact hV.2 x hxV
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · refine ⟨b, hb, Or.inl ?_⟩
    show b * x ^ (2 * m) = b
    rw [zpow_mul, hx2, one_zpow, mul_one]
  · refine ⟨b, hb, Or.inr ?_⟩
    show b * x ^ (2 * m + 1) = b * x
    rw [zpow_add_one, zpow_mul, hx2, one_zpow, one_mul]

theorem mQuot_sup_zpowers {V B : Subgroup G} (hV : IsElemAbelian 2 V) (hBV : B ≤ V)
    {x : G} (hxV : x ∈ V) (hxB : x ∉ B) : E3.mQuot (B ⊔ Subgroup.zpowers x) B = 1 := by
  have hZV : Subgroup.zpowers x ≤ V := Subgroup.zpowers_le.2 hxV
  have hcomm : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV (hBV ha) (hZV hb)
  have hinf : B ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyB, hyx⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyx
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq]; exact hV.2 x hxV
    rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, hx2, one_zpow]
      exact Subgroup.one_mem _
    · exfalso
      apply hxB
      have hx' : x ^ (2 * m + 1) = x := by
        rw [zpow_add_one, zpow_mul, hx2, one_zpow, one_mul]
      rw [hx'] at hyB
      exact hyB
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one] at hcard
  have hx1 : x ≠ 1 := fun h1 => hxB (h1 ▸ B.one_mem)
  have hcz : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hV.2 x hxV) hx1
  have h1 := Subgroup.relIndex_mul_card B (B ⊔ Subgroup.zpowers x)
  rw [inf_eq_left.2 le_sup_left, hcard, hcz] at h1
  have h2 : B.relIndex (B ⊔ Subgroup.zpowers x) = 2 :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (mul_comm _ _))
  unfold E3.mQuot
  rw [h2]
  exact padicValNat_self (p := 2)

theorem mQuot_sup_zpowers_add {V B : Subgroup G} (hV : IsElemAbelian 2 V) (hBV : B ≤ V)
    {x : G} (hxV : x ∈ V) (hxB : x ∉ B) :
    E3.mQuot V (B ⊔ Subgroup.zpowers x) + 1 = E3.mQuot V B := by
  have h := E3.mQuot_add (V := V) (le_sup_left : B ≤ B ⊔ Subgroup.zpowers x)
    (sup_le hBV (Subgroup.zpowers_le.2 hxV))
  rw [mQuot_sup_zpowers hV hBV hxV hxB] at h
  omega

theorem eq_of_le_of_mQuot_eq {V B D : Subgroup G} (hV : IsPGroup 2 V) (hDB : D ≤ B)
    (hBV : B ≤ V) (h : E3.mQuot V B = E3.mQuot V D) : D = B := by
  have h1 := E3.mQuot_add hDB hBV
  have h0 : E3.mQuot B D = 0 := by omega
  exact (E3.mQuot_eq_zero_iff (hV.to_le hBV) hDB).1 h0

theorem oddCoreIn_le_of_e619 (h619 : E619Stmt) (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    (h15 : HypE615 hV M) {B D : Subgroup G} (hBV : B ≤ V) (hB1 : E3.mQuot V B = 1)
    (hDB : D ≤ B) (hD2 : E3.mQuot V D = 2) :
    oddCoreIn (Subgroup.centralizer (B : Set G)) ≤
      oddCoreIn (Subgroup.centralizer (D : Set G)) := by
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  obtain ⟨c, hcB, hcD⟩ : ∃ c ∈ B, c ∉ D := by
    by_contra hall
    push Not at hall
    have : D = B := le_antisymm hDB hall
    rw [this, hB1] at hD2
    exact absurd hD2 (by norm_num)
  obtain ⟨W₀, hDW₀, hW₀V, hcW₀, hW₀1⟩ :=
    exists_hyperplane_not_mem hV (hDB.trans hBV) (hBV hcB) hcD
  have hle : D ≤ B ⊓ W₀ := le_inf hDB hDW₀
  have hm : E3.mQuot V (B ⊓ W₀) = 2 := by
    have h1 := E3.mQuot_mono (V := V) hle
    have h2 := mQuot_inf_le (U := B) (U' := W₀) hV2
    rcases Nat.lt_or_ge (E3.mQuot V (B ⊓ W₀)) 2 with hlt | hge
    · exfalso
      have hW : E3.mQuot V (B ⊓ W₀) = 1 ∨ E3.mQuot V (B ⊓ W₀) = 0 := by omega
      have heq : B ⊓ W₀ = W₀ := by
        have h3 := E3.mQuot_add (V := V) (inf_le_right : B ⊓ W₀ ≤ W₀) hW₀V
        have hbot : E3.mQuot V (B ⊓ W₀) ≠ 0 := by
          intro h0
          have := (E3.mQuot_eq_zero_iff hV2 (inf_le_right.trans hW₀V)).1 h0
          rw [← this] at hW₀1
          have h4 := E3.mQuot_mono (V := V) (inf_le_right : B ⊓ W₀ ≤ W₀)
          rw [← this, E3.mQuot_self] at h4
          omega
        have h5 : E3.mQuot W₀ (B ⊓ W₀) = 0 := by omega
        exact (E3.mQuot_eq_zero_iff (hV2.to_le hW₀V) inf_le_right).1 h5
      apply hcW₀
      have hW₀B : W₀ ≤ B := heq ▸ inf_le_left
      have hBW₀ : B = W₀ := (eq_of_le_of_mQuot_eq hV2 hW₀B hBV (by rw [hB1, hW₀1])).symm
      exact hBW₀ ▸ hcB
    · omega
  have hD : D = B ⊓ W₀ := eq_of_le_of_mQuot_eq hV2 hle (inf_le_left.trans hBV) (by rw [hm, hD2])
  rw [hD]
  exact h619 _ T M V B W₀ hV h h15 hBV hB1 hW₀V hW₀1

omit [Finite G] in
theorem e620Theta_le (hUV : U₀ ≤ V) (hV : IsElemAbelian 2 V) {e : G} (heV : e ∈ V) :
    e620Theta U₀ e ≤ Subgroup.centralizer ((U₀ ⊔ Subgroup.zpowers e : Subgroup G) : Set G) ∧
      V ≤ Subgroup.normalizer (e620Theta U₀ e : Set G) := by
  refine ⟨E3.oddCoreIn_le _, le_trans (fun v hv => ?_) (E3.le_normalizer_oddCoreIn _)⟩
  exact Subgroup.mem_centralizer_iff.2 fun w hw =>
    B2F.isElemAbelian_comm hV ((sup_le hUV (Subgroup.zpowers_le.2 heV)) hw) hv

theorem e620Theta_balance (h619 : E619Stmt) (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    (h15 : HypE615 hV M) (hU₀V : U₀ ≤ V) (hU₀3 : E3.mQuot V U₀ = 3) (hEV : E ≤ V)
    (hE1 : U₀ ⊓ E = ⊥) {e f : G} (heE : e ∈ E) (he1 : e ≠ 1) (hfE : f ∈ E) (hf1 : f ≠ 1) :
    e620Theta U₀ e ⊓ Subgroup.centralizer ({f} : Set G) ≤ e620Theta U₀ f := by
  by_cases hef : e = f
  · subst hef
    exact inf_le_left
  have heV := hEV heE
  have hfV := hEV hfE
  have hnotU : ∀ x ∈ E, x ≠ 1 → x ∉ U₀ := fun x hx hx1 hxU => by
    have : x ∈ U₀ ⊓ E := ⟨hxU, hx⟩
    rw [hE1] at this
    exact hx1 this
  have hnot2 : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → x ≠ y →
      y ∉ U₀ ⊔ Subgroup.zpowers x := by
    intro x hx y hy hx1 hy1 hxy hmem
    obtain ⟨b, hb, hyb | hyb⟩ := mem_sup_zpowers_iff hV hU₀V (hEV hx) hmem
    · exact hnotU y hy hy1 (hyb ▸ hb)
    · have hbE : b ∈ E := by
        have : b = y * x⁻¹ := by rw [hyb]; group
        rw [this]
        exact E.mul_mem hy (E.inv_mem hx)
      have hb1 : b = 1 := by
        have : b ∈ U₀ ⊓ E := ⟨hb, hbE⟩
        rw [hE1] at this
        exact this
      rw [hb1, one_mul] at hyb
      exact hxy hyb.symm
  set W₁ := U₀ ⊔ Subgroup.zpowers e ⊔ Subgroup.zpowers f with hW₁def
  have hUe : E3.mQuot V (U₀ ⊔ Subgroup.zpowers e) = 2 := by
    have := mQuot_sup_zpowers_add hV hU₀V heV (hnotU e heE he1)
    omega
  have hUf : E3.mQuot V (U₀ ⊔ Subgroup.zpowers f) = 2 := by
    have := mQuot_sup_zpowers_add hV hU₀V hfV (hnotU f hfE hf1)
    omega
  have hW₁V : W₁ ≤ V := sup_le (sup_le hU₀V (Subgroup.zpowers_le.2 heV)) (Subgroup.zpowers_le.2 hfV)
  have hW₁1 : E3.mQuot V W₁ = 1 := by
    have := mQuot_sup_zpowers_add hV (sup_le hU₀V (Subgroup.zpowers_le.2 heV)) hfV
      (hnot2 e heE f hfE he1 hf1 hef)
    rw [hW₁def]
    omega
  have hUfW : U₀ ⊔ Subgroup.zpowers f ≤ W₁ :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hC : Subgroup.centralizer (W₁ : Set G) =
      Subgroup.centralizer ((U₀ ⊔ Subgroup.zpowers e : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ({f} : Set G) := by
    rw [hW₁def, centralizer_sup_eq, centralizer_zpowers_eq]
  have hstep1 : e620Theta U₀ e ⊓ Subgroup.centralizer ({f} : Set G) ≤
      oddCoreIn (Subgroup.centralizer (W₁ : Set G)) := by
    refine le_oddCoreIn_of_odd ?_ ?_ ?_
    · rw [hC]
      exact inf_le_inf_right _ (E3.oddCoreIn_le _)
    · refine B2F.le_normalizer_inf ?_ ?_
      · rw [hC]
        exact inf_le_left.trans (E3.le_normalizer_oddCoreIn _)
      · rw [hC]
        exact inf_le_right.trans Subgroup.le_normalizer
    · exact Odd.of_dvd_nat (E3.odd_card_oddCoreIn' _) (Subgroup.card_dvd_of_le inf_le_left)
  exact hstep1.trans (oddCoreIn_le_of_e619 h619 hV h h15 hW₁V hW₁1 hUfW hUf)


theorem e620_functor (h619 : E619Stmt) (hV : IsElemAbelian 2 V) (h : HypE61 T M V)
    (h15 : HypE615 hV M) (hU₀V : U₀ ≤ V) (hU₀3 : E3.mQuot V U₀ = 3) :
    ∃ X : Subgroup G, X ≤ Subgroup.centralizer (U₀ : Set G) ∧
      V ≤ Subgroup.normalizer (X : Set G) ∧ Odd (Nat.card X) ∧
      (∀ B : Subgroup G, U₀ ≤ B → B ≤ V → B ≠ U₀ →
        X ⊓ Subgroup.centralizer (B : Set G) = oddCoreIn (Subgroup.centralizer (B : Set G))) ∧
      ∀ z ∈ V, z ∉ U₀ →
        oddCoreIn (Subgroup.centralizer ((U₀ ⊔ Subgroup.zpowers z : Subgroup G) : Set G)) = ⊥ →
        ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm hV ha hb
  obtain ⟨E, hEV, hE1, hE2⟩ := exists_compl_of_le hV hU₀V
  have hcard : Nat.card E = 2 ^ 3 := by
    have h1 := B2F.card_sup_mul_card_inf_of_commute (A := U₀) (B := E)
      (fun a ha b hb => hVc _ (hU₀V ha) _ (hEV hb))
    rw [hE2, hE1, Subgroup.card_bot, mul_one] at h1
    have h2 := Subgroup.relIndex_mul_card U₀ V
    rw [inf_eq_left.2 hU₀V, E3.relIndex_eq_two_pow hV2, hU₀3] at h2
    have hpos : 0 < Nat.card U₀ := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (h2.symm.trans (mul_comm _ _)))
  have hnotU : ∀ x ∈ E, x ≠ 1 → x ∉ U₀ := fun x hx hx1 hxU => by
    have : x ∈ U₀ ⊓ E := ⟨hxU, hx⟩
    rw [hE1] at this
    exact hx1 this
  have hEab : IsMulCommutative ↥E :=
    ⟨⟨fun a b => Subtype.ext (hVc _ (hEV a.2) _ (hEV b.2))⟩⟩
  have hexp : ∀ a ∈ E, a ^ 2 = 1 := fun a ha => hV.2 a (hEV ha)
  have hθmap : ∀ a ∈ V, ∀ x ∈ V,
      (e620Theta U₀ a).map (MulAut.conj x).toMonoidHom = e620Theta U₀ a := by
    intro a ha x hx
    have hxN : x⁻¹ ∈ Subgroup.normalizer (e620Theta U₀ a : Set G) :=
      (e620Theta_le hU₀V hV ha).2 (V.inv_mem hx)
    have h1 := (BenderBranch.conjugate_eq_iff_mem_normalizer (H := e620Theta U₀ a)).2 hxN
    unfold CFSG.conjugate at h1
    rwa [inv_inv] at h1
  have hθ : IsSolvableSignalizerFunctor 2 E (e620Theta U₀) :=
    { le_centralizer := fun a ha _ => (e620Theta_le hU₀V hV (hEV ha)).1.trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))))
      coprime := fun a _ _ => Nat.coprime_two_left.2 (E3.odd_card_oddCoreIn' _)
      invariant := fun a ha _ x hx => hθmap a (hEV ha) x (hEV hx)
      balance := fun a ha ha1 b hb hb1 =>
        e620Theta_balance h619 hV h h15 hU₀V hU₀3 hEV hE1 ha ha1 hb hb1
      solvable := fun a _ _ => CFSG.FeitThompson.isSolvable_of_odd_natCard _ (E3.odd_card_oddCoreIn' _) }
  obtain ⟨hcop, -, hcomp⟩ := CFSG.SignalizerFunctorTheorem.glauberman_solvable_signalizer_functor
    G 2 Nat.prime_two E hEab hexp (by rw [hcard]) (e620Theta U₀) hθ
  set X : Subgroup G := ⨆ (a : G) (_ : a ∈ E) (_ : a ≠ 1), e620Theta U₀ a with hXdef
  have hθX : ∀ a ∈ E, a ≠ 1 → e620Theta U₀ a ≤ X := fun a ha ha1 =>
    le_iSup_of_le a (le_iSup_of_le ha (le_iSup_of_le ha1 le_rfl))
  have hXU : X ≤ Subgroup.centralizer (U₀ : Set G) :=
    iSup_le fun a => iSup_le fun ha => iSup_le fun _ =>
      (e620Theta_le hU₀V hV (hEV ha)).1.trans (Subgroup.centralizer_le
        (show (U₀ : Set G) ⊆ (U₀ ⊔ Subgroup.zpowers a : Subgroup G) from
          fun _ hx => Subgroup.mem_sup_left hx))
  have hXmap : ∀ v ∈ V, X ≤ X.comap (MulAut.conj v).toMonoidHom := by
    intro v hv
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    intro y hy
    rw [Subgroup.mem_comap]
    have h1 : (MulAut.conj v).toMonoidHom y ∈ (e620Theta U₀ a).map (MulAut.conj v).toMonoidHom :=
      ⟨y, hy, rfl⟩
    rw [hθmap a (hEV ha) v hv] at h1
    exact hθX a ha ha1 h1
  have hVN : V ≤ Subgroup.normalizer (X : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hXmap v hv hx
    · intro hx
      have h1 := hXmap v⁻¹ (V.inv_mem hv) hx
      rw [Subgroup.mem_comap] at h1
      have h2 : (MulAut.conj v⁻¹).toMonoidHom (v * x * v⁻¹) = x := by
        simp [mul_assoc]
      rwa [h2] at h1
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.1 hcop
  have hEN : E ≤ Subgroup.normalizer (U₀ : Set G) := fun k hk =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun m hm =>
      hVc _ (hU₀V hm) _ (hEV hk))
  have hdec : ∀ b ∈ V, b ∉ U₀ → ∃ u ∈ U₀, ∃ a ∈ E, a ≠ 1 ∧ u * a = b := by
    intro b hbV hbU
    rw [← hE2, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left U₀ E hEN] at hbV
    obtain ⟨u, hu, a, ha, hua⟩ := hbV
    simp only at hua
    refine ⟨u, hu, a, ha, fun h1 => hbU ?_, hua⟩
    rw [← hua, h1, mul_one]
    exact hu
  refine ⟨X, hXU, hVN, hXodd, ?_, ?_⟩
  · intro B hU₀B hBV hBne
    obtain ⟨b, hbB, hbU⟩ : ∃ b ∈ B, b ∉ U₀ := by
      by_contra hall
      push Not at hall
      exact hBne (le_antisymm hall hU₀B)
    obtain ⟨u, hu, a, ha, ha1, hua⟩ := hdec b (hBV hbB) hbU
    have haB : a ∈ B := by
      have : a = u⁻¹ * b := by rw [← hua]; group
      rw [this]
      exact B.mul_mem (B.inv_mem (hU₀B hu)) hbB
    have hUa : U₀ ⊔ Subgroup.zpowers a ≤ B := sup_le hU₀B (Subgroup.zpowers_le.2 haB)
    have hUa2 : E3.mQuot V (U₀ ⊔ Subgroup.zpowers a) = 2 := by
      have := mQuot_sup_zpowers_add hV hU₀V (hEV ha) (hnotU a ha ha1)
      omega
    have hθa : e620Theta U₀ a = X ⊓ Subgroup.centralizer {a} := hcomp a ha ha1
    apply le_antisymm
    · have h1 : X ⊓ Subgroup.centralizer (B : Set G) ≤
          e620Theta U₀ a ⊓ Subgroup.centralizer (B : Set G) := by
        rw [hθa]
        exact le_inf (le_inf inf_le_left (inf_le_right.trans
          (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haB)))) inf_le_right
      refine h1.trans (le_oddCoreIn_of_odd inf_le_right ?_ ?_)
      · exact B2F.le_normalizer_inf
          ((Subgroup.centralizer_le hUa).trans (E3.le_normalizer_oddCoreIn _))
          Subgroup.le_normalizer
      · exact Odd.of_dvd_nat (E3.odd_card_oddCoreIn' _) (Subgroup.card_dvd_of_le inf_le_left)
    · refine le_inf (le_trans ?_ (hθX a ha ha1)) (E3.oddCoreIn_le _)
      have hBm : E3.mQuot V B ≤ 2 := hUa2 ▸ E3.mQuot_mono hUa
      rcases (show E3.mQuot V B = 0 ∨ E3.mQuot V B = 1 ∨ E3.mQuot V B = 2 by omega) with
        h0 | h1 | h2
      · have hBV' : B = V := (E3.mQuot_eq_zero_iff hV2 hBV).1 h0
        rw [hBV', oddCoreIn_centralizer_V h]
        exact bot_le
      · exact oddCoreIn_le_of_e619 h619 hV h h15 hBV h1 hUa hUa2
      · have hB' : U₀ ⊔ Subgroup.zpowers a = B :=
          eq_of_le_of_mQuot_eq hV2 hUa hBV (by rw [h2, hUa2])
        rw [← hB']
        exact le_rfl
  · intro z hzV hzU hOz a₁ ha₁ b₁ hb₁
    obtain ⟨u, hu, a, ha, ha1, hua⟩ := hdec z hzV hzU
    have hz2 : z * z = 1 := by rw [← sq]; exact hV.2 z hzV
    have hUaz : U₀ ⊔ Subgroup.zpowers a = U₀ ⊔ Subgroup.zpowers z := by
      apply le_antisymm
      · refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
        have : a = u⁻¹ * z := by rw [← hua]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (U₀.inv_mem hu))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
      · refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
        rw [← hua]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
    have hfix : X ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
      rw [eq_bot_iff]
      rintro w ⟨hwX, hwz⟩
      have hwu : u * w = w * u := Subgroup.mem_centralizer_iff.1 (hXU hwX) u hu
      have hwz' : z * w = w * z := Subgroup.mem_centralizer_iff.1 hwz z (Set.mem_singleton z)
      have hwa : w ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have e1 : u * (a * w) = u * (w * a) := by
          calc u * (a * w) = (u * a) * w := by group
            _ = z * w := by rw [hua]
            _ = w * z := hwz'
            _ = w * (u * a) := by rw [hua]
            _ = (w * u) * a := by group
            _ = (u * w) * a := by rw [hwu]
            _ = u * (w * a) := by group
        exact (mul_left_cancel e1).symm
      have hw : w ∈ e620Theta U₀ a := by
        rw [hcomp a ha ha1]
        exact ⟨hwX, hwa⟩
      unfold e620Theta at hw
      rw [hUaz, hOz] at hw
      exact hw
    have hzN : ∀ w : ↥X, z * (w : G) * z⁻¹ ∈ X := fun w =>
      (Subgroup.mem_normalizer_iff.1 (hVN hzV) w).1 w.2
    let φ : ↥X →* ↥X :=
      { toFun := fun w => ⟨z * (w : G) * z⁻¹, hzN w⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
    have hφ : ∀ w : ↥X, (φ w : G) = z * (w : G) * z⁻¹ := fun _ => rfl
    have hfpf : MonoidHom.FixedPointFree φ := by
      intro w hw
      have hw' : z * (w : G) * z⁻¹ = w := by rw [← hφ, hw]
      have hmem : (w : G) ∈ X ⊓ Subgroup.centralizer ({z} : Set G) := by
        refine ⟨w.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        calc (w : G) * z = (z * (w : G) * z⁻¹) * z := by rw [hw']
          _ = z * w := by group
      rw [hfix] at hmem
      exact Subtype.ext hmem
    have hinv : Function.Involutive φ := by
      intro w
      apply Subtype.ext
      rw [hφ, hφ]
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
      rw [hzi]
      calc z * (z * (w : G) * z) * z = (z * z) * w * (z * z) := by group
        _ = w := by rw [hz2, one_mul, mul_one]
    have hc := hfpf.commute_all_of_involutive hinv ⟨a₁, ha₁⟩ ⟨b₁, hb₁⟩
    exact congrArg Subtype.val hc.eq

end Functor

end E6

end CFSG.Quasithin
