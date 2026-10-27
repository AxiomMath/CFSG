module

public import CFSG.RankThree.PartTwo.Sec21.Item226Pre

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)
open CFSG.Assembly (IsElemAbelian)

section SL2

variable {F : Type} [Field F]

@[expose] noncomputable def sl2UnipHom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun b := ⟨!![1, Multiplicative.toAdd b; 0, 1], by simp [det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    simp only [toAdd_one]
    exact Matrix.one_fin_two.symm
  map_mul' a b := by
    apply Subtype.ext
    change !![(1 : F), Multiplicative.toAdd (a * b); 0, 1] =
      !![(1 : F), Multiplicative.toAdd a; 0, 1] * !![(1 : F), Multiplicative.toAdd b; 0, 1]
    rw [toAdd_mul, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]

@[expose] noncomputable def sl2DiagHom : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun u := ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by simp [det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    change !![((1 : Fˣ) : F), 0; 0, (((1 : Fˣ)⁻¹ : Fˣ) : F)] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![((a * b : Fˣ) : F), 0; 0, (((a * b)⁻¹ : Fˣ) : F)] =
      !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] * !![(b : F), 0; 0, ((b⁻¹ : Fˣ) : F)]
    rw [mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem coe_sl2UnipHom (b : Multiplicative F) :
    ((sl2UnipHom b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, Multiplicative.toAdd b; 0, 1] := rfl

theorem coe_sl2DiagHom (u : Fˣ) :
    ((sl2DiagHom u : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)] := rfl

theorem sl2DiagHom_injective : Function.Injective (sl2DiagHom (F := F)) := by
  intro a b h
  have h1 := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [coe_sl2DiagHom] at h1
  exact Units.ext h1

@[expose] noncomputable def sl2Unip : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  (sl2UnipHom (F := F)).range

theorem sl2Diag_conj_unip (v : Fˣ) (b : F) :
    sl2DiagHom v * sl2UnipHom (Multiplicative.ofAdd b) * (sl2DiagHom v)⁻¹ =
      sl2UnipHom (Multiplicative.ofAdd ((v : F) * (v : F) * b)) := by
  rw [← map_inv]
  apply Subtype.ext
  change ((sl2DiagHom v : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((sl2UnipHom (Multiplicative.ofAdd b) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) *
      ((sl2DiagHom v⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    ((sl2UnipHom (Multiplicative.ofAdd ((v : F) * (v : F) * b)) : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)
  rw [coe_sl2DiagHom, coe_sl2DiagHom, coe_sl2UnipHom, coe_sl2UnipHom, toAdd_ofAdd, toAdd_ofAdd,
    inv_inv, mul_fin_two, mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm, mul_left_comm]

theorem sl2DiagHom_mem_normalizer (u : Fˣ) :
    sl2DiagHom u ∈ Subgroup.normalizer (sl2Unip (F := F) : Set (SpecialLinearGroup (Fin 2) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨b, rfl⟩
    have := sl2Diag_conj_unip u (Multiplicative.toAdd b)
    rw [ofAdd_toAdd] at this
    exact ⟨_, this.symm⟩
  · rintro ⟨b, hb⟩
    have hg : g = (sl2DiagHom u)⁻¹ * sl2UnipHom b * sl2DiagHom u := by rw [hb]; group
    have := sl2Diag_conj_unip u⁻¹ (Multiplicative.toAdd b)
    rw [map_inv, inv_inv, ofAdd_toAdd] at this
    exact ⟨_, this.symm.trans hg.symm⟩

theorem isPGroup_sl2Unip [CharP F 2] : IsPGroup 2 (sl2Unip (F := F)) := by
  rintro ⟨_, b, rfl⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hb : b ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, ← two_mul, h2, zero_mul]
  have : sl2UnipHom b ^ 2 = 1 := by rw [← map_pow, hb, map_one]
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  exact this

theorem sl2Unip_ne_bot : sl2Unip (F := F) ≠ ⊥ := by
  intro h
  have hmem : sl2UnipHom (Multiplicative.ofAdd (1 : F)) ∈ sl2Unip (F := F) := ⟨_, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have := congrArg (fun g : SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F) 0 1) hmem
  simp only [coe_sl2UnipHom, toAdd_ofAdd] at this
  simp at this

end SL2

section Rank

variable {P : Type*} [Monoid P] {p : ℕ}

@[expose] def zmodPowHom [NeZero p] (u : P) (hu : u ^ p = 1) : Multiplicative (ZMod p) →* P where
  toFun k := u ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val +
      (Multiplicative.toAdd b).val) p, pow_add, pow_mul, hu, one_pow, mul_one]

end Rank

theorem not_three_dvd_two_pow_sub_one {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h4 : 4 ^ k % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by rw [pow_succ, pow_mul]; ring
  rw [h2]
  have hpos : 0 < 4 ^ k := by positivity
  omega

variable {G : Type} [Group G] [Finite G]

theorem le_localRank_of_elem {p : ℕ} (hp : p.Prime) {H E : Subgroup G}
    (hH : CFSG.Assembly.IsTwoLocal H) (hEH : E ≤ H) (hE : IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ localRank p G := by
  have hbE : ∀ k' : ℕ, ∀ E' : Subgroup G, Nat.card E' = p ^ k' → k' ≤ Nat.card G :=
    fun k' E' h => (CFSG.RankThreeEvenClassification.Helpers.exponent_le_prime_power p hp k').trans
      (h ▸ Subgroup.card_le_card_group E')
  have h1 : k ≤ CFSG.Assembly.pRank p H :=
    le_csSup ⟨Nat.card G, by rintro _ ⟨E', -, -, h⟩; exact hbE _ E' h⟩ ⟨E, hEH, hE, hk⟩
  have h2 : CFSG.Assembly.pRank p H ≤ localRank p G := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨H, hH, rfl⟩
    rintro _ ⟨H', -, rfl⟩
    exact (CFSG.RankThreeEvenClassification.Helpers.pRank_le_card p hp H').trans
      (Subgroup.card_le_card_group H')
  exact h1.trans h2

theorem exists_localRank_ge_three {n : ℕ} (hn : 1 < n) (hodd : Odd n) {K₁ K₂ K₃ : Subgroup G}
    (e₁ : K₁ ≃* projSL 2 (GaloisField 2 n)) (e₂ : K₂ ≃* projSL 2 (GaloisField 2 n))
    (e₃ : K₃ ≃* projSL 2 (GaloisField 2 n))
    (h12 : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (h13 : ∀ x ∈ K₁, ∀ y ∈ K₃, x * y = y * x)
    (h23 : ∀ x ∈ K₂, ∀ y ∈ K₃, x * y = y * x) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ 3 ≤ localRank p G := by
  classical
  have hq4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set p := Nat.minFac (2 ^ n - 1) with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ 2 ^ n - 1 := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpd
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    omega
  have hp3 : p ≠ 3 := fun h => not_three_dvd_two_pow_sub_one hodd (h ▸ hpd)
  have hp5 : 3 < p := by have := hp.two_le; omega
  have : Fact p.Prime := ⟨hp⟩
  have hcardF : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n (by omega)]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p (hcardF ▸ hpd)
  set F := GaloisField 2 n
  set f₁ := e₁.trans (projSLTwoEquivSL F) with hf₁
  set f₂ := e₂.trans (projSLTwoEquivSL F) with hf₂
  set f₃ := e₃.trans (projSLTwoEquivSL F) with hf₃
  set t₁ : G := (f₁.symm (sl2DiagHom u) : G) with ht₁
  set t₂ : G := (f₂.symm (sl2DiagHom u) : G) with ht₂
  set t₃ : G := (f₃.symm (sl2DiagHom u) : G) with ht₃
  have ht₁K : t₁ ∈ K₁ := (f₁.symm (sl2DiagHom u)).2
  have ht₂K : t₂ ∈ K₂ := (f₂.symm (sl2DiagHom u)).2
  have ht₃K : t₃ ∈ K₃ := (f₃.symm (sl2DiagHom u)).2
  have hord : ∀ {K : Subgroup G} (f : K ≃* SpecialLinearGroup (Fin 2) F),
      orderOf ((f.symm (sl2DiagHom u) : K) : G) = p := fun f => by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
      orderOf_injective _ sl2DiagHom_injective u, hu]
  have hpow : ∀ {K : Subgroup G} (f : K ≃* SpecialLinearGroup (Fin 2) F),
      ((f.symm (sl2DiagHom u) : K) : G) ^ p = 1 := fun f => by
    rw [← hord f]
    exact pow_orderOf_eq_one _
  set U₁ : Subgroup G := ((sl2Unip (F := F)).map f₁.symm.toMonoidHom).map K₁.subtype with hU₁
  have hU₁ne : U₁ ≠ ⊥ := by
    intro h
    apply sl2Unip_ne_bot (F := F)
    rw [hU₁, Subgroup.map_eq_bot_iff_of_injective _ K₁.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ f₁.symm.injective] at h
    exact h
  have hU₁2 : IsPGroup 2 U₁ := ((isPGroup_sl2Unip (F := F)).map _).map _
  set H := Subgroup.normalizer (U₁ : Set G) with hH
  have hHloc : CFSG.Assembly.IsTwoLocal H := ⟨U₁, hU₁ne, hU₁2, rfl⟩
  have hUK : U₁ ≤ K₁ := Subgroup.map_subtype_le _
  have ht₁H : t₁ ∈ H := by
    have h1 : f₁.symm (sl2DiagHom u) ∈ Subgroup.normalizer
        (((sl2Unip (F := F)).map f₁.symm.toMonoidHom : Subgroup K₁) : Set K₁) :=
      Subgroup.le_normalizer_map _ ⟨_, sl2DiagHom_mem_normalizer u, rfl⟩
    exact Subgroup.le_normalizer_map _ ⟨_, h1, rfl⟩
  have hcentH : ∀ g : G, (∀ x ∈ K₁, g * x = x * g) → g ∈ H := by
    intro g hg
    rw [hH, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hg x (hUK hx), mul_inv_cancel_right]
      exact hx
    · intro hx
      have hxK := hUK hx
      have hy := hg _ hxK
      have hxy : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * ((g * x * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hy]
          _ = g * x * g⁻¹ := by group
      rw [hxy]
      exact hx
  have ht₂H : t₂ ∈ H := hcentH t₂ fun x hx => (h12 x hx t₂ ht₂K).symm
  have ht₃H : t₃ ∈ H := hcentH t₃ fun x hx => (h13 x hx t₃ ht₃K).symm
  have c12 : Commute t₁ t₂ := h12 t₁ ht₁K t₂ ht₂K
  have c13 : Commute t₁ t₃ := h13 t₁ ht₁K t₃ ht₃K
  have c23 : Commute t₂ t₃ := h23 t₂ ht₂K t₃ ht₃K
  set g₁ := zmodPowHom t₁ (hpow f₁)
  set g₂ := zmodPowHom t₂ (hpow f₂)
  set g₃ := zmodPowHom t₃ (hpow f₃)
  set g₂₃ := MonoidHom.noncommCoprod g₂ g₃ fun a b => (c23.pow_pow _ _)
  have hc1 : ∀ a b, Commute (g₁ a) (g₂₃ b) := fun a b => by
    obtain ⟨b, c⟩ := b
    change Commute (t₁ ^ _) (t₂ ^ _ * t₃ ^ _)
    exact (c12.pow_pow _ _).mul_right (c13.pow_pow _ _)
  set h := MonoidHom.noncommCoprod g₁ g₂₃ hc1 with hh
  have happly : ∀ a b c, h (a, (b, c)) = t₁ ^ (Multiplicative.toAdd a).val *
      (t₂ ^ (Multiplicative.toAdd b).val * t₃ ^ (Multiplicative.toAdd c).val) := fun _ _ _ => rfl
  have hval : ∀ (a : Multiplicative (ZMod p)) (t : G), orderOf t = p →
      t ^ (Multiplicative.toAdd a).val = 1 → a = 1 := by
    intro a t ht h1
    rw [← orderOf_dvd_iff_pow_eq_one, ht] at h1
    have hlt := ZMod.val_lt (Multiplicative.toAdd a)
    have h0 : (Multiplicative.toAdd a).val = 0 := Nat.eq_zero_of_dvd_of_lt h1 hlt
    apply Multiplicative.toAdd.injective
    rw [toAdd_one]
    exact (ZMod.val_eq_zero _).mp h0
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b, c⟩ h1
    rw [happly] at h1
    have hb2 : t₂ ^ (Multiplicative.toAdd b).val ∈ K₂ := K₂.pow_mem ht₂K _
    have hc3 : t₃ ^ (Multiplicative.toAdd c).val ∈ K₃ := K₃.pow_mem ht₃K _
    have ha1 : t₁ ^ (Multiplicative.toAdd a).val ∈ K₁ := K₁.pow_mem ht₁K _
    have hcomm1 : ∀ x ∈ K₁, (t₂ ^ (Multiplicative.toAdd b).val *
        t₃ ^ (Multiplicative.toAdd c).val) * x = x * (t₂ ^ (Multiplicative.toAdd b).val *
        t₃ ^ (Multiplicative.toAdd c).val) := by
      intro x hx
      rw [mul_assoc, (h13 x hx _ hc3).symm, ← mul_assoc, (h12 x hx _ hb2).symm, mul_assoc]
    have hA : t₁ ^ (Multiplicative.toAdd a).val = 1 := by
      have heq : t₁ ^ (Multiplicative.toAdd a).val =
          (t₂ ^ (Multiplicative.toAdd b).val * t₃ ^ (Multiplicative.toAdd c).val)⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      have hz : (⟨_, ha1⟩ : K₁) = 1 := eq_one_of_forall_commute_of_mulEquiv_projSL e₁ fun x => by
        apply Subtype.ext
        change (x : G) * t₁ ^ (Multiplicative.toAdd a).val =
          t₁ ^ (Multiplicative.toAdd a).val * (x : G)
        rw [heq]
        have := hcomm1 x x.2
        calc (x : G) * (t₂ ^ (Multiplicative.toAdd b).val * t₃ ^ (Multiplicative.toAdd c).val)⁻¹
            = (t₂ ^ (Multiplicative.toAdd b).val * t₃ ^ (Multiplicative.toAdd c).val)⁻¹ *
              ((t₂ ^ (Multiplicative.toAdd b).val * t₃ ^ (Multiplicative.toAdd c).val) *
              (x : G)) *
              (t₂ ^ (Multiplicative.toAdd b).val * t₃ ^ (Multiplicative.toAdd c).val)⁻¹ := by
                group
          _ = (t₂ ^ (Multiplicative.toAdd b).val *
              t₃ ^ (Multiplicative.toAdd c).val)⁻¹ * (x : G) := by rw [this]; group
      exact congrArg Subtype.val hz
    rw [hA, one_mul] at h1
    have hB : t₂ ^ (Multiplicative.toAdd b).val = 1 := by
      have heq : t₂ ^ (Multiplicative.toAdd b).val = (t₃ ^ (Multiplicative.toAdd c).val)⁻¹ :=
        eq_inv_of_mul_eq_one_left h1
      have hz : (⟨_, hb2⟩ : K₂) = 1 := eq_one_of_forall_commute_of_mulEquiv_projSL e₂ fun x => by
        apply Subtype.ext
        change (x : G) * t₂ ^ (Multiplicative.toAdd b).val =
          t₂ ^ (Multiplicative.toAdd b).val * (x : G)
        rw [heq]
        have := h23 x x.2 _ hc3
        calc (x : G) * (t₃ ^ (Multiplicative.toAdd c).val)⁻¹
            = (t₃ ^ (Multiplicative.toAdd c).val)⁻¹ * (t₃ ^ (Multiplicative.toAdd c).val *
              (x : G)) * (t₃ ^ (Multiplicative.toAdd c).val)⁻¹ := by group
          _ = (t₃ ^ (Multiplicative.toAdd c).val)⁻¹ * (x : G) := by rw [← this]; group
      exact congrArg Subtype.val hz
    rw [hB, one_mul] at h1
    rw [hval a t₁ (hord f₁) hA, hval b t₂ (hord f₂) hB, hval c t₃ (hord f₃) h1]
    rfl
  have hEH : h.range ≤ H := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    rw [happly]
    exact H.mul_mem (H.pow_mem ht₁H _) (H.mul_mem (H.pow_mem ht₂H _) (H.pow_mem ht₃H _))
  have hEe : IsElemAbelian p h.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, rfl⟩⟩ := y
      apply Subtype.ext
      change h a * h b = h b * h a
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := by
        obtain ⟨a₁, a₂, a₃⟩ := a
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
          apply Multiplicative.toAdd.injective <;> simp
      rw [this, map_one]
  have hEcard : Nat.card h.range = p ^ 3 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, Nat.card_prod,
      Nat.card_eq_fintype_card (α := Multiplicative (ZMod p)), Fintype.card_multiplicative,
      ZMod.card]
    ring
  exact ⟨p, hp, hp5, le_localRank_of_elem hp hHloc hEH hEe hEcard⟩

theorem commute_kOf_of_four (h223 : Item223) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4) {n : ℕ}
    (eL : L ≃* projSU 4 2 n) {φ ψ : MulAut A} (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A)
    (hne : ψ ≠ φ) (hc : ψ * φ = φ * ψ) : ∀ x ∈ kOf A φ, ∀ y ∈ kOf A ψ, x * y = y * x := by
  obtain ⟨-, h2, -⟩ := h223 G A E U c L hpair hA81 n ⟨eL⟩ φ hφ ψ hψ
  have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (h2 hne hc)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y hy).symm

theorem false_of_three_commuting_dStar (h222 : Item222) (h223 : Item223)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hA81 : Nat.card A = 3 ^ 4)
    (hK : KOfWellDefined A)
    (htr : ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ)
    {φ₁ φ₂ φ₃ : MulAut A} (h₁ : φ₁ ∈ dStar A) (h₂ : φ₂ ∈ dStar A) (h₃ : φ₃ ∈ dStar A)
    (h12 : φ₁ ≠ φ₂) (h13 : φ₁ ≠ φ₃) (h23 : φ₂ ≠ φ₃)
    (c12 : φ₁ * φ₂ = φ₂ * φ₁) (c13 : φ₁ * φ₃ = φ₃ * φ₁) (c23 : φ₂ * φ₃ = φ₃ * φ₂) : False := by
  obtain ⟨φ₀, -, hφ₀D, n, hn1, hnodd, ⟨eL⟩, ⟨eK₀⟩, -⟩ := exists_case_five h222 hpair hA81
  have hk : ∀ {φ : MulAut A}, φ ∈ dStar A → Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 n)) :=
    fun {φ} hφ => by
      obtain ⟨g, hg, hgφ⟩ := htr φ₀ hφ₀D φ hφ
      obtain ⟨e⟩ := nonempty_kOf_mulEquiv_of_conj hK hφ₀D (closure_dStar_le_wStar A hg) hgφ
      exact ⟨e.trans eK₀⟩
  obtain ⟨e₁⟩ := hk h₁
  obtain ⟨e₂⟩ := hk h₂
  obtain ⟨e₃⟩ := hk h₃
  obtain ⟨p, hp, hp3, hle⟩ := exists_localRank_ge_three hn1 hnodd e₁ e₂ e₃
    (commute_kOf_of_four h223 hpair hA81 eL h₁ h₂ (Ne.symm h12) c12.symm)
    (commute_kOf_of_four h223 hpair hA81 eL h₁ h₃ (Ne.symm h13) c13.symm)
    (commute_kOf_of_four h223 hpair hA81 eL h₂ h₃ (Ne.symm h23) c23.symm)
  have := hpair.standing.toTheoremFourHyp.localRank_lt p hp hp3
  omega

end CFSG.RankThree.PartTwo.Sec21
