module

public import CFSG.Quasithin.H13.L32A714a
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a
public import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Quasithin

section Gen

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem pow_mod_three_eq {x : Γ} (hx : x ^ 3 = 1) (m : ℕ) : x ^ (m % 3) = x ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem three_le_pRank {y a c : Γ} (hy : y ^ 3 = 1) (ha : a ^ 3 = 1) (hc : c ^ 3 = 1)
    (hya : y * a = a * y) (hyc : y * c = c * y) (hac : a * c = c * a)
    (hind : ∀ i j l : ℕ, i < 3 → j < 3 → l < 3 → y ^ i * a ^ j * c ^ l = 1 →
      i = 0 ∧ j = 0 ∧ l = 0) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup Γ) := by
  have hcy : Commute y a := hya
  have hcc : Commute y c := hyc
  have hac' : Commute a c := hac
  let f : Multiplicative (Fin 3 → ZMod 3) →* Γ :=
    { toFun := fun v => y ^ (Multiplicative.toAdd v 0).val * a ^ (Multiplicative.toAdd v 1).val *
        c ^ (Multiplicative.toAdd v 2).val
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, ZMod.val_add]
        rw [pow_mod_three_eq hy, pow_mod_three_eq ha, pow_mod_three_eq hc, pow_add, pow_add,
          pow_add]
        have h1 := (hcy.pow_pow (Multiplicative.toAdd w 0).val (Multiplicative.toAdd v 1).val).eq
        have h2 := (hcc.pow_pow (Multiplicative.toAdd w 0).val (Multiplicative.toAdd v 2).val).eq
        have h3 := (hac'.pow_pow (Multiplicative.toAdd w 1).val (Multiplicative.toAdd v 2).val).eq
        generalize y ^ (Multiplicative.toAdd v 0).val = Y₁ at h1 h2 h3 ⊢
        generalize y ^ (Multiplicative.toAdd w 0).val = Y₂ at h1 h2 h3 ⊢
        generalize a ^ (Multiplicative.toAdd v 1).val = A₁ at h1 h2 h3 ⊢
        generalize a ^ (Multiplicative.toAdd w 1).val = A₂ at h1 h2 h3 ⊢
        generalize c ^ (Multiplicative.toAdd v 2).val = C₁ at h1 h2 h3 ⊢
        generalize c ^ (Multiplicative.toAdd w 2).val = C₂ at h1 h2 h3 ⊢
        calc Y₁ * Y₂ * (A₁ * A₂) * (C₁ * C₂) = Y₁ * (Y₂ * A₁) * A₂ * (C₁ * C₂) := by group
          _ = Y₁ * A₁ * (Y₂ * (A₂ * C₁)) * C₂ := by rw [h1]; group
          _ = Y₁ * A₁ * (Y₂ * C₁ * A₂) * C₂ := by rw [h3]; group
          _ = Y₁ * A₁ * C₁ * (Y₂ * A₂ * C₂) := by rw [h2]; group }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h := hind _ _ _ (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hv
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h.1
    · exact (ZMod.val_eq_zero _).mp h.2.1
    · exact (ZMod.val_eq_zero _).mp h.2.2
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun v w => mul_comm v w)
    (fun v => ?_) (k := 3) ?_ f hf le_top
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  · rw [Nat.card_eq_fintype_card]
    simp

theorem mem_center_of_pow_three (hrank : Open.pRank 3 (⊤ : Subgroup Γ) ≤ 2) {X : Subgroup Γ}
    (hX : IsPOnePlusTwo 3 ↥X) {y : Γ} (hyC : y ∈ Subgroup.centralizer (X : Set Γ))
    (hy3 : y ^ 3 = 1) : y ∈ (Subgroup.center ↥X).map X.subtype := by
  by_contra hyZ
  obtain ⟨a, ha⟩ : ∃ a : ↥X, a ∉ Subgroup.center ↥X := by
    by_contra hno
    push Not at hno
    exact Heis.center_ne_top hX (eq_top_iff.mpr fun x _ => hno x)
  obtain ⟨c, hcZ, hc1⟩ := Heis.exists_center_ne_one hX
  have ha3 : (a : Γ) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, Heis.pow_three_eq hX, Subgroup.coe_one]
  have hc3 : (c : Γ) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, Heis.pow_three_eq hX, Subgroup.coe_one]
  have hya : y * a = a * y := (Subgroup.mem_centralizer_iff.mp hyC a a.2).symm
  have hyc : y * c = c * y := (Subgroup.mem_centralizer_iff.mp hyC c c.2).symm
  have hac : (a : Γ) * c = c * a := congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ a)
  have hyX : ∀ x : ↥X, (x : Γ) = y → False := by
    intro x hx
    apply hyZ
    refine ⟨x, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, hx⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hx]
    exact (Subgroup.mem_centralizer_iff.mp hyC g g.2)
  have hy1 : ∀ x : ↥X, (x : Γ) = y ^ 2 → False := by
    intro x hx
    refine hyX (x ^ 2) ?_
    rw [Subgroup.coe_pow, hx, ← pow_mul]
    calc y ^ (2 * 2) = y ^ 3 * y := by rw [show 2 * 2 = 3 + 1 by norm_num, pow_succ]
      _ = y := by rw [hy3, one_mul]
  refine absurd (three_le_pRank hy3 ha3 hc3 hya hyc hac ?_) (by omega)
  intro i j l hi hj hl h
  have hyi : y ^ i = ((a ^ j * c ^ l)⁻¹ : ↥X) := by
    rw [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    calc y ^ i = y ^ i * (a : Γ) ^ j * (c : Γ) ^ l * ((c : Γ) ^ l)⁻¹ * ((a : Γ) ^ j)⁻¹ := by group
      _ = ((a : Γ) ^ j * (c : Γ) ^ l)⁻¹ := by rw [h]; group
  have hi0 : i = 0 := by
    interval_cases i
    · rfl
    · exact (hyX _ (by rw [← hyi, pow_one])).elim
    · exact (hy1 _ hyi.symm).elim
  subst hi0
  rw [pow_zero, one_mul] at h
  have hacZ : a ^ j ∈ Subgroup.center ↥X := by
    have e : a ^ j = (c ^ l)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_inv, Subgroup.coe_pow]
      exact eq_inv_of_mul_eq_one_left h
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcZ l)
  have hj0 : j = 0 := by
    interval_cases j
    · rfl
    · exact (ha (by simpa using hacZ)).elim
    · exact (ha (Heis.mem_center_of_sq hX hacZ)).elim
  subst hj0
  rw [pow_zero, one_mul] at h
  refine ⟨rfl, rfl, ?_⟩
  interval_cases l
  · rfl
  · exact (hc1 (Subtype.ext (by simpa using h))).elim
  · exfalso
    apply hc1
    apply Subtype.ext
    have e : (c : Γ) = (c : Γ) ^ 3 * ((c : Γ) ^ 2)⁻¹ := by group
    rw [e, hc3, h]
    simp

omit [Finite Γ] in
theorem conj_eq_of_coprime {p : ℕ} {Y : Subgroup Γ} (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hYp : IsPGroup p ↥Y) {g : Γ} (hgY : g ∈ Subgroup.normalizer (Y : Set Γ)) {m : ℕ}
    (hm : Nat.Coprime p m) (hgm : ∀ y ∈ Y, g ^ m * y * (g ^ m)⁻¹ = y)
    (hΩ : ∀ y ∈ Y, y ^ p = 1 → g * y * g⁻¹ = y) {y : Γ} (hy : y ∈ Y) : g * y * g⁻¹ = y := by
  obtain ⟨k, hk⟩ := hYp ⟨y, hy⟩
  have hk' : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  clear hk
  induction k generalizing y with
  | zero =>
    rw [pow_zero, pow_one] at hk'
    rw [hk', mul_one, mul_inv_cancel]
  | succ k ih =>
    have h1 : g * y ^ p * g⁻¹ = y ^ p :=
      ih (Y.pow_mem hy p) (by rw [← pow_mul, ← pow_succ']; exact hk')
    have hgy : g * y * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgY y).mp hy
    have hbY : g * y * g⁻¹ * y⁻¹ ∈ Y := Y.mul_mem hgy (Y.inv_mem hy)
    have hbp : (g * y * g⁻¹ * y⁻¹) ^ p = 1 := by
      have hc : Commute (g * y * g⁻¹) y⁻¹ := hYc _ hgy _ (Y.inv_mem hy)
      rw [hc.mul_pow, conj_pow, h1, inv_pow, mul_inv_cancel]
    have hbg := hΩ _ hbY hbp
    have hj : ∀ j : ℕ, g ^ j * y * (g ^ j)⁻¹ = (g * y * g⁻¹ * y⁻¹) ^ j * y := by
      intro j
      induction j with
      | zero => simp
      | succ j ihj =>
        calc g ^ (j + 1) * y * (g ^ (j + 1))⁻¹ = g * (g ^ j * y * (g ^ j)⁻¹) * g⁻¹ := by group
          _ = (g * (g * y * g⁻¹ * y⁻¹) * g⁻¹) ^ j * (g * y * g⁻¹) := by
            rw [ihj, conj_pow]; group
          _ = (g * y * g⁻¹ * y⁻¹) ^ (j + 1) * y := by
            rw [hbg, pow_succ, mul_assoc ((g * y * g⁻¹ * y⁻¹) ^ j)]
            congr 1
            group
    have hbm : (g * y * g⁻¹ * y⁻¹) ^ m = 1 := by
      have h2 := hj m
      rw [hgm y hy] at h2
      calc (g * y * g⁻¹ * y⁻¹) ^ m = (g * y * g⁻¹ * y⁻¹) ^ m * y * y⁻¹ := by group
        _ = 1 := by rw [← h2, mul_inv_cancel]
    have hb1 : g * y * g⁻¹ * y⁻¹ = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hm (orderOf_dvd_of_pow_eq_one hbp)
        (orderOf_dvd_of_pow_eq_one hbm))
    exact mul_inv_eq_one.mp hb1

theorem isPGroup_three_centralizer (hrank : Open.pRank 3 (⊤ : Subgroup Γ) ≤ 2)
    (hO : CFSG.pPrimeCore 3 Γ = ⊥) {X : Subgroup Γ} [X.Normal] (hX : IsPOnePlusTwo 3 ↥X) :
    IsPGroup 3 ↥(Subgroup.centralizer (X : Set Γ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer (X : Set Γ) with hC
  have hZ : ∀ c : ↥C, c ^ 3 = 1 → (c : Γ) ∈ (Subgroup.center ↥X).map X.subtype := fun c hc =>
    mem_center_of_pow_three hrank hX c.2 (by simpa using congrArg Subtype.val hc)
  have hZC : ∀ c : ↥C, c ^ 3 = 1 → ∀ g : ↥C, g * c = c * g := by
    intro c hc g
    obtain ⟨x, -, hx⟩ := hZ c hc
    have hcX : (c : Γ) ∈ X := hx ▸ x.2
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp g.2 _ hcX).symm
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥C))
  have hPcyc : IsCyclic ↥(P : Subgroup ↥C) := by
    by_contra hnc
    have : Fact (IsPGroup 3 ↥(P : Subgroup ↥C)) := ⟨P.isPGroup'⟩
    obtain ⟨S, -, hS9, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
    have hpow : ∀ s : ↥S, ((s : ↥(P : Subgroup ↥C)) : ↥C) ^ 3 = 1 := by
      intro s
      have h1 : s ^ 3 = 1 := by
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSel.exponent_dvd_p s
      simpa using congrArg (fun t : ↥S => ((t : ↥(P : Subgroup ↥C)) : ↥C)) h1
    let f : ↥S → ↥((Subgroup.center ↥X).map X.subtype) := fun s =>
      ⟨(((s : ↥(P : Subgroup ↥C)) : ↥C) : Γ), hZ _ (hpow s)⟩
    have hf : Function.Injective f := by
      intro s t hst
      have := congrArg Subtype.val hst
      exact Subtype.ext (Subtype.ext (Subtype.ext this))
    have hle := Nat.card_le_card_of_injective f hf
    rw [hS9, Subgroup.card_map_of_injective X.subtype_injective, Heis.card_center hX] at hle
    norm_num at hle
  have hPcomm : IsMulCommutative ↥(P : Subgroup ↥C) := inferInstance
  have hPc : ∀ a ∈ (P : Subgroup ↥C), ∀ b ∈ (P : Subgroup ↥C), a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hPcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hNC : Subgroup.normalizer ((P : Subgroup ↥C) : Set ↥C) ≤
      Subgroup.centralizer ((P : Subgroup ↥C) : Set ↥C) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨e, m, hm3, hom⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
    have hgm3 : (g ^ m) ^ 3 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hom, pow_orderOf_eq_one]
    have hzp : IsPGroup 3 ↥(Subgroup.zpowers (g ^ m)) := by
      rintro ⟨z, hz⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      refine ⟨e, Subtype.ext ?_⟩
      change ((g ^ m) ^ n) ^ 3 ^ e = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgm3, one_zpow]
    have hgmP : g ^ m ∈ (P : Subgroup ↥C) := by
      have hmem : g ^ m ∈ Subgroup.zpowers (g ^ m) ⊓ Subgroup.normalizer (P : Set ↥C) :=
        ⟨Subgroup.mem_zpowers _, Subgroup.pow_mem _ hg m⟩
      rw [hzp.inf_normalizer_sylow P] at hmem
      exact hmem.2
    have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
    have key := conj_eq_of_coprime hPc P.isPGroup' hg hcop
      (fun z hz => by rw [hPc _ hgmP _ hz]; group)
      (fun z _ hz3 => by rw [hZC z hz3 g]; group) hy
    calc y * g = g * y * g⁻¹ * g := by rw [key]
      _ = g * y := by group
  obtain ⟨Kc, -, hK3, hKidx, -, hKchar, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hNC
  have : Kc.Characteristic := hKchar
  have hKΓ : (Kc.map C.subtype).Normal := inferInstance
  have hKbot : Kc.map C.subtype = ⊥ := by
    refine (CFSG.pPrimeCore_eq_bot_iff.mp hO) _ hKΓ ?_
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK3
  have hK : Kc = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hKbot
  rw [hK, Subgroup.index_bot] at hKidx
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  exact IsPGroup.of_card (hKidx.trans hn)

end Gen

end CFSG.Quasithin.H13.L32A
