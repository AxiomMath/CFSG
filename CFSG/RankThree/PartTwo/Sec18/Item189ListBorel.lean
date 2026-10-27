module

public import CFSG.Goldschmidt.Steps.G3aBorel

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.Goldschmidt.G3a

section BorelThree

@[expose] def BorelOrderThree189 (X : Type) [Group X] : Prop :=
  ∀ T : Sylow 2 X, ∃ D : Subgroup X, BorelSetup T D ∧ ¬ 3 ∣ Nat.card (BorelSetup.kerD D T)

variable {X : Type} [Group X] [Finite X]

theorem exists_two_fixed_sylow189 {x : X} (hx : orderOf x = 3)
    (hcard : Nat.card (Sylow 2 X) % 3 = 2) :
    ∃ U U' : Sylow 2 X, U ≠ U' ∧
      x ∈ Subgroup.normalizer ((U : Subgroup X) : Set X) ∧
      x ∈ Subgroup.normalizer ((U' : Subgroup X) : Set X) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  have hmod := hG.card_modEq_card_fixedPoints (α := Sylow 2 X)
  have hmod' : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) (Sylow 2 X)) % 3 = 2 := by
    unfold Nat.ModEq at hmod
    omega
  have h1 : 1 < Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) (Sylow 2 X)) := by omega
  haveI := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne
    (MulAction.fixedPoints (Subgroup.zpowers x) (Sylow 2 X))
  have hfix : ∀ V : Sylow 2 X, V ∈ MulAction.fixedPoints (Subgroup.zpowers x) (Sylow 2 X) →
      x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) := fun V hV =>
    Sylow.smul_eq_iff_mem_normalizer.mp (hV ⟨x, Subgroup.mem_zpowers x⟩)
  exact ⟨a, b, fun h => hab (Subtype.ext h), hfix a ha, hfix b hb⟩

theorem eq_one_of_commute_orderThree189 {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D)
    (h3 : ¬ 3 ∣ Nat.card (BorelSetup.kerD D T)) {d : X} (hd : d ∈ D) (hd3 : orderOf d = 3)
    {c : X} (hc : c ∈ (T : Subgroup X)) (hdc : d * c = c * d) : c = 1 := by
  by_contra hc1
  obtain ⟨k, hk2, hk1⟩ := BorelSetup.exists_involution_pow hc hc1
  have hzZ := h.inv _ ((T : Subgroup X).pow_mem hc k) hk2
  have hcomm : d * c ^ k = c ^ k * d := (Commute.pow_right hdc k).eq
  have hdC := h.mem_centralizer_center hd hzZ hk1 hcomm
  apply h3
  rw [← hd3]
  exact Subgroup.orderOf_dvd_natCard (BorelSetup.kerD D T)
    (show d ∈ BorelSetup.kerD D T from ⟨hd, hdC⟩)

theorem exists_conj_orderThree189 {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D)
    (h3 : ¬ 3 ∣ Nat.card (BorelSetup.kerD D T)) {x : X}
    (hxN : x ∈ Subgroup.normalizer ((T : Subgroup X) : Set X)) (hx3 : orderOf x = 3) :
    ∃ s ∈ (T : Subgroup X), ∃ d ∈ D, orderOf d = 3 ∧ x = s⁻¹ * d * s := by
  obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul hxN
  have hTn : ∀ u ∈ (T : Subgroup X), d * u * d⁻¹ ∈ (T : Subgroup X) := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (h.le hd) u).mp hu
  have hx1 : t * d * (t * d) * (t * d) = 1 := by
    rw [← pow_three', ← hx3]
    exact pow_orderOf_eq_one _
  have hd3' : d ^ 3 ∈ (T : Subgroup X) ⊓ D := by
    refine ⟨?_, D.pow_mem hd 3⟩
    have e : d ^ 3 = (t * (d * t * d⁻¹) * (d * (d * t * d⁻¹) * d⁻¹))⁻¹ *
        (t * d * (t * d) * (t * d)) := by group
    rw [e, hx1, mul_one]
    exact (T : Subgroup X).inv_mem
      ((T : Subgroup X).mul_mem ((T : Subgroup X).mul_mem ht (hTn t ht)) (hTn _ (hTn t ht)))
  rw [h.inf, Subgroup.mem_bot] at hd3'
  have hord : orderOf d = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hd3') with h1 | h1
    · exfalso
      have hd1 : d = 1 := orderOf_eq_one_iff.mp h1
      subst hd1
      rw [mul_one] at hx3
      obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp (T : Sylow 2 X).isPGroup') ⟨t, ht⟩
      rw [Subgroup.orderOf_mk, hx3] at hn
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (dvd_of_eq hn)) (by norm_num)
    · exact h1
  have hC : ∀ c ∈ (T : Subgroup X), d * c = c * d → c = 1 := fun c hc hdc =>
    eq_one_of_commute_orderThree189 h h3 hd hord hc hdc
  obtain ⟨s, hs, hsd⟩ := BorelSetup.exists_eq_commutator (h.le hd) hC ht
  exact ⟨s, hs, d, hd, hord, by rw [← hsd]; group⟩

theorem eq_of_fixed_orderThree189 {T : Sylow 2 X} {D : Subgroup X} (h : BorelSetup T D)
    (h3 : ¬ 3 ∣ Nat.card (BorelSetup.kerD D T)) {x : X} (hx3 : orderOf x = 3)
    (hxT : x ∈ Subgroup.normalizer ((T : Subgroup X) : Set X)) {T' : Sylow 2 X} (hT' : T' ≠ T)
    (hxT' : x ∈ Subgroup.normalizer ((T' : Subgroup X) : Set X)) {P : Sylow 2 X}
    (hxP : x ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)) : P = T ∨ P = T' := by
  by_cases hPT : P = T
  · exact Or.inl hPT
  right
  obtain ⟨s₀, hs₀, d, hd, hd3, hxd⟩ := exists_conj_orderThree189 h h3 hxT hx3
  have hC : ∀ c ∈ (T : Subgroup X), x * c = c * x → c = 1 := by
    intro c hc hxc
    have hc' : s₀ * c * s₀⁻¹ ∈ (T : Subgroup X) :=
      (T : Subgroup X).mul_mem ((T : Subgroup X).mul_mem hs₀ hc) ((T : Subgroup X).inv_mem hs₀)
    have hcomm : d * (s₀ * c * s₀⁻¹) = (s₀ * c * s₀⁻¹) * d := by
      have e1 : d = s₀ * x * s₀⁻¹ := by rw [hxd]; group
      rw [e1]
      calc s₀ * x * s₀⁻¹ * (s₀ * c * s₀⁻¹) = s₀ * (x * c) * s₀⁻¹ := by group
        _ = s₀ * (c * x) * s₀⁻¹ := by rw [hxc]
        _ = s₀ * c * s₀⁻¹ * (s₀ * x * s₀⁻¹) := by group
    have h1 := eq_one_of_commute_orderThree189 h h3 hd hd3 hc' hcomm
    have : c = s₀⁻¹ * (s₀ * c * s₀⁻¹) * s₀ := by group
    rw [this, h1]
    group
  obtain ⟨s, hs, rfl⟩ := h.exists_smul hT' hPT
  have h1 : s⁻¹ * x * s ∈ Subgroup.normalizer ((T' : Subgroup X) : Set X) :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_normalizer_conj_smul_iff.mp hxP
  have h5 : x⁻¹ * (s⁻¹ * x * s) ∈ (T : Subgroup X) := by
    have e : x⁻¹ * (s⁻¹ * x * s) = (x⁻¹ * s⁻¹ * x⁻¹⁻¹) * s := by group
    rw [e]
    exact (T : Subgroup X).mul_mem ((Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ hxT) s⁻¹).mp ((T : Subgroup X).inv_mem hs)) hs
  have h4 : x⁻¹ * (s⁻¹ * x * s) ∈ Subgroup.normalizer ((T' : Subgroup X) : Set X) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxT') h1
  have h6 := CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.eq_one_of_mem_normalizer
    h.se hT' h5 h4
  have hsx : x * s = s * x := by
    calc x * s = s * x * (x⁻¹ * (s⁻¹ * x * s)) := by group
      _ = s * x := by rw [h6, mul_one]
  rw [hC s hs hsx, one_smul]

theorem exists_fixed_pair189 (hB : BorelOrderThree189 X) {x : X} (hx3 : orderOf x = 3)
    (hcard : Nat.card (Sylow 2 X) % 3 = 2) :
    ∃ U U' : Sylow 2 X, U ≠ U' ∧
      x ∈ Subgroup.normalizer ((U : Subgroup X) : Set X) ∧
      x ∈ Subgroup.normalizer ((U' : Subgroup X) : Set X) ∧
      ∀ V : Sylow 2 X, x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) → V = U ∨ V = U' := by
  obtain ⟨U, U', hne, hxU, hxU'⟩ := exists_two_fixed_sylow189 hx3 hcard
  obtain ⟨D, hD, h3⟩ := hB U
  exact ⟨U, U', hne, hxU, hxU', fun V hV =>
    eq_of_fixed_orderThree189 hD h3 hx3 hxU hne.symm hxU' hV⟩

theorem exists_conj_mem_zpowers189 (hB : BorelOrderThree189 X)
    (hcard : Nat.card (Sylow 2 X) % 3 = 2) {x x' : X} (hx : orderOf x = 3)
    (hx' : orderOf x' = 3) : ∃ g : X, g * x' * g⁻¹ ∈ Subgroup.zpowers x := by
  classical
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨D, hD, h3⟩ := hB T
  have key : ∀ y : X, orderOf y = 3 → ∃ g : X, ∃ d ∈ D, orderOf d = 3 ∧ y = g * d * g⁻¹ := by
    intro y hy
    obtain ⟨U, U', hne, hyU, -⟩ := exists_two_fixed_sylow189 hy hcard
    obtain ⟨c, rfl⟩ := MulAction.exists_smul_eq X T U
    have hyT : c⁻¹ * y * c ∈ Subgroup.normalizer ((T : Subgroup X) : Set X) :=
      CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_normalizer_conj_smul_iff.mp
        hyU
    have hy3 : orderOf (c⁻¹ * y * c) = 3 := by
      have := (MulAut.conj c⁻¹).orderOf_eq y
      rw [hy] at this
      simpa [MulAut.conj_apply] using this
    obtain ⟨s, hs, d, hd, hd3, hsd⟩ := exists_conj_orderThree189 hD h3 hyT hy3
    refine ⟨c * s⁻¹, d, hd, hd3, ?_⟩
    have e : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [e, hsd]
    group
  obtain ⟨g₁, d₁, hd₁, hd₁3, hxg⟩ := key x hx
  obtain ⟨g₂, d₂, hd₂, hd₂3, hxg'⟩ := key x' hx'
  have hzp : d₂ ∈ Subgroup.zpowers d₁ := by
    haveI := hD.cyc
    have hle₁ : Subgroup.zpowers d₁ ≤ D := Subgroup.zpowers_le.mpr hd₁
    have hle₂ : Subgroup.zpowers d₂ ≤ D := Subgroup.zpowers_le.mpr hd₂
    have hH : Nat.card ((Subgroup.zpowers d₂).subgroupOf D) =
        Nat.card ((Subgroup.zpowers d₁).subgroupOf D) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv, Nat.card_zpowers,
        Nat.card_zpowers, hd₁3, hd₂3]
    have hsub : (Subgroup.zpowers d₂).subgroupOf D ≤ (Subgroup.zpowers d₁).subgroupOf D :=
      IsCyclic.subgroup_le_iff_card_dvd.mpr (dvd_of_eq hH)
    exact hsub (show (⟨d₂, hd₂⟩ : D) ∈ (Subgroup.zpowers d₂).subgroupOf D from
      Subgroup.mem_zpowers d₂)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzp
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  have e1 : g₁ * g₂⁻¹ * x' * (g₁ * g₂⁻¹)⁻¹ = g₁ * d₂ * g₁⁻¹ := by rw [hxg']; group
  rw [e1, ← hj, Subgroup.mem_zpowers_iff]
  exact ⟨j, by rw [hxg, conj_zpow]⟩

theorem exists_unique_sylow189 (hB : ∀ T : Sylow 2 X, ∃ D : Subgroup X, BorelSetup T D)
    {R : Subgroup X} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) :
    ∃! U : Sylow 2 X, R ≤ (U : Subgroup X) := by
  obtain ⟨U, hU⟩ := hR.exists_le_sylow
  refine ⟨U, hU, fun V hV => ?_⟩
  by_contra hne
  obtain ⟨D, hD⟩ := hB U
  apply hR1
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  exact CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.eq_one_of_mem_of_mem hD.se hne
    (hU hr) (hV hr)

theorem no_swap189 (hB : BorelOrderThree189 X) {x : X} {U U' : Sylow 2 X} (hne : U ≠ U')
    (hxU : x ∈ Subgroup.normalizer ((U : Subgroup X) : Set X))
    (hxU' : x ∈ Subgroup.normalizer ((U' : Subgroup X) : Set X))
    (hfix : ∀ V : Sylow 2 X, x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) → V = U ∨ V = U')
    {h : X} (hhx : h * x = x * h) (hswap : h • U = U') : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcx : h⁻¹ * x * h = x := by
    calc h⁻¹ * x * h = h⁻¹ * (x * h) := by group
      _ = h⁻¹ * (h * x) := by rw [← hhx]
      _ = x := by group
  have hperm : ∀ V : Sylow 2 X, x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) →
      x ∈ Subgroup.normalizer (((h • V : Sylow 2 X) : Subgroup X) : Set X) := by
    intro V hV
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_normalizer_conj_smul_iff,
      hcx]
    exact hV
  have hU'swap : h • U' = U := by
    rcases hfix _ (hperm U' hxU') with h2 | h2
    · exact h2
    · exact absurd (smul_left_cancel h (hswap.trans h2.symm)) hne
  have hsq : h ^ 2 • U = U := by rw [pow_two, mul_smul, hswap, hU'swap]
  have hsq' : h ^ 2 • U' = U' := by rw [pow_two, mul_smul, hU'swap, hswap]
  have hpow : ∀ V : Sylow 2 X, h ^ 2 • V = V → ∀ j : ℕ, (h ^ 2) ^ j • V = V := by
    intro V hV j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hV, ih]
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf h) (orderOf_pos h).ne'
  obtain ⟨j, rfl⟩ := hb
  set g := h ^ (2 * j + 1) with hg
  have hgU : g • U = U' := by
    rw [hg, pow_succ, mul_smul, hswap, pow_mul]
    exact hpow U' hsq' j
  have hgU' : g • U' = U := by
    rw [hg, pow_succ, mul_smul, hU'swap, pow_mul]
    exact hpow U hsq j
  have hordg : orderOf g = 2 ^ a := by
    rw [hg, orderOf_pow_of_dvd (by omega) (by rw [hab]; exact dvd_mul_left _ _), hab,
      Nat.mul_div_cancel _ (by omega)]
  have hR2 : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hordg])
  have hR1 : Subgroup.zpowers g ≠ ⊥ := by
    intro hbot
    have h1 : g = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [h1, one_smul] at hgU
    exact hne hgU
  obtain ⟨V, hV, hVu⟩ := exists_unique_sylow189 (fun T => (hB T).imp fun D hD => hD.1) hR2 hR1
  have hgx : Commute g x := Commute.pow_left (show Commute h x from hhx) _
  have hxV : Subgroup.zpowers g ≤ ((x • V : Sylow 2 X) : Subgroup X) := by
    intro r hr
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    have hk : (g ^ k) * x = x * (g ^ k) := ((Commute.zpow_left hgx k)).eq
    have e : x⁻¹ * g ^ k * x = g ^ k := by
      calc x⁻¹ * g ^ k * x = x⁻¹ * (g ^ k * x) := by group
        _ = x⁻¹ * (x * g ^ k) := by rw [hk]
        _ = g ^ k := by group
    rw [e]
    exact hV hr
  have hxNV : x ∈ Subgroup.normalizer ((V : Subgroup X) : Set X) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (hVu _ hxV)
  have hgmem : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
  rcases hfix V hxNV with rfl | rfl
  · have : g • V = V := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hV hgmem))
    exact hne (this.symm.trans hgU)
  · have : g • V = V := Sylow.smul_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hV hgmem))
    exact hne (hgU'.symm.trans this)

end BorelThree

end CFSG.RankThree.PartTwo.Sec18
