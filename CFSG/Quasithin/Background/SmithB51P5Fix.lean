module

public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.P3G2Zorn

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

namespace P5

section Realize

variable {V : Type} [CommGroup V]

theorem exists_fixed_class {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (γ : D.Gam) {m : D.Amb} (hm : m ∈ D.sec)
    (hfix : D.act γ m = m) (hmk : m ∉ D.ker) :
    ∃ s ∈ U, s ∉ Z ∧ ((π γ : ↥H) : MulAut V) s * s⁻¹ ∈ Z := by
  obtain ⟨-, -, -, hHU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  obtain ⟨s₀, hs₀⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hu : ((π γ : ↥H) : MulAut V) (s₀ : V) ∈ U := hHU (π γ) s₀ s₀.2
  have hm2 : D.act γ m ∈ D.sec := hsec γ m hm
  have h1 := hβe γ s₀ ⟨m, hm⟩ hu hm2 hs₀
  have h2 : (⟨D.act γ m, hm2⟩ : ↥D.sec) = ⟨m, hm⟩ := Subtype.ext hfix
  rw [h2, ← hs₀] at h1
  refine ⟨s₀, s₀.2, fun hsZ => hmk ?_, ?_⟩
  · have h3 := (hβk s₀).2 hsZ
    rw [hs₀, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
    exact h3
  · have h4 : β (⟨((π γ : ↥H) : MulAut V) (s₀ : V), hu⟩ * s₀⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    exact (hβk _).1 h4

theorem exists_moved_class {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (γ : D.Gam) {m : D.Amb} (hm : m ∈ D.sec)
    (hmove : D.act γ m * m⁻¹ ∉ D.ker) :
    ∃ s ∈ U, ((π γ : ↥H) : MulAut V) s * s⁻¹ ∉ Z := by
  obtain ⟨-, -, -, hHU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  obtain ⟨s₀, hs₀⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hu : ((π γ : ↥H) : MulAut V) (s₀ : V) ∈ U := hHU (π γ) s₀ s₀.2
  have hm2 : D.act γ m ∈ D.sec := hsec γ m hm
  have h1 := hβe γ s₀ ⟨m, hm⟩ hu hm2 hs₀
  refine ⟨s₀, s₀.2, fun hZ => hmove ?_⟩
  have h4 := (hβk (⟨((π γ : ↥H) : MulAut V) (s₀ : V), hu⟩ * s₀⁻¹)).2 hZ
  rw [map_mul, map_inv, h1, hs₀, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h4
  exact h4

end Realize

section Sym

@[expose] def c3 (m : ℕ) (hm : 5 ≤ m) : Equiv.Perm (Fin m) :=
  Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩ * Equiv.swap ⟨1, by omega⟩ ⟨2, by omega⟩

@[expose] def x34 (m : ℕ) : G6.PermMod m :=
  Multiplicative.ofAdd fun i => if (i : ℕ) = 3 ∨ (i : ℕ) = 4 then 1 else 0

@[expose] def x03 (m : ℕ) : G6.PermMod m :=
  Multiplicative.ofAdd fun i => if (i : ℕ) = 0 ∨ (i : ℕ) = 3 then 1 else 0

theorem symDn_facts (m : ℕ) (hm5 : 5 ≤ m) (hm8 : m ≤ 8) :
    c3 m hm5 ^ 3 = 1 ∧ (∑ i, Multiplicative.toAdd (x34 m) i = 0) ∧
      G6.permAct m (c3 m hm5) (x34 m) = x34 m ∧ x34 m ≠ 1 ∧ x34 m ≠ G6.allOnes m ∧
      (∑ i, Multiplicative.toAdd (x03 m) i = 0) ∧
      G6.permAct m (c3 m hm5) (x03 m) * (x03 m)⁻¹ ≠ 1 ∧
      G6.permAct m (c3 m hm5) (x03 m) * (x03 m)⁻¹ ≠ G6.allOnes m := by
  interval_cases m <;> decide +revert

theorem mem_zpowers_of_sq {M : Type*} [Group M] {a x : M} (ha : a ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact ha
  rw [zpow_eq_zpow_emod k h2]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem allOnes_sq (m : ℕ) : G6.allOnes m ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp [G6.allOnes]
  decide

theorem exists_order_three_of_symDn {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {m : ℕ} (hm5 : 5 ≤ m) (hm8 : m ≤ 8) (hS : SymmetricNatural H U Z m) :
    ∃ g ∈ H, g ^ 3 = 1 ∧ (∃ s ∈ U, s ∉ Z ∧ g s * s⁻¹ ∈ Z) ∧ ∃ s ∈ U, g s * s⁻¹ ∉ Z := by
  obtain ⟨π, hπ⟩ := hS
  obtain ⟨h3, h34c, h34f, h34a, h34b, h03c, h03a, h03b⟩ := symDn_facts m hm5 hm8
  have hker : ∀ x : G6.PermMod m, x ≠ 1 → x ≠ G6.allOnes m → x ∉ (FFModel.symDn m).ker := by
    intro x hx1 hx2 hx
    rcases mem_zpowers_of_sq (allOnes_sq m) hx.1 with h | h
    · exact hx1 h
    · exact hx2 h
  refine ⟨((π (c3 m hm5) : ↥H) : MulAut V), (π (c3 m hm5)).2, ?_, ?_, ?_⟩
  · have h1 : π (c3 m hm5) ^ 3 = 1 :=
      (map_pow π (c3 m hm5) 3).symm.trans ((congrArg π h3).trans (map_one π))
    rw [← Subgroup.coe_pow, h1]
    rfl
  · exact exists_fixed_class hπ (c3 m hm5) (m := x34 m) (G6.mem_coreMod.2 h34c) h34f
      (hker _ h34a h34b)
  · exact exists_moved_class hπ (c3 m hm5) (m := x03 m) (G6.mem_coreMod.2 h03c)
      (hker _ h03a h03b)

end Sym

section Zorn

open Matrix CFSG.Quasithin.JonesParshall

variable {K : Type} [Field K]

@[expose] def perm3 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem perm3_det : (perm3 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [perm3, det_fin_three]

@[expose] def perm3SL : SL3 K := ⟨perm3, perm3_det⟩

theorem perm3SL_pow_three : (perm3SL : SL3 K) ^ 3 = 1 := by
  apply Subtype.ext
  change (perm3 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [perm3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem gAFun_perm3 (x : quasithinZorn K) :
    gAFun (perm3 : Matrix (Fin 3) (Fin 3) K) x =
      (x.1, perm3 *ᵥ x.2.1, perm3 *ᵥ x.2.2.1, x.2.2.2) := by
  have hadj : (adjugate (perm3 : Matrix (Fin 3) (Fin 3) K))ᵀ = perm3 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [perm3, adjugate_fin_three]
  simp only [gAFun, hadj]

theorem zorn_facts :
    gAFun (perm3 : Matrix (Fin 3) (Fin 3) K) ((0 : K), ![1, 1, 1], (0 : Fin 3 → K), (0 : K)) =
        ((0 : K), ![1, 1, 1], (0 : Fin 3 → K), (0 : K)) ∧
      gAFun (perm3 : Matrix (Fin 3) (Fin 3) K) ((0 : K), ![1, 0, 0], (0 : Fin 3 → K), (0 : K)) -
          ((0 : K), ![1, 0, 0], (0 : Fin 3 → K), (0 : K)) =
        ((0 : K), ![-1, 1, 0], (0 : Fin 3 → K), (0 : K)) := by
  rw [gAFun_perm3, gAFun_perm3]
  refine ⟨?_, ?_⟩
  · simp only [Prod.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_⟩
    · ext i
      fin_cases i <;> simp [perm3, mulVec, dotProduct, Fin.sum_univ_three]
    · simp
  · simp only [Prod.mk_sub_mk, sub_zero, Prod.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_⟩
    · ext i
      fin_cases i <;> simp [perm3]
    · simp

theorem exists_order_three_of_g2 {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} (hG2 : G2Natural H U Z 1) :
    ∃ g ∈ H, g ^ 3 = 1 ∧ (∃ s ∈ U, s ∉ Z ∧ g s * s⁻¹ ∈ Z) ∧ ∃ s ∈ U, g s * s⁻¹ ∉ Z := by
  obtain ⟨K', hK', hf, hc, π, hπ⟩ := hG2
  have : Fintype K' := Fintype.ofFinite K'
  have hch : CharP K' 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hc])
  have hmem : ((g2A (perm3SL : SL3 K') : ↥(Explicit.cayleyGroup K')) :
      quasithinZorn K' ≃ₗ[K'] quasithinZorn K') ∈ quasithinG2 K' := by
    rw [G11.P3G2.quasithinG2_eq_cayleyGroup]
    exact (g2A (perm3SL : SL3 K')).2
  set γ : ↥(quasithinG2 K') := ⟨_, hmem⟩
  obtain ⟨hfix, hmove⟩ := zorn_facts (K := K')
  set m0 : (FFModel.zornQ (quasithinG2 K')).Amb :=
    Multiplicative.ofAdd ((0 : K'), ![1, 1, 1], (0 : Fin 3 → K'), (0 : K'))
  set m1 : (FFModel.zornQ (quasithinG2 K')).Amb :=
    Multiplicative.ofAdd ((0 : K'), ![1, 0, 0], (0 : Fin 3 → K'), (0 : K'))
  have hfix' : (FFModel.zornQ (quasithinG2 K')).act γ m0 = m0 :=
    congrArg Multiplicative.ofAdd hfix
  have hmove' : (FFModel.zornQ (quasithinG2 K')).act γ m1 * m1⁻¹ =
      (Multiplicative.ofAdd ((0 : K'), ![-1, 1, 0], (0 : Fin 3 → K'), (0 : K')) :
        (FFModel.zornQ (quasithinG2 K')).Amb) := by
    have h2 : (Multiplicative.ofAdd (gAFun perm3 ((0 : K'), ![1, 0, 0], (0 : Fin 3 → K'),
        (0 : K'))) : Multiplicative (quasithinZorn K')) *
          (Multiplicative.ofAdd ((0 : K'), ![1, 0, 0], (0 : Fin 3 → K'), (0 : K')))⁻¹ =
        Multiplicative.ofAdd ((0 : K'), ![-1, 1, 0], (0 : Fin 3 → K'), (0 : K')) := by
      rw [← div_eq_mul_inv, ← ofAdd_sub, hmove]
    exact h2
  have hR : ∀ y : quasithinZorn K', y.2.1 ≠ 0 →
      (Multiplicative.ofAdd y : (FFModel.zornQ (quasithinG2 K')).Amb) ∉
        (FFModel.zornQ (quasithinG2 K')).ker := by
    rintro y hy ⟨c, hc'⟩
    apply hy
    have : y = (c, 0, 0, c) := hc'
    rw [this]
  have hγ3 : γ ^ 3 = 1 := by
    apply Subtype.ext
    have h1 : (g2A (perm3SL : SL3 K')) ^ 3 = 1 := by rw [← map_pow, perm3SL_pow_three, map_one]
    have h2 := congrArg (fun x : ↥(Explicit.cayleyGroup K') =>
      (x : quasithinZorn K' ≃ₗ[K'] quasithinZorn K')) h1
    simpa using h2
  refine ⟨((π γ : ↥H) : MulAut V), (π γ).2, ?_, ?_, ?_⟩
  · have h1 : π γ ^ 3 = 1 := (map_pow π γ 3).symm.trans ((congrArg π hγ3).trans (map_one π))
    rw [← Subgroup.coe_pow, h1]
    rfl
  · exact exists_fixed_class hπ γ (m := m0) (show (0 : K') + 0 = 0 by simp) hfix'
      (hR _ (fun h0 => by simpa using congrFun h0 0))
  · refine exists_moved_class hπ γ (m := m1) (show (0 : K') + 0 = 0 by simp) ?_
    rw [hmove']
    exact hR _ (fun h0 => by simpa using congrFun h0 1)

end Zorn

section Three

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem mem_of_pow_three_eq_one (h : B51Hyp G L) {T : Subgroup (MulAut V)} (hTG : T ≤ G)
    (hT2 : IsPGroup 2 ↥T) {g : MulAut V} (hg : g ∈ L ⊔ T) (hg3 : g ^ 3 = 1) : g ∈ L := by
  obtain ⟨k, hk⟩ := sup_two_pow_mem h hTG hT2 g hg
  have hmod : g ^ 2 ^ k = g ^ (2 ^ k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ k) 3, pow_add, pow_mul, hg3, one_pow, one_mul]
  rw [hmod] at hk
  have h3 : 2 ^ k % 3 ≠ 0 := by
    intro h0
    have : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) this)
    omega
  have hlt : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : 2 ^ k % 3
  · exact absurd rfl h3
  · simpa using hk
  · have : g = (g ^ 2) ^ 2 := by
      rw [← pow_mul]
      calc g = g ^ 3 * g := by rw [hg3, one_mul]
        _ = g ^ (2 * 2) := by rw [← pow_succ]
    rw [this]
    exact L.pow_mem hk 2

theorem exists_order_three_of_case1i (h : B51Hyp G L) {T : Subgroup (MulAut V)}
    (hT : IsSylowTwoOf T G) (hGT : G = L ⊔ T)
    (hmod : (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural G (commV L) (fixV L ⊓ commV L) n) ∨
      G2Natural G (commV L) (fixV L ⊓ commV L) 1) :
    ∃ g ∈ L, g ^ 3 = 1 ∧
      (∃ s ∈ commV L, s ∉ fixV L ⊓ commV L ∧ g s * s⁻¹ ∈ fixV L ⊓ commV L) ∧
      ∃ s ∈ commV L, g s * s⁻¹ ∉ fixV L ⊓ commV L := by
  have hex : ∃ g ∈ G, g ^ 3 = 1 ∧
      (∃ s ∈ commV L, s ∉ fixV L ⊓ commV L ∧ g s * s⁻¹ ∈ fixV L ⊓ commV L) ∧
      ∃ s ∈ commV L, g s * s⁻¹ ∉ fixV L ⊓ commV L := by
    rcases hmod with ⟨n, hn5, hn8, hS⟩ | hG2
    · exact exists_order_three_of_symDn hn5 hn8 hS
    · exact exists_order_three_of_g2 hG2
  obtain ⟨g, hgG, hg3, hfix, hmove⟩ := hex
  have hgLT : g ∈ L ⊔ T := hGT ▸ hgG
  exact ⟨g, mem_of_pow_three_eq_one h hT.1 hT.2.1 hgLT hg3, hg3, hfix, hmove⟩

end Three

end P5

end B5

end CFSG.Quasithin
