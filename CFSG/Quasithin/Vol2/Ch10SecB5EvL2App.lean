module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvPair3
public import CFSG.Quasithin.Vol2.Ch10SecB6Bar

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {t : G}
  {Ψ : ↥(fsuL0 T L) →* L32.Γ × L32.Γ} {c : L32.Γ} {A K E : Subgroup L32.Γ}

theorem not_five_dvd_card_sup (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) {R : Subgroup G}
    (hRT : R ≤ T) : ¬ 5 ∣ Nat.card ↥(XOf T L Ψ A ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set X := XOf T L Ψ A with hXdef
  intro h5
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hy5 : orderOf (y : G) = 5 := by rw [Subgroup.orderOf_coe, hy]
  have hRN : R ≤ Subgroup.normalizer (X : Set G) := hRT.trans (isXi_XOf h hD).2.1
  have hy' : (y : G) ∈ ((X ⊔ R : Subgroup G) : Set G) := y.2
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X R hRN] at hy'
  obtain ⟨x, hx, r, hr, hxr'⟩ := hy'
  have hxr : x * r = (y : G) := hxr'
  obtain ⟨j, hj⟩ := (h.hyp.fsu.sylow.1.to_le hRT) ⟨r, hr⟩
  have hj' : r ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq hx (hRN hr) (2 ^ j)
  rw [hj', mul_one] at hpow
  have hcop : Nat.Coprime (2 ^ j) (orderOf (x * r)) := by
    rw [hxr, hy5]
    exact Nat.Coprime.pow_left j (by norm_num)
  have hmem := A4.mem_zpowers_pow_of_coprime hcop
  rw [hpow] at hmem
  have hyX : (y : G) ∈ X := by rw [← hxr]; exact (Subgroup.zpowers_le.mpr hx') hmem
  have hO := pow_three_mem h hD hyX
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) ⟨_, hO⟩
  have hk' : ((y : G) ^ 3) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have h1 : (y : G) ^ 3 = 1 := by
    have hd1 : orderOf ((y : G) ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf ((y : G) ^ 3) ∣ 5 := by
      rw [← hy5]
      exact orderOf_pow_dvd 3
    have hg : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := Nat.dvd_gcd hd1 hd2
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this
  have := orderOf_dvd_of_pow_eq_one h1
  rw [hy5] at this
  norm_num at this

theorem exists_E9_le_XOf (h : MaxCtx T L I t Ψ c) (hD : ParData A K E) :
    ∃ P : Subgroup G, P ≤ XOf T L Ψ A ∧ Nat.card P = 9 ∧ ∀ x ∈ P, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := XOf T L Ψ A with hXdef
  have hXi := isXi_XOf h hD
  have hrel := relIndex_XOf h hD
  have h3 : 3 ∣ Nat.card X := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := exists_isSylowIn_three X
  refine ⟨P3, hP3.1, by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel], fun x hx => ?_⟩
  have hinf := hP3.inf_pCoreOf_two_eq_bot (by norm_num)
  have hm : x ^ 3 ∈ P3 ⊓ pCoreOf 2 X := ⟨P3.pow_mem hx 3, pow_three_mem h hD (hP3.1 hx)⟩
  rw [hinf] at hm
  exact hm

theorem normalizer_T1_le_XOf_L2q
    (h311 : Theorem311Stmt) (h : MaxCtx T L I t Ψ c)
    (hD : ParData A K E) (hA : A = L32.Pa ∨ A = L32.Pb) {K₁ : Subgroup G} {s : G} (hs : s ∈ T)
    (hK₁ : K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)))
    (hsn : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hK : conjClosure (XOf T L Ψ A)
        (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) =
      K₁ ⊔ CFSG.conjugate K₁ s)
    {m : ℕ} (hme : Even m) (hm : 0 < m) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ m) (e : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.hyp.fsu.simple
  have hKl : LocalSQTK G := (qtkeCore_of_cat h.hyp.fsu.nonabelian h.hyp.fsu.qtke).1
  obtain ⟨hXK, hG₀K, hS⟩ := inGzero_data h (A := A)
  have hH2 := pCoreOf_GA_ne_bot h311 h hD hA
  have hsG₀ : s ∈ Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T) :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right hs)
  have hK₂ : CFSG.conjugate K₁ s ∈
      cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ (preIn Ψ (A.prod A) ⊔ T)) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj s⁻¹) hK₁
    rwa [A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer (Subgroup.inv_mem _ hsG₀))] at h1
  have hne : K₁ ≠ CFSG.conjugate K₁ s := SecA.ne_conjugate hsn
  obtain ⟨e₂⟩ := nonempty_modO2_conjugate K₁ s
  have hm2 : 2 ≤ m := by
    obtain ⟨k, rfl⟩ := hme
    omega
  obtain ⟨φ, hφ, hker, -, -⟩ := exists_pair_prod hKl h.h37 hH2 hK₁ hK₂ hne
    (center_eq_bot_of_mulEquiv hF e) (center_eq_bot_of_mulEquiv hF (e₂.trans e))
  have hNK : Subgroup.normalizer (T1 T L : Set G) ≤
      Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G) := by
    rw [← hK]
    exact le_sup_left.trans hG₀K
  rw [hK] at hXK hS
  have h5 := not_five_dvd_card_sup h hD (R := T ⊓ (K₁ ⊔ CFSG.conjugate K₁ s)) inf_le_left
  have hXN := le_normalizer_of_pair hm2 hm2 hme hme hF hF e (e₂.trans e) hφ hker hS hXK h5
  have hW : pCoreOf 2 (XOf T L Ψ A ⊔ T ⊓ (K₁ ⊔ CFSG.conjugate K₁ s)) =
      T ⊓ (K₁ ⊔ CFSG.conjugate K₁ s) := by
    refine le_antisymm (CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf
      (B6.isSylowTwoOf_mono hS le_sup_right (sup_le hXK hS.1))) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_sup_right
      (sup_le hXN Subgroup.le_normalizer) hS.2.1
  obtain ⟨P3, hP3X, hP3, hP33⟩ := exists_E9_le_XOf h hD
  have hSX : T ⊓ (K₁ ⊔ CFSG.conjugate K₁ s) ≤ Subgroup.normalizer (XOf T L Ψ A : Set G) :=
    inf_le_left.trans (isXi_XOf h hD).2.1
  refine normalizer_T1_le_of_weakClosed h hD hXK hS hNK (fun g _ hg => ?_) fun g hg hg3 => ?_
  · rw [hW] at hg ⊢
    exact Subgroup.eq_of_le_of_card_ge hg
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  · rw [hW] at hg
    exact mem_of_orderOf_three_of_pair hm2 hm2 hme hme hF hF e (e₂.trans e) hφ hker hS hXK h5
      hSX hP3X hP3 hP33 hg hg3

end CFSG.Quasithin.Vol2.Ch10.SecB
