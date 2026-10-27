module

public import CFSG.Quasithin.EmptyFaithful.SzN17Perm

public section

namespace CFSG.Quasithin.SzN17

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank CFSG.Quasithin.S153L
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem goodFactor_of_sl2 {H P G : Subgroup Ω} (hP : IsSylowTwoOf P H) (hGH : G ≤ H)
    (hGn : ∀ h ∈ H, ∀ g ∈ G, h * g * h⁻¹ ∈ G) {n : ℕ} {F : Type} [Field F] [Finite F] (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : ↥G ≃* ↥(StatedSL 2 F)) :
    (∃ Z, GoodFactor H P G Z) ∧ CenterTrivial G := by
  have hcard : Nat.card ↥G = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow hF]
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hs : IsSimpleGroup ↥G := by
      have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
      exact e.isSimpleGroup
    have hnp : ¬ (Nat.card ↥G).Prime := by
      refine comp_not_prime_of_four_dvd ?_
      rw [hcard]
      exact Dvd.dvd.mul_right ((pow_dvd_pow 2 h2 : 2 ^ 2 ∣ 2 ^ n)) _
    have := goodFactor_of_simple (H := H) (P := P) hs hnp
    exact ⟨⟨_, this.1⟩, this.2⟩
  · have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    have h6 : Nat.card ↥G = 6 := by rw [hcard]; norm_num
    exact ⟨goodFactor_of_small hP hGH hGn (by rw [h6]),
      centerTrivial_of_card_six h6 (comp_noncomm_of_equiv e (comp_noncomm_sl2 F))⟩

theorem goodFactor_of_sl3 {H P G : Subgroup Ω} {m : ℕ} {F : Type} [Field F] [Finite F]
    (hm1 : 1 ≤ m) (hm : Odd m) (hF : Nat.card F = 2 ^ m) (e : ↥G ≃* ↥(StatedSL 3 F)) :
    (∃ Z, GoodFactor H P G Z) ∧ CenterTrivial G := by
  have hs : IsSimpleGroup ↥G := by
    have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hm
    exact e.isSimpleGroup
  have hnp : ¬ (Nat.card ↥G).Prime := by
    refine comp_not_prime_of_four_dvd ?_
    rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hF, ← pow_mul]
    have h4 : 2 ^ 2 ∣ 2 ^ (m * 3) := pow_dvd_pow 2 (by omega)
    exact Dvd.dvd.mul_right h4 _
  have := goodFactor_of_simple (H := H) (P := P) hs hnp
  exact ⟨⟨_, this.1⟩, this.2⟩

theorem goodFactor_of_image_sl2 {H P G : Subgroup Ω} (hP : IsSylowTwoOf P H) (hGH : G ≤ H)
    (hGn : ∀ h ∈ H, ∀ g ∈ G, h * g * h⁻¹ ∈ G) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) (π : ↥(StatedSL 2 F) →* ↥G) (hπ : Function.Surjective π) :
    ∃ Z, GoodFactor H P G Z := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial F)
      simp [hF] at this
    · exact hn
  have hcard : Nat.card ↥(StatedSL 2 F) = 2 ^ n * (4 ^ n - 1) := R3c.card_statedSL_two_pow hF
  rcases Nat.lt_or_ge 1 n with h2 | h1
  · have hchar : CharP F 2 := R3c.charP_two_of_natCard_eq_two_pow hF
    have h4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    have hsimple : IsSimpleGroup ↥(StatedSL 2 F) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
    rcases hsimple.eq_bot_or_eq_top_of_normal π.ker with hker | hker
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hker
      let e : ↥(StatedSL 2 F) ≃* ↥G := MulEquiv.ofBijective π ⟨hinj, hπ⟩
      have hs : IsSimpleGroup ↥G := e.symm.isSimpleGroup
      have hcardG : Nat.card ↥G = 2 ^ n * (4 ^ n - 1) := by
        rw [← Nat.card_congr e.toEquiv, hcard]
      have hnp : ¬ (Nat.card ↥G).Prime := by
        refine comp_not_prime_of_four_dvd ?_
        rw [hcardG]
        exact Dvd.dvd.mul_right ((pow_dvd_pow 2 h2 : 2 ^ 2 ∣ 2 ^ n)) _
      exact ⟨_, (goodFactor_of_simple (H := H) (P := P) hs hnp).1⟩
    · have hsub : Subsingleton ↥G := by
        refine ⟨fun a b => ?_⟩
        obtain ⟨x, rfl⟩ := hπ a
        obtain ⟨y, rfl⟩ := hπ b
        have hx : x ∈ π.ker := hker ▸ Subgroup.mem_top x
        have hy : y ∈ π.ker := hker ▸ Subgroup.mem_top y
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]
      have h1 : Nat.card ↥G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, inferInstance⟩
      exact goodFactor_of_small hP hGH hGn (by rw [h1]; exact one_dvd _)
  · have hn1 : n = 1 := le_antisymm h1 hn
    subst hn1
    have h6 : Nat.card ↥(StatedSL 2 F) = 6 := by rw [hcard]; norm_num
    refine goodFactor_of_small hP hGH hGn ?_
    have := Subgroup.card_dvd_of_surjective hπ
    rwa [h6] at this

theorem goodFactor_of_factorList {V : Type} [CommGroup V] [Finite V] {H P G : Subgroup (MulAut V)}
    (hP : IsSylowTwoOf P H) (hGH : G ≤ H) (hGn : ∀ h ∈ H, ∀ g ∈ G, h * g * h⁻¹ ∈ G)
    (hf : B56FactorList ↥G) : (∃ Z, GoodFactor H P G Z) ∧ CenterTrivial G := by
  rcases hf with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, hm1, hm, hF, ⟨e⟩⟩
  · exact goodFactor_of_sl2 hP hGH hGn hn hF e
  · obtain ⟨e⟩ := he
    have := goodFactor_of_perm5 hP hGH hGn e
    exact ⟨⟨_, this.1⟩, this.2⟩
  · exact goodFactor_of_sl3 hm1 hm hF e


omit [Finite Ω] in
theorem mem_sup_iff_of_right_le_normalizer {K E : Subgroup Ω} (hE : E ≤ Subgroup.normalizer (K : Set Ω))
    {x : Ω} : x ∈ K ⊔ E ↔ ∃ k ∈ K, ∃ e ∈ E, k * e = x := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K E hE]
  exact Set.mem_mul

omit [Finite Ω] in
theorem mem_of_pow_mem_of_coprime' {C : Subgroup Ω} {x : Ω} {m n : ℕ} (hmn : Nat.Coprime m n)
    (h1 : x ^ m ∈ C) (h2 : x ^ n ∈ C) : x ∈ C := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hmn
  have hx : x = (x ^ m) ^ a * (x ^ n) ^ b := by
    calc x = x ^ (a * m + b * n) := by rw [hab, zpow_one]
      _ = (x ^ m) ^ a * (x ^ n) ^ b := by
        rw [zpow_add, mul_comm a, zpow_mul, mul_comm b, zpow_mul, zpow_natCast, zpow_natCast]
  rw [hx]
  exact C.mul_mem (C.zpow_mem h1 a) (C.zpow_mem h2 b)

omit [Finite Ω] in
theorem pow_mul_mem {K : Subgroup Ω} {k p : Ω} (hk : k ∈ K) (hp : p ∈ Subgroup.normalizer (K : Set Ω))
    (n : ℕ) : ∃ k' ∈ K, (k * p) ^ n = k' * p ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', h⟩ := ih
    have hpn : p ^ n ∈ Subgroup.normalizer (K : Set Ω) := Subgroup.pow_mem _ hp n
    have hconj : p ^ n * k * (p ^ n)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hpn k).1 hk
    refine ⟨k' * (p ^ n * k * (p ^ n)⁻¹), K.mul_mem hk' hconj, ?_⟩
    calc (k * p) ^ (n + 1) = (k * p) ^ n * (k * p) := pow_succ _ _
      _ = k' * p ^ n * (k * p) := by rw [h]
      _ = k' * (p ^ n * k * (p ^ n)⁻¹) * p ^ (n + 1) := by group

omit [Finite Ω] in
theorem digest_of_good_self {H P Z : Subgroup Ω} (hZ : GoodFactor H P H Z) :
    Z ≤ H ∧ Fixed3 H Z ∧ H ≤ perfectCore H ⊔ Z ⊔ P := by
  refine ⟨hZ.le, ?_, hZ.decomp⟩
  rcases hZ.normal with h | h
  · rw [h]; exact fixed3_bot
  · exact fixed3_of_unique (Z₁ := Z) (Z₂ := Z) (fun Q hQ => Or.inl (hZ.unique Q hQ)) h

omit [Finite Ω] in
theorem normal_of_commuting {A B H : Subgroup Ω} (hsup : A ⊔ B = H)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    (∀ h ∈ H, ∀ g ∈ A, h * g * h⁻¹ ∈ A) ∧ (∀ h ∈ H, ∀ g ∈ B, h * g * h⁻¹ ∈ B) := by
  constructor
  · intro h hh g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul hc (hsup ▸ hh)
    have e : a * b * g * (a * b)⁻¹ = a * g * a⁻¹ := by
      have h1 : g * b = b * g := hc g hg b hb
      calc a * b * g * (a * b)⁻¹ = a * (b * g) * b⁻¹ * a⁻¹ := by group
        _ = a * (g * b) * b⁻¹ * a⁻¹ := by rw [h1]
        _ = a * g * a⁻¹ := by group
    rw [e]
    exact A.mul_mem (A.mul_mem ha hg) (A.inv_mem ha)
  · intro h hh g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := S153L.comp_exists_mul hc (hsup ▸ hh)
    have e : a * b * g * (a * b)⁻¹ = b * g * b⁻¹ := by
      have h1 : a * (b * g * b⁻¹) = (b * g * b⁻¹) * a :=
        hc a ha _ (B.mul_mem (B.mul_mem hb hg) (B.inv_mem hb))
      calc a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ := by group
        _ = (b * g * b⁻¹) * a * a⁻¹ := by rw [h1]
        _ = b * g * b⁻¹ := by group
    rw [e]
    exact B.mul_mem (B.mul_mem hb hg) (B.inv_mem hb)

omit [Finite Ω] in
theorem normal_sup_of_zpowers {K₀ P H : Subgroup Ω} {t : Ω} (hH : H = K₀ ⊔ Subgroup.zpowers t)
    (ht : t ∈ Subgroup.normalizer (K₀ : Set Ω)) (hPH : P ≤ H) :
    ∀ h ∈ H, ∀ y ∈ K₀ ⊔ P, h * y * h⁻¹ ∈ K₀ ⊔ P := by
  have hzN : Subgroup.zpowers t ≤ Subgroup.normalizer (K₀ : Set Ω) := Subgroup.zpowers_le.2 ht
  have hHdec : ∀ x ∈ H, ∃ k ∈ K₀, ∃ s ∈ Subgroup.zpowers t, k * s = x := fun x hx =>
    (mem_sup_iff_of_right_le_normalizer hzN).1 (by rw [← hH]; exact hx)
  have hPN : P ≤ Subgroup.normalizer (K₀ : Set Ω) := by
    intro p hp
    obtain ⟨k, hk, s, hs, rfl⟩ := hHdec p (hPH hp)
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk) (hzN hs)
  have hK₀H' : K₀ ≤ K₀ ⊔ P := le_sup_left
  have hzH' : ∀ u ∈ Subgroup.zpowers t, ∀ y ∈ K₀ ⊔ P, u * y * u⁻¹ ∈ K₀ ⊔ P := by
    intro u hu y hy
    obtain ⟨k, hk, p, hp, rfl⟩ := (mem_sup_iff_of_right_le_normalizer hPN).1 hy
    obtain ⟨k₂, hk₂, s, hs, hps⟩ := hHdec p (hPH hp)
    have huK : u * k * u⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.1 (hzN hu) k).1 hk
    have huK₂ : u * k₂ * u⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.1 (hzN hu) k₂).1 hk₂
    have hsu : u * s * u⁻¹ = s := by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
      rw [zpow_mul_comm t a b]
      group
    have e : u * (k * p) * u⁻¹ = ((u * k * u⁻¹) * ((u * k₂ * u⁻¹) * k₂⁻¹)) * p := by
      calc u * (k * p) * u⁻¹ = (u * k * u⁻¹) * (u * p * u⁻¹) := by group
        _ = (u * k * u⁻¹) * (u * (k₂ * s) * u⁻¹) := by rw [hps]
        _ = (u * k * u⁻¹) * ((u * k₂ * u⁻¹) * (u * s * u⁻¹)) := by group
        _ = (u * k * u⁻¹) * ((u * k₂ * u⁻¹) * s) := by rw [hsu]
        _ = ((u * k * u⁻¹) * ((u * k₂ * u⁻¹) * k₂⁻¹)) * p := by rw [← hps]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (K₀.mul_mem huK (K₀.mul_mem huK₂ (K₀.inv_mem hk₂)))) (Subgroup.mem_sup_right hp)
  intro h hh y hy
  obtain ⟨k, hk, s, hs, rfl⟩ := hHdec h hh
  have : k * s * y * (k * s)⁻¹ = k * (s * y * s⁻¹) * k⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK₀H' hk) (hzH' s hs y hy))
    ((K₀ ⊔ P).inv_mem (hK₀H' hk))

theorem le_of_isPGroup_of_normal {H P H' : Subgroup Ω} (hP : IsSylowTwoOf P H) (hPH' : P ≤ H')
    (hnorm : ∀ h ∈ H, ∀ y ∈ H', h * y * h⁻¹ ∈ H') {A : Subgroup Ω} (hAH : A ≤ H)
    (hA : IsPGroup 2 A) : A ≤ H' := by
  intro a ha
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hP hAH hA
  have hhaP : h * a * h⁻¹ ∈ P := hle (mem_cjSub.2 (by
    have : h⁻¹ * (h * a * h⁻¹) * h = a := by group
    rw [this]; exact ha))
  have e : a = h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ := by group
  rw [e]
  exact hnorm h⁻¹ (H.inv_mem hh) _ (hPH' hhaP)

section Cases

variable {V : Type} [CommGroup V] [Finite V]

theorem digest_case1 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case1 H) :
    ∃ Z, Z ≤ H ∧ Fixed3 H Z ∧ H ≤ perfectCore H ⊔ Z ⊔ P := by
  obtain ⟨hq, ⟨⟨-, hcase⟩, -⟩, -⟩ := h
  have hE : quasithinGenFitting H ≤ H := quasithinGenFitting_le H
  have hper : ⁅quasithinGenFitting H, quasithinGenFitting H⁆ = quasithinGenFitting H :=
    comp_perfect_of_isQuasisimple hq
  have hEc : quasithinGenFitting H ≤ perfectCore H := le_perfectCore_of_perfect hE hper
  have hHE : H ≤ quasithinGenFitting H ⊔ P := by
    rcases hcase with ⟨-, -, hT⟩ | ⟨hGL, -⟩ | ⟨n, hGL, -⟩ | ⟨hGL, -⟩
    · rcases hT P hP with h1 | ⟨h1, -⟩
      · exact h1.le.trans le_sup_left
      · exact h1.le
    · exact hGL.le.trans le_sup_left
    · exact hGL.le.trans le_sup_left
    · exact hGL.le.trans le_sup_left
  exact ⟨⊥, bot_le, fixed3_bot, hHE.trans (sup_le (hEc.trans (le_sup_of_le_left le_sup_left)) le_sup_right)⟩

theorem digest_case2 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case2 H) :
    ∃ Z, Z ≤ H ∧ Fixed3 H Z ∧ H ≤ perfectCore H ⊔ Z ⊔ P := by
  obtain ⟨⟨e⟩, -, -⟩ := h
  have h6 : Nat.card ↥H = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨Z, hZ⟩ := goodFactor_of_small hP le_rfl
    (fun h hh g hg => H.mul_mem (H.mul_mem hh hg) (H.inv_mem hh)) (by rw [h6])
  exact ⟨Z, digest_of_good_self hZ⟩

theorem digest_case3 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case3 H) :
    ∃ Z, Z ≤ H ∧ Fixed3 H Z ∧ H ≤ perfectCore H ⊔ Z ⊔ P := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, -⟩ := h
  have hG₁H : G₁ ≤ H := hsup ▸ le_sup_left
  have hG₂H : G₂ ≤ H := hsup ▸ le_sup_right
  obtain ⟨hn₁, hn₂⟩ := normal_of_commuting hsup hc
  obtain ⟨⟨Z₁, hZ₁⟩, hc₁⟩ := goodFactor_of_factorList hP hG₁H hn₁ hf₁
  obtain ⟨⟨Z₂, hZ₂⟩, -⟩ := goodFactor_of_factorList hP hG₂H hn₂ hf₂
  have := digest_of_product hsup hc hinf (Or.inl hc₁) hZ₁ hZ₂
  exact ⟨Z₁ ⊔ Z₂, this.2.2, this.2.1, this.1⟩

theorem digest_case5 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (h : B56Case5 H) :
    ∃ Z, Z ≤ H ∧ Fixed3 H Z ∧ H ≤ perfectCore H ⊔ Z ⊔ P := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, h₂⟩ := h
  have hG₁H : G₁ ≤ H := hsup ▸ le_sup_left
  have hG₂H : G₂ ≤ H := hsup ▸ le_sup_right
  obtain ⟨hn₁, hn₂⟩ := normal_of_commuting hsup hc
  obtain ⟨⟨Z₁, hZ₁⟩, hc₁⟩ := goodFactor_of_sl3 (G := G₁) (P := P) (H := H) (m := 1) (F := ZMod 2)
    le_rfl odd_one (by simp) e₁
  have hG₂ : ∃ Z₂, GoodFactor H P G₂ Z₂ := by
    rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hR⟩
    · exact (goodFactor_of_sl3 (G := G₂) (P := P) (H := H) (m := 1) (F := ZMod 2)
        le_rfl odd_one (by simp) e₂).1
    · exact goodFactor_of_image_sl2 hP hG₂H hn₂ hF π hR.1
  obtain ⟨Z₂, hZ₂⟩ := hG₂
  have := digest_of_product hsup hc hinf (Or.inl hc₁) hZ₁ hZ₂
  exact ⟨Z₁ ⊔ Z₂, this.2.2, this.2.1, this.1⟩


theorem digest_case4 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (hffJ : H = ffJ H)
    (h : B56Case4 H) : ∃ Z, Z ≤ H ∧ Fixed3 H Z ∧ H ≤ perfectCore H ⊔ Z ⊔ P := by
  obtain ⟨G₁, G₂, t, hJt, hinf, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ := h
  have htK₀ : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    InternalSec.mem_normalizer_sup ht₁ ht₂
  have hK₀H : G₁ ⊔ G₂ ≤ H := by rw [hJt]; exact le_sup_left
  have hG₁H : G₁ ≤ H := le_sup_left.trans hK₀H
  have hG₂H : G₂ ≤ H := le_sup_right.trans hK₀H
  have hPH : P ≤ H := hP.1
  have hnormH' := normal_sup_of_zpowers hJt htK₀ hPH
  have hH2 : H ≤ (G₁ ⊔ G₂) ⊔ P := by
    calc H = ffJ H := hffJ
      _ ≤ (G₁ ⊔ G₂) ⊔ P := iSup₂_le fun A hA =>
        le_of_isPGroup_of_normal hP le_sup_right hnormH' hA.1
          (B6.isPGroup_two_of_isElemAbelian2 hA.2.2.1)
  have hs₁ : IsSimpleGroup ↥G₁ := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e₁.isSimpleGroup
  have hnp₁ : ¬ (Nat.card ↥G₁).Prime := by
    rw [Nat.card_congr e₁.toEquiv, card_alternatingGroup1527d 6 (by norm_num)]
    norm_num [Nat.factorial]
  obtain ⟨hgood₁, hcen₁⟩ := goodFactor_of_simple (H := H) (P := P) hs₁ hnp₁
  have hq₁ : CFSG.IsQuasisimple ↥G₁ := comp_quasisimple_of_simple hs₁ hnp₁
  have hperf₁ : ⁅G₁, G₁⁆ = G₁ := comp_perfect_of_isQuasisimple hq₁
  have hG₁core : G₁ ≤ perfectCore H := le_perfectCore_of_perfect hG₁H hperf₁
  have hHN₂ : H ≤ Subgroup.normalizer (G₂ : Set (MulAut V)) := by
    rw [hJt]
    refine sup_le (sup_le (fun a ha => ?_) Subgroup.le_normalizer) (Subgroup.zpowers_le.2 ht₂)
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm)
  have hG₂n : ∀ h ∈ H, ∀ g ∈ G₂, h * g * h⁻¹ ∈ G₂ := fun h hh g hg =>
    (Subgroup.mem_normalizer_iff.1 (hHN₂ hh) g).1 hg
  have hG₂N : IsNormalThree H G₂ := ⟨hG₂H, hG₂n, hc₂⟩
  have hHN : H ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) := by
    rw [hJt]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 htK₀)
  have hPN : P ≤ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup (MulAut V)) : Set (MulAut V)) :=
    hPH.trans hHN
  have hΞ : ∀ Q : Subgroup (MulAut V), IsNormalThree H Q → Q = G₂ ∨ Q = G₂ := by
    intro Q hQ
    left
    obtain ⟨hQH, hQn, hQc⟩ := hQ
    have hQK : Q ≤ G₁ ⊔ G₂ := by
      intro q hq
      obtain ⟨k, hk, p, hp, hkp⟩ := (mem_sup_iff_of_right_le_normalizer hPN).1 (hH2 (hQH hq))
      obtain ⟨m, hm⟩ := hP.2.1 ⟨p, hp⟩
      have hpm : p ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      obtain ⟨k', hk', hpow⟩ := pow_mul_mem hk (hPN hp) (2 ^ m)
      have hq2 : q ^ 2 ^ m ∈ G₁ ⊔ G₂ := by
        rw [← hkp, hpow, hpm, mul_one]; exact hk'
      have hq3 : q ^ 3 = 1 := by
        have h1 : (⟨q, hq⟩ : ↥Q) ^ Nat.card ↥Q = 1 := pow_card_eq_one'
        rw [hQc] at h1
        simpa using congrArg Subtype.val h1
      exact mem_of_pow_mem_of_coprime' (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2))
        (by rw [hq3]; exact one_mem _) hq2
    have hQ' : IsNormalThree (G₁ ⊔ G₂) Q :=
      ⟨hQK, fun x hx q hq => hQn x (hK₀H hx) q hq, hQc⟩
    rcases normalThree_le_factor hc hinf hcen₁ hQ' with hQG₁ | hQG₂
    · exfalso
      have hQbot := hgood₁.unique Q
        ⟨hQG₁, fun x hx q hq => hQn x (hG₁H hx) q hq, hQc⟩
      rw [hQbot, Subgroup.card_bot] at hQc
      omega
    · exact Subgroup.eq_of_le_of_card_ge hQG₂ (by rw [hc₂, hQc])
  refine ⟨G₂, hG₂H, fixed3_of_unique hΞ hG₂N, ?_⟩
  have hK₀core : G₁ ⊔ G₂ ≤ perfectCore H ⊔ G₂ := sup_le (hG₁core.trans le_sup_left) le_sup_right
  exact hH2.trans (sup_le (hK₀core.trans le_sup_left) le_sup_right)

theorem digest_of_b56 {H P : Subgroup (MulAut V)} (hP : IsSylowTwoOf P H) (hffJ : H = ffJ H)
    (hcases : B56Case1 H ∨ B56Case2 H ∨ B56Case3 H ∨ B56Case4 H ∨ B56Case5 H) :
    ∃ Z, Z ≤ H ∧ Fixed3 H Z ∧ H ≤ perfectCore H ⊔ Z ⊔ P := by
  rcases hcases with h | h | h | h | h
  · exact digest_case1 hP h
  · exact digest_case2 hP h
  · exact digest_case3 hP h
  · exact digest_case4 hP hffJ h
  · exact digest_case5 hP h

end Cases

end CFSG.Quasithin.SzN17
