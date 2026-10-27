module

public import CFSG.Quasithin.EmptyFaithful.SBc15F5Def

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace SBc15

namespace F5

section Counting

variable {D : Type} [Group D] [Finite D] {A : Subgroup D}

theorem card_dvd_four_of_isPGroup (hA : Nat.card A = 60) {V : Subgroup D} (hVA : V ≤ A)
    (hV : IsPGroup 2 V) : Nat.card V ∣ 4 := by
  obtain ⟨n, hn⟩ := hV.exists_card_eq
  have hd : 2 ^ n ∣ 60 := by
    have := Subgroup.card_dvd_of_le hVA
    rwa [hn, hA] at this
  have hn2 : n ≤ 2 := by
    by_contra h
    have h8 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h8.trans hd
    omega
  rw [hn]
  exact (pow_dvd_pow 2 hn2 : 2 ^ n ∣ 2 ^ 2)

theorem three_dvd_of_nine_dvd_mul {m n : ℕ} (hm : m ∣ 12) (hn : n ∣ 12) (h : 9 ∣ m * n) :
    3 ∣ m ∧ 3 ∣ n := by
  have hm' : m ≤ 12 := Nat.le_of_dvd (by norm_num) hm
  have hn' : n ≤ 12 := Nat.le_of_dvd (by norm_num) hn
  interval_cases m <;> interval_cases n <;> omega

omit [Finite D] in
theorem card_dvd_twelve (hA : Nat.card A = 60) {Y : Subgroup D} (hYA : Y ≤ A) {a : ℕ}
    (hY : Nat.card Y ∣ 9 * 2 ^ a) : Nat.card Y ∣ 12 := by
  have h60 : Nat.card Y ∣ 60 := by
    have := Subgroup.card_dvd_of_le hYA
    rwa [hA] at this
  have h5 : ¬ 5 ∣ Nat.card Y := by
    intro h
    have h' := h.trans hY
    have hp : Nat.Prime 5 := by norm_num
    rcases (Nat.Prime.dvd_mul hp).mp h' with h9 | h2
    · omega
    · have := hp.dvd_of_dvd_pow h2
      omega
  have hcop : Nat.Coprime (Nat.card Y) 5 :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr h5).symm
  exact hcop.dvd_of_dvd_mul_right (by simpa using h60)

omit [Finite D] in
theorem card_prod_subgroup {N : Type} [Group N] (H : Subgroup D) (K : Subgroup N) :
    Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod]

end Counting

end F5

section Prod

open F5

variable {D : Type} [Group D] [Finite D] {A : Subgroup D}

theorem weakClosure_prod (hA : A5Facts D A) {U X : Subgroup (D × D)} {k : D × D}
    (hUA : U ≤ A.prod A) (hU2 : IsPGroup 2 U) (hU16 : Nat.card U = 16)
    (hXA : X ≤ A.prod A) (hUX : ∀ u ∈ U, ∀ x ∈ X, u * x * u⁻¹ ∈ X) (hO : oTwoUpper X = X)
    (h9 : ∃ a : ℕ, Nat.card X = 9 * 2 ^ a) (hk : k ∈ A.prod A)
    (hkU : ∀ w ∈ pCoreOf 2 (X ⊔ U), k * w * k⁻¹ ∈ U) : k ∈ X ⊔ U := by
  obtain ⟨a, ha⟩ := h9
  have hA60 := hA.card_A
  set V₁ : Subgroup D := U.map (MonoidHom.fst D D) with hV₁
  set V₂ : Subgroup D := U.map (MonoidHom.snd D D) with hV₂
  have hV₁A : V₁ ≤ A := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hUA hu).1
  have hV₂A : V₂ ≤ A := by
    rintro _ ⟨u, hu, rfl⟩
    exact (hUA hu).2
  have hV₁d := card_dvd_four_of_isPGroup hA60 hV₁A (hU2.map (MonoidHom.fst D D))
  have hV₂d := card_dvd_four_of_isPGroup hA60 hV₂A (hU2.map (MonoidHom.snd D D))
  have hV₁le : Nat.card V₁ ≤ 4 := Nat.le_of_dvd (by norm_num) hV₁d
  have hV₂le : Nat.card V₂ ≤ 4 := Nat.le_of_dvd (by norm_num) hV₂d
  have hUV : U ≤ V₁.prod V₂ := fun u hu =>
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_map_of_mem _ hu, Subgroup.mem_map_of_mem _ hu⟩
  have hprodV : Nat.card (V₁.prod V₂) = Nat.card V₁ * Nat.card V₂ := card_prod_subgroup V₁ V₂
  have h16le : 16 ≤ Nat.card V₁ * Nat.card V₂ := by
    have := Subgroup.card_le_of_le hUV
    rwa [hprodV, hU16] at this
  have hV₁4 : Nat.card V₁ = 4 := by
    by_contra hne
    have : Nat.card V₁ ≤ 3 := by omega
    nlinarith
  have hV₂4 : Nat.card V₂ = 4 := by
    by_contra hne
    have : Nat.card V₂ ≤ 3 := by omega
    nlinarith
  have hUeq : U = V₁.prod V₂ :=
    Subgroup.eq_of_le_of_card_ge hUV (by rw [hprodV, hV₁4, hV₂4, hU16])
  set Y₁ : Subgroup D := X.map (MonoidHom.fst D D) with hY₁
  set Y₂ : Subgroup D := X.map (MonoidHom.snd D D) with hY₂
  have hY₁A : Y₁ ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hXA hx).1
  have hY₂A : Y₂ ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hXA hx).2
  have hXY : X ≤ Y₁.prod Y₂ := fun x hx =>
    Subgroup.mem_prod.mpr ⟨Subgroup.mem_map_of_mem _ hx, Subgroup.mem_map_of_mem _ hx⟩
  have hVY₁ : ∀ v ∈ V₁, ∀ y ∈ Y₁, v * y * v⁻¹ ∈ Y₁ := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨u * x * u⁻¹, hUX u hu x hx, by simp⟩
  have hVY₂ : ∀ v ∈ V₂, ∀ y ∈ Y₂, v * y * v⁻¹ ∈ Y₂ := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨x, hx, rfl⟩
    exact ⟨u * x * u⁻¹, hUX u hu x hx, by simp⟩
  have hOY₁ : oTwoUpper Y₁ = Y₁ := by rw [hY₁, oTwoUpper_map, hO]
  have hOY₂ : oTwoUpper Y₂ = Y₂ := by rw [hY₂, oTwoUpper_map, hO]
  have hX9 : 9 ∣ Nat.card X := ⟨2 ^ a, ha⟩
  have hY₁12 : Nat.card Y₁ ∣ 12 :=
    card_dvd_twelve hA60 hY₁A (ha ▸ Subgroup.card_map_dvd (MonoidHom.fst D D) (H := X))
  have hY₂12 : Nat.card Y₂ ∣ 12 :=
    card_dvd_twelve hA60 hY₂A (ha ▸ Subgroup.card_map_dvd (MonoidHom.snd D D) (H := X))
  have hprodY : Nat.card (Y₁.prod Y₂) = Nat.card Y₁ * Nat.card Y₂ := card_prod_subgroup Y₁ Y₂
  have h3Y : 3 ∣ Nat.card Y₁ ∧ 3 ∣ Nat.card Y₂ := by
    have h9Y : 9 ∣ Nat.card Y₁ * Nat.card Y₂ := by
      rw [← hprodY]
      exact hX9.trans (Subgroup.card_dvd_of_le hXY)
    exact three_dvd_of_nine_dvd_mul hY₁12 hY₂12 h9Y
  obtain ⟨B₁, hB₁c, hB₁N, hB₁A, hB₁Y, hB₁comm⟩ := hA.exists_normalizer V₁ hV₁A hV₁4
  obtain ⟨B₂, hB₂c, hB₂N, hB₂A, hB₂Y, hB₂comm⟩ := hA.exists_normalizer V₂ hV₂A hV₂4
  have hYB₁ : Y₁ = B₁ := hB₁Y Y₁ hY₁A hVY₁ hOY₁ h3Y.1 hY₁12
  have hYB₂ : Y₂ = B₂ := hB₂Y Y₂ hY₂A hVY₂ hOY₂ h3Y.2 hY₂12
  have hfst : ∀ w ∈ V₁, ((w, 1) : D × D) ∈ X := by
    intro w hw
    have h3 : 3 ∣ Nat.card B₁ := by rw [hB₁c]; norm_num
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have haB : (a' : D) ∈ B₁ := a'.2
    have haY : (a' : D) ∈ Y₁ := hYB₁ ▸ haB
    obtain ⟨x, hx, hxa⟩ := haY
    have hao : orderOf (a' : D) = 3 := by rw [Subgroup.orderOf_coe]; exact ha'
    obtain ⟨v, hv, hvw⟩ := hB₁comm (a' : D) haB hao w hw
    have hvU : ((v, 1) : D × D) ∈ U := by
      rw [hUeq]
      exact Subgroup.mem_prod.mpr ⟨hv, one_mem _⟩
    have hmem := X.mul_mem (hUX _ hvU x hx) (X.inv_mem hx)
    have heq : ((v, 1) : D × D) * x * (v, 1)⁻¹ * x⁻¹ = (w, 1) := by
      ext
      · simp only [Prod.fst_mul, Prod.fst_inv]
        rw [← hvw]
        simp only [MonoidHom.coe_fst] at hxa
        rw [hxa]
      · simp
    rwa [heq] at hmem
  have hsnd : ∀ w ∈ V₂, ((1, w) : D × D) ∈ X := by
    intro w hw
    have h3 : 3 ∣ Nat.card B₂ := by rw [hB₂c]; norm_num
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨a', ha'⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have haB : (a' : D) ∈ B₂ := a'.2
    have haY : (a' : D) ∈ Y₂ := hYB₂ ▸ haB
    obtain ⟨x, hx, hxa⟩ := haY
    have hao : orderOf (a' : D) = 3 := by rw [Subgroup.orderOf_coe]; exact ha'
    obtain ⟨v, hv, hvw⟩ := hB₂comm (a' : D) haB hao w hw
    have hvU : ((1, v) : D × D) ∈ U := by
      rw [hUeq]
      exact Subgroup.mem_prod.mpr ⟨one_mem _, hv⟩
    have hmem := X.mul_mem (hUX _ hvU x hx) (X.inv_mem hx)
    have heq : ((1, v) : D × D) * x * (1, v)⁻¹ * x⁻¹ = (1, w) := by
      ext
      · simp
      · simp only [Prod.snd_mul, Prod.snd_inv]
        rw [← hvw]
        simp only [MonoidHom.coe_snd] at hxa
        rw [hxa]
    rwa [heq] at hmem
  have hUX' : U ≤ X := by
    intro u hu
    rw [hUeq] at hu
    obtain ⟨h1, h2⟩ := Subgroup.mem_prod.mp hu
    have hu' : u = (u.1, 1) * (1, u.2) := by simp
    rw [hu']
    exact X.mul_mem (hfst _ h1) (hsnd _ h2)
  have hprodB : Nat.card (B₁.prod B₂) = 144 := by
    rw [card_prod_subgroup, hB₁c, hB₂c]
  have hXB : X ≤ B₁.prod B₂ := by
    rw [← hYB₁, ← hYB₂]
    exact hXY
  have hX144 : Nat.card X = 144 := by
    have h16X : 16 ∣ Nat.card X := by
      have := Subgroup.card_dvd_of_le hUX'
      rwa [hU16] at this
    have hXd : Nat.card X ∣ 144 := by
      have := Subgroup.card_dvd_of_le hXB
      rwa [hprodB] at this
    have h144 : 16 * 9 ∣ Nat.card X :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h16X hX9
    exact Nat.dvd_antisymm hXd (by simpa using h144)
  have hXeq : X = B₁.prod B₂ :=
    Subgroup.eq_of_le_of_card_ge hXB (by rw [hprodB, hX144])
  have hsup : X ⊔ U = X := sup_eq_left.mpr hUX'
  have hUpc : U ≤ pCoreOf 2 (X ⊔ U) := by
    rw [hsup]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUX' ?_ hU2
    intro x hx
    apply A4.mem_normalizer_of_conj_mem
    intro u hu
    rw [hXeq] at hx
    rw [hUeq] at hu ⊢
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.mp hx
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.mp hu
    exact Subgroup.mem_prod.mpr ⟨hB₁N _ hx1 _ hu1, hB₂N _ hx2 _ hu2⟩
  have hkU' : ∀ u ∈ U, k * u * k⁻¹ ∈ U := fun u hu => hkU u (hUpc hu)
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.mp hk
  have hk1B : k.1 ∈ B₁ := by
    refine hB₁A _ hk1 fun v hv => ?_
    have hvU : ((v, 1) : D × D) ∈ U := by
      rw [hUeq]
      exact Subgroup.mem_prod.mpr ⟨hv, one_mem _⟩
    have := hkU' _ hvU
    rw [hUeq] at this
    simpa using (Subgroup.mem_prod.mp this).1
  have hk2B : k.2 ∈ B₂ := by
    refine hB₂A _ hk2 fun v hv => ?_
    have hvU : ((1, v) : D × D) ∈ U := by
      rw [hUeq]
      exact Subgroup.mem_prod.mpr ⟨one_mem _, hv⟩
    have := hkU' _ hvU
    rw [hUeq] at this
    simpa using (Subgroup.mem_prod.mp this).2
  have hkX : k ∈ X := by
    rw [hXeq]
    exact Subgroup.mem_prod.mpr ⟨hk1B, hk2B⟩
  exact Subgroup.mem_sup_left hkX

end Prod

end SBc15

end CFSG.Quasithin
