module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCtx
public import CFSG.Quasithin.Background.D2Involutions
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique

section Involution

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem isElemAbelian2_zpowers {a : MulAut W} (ha : a ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers a) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers ha

omit [Finite W] in
theorem rk_commV_eq_two {a : MulAut W} (h : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) :
    rk ↥(commV (Subgroup.zpowers a)) = 2 := by
  unfold rk
  rw [h, padicValNat.prime_pow]

theorem rkIdx_fixV_eq_two {a : MulAut W}
    (h : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) :
    rkIdx (fixV (Subgroup.zpowers a)) = 2 := by
  rw [rkIdx_fixV_zpowers]
  exact rk_commV_eq_two h

omit [Finite W] in
theorem rk_zpowers_eq_one {a : MulAut W} (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1) :
    rk ↥(Subgroup.zpowers a) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  unfold rk
  rw [Nat.card_zpowers, hord, padicValNat_self]

theorem qOf_le_two {X : Subgroup (MulAut W)} {a : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (haX : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (h : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) :
    qOf X ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hr : rAV (Subgroup.zpowers a) ≤ 2 := by
    unfold rAV
    rw [rkIdx_fixV_zpowers, rk_commV_eq_two h, rk_zpowers_eq_one ha1 ha2]
    norm_num
  have hA2 : IsA2 X (Subgroup.zpowers a) :=
    ⟨Subgroup.zpowers_le.mpr haX, fun hb => ha1 (by simpa using (Subgroup.zpowers_eq_bot.mp hb)),
      isElemAbelian2_zpowers ha2⟩
  exact qOf_le_iff.mpr ⟨Subgroup.zpowers a, hA2, isQuadratic_zpowers hW ha2, hr⟩

theorem qhatOf_le_two {X : Subgroup (MulAut W)} {a : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (haX : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (h : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) :
    qhatOf X ≤ ((2 : ℚ) : WithTop ℚ) :=
  (qhatOf_le_qOf X).trans (qOf_le_two hW haX ha1 ha2 h)

theorem mParam_le_two {X : Subgroup (MulAut W)} {a : MulAut W}
    (haX : a ∈ X) (ha1 : a ≠ 1) (ha2 : a ^ 2 = 1)
    (h : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2) : E3.mParam X ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have heven : Even (Nat.card ↥X) := by
    have hd : orderOf (⟨a, haX⟩ : ↥X) ∣ Nat.card ↥X := orderOf_dvd_natCard _
    have hord' : orderOf (⟨a, haX⟩ : ↥X) = 2 := by
      rw [← hord]
      exact Subgroup.orderOf_mk a haX
    rw [hord'] at hd
    exact even_iff_two_dvd.mpr hd
  simp only [E3.mParam, heven, ↓reduceIte]
  exact Nat.sInf_le ⟨a, haX, hord, (rkIdx_fixV_eq_two h).symm⟩

end Involution

section Order3

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def CovOrder3 (J : Subgroup (MulAut W)) : Prop :=
  ∀ w : W, w ≠ 1 → ∃ g ∈ J, orderOf g = 3 ∧ g w = w

variable {G₀ K S : Subgroup (MulAut W)} {a : MulAut W} {z : W}

theorem Ctx1.mem_K_or_mul (h : Ctx1 W G₀ K a S z) {g : MulAut W} (hg : g ∈ G₀) :
    g ∈ K ∨ ∃ k ∈ K, g = k * a := by
  have ha2 : a * a = 1 := by rw [← pow_two]; exact h.a2
  let Q : Subgroup (MulAut W) :=
    { carrier := {g | g ∈ K ∨ ∃ k ∈ K, g = k * a}
      one_mem' := Or.inl K.one_mem
      mul_mem' := by
        rintro x y (hx | ⟨k₁, hk₁, rfl⟩) (hy | ⟨k₂, hk₂, rfl⟩)
        · exact Or.inl (K.mul_mem hx hy)
        · exact Or.inr ⟨x * k₂, K.mul_mem hx hk₂, by group⟩
        · refine Or.inr ⟨k₁ * (a * y * a⁻¹), K.mul_mem hk₁ (h.aN y hy), ?_⟩
          group
        · refine Or.inl ?_
          have e : k₁ * a * (k₂ * a) = k₁ * (a * k₂ * a⁻¹) * (a * a) := by group
          rw [e, ha2, mul_one]
          exact K.mul_mem hk₁ (h.aN k₂ hk₂)
      inv_mem' := by
        rintro x (hx | ⟨k, hk, rfl⟩)
        · exact Or.inl (K.inv_mem hx)
        · refine Or.inr ⟨a * k⁻¹ * a⁻¹, h.aN _ (K.inv_mem hk), ?_⟩
          have e2 : a⁻¹ = a := by
            rw [inv_eq_iff_mul_eq_one]
            exact ha2
          calc (k * a)⁻¹ = a⁻¹ * k⁻¹ := mul_inv_rev k a
            _ = a * k⁻¹ := by rw [e2]
            _ = (a * k⁻¹ * a⁻¹) * a := by group }
  have hle : G₀ ≤ Q := by
    rw [h.G₀eq]
    refine sup_le (fun k hk => Or.inl hk) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr ⟨1, K.one_mem, by group⟩
  exact hle hg

theorem Ctx1.mem_K_of_orderOf_three (h : Ctx1 W G₀ K a S z) {g : MulAut W} (hg : g ∈ G₀)
    (h3 : orderOf g = 3) : g ∈ K := by
  have hsq : g ^ 2 ∈ K := by
    rcases h.mem_K_or_mul hg with hk | ⟨k, hk, rfl⟩
    · exact K.pow_mem hk 2
    · have ha2 : a * a = 1 := by rw [← pow_two]; exact h.a2
      have e : (k * a) ^ 2 = k * (a * k * a⁻¹) * (a * a) := by rw [pow_two]; group
      rw [e, ha2, mul_one]
      exact K.mul_mem hk (h.aN k hk)
  have h4 : g = (g ^ 2) ^ 2 := by
    have h33 : g ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one g
    calc g = g ^ 3 * g := by rw [h33, one_mul]
      _ = (g ^ 2) ^ 2 := by group
  rw [h4]
  exact K.pow_mem hsq 2

theorem Ctx1.false_of_cov (h : Ctx1 W G₀ K a S z) {J : Subgroup (MulAut W)} (hJ : J ≤ G₀)
    (hcov : CovOrder3 J) : False := by
  obtain ⟨g, hg, h3, hgz⟩ := hcov z h.z1
  exact h.three g (h.mem_K_of_orderOf_three (hJ hg) h3) h3 hgz

end Order3

section Centralizer

variable {W : Type} [CommGroup W] [Finite W]

theorem eq_one_of_commute_irr {K : Subgroup (MulAut W)} (hW : ∀ w : W, w ^ 2 = 1)
    (hirr : IsIrrOn153 K ⊤) {c : MulAut W} {e : ℕ} (hc : c ^ 2 ^ e = 1)
    (hcomm : ∀ k ∈ K, k * c = c * k) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    have hdvd : orderOf c ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hc
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hne : (⊤ : Subgroup W) ≠ ⊥ := hirr.1
  obtain ⟨m, -, hm1, hmfix⟩ := B1.exists_fixed_ne_one hW hB
    (M := ⊤) (fun b _ m hm => hm) hne
  have hinv : ∀ k ∈ K, ∀ b ∈ fixV (Subgroup.zpowers c), k b ∈ fixV (Subgroup.zpowers c) := by
    intro k hk b hb x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hcomm' : ∀ i : ℤ, k * c ^ i = c ^ i * k := fun i =>
      ((Commute.zpow_right (show Commute k c from hcomm k hk) i)).eq
    have h1 : (c ^ i) (k b) = k ((c ^ i) b) := by
      have := congrArg (fun g : MulAut W => g b) (hcomm' i)
      simpa using this.symm
    rw [h1, hb (c ^ i) (Subgroup.zpow_mem_zpowers c i)]
  have hfixtop : fixV (Subgroup.zpowers c) = ⊤ := by
    rcases hirr.2.2 (fixV (Subgroup.zpowers c)) le_top hinv with h0 | h0
    · exfalso
      have hmem : m ∈ fixV (Subgroup.zpowers c) := hmfix
      rw [h0] at hmem
      exact hm1 (Subgroup.mem_bot.1 hmem)
    · exact h0
  ext w
  have : w ∈ fixV (Subgroup.zpowers c) := by rw [hfixtop]; exact Subgroup.mem_top w
  exact this c (Subgroup.mem_zpowers c)

end Centralizer

end S153G93D

end CFSG.Quasithin
