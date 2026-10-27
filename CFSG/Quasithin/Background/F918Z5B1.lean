module

public import CFSG.Quasithin.Background.F918Z5ATensor
public import CFSG.Quasithin.Background.F918Z5BDens
public import CFSG.Quasithin.Background.F918Z5BMat
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.SqModel

open CFSG.Assembly.LowTwoRank
open scoped Matrix

theorem det_eq_one_of_isPerfect {G : Type*} [Group G] [Group.IsPerfect G] {F : Type}
    [Field F] {n : ℕ} (f : G →* Matrix.GeneralLinearGroup (Fin n) F) (g : G) :
    ((f g : Matrix.GeneralLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
  have hs : Subsingleton (Matrix.GeneralLinearGroup.det.comp f).range := by
    have : Group.IsPerfect (Matrix.GeneralLinearGroup.det.comp f).range :=
      Group.IsPerfect.range _
    infer_instance
  have h : (Matrix.GeneralLinearGroup.det.comp f) g = 1 := by
    have := hs.elim ⟨_, g, rfl⟩ (1 : ↥(Matrix.GeneralLinearGroup.det.comp f).range)
    exact congrArg Subtype.val this
  have := congrArg (fun u : Fˣ => (u : F)) h
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using this

section CharTwo

variable {K : Type} [Field K]

theorem mem_statedSL_of_det_eq_one {n : ℕ} {A : Matrix.GeneralLinearGroup (Fin n) K}
    (h : (A : Matrix (Fin n) (Fin n) K).det = 1) : A ∈ StatedSL n K :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

theorem statedScalars_subgroupOf_eq_bot [CharP K 2] :
    (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

theorem nonempty_statedProj_mulEquiv_sl [CharP K 2] :
    Nonempty (StatedProj (StatedSL 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_eq_bot (K := K))).trans
    QuotientGroup.quotientBot).trans (specialLinearGroupEquivStatedSL 2 K).symm⟩

theorem card_specialLinearGroup_two [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem charP_two_of_card_eq_two_pow [Finite K] {n : ℕ} (hn : n ≠ 0) (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  have h0 : ((2 ^ n : ℕ) : K) = 0 := by
    have h := FiniteField.cast_card_eq_zero K
    rwa [← Nat.card_eq_fintype_card, hK] at h
  rw [Nat.cast_pow] at h0
  exact pow_eq_zero_iff hn |>.mp h0

end CharTwo

section Orders

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem pow_card_sub_one_or_add_one_of_odd (y : Matrix.SpecialLinearGroup (Fin 2) K) {m : ℕ}
    (hm : Odd m) (hy : y ^ m = 1) :
    y ^ (Nat.card K - 1) = 1 ∨ y ^ (Nat.card K + 1) = 1 := by
  have := Fintype.ofFinite K
  have hA : (y : Matrix (Fin 2) (Fin 2) K) ^ m = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hy]
    rfl
  have hnk : (m : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    exact fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
  rw [Nat.card_eq_fintype_card]
  rcases CFSG.LinearAlgebra.pow_card_sub_one_or_pow_card_add_one _ y.2 hA hnk with h | h
  · left
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact h
  · right
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    exact h

theorem sq_eq_one_of_even_orderOf {F : Type} [Field F] [CharP F 2] {G : Type*} [Group G]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) F) (hinj : Function.Injective ρ)
    (hdet : ∀ g, ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1)
    (g : G) (hfin : orderOf g ≠ 0) (heven : Even (orderOf g)) :
    ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  obtain ⟨k, hk⟩ := heven
  have hk0 : k ≠ 0 := by omega
  have hmat : ∀ j : ℕ, ((ρ (g ^ j) : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) ^ j := fun j => by
    rw [map_pow, Units.val_pow_eq_pow_val]
  refine mul_self_eq_one_of_commute_involution _ ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) ^
    k : Matrix (Fin 2) (Fin 2) F) (hdet g) ?_ ?_ ?_
  · rw [← pow_add, ← hk, ← hmat, pow_orderOf_eq_one, map_one]
    rfl
  · intro h
    have h1 : ρ (g ^ k) = 1 := by
      apply Units.ext
      rw [hmat]
      exact h
    exact pow_ne_one_of_lt_orderOf hk0 (by omega) (hinj (h1.trans (map_one ρ).symm))
  · exact (Commute.refl _).pow_right k |>.eq

end Orders

theorem trace_pow_eq_trace {G : Type*} [Group G] {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) K₀) {n : ℕ} (hn : Nat.card K₀ = 2 ^ n)
    {F : Type} [Field F] [CharP F 2] (ρ : G →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hinj : Function.Injective ρ)
    (hdet : ∀ g, ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1)
    (g : G) :
    ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace ^ 2 ^ n =
      ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  have : Finite G := Finite.of_equiv _ e.symm.toEquiv
  have hfin : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine trace_pow_two_pow_eq n _ (hdet g) ?_
  rcases Nat.even_or_odd (orderOf g) with heven | hodd
  · exact Or.inl (sq_eq_one_of_even_orderOf ρ hinj hdet g hfin heven)
  · right
    have hy : (e g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hmat : ∀ j : ℕ, ((ρ (g ^ j) : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) ^ j := fun j => by
      rw [map_pow, Units.val_pow_eq_pow_val]
    have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rcases pow_card_sub_one_or_add_one_of_odd (e g) hodd hy with h | h
    · left
      rw [hn] at h
      have h1 : g ^ (2 ^ n - 1) = 1 := e.injective (by rw [map_pow, h, map_one])
      have h2 : ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^
          (2 ^ n - 1) = 1 := by
        rw [← hmat, h1, map_one]
        rfl
      calc ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^ 2 ^ n
          = ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^
            (2 ^ n - 1) * ((ρ g : Matrix.GeneralLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) := by rw [← pow_succ, Nat.sub_add_cancel hq]
        _ = _ := by rw [h2, one_mul]
    · right
      rw [hn] at h
      have h1 : g ^ (2 ^ n + 1) = 1 := e.injective (by rw [map_pow, h, map_one])
      rw [← pow_succ, ← hmat, h1, map_one]
      rfl

section Main

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)}

theorem closure_range_rho_eq_top {F : Type} [Field F] {d r : ℕ}
    {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)}
    {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F} (hd : 0 < d) (hM : IsMatModel D X β ρ σ) :
    AddSubgroup.closure (Set.range fun g : ↥D =>
      ((ρ g : Matrix.GeneralLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)) = ⊤ := by
  refine closure_eq_top_of_irr_of_comm hd ⟨1, by simp⟩ ?_ ?_ ?_
  · rintro _ ⟨g, rfl⟩ _ ⟨h, rfl⟩
    exact ⟨g * h, by simp⟩
  · intro W hW
    exact hM.I_irr W fun g w hw => hW _ ⟨g, rfl⟩ w hw
  · intro φ hφ
    exact hM.comm_F φ fun g w => hφ _ ⟨g, rfl⟩ w

variable {F : Type} [Field F] [Finite F] [CharP F 2]
  {β : V ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F)}
  {ρ : ↥D →* Matrix.GeneralLinearGroup (Fin 2) F}
  {σ : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F}

theorem card_le_two_pow (hM : IsMatModel D X β ρ σ) (hperfD : Group.IsPerfect ↥D)
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (e : ↥D ≃* Matrix.SpecialLinearGroup (Fin 2) K₀) {n : ℕ} (hn : Nat.card K₀ = 2 ^ n)
    (hn1 : n ≠ 0) : Nat.card F ≤ 2 ^ n := by
  have := hperfD
  have hinj := hM.rho_injective
  have hdet := det_eq_one_of_isPerfect ρ
  have hdens := closure_range_rho_eq_top (by norm_num) hM
  have htr : ∀ A : Matrix (Fin 2) (Fin 2) F, A.trace ^ 2 ^ n = A.trace := by
    intro A
    refine trace_pow_eq_of_mem_closure n ?_ A (by rw [hdens]; trivial)
    rintro _ ⟨g, rfl⟩
    exact trace_pow_eq_trace e hn ρ hinj hdet g
  have hf : ∀ f : F, f ^ 2 ^ n = f := fun f => by
    have := htr !![f, 0; 0, 0]
    simpa using this
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  exact card_le_of_pow_eq_self (Nat.one_lt_two_pow hn1) hf

theorem card_eq_two_pow (hM : IsMatModel D X β ρ σ) (hperfD : Group.IsPerfect ↥D)
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    (e : ↥D ≃* Matrix.SpecialLinearGroup (Fin 2) K₀) {n : ℕ} (hn : Nat.card K₀ = 2 ^ n)
    (hn1 : n ≠ 0) : Nat.card F = 2 ^ n := by
  have := hperfD
  have hle := card_le_two_pow hM hperfD e hn hn1
  have hinj := hM.rho_injective
  have hdet := det_eq_one_of_isPerfect ρ
  have hD : Nat.card ↥D = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_specialLinearGroup_two, hn]
  have hρ' : Nat.card ↥D ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    refine Nat.card_le_card_of_injective (fun g => ⟨(ρ g : Matrix (Fin 2) (Fin 2) F), hdet g⟩) ?_
    intro g h hgh
    apply hinj
    apply Units.ext
    exact congrArg Subtype.val hgh
  rw [hD, card_specialLinearGroup_two] at hρ'
  by_contra hne
  have hlt : Nat.card F < 2 ^ n := lt_of_le_of_ne hle hne
  have hq2 : 1 < Nat.card F := Finite.one_lt_card
  have h3 : Nat.card F ^ 2 - 1 < (2 ^ n) ^ 2 - 1 := by
    have h4 : Nat.card F ^ 2 < (2 ^ n) ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
    have h5 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have := Nat.mul_lt_mul_of_lt_of_lt hlt h3
  omega

theorem matModel_two_equiv (hM : IsMatModel D X β ρ σ) (hperfD : Group.IsPerfect ↥D)
    (hperfX : Group.IsPerfect ↥X) {n₀ : ℕ} (hD : IsPSL 2 2 n₀ ↥D)
    (hXD : Nonempty (↥D ≃* ↥X)) :
    Nat.card F = 2 ^ n₀ ∧ ρ.range = StatedSL 2 F ∧ σ.range = StatedSL 2 F := by
  obtain ⟨⟨-, hn1, -⟩, K₀, _, _, hK₀, ⟨e₀⟩⟩ := hD
  have hn1' : n₀ ≠ 0 := by omega
  have : CharP K₀ 2 := charP_two_of_card_eq_two_pow hn1' hK₀
  obtain ⟨e₁⟩ := nonempty_statedProj_mulEquiv_sl (K := K₀)
  have hcard := card_eq_two_pow hM hperfD (e₀.trans e₁) hK₀ hn1'
  have hDcard : Nat.card ↥D = Nat.card ↥(StatedSL 2 F) := by
    rw [Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv.symm,
      card_specialLinearGroup_two, Nat.card_congr (e₀.trans e₁).toEquiv,
      card_specialLinearGroup_two, hK₀, hcard]
  refine ⟨hcard, ?_, ?_⟩
  · have := hperfD
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact mem_statedSL_of_det_eq_one (det_eq_one_of_isPerfect ρ g)
    · rw [Nat.card_congr (MonoidHom.ofInjective hM.rho_injective).toEquiv.symm, hDcard]
  · have := hperfX
    obtain ⟨eXD⟩ := hXD
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact mem_statedSL_of_det_eq_one (det_eq_one_of_isPerfect σ x)
    · rw [Nat.card_congr (MonoidHom.ofInjective hM.sigma_injective).toEquiv.symm,
        ← Nat.card_congr eXD.toEquiv, hDcard]

end Main

end CFSG.Quasithin.SqModel
