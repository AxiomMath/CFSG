module

public import CFSG.Quasithin.Background.D2Tools
public import CFSG.Quasithin.EmptyFaithful.S153Ofour
public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace S152N

section Offender

variable {V : Type*} [CommGroup V] [Finite V]

theorem rk_of_mem_Qset (hV : ∀ v : V, v ^ 2 = 1) (hrk : rk V = 4) {X D : Subgroup (MulAut V)}
    (hq : (2 : WithTop ℚ) ≤ qOf X) (hD : D ∈ Qset X) : rk D = 1 ∧ rk (commV D) = 2 := by
  obtain ⟨⟨hA2, hr⟩, hc⟩ := hD
  have h2 : (2 : ℚ) ≤ rAV D := by
    have := le_kq_iff.mp (by simpa [qOf] using hq : ((2 : ℚ) : WithTop ℚ) ≤ kq X 2) D hA2 hc
    exact this
  have hrAV : rAV D = 2 := le_antisymm hr h2
  have hmul := hA2.rAV_mul
  rw [hrAV] at hmul
  have hmul' : 2 * rk D = rkIdx (fixV D) := by exact_mod_cast hmul
  have hDp : IsPGroup 2 D := hA2.isElemAbelian2.isPGroup
  have hfix := rk_fixV_pos_of_isPGroup_two hV hDp (by omega)
  have hsum := rk_add_rkIdx (fixV D)
  have hpos := hA2.rk_pos
  have hrk1 : rk D = 1 := by omega
  refine ⟨hrk1, ?_⟩
  have hcard : Nat.card D = 2 := by
    rw [card_eq_two_pow_of_isPGroup hDp, hrk1, pow_one]
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ D, d ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA2.ne_bot ((Subgroup.eq_bot_iff_forall _).mpr hcon)
  have hDd : D = Subgroup.zpowers d := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hd) ?_).symm
    rw [hcard, Nat.card_zpowers]
    have : orderOf d ≠ 1 := fun h => hd1 (orderOf_eq_one_iff.mp h)
    have : 0 < orderOf d := orderOf_pos d
    omega
  rw [hDd, ← rkIdx_fixV_zpowers d, ← hDd]
  omega

end Offender


section GroupTheory

variable {Γ : Type*} [Group Γ]

theorem eq_of_card_le_two [Finite Γ] {S : Subgroup Γ} (hS : Nat.card S ≤ 2) {a b : Γ}
    (ha : a ∈ S) (hb : b ∈ S) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  by_contra hne
  have hinj : Function.Injective (![(1 : S), ⟨a, ha⟩, ⟨b, hb⟩] : Fin 3 → S) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Subtype.ext_iff, eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem card_le_two_of_dvd [Finite Γ] {S : Subgroup Γ} (hS : IsPGroup 2 S) {n : ℕ}
    (hn : Nat.card S ∣ n) (h4 : ¬ 4 ∣ n) : Nat.card S ≤ 2 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    have : k ≤ 1 := by omega
    have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  apply h4
  refine dvd_trans ?_ (hk ▸ hn)
  exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)

theorem comm_of_card_le_four [Finite Γ] {S : Subgroup Γ} (hS : IsPGroup 2 S)
    (hc : Nat.card S ≤ 4) : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hk2 : k ≤ 2 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have key : IsMulCommutative S := by
    interval_cases k
    · have : Subsingleton S := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have : IsCyclic S := isCyclic_of_prime_card (p := 2) (by simpa using hk)
      infer_instance
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hk
  intro a ha b hb
  have := mul_comm' (⟨a, ha⟩ : S) ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem involution_mem_of_normal [Finite Γ] {M0 Mb Tb : Subgroup Γ} (hsyl : IsSylowTwoOf Tb Mb)
    (hM0 : M0 ≤ Mb) (hnorm : ∀ g ∈ Mb, ∀ y ∈ M0, g * y * g⁻¹ ∈ M0)
    (huniq : ∀ a ∈ Tb, ∀ b ∈ Tb, a ^ 2 = 1 → b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b)
    {u : Γ} (hu : u ∈ M0) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) {x : Γ} (hx : x ∈ Tb) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : x ∈ M0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hu2 hu1, pow_one])
  obtain ⟨S, hS, hPS⟩ := A4.exists_isSylowTwoOf_ge (P := Subgroup.zpowers u) (H := Mb)
    (Subgroup.zpowers_le.mpr (hM0 hu)) hP
  obtain ⟨h, hh, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hS hsyl
  have hmem : h * u * h⁻¹ ∈ Tb := by
    rw [hconj]
    simpa [mul_assoc] using hPS (Subgroup.mem_zpowers u)
  have hsq : (h * u * h⁻¹) ^ 2 = 1 := by rw [conj_pow, hu2]; simp
  have hne : h * u * h⁻¹ ≠ 1 := by
    intro h1
    apply hu1
    simpa using h1
  have := huniq _ hmem x hx hsq hx2 hne hx1
  rw [← this]
  exact hnorm h hh u hu

end GroupTheory

section Omega

variable {W : Type*} [CommGroup W] [Finite W]

theorem comm_of_isOmegaFourPlus (hexp : ∀ w : W, w * w = 1) {X : Subgroup (MulAut W)}
    (hX : IsOmegaFourPlus X) {P : Subgroup (MulAut W)} (hPX : P ≤ X) (hP : IsPGroup 2 P) :
    ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  obtain ⟨hcard, q, hq, hn, hp, hmem⟩ := hX
  obtain ⟨L₁, L₂, t, hS, -⟩ := exists_ofourStruct_of_plusType hexp hcard hq hn hp
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact hexp w
  have hrkW : rk W = 4 := by
    have h1 := card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW2)
    rw [hcard] at h1
    have : (2 : ℕ) ^ rk W = 2 ^ 4 := by omega
    exact Nat.pow_right_injective (le_refl 2) this
  have hPY : P ≤ orthogonalGroupOf q := fun g hg => ((hmem g).mp (hPX hg)).1
  obtain ⟨S, hSyl, hPS⟩ := A4.exists_isSylowTwoOf_ge hPY hP
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts hSyl
  have hs₁S : s₁ ∈ S := hF.sylow.s₁_mem_S.1
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hodd : ¬ Even (rk (commV (Subgroup.zpowers s₁))) := by
    have hsum := rk_commV_add_rk_fixV s₁
    set F := fixV (Subgroup.zpowers s₁) with hFdef
    have hU₂F : commV L₂ ≤ F := by
      intro u hu
      exact mem_fixV_zpowers_iff.mpr (hS.L₁_fix₂ hs₁L hu)
    have ha₁F : a₁ ∈ F := mem_fixV_zpowers_iff.mpr
      ((hF.sylow.fix₁ a₁ hF.sylow.a₁_mem).mpr (Or.inr rfl))
    have ha₁U₂ : a₁ ∉ commV L₂ := by
      intro h2
      have : a₁ ∈ commV L₁ ⊓ commV L₂ := ⟨hF.sylow.a₁_mem, h2⟩
      rw [hS.inf, Subgroup.mem_bot] at this
      exact hF.sylow.a₁_ne this
    have hcardU₂ : Nat.card (commV L₂) = 4 := hS.symm.card_U₁
    have hlt : Nat.card (commV L₂) < Nat.card F := by
      by_contra hcon
      exact ha₁U₂ ((Subgroup.eq_of_le_of_card_ge hU₂F (not_lt.mp hcon)) ▸ ha₁F)
    have hFcard := card_eq_two_pow hW2 F
    have hrkF3 : 3 ≤ rk F := by
      by_contra h
      have : 2 ^ rk F ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hne : rk (commV (Subgroup.zpowers s₁)) ≠ 0 := by
      intro h0
      have hbot : commV (Subgroup.zpowers s₁) = ⊥ := (rk_eq_zero_iff hW2).mp h0
      rw [commV_eq_commSub, commSub_eq_bot_iff] at hbot
      apply hF.sylow.s₁_ne
      ext w
      have := hbot (Subgroup.mem_top w) s₁ (Subgroup.mem_zpowers s₁)
      simpa using this
    have : rk (commV (Subgroup.zpowers s₁)) = 1 := by omega
    rw [this]
    decide
  have hs₁P : s₁ ∉ P := fun h => hodd ((hmem s₁).mp (hPX h)).2
  have hcardS := hS.card_T hSyl
  have hlt : Nat.card P < Nat.card S := by
    by_contra hcon
    exact hs₁P ((Subgroup.eq_of_le_of_card_ge hPS (not_lt.mp hcon)) ▸ hs₁S)
  have hdvd : Nat.card P ∣ Nat.card S := Subgroup.card_dvd_of_le hPS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hk3 : k < 3 := by
    by_contra h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact comm_of_card_le_four hP (by
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)

end Omega

end S152N

end CFSG.Quasithin
