module

public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Embed
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA17

section Elementary

theorem exists_of_card_eq_two {X : Type*} [Group X] (h : Nat.card X = 2) :
    ∃ z : X, z ≠ 1 ∧ ∀ w : X, w = 1 ∨ w = z := by
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : X)).mp h
  exact ⟨z, hz, fun w => by
    by_cases hw : w = 1
    · exact Or.inl hw
    · exact Or.inr (huniq w hw)⟩

theorem twoPart_eq_of_card {G : Type*} [Group G] {H : Subgroup G} {n m : ℕ} (hm : ¬ 2 ∣ m)
    (hc : Nat.card H = 2 ^ n * m) : twoPart H = 2 ^ n := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero 2)
  unfold twoPart
  rw [hc, Nat.factorization_mul (pow_ne_zero n two_ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem pow_le_twoPart {G : Type*} [Group G] [Finite G] {H : Subgroup G} {k : ℕ}
    (h : 2 ^ k ∣ Nat.card H) : 2 ^ k ≤ twoPart H := by
  unfold twoPart
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h)

theorem card_eq_card_oTwoQuot_mul {G : Type} [Group G] (H : Subgroup G) :
    Nat.card H = Nat.card (OTwoQuot H) * Nat.card (pCoreOf 2 H) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
  have h2 : Nat.card (pCoreOf 2 H) = Nat.card (CFSG.Open.pCore 2 ↥H) := by
    unfold pCoreOf
    exact Subgroup.card_map_of_injective H.subtype_injective
  rw [h2]
  exact h1

end Elementary

section Setting

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem exists_central_involution (h : Hyp1421 G T M) :
    ∃ z : G, z ∈ quasithinOmegaOneCenter T ∧ z ≠ 1 ∧ z * z = 1 ∧
      ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z := by
  obtain ⟨z, hz1, hall⟩ := exists_of_card_eq_two h.card_omegaOneCenter
  have hzz : z * z = 1 := by
    rcases hall (z * z) with h1 | h1
    · exact h1
    · exfalso
      apply hz1
      have : z * z = z * 1 := by rw [h1, mul_one]
      exact mul_left_cancel this
  refine ⟨(z : G), z.2, fun h1 => hz1 (Subtype.ext h1), congrArg Subtype.val hzz, fun w hw => ?_⟩
  rcases hall ⟨w, hw⟩ with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

omit [Finite G] in
theorem centralizer_eq_mcOf {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T)
    (hall : ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z) :
    Subgroup.centralizer ({z} : Set G) = mcOf T := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, mcOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx w hw
    rcases hall w hw with rfl | rfl
    · simp
    · exact hx.symm
  · intro hx
    exact (hx z hzZ).symm

theorem T_le_mcOf (h : Hyp1421 G T M) : T ≤ mcOf T := h.toQTFE14.t_le_mc

theorem charTwo_mcOf (h : Hyp1421 G T M) : CharTwo (mcOf T) :=
  charTwo_of_inH' h.qtke h.sylow (inH_of_inM ⟨h.mc_max, T_le_mcOf h⟩)

theorem isSylowTwoOf_T_mcOf (h : Hyp1421 G T M) : IsSylowTwoOf T (mcOf T) :=
  isSylowTwoOf_of_isSylowTwo h.sylow (T_le_mcOf h)

theorem le_mcOf_of_isHStar (h : Hyp1421 G T M) (hH : IsHStar T M H) : H ≤ mcOf T :=
  (h.isUniqueM_centralizer hH.1 hH.2.1).1.2

theorem K1_le_mcOf (st : Setting1427 T M H K1) : K1 ≤ mcOf T :=
  st.notation_.le_K.trans ((oTwoUpper_le H).trans (le_mcOf_of_isHStar st.hyp st.hStar))

theorem exists_theta_mcOf (h : Hyp1421 G T M) (hQ : IsQ8D8 ↥(pCoreOf 2 (mcOf T))) :
    ∃ θ : ↥(mcOf T) →* Equiv.Perm (Fin 5),
      θ.ker = (pCoreOf 2 (mcOf T)).subgroupOf (mcOf T) := by
  refine exists_hom_perm5 (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) hQ ?_
  intro x hx hc
  exact charTwo_mcOf h ⟨hx, Subgroup.mem_centralizer_iff.mpr fun q hq => (hc q hq).symm⟩

theorem eq_mcOf_of_card (h : Hyp1421 G T M) (hK1 : K1 ≤ mcOf T)
    (hQ : IsQ8D8 ↥(pCoreOf 2 (mcOf T))) (hK1c : Nat.card K1 = 1920)
    (hT : Nat.card T ≤ 128) : K1 = mcOf T := by
  obtain ⟨θ, hker⟩ := exists_theta_mcOf h hQ
  have hc := card_eq_mul_card_range (pCoreOf_le 2 _) hQ hker
  have hdvd := card_range_dvd θ
  have h1920 : 1920 ∣ Nat.card (mcOf T) := hK1c ▸ Subgroup.card_dvd_of_le hK1
  set r := Nat.card θ.range with hr
  have h60 : 60 ∣ r := by
    rw [hc, show (1920 : ℕ) = 32 * 60 by norm_num] at h1920
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1920
  have hr' : r = 60 ∨ r = 120 := by
    obtain ⟨k, hk⟩ := h60
    have hk' : k ∣ 2 := by
      have : 60 * k ∣ 60 * 2 := by rw [← hk]; exact hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    have : k = 1 ∨ k = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hk' with h | h
      · exact Or.inl h
      · exact Or.inr h
    rcases this with rfl | rfl
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rcases hr' with h60' | h120
  · refine Subgroup.eq_of_le_of_card_ge hK1 ?_
    rw [hc, h60']
    omega
  · exfalso
    have hc3840 : Nat.card (mcOf T) = 3840 := by rw [hc, h120]
    have hsyl := isSylowTwoOf_T_mcOf h
    have h256 : 2 ^ 8 ∣ Nat.card (mcOf T) := by rw [hc3840]; norm_num
    have := pow_le_twoPart h256
    rw [← hsyl.card_eq] at this
    omega

end Setting

end S1421QA17

end CFSG.Quasithin
