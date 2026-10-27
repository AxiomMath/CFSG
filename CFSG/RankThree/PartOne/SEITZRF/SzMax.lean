module

public import CFSG.RankThree.PartOne.SEITZ2.SzOuter
public import CFSG.RankThree.PartOne.SEITZ9.SzTorus
public import CFSG.RankThree.PartOne.SEITZ10.SzCase2
public import CFSG.RankThree.PartOne.SEITZ9.SzModule

public section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.SEITZ2 CFSG.RankThree.PartOne.SEITZ9
  CFSG.RankThree.PartOne.SEITZ10
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_S)
open CFSG.RankThree.PartOne.KE (fixField)
open CFSG.RankThree.PartOne.CTP (fixedSubgroup mem_fixedSubgroup)

theorem exists_mem_subfield_ne_zero_ne_one {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : 2 < Nat.card k) : ∃ m ∈ k, m ≠ 0 ∧ m ≠ 1 := by
  by_contra hcon
  have hsub : (k : Set K) ⊆ {0, 1} := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · by_cases hx1 : x = 1
      · simp [hx1]
      · exact absurd ⟨x, hx, hx0, hx1⟩ hcon
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair zero_ne_one, ← Nat.card_coe_set_eq] at h
  exact absurd hk (not_lt.2 h)

section Centralizer

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiWElt_mul_D (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) :
    suzukiWElt a K * suzukiDElt a K l = suzukiDElt a K l⁻¹ * suzukiWElt a K := by
  calc suzukiWElt a K * suzukiDElt a K l
      = (suzukiWElt a K * suzukiDElt a K l * suzukiWElt a K) * suzukiWElt a K := by
        rw [mul_assoc (suzukiWElt a K * suzukiDElt a K l), suzukiWElt_mul_self, mul_one]
    _ = suzukiDElt a K l⁻¹ * suzukiWElt a K := by rw [suzukiWElt_D_W hK]

theorem suzukiDElt_conj_bigCell (hK : Nat.card K = 2 ^ (2 * a + 1)) (m l : Kˣ) (u v c d : K) :
    suzukiDElt a K m *
        (suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d) *
        (suzukiDElt a K m)⁻¹ =
      suzukiSElt a K ((m⁻¹ : Kˣ) * u) (((m⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * v) *
        suzukiDElt a K (m * m * l) * suzukiWElt a K *
        suzukiSElt a K ((m⁻¹ : Kˣ) * c) (((m⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * d) := by
  have h1 := suzukiDElt_conj' hK m u v
  have h2 := suzukiDElt_conj' hK m c d
  have h3 : suzukiDElt a K m * suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K m)⁻¹ =
      suzukiDElt a K (m * m * l) * suzukiWElt a K := by
    calc suzukiDElt a K m * suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K m)⁻¹
        = suzukiDElt a K m * suzukiDElt a K l * (suzukiWElt a K * suzukiDElt a K m⁻¹) := by
          rw [suzukiDElt_inv]; group
      _ = suzukiDElt a K m * suzukiDElt a K l * (suzukiDElt a K m * suzukiWElt a K) := by
          rw [suzukiWElt_mul_D hK, inv_inv]
      _ = (suzukiDElt a K m * suzukiDElt a K l * suzukiDElt a K m) * suzukiWElt a K := by group
      _ = suzukiDElt a K (m * m * l) * suzukiWElt a K := by
          rw [suzukiDElt_mul, suzukiDElt_mul, mul_right_comm m l m]
  calc suzukiDElt a K m *
        (suzukiSElt a K u v * suzukiDElt a K l * suzukiWElt a K * suzukiSElt a K c d) *
        (suzukiDElt a K m)⁻¹
      = (suzukiDElt a K m * suzukiSElt a K u v * (suzukiDElt a K m)⁻¹) *
        (suzukiDElt a K m * suzukiDElt a K l * suzukiWElt a K * (suzukiDElt a K m)⁻¹) *
        (suzukiDElt a K m * suzukiSElt a K c d * (suzukiDElt a K m)⁻¹) := by group
    _ = _ := by rw [h1, h2, h3]; group

theorem suzuki_eq_one_of_commute (hK : Nat.card K = 2 ^ (2 * a + 1)) {m : Kˣ} (hm : m ≠ 1)
    {c : suzukiGroup a K} (hD : suzukiDElt a K m * c = c * suzukiDElt a K m)
    (hS : suzukiSElt a K 1 0 * c = c * suzukiSElt a K 1 0) : c = 1 := by
  obtain ⟨hform, -, huniq1, huniq2⟩ := suzuki_bruhat_normal_form hK c
  have hc : suzukiDElt a K m * c * (suzukiDElt a K m)⁻¹ = c := by rw [hD]; group
  have h2 : (2 : K) = 0 := (suzuki_frob_data a hK).1
  have hm1 : ((m⁻¹ : Kˣ) : K) ≠ 1 := fun h => hm (inv_eq_one.1 (Units.ext h))
  rcases hform with ⟨u, v, l, rfl⟩ | ⟨u, v, l, c', d', rfl⟩
  · have e : suzukiDElt a K m * (suzukiSElt a K u v * suzukiDElt a K l) * (suzukiDElt a K m)⁻¹ =
        suzukiSElt a K ((m⁻¹ : Kˣ) * u) (((m⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * v) *
          suzukiDElt a K l := by
      have h4 : suzukiDElt a K m * suzukiDElt a K l * (suzukiDElt a K m)⁻¹ = suzukiDElt a K l := by
        rw [suzukiDElt_inv, suzukiDElt_mul, suzukiDElt_mul, mul_comm m l, mul_assoc, mul_inv_cancel,
          mul_one]
      calc suzukiDElt a K m * (suzukiSElt a K u v * suzukiDElt a K l) * (suzukiDElt a K m)⁻¹
          = (suzukiDElt a K m * suzukiSElt a K u v * (suzukiDElt a K m)⁻¹) *
              (suzukiDElt a K m * suzukiDElt a K l * (suzukiDElt a K m)⁻¹) := by group
        _ = _ := by rw [suzukiDElt_conj' hK, h4]
    obtain ⟨hu, hv, -⟩ := huniq1 u v ((m⁻¹ : Kˣ) * u)
      (((m⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) * v) l l rfl (hc.symm.trans e)
    have hu0 : u = 0 := by
      have : (((m⁻¹ : Kˣ) : K) - 1) * u = 0 := by linear_combination -hu
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hm1)
    have hθ : ((m⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) ≠ 1 := fun h =>
      hm1 (pow_theta_succ_injective hK (by simpa using h))
    have hv0 : v = 0 := by
      have : (((m⁻¹ : Kˣ) : K) ^ (2 ^ (a + 1) + 1) - 1) * v = 0 := by linear_combination -hv
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hθ)
    subst hu0 hv0
    rw [suzukiSElt_zero_zero hK, one_mul] at hS ⊢
    have e2 : (suzukiDElt a K l)⁻¹ * suzukiSElt a K 1 0 * suzukiDElt a K l =
        suzukiSElt a K 1 0 := by
      rw [mul_assoc, hS, inv_mul_cancel_left]
    rw [suzukiDElt_conj hK, suzukiSElt_inj] at e2
    have hl : l = 1 := Units.ext (by simpa using e2.1)
    rw [hl, suzukiDElt_one]
  · exfalso
    obtain ⟨-, -, hll, -⟩ := huniq2 u v c' d' _ _ _ _ l (m * m * l) rfl
      (hc.symm.trans (suzukiDElt_conj_bigCell hK m l u v c' d'))
    have hmm : m * m = 1 := by
      have h : m * m * l = 1 * l := by rw [one_mul]; exact hll.symm
      exact mul_right_cancel h
    have hmm' : (m : K) * m = 1 := by rw [← Units.val_mul, hmm, Units.val_one]
    have hsq : ((m : K) - 1) ^ 2 = 0 := by linear_combination hmm' + (1 - (m : K)) * h2
    exact hm (Units.ext (sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)))

end Centralizer

section Normalizer

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzuki_mem_fixed_of_conj_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K)
    (hk8 : 2 < Nat.card (fixField σ)) {y : suzukiGroup a K}
    (hy : ∀ r ∈ fixedSubgroup (szFieldAut a K σ), y * r * y⁻¹ ∈ fixedSubgroup (szFieldAut a K σ)) :
    y ∈ fixedSubgroup (szFieldAut a K σ) := by
  obtain ⟨m, hmk, hm0, hm1⟩ := exists_mem_subfield_ne_zero_ne_one (fixField σ) hk8
  have hcomm : ∀ r ∈ fixedSubgroup (szFieldAut a K σ),
      y⁻¹ * szFieldAut a K σ y * r = r * (y⁻¹ * szFieldAut a K σ y) := by
    intro r hr
    have h1 := hy r hr
    rw [mem_fixedSubgroup, map_mul, map_mul, map_inv, mem_fixedSubgroup.1 hr] at h1
    calc y⁻¹ * szFieldAut a K σ y * r
        = y⁻¹ * (szFieldAut a K σ y * r * (szFieldAut a K σ y)⁻¹) * szFieldAut a K σ y := by
          group
      _ = y⁻¹ * (y * r * y⁻¹) * szFieldAut a K σ y := by rw [h1]
      _ = r * (y⁻¹ * szFieldAut a K σ y) := by group
  have hmU : Units.mk0 m hm0 ≠ 1 := fun h => hm1 (by simpa using congrArg Units.val h)
  have hD := hcomm (suzukiDElt a K (Units.mk0 m hm0))
    (suzukiDElt_mem_fixed σ (l := Units.mk0 m hm0) (by simpa using hmk))
  have hS := hcomm (suzukiSElt a K 1 0) (suzukiSElt_mem_fixed σ (map_one σ) (map_zero σ))
  have h1 : y⁻¹ * szFieldAut a K σ y = 1 := suzuki_eq_one_of_commute hK hmU hD.symm hS.symm
  rw [mem_fixedSubgroup]
  exact (inv_mul_eq_one.1 h1).symm

end Normalizer

theorem suzuki_normalizer_subfield
    {a : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (σ : K ≃+* K) (hk8 : 2 < Nat.card (fixField σ)) :
    Subgroup.normalizer (fixedSubgroup (szFieldAut a K σ) : Set (suzukiGroup a K)) =
      fixedSubgroup (szFieldAut a K σ) :=
  le_antisymm (fun _ hy => suzuki_mem_fixed_of_conj_mem hK σ hk8
    fun r hr => (Subgroup.mem_normalizer_iff.1 hy r).1 hr) Subgroup.le_normalizer

theorem suzuki_subfield_maximal_odd
    {a : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (σ : K ≃+* K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : orderOf σ = p)
    (hk8 : 2 < Nat.card (fixField σ)) {Y : Subgroup (suzukiGroup a K)}
    (hRY : fixedSubgroup (szFieldAut a K σ) ≤ Y)
    (hne : ¬ Y ≤ fixedSubgroup (szFieldAut a K σ)) : Y = ⊤ := by
  have hfinG : Finite (suzukiGroup a K) := finite_suzukiGroup hK
  obtain ⟨b, m, hab, hbp, hk⟩ := KE.card_fixField_suzuki_odd hp hp2 hK hσ
  have hb1 : 1 ≤ b := by
    by_contra hb0
    obtain rfl : b = 0 := by omega
    have hk2 : Nat.card (fixField σ) = 2 := by simpa using hk
    omega
  obtain ⟨e⟩ := KE.fixed_szFieldAut_equiv hK hk hab
  rw [← fixedSubgroup_eq_eqLocus] at e
  set R := fixedSubgroup (szFieldAut a K σ) with hR
  set k : Subfield K := fixField σ with hkdef
  have hσk : ∀ c ∈ k, σ c = c := fun c hc => hc
  have hUk : ∀ u ∈ k, ∀ v ∈ k, suzukiSElt a K u v ∈ Y := fun u hu v hv =>
    hRY (suzukiSElt_mem_fixed σ (hσk u hu) (hσk v hv))
  have hTk : ∀ l : Kˣ, (l : K) ∈ k → suzukiDElt a K l ∈ Y := fun l hl =>
    hRY (suzukiDElt_mem_fixed σ (hσk _ hl))
  have hW : suzukiWElt a K ∈ Y := hRY (suzukiWElt_mem_fixed σ)
  have hKk : Nat.card K = Nat.card k ^ p := by
    rw [hK, hk, ← pow_mul]
    congr 1
    omega
  by_cases hcase : ∀ g' : suzukiB a K, (g' : suzukiGroup a K) ∈ Y →
      ((torusPart hK g' : Kˣ) : K) ∈ k
  · exfalso
    obtain ⟨N, hNn, hNo, hNcard⟩ := bender_case2 hK hk hb1 hUk hW hcase
    have hsimple : IsSimpleGroup (suzukiGroup b k) := (suzuki_simple hb1 hk).2.2
    have hRsimple : IsSimpleGroup ↥R := e.isSimpleGroup
    have hcardR : Nat.card R = Nat.card k ^ 2 * (Nat.card k ^ 2 + 1) * (Nat.card k - 1) := by
      rw [Nat.card_congr e.toEquiv, suzuki_order hk, hk]
      exact mul_right_comm _ _ _
    have hR2 : 2 ∣ Nat.card R := by
      have hmem : suzukiSElt a K 0 1 ∈ R := suzukiSElt_mem_fixed σ σ.map_zero σ.map_one
      have hdvd := Subgroup.orderOf_dvd_natCard R hmem
      rw [CFSG.ShultStronglyClosedTI.SuzukiModel.orderOf_suzukiSElt_zero hK one_ne_zero] at hdvd
      exact hdvd
    set R' : Subgroup ↥Y := R.subgroupOf Y with hR'
    have eR : ↥R' ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRY
    have : IsSimpleGroup ↥R' := eR.isSimpleGroup
    have hR'card : Nat.card R' = Nat.card R := Nat.card_congr eR.toEquiv
    have hR'N : R' ≤ N :=
      le_of_isSimpleGroup_of_odd_index N hNo R' (even_iff_two_dvd.2 (hR'card ▸ hR2))
    have hNR' : R' = N := Subgroup.eq_of_le_of_card_ge hR'N (by rw [hNcard, hR'card, hcardR])
    have hnorm : R'.Normal := hNR' ▸ hNn
    have hYnorm : Y ≤ Subgroup.normalizer (R : Set (suzukiGroup a K)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).1 hnorm
    rw [suzuki_normalizer_subfield hK σ hk8] at hYnorm
    exact hne hYnorm
  · obtain ⟨g', hg'Y, hg'k⟩ : ∃ g' : suzukiB a K, (g' : suzukiGroup a K) ∈ Y ∧
        ((torusPart hK g' : Kˣ) : K) ∉ k := by
      by_contra hcon
      exact hcase fun g' hg' => by_contra fun hk' => hcon ⟨g', hg', hk'⟩
    obtain ⟨u, v, hgg⟩ := torusPart_spec hK g'
    exact suzuki_eq_top_of_irrational_torus hK hp hKk Y hUk hTk hW hg'k (hgg ▸ hg'Y)

end CFSG.RankThree.PartOne.SEITZRF
