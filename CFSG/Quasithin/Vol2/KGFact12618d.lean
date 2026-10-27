module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.KGFact12618a

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv

section Fifteen

theorem exists_orderOf_eq_fifteen {M : Type*} [Group M] [Finite M] (hM : Nat.card M = 45) :
    ∃ x : M, orderOf x = 15 := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 (show 5 ∣ Nat.card M by rw [hM]; norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 (show 3 ∣ Nat.card M by rw [hM]; norm_num)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 M))
  have hidx5 : (P : Subgroup M).index = 9 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P.isPGroup'
    have hi := P.not_dvd_index
    have hc := (P : Subgroup M).card_mul_index
    rw [hk, hM] at hc
    have hk3 : k < 2 := by
      by_contra h
      have h1 : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 (by omega)
      have h2 : 5 ^ 2 ∣ 45 := hc ▸ h1.trans (dvd_mul_right _ _)
      norm_num at h2
    interval_cases k
    · exfalso
      apply hi
      rw [pow_zero, one_mul] at hc
      rw [hc]
      norm_num
    · rw [pow_one] at hc
      omega
  have hP5 : Nat.card ↥(P : Subgroup M) = 5 := by
    have := (P : Subgroup M).card_mul_index
    rw [hidx5, hM] at this
    omega
  have hn5 := card_sylow_modEq_one 5 M
  have hd5 := Sylow.card_dvd_index P
  rw [hidx5] at hd5
  have hs5 : Nat.card (Sylow 5 M) = 1 := by
    have hle : Nat.card (Sylow 5 M) ≤ 9 := Nat.le_of_dvd (by norm_num) hd5
    have hpos : 0 < Nat.card (Sylow 5 M) := Nat.card_pos
    unfold Nat.ModEq at hn5
    interval_cases h : Nat.card (Sylow 5 M) <;> omega
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 M))
  have hidx3 : (R : Subgroup M).index = 5 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 R.isPGroup'
    have hi := R.not_dvd_index
    have hc := (R : Subgroup M).card_mul_index
    rw [hk, hM] at hc
    have hk3 : k < 3 := by
      by_contra h
      have h1 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
      have h2 : 3 ^ 3 ∣ 45 := hc ▸ h1.trans (dvd_mul_right _ _)
      norm_num at h2
    interval_cases k
    · exfalso
      apply hi
      rw [pow_zero, one_mul] at hc
      rw [hc]
      norm_num
    · exfalso
      apply hi
      rw [pow_one] at hc
      have : (R : Subgroup M).index = 15 := by omega
      rw [this]
      norm_num
    · norm_num at hc
      omega
  have hR9 : Nat.card ↥(R : Subgroup M) = 9 := by
    have := (R : Subgroup M).card_mul_index
    rw [hidx3, hM] at this
    omega
  have hn3 := card_sylow_modEq_one 3 M
  have hd3 := Sylow.card_dvd_index R
  rw [hidx3] at hd3
  have hs3 : Nat.card (Sylow 3 M) = 1 := by
    have hle : Nat.card (Sylow 3 M) ≤ 5 := Nat.le_of_dvd (by norm_num) hd3
    have hpos : 0 < Nat.card (Sylow 3 M) := Nat.card_pos
    unfold Nat.ModEq at hn3
    interval_cases h : Nat.card (Sylow 3 M) <;> omega
  have : Subsingleton (Sylow 5 M) := Finite.card_le_one_iff_subsingleton.1 hs5.le
  have : Subsingleton (Sylow 3 M) := Finite.card_le_one_iff_subsingleton.1 hs3.le
  have hPn : (P : Subgroup M).Normal := Sylow.normal_of_subsingleton P
  have hRn : (R : Subgroup M).Normal := Sylow.normal_of_subsingleton R
  have hxP : x ∈ (P : Subgroup M) := by
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card
      (show Nat.card ↥(Subgroup.zpowers x) = 5 ^ 1 by rw [Nat.card_zpowers, hx, pow_one]))
    rw [Subsingleton.elim Q P] at hQ
    exact hQ (Subgroup.mem_zpowers x)
  have hyR : y ∈ (R : Subgroup M) := by
    obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card
      (show Nat.card ↥(Subgroup.zpowers y) = 3 ^ 1 by rw [Nat.card_zpowers, hy, pow_one]))
    rw [Subsingleton.elim Q R] at hQ
    exact hQ (Subgroup.mem_zpowers y)
  have hPR : (P : Subgroup M) ⊓ (R : Subgroup M) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : orderOf z ∣ 5 := hP5 ▸ Subgroup.orderOf_dvd_natCard _ hz.1
    have h2 : orderOf z ∣ 9 := hR9 ▸ Subgroup.orderOf_dvd_natCard _ hz.2
    have h3 : orderOf z ∣ Nat.gcd 5 9 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 5 9 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at h3
    rw [Subgroup.mem_bot]
    exact h3
  have hcomm : Commute x y := by
    have hc : x * y * x⁻¹ * y⁻¹ ∈ (P : Subgroup M) ⊓ (R : Subgroup M) := by
      refine ⟨?_, ?_⟩
      · have h1 : y * x⁻¹ * y⁻¹ ∈ (P : Subgroup M) :=
          hPn.conj_mem _ ((P : Subgroup M).inv_mem hxP) y
        have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [this]
        exact (P : Subgroup M).mul_mem hxP h1
      · have h1 : x * y * x⁻¹ ∈ (R : Subgroup M) := hRn.conj_mem _ hyR x
        exact (R : Subgroup M).mul_mem h1 ((R : Subgroup M).inv_mem hyR)
    rw [hPR, Subgroup.mem_bot] at hc
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [hc, one_mul]
  refine ⟨x * y, ?_⟩
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hy]; norm_num), hx, hy]

theorem not_orderOf_perm6_eq_fifteen (σ : Perm (Fin 6)) : orderOf σ ≠ 15 := by
  classical
  intro h
  have hmem : ∀ a ∈ σ.cycleType, a ∣ 15 := fun a ha => h ▸ Perm.dvd_of_mem_cycleType ha
  have hsum : σ.cycleType.sum ≤ 6 := by
    rw [Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hle : ∀ a ∈ σ.cycleType, a ≤ 6 := fun a ha =>
    (Multiset.le_sum_of_mem ha).trans hsum
  have hlcm := Perm.lcm_cycleType σ
  have hex : ∀ d : ℕ, ¬ 15 ∣ d → ∃ a ∈ σ.cycleType, ¬ a ∣ d := by
    intro d hd
    by_contra hc
    push Not at hc
    have : σ.cycleType.lcm ∣ d := Multiset.lcm_dvd.2 hc
    rw [hlcm, h] at this
    exact hd this
  obtain ⟨a, ha, ha5⟩ := hex 5 (by norm_num)
  obtain ⟨b, hb, hb3⟩ := hex 3 (by norm_num)
  have ha3 : a = 3 := by
    have h1 := hmem a ha
    have h2 := Perm.two_le_of_mem_cycleType ha
    have h4 := hle a ha
    interval_cases a <;> omega
  have hb5 : b = 5 := by
    have h1 := hmem b hb
    have h2 := Perm.two_le_of_mem_cycleType hb
    have h4 := hle b hb
    interval_cases b <;> omega
  subst ha3 hb5
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem ha
  have h5t : 5 ∈ t := by
    rw [ht, Multiset.mem_cons] at hb
    exact hb.resolve_left (by norm_num)
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem h5t
  rw [ht, hu, Multiset.sum_cons, Multiset.sum_cons] at hsum
  omega

theorem not_orderOf_alt6_eq_fifteen (x : ↥(alternatingGroup (Fin 6))) : orderOf x ≠ 15 := by
  rw [← Subgroup.orderOf_coe]
  exact not_orderOf_perm6_eq_fifteen _

end Fifteen

section SmallIndex

open scoped commutatorElement

theorem eq_top_of_map_index_le {X : Type*} [Group X] (φ : X →* ↥(alternatingGroup (Fin 6)))
    (hZ : ∀ z ∈ φ.ker, ∀ x : X, z * x = x * z)
    (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) (M : Subgroup X) (hM : (M.map φ).index ≤ 5) :
    M = ⊤ := by
  have hA6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have htop : M.map φ = ⊤ :=
    eq_top_of_index_le (alternatingGroup.isSimpleGroup (by simp)) (fun m hm => by
      rw [hA6]
      interval_cases m <;> decide) _ hM
  have hdec : ∀ x : X, ∃ m ∈ M, ∃ z ∈ φ.ker, x = m * z := by
    intro x
    have hx : φ x ∈ M.map φ := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmx⟩ := hx
    refine ⟨m, hm, m⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
  rw [eq_top_iff, ← hperf, Subgroup.commutator_le]
  rintro g₁ - g₂ -
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := hdec g₁
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := hdec g₂
  have e₁ := hZ z₁ hz₁
  have e₂ := hZ z₂ hz₂
  have hc : ⁅m₁ * z₁, m₂ * z₂⁆ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
    rw [commutatorElement_def]
    calc m₁ * z₁ * (m₂ * z₂) * (m₁ * z₁)⁻¹ * (m₂ * z₂)⁻¹
        = m₁ * (z₁ * (m₂ * z₂)) * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by group
      _ = m₁ * ((m₂ * z₂) * z₁) * z₁⁻¹ * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by rw [e₁ (m₂ * z₂)]
      _ = m₁ * m₂ * (z₂ * m₁⁻¹) * z₂⁻¹ * m₂⁻¹ := by group
      _ = m₁ * m₂ * (m₁⁻¹ * z₂) * z₂⁻¹ * m₂⁻¹ := by rw [e₂ m₁⁻¹]
      _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by group
  rw [hc]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

end SmallIndex

section Eight

theorem orbit_ncard_eq_six {H : Subgroup (Perm (Fin 8))} (φ : ↥H →* ↥(alternatingGroup (Fin 6)))
    (hφs : Function.Surjective φ) (hsmall : ∀ M : Subgroup ↥H, (M.map φ).index ≤ 5 → M = ⊤)
    (h7 : ¬ 7 ∣ Nat.card ↥H) (p : Fin 8) (hp : ∃ h ∈ H, h p ≠ p) :
    (MulAction.orbit ↥H p).ncard = 6 := by
  classical
  set M := MulAction.stabilizer ↥H p with hMdef
  have hidx : M.index = (MulAction.orbit ↥H p).ncard := MulAction.index_stabilizer ↥H p
  have hle : (MulAction.orbit ↥H p).ncard ≤ 8 := by
    calc (MulAction.orbit ↥H p).ncard ≤ (Set.univ : Set (Fin 8)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = 8 := by rw [Set.ncard_univ, Nat.card_fin]
  have hne : M ≠ ⊤ := by
    intro htop
    obtain ⟨h, hh, hhp⟩ := hp
    have : (⟨h, hh⟩ : ↥H) ∈ M := htop ▸ Subgroup.mem_top _
    exact hhp this
  have hdm := Subgroup.index_map_dvd (H := M) hφs
  have hMpos : 0 < M.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have h6 : 6 ≤ (MulAction.orbit ↥H p).ncard := by
    by_contra hlt
    exact hne (hsmall _ ((Nat.le_of_dvd hMpos hdm).trans (by omega)))
  have hdvd : (MulAction.orbit ↥H p).ncard ∣ Nat.card ↥H := by
    rw [← hidx]
    exact M.index_dvd_card
  interval_cases h : (MulAction.orbit ↥H p).ncard
  · rfl
  · exact absurd hdvd h7
  ·
    exfalso
    rw [hidx] at hdm
    have hle8 : (M.map φ).index ≤ 8 := Nat.le_of_dvd (by norm_num) hdm
    have hpos : 0 < (M.map φ).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have h8 : (M.map φ).index = 8 := by
      by_contra h8
      have : (M.map φ).index ≤ 5 := by
        interval_cases hi : (M.map φ).index <;> omega
      exact hne (hsmall _ this)
    have hc := (M.map φ).card_mul_index
    rw [h8, nat_card_alternatingGroup, Nat.card_fin] at hc
    have h45 : Nat.card ↥(M.map φ) = 45 := by
      have : (6 : ℕ).factorial / 2 = 360 := by decide
      omega
    obtain ⟨x, hx⟩ := exists_orderOf_eq_fifteen h45
    rw [← Subgroup.orderOf_coe] at hx
    exact not_orderOf_alt6_eq_fifteen _ hx

theorem exists_two_fixed_eight {H : Subgroup (Perm (Fin 8))}
    (horb : ∀ p : Fin 8, (∃ h ∈ H, h p ≠ p) → (MulAction.orbit ↥H p).ncard = 6)
    (hH : ∃ h ∈ H, h ≠ 1) :
    ∃ p q : Fin 8, p ≠ q ∧ (∀ h ∈ H, h p = p ∧ h q = q) ∧
      ∀ r : Fin 8, (∀ h ∈ H, h r = r) → r = p ∨ r = q := by
  classical
  obtain ⟨h₀, hh₀, hh₀1⟩ := hH
  obtain ⟨x, hx⟩ : ∃ x : Fin 8, h₀ x ≠ x := by
    by_contra hc
    push Not at hc
    exact hh₀1 (Perm.ext hc)
  set O := MulAction.orbit ↥H x with hO
  have hO6 : O.ncard = 6 := horb x ⟨h₀, hh₀, hx⟩
  have hfix : ∀ y, y ∉ O → ∀ h ∈ H, h y = y := by
    intro y hy
    by_contra hc
    push Not at hc
    have hy6 := horb y hc
    have hdisj : Disjoint O (MulAction.orbit ↥H y) := by
      rw [Set.disjoint_left]
      intro z hzx hzy
      have h1 : MulAction.orbit ↥H z = MulAction.orbit ↥H y := MulAction.orbit_eq_iff.2 hzy
      have h2 : MulAction.orbit ↥H z = O := MulAction.orbit_eq_iff.2 hzx
      apply hy
      rw [← h2, h1]
      exact MulAction.mem_orbit_self y
    have hu := Set.ncard_union_eq hdisj
    rw [hO6, hy6] at hu
    have hle : (O ∪ MulAction.orbit ↥H y).ncard ≤ 8 := by
      calc _ ≤ (Set.univ : Set (Fin 8)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
        _ = 8 := by rw [Set.ncard_univ, Nat.card_fin]
    omega
  have hmove : ∀ y ∈ O, ∃ h ∈ H, h y ≠ y := by
    intro y hy
    by_contra hc
    push Not at hc
    have h1 : MulAction.orbit ↥H y = {y} := by
      ext z
      simp only [Set.mem_singleton_iff]
      constructor
      · rintro ⟨g, rfl⟩
        exact hc g g.2
      · rintro rfl
        exact MulAction.mem_orbit_self z
    have h2 : MulAction.orbit ↥H y = O := MulAction.orbit_eq_iff.2 hy
    rw [← h2, h1, Set.ncard_singleton] at hO6
    omega
  have hc2 : Oᶜ.ncard = 2 := by
    have := Set.ncard_add_ncard_compl O
    rw [hO6, Nat.card_fin] at this
    omega
  obtain ⟨p, q, hpq, hpqO⟩ := Set.ncard_eq_two.1 hc2
  have hp : p ∉ O := by
    have : p ∈ Oᶜ := by rw [hpqO]; exact Set.mem_insert _ _
    exact this
  have hq : q ∉ O := by
    have : q ∈ Oᶜ := by rw [hpqO]; exact Set.mem_insert_of_mem _ rfl
    exact this
  refine ⟨p, q, hpq, fun h hh => ⟨hfix p hp h hh, hfix q hq h hh⟩, fun r hr => ?_⟩
  have hrO : r ∈ Oᶜ := by
    intro hrO
    obtain ⟨h, hh, hhr⟩ := hmove r hrO
    exact hhr (hr h hh)
  rw [hpqO] at hrO
  simpa using hrO

end Eight

end CFSG.Quasithin.H13.KG12618
