module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallElem
public import CFSG.Quasithin.Background.Harris.R1.D4Klein

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open CFSG.Open Subgroup

open scoped IsMulCommutative

variable {Hh : Type} [Group Hh]

theorem commute_of_commutator_mem {V V₀ : Subgroup Hh} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    {c : Hh} (hc : c ^ 3 = 1) (hcV : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀)
    (hcV₀ : ∀ w ∈ V₀, c * w = w * c) : ∀ v ∈ V, c * v = v * c := by
  intro v hv
  have hwV₀ : c * v * c⁻¹ * v⁻¹ ∈ V₀ := hcV v hv
  set w : Hh := c * v * c⁻¹ * v⁻¹ with hw
  have hwV : w ∈ V := hV₀ hwV₀
  have hw2 : w * w = 1 := by simpa [pow_two] using hV.2 w hwV
  have h1 : c * v * c⁻¹ = w * v := by rw [hw]; group
  have hcw : c * w * c⁻¹ = w := by
    have := hcV₀ w hwV₀
    calc c * w * c⁻¹ = w * c * c⁻¹ := by rw [this]
      _ = w := by group
  have h2 : c * (w * v) * c⁻¹ = v := by
    calc c * (w * v) * c⁻¹ = (c * w * c⁻¹) * (c * v * c⁻¹) := by group
      _ = w * (w * v) := by rw [hcw, h1]
      _ = (w * w) * v := by group
      _ = v := by rw [hw2]; group
  have h3 : c * v * c⁻¹ = v := by
    have hcube : c * (c * (c * v * c⁻¹) * c⁻¹) * c⁻¹ = v := by
      have hc' : c * (c * c) = 1 := by rw [← pow_three]; exact hc
      have : c * (c * (c * v * c⁻¹) * c⁻¹) * c⁻¹ = (c * (c * c)) * v * (c * (c * c))⁻¹ := by
        group
      rw [this, hc']; group
    rw [h1, h2] at hcube
    exact hcube
  calc c * v = (c * v * c⁻¹) * c := by group
    _ = v * c := by rw [h3]

theorem le_sup_centralizer_of_commutator_mem {V V₀ : Subgroup Hh} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ ≤ V) {c : Hh} (hc : c ^ 3 = 1) (hcV : ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ V₀) :
    V ≤ (V ⊓ centralizer ({c} : Set Hh)) ⊔ V₀ := by
  intro v hv
  have hcV' : ∀ u ∈ V, c * u * c⁻¹ ∈ V := by
    intro u hu
    have h := V.mul_mem (hV₀ (hcV u hu)) hu
    have e : c * u * c⁻¹ = (c * u * c⁻¹ * u⁻¹) * u := by group
    rw [e]; exact h
  set v1 : Hh := c * v * c⁻¹ with hv1
  set v2 : Hh := c * v1 * c⁻¹ with hv2
  have hv1V : v1 ∈ V := hcV' v hv
  have hv2V : v2 ∈ V := hcV' v1 hv1V
  have hw1 : v2 * v1⁻¹ ∈ V₀ := by rw [hv2]; exact hcV v1 hv1V
  have hv3 : c * v2 * c⁻¹ = v := by
    have hc' : c * (c * c) = 1 := by rw [← pow_three]; exact hc
    have : c * v2 * c⁻¹ = (c * (c * c)) * v * (c * (c * c))⁻¹ := by rw [hv2, hv1]; group
    rw [this, hc']; group
  have hcomm01 : v * v1 = v1 * v := comm_of_isElemAbelian hV hv hv1V
  have hcomm02 : v * v2 = v2 * v := comm_of_isElemAbelian hV hv hv2V
  have hcomm12 : v1 * v2 = v2 * v1 := comm_of_isElemAbelian hV hv1V hv2V
  have hv11 : v1⁻¹ = v1 := by
    have h := hV.2 v1 hv1V
    rw [pow_two] at h
    exact inv_eq_of_mul_eq_one_right h
  have hfix : c * (v * v1 * v2) * c⁻¹ = v * v1 * v2 := by
    calc c * (v * v1 * v2) * c⁻¹ = (c * v * c⁻¹) * (c * v1 * c⁻¹) * (c * v2 * c⁻¹) := by group
      _ = v1 * v2 * v := by rw [← hv1, ← hv2, hv3]
      _ = v1 * (v2 * v) := by rw [mul_assoc]
      _ = v1 * (v * v2) := by rw [hcomm02]
      _ = (v1 * v) * v2 := by rw [← mul_assoc]
      _ = (v * v1) * v2 := by rw [hcomm01]
  have hcent : v * v1 * v2 ∈ centralizer ({c} : Set Hh) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := hfix
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hmem : v * v1 * v2 ∈ V ⊓ centralizer ({c} : Set Hh) :=
    Subgroup.mem_inf.mpr ⟨V.mul_mem (V.mul_mem hv hv1V) hv2V, hcent⟩
  have hv12 : (v1 * v2)⁻¹ ∈ V₀ := by
    have : v1 * v2 = v2 * v1⁻¹ := by rw [hv11, hcomm12]
    rw [this]
    exact V₀.inv_mem hw1
  have hv_eq : v = (v * v1 * v2) * (v1 * v2)⁻¹ := by group
  rw [hv_eq]
  exact Subgroup.mul_mem_sup hmem hv12

variable [Finite Hh]

private theorem s1667_e4_card_eq_four {V : Subgroup Hh} (hV : IsElemAbelian 2 V)
    (hcard : Nat.card V ≤ 4) (h3 : 3 ≤ Nat.card V) : Nat.card V = 4 := by
  have hpg : IsPGroup 2 ↥V := fun y => ⟨1, by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hV.2 y y.2⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hpg
  have hj_ge : 2 ≤ j := by
    have h1 : 2 ^ 1 < 2 ^ j := by
      rw [show (2 : ℕ) ^ 1 = 2 by norm_num, ← hj]
      omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have hj_le : j ≤ 2 := by
    have h2 : 2 ^ j ≤ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hj]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hj2 : j = 2 := by omega
  have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
  simpa [hj, hj2] using h4

private theorem s1667_e4_card_eq_two {V X : Subgroup Hh} (hV : IsElemAbelian 2 V)
    (hcardV : Nat.card V = 4) (hXV : X ≤ V) (hXne : X ≠ ⊥) (hXVne : X ≠ V) :
    Nat.card X = 2 := by
  have hXel : IsElemAbelian 2 X := isElemAbelian_of_le hV hXV
  have hpg : IsPGroup 2 ↥X := fun y => ⟨1, by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hXel.2 y y.2⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hpg
  have hdvd : Nat.card X ∣ 4 := by
    simpa [hcardV] using Subgroup.card_dvd_of_le hXV
  have hle : Nat.card X ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hne4 : Nat.card X ≠ 4 := by
    intro h
    exact hXVne (Subgroup.eq_of_le_of_card_ge hXV (by simp [hcardV, h]))
  have hj_ge : 1 ≤ j := by
    by_contra hj0
    have hj0' : j = 0 := by omega
    apply hXne
    apply Subgroup.eq_bot_of_card_eq
    rw [hj, hj0']
    norm_num
  have hj_le : j ≤ 2 := by
    have h2 : 2 ^ j ≤ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hj]
      exact hle
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hj_ne2 : j ≠ 2 := by
    intro h2
    apply hne4
    rw [hj, h2]
    norm_num
  have hj1 : j = 1 := by omega
  have h2' : (2 : ℕ) ^ 1 = 2 := by norm_num
  simpa [hj, hj1] using h2'

theorem centralizes_or_fixedPointFree {V₀ : Subgroup Hh} (hV₀ : IsElemAbelian 2 V₀)
    (hcard : Nat.card V₀ ≤ 4) {c : Hh} (hc : orderOf c = 3)
    (hn : c ∈ normalizer (V₀ : Set Hh)) :
    (∀ w ∈ V₀, c * w = w * c) ∨ (Nat.card V₀ = 4 ∧ V₀ ⊓ centralizer ({c} : Set Hh) = ⊥) := by
  have hc3 : c * c * c = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc] at h
    rwa [pow_three'] at h
  have hcn : ∀ v ∈ V₀, c * v * c⁻¹ ∈ V₀ := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hn v).mp hv
  have hsq : ∀ v ∈ V₀, v * v = 1 := fun v hv => by
    have := hV₀.2 v hv
    simpa [pow_two] using this
  by_cases hall : ∀ w ∈ V₀, c * w = w * c
  · exact Or.inl hall
  · right
    have hnot : ∃ w, w ∈ V₀ ∧ c * w ≠ w * c := by
      push Not at hall
      exact hall
    obtain ⟨w, hw, hnotw⟩ := hnot
    have hw1 : w ≠ 1 := fun h => hnotw (by rw [h]; group)
    have hcwV₀ : c * w * c⁻¹ ∈ V₀ := hcn w hw
    have hcw1 : c * w * c⁻¹ ≠ 1 := fun h => hw1 (by
      have : w = c⁻¹ * (c * w * c⁻¹) * c := by group
      rw [this, h]; group)
    have hcwne : c * w * c⁻¹ ≠ w := fun h => hnotw (by
      have : c * w = w * c := by
        calc c * w = (c * w * c⁻¹) * c := by group
          _ = w * c := by rw [h]
      exact this)
    have hcard3 : 3 ≤ Nat.card V₀ := by
      classical
      haveI : Fintype ↥V₀ := Fintype.ofFinite ↥V₀
      let a : ↥V₀ := ⟨1, V₀.one_mem⟩
      let b : ↥V₀ := ⟨w, hw⟩
      let d : ↥V₀ := ⟨c * w * c⁻¹, hcwV₀⟩
      have hab : a ≠ b := fun h => hw1 (congrArg (fun z : ↥V₀ => (z : Hh)) h).symm
      have had : a ≠ d := fun h => hcw1 (congrArg (fun z : ↥V₀ => (z : Hh)) h).symm
      have hbd : b ≠ d := fun h => hcwne (congrArg (fun z : ↥V₀ => (z : Hh)) h).symm
      have hs : ({a, b, d} : Finset ↥V₀).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, had]),
          Finset.card_insert_of_notMem (by simp [hbd]), Finset.card_singleton]
      have hle := Finset.card_le_univ ({a, b, d} : Finset ↥V₀)
      rw [hs] at hle
      simpa [Nat.card_eq_fintype_card] using hle
    have hcard4 : Nat.card V₀ = 4 := s1667_e4_card_eq_four hV₀ hcard hcard3
    refine ⟨hcard4, ?_⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have huV : u ∈ V₀ := (Subgroup.mem_inf.mp hu).1
    have huc : u * c = c * u := by
      have := (Subgroup.mem_inf.mp hu).2
      rwa [Subgroup.mem_centralizer_singleton_iff] at this
    have hcu : c * u * c⁻¹ = u := by
      calc c * u * c⁻¹ = u * c * c⁻¹ := by rw [huc]
        _ = u := by group
    by_contra hu1
    exact (CFSG.Quasithin.Background.Harris.R1.conj_ne_of_cube (V := V₀) hcard4 hsq hcn hc3 hw
      hcwne huV hu1) hcu

theorem eq_bot_of_invariant_of_fixedPointFree {V₀ X : Subgroup Hh} (hV₀ : IsElemAbelian 2 V₀)
    (h4 : Nat.card V₀ = 4) {c : Hh} (hfix : V₀ ⊓ centralizer ({c} : Set Hh) = ⊥)
    (hXV₀ : X ≤ V₀) (hX : ∀ x ∈ X, c * x * c⁻¹ ∈ X) (hne : X ≠ V₀) : X = ⊥ := by
  by_contra hXne
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have hxX : (x : Hh) ∈ X := x.2
  have hxV : (x : Hh) ∈ V₀ := hXV₀ hxX
  have hx1' : (x : Hh) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hx2 : (x : Hh) * (x : Hh) = 1 := by
    have := hV₀.2 (x : Hh) hxV
    simpa [pow_two] using this
  have hcardX : Nat.card X = 2 := s1667_e4_card_eq_two hV₀ h4 hXV₀ hXne hne
  have hxord : orderOf (x : Hh) = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1'
  have hzp : Subgroup.zpowers (x : Hh) = X := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
    rw [Nat.card_zpowers, hxord, hcardX]
  have hconjX : c * (x : Hh) * c⁻¹ ∈ Subgroup.zpowers (x : Hh) := by
    rw [hzp]; exact hX (x : Hh) hxX
  have hconj1 : c * (x : Hh) * c⁻¹ ≠ 1 := fun h => hx1' (by
    have : (x : Hh) = c⁻¹ * (c * (x : Hh) * c⁻¹) * c := by group
    rw [this, h]; group)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hconjX
  have hk' : (x : Hh) ^ (k % (orderOf (x : Hh) : ℤ)) = c * (x : Hh) * c⁻¹ := by
    rw [zpow_mod_orderOf, hk]
  have hx2z : ((orderOf (x : Hh) : ℤ)) = (2 : ℤ) := by rw [hxord]; norm_num
  rw [hx2z] at hk'
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · rw [hk0, zpow_zero] at hk'
    exact absurd hk'.symm hconj1
  · rw [hk1, zpow_one] at hk'
    have hxc : (x : Hh) * c = c * (x : Hh) := by
      calc (x : Hh) * c = (c * (x : Hh) * c⁻¹) * c := by
            conv_lhs => rw [hk']
        _ = c * (x : Hh) := by group
    have hmem : (x : Hh) ∈ V₀ ⊓ centralizer ({c} : Set Hh) :=
      Subgroup.mem_inf.mpr ⟨hxV, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hxc⟩
    rw [hfix] at hmem
    exact hx1' (Subgroup.mem_bot.mp hmem)

theorem exists_commutator_eq {V₀ : Subgroup Hh} (hV₀ : IsElemAbelian 2 V₀) {c : Hh}
    (hn : c ∈ normalizer (V₀ : Set Hh)) (hfix : V₀ ⊓ centralizer ({c} : Set Hh) = ⊥) :
    ∀ w ∈ V₀, ∃ e ∈ V₀, c * e * c⁻¹ * e⁻¹ = w := by
  haveI : IsMulCommutative ↥V₀ := hV₀.1
  intro w hw
  let κ : ↥V₀ →* ↥V₀ :=
    MonoidHom.mk' (fun e => ⟨c * (e : Hh) * c⁻¹,
      (Subgroup.mem_normalizer_iff.mp hn (e : Hh)).mp e.2⟩) (fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group)
  let ι : ↥V₀ →* ↥V₀ :=
    MonoidHom.mk' (fun e => e⁻¹) (fun x y => by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_inv_rev]
      exact comm_of_isElemAbelian hV₀ (V₀.inv_mem y.2) (V₀.inv_mem x.2))
  let δ : ↥V₀ →* ↥V₀ := κ * ι
  have hδ : ∀ e : ↥V₀, (δ e : Hh) = c * (e : Hh) * c⁻¹ * (e : Hh)⁻¹ := by
    intro e
    simp [δ, κ, ι]
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have he' : c * (e : Hh) * c⁻¹ * (e : Hh)⁻¹ = 1 := by
      have := congrArg (fun z : ↥V₀ => (z : Hh)) he
      rwa [hδ e] at this
    have hce : c * (e : Hh) = (e : Hh) * c := by
      have h1 : c * (e : Hh) * c⁻¹ = (e : Hh) := by
        rw [mul_inv_eq_one] at he'
        exact he'
      calc c * (e : Hh) = (c * (e : Hh) * c⁻¹) * c := by group
        _ = (e : Hh) * c := by rw [h1]
    have hmem : (e : Hh) ∈ V₀ ⊓ centralizer ({c} : Set Hh) :=
      Subgroup.mem_inf.mpr ⟨e.2, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hce.symm⟩
    have := Subgroup.mem_bot.mp (hfix ▸ hmem)
    exact Subtype.ext this
  have hsurj : Function.Surjective δ := Finite.injective_iff_surjective.mp hinj
  obtain ⟨e, he⟩ := hsurj ⟨w, hw⟩
  refine ⟨(e : Hh), e.2, ?_⟩
  have := congrArg (fun z : ↥V₀ => (z : Hh)) he
  rwa [hδ e] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
