module

public import CFSG.RankThree.PartOne.SEITZ2.SUnCore
public import CFSG.RankThree.PartOne.SEITZ2.SUnField
public import CFSG.RankThree.PartOne.SEITZ2.SUnRat
public import CFSG.RankThree.PartOne.SEITZ2.SU3Main

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {σ : K ≃+* K}
  {σ₀ : k ≃+* k}

omit [Finite K] [CharP K 2] in
theorem herm_incl_eq_zeroN (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {n : ℕ}
    {a₁ : Fin n → k} (h : herm σ (incl a₁ : Fin n → K) (incl a₁) = 0) : herm σ₀ a₁ a₁ = 0 := by
  rw [herm_incl hσk] at h
  exact Subtype.ext h

omit [Finite K] in
theorem exists_phiN_isTv {n : ℕ} (hσ₀ : ∀ c, σ₀ (σ₀ c) = c)
    (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {a : Fin n → K} (ha : IsRat k a)
    (hiso : herm σ a a = 0) {c : K} (hc : c ∈ k) (hσc : σ c = c) :
    ∃ t ∈ (phiN hσk).range, IsTv σ t a c := by
  obtain ⟨a₁, rfl⟩ := exists_incl_eq ha
  have hc2 : c + c = 0 := CharTwo.add_self_eq_zero c
  have hc₁ : (⟨c, hc⟩ : k) + σ₀ ⟨c, hc⟩ = 0 := by
    apply Subtype.ext
    change c + ((σ₀ ⟨c, hc⟩ : k) : K) = 0
    rw [← hσk, hσc, hc2]
  obtain ⟨t₁, ht₁⟩ := exists_isTv hσ₀ (herm_incl_eq_zeroN hσk hiso) hc₁
  exact ⟨phiN hσk t₁, ⟨t₁, rfl⟩, isTv_phiN hσk ht₁⟩

omit [Finite K] [CharP K 2] in
theorem exists_phiN_smul_eq {N : ℕ} (hN : 3 ≤ N) (hσ₀ : IsUnitaryInvolution σ₀)
    (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {x x' : Fin N → K} (hx : IsRat k x)
    (hx' : IsRat k x') (hx0 : x ≠ 0) (hx'0 : x' ≠ 0) (hxi : herm σ x x = 0)
    (hx'i : herm σ x' x' = 0) : ∃ r ∈ (phiN (n := N) hσk).range, r • x = x' := by
  obtain ⟨x₁, rfl⟩ := exists_incl_eq hx
  obtain ⟨x₁', rfl⟩ := exists_incl_eq hx'
  have h1 : x₁ ≠ 0 := fun h => hx0 (by rw [h]; funext i; simp [incl])
  have h1' : x₁' ≠ 0 := fun h => hx'0 (by rw [h]; funext i; simp [incl])
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ₀ hN h1
    (herm_incl_eq_zeroN hσk hxi) h1' (herm_incl_eq_zeroN hσk hx'i)
  exact ⟨phiN hσk t, ⟨t, rfl⟩, by rw [phiN_smul, ht]⟩

theorem isTv_full_sup {N : ℕ} (hN : 3 ≤ N) (hσ : IsUnitaryInvolution σ)
    (hσ₀ : IsUnitaryInvolution σ₀)
    (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p) (hk4 : 4 ∣ Nat.card (ratFix σ k))
    (hq : ∃ s : k, s ≠ 0 ∧ σ₀ s * s ≠ 1) {ω : K} (hωk : ω ∈ k) (hω1 : ω ≠ 1)
    (hωn : σ ω * ω = 1)
    (hquad : ∀ z s t : K, σ z = z → s ∈ k → t ∈ k → σ s = s → σ t = t → z ^ 2 + s * z + t = 0 →
      z ∈ k)
    {a₀ b₀ : Fin N → K} (ha : herm σ a₀ a₀ = 0) (hb : herm σ b₀ b₀ = 0)
    (hab : herm σ a₀ b₀ = 1) (ha_rat : IsRat k a₀) (A : GL (Fin N) K)
    (hA : conjTr σ (A : Matrix (Fin N) (Fin N) K) * (A : Matrix (Fin N) (Fin N) K) = 1)
    (hne : (phiN hσk).range.map (conjU A hA) ≠ (phiN hσk).range) :
    ∀ b : fixSub σ, ∃ t ∈ (phiN hσk).range ⊔ (phiN hσk).range.map (conjU A hA),
      IsTv σ t a₀ (b : K) := by
  classical
  have hσi := hσ.invol
  set R := (phiN hσk).range with hR
  set R' := R.map (conjU A hA) with hR'
  set M := R ⊔ R' with hM
  have hRM : R ≤ M := le_sup_left
  have hR'M : R' ≤ M := le_sup_right
  have hM_rat : ∀ a : Fin N → K, IsRat k a → herm σ a a = 0 → ∀ c : K, c ∈ k → σ c = c →
      ∃ t ∈ M, IsTv σ t a c := by
    intro a ha' hiso c hc hσc
    obtain ⟨t, htR, ht⟩ := exists_phiN_isTv hσ₀.invol hσk ha' hiso hc hσc
    exact ⟨t, hRM htR, ht⟩
  have hM_trans : ∀ x x' : Fin N → K, IsRat k x → IsRat k x' → x ≠ 0 → x' ≠ 0 →
      herm σ x x = 0 → herm σ x' x' = 0 → ∃ r ∈ M, r • x = x' := by
    intro x x' hx hx' hx0 hx'0 hxi hx'i
    obtain ⟨x₁, rfl⟩ := exists_incl_eq hx
    obtain ⟨x₁', rfl⟩ := exists_incl_eq hx'
    have h1 : x₁ ≠ 0 := fun h => hx0 (by rw [h]; funext i; simp [incl])
    have h1' : x₁' ≠ 0 := fun h => hx'0 (by rw [h]; funext i; simp [incl])
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ₀ hN h1
      (herm_incl_eq_zeroN hσk hxi) h1' (herm_incl_eq_zeroN hσk hx'i)
    exact ⟨phiN hσk t, hRM ⟨t, rfl⟩, by rw [phiN_smul, ht]⟩
  have hex : ∃ (t₁ : SUid σ₀ N) (a₁ : Fin N → k) (c₁ : k), IsTv σ₀ t₁ a₁ c₁ ∧
      herm σ₀ a₁ a₁ = 0 ∧ c₁ + σ₀ c₁ = 0 ∧ conjU A hA (phiN hσk t₁) ∉ R := by
    by_contra hcon
    push Not at hcon
    have hle : R' ≤ R := by
      let S : Subgroup (SUid σ₀ N) := R.comap ((conjU A hA).comp (phiN hσk))
      have hT : T σ₀ N ≤ S := by
        rw [T]
        refine (Subgroup.closure_le S).2 ?_
        rintro t ⟨a, c, ha', hc', ht⟩
        exact hcon t a c ht ha' hc'
      have htop : T σ₀ N = ⊤ := T_eq_top hσ₀ (by omega) (fun _ => hq)
      have hS : S = ⊤ := eq_top_iff.2 (htop ▸ hT)
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      have hg : g ∈ S := hS ▸ Subgroup.mem_top g
      exact hg
    have hcard : Nat.card R' = Nat.card R :=
      Subgroup.card_map_of_injective (conjU_injective A hA)
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard.ge)
  obtain ⟨t₁, a₁, c₁, ht₁, ha₁, hc₁, hnot⟩ := hex
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha₁0 : a₁ ≠ 0 := by
    intro h
    apply hnot
    have h1 : t₁ = 1 := by
      apply ext_smul σ₀
      intro v
      rw [ht₁ v, h]
      simp
    rw [h1, map_one, map_one]
    exact R.one_mem
  set a : Fin N → K := incl a₁ with ha_def
  set y : Fin N → K := (A : Matrix (Fin N) (Fin N) K) *ᵥ a with hy_def
  have haiso : herm σ a a = 0 := by
    rw [ha_def, herm_incl hσk, ha₁]
    rfl
  have hyiso : herm σ y y = 0 := by rw [hy_def, herm_unitary_mulVec hA]; exact haiso
  have hAinv : ∀ v : Fin N → K, (((A⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) *ᵥ
      ((A : Matrix (Fin N) (Fin N) K) *ᵥ v)) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hy0 : y ≠ 0 := by
    intro h
    have h1 : a = 0 := by
      have := hAinv a
      rw [← hy_def, h, Matrix.mulVec_zero] at this
      exact this.symm
    apply ha₁0
    apply incl_injective (K := K)
    rw [← ha_def, h1]
    funext i
    simp [incl]
  have hc₁σ : σ (c₁ : K) = c₁ := by
    have := congrArg (fun z : k => (z : K)) hc₁
    simp only [Subfield.coe_add, Subfield.coe_zero] at this
    rw [← hσk] at this
    linear_combination this - (c₁ : K) * h2
  have hyM : ∀ c : K, c ∈ k → σ c = c → ∃ t ∈ M, IsTv σ t y c := by
    intro c hc hσc
    have hc2 : c + c = 0 := CharTwo.add_self_eq_zero c
    have hc' : (⟨c, hc⟩ : k) + σ₀ ⟨c, hc⟩ = 0 := by
      apply Subtype.ext
      change c + ((σ₀ ⟨c, hc⟩ : k) : K) = 0
      rw [← hσk, hσc, hc2]
    obtain ⟨t₂, ht₂⟩ := exists_isTv hσ₀.invol ha₁ hc'
    exact ⟨conjU A hA (phiN hσk t₂), hR'M ⟨phiN hσk t₂, ⟨t₂, rfl⟩, rfl⟩,
      (isTv_phiN hσk ht₂).conjU⟩
  have hirr : ¬ ∃ lam : K, lam ≠ 0 ∧ σ lam * lam ∈ k ∧ ∃ w : Fin N → K, (∀ i, w i ∈ k) ∧
      y = lam • w := by
    rintro ⟨lam, hlam0, hlamN, w, hw, hyw⟩
    have ht : IsTv σ (conjU A hA (phiN hσk t₁)) y (c₁ : K) := (isTv_phiN hσk ht₁).conjU
    rw [hyw, isTv_smul_vec] at ht
    have hNlam : σ lam * lam ≠ 0 := mul_ne_zero ((map_ne_zero σ).2 hlam0) hlam0
    have hwiso : herm σ w w = 0 := by
      have h3 : herm σ y y = (σ lam * lam) * herm σ w w := by
        rw [hyw, herm_smul_left, herm_smul_right]
        ring
      rw [hyiso] at h3
      exact (mul_eq_zero.1 h3.symm).resolve_left hNlam
    obtain ⟨t', ht'R, ht'⟩ := exists_phiN_isTv hσ₀.invol hσk hw hwiso
      (c := (c₁ : K) * (σ lam * lam)) (k.mul_mem c₁.2 hlamN)
      (by rw [map_mul, hc₁σ, map_mul, hσi]; ring)
    exact hnot (ht.unique ht' ▸ ht'R)
  have hnorm : ∃ i j : Fin N, i ≠ j ∧ ∃ μ : K, (μ = 1 ∨ μ = ω ∨ μ = ω ^ 2) ∧
      σ (herm σ (Pi.single i 1 + Pi.single j μ : Fin N → K) y) *
        herm σ (Pi.single i 1 + Pi.single j μ : Fin N → K) y ∉ k := by
    by_contra hcon
    push Not at hcon
    exact hirr (exists_rational_of_norms_n hσi (fun c hc => by
      rw [hσk ⟨c, hc⟩]; exact (σ₀ ⟨c, hc⟩).2) hωk hω1 hωn hquad hy0 hyiso hcon)
  obtain ⟨i, j, hij, μ, hμ, hxy⟩ := hnorm
  have hμk : μ ∈ k := by
    rcases hμ with rfl | rfl | rfl
    · exact k.one_mem
    · exact hωk
    · exact k.pow_mem hωk 2
  have hμn : σ μ * μ = 1 := by
    rcases hμ with rfl | rfl | rfl
    · simp
    · exact hωn
    · rw [map_pow, ← mul_pow, hωn, one_pow]
  have hx_rat : IsRat k (Pi.single i 1 + Pi.single j μ : Fin N → K) := by
    intro l
    rw [Pi.add_apply]
    refine k.add_mem ?_ ?_
    · rcases eq_or_ne l i with rfl | hl
      · simp [k.one_mem]
      · rw [Pi.single_eq_of_ne hl]
        exact k.zero_mem
    · rcases eq_or_ne l j with rfl | hl
      · simpa using hμk
      · rw [Pi.single_eq_of_ne hl]
        exact k.zero_mem
  have hx0 : (Pi.single i 1 + Pi.single j μ : Fin N → K) ≠ 0 := by
    intro h
    have := congrFun h i
    simp [Pi.single_eq_of_ne hij] at this
  have hx : herm σ (Pi.single i 1 + Pi.single j μ : Fin N → K) (Pi.single i 1 + Pi.single j μ) =
      0 := by
    rw [herm_single_add_single_self hij, hμn]
    exact CharTwo.add_self_eq_zero 1
  have hfull := exists_isTv_fullN hσ hp hp2 hK hk4 ha hb hab ha_rat (M := M) hM_rat hM_trans
    hyiso hyM hx_rat hx0 hx hxy
  exact hfull

end Main

end CFSG.RankThree.PartOne.SEITZ2
