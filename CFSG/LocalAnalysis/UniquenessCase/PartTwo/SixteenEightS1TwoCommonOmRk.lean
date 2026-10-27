module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LieType.BorelTits

private theorem s16e_twoOR_false_of_card_le_two {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hcard : Nat.card ↥A ≤ 2) {y y₁ y₂ : G}
    (hy : y ∈ A) (h1 : y₁ ∈ A) (h2 : y₂ ∈ A)
    (h1y : y₁ ≠ y) (h2y : y₂ ≠ y) (h12 : y₁ ≠ y₂) : False := by
  classical
  haveI : Fintype ↥A := Fintype.ofFinite ↥A
  let v : Fin 3 → ↥A := ![⟨y₁, h1⟩, ⟨y₂, h2⟩, ⟨y, hy⟩]
  have hv : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v, Subtype.ext_iff]
  have h3 : 3 ≤ Fintype.card ↥A := by
    simpa using Fintype.card_le_of_injective v hv
  have hcard' : Fintype.card ↥A ≤ 2 := by
    rwa [Nat.card_eq_fintype_card] at hcard
  omega

theorem s16e_two_om_comm_rk_ge {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {J : Subgroup W} {n : ℕ} (hn : n = 6 ∨ n = 8) (h : NatOmegaMinus H J ⊥ n 1) {x : MulAut W}
    (hx : x ∈ H) (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) :
    2 ≤ rk ↥(commSub J (Subgroup.zpowers x)) := by
  have _ := hx2
  obtain ⟨-, K, hK, hKf, b, c, hK2, hpoly, hReal⟩ := h
  letI := hK
  haveI : Finite K := hKf
  haveI : Fintype K := Fintype.ofFinite K
  let d : ℕ := n / 2
  obtain ⟨π, hπ⟩ := hReal
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hβinj : Function.Injective β := by
    intro p q hpq
    have h1 : β (p * q⁻¹) = 1 := by rw [map_mul, map_inv, hpq, mul_inv_cancel]
    have h2 : ((p * q⁻¹ : ↥J) : W) ∈ (⊥ : Subgroup W) := (hβker (p * q⁻¹)).1 h1
    have h3 : p * q⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  obtain ⟨γ, hγ⟩ := R.surj ⟨x, hx⟩
  have hxπeq : ((π γ : ↥H) : MulAut W) = x :=
    congrArg (fun h : ↥H => (h : MulAut W)) hγ
  let xπ : MulAut W := ((π γ : ↥H) : MulAut W)
  have hxπ : xπ = x := hxπeq
  rw [← hxπ]
  have hxhne : (⟨x, hx⟩ : ↥H) ≠ 1 := by
    intro h1
    exact hx1 (by simpa using congrArg (fun h : ↥H => (h : MulAut W)) h1)
  have hγne : γ ≠ 1 := by
    intro h1
    apply hxhne
    calc (⟨x, hx⟩ : ↥H) = π γ := hγ.symm
      _ = π 1 := congrArg π h1
      _ = 1 := map_one π
  have hγGL : (γ : Matrix.GeneralLinearGroup (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K) ≠ 1 := by
    intro h1
    exact hγne (Subtype.ext (by simpa using h1))
  let g : Matrix (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2)
      (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K :=
    (γ : Matrix.GeneralLinearGroup (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K)
  have hg1 : g ≠ 1 := by
    intro h1
    exact hγGL (Units.ext h1)
  have hK2' : Nat.card K = 2 := by simpa using hK2
  have htwoK : (2 : K) = 0 := by
    have hq := FiniteField.cast_card_eq_zero (K := K)
    rw [← Nat.card_eq_fintype_card, hK2'] at hq
    exact hq
  have hneg : ∀ y : K, -y = y := by
    intro y
    rw [neg_eq_iff_add_eq_zero, ← two_mul, htwoK, zero_mul]
  let Φ : QuadForm K (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K) := quadMinusForm d K b c hpoly
  have hQ : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K, Φ.Q (Matrix.mulVec g v) = Φ.Q v :=
    fun v => orthGroup_preserves Φ.Q (statedOmega_le_orthGroup Φ.Q γ.2) v
  have hvv : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K, v + v = 0 := by
    intro v
    rw [← two_smul K v, htwoK, zero_smul]
  have hnegv : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K, -v = v :=
    fun v => (neg_eq_iff_add_eq_zero).2 (hvv v)
  have hJsq : ∀ u : ↥J, u ^ 2 = 1 := by
    intro u
    apply hβinj
    rw [map_pow, map_one]
    rw [← ofAdd_toAdd (β u), pow_two, ← ofAdd_add]
    rw [show Multiplicative.toAdd (β u) + Multiplicative.toAdd (β u) = 0 from hvv _]
    rw [ofAdd_zero]
  let A : Subgroup W := commSub J (Subgroup.zpowers xπ)
  have hxπ_range : xπ ∈ (Subgroup.subtype H).range := ⟨π γ, rfl⟩
  have hzp_le : Subgroup.zpowers xπ ≤ (Subgroup.subtype H).range :=
    Subgroup.zpowers_le.mpr hxπ_range
  have hAJ : A ≤ J := by
    change commSub J (Subgroup.zpowers xπ) ≤ J
    refine commSub_le_of_invariant (fun y hy w hw => ?_)
    obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp (hzp_le hy)
    rw [← hh]
    exact R.U_inv h w hw
  have hAsq : ∀ a : ↥A, a ^ 2 = 1 := by
    intro a
    apply Subtype.ext
    show ((a : W) ^ 2) = (1 : W)
    have := hJsq ⟨(a : W), hAJ a.2⟩
    simpa using congrArg Subtype.val this
  have hApg : IsPGroup 2 ↥A := isPGroup_two_of_sq_eq_one hAsq
  have hAcard : Nat.card ↥A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hApg
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K, Matrix.mulVec g v₀ ≠ v₀ := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hg1
    have hM : g = 1 := by
      ext i j
      have hv := congrFun (hc (Pi.single j 1)) i
      simpa [g, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
        Pi.single_apply, eq_comm] using hv
    exact hM
  let a : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K := Matrix.mulVec g v₀ - v₀
  have ha0 : a ≠ 0 := by
    rw [show a = Matrix.mulVec g v₀ - v₀ from rfl]
    exact sub_ne_zero.mpr hv₀
  have hv₀def : Matrix.mulVec g v₀ = a + v₀ := by
    rw [show a = Matrix.mulVec g v₀ - v₀ from rfl, sub_add_cancel]
  obtain ⟨w₀J, hβw₀⟩ := hβsurj (Multiplicative.ofAdd v₀)
  have hxw₀ : xπ (w₀J : W) ∈ J := R.U_inv (π γ) (w₀J : W) w₀J.2
  let u₀J : ↥J := ⟨xπ (w₀J : W) * (w₀J : W)⁻¹, J.mul_mem hxw₀ (J.inv_mem w₀J.2)⟩
  have hu₀A : (u₀J : W) ∈ A := by
    change xπ (w₀J : W) * (w₀J : W)⁻¹ ∈ commSub J (Subgroup.zpowers xπ)
    exact Subgroup.subset_closure ⟨xπ, Subgroup.mem_zpowers xπ, (w₀J : W), w₀J.2, rfl⟩
  have hcomm : ∀ (u : ↥J) (hu : xπ (u : W) ∈ J),
      β ⟨xπ (u : W) * (u : W)⁻¹, J.mul_mem hu (J.inv_mem u.2)⟩ =
        Multiplicative.ofAdd
          (Matrix.mulVec g (Multiplicative.toAdd (β u)) - Multiplicative.toAdd (β u)) := by
    intro u hu
    have hsub : (⟨xπ (u : W) * (u : W)⁻¹, J.mul_mem hu (J.inv_mem u.2)⟩ : ↥J) =
        ⟨xπ (u : W), hu⟩ * u⁻¹ := rfl
    rw [hsub, map_mul, map_inv]
    rw [show β (⟨xπ (u : W), hu⟩ : ↥J) =
        natAct (StatedOmega (StatedQuadMinus (n / 2) K b c)) γ (β u) by
      exact hβe γ u hu]
    simp only [natAct, toAdd_ofAdd]
    rw [show (β u)⁻¹ = Multiplicative.ofAdd (-(Multiplicative.toAdd (β u))) from rfl]
    rw [← ofAdd_add, sub_eq_add_neg]
  have hu₀β : β u₀J = Multiplicative.ofAdd a := by
    have h := hcomm w₀J hxw₀
    rw [hβw₀] at h
    simpa [a, toAdd_ofAdd] using h
  have hu₀ne1 : (u₀J : W) ≠ 1 := by
    intro h1
    have h2 : u₀J = 1 := Subtype.ext (by simpa using h1)
    have h3 : β u₀J = 1 := by rw [h2, map_one]
    rw [hu₀β, ofAdd_eq_one] at h3
    exact ha0 h3
  have hAdef : A = commSub J (Subgroup.zpowers xπ) := rfl
  by_contra hlt
  have hltA : ¬ 2 ≤ rk ↥A := by rwa [← hAdef] at hlt
  have hrk : rk ↥A ≤ 1 := by
    have := not_le.1 hltA
    omega
  have hAle2 : Nat.card ↥A ≤ 2 := by
    rw [hAcard]
    calc 2 ^ rk ↥A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hrk
      _ = 2 := by norm_num
  have hAtriv : ∀ y ∈ A, y = 1 ∨ y = (u₀J : W) := by
    intro y hy
    by_contra hcon
    push Not at hcon
    exact s16e_twoOR_false_of_card_le_two hAle2 hy A.one_mem hu₀A
      hcon.1.symm hcon.2.symm hu₀ne1.symm
  have hkey : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K,
      Matrix.mulVec g v = v ∨ Matrix.mulVec g v = v + a := by
    intro v
    obtain ⟨u, hu⟩ := hβsurj (Multiplicative.ofAdd v)
    have huJ : xπ (u : W) ∈ J := R.U_inv (π γ) (u : W) u.2
    have hβs : β ⟨xπ (u : W) * (u : W)⁻¹, J.mul_mem huJ (J.inv_mem u.2)⟩ =
        Multiplicative.ofAdd (Matrix.mulVec g v - v) := by
      rw [hcomm u huJ, hu]
      simp [toAdd_ofAdd]
    have hsA : xπ (u : W) * (u : W)⁻¹ ∈ A :=
      Subgroup.subset_closure ⟨xπ, Subgroup.mem_zpowers xπ, (u : W), u.2, rfl⟩
    rcases hAtriv _ hsA with hs | hs
    · left
      have h1 : β ⟨xπ (u : W) * (u : W)⁻¹, J.mul_mem huJ (J.inv_mem u.2)⟩ = 1 := by
        have hsub2 : (⟨xπ (u : W) * (u : W)⁻¹,
            J.mul_mem huJ (J.inv_mem u.2)⟩ : ↥J) = 1 := Subtype.ext hs
        rw [hsub2, map_one]
      rw [hβs, ofAdd_eq_one, sub_eq_zero] at h1
      exact h1
    · right
      have h2 : β ⟨xπ (u : W) * (u : W)⁻¹, J.mul_mem huJ (J.inv_mem u.2)⟩ =
          Multiplicative.ofAdd a := by
        have hsub2 : (⟨xπ (u : W) * (u : W)⁻¹,
            J.mul_mem huJ (J.inv_mem u.2)⟩ : ↥J) = u₀J := Subtype.ext hs
        rw [hsub2]
        exact hu₀β
      rw [hβs] at h2
      have h3 : Matrix.mulVec g v - v = a := by
        have := congrArg Multiplicative.toAdd h2
        simpa [toAdd_ofAdd] using this
      exact (sub_eq_iff_eq_add.mp h3).trans (add_comm a v)
  have hactive : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K,
      Matrix.mulVec g v = v + a → Φ.polar.β v a = Φ.Q a := by
    intro v hv
    have hvQ : Φ.Q (v + a) = Φ.Q v := by
      rw [← hv]
      exact hQ v
    have hadd := Φ.Q_add v a
    rw [hadd] at hvQ
    have hsum : Φ.Q a + Φ.polar.β v a = 0 := by
      have h1 : Φ.Q v + (Φ.Q a + Φ.polar.β v a) = Φ.Q v + 0 := by
        rw [add_zero, ← add_assoc]
        exact hvQ
      exact add_left_cancel h1
    have hβeq : Φ.polar.β v a = -Φ.Q a := ((neg_eq_iff_add_eq_zero).2 hsum).symm
    rw [hβeq, hneg]
  have hinactive : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K,
      Matrix.mulVec g v = v → Φ.polar.β v a = 0 := by
    intro v hv
    have hv0 : Matrix.mulVec g (v + v₀) = (v + v₀) + a := by
      rw [Matrix.mulVec_add, hv, hv₀def]
      abel
    have hact := hactive (v + v₀) hv0
    have hact0 := hactive v₀ (by rw [hv₀def]; abel)
    rw [Φ.polar.add_left] at hact
    rw [hact0] at hact
    have hlast : Φ.polar.β v a + Φ.Q a = 0 + Φ.Q a := by rw [zero_add]; exact hact
    exact add_right_cancel hlast
  by_cases hQa0 : Φ.Q a = 0
  · have hβ0 : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K, Φ.polar.β v a = 0 := by
      intro v
      rcases hkey v with hv | hv
      · exact hinactive v hv
      · rw [hactive v hv, hQa0]
    have hall : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K, Φ.polar.β a v = 0 := by
      intro v
      rw [Φ.polar_symm]
      exact hβ0 v
    exact ha0 (Φ.polar.nondeg a hall)
  · have hga : ∀ v : Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2 → K,
        Matrix.mulVec g v = v - (Φ.polar.β v a / Φ.Q a) • a := by
      intro v
      rcases hkey v with hv | hv
      · rw [hinactive v hv, hv, zero_div, zero_smul, sub_zero]
      · rw [hactive v hv, hv, div_self hQa0, one_smul, sub_eq_add_neg, hnegv a]
    exact (reflection_notMem_statedOmega Φ hQa0 hga)
      (show (γ : Matrix.GeneralLinearGroup (Fin (d - 1) ⊕ Fin (d - 1) ⊕ Fin 2) K) ∈
        StatedOmega Φ.Q from γ.2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
