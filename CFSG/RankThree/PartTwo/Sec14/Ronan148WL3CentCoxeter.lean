module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentGen
public import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec12.ONanKS128Diag

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem qSubPi_cube_div {q : ℕ} (hq : ModThree π q) (hq2 : 2 < q) :
    ∃ m, qSubPi π (q ^ 3) / qSubPi π q = 3 * m ∧ 1 < m ∧ ¬ 3 ∣ m := by
  cases π
  · change q % 3 = 2 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 2 := ⟨q / 3, by omega⟩
    refine ⟨3 * t ^ 2 + 3 * t + 1, ?_, by nlinarith, by omega⟩
    change ((3 * t + 2) ^ 3 + 1) / (3 * t + 2 + 1) = _
    rw [show (3 * t + 2) ^ 3 + 1 = (3 * (3 * t ^ 2 + 3 * t + 1)) * (3 * t + 2 + 1) by ring,
      Nat.mul_div_cancel _ (by omega)]
  · change q % 3 = 1 at hq
    obtain ⟨t, rfl⟩ : ∃ t, q = 3 * t + 1 := ⟨q / 3, by omega⟩
    have ht : 1 ≤ t := by omega
    refine ⟨3 * t ^ 2 + 3 * t + 1, ?_, by nlinarith, by omega⟩
    change ((3 * t + 1) ^ 3 - 1) / (3 * t + 1 - 1) = _
    rw [show (3 * t + 1) ^ 3 - 1 = (3 * (3 * t ^ 2 + 3 * t + 1)) * (3 * t + 1 - 1) by
      rw [Nat.add_sub_cancel]
      exact Nat.sub_eq_of_eq_add (by ring),
      Nat.mul_div_cancel _ (by omega)]

theorem eq_of_commute_irreducible {Y : Matrix (Fin 3) (Fin 3) K}
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, Y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    {u v w : K} (hc : Y * diagonal ![u, v, w] = diagonal ![u, v, w] * Y) : u = v ∧ u = w := by
  set Dm := diagonal ![u, v, w] with hDm
  set W := LinearMap.ker (Matrix.toLin' Dm - u • LinearMap.id) with hW
  have hmem : ∀ x : Fin 3 → K, x ∈ W ↔ Dm *ᵥ x = u • x := by
    intro x
    rw [hW, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hinv : ∀ x ∈ W, Y *ᵥ x ∈ W := by
    intro x hx
    rw [hmem] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have hDe : ∀ i : Fin 3, Dm *ᵥ Pi.single i (1 : K) = (![u, v, w] i) • Pi.single i (1 : K) := by
    intro i
    ext j
    rw [hDm, Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_apply, hj]
  have he0 : Pi.single (0 : Fin 3) (1 : K) ∈ W := by
    rw [hmem, hDe]
    rfl
  rcases hirr W hinv with h | h
  · exfalso
    rw [h, Submodule.mem_bot] at he0
    have := congrFun he0 0
    simp at this
  · have h1 : Pi.single (1 : Fin 3) (1 : K) ∈ W := h ▸ Submodule.mem_top
    have h2 : Pi.single (2 : Fin 3) (1 : K) ∈ W := h ▸ Submodule.mem_top
    rw [hmem, hDe] at h1 h2
    have h1' := congrFun h1 1
    have h2' := congrFun h2 2
    simp at h1' h2'
    exact ⟨h1'.symm, h2'.symm⟩

theorem trace_monomial_eq_zero (a b c : Kˣ) {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k < 3) :
    ((diagUnits a b c * cycThree ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace = 0 := by
  rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
  · rw [pow_one, Units.val_mul, coe_diagUnits_eq, coe_cycThree]
    simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply]
  · rw [pow_two, Units.val_mul, Units.val_mul, coe_diagUnits_eq, coe_cycThree]
    simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply]

variable {ι : Type*} {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))}
  {e₀ : projImage (slPi π 3 (p ^ f) K)}

theorem CentConfig.false_of_coxeter (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hq2 : 2 < p ^ f) (hc : CentConfig π p f K α e₀) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ))
    {γ : MulAut (projImage (slPi π 3 (p ^ f) K))} (hγ3 : γ ^ 3 = 1) (hγe : γ e₀ = e₀)
    (hγo : ∀ u, γ ≠ MulAut.conj u)
    (hgen : ∀ x, α x ∈ Subgroup.zpowers (MulAut.conj e₀) ⊔ Subgroup.zpowers γ)
    {a b c : Kˣ} {k : ℕ} (hk1 : 1 ≤ k) (hk3 : k < 3)
    (hyH : diagUnits a b c * cycThree ^ k ∈ glPi π 3 (p ^ f) K)
    (hγ : ∀ m : projImage (slPi π 3 (p ^ f) K), (γ m : ProjGenLinGroup (Fin 3) K) =
      pmk (diagUnits a b c * cycThree ^ k) * (m : ProjGenLinGroup (Fin 3) K) *
        (pmk (diagUnits a b c * cycThree ^ k))⁻¹) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have := finite_projImage hK
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨y, hy⟩ : ∃ y : GL (Fin 3) K, y = diagUnits a b c * cycThree ^ k := ⟨_, rfl⟩
  rw [← hy] at hyH hγ
  have hnot : ¬ ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹ := by
    rintro ⟨l, hl, hlm⟩
    apply hγo (projOf _ ⟨l, hl⟩)
    ext m
    obtain ⟨s, hs, hsm⟩ := m.2
    rw [hγ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_projOf,
      ← hsm, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, hlm s hs]
  have hy3 : y ^ 3 ∈ StatedScalars (Fin 3) K := pow_three_mem_scalars hK hq hq2 hγ3 hγ
  have hyZ : y ∉ zPi π 3 (p ^ f) K := by
    intro h
    exact hnot ⟨1, one_mem _, fun m _ => by
      obtain ⟨u, hu⟩ := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h
      rw [← hu, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u m).eq.symm,
        mul_inv_cancel_right]
      group⟩
  have hy3Z : y ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.mpr ⟨pow_mem hyH 3, hy3⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, hcases⟩ := rank3II_4_10_one hK hq hτ hτ1 hyH hyZ hy3Z
  rcases hcases with ⟨⟨g, hg, hD⟩, -, -⟩ | ⟨⟨g, hg, e', he', hD⟩, -, -⟩ |
    ⟨-, -, hirr, hcyc, hcardC, -⟩
  ·
    exact hnot ((rank3II_4_10_two hK hq hτ hτ1 hyH hyZ hy3Z).mpr
      (Or.inl ⟨y * z, ⟨z, hz, rfl⟩, g, hg, hD⟩))
  ·
    have he3 : (e' : K) ^ 3 = 1 := by
      rcases he' with h | h <;> rw [h]
      · exact hτ
      · rw [← pow_mul, pow_mul', hτ, one_pow]
    have he1 : e' ≠ 1 := by
      rintro rfl
      rw [Units.val_one] at he'
      rcases he' with h | h
      · exact hτ1 h.symm
      · apply hτ1
        calc τ = τ ^ 3 / τ ^ 2 := by field_simp
          _ = 1 := by rw [hτ, ← h, div_one]
    have htr := trace_ne_zero_of_type2 hK hq (x := y) ⟨e', he3, he1, z, hz, g, hg, hD⟩
    rw [hy] at htr
    exact htr (trace_monomial_eq_zero a b c hk1 hk3)
  ·
    set C := slPi π 3 (p ^ f) K ⊓ Subgroup.centralizer {y * z} with hC
    obtain ⟨m', hN, hm1, hm3⟩ := qSubPi_cube_div hq hq2
    rw [hN] at hcardC
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := C)
    have hog₀ : orderOf g₀ = 3 * m' := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, hcardC]
    set l : C := g₀ ^ 3 with hldef
    have hol : orderOf l = m' := by
      rw [hldef, orderOf_pow' _ (by norm_num), hog₀, Nat.gcd_mul_right_left]
      omega
    have hlL : (l : GL (Fin 3) K) ∈ slPi π 3 (p ^ f) K := (Subgroup.mem_inf.mp l.2).1
    have hlC : (l : GL (Fin 3) K) * (y * z) = (y * z) * l :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp l.2).2)
    have hzs := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
    obtain ⟨zu, hzu⟩ := hzs
    have hsc : ∀ (u : Kˣ) (g : GL (Fin 3) K), g * GeneralLinearGroup.scalar (Fin 3) u =
        GeneralLinearGroup.scalar (Fin 3) u * g :=
      fun u g => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u g).eq
    have hz' : ∀ g : GL (Fin 3) K, g * z = z * g := fun g => by rw [← hzu]; exact hsc zu g
    have hly : (l : GL (Fin 3) K) * y = y * l := by
      have h2 : (l : GL (Fin 3) K) * y * z = y * l * z := by
        calc (l : GL (Fin 3) K) * y * z = l * (y * z) := mul_assoc _ _ _
          _ = (y * z) * l := hlC
          _ = y * (z * l) := mul_assoc _ _ _
          _ = y * (l * z) := by rw [hz' l]
          _ = y * l * z := (mul_assoc _ _ _).symm
      exact mul_right_cancel h2
    set w : projImage (slPi π 3 (p ^ f) K) := projOf _ ⟨l, hlL⟩ with hwdef
    have hw : (w : ProjGenLinGroup (Fin 3) K) = pmk (l : GL (Fin 3) K) := coe_projOf _ _
    have hW3 : ¬ 3 ∣ Nat.card (Subgroup.zpowers w) := by
      rw [Nat.card_zpowers]
      intro h3
      have hwm : w ^ m' = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, hw, ← map_pow, ← Subgroup.coe_pow, ← hol, pow_orderOf_eq_one]
        rfl)
      exact hm3 (dvd_trans h3 (orderOf_dvd_of_pow_eq_one hwm))
    have hγw : γ w = w := Subtype.ext (by
      rw [hγ, hw, ← map_inv, ← map_mul, ← map_mul, ← hly, mul_inv_cancel_right])
    obtain ⟨μ, hμ⟩ := exists_conj_eq_scalar_mul hγ hγe he₀
    set d := diagTau hτ with hd
    set S := GeneralLinearGroup.scalar (Fin 3) μ with hS
    have hyd : y * d = S * d * y := by
      calc y * d = (y * d * y⁻¹) * y := by group
        _ = S * d * y := by rw [hμ]
    have hdy : d⁻¹ * (y * z) * d = S * (y * z) := by
      calc d⁻¹ * (y * z) * d = d⁻¹ * y * (z * d) := by group
        _ = d⁻¹ * y * (d * z) := by rw [hz' d]
        _ = d⁻¹ * (y * d) * z := by group
        _ = d⁻¹ * (S * d * y) * z := by rw [hyd]
        _ = d⁻¹ * (d * S * y) * z := by rw [hS, ← hsc μ d]
        _ = S * (y * z) := by group
    have hdY : d * (y * z) * d⁻¹ = S⁻¹ * (y * z) := by
      have h1 : y * z = d * (S * (y * z)) * d⁻¹ := by rw [← hdy]; group
      have hSd : S * (d * (y * z) * d⁻¹) = d * (S * (y * z)) * d⁻¹ := by
        calc S * (d * (y * z) * d⁻¹) = (S * d) * (y * z) * d⁻¹ := by group
          _ = (d * S) * (y * z) * d⁻¹ := by rw [(hsc μ d).symm]
          _ = d * (S * (y * z)) * d⁻¹ := by group
      calc d * (y * z) * d⁻¹ = S⁻¹ * (S * (d * (y * z) * d⁻¹)) := by group
        _ = S⁻¹ * (d * (S * (y * z)) * d⁻¹) := by rw [hSd]
        _ = S⁻¹ * (y * z) := by rw [← h1]
    have hdC : ∀ c' ∈ C, d * c' * d⁻¹ ∈ C := by
      intro c' hc'
      obtain ⟨hc'L, hc'C⟩ := Subgroup.mem_inf.mp hc'
      rw [Subgroup.mem_centralizer_singleton_iff] at hc'C
      refine Subgroup.mem_inf.mpr ⟨conj_mem_slPi hπ (slPi_le_glPi hπ (diagTau_mem_slPi hπ hq' hτ))
        hc'L, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc d * c' * d⁻¹ * (y * z) = d * c' * (d⁻¹ * (y * z) * d) * d⁻¹ := by group
        _ = d * c' * (S * (y * z)) * d⁻¹ := by rw [hdy]
        _ = d * (c' * S) * (y * z) * d⁻¹ := by group
        _ = d * (S * c') * (y * z) * d⁻¹ := by rw [hsc μ c']
        _ = (d * S) * c' * (y * z) * d⁻¹ := by group
        _ = (S * d) * c' * (y * z) * d⁻¹ := by rw [hsc μ d]
        _ = S * (d * (c' * (y * z)) * d⁻¹) := by group
        _ = S * (d * ((y * z) * c') * d⁻¹) := by rw [hc'C]
        _ = S * (d * (y * z) * d⁻¹) * (d * c' * d⁻¹) := by group
        _ = (y * z) * (d * c' * d⁻¹) := by rw [hdY]; group
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨_, hdC g₀ g₀.2⟩)
    have hdl : d * (l : GL (Fin 3) K) * d⁻¹ = (l : GL (Fin 3) K) ^ j := by
      have hj' : ((g₀ ^ j : C) : GL (Fin 3) K) = d * g₀ * d⁻¹ := congrArg Subtype.val hj
      rw [Subgroup.coe_zpow] at hj'
      rw [hldef, Subgroup.coe_pow, ← conj_pow, ← hj', ← zpow_natCast, ← zpow_natCast,
        ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    have hconjw : MulAut.conj e₀ w = w ^ j := Subtype.ext (by
      rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he₀, hw,
        Subgroup.coe_zpow, hw, ← map_inv, ← map_mul, ← map_mul, ← map_zpow, hdl])
    have hinvW : ∀ x, ∀ v ∈ Subgroup.zpowers w, α x v ∈ Subgroup.zpowers w := by
      intro x
      refine mapsTo_of_mem_sup ?_ ?_ (hgen x)
      · rintro _ ⟨n, rfl⟩
        rw [map_zpow, hconjw, ← _root_.zpow_mul]
        exact Subgroup.zpow_mem_zpowers w _
      · rintro _ ⟨n, rfl⟩
        rw [map_zpow, hγw]
        exact Subgroup.zpow_mem_zpowers w _
    obtain ⟨x₀, hx₀⟩ := hc.conj_e
    have hfix := hc.hV _ hW3 hinvW x₀ w (Subgroup.mem_zpowers w)
    rw [hx₀] at hfix
    have hfix' := congrArg Subtype.val hfix
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, he₀, hw,
      ← map_inv, ← map_mul, ← map_mul] at hfix'
    obtain ⟨ν, hν⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hfix'
    have hν' : d * (l : GL (Fin 3) K) * d⁻¹ = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * l := by
      calc d * (l : GL (Fin 3) K) * d⁻¹ =
          d * l * d⁻¹ * GeneralLinearGroup.scalar (Fin 3) ν * GeneralLinearGroup.scalar (Fin 3) ν⁻¹ := by
            rw [mul_assoc (d * l * d⁻¹), ← map_mul, mul_inv_cancel, map_one, mul_one]
        _ = GeneralLinearGroup.scalar (Fin 3) ν⁻¹ * l := by rw [hν, hsc]
    have hν3 : ν ^ 3 = 1 := by
      have h := pow_three_eq_one_of_conj hν'
      rwa [inv_pow, inv_eq_one] at h
    have hl1 : (l : GL (Fin 3) K) ^ m' = 1 := by
      rw [← Subgroup.coe_pow, ← hol, pow_orderOf_eq_one, Subgroup.coe_one]
    have hνm : ν ^ m' = 1 := by
      have h1 : (d * (l : GL (Fin 3) K) * d⁻¹) ^ m' = 1 := by
        rw [conj_pow, hl1, mul_one, mul_inv_cancel]
      rw [hν', (Commute.mul_pow (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ν⁻¹ _).symm m'),
        hl1, mul_one, ← map_pow] at h1
      have h2 : (ν⁻¹ : Kˣ) ^ m' = 1 := by
        have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
        simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
          Units.val_one, Matrix.one_apply_eq] at this
        exact Units.ext this
      rwa [inv_pow, inv_eq_one] at h2
    have hν1 : ν = 1 := by
      have h1 : orderOf ν ∣ Nat.gcd 3 m' :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hν3) (orderOf_dvd_of_pow_eq_one hνm)
      rw [(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3] at h1
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
    rw [hν1, inv_one, map_one, one_mul] at hν'
    have hld : (l : GL (Fin 3) K) * diagTau hτ = diagTau hτ * l := by
      calc (l : GL (Fin 3) K) * diagTau hτ = d * l * d⁻¹ * d := by rw [hν']
        _ = diagTau hτ * l := by rw [hd]; group
    obtain ⟨u₀, u₁, u₂, hlu⟩ := exists_eq_diagUnits_of_commute hτ hτ1 hld
    have hcomm : ((y * z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![(u₀ : K), u₁, u₂] = diagonal ![(u₀ : K), u₁, u₂] * (y * z : GL (Fin 3) K) := by
      rw [← coe_diagUnits, ← hlu, ← Units.val_mul, ← Units.val_mul, hlC]
    obtain ⟨h01, h02⟩ := eq_of_commute_irreducible hirr hcomm
    have hu01 : u₀ = u₁ := Units.ext h01
    have hu02 : u₀ = u₂ := Units.ext h02
    have hl3 : (l : GL (Fin 3) K) ^ 3 = 1 := by
      have hdet := ((mem_slPi_iff hπ).mp hlL).2
      rw [hlu, coe_diagUnits, det_diagonal, Fin.prod_univ_three] at hdet
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] at hdet
      rw [← hu01, ← hu02] at hdet
      rw [hlu, ← hu01, ← hu02, Sec12.KS128Move.diagUnits_pow]
      have hu3 : u₀ ^ 3 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, pow_two]
        exact hdet)
      rw [hu3, Sec12.KS128Move.diagUnits_one]
    have hdvd : m' ∣ 3 := hol ▸ orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      rw [Subgroup.coe_pow, hl3, Subgroup.coe_one]))
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m' <;> simp_all

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
