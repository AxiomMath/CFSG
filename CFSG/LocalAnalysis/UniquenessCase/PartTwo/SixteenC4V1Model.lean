module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega
public import CFSG.Quasithin.Background.RonanF57Nsu
public import TauCeti.FieldTheory.Finite.Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KFU
open CFSG.LieType.Universal.Unitary (SUid)

section Model

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

private theorem s16c4v1_mod_char_two (hK : Nat.card K = 4) : (2 : K) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hK'
  exact CharP.cast_eq_zero K 2

private theorem s16c4v1_mod_quadratic_roots (hK : Nat.card K = 4) {ω x : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hx : x ^ 2 + x + 1 = 0) : x = ω ∨ x = ω ^ 2 := by
  have h2 : (2 : K) = 0 := s16c4v1_mod_char_two hK
  have hωsum : ω + ω ^ 2 = 1 := by linear_combination -hω + (ω ^ 2 + ω) * h2
  have hω3 : ω ^ 3 = 1 := by linear_combination ω * hω - hω
  have hfac : (x - ω) * (x - ω ^ 2) = 0 := by
    have hexp : (x - ω) * (x - ω ^ 2) = x ^ 2 + x + 1 := by
      linear_combination -x * hωsum + hω3 - x * h2
    rw [hexp, hx]
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem s16c4v1_mod_sigma_apply (hK : Nat.card K = 4)
    (hσ : IsUnitaryInvolution σ) (c : K) : σ c = c ^ 2 := by
  obtain ⟨ω, hω⟩ := TauCeti.exists_sq_add_self_add_one_eq_zero_of_card_eq_four hK
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω
    simp at hω
  have h2 : (2 : K) = 0 := s16c4v1_mod_char_two hK
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1] at hω
    norm_num at hω
    have h3 : (3 : K) = 1 := by
      have : (3 : K) = (2 : K) + 1 := by norm_num
      rw [this, h2, zero_add]
    rw [h3] at hω
    exact one_ne_zero hω
  have hωsum : ω + ω ^ 2 = 1 := by linear_combination -hω + (ω ^ 2 + ω) * h2
  have hω3 : ω ^ 3 = 1 := by linear_combination ω * hω - hω
  have hσω : (σ ω) ^ 2 + σ ω + 1 = 0 := by
    have := congrArg σ hω
    simp only [map_add, map_pow, map_one, map_zero] at this
    exact this
  have hσω_cases : σ ω = ω ∨ σ ω = ω ^ 2 := s16c4v1_mod_quadratic_roots hK hω hσω
  have hσid : σ ω = ω → ∀ y : K, σ y = y := by
    intro hsω y
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]
    · by_cases hy1 : y = 1
      · rw [hy1, map_one]
      · have hy : y ^ 2 + y + 1 = 0 :=
          TauCeti.sq_add_self_add_one_eq_zero hK hy0 hy1
        rcases s16c4v1_mod_quadratic_roots hK hω hy with h | h
        · rw [h, hsω]
        · rw [h, map_pow, hsω]
  have hσω_ne : σ ω ≠ ω := by
    intro h
    obtain ⟨c, hc⟩ := hσ.exists_ne
    exact hc (hσid h c)
  rcases hσω_cases with h | h
  · exact absurd h hσω_ne
  · have hσw2 : σ (ω ^ 2) = ω := by
      rw [map_pow, h]
      calc (ω ^ 2) ^ 2 = ω ^ 4 := by ring
        _ = ω := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hω3, one_mul]
    by_cases hc0 : c = 0
    · rw [hc0, map_zero, zero_pow (by norm_num)]
    · by_cases hc1 : c = 1
      · rw [hc1, map_one, one_pow]
      · have hc : c ^ 2 + c + 1 = 0 :=
          TauCeti.sq_add_self_add_one_eq_zero hK hc0 hc1
        rcases s16c4v1_mod_quadratic_roots hK hω hc with hcω | hcω
        · rw [hcω, h]
        · rw [hcω, hσw2]
          rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_succ, hω3, one_mul]

private theorem s16c4v1_mod_herm_eq_sum (hK : Nat.card K = 4)
    (hσ : IsUnitaryInvolution σ) (x : Fin 4 → K) :
    herm σ x x = ∑ i, x i ^ 3 := by
  simp only [herm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s16c4v1_mod_sigma_apply σ hK hσ]
  ring

private theorem s16c4v1_mod_suid_eq_statedSU (hK : Nat.card K = 4)
    (hσ : IsUnitaryInvolution σ) : SUid σ 4 = StatedSU 4 (2 ^ 1) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 2 :=
    CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hK'
  have hσeq : σ = CFSG.LieType.BorelTits.unitaryInvolution K 2 1 := by
    ext c
    rw [s16c4v1_mod_sigma_apply σ hK hσ,
      CFSG.LieType.BorelTits.unitaryInvolution_apply]
    norm_num
  rw [hσeq]
  exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK' 4

private theorem s16c4v1_mod_isElemAbelian_subgroupOf {p : ℕ}
    (E : Subgroup (GL (Fin 4) K)) (hEle : E ≤ StatedSU 4 (2 ^ 1) K)
    (hS : SUid σ 4 = StatedSU 4 (2 ^ 1) K) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.subgroupOf (SUid σ 4)) := by
  have hES : E ≤ SUid σ 4 := by rw [hS]; exact hEle
  haveI : IsMulCommutative E := hE.1
  refine ⟨inferInstance, fun x hx => Subtype.ext ?_⟩
  have hx' : (x : GL (Fin 4) K) ∈ E := hx
  simpa using hE.2 (x : GL (Fin 4) K) hx'

private theorem s16c4v1_mod_card_subgroupOf (E : Subgroup (GL (Fin 4) K))
    (hEle : E ≤ StatedSU 4 (2 ^ 1) K) (hS : SUid σ 4 = StatedSU 4 (2 ^ 1) K) :
    Nat.card (E.subgroupOf (SUid σ 4)) = Nat.card E := by
  have hES : E ≤ SUid σ 4 := by rw [hS]; exact hEle
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv


theorem s16c4v1_card_le_27 (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    (E : Subgroup ↥(SUid σ 4)) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData 2 1 K := CFSG.Quasithin.RonanF57.unitaryFieldData_of_card hK
  have hS : SUid σ 4 = StatedSU 4 (2 ^ 1) K := s16c4v1_mod_suid_eq_statedSU σ hK hσ
  let φ : ↥(SUid σ 4) ≃* ↥(unitarySU 2 1 K 4) := MulEquiv.subgroupCongr hS
  let E₀ : Subgroup ↥(unitarySU 2 1 K 4) := E.map φ.toMonoidHom
  have hE₀ : IsElemAbelian 3 E₀ := hE.map φ.toMonoidHom
  have hcard₀ : Nat.card E₀ = Nat.card E := Subgroup.card_map_of_injective φ.injective
  obtain ⟨s, hs⟩ := s15k_om6_conj_torus hU E₀ hE₀
  obtain ⟨-, hT⟩ := s15k_om6_torus hU
  set T := (torusSU 3 4 K).subgroupOf (unitarySU 2 1 K 4) with hTdef
  have hle : E₀.map (MulAut.conj s).toMonoidHom ≤ T := by
    rintro y ⟨z, hz, rfl⟩
    exact hs z hz
  calc Nat.card E = Nat.card E₀ := hcard₀.symm
    _ = Nat.card (E₀.map (MulAut.conj s).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj s).injective).symm
    _ ≤ Nat.card T := Subgroup.card_le_of_le hle
    _ = 27 := hT
    _ = 3 ^ 3 := by norm_num

theorem s16c4v1_stab_nonsing (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    {v : Fin 4 → K} (hv : herm σ v v ≠ 0) :
    ∃ E : Subgroup ↥(SUid σ 4), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ ∀ γ ∈ E, γ • v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : SUid σ 4 = StatedSU 4 (2 ^ 1) K := s16c4v1_mod_suid_eq_statedSU σ hK hσ
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hsum : ∑ i, v i ^ (2 ^ 1 + 1) ≠ 0 := by
    have h3 : (2 : ℕ) ^ 1 + 1 = 3 := by norm_num
    rw [h3, ← s16c4v1_mod_herm_eq_sum σ hK hσ v]
    exact hv
  obtain ⟨E, hEle, hE, hEcard, hEfix⟩ :=
    exists_stab_elemAbelian_nonsing (p := 3) (n := 1) Nat.prime_three (by norm_num) hK' hsum
  let E' : Subgroup ↥(SUid σ 4) := E.subgroupOf (SUid σ 4)
  have hE' : IsElemAbelian 3 E' := s16c4v1_mod_isElemAbelian_subgroupOf σ E hEle hS hE
  have hcard' : Nat.card E' = 3 ^ 2 := by
    rw [s16c4v1_mod_card_subgroupOf σ E hEle hS, hEcard]
  refine ⟨E', hE', hcard', fun γ hγ => ?_⟩
  have hγE : (γ : GL (Fin 4) K) ∈ E := hγ
  simpa [CFSG.ClassicalGroups.Unitary.smul_def] using hEfix (γ : GL (Fin 4) K) hγE

theorem s16c4v1_stab_ne_zero (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    {v : Fin 4 → K} (hv : v ≠ 0) :
    ∃ γ : ↥(SUid σ 4), γ ≠ 1 ∧ γ ^ 3 = 1 ∧ γ • v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : SUid σ 4 = StatedSU 4 (2 ^ 1) K := s16c4v1_mod_suid_eq_statedSU σ hK hσ
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨E, hEle, hE, hEcard, hEfix⟩ :=
    exists_stab_elemAbelian_ne_zero (p := 3) (n := 1) Nat.prime_three (by norm_num) hK' hv
  let E' : Subgroup ↥(SUid σ 4) := E.subgroupOf (SUid σ 4)
  have hE' : IsElemAbelian 3 E' := s16c4v1_mod_isElemAbelian_subgroupOf σ E hEle hS hE
  have hcard' : Nat.card E' = 3 := by
    rw [s16c4v1_mod_card_subgroupOf σ E hEle hS, hEcard, pow_one]
  obtain ⟨γ, hγE, hγ1⟩ : ∃ γ ∈ E', γ ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one E' with hbot | h
    · exfalso
      rw [hbot] at hcard'
      simp at hcard'
    · exact h
  exact ⟨γ, hγ1, hE'.2 γ hγE,
    by simpa [CFSG.ClassicalGroups.Unitary.smul_def] using hEfix (γ : GL (Fin 4) K) hγE⟩

theorem s16c4v1_cover_model (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    (E : Subgroup ↥(SUid σ 4)) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    {v : Fin 4 → K} (hv : v ≠ 0) :
    ∃ g e : ↥(SUid σ 4), e ∈ E ∧ e ≠ 1 ∧ e • (g • v) = g • v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : SUid σ 4 = StatedSU 4 (2 ^ 1) K := s16c4v1_mod_suid_eq_statedSU σ hK hσ
  let φ : ↥(SUid σ 4) ≃* ↥(unitarySU 2 1 K 4) := MulEquiv.subgroupCongr hS
  let E₀ : Subgroup ↥(unitarySU 2 1 K 4) := E.map φ.toMonoidHom
  have hE₀ : IsElemAbelian 3 E₀ := hE.map φ.toMonoidHom
  have hcard₀ : Nat.card E₀ = 3 ^ 3 := by
    show Nat.card (E.map φ.toMonoidHom) = 3 ^ 3
    rw [Subgroup.card_map_of_injective φ.injective, hcard]
  have hU : UnitaryFieldData 2 1 K := CFSG.Quasithin.RonanF57.unitaryFieldData_of_card hK
  obtain ⟨s, hs⟩ := s15k_om6_conj_torus hU E₀ hE₀
  obtain ⟨-, hTcard⟩ := s15k_om6_torus hU
  set T := (torusSU 3 4 K).subgroupOf (unitarySU 2 1 K 4) with hT
  have hle : E₀.map (MulAut.conj s).toMonoidHom ≤ T := by
    rintro y ⟨z, hz, rfl⟩
    exact hs z hz
  have hTeq : E₀.map (MulAut.conj s).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, hcard₀, hTcard]
      norm_num)
  obtain ⟨γ, hγ1, hγ3, hγv⟩ := s16c4v1_stab_ne_zero σ hK hσ hv
  let γ₁ : ↥(unitarySU 2 1 K 4) := φ γ
  have hγ₁1 : γ₁ ≠ 1 := by
    intro h
    apply hγ1
    have h2 := congrArg φ.symm h
    simpa [γ₁] using h2
  have hγ₁3 : γ₁ ^ 3 = 1 := by
    have h2 := congrArg φ hγ3
    simpa [γ₁] using h2
  have hγ₁v : γ₁ • v = v := by
    rw [Subgroup.smul_def,
      show (γ₁ : GL (Fin 4) K) = (γ : GL (Fin 4) K) from MulEquiv.subgroupCongr_apply hS γ]
    exact hγv
  have hγ₁E : IsElemAbelian 3 (Subgroup.zpowers γ₁) := isElemAbelian_zpowers hγ₁3
  obtain ⟨s', hs'⟩ := s15k_om6_conj_torus hU (Subgroup.zpowers γ₁) hγ₁E
  have hmemT : s' * γ₁ * s'⁻¹ ∈ T :=
    Subgroup.mem_subgroupOf.mpr (hs' γ₁ (Subgroup.mem_zpowers γ₁))
  rw [← hTeq] at hmemT
  obtain ⟨e₀, he₀E, he₀eq⟩ := Subgroup.mem_map.mp hmemT
  let g₁ : ↥(unitarySU 2 1 K 4) := s⁻¹ * s'
  have he₀eq' : s * e₀ * s⁻¹ = s' * γ₁ * s'⁻¹ := by
    simpa [MulAut.conj_apply] using he₀eq
  have he₀conj : e₀ = g₁ * γ₁ * g₁⁻¹ := by
    have h := congrArg (fun x => s⁻¹ * x * s) he₀eq'
    calc e₀ = s⁻¹ * (s * e₀ * s⁻¹) * s := by group
      _ = s⁻¹ * (s' * γ₁ * s'⁻¹) * s := by rw [h]
      _ = g₁ * γ₁ * g₁⁻¹ := by simp only [g₁]; group
  have he₀1 : e₀ ≠ 1 := by
    rw [he₀conj]
    intro h
    apply hγ₁1
    have h2 := congrArg (fun x => g₁⁻¹ * x * g₁) h
    simpa [mul_assoc] using h2
  have hfix : e₀ • (g₁ • v) = g₁ • v := by
    calc e₀ • (g₁ • v) = (e₀ * g₁) • v := (mul_smul e₀ g₁ v).symm
      _ = (g₁ * γ₁) • v := by rw [he₀conj]; group
      _ = g₁ • (γ₁ • v) := mul_smul g₁ γ₁ v
      _ = g₁ • v := by rw [hγ₁v]
  obtain ⟨x, hxE, hxeq⟩ := Subgroup.mem_map.mp he₀E
  have hex : φ.symm e₀ = x := by
    rw [← hxeq]
    simpa using φ.symm_apply_apply x
  have hval : ∀ (y : ↥(unitarySU 2 1 K 4)) (w : Fin 4 → K), (φ.symm y) • w = y • w := by
    intro y w
    rw [Subgroup.smul_def, Subgroup.smul_def,
      show ((φ.symm y : ↥(SUid σ 4)) : GL (Fin 4) K) = (y : GL (Fin 4) K) from
        MulEquiv.subgroupCongr_symm_apply hS y]
  refine ⟨φ.symm g₁, φ.symm e₀, ?_, ?_, ?_⟩
  · rw [hex]
    exact hxE
  · intro h
    apply he₀1
    have h2 := congrArg φ h
    simpa using h2
  · rw [hval g₁ v, hval e₀ (g₁ • v)]
    exact hfix

theorem s16c4v1_lin_normalizer (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A)
    (hN : ∀ g : ↥(SUid σ 4), ∃ g' : ↥(SUid σ 4),
      ∀ x : Fin 4 → K, A *ᵥ (g • x) = g' • (A *ᵥ x)) :
    ∃ (c : K) (γ : ↥(SUid σ 4)), c ≠ 0 ∧ ∀ x : Fin 4 → K, A *ᵥ x = c • (γ • x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData 2 1 K := CFSG.Quasithin.RonanF57.unitaryFieldData_of_card hK
  have hS2 : SUid σ 4 = StatedSU 4 2 K := by
    simpa only [pow_one] using s16c4v1_mod_suid_eq_statedSU σ hK hσ
  let u : GL (Fin 4) K := hA.unit
  have hu : (u : Matrix (Fin 4) (Fin 4) K) = A := IsUnit.unit_spec hA
  have hmap : (SUid σ 4).map (MulAut.conj u).toMonoidHom ≤ SUid σ 4 := by
    rintro x ⟨g, hg, rfl⟩
    let gs : ↥(SUid σ 4) := ⟨g, hg⟩
    obtain ⟨g', hg'x⟩ := hN gs
    have hmat : (u : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) =
        ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) := by
      apply Matrix.ext_of_mulVec_single
      intro j
      simpa only [CFSG.ClassicalGroups.Unitary.smul_def, ← Matrix.mulVec_mulVec, ← hu, gs]
        using hg'x (Pi.single j 1)
    have hconj : (MulAut.conj u).toMonoidHom (g : GL (Fin 4) K) = (g' : GL (Fin 4) K) := by
      apply Units.ext
      show (u : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) *
          ((u⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      calc (u : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) *
            ((u⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
          = ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) *
              ((u⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by rw [hmat]
        _ = ((g' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
            rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [hconj]
    exact g'.2
  have heq : (SUid σ 4).map (MulAut.conj u).toMonoidHom = SUid σ 4 :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj u).injective])
  have heqSU : (StatedSU 4 2 K).map (MulAut.conj u).toMonoidHom = StatedSU 4 2 K := by
    rw [← hS2]
    exact heq
  have huN : u ∈ CFSG.Quasithin.RonanF57.NSU K :=
    CFSG.Quasithin.RonanF57.mem_NSU_of_map_conj_eq heqSU
  obtain ⟨c, u', hc, hu'unit, hAeq⟩ :=
    CFSG.Quasithin.RonanF57.exists_unitary_scalar_of_mem_NSU hK huN
  have hbar : (CFSG.Quasithin.RonanF57.unitaryFieldData_of_card hK).bar = (σ : K →+* K) := by
    ext x
    rw [CFSG.Quasithin.RonanF57.bar_eq_sq]
    exact (s16c4v1_mod_sigma_apply σ hK hσ x).symm
  have hu'unit' : ((u' : Matrix (Fin 4) (Fin 4) K).map σ)ᵀ *
      (u' : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [hbar] at hu'unit
    exact hu'unit
  set d : K := (u' : Matrix (Fin 4) (Fin 4) K).det with hd
  have hdsig : σ d * d = 1 := by
    have h1 := congrArg Matrix.det hu'unit'
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    have h2 : ((u' : Matrix (Fin 4) (Fin 4) K).map σ).det = σ d := by
      have h3 := RingHom.map_det (σ : K →+* K) (u' : Matrix (Fin 4) (Fin 4) K)
      rw [hd]
      exact h3.symm
    rwa [h2, hd] at h1
  have hd3 : d ^ 3 = 1 := by
    calc d ^ 3 = d ^ 2 * d := by ring
      _ = 1 := by rw [← s16c4v1_mod_sigma_apply σ hK hσ d]; exact hdsig
  have hd0 : d ≠ 0 := fun h0 => by rw [h0] at hd3; simp at hd3
  set u'' : Matrix (Fin 4) (Fin 4) K := d⁻¹ • (u' : Matrix (Fin 4) (Fin 4) K) with hu''
  have hu'eq : (u' : Matrix (Fin 4) (Fin 4) K) = d • u'' := by
    rw [hu'', smul_smul, mul_inv_cancel₀ hd0, one_smul]
  have hdet : u''.det = 1 := by
    rw [hu'', Matrix.det_smul, Fintype.card_fin, hd]
    calc (d⁻¹ : K) ^ 4 * d = (d ^ 3)⁻¹ := by
          rw [← inv_pow]
          field_simp
      _ = 1 := by rw [hd3, inv_one]
  have hconj : CFSG.LieType.Universal.Unitary.conjTr σ u'' * u'' = 1 := by
    show ((u''.map σ)ᵀ) * u'' = 1
    rw [hu'']
    have hmap' : ((d⁻¹ • (u' : Matrix (Fin 4) (Fin 4) K)).map σ) =
        σ d⁻¹ • ((u' : Matrix (Fin 4) (Fin 4) K).map σ) := by
      ext i j
      simp [Matrix.map_apply, Matrix.smul_apply, map_mul]
    rw [hmap', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu'unit']
    have hsc : σ d⁻¹ * d⁻¹ = 1 := by
      calc σ d⁻¹ * d⁻¹ = (σ d)⁻¹ * d⁻¹ := by rw [map_inv₀]
        _ = d⁻¹ * (σ d)⁻¹ := by rw [mul_comm]
        _ = (d * σ d)⁻¹ := (mul_inv d (σ d)).symm
        _ = (σ d * d)⁻¹ := by rw [mul_comm]
        _ = 1 := by rw [hdsig, inv_one]
    rw [hsc, one_smul]
  have hiso : ∀ x y, herm σ (u'' *ᵥ x) (u'' *ᵥ y) = herm σ x y := by
    intro x y
    rw [herm_mulVec, hconj, Matrix.one_mulVec]
  let γ : ↥(SUid σ 4) := CFSG.ClassicalGroups.Unitary.mkSU σ u'' hdet hiso
  refine ⟨c * d, γ, mul_ne_zero hc hd0, fun x => ?_⟩
  calc A *ᵥ x = (c • (u' : Matrix (Fin 4) (Fin 4) K)) *ᵥ x := by rw [← hu, hAeq]
    _ = c • ((u' : Matrix (Fin 4) (Fin 4) K) *ᵥ x) := Matrix.smul_mulVec _ _ _
    _ = c • (d • (u'' *ᵥ x)) := by rw [hu'eq, Matrix.smul_mulVec]
    _ = (c * d) • (u'' *ᵥ x) := by rw [smul_smul]
    _ = (c * d) • (γ • x) := by
        rw [show γ • x = u'' *ᵥ x from
          CFSG.ClassicalGroups.Unitary.mkSU_smul σ u'' hdet hiso x]

private def s16c4v1_mod_hermForm (hσ : IsUnitaryInvolution σ) :
    CFSG.LieType.BorelTits.ReflForm K (Fin 4 → K) where
  σ := σ
  β := herm σ
  add_left := herm_add_left σ
  smul_left := fun c u v => herm_smul_left σ c u v
  add_right := herm_add_right σ
  smul_right := fun c u v => herm_smul_right σ c u v
  refl := fun u v h => by rw [herm_conj σ hσ.invol, h, map_zero]
  nondeg := fun u h => eq_zero_of_herm σ h

private theorem s16c4v1_mod_totallyIsotropic (hσ : IsUnitaryInvolution σ)
    {P : Submodule K (Fin 4 → K)} (hP : ∀ x ∈ P, herm σ x x = 0) :
    ∀ x ∈ P, ∀ y ∈ P, herm σ x y = 0 := by
  intro x hx y hy
  by_contra hd
  obtain ⟨c₀, hc₀⟩ := hσ.trace_surj 1 (map_one σ)
  set c : K := c₀ * (herm σ x y)⁻¹ with hc
  have hmem : x + c • y ∈ P := P.add_mem hx (P.smul_mem c hy)
  have h1 := hP (x + c • y) hmem
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
    hP x hx, hP y hy, herm_conj σ hσ.invol x y, mul_zero, zero_mul, add_zero,
    zero_add] at h1
  have h2 : c * herm σ x y = c₀ := by
    rw [hc, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have h3 : σ c * σ (herm σ x y) = σ c₀ := by rw [← map_mul, h2]
  rw [h2, h3, add_comm] at h1
  exact one_ne_zero (hc₀.symm.trans h1)

theorem s16c4v1_isotropic (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    (P : Submodule K (Fin 4 → K)) (hP : ∀ x ∈ P, herm σ x x = 0) :
    (∀ x ∈ P, ∀ y ∈ P, herm σ x y = 0) ∧ Module.finrank K P ≤ 2 := by
  have htot := s16c4v1_mod_totallyIsotropic σ hσ hP
  refine ⟨htot, ?_⟩
  set F := s16c4v1_mod_hermForm σ hσ with hF
  have hle : P ≤ F.perp P := fun x hx => F.mem_perp.mpr fun y hy => htot y hy x hx
  have h1 := F.finrank_perp P
  rw [Module.finrank_fin_fun] at h1
  have h2 := Submodule.finrank_mono hle
  omega

theorem s16c4v1_perp_self (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    (P : Submodule K (Fin 4 → K)) (hP : ∀ x ∈ P, ∀ y ∈ P, herm σ x y = 0)
    (h2 : Module.finrank K P = 2) :
    ∀ x : Fin 4 → K, (∀ y ∈ P, herm σ y x = 0) → x ∈ P := by
  intro x hx
  set F := s16c4v1_mod_hermForm σ hσ with hF
  have hle : P ≤ F.perp P := fun y hy => F.mem_perp.mpr fun z hz => hP z hz y hy
  have hdim : Module.finrank K P = Module.finrank K (F.perp P) := by
    have h1 := F.finrank_perp P
    rw [Module.finrank_fin_fun] at h1
    omega
  have heq : P = F.perp P := Submodule.eq_of_le_of_finrank_eq hle hdim
  rw [heq]
  exact F.mem_perp.mpr hx

private theorem s16c4v1_mod_root_coeff (hK : Nat.card K = 4)
    (hσ : IsUnitaryInvolution σ) {v : Fin 4 → K} (hv : v ≠ 0)
    (hvsing : herm σ v v = 0) (γ : ↥(SUid σ 4))
    (hγ : ∀ x : Fin 4 → K, γ • x - x ∈ K ∙ v) :
    ∃ c : K, c + σ c = 0 ∧ ∀ x : Fin 4 → K, γ • x = x + (c * herm σ v x) • v := by
  have hex : ∀ x : Fin 4 → K, ∃ a : K, a • v = γ • x - x :=
    fun x => Submodule.mem_span_singleton.mp (hγ x)
  choose f hf using hex
  have hxsplit : ∀ x : Fin 4 → K, γ • x = x + f x • v := by
    intro x
    rw [hf x]
    abel
  have hA : ∀ x y : Fin 4 → K, σ (f x) * herm σ v y + f y * herm σ x v = 0 := by
    intro x y
    have h1 := herm_smul_smul σ γ x y
    rw [hxsplit x, hxsplit y] at h1
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hvsing,
      mul_zero, zero_mul, add_zero, zero_add] at h1
    have h4 : herm σ x y + (σ (f x) * herm σ v y + f y * herm σ x v) = herm σ x y + 0 := by
      rw [add_zero]
      simpa only [add_assoc] using h1
    exact add_left_cancel h4
  have hfv : f v = 0 := by
    obtain ⟨y, hy⟩ := exists_herm_ne_zero σ hv
    have h1 := hA v y
    rw [hvsing, mul_zero, add_zero] at h1
    have h2 : σ (f v) = 0 := (mul_eq_zero.mp h1).resolve_right hy
    exact (map_eq_zero_iff σ σ.injective).mp h2
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
    by_contra h
    rw [not_exists] at h
    exact hv (funext fun i => not_not.mp (h i))
  set y₀ : Fin 4 → K := (σ (v i))⁻¹ • (Pi.single i 1 : Fin 4 → K) with hy₀
  have hy₀1 : herm σ v y₀ = 1 := by
    rw [hy₀, herm_smul_right, herm_single_right, mul_one]
    exact inv_mul_cancel₀ ((map_ne_zero σ).mpr hi)
  have hfx : ∀ x : Fin 4 → K, f x = σ (-(f y₀)) * herm σ v x := by
    intro x
    have h1 := hA x y₀
    rw [hy₀1, mul_one] at h1
    have h2 : σ (f x) = -(f y₀ * herm σ x v) := eq_neg_of_add_eq_zero_left h1
    have h3 : f x = σ (-(f y₀ * herm σ x v)) := by
      rw [← h2]
      exact (hσ.invol (f x)).symm
    rw [h3, map_neg, map_mul, map_neg, (herm_conj σ hσ.invol x v).symm]
    ring
  set c : K := σ (-(f y₀)) with hc
  have hc0 : c + σ c = 0 := by
    obtain ⟨w, hw⟩ := exists_herm_ne_zero σ hv
    have h1 := hA w w
    rw [hfx w, herm_conj σ hσ.invol v w, map_mul] at h1
    have h2 : (c + σ c) * (herm σ v w * σ (herm σ v w)) = 0 := by
      have heq : (c + σ c) * (herm σ v w * σ (herm σ v w)) =
          σ c * σ (herm σ v w) * herm σ v w + c * herm σ v w * σ (herm σ v w) := by
        ring
      rw [heq]
      exact h1
    have h3 : herm σ v w * σ (herm σ v w) ≠ 0 :=
      mul_ne_zero hw ((map_ne_zero σ).mpr hw)
    exact (mul_eq_zero.mp h2).resolve_right h3
  exact ⟨c, hc0, fun x => by rw [hxsplit x, hfx x]⟩

theorem s16c4v1_root_card (hK : Nat.card K = 4) (hσ : IsUnitaryInvolution σ)
    (P : Submodule K (Fin 4 → K)) (hP1 : Module.finrank K P = 1)
    (hP : ∀ x ∈ P, herm σ x x = 0) (X : Subgroup ↥(SUid σ 4))
    (hX : ∀ γ ∈ X, ∀ x : Fin 4 → K, γ • x - x ∈ P) : Nat.card X ≤ 2 := by
  classical
  obtain ⟨v₀, hv₀, hspan⟩ := finrank_eq_one_iff'.mp hP1
  set v : Fin 4 → K := (v₀ : Fin 4 → K) with hv
  have hv0 : v ≠ 0 := fun h => hv₀ (Subtype.ext h)
  have hvsing : herm σ v v = 0 := hP v v₀.2
  have hPspan : P = K ∙ v := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨a, ha⟩ := hspan ⟨x, hx⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨a, congrArg Subtype.val ha⟩
    · rw [hv]
      exact (Submodule.span_singleton_le_iff_mem (v₀ : Fin 4 → K) P).mpr v₀.2
  have hX' : ∀ (γ : X) (x : Fin 4 → K),
      ((γ : ↥(SUid σ 4)) • x - x) ∈ K ∙ v := by
    intro γ x
    rw [← hPspan]
    exact hX (γ : ↥(SUid σ 4)) γ.2 x
  have hexc : ∀ γ : X, ∃ c : K, c + σ c = 0 ∧
      ∀ x : Fin 4 → K, ((γ : ↥(SUid σ 4)) • x = x + (c * herm σ v x) • v) :=
    fun γ => s16c4v1_mod_root_coeff σ hK hσ hv0 hvsing (γ : ↥(SUid σ 4)) (hX' γ)
  choose c hc using hexc
  have hc01 : ∀ γ : X, c γ = 0 ∨ c γ = 1 := by
    intro γ
    have h1 := (hc γ).1
    rw [s16c4v1_mod_sigma_apply σ hK hσ] at h1
    have h2 : c γ * (1 + c γ) = 0 := by
      have heq : c γ * (1 + c γ) = c γ + c γ ^ 2 := by ring
      rw [heq]
      exact h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      have h' : c γ + 1 = 0 := by rwa [add_comm] at h
      have hneg : c γ = -1 := eq_neg_of_add_eq_zero_left h'
      have hneg1 : (-1 : K) = 1 := by
        rw [neg_eq_iff_add_eq_zero]
        simpa only [one_add_one_eq_two] using s16c4v1_mod_char_two hK
      rw [hneg, hneg1]
  let Ψ : X → {c : K // c = 0 ∨ c = 1} := fun γ => ⟨c γ, hc01 γ⟩
  have hΨ : Function.Injective Ψ := by
    intro γ₁ γ₂ h
    have hc12 : c γ₁ = c γ₂ := congrArg Subtype.val h
    apply Subtype.ext
    apply CFSG.ClassicalGroups.Unitary.ext_smul
    intro x
    rw [(hc γ₁).2 x, (hc γ₂).2 x, hc12]
  have hcard2 : Nat.card {c : K // c = 0 ∨ c = 1} ≤ 2 := by
    let g : {c : K // c = 0 ∨ c = 1} → Fin 2 := fun c => if c.1 = 0 then 0 else 1
    have hg : Function.Injective g := by
      intro a b hab
      rcases a.2 with ha | ha <;> rcases b.2 with hb | hb
      · exact Subtype.ext (ha.trans hb.symm)
      · exfalso
        have ha' : g a = (0 : Fin 2) := by simp [g, ha]
        have hb' : g b = (1 : Fin 2) := by simp [g, hb]
        rw [ha', hb'] at hab
        exact (by decide : (0 : Fin 2) ≠ 1) hab
      · exfalso
        have ha' : g a = (1 : Fin 2) := by simp [g, ha]
        have hb' : g b = (0 : Fin 2) := by simp [g, hb]
        rw [ha', hb'] at hab
        exact (by decide : (1 : Fin 2) ≠ 0) hab
      · exact Subtype.ext (ha.trans hb.symm)
    have := Nat.card_le_card_of_injective g hg
    simpa using this
  exact (Nat.card_le_card_of_injective Ψ hΨ).trans hcard2

end Model

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
