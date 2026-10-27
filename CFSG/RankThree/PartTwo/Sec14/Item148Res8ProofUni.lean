module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofUniFix
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BFieldPSU
import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS.IVK (fixedField mem_fixedField_iff)
open CFSG.RankThree.PartTwo.KFacts (suField coe_suField psuField psuField_mk suIncl
  mem_range_suIncl_iff bar_coe_fixedField)
open CFSG.HardMathSupport.Solomon.Coordinator (l3bUT l3bUG l3bFix mem_l3bUT_of_fixed
  cube_fix_mem_l3bUT ker_l3bUG l3bUTEquiv)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)

variable {n : ℕ} {K : Type} [Field K]

section Mk

variable {f : ℕ} (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def mkSU3 (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hu : (M.map h.bar)ᵀ * M = 1) : unitarySU 2 f K 3 :=
  ⟨GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero),
    (mem_unitarySU_iff h).mpr ⟨hdet, hu⟩⟩

theorem suField_mkSU3 (σ : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K) (hdet : M.det = 1)
    (hu : (M.map h.bar)ᵀ * M = 1) (hM : M.map σ = M) :
    suField h σ (mkSU3 h M hdet hu) = mkSU3 h M hdet hu := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_suField, coe_glAut]
  exact hM

theorem diagonal_unitary (v : Fin 3 → K) (hv : ∀ i, h.bar (v i) * v i = 1) :
    ((diagonal v).map h.bar)ᵀ * diagonal v = 1 := by
  rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext i
  exact hv i

theorem cyc_unitary :
    ((!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end Mk

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_omega (h : UnitaryFieldData 2 (3 * n) K) (hodd : Odd n) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ h.bar ω = ω ^ 2 ∧ σ ω = ω := by
  have := h.finite
  have : CharP K 2 := h.charP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 2 ^ (2 * (3 * n)) - 1 := by rw [Nat.card_units, h.card]
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [hcard, pow_mul]
    have : (2 ^ 2) ^ (3 * n) % 3 = 1 := by rw [Nat.pow_mod]; norm_num
    have hpos : 1 ≤ (2 ^ 2) ^ (3 * n) := Nat.one_le_pow _ _ (by norm_num)
    omega
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  set ω : K := (u : K) with hωdef
  have hω3 : ω ^ 3 = 1 := by
    rw [hωdef, ← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hω1 : ω ≠ 1 := by
    intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    norm_num at hu
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have e : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp e with e1 | e1
    · exact absurd (sub_eq_zero.mp e1) hω1
    · exact e1
  have hpow : ∀ m : ℕ, m % 3 = 2 → ω ^ m = ω ^ 2 := by
    intro m hm
    rw [← Nat.div_add_mod m 3, hm, pow_add, pow_mul, hω3, one_pow, one_mul]
  refine ⟨ω, hω, ?_, ?_⟩
  · rw [UnitaryFieldData.bar_apply]
    exact hpow _ (two_pow_mod_three_of_odd (Nat.odd_mul.mpr ⟨by decide, hodd⟩))
  ·
    have hroot : σ ω ^ 2 + σ ω + 1 = 0 := by
      rw [← map_pow, ← map_add, ← map_one σ, ← map_add, hω, map_zero]
    have hfac : (σ ω - ω) * (σ ω - ω ^ 2) = 0 := by
      linear_combination hroot - σ ω * hω + hω3
    rcases mul_eq_zero.mp hfac with e | e
    · exact sub_eq_zero.mp e
    · exfalso
      have he : σ ω = ω ^ 2 := sub_eq_zero.mp e
      have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
      have e3 : (σ ^ 3) ω = σ (σ (σ ω)) := by rw [pow_three']; rfl
      rw [hσ3, he, map_pow, he, ← pow_mul, map_pow, he, ← pow_mul] at e3
      have e4 : ω ^ (2 * 2 * 2) = ω ^ 2 := hpow _ (by norm_num)
      rw [e4] at e3
      have hω0 : ω ≠ 0 := by
        intro h0
        rw [h0] at hω3
        norm_num at hω3
      apply hω1
      have e5 : ω * (ω - 1) = 0 := by
        have : (1 : K ≃+* K) ω = ω := rfl
        rw [this] at e3
        linear_combination -e3
      rcases mul_eq_zero.mp e5 with e6 | e6
      · exact absurd e6 hω0
      · exact sub_eq_zero.mp e6

theorem card_unitarySU_eq_three_mul (h : UnitaryFieldData 2 (3 * n) K) (hodd : Odd n)
    {σ : K ≃+* K} (h₀ : UnitaryFieldData 2 n (fixedField σ)) :
    Nat.card (unitarySU 2 n (fixedField σ) 3) = 3 * Nat.card (l3bUT h rfl h₀) := by
  rw [← Nat.card_congr (l3bUTEquiv h rfl h₀).toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (unitaryScalars h₀ 3),
    card_unitaryScalars h₀ (by norm_num : 1 ≤ 3)]
  have hg : Nat.gcd 3 (2 ^ n + 1) = 3 :=
    Nat.gcd_eq_left (by have := two_pow_mod_three_of_odd hodd; omega)
  rw [hg, mul_comm]

theorem overgroup_l3bUT (h : UnitaryFieldData 2 (3 * n) K)
    (hn : 3 ≤ n) (hodd : Odd n) {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (h₀ : UnitaryFieldData 2 n (fixedField σ)) (H : Subgroup (unitaryPSU h 3))
    (hH : l3bUT h rfl h₀ ≤ H) :
    H = ⊤ ∨ (H ≤ Subgroup.normalizer (l3bUT h rfl h₀ : Set (unitaryPSU h 3)) ∧
      Nat.card H ∣ 3 * Nat.card (l3bUT h rfl h₀)) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨ω, hω, hωbar, hσω⟩ := exists_omega h hodd hσ
  obtain ⟨hω3, hωω, hω4⟩ := omega_facts hω
  have hb2 : h.bar (ω ^ 2) = ω := by
    rw [map_pow, hωbar]
    linear_combination hω4
  have hσω2 : σ (ω ^ 2) = ω ^ 2 := by rw [map_pow, hσω]
  set Fq := (fixedField σ ⊓ h.fixedField : Subfield K) with hFq
  set P₀ := l3bUT h rfl h₀ with hP₀
  set Ht := H.comap (unitaryProj h 3) with hHt
  set Hh := Ht.map (suToSL h) with hHh
  have hHU : Hh ≤ (suToSL h).range := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  have hmemHh : ∀ g, g ∈ Ht → suToSL h g ∈ Hh := fun g hg => ⟨g, hg, rfl⟩
  have hmemHt : ∀ g, suToSL h g ∈ Hh → g ∈ Ht := by
    rintro g ⟨g', hg', hgg⟩
    rwa [suToSL_injective h hgg] at hg'
  have hfixHt : ∀ g : unitarySU 2 (3 * n) K 3, suField h σ g = g → g ∈ Ht :=
    fun g hg => hH (mem_l3bUT_of_fixed h rfl h₀ hg)
  have hFqbar : ∀ b ∈ Fq, h.bar b = b := fun b hb =>
    (UnitaryFieldData.mem_fixedField h).mp (Subfield.mem_inf.mp hb).2
  have hFqσ : ∀ b ∈ Fq, σ b = b := fun b hb =>
    (mem_fixedField_iff σ b).mp (Subfield.mem_inf.mp hb).1
  have hrat : ∀ w : Fin 3 → K, (∀ i, σ (w i) = w i) → ∀ hw : barVec h w ⬝ᵥ w = 0,
      ∀ b ∈ Fq, rankOneSL w (barVec h w) hw b ∈ Hh := by
    intro w hwσ hw b hb
    rw [← suToSL_tvSU h w hw (hFqbar b hb)]
    apply hmemHh
    apply hfixHt
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    show (1 + b • vecMulVec w (barVec h w)).map σ = 1 + b • vecMulVec w (barVec h w)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vecMulVec_apply, barVec_apply, hFqσ b hb, hwσ, map_bar_comm]
  have ha₀ : barVec h ![1, 1, 0] ⬝ᵥ ![1, 1, 0] = 0 := by
    have e : barVec h ![1, 1, 0] ⬝ᵥ ![1, 1, 0] = h.bar 1 * 1 + h.bar 1 * 1 := by
      simp [dotProduct, Fin.sum_univ_three, barVec_apply]
    rw [e, map_one]
    linear_combination h2
  have hb₀ : barVec h ![ω, ω ^ 2, 0] ⬝ᵥ ![ω, ω ^ 2, 0] = 0 := by
    have e : barVec h ![ω, ω ^ 2, 0] ⬝ᵥ ![ω, ω ^ 2, 0] =
        h.bar ω * ω + h.bar (ω ^ 2) * ω ^ 2 := by
      simp [dotProduct, Fin.sum_univ_three, barVec_apply]
    rw [e, hb2, hωbar]
    linear_combination 2 * hω3 + h2
  have hab : barVec h ![1, 1, 0] ⬝ᵥ ![ω, ω ^ 2, 0] = 1 := by
    have e : barVec h ![1, 1, 0] ⬝ᵥ ![ω, ω ^ 2, 0] = h.bar 1 * ω + h.bar 1 * ω ^ 2 := by
      simp [dotProduct, Fin.sum_univ_three, barVec_apply]
    rw [e, map_one]
    linear_combination hωω
  have ha₀σ : ∀ i, σ ((![1, 1, 0] : Fin 3 → K) i) = (![1, 1, 0] : Fin 3 → K) i := by
    intro i
    fin_cases i <;> simp
  have hb₀σ : ∀ i, σ ((![ω, ω ^ 2, 0] : Fin 3 → K) i) = (![ω, ω ^ 2, 0] : Fin 3 → K) i := by
    intro i
    fin_cases i <;> simp [hσω]
  have hN1 : h.bar ω * ω = 1 := by
    rw [hωbar]
    linear_combination hω3
  have hN2 : h.bar (ω ^ 2) * ω ^ 2 = 1 := by
    rw [hb2]
    linear_combination hω3
  have hN0 : h.bar (1 : K) * 1 = 1 := by rw [map_one, one_mul]
  have hdiagU : ∀ x y z : K, h.bar x * x = 1 → h.bar y * y = 1 → h.bar z * z = 1 →
      ((diagonal ![x, y, z]).map h.bar)ᵀ * diagonal ![x, y, z] = 1 := by
    intro x y z hx hy hz
    apply diagonal_unitary h
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  have hdet : ∀ x y z : K, (diagonal ![x, y, z]).det = x * y * z := by
    intro x y z
    rw [det_diagonal, Fin.prod_univ_three]
    rfl
  have hdσ : ∀ x y z : K, σ x = x → σ y = y → σ z = z →
      (diagonal ![x, y, z]).map σ = diagonal ![x, y, z] := by
    intro x y z hx hy hz
    rw [diagonal_map (map_zero σ)]
    congr 1
    ext i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  have hd1 : (diagonal ![ω, ω ^ 2, 1]).det = 1 := by
    rw [hdet]
    linear_combination hω3
  have hdD₁ : (diagonal ![1, ω, ω ^ 2]).det = 1 := by
    rw [hdet]
    linear_combination hω3
  have hdD₂ : (diagonal ![1, ω ^ 2, ω]).det = 1 := by
    rw [hdet]
    linear_combination hω3
  have hdP : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [det_fin_three]
    simp
  set d := mkSU3 h (diagonal ![ω, ω ^ 2, 1]) hd1 (hdiagU _ _ _ hN1 hN2 hN0) with hd
  set D₁ := mkSU3 h (diagonal ![1, ω, ω ^ 2]) hdD₁ (hdiagU _ _ _ hN0 hN1 hN2) with hD₁
  set D₂ := mkSU3 h (diagonal ![1, ω ^ 2, ω]) hdD₂ (hdiagU _ _ _ hN0 hN2 hN1) with hD₂
  set Pc := mkSU3 h !![0, 0, 1; 1, 0, 0; 0, 1, 0] hdP (cyc_unitary h) with hPc
  have hdfix : suField h σ d = d :=
    suField_mkSU3 h σ _ _ _ (hdσ _ _ _ hσω hσω2 (map_one σ))
  have hD₁fix : suField h σ D₁ = D₁ :=
    suField_mkSU3 h σ _ _ _ (hdσ _ _ _ (map_one σ) hσω hσω2)
  have hD₂fix : suField h σ D₂ = D₂ :=
    suField_mkSU3 h σ _ _ _ (hdσ _ _ _ (map_one σ) hσω2 hσω)
  have hPcfix : suField h σ Pc = Pc := by
    refine suField_mkSU3 h σ _ _ _ ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rcases uni_rootSet_dichotomy h hn hodd hσ Hh hHU ha₀ hb₀ hab (hrat _ ha₀σ ha₀)
      (hrat _ hb₀σ hb₀) with hS | hall
  swap
  ·
    left
    have hq : 2 ^ (3 * n) ≠ 2 := by
      intro h2'
      have : 3 * n = 1 := Nat.pow_right_injective le_rfl (h2'.trans (pow_one 2).symm)
      omega
    have htop : Ht = ⊤ := eq_top_of_tvSU_mem h hq hω hωbar Ht d rfl (hfixHt d hdfix) Pc rfl
      (hfixHt Pc hPcfix) ha₀ (fun c hc => hmemHt _ (by rw [suToSL_tvSU]; exact hall c hc))
    rw [eq_top_iff]
    intro x _
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
    have : g ∈ Ht := htop ▸ Subgroup.mem_top g
    exact this
  right
  have hsemi := fun (g : SpecialLinearGroup (Fin 3) K) (hg : g ∈ Hh) =>
    exists_map_eq_smul_uni h (by omega) hσ hω hωbar hσω Hh hHU hrat ha₀ hS
      (suToSL h D₁) (suToSL h D₂) (suToSL h Pc) (hmemHh _ (hfixHt _ hD₁fix))
      (hmemHh _ (hfixHt _ hD₂fix)) (hmemHh _ (hfixHt _ hPcfix)) rfl rfl rfl hg
  have hnormζ : ∀ ζ : K, ζ ^ 3 = 1 → h.bar ζ * ζ = 1 := by
    intro ζ hζ
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    have hm : (2 ^ (3 * n) + 1) % 3 = 0 := by
      have := two_pow_mod_three_of_odd (n := 3 * n) (Nat.odd_mul.mpr ⟨by decide, hodd⟩)
      omega
    rw [← Nat.div_add_mod (2 ^ (3 * n) + 1) 3, hm, add_zero, pow_mul, hζ, one_pow]
  have hscal : ∀ g ∈ Ht, ∃ z ∈ unitaryScalars h 3, suField h σ g = g * z := by
    intro g hg
    obtain ⟨ζ, hζ3, hζ⟩ := hsemi (suToSL h g) (hmemHh g hg)
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      norm_num at hζ3
    set u := Units.mk0 ζ hζ0 with hu
    have hun : h.norm (u : K) = 1 := by
      rw [UnitaryFieldData.norm, mul_comm]
      exact hnormζ ζ hζ3
    have hu3 : u ^ 3 = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hζ3, Units.val_one])
    set z : unitarySU 2 (3 * n) K 3 := ⟨GeneralLinearGroup.scalar (Fin 3) u,
      scalar_mem_unitarySU h (by norm_num) hun hu3⟩ with hz
    refine ⟨z, ⟨u, hun, hu3, rfl⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_suField, coe_glAut]
    have e1 : ((SpecialLinearGroup.map σ.toRingHom (suToSL h g) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ := by
      rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_suToSL]
      rfl
    rw [← e1, hζ, coe_suToSL]
    show ζ • ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
    rfl
  have hfixH : ∀ x ∈ H, psuField h σ x = x := by
    intro x hx
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
    obtain ⟨z, hz, hgz⟩ := hscal g hx
    show psuField h σ (g : unitaryPSU h 3) = (g : unitaryPSU h 3)
    rw [psuField_mk, hgz]
    apply QuotientGroup.eq.mpr
    have e : (g * z)⁻¹ * g = z⁻¹ := by group
    rw [e]
    exact (unitaryScalars h 3).inv_mem hz
  have hconjP : ∀ x ∈ H, ∀ y ∈ P₀, x * y * x⁻¹ ∈ P₀ := by
    intro x hx y hy
    obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
    obtain ⟨y₀, rfl⟩ := hy
    obtain ⟨z, hz, hgz⟩ := hscal g hx
    set s := suIncl h h₀ (bar_coe_fixedField h rfl h₀) y₀ with hs
    have hsfix : suField h σ s = s := (mem_range_suIncl_iff h h₀ _ s).mp ⟨y₀, rfl⟩
    have e : unitaryProj h 3 g * l3bUG h rfl h₀ y₀ * (unitaryProj h 3 g)⁻¹ =
        unitaryProj h 3 (g * s * g⁻¹) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [e]
    apply mem_l3bUT_of_fixed h rfl h₀
    have hzc : ∀ w, w * z = z * w := fun w =>
      Subgroup.mem_center_iff.mp (unitaryScalars_le_center h 3 hz) w
    rw [map_mul, map_mul, map_inv, hgz, hsfix]
    calc g * z * s * (g * z)⁻¹ = g * (z * s) * z⁻¹ * g⁻¹ := by group
      _ = g * (s * z) * z⁻¹ * g⁻¹ := by rw [← hzc s]
      _ = g * s * g⁻¹ := by group
  have hnorm : H ≤ Subgroup.normalizer (P₀ : Set (unitaryPSU h 3)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconjP x hx y
    · intro hy
      have := hconjP x⁻¹ (H.inv_mem hx) _ hy
      simpa [mul_assoc] using this
  refine ⟨hnorm, ?_⟩
  have hcube : ∀ x ∈ H, x ^ 3 ∈ P₀ := fun x hx => cube_fix_mem_l3bUT h rfl h₀ (hfixH x hx)
  have hle : Nat.card H ≤ 3 * Nat.card P₀ := by
    rw [← card_unitarySU_eq_three_mul h hodd h₀]
    refine le_trans (Subgroup.card_le_of_le (fun x hx => ?_))
      (Item148Res5.card_eqLocus_psuField_le h rfl h₀)
    exact hfixH x hx
  set P₀' := P₀.subgroupOf H with hP₀'
  have hcardP₀' : Nat.card P₀' = Nat.card P₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have hidx := Subgroup.card_mul_index P₀'
  rw [hcardP₀'] at hidx
  have hpos : 0 < Nat.card P₀ := Nat.card_pos
  have hidx3 : P₀'.index ≤ 3 := by
    by_contra hcon
    have hcon : 3 < P₀'.index := Nat.lt_of_not_le hcon
    have : 3 * Nat.card P₀ < Nat.card H := by
      rw [← hidx]
      nlinarith
    omega
  have hidx2 : P₀'.index ≠ 2 := by
    intro h2'
    have hall : ∀ x : H, x ∈ P₀' := by
      intro x
      have hsq := Subgroup.sq_mem_of_index_two h2' x
      have hcb : x ^ 3 ∈ P₀' := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hcube x x.2
      have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
      rw [this]
      exact P₀'.mul_mem hcb (P₀'.inv_mem hsq)
    have htop : P₀' = ⊤ := eq_top_iff.mpr fun x _ => hall x
    rw [htop, Subgroup.index_top] at h2'
    omega
  have hidx0 : P₀'.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  rw [← hidx]
  interval_cases hi : P₀'.index
  · omega
  · rw [mul_one]
    exact Dvd.intro_left 3 rfl
  · omega
  · rw [mul_comm]

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
