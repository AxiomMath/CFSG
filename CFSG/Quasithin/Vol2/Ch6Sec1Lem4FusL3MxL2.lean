module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyCover3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists

private theorem exists_coeffs_inverter_L3mxL2 {F : Type} [Field F] (a b c d : F) :
    ∃ r₁ r₂ r₃ : F, r₁ ^ 2 + r₂ * r₃ = 1 ∧ (a - d) * r₁ + c * r₂ + b * r₃ = 0 := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · exact ⟨0, 1, 1, by ring, by simp [hb, hc]⟩
    · have hci : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
      exact ⟨1, -(a - d) * c⁻¹, 0, by ring, by linear_combination (-(a - d)) * hci⟩
  · have hbi : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
    exact ⟨1, 0, -(a - d) * b⁻¹, by ring, by linear_combination (-(a - d)) * hbi⟩

theorem exists_inverter_statedSL {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 < p) (hF : Nat.card F = p) :
    ∀ B ∈ sl2Of (⊤ : Subgroup (GL (Fin 2) F)), B ^ 5 = 1 → B ≠ 1 →
      ∃ R ∈ (⊤ : Subgroup (GL (Fin 2) F)), R * R = 1 ∧
        (Matrix.GeneralLinearGroup.det R : Fˣ) = -1 ∧ R * B * R⁻¹ = B⁻¹ := by
  intro B hB _ _
  have hdetB : (B : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp only [sl2Of, Subgroup.mem_inf, MonoidHom.mem_ker] at hB
    have h := congrArg Units.val hB.2
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) F, (B : Matrix (Fin 2) (Fin 2) F) = M :=
    ⟨_, rfl⟩
  rw [hM, Matrix.det_fin_two] at hdetB
  obtain ⟨r₁, r₂, r₃, hsq, hlin⟩ :=
    exists_coeffs_inverter_L3mxL2 (M 0 0) (M 0 1) (M 1 0) (M 1 1)
  have hRR : !![r₁, r₂; r₃, -r₁] * !![r₁, r₂; r₃, -r₁] = (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hsq
  obtain ⟨R, hR⟩ : ∃ R : GL (Fin 2) F, (R : Matrix (Fin 2) (Fin 2) F) = !![r₁, r₂; r₃, -r₁] :=
    ⟨⟨!![r₁, r₂; r₃, -r₁], !![r₁, r₂; r₃, -r₁], hRR, hRR⟩, rfl⟩
  have hRR' : R * R = 1 := Units.ext (by rw [Units.val_mul, hR, hRR, Units.val_one])
  have hRinv : R⁻¹ = R := inv_eq_of_mul_eq_one_right hRR'
  have hBBi : M * !![M 1 1, -M 0 1; -M 1 0, M 0 0] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hdetB
  have hBinv : ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![M 1 1, -M 0 1; -M 1 0, M 0 0] :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hM]; exact hBBi)
  have hRB : R * B = B⁻¹ * R := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hR, hBinv, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hlin
  refine ⟨R, Subgroup.mem_top R, hRR', ?_, ?_⟩
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hR, Units.val_neg, Units.val_one,
      Matrix.det_fin_two_of]
    linear_combination -hsq
  · rw [hRinv, hRB, mul_assoc, hRR', mul_one]

private theorem two_ne_zero_rankL3mxL2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hF : Nat.card F = p) : (2 : F) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = p ^ 1 := by rw [pow_one, ← Nat.card_eq_fintype_card, hF]
  let : CharP F p := charP_of_card_eq_prime_pow hFc
  intro h
  have h2 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

private theorem odd_card_of_pow_three_L3mxL2 {Z : Type*} [Group Z] [Finite Z]
    (h : ∀ z : Z, z ^ 3 = 1) : Odd (Nat.card Z) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card Z := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h g)
  rw [hg] at h3
  omega

theorem rank_statedSL {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = p) {G : Type*} [Group G] (ψ : ↥(StatedSL 3 F) →* G)
    (hker : ψ.ker ≤ (StatedScalars (Fin 3) F).subgroupOf (StatedSL 3 F)) :
    ∀ V : Subgroup G, V ≤ ψ.range → IsElemAbelian 2 V → Nat.card V ≤ 4 := by
  intro V hV hVel
  have h2 : (2 : F) ≠ 0 := two_ne_zero_rankL3mxL2 hp hp5 hF
  have hcen : ∀ z ∈ ψ.ker, z ∈ Subgroup.center ↥(StatedSL 3 F) := fun z hz =>
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center (StatedSL 3 F) (hker hz)
  have hz3 : ∀ z ∈ ψ.ker, z ^ 3 = 1 := fun z hz =>
    linConj_ker_pow_three z (by rw [QuotientGroup.ker_mk']; exact hker hz)
  have hodd : Odd (Nat.card ψ.ker) :=
    odd_card_of_pow_three_L3mxL2 (fun z => Subtype.ext (by simpa using hz3 z.1 z.2))
  have hkerc : ∀ g ∈ ψ.ker, ∀ h : ↥(StatedSL 3 F), g * h = h * g := fun g hg h =>
    (Subgroup.mem_center_iff.mp (hcen g hg) h).symm
  have hm : ∀ T : Subgroup ↥(StatedSL 3 F), (∀ x ∈ T, x * x = 1) → Nat.card T ≤ 4 :=
    fun T hT => CFSG.QuasithinUnique.Setup.Family.card_le_four_of_det_one h2 (H := StatedSL 3 F)
      (fun x hx => (linConj_mem_statedSL x).mp hx) T hT
  have hE2 : ∀ x ∈ V, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hVel.2 x hx
  have hEc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  exact CFSG.QuasithinUnique.Setup.Family.card_le_of_lifts ψ hkerc hodd 4 hm V hV hE2 hEc

end CFSG.Quasithin.H13
