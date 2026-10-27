module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SUFourTorusGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSUFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KCOrthogonal
open scoped Matrix commutatorElement

theorem hasFpfTorusGen_statedOmegaMinus {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    HasFpfTorusGen (StatedOmega (StatedQuadMinus 3 K b c)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, _, _, D, Φ, ψ, ρ, _, hρinj, hρψ, hΦ⟩ :=
    exists_statedOmegaMinus_equiv_sixSU hK hirr
  have : Finite E := D.finite_E
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have hE : Nat.card E = (2 ^ n) ^ 2 := by rw [D.card_E, hK]
  have hσu : IsUnitaryInvolution (unitaryInvolution E 2 n) :=
    isUnitaryInvolution_unitaryInvolution hE
  have hσ : ∀ z, D.σ z = unitaryInvolution E 2 n z :=
    sigma_eq_unitaryInvolution_of_card D hK
  obtain ⟨P, ι, hP, hιP⟩ := exists_sixSU_conjEquiv_SUid D hσu hσ
  have hpq : (↑P : Matrix (Fin 4) (Fin 4) E) * (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqp : (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E) * (↑P : Matrix (Fin 4) (Fin 4) E) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hq1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hq4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmul : (2 ^ n - 1) * (2 ^ n + 1) = (2 ^ n) ^ 2 - 1 := by
    zify [hq1, Nat.one_le_pow 2 (2 ^ n) (by omega)]
    ring
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hE]
  have hlord : orderOf ((g ^ (2 ^ n - 1) : Eˣ) : E) = 2 ^ n + 1 := by
    rw [orderOf_units, orderOf_pow_of_dvd (by omega) ⟨2 ^ n + 1, by rw [hord, hmul]⟩, hord,
      ← hmul, Nat.mul_div_cancel_left _ (by omega)]
  generalize ((g ^ (2 ^ n - 1) : Eˣ) : E) = l at hlord
  have hlnorm : unitaryInvolution E 2 n l * l = 1 := by
    rw [unitaryInvolution_apply, ← pow_succ, ← hlord]
    exact pow_orderOf_eq_one l
  have hl1 : l ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hlord
    omega
  have hl0 : l ≠ 0 := by
    intro h0
    have h := pow_orderOf_eq_one l
    rw [hlord, h0, zero_pow (by omega)] at h
    exact zero_ne_one h
  have hl3 : (l ^ 3)⁻¹ ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one (inv_eq_one.mp h)
    rw [hlord] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hl2 : l ^ 2 ≠ 1 := by
    intro h
    have h1 : orderOf l ∣ 2 := orderOf_dvd_of_pow_eq_one h
    rw [hlord] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    omega
  have hl2inv : (l ^ 2)⁻¹ ≠ 1 := by
    intro h
    exact hl2 (inv_eq_one.mp h)
  have hlinv : (l ^ 3)⁻¹ * l = (l ^ 2)⁻¹ := by
    rw [← inv_pow, ← inv_pow]
    field_simp
  have hoddl : Odd (orderOf l) := by
    rw [hlord]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have h3 : ∃ s : E, s ≠ 0 ∧ unitaryInvolution E 2 n s * s ≠ 1 := by
    refine ⟨g, g.ne_zero, fun h => ?_⟩
    rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val] at h
    have h1 : g ^ (2 ^ n + 1) = 1 := Units.ext (by rw [h, Units.val_one])
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord, ← hmul] at h2
    have h4 := Nat.le_of_dvd (by omega) h2
    have h5 : (2 ^ n - 1) * (2 ^ n + 1) ≤ 1 * (2 ^ n + 1) := by rwa [one_mul]
    have h6 := Nat.le_of_mul_le_mul_right h5 (by omega)
    omega
  obtain ⟨t₀, t₁, hcomm, ho₀, ho₁, ht₀, ht₁⟩ := exists_su4_torus hlnorm
  let γ₀ : ↥(StatedOmega (StatedQuadMinus 3 K b c)) := Φ (ι t₀)
  let γ₁ : ↥(StatedOmega (StatedQuadMinus 3 K b c)) := Φ (ι t₁)
  let d₀ : Fin 4 → E := fun i => if i = 0 then (l ^ 3)⁻¹ else l
  let d₁ : Fin 4 → E := fun i => if i = 1 then (l ^ 3)⁻¹ else l
  have hd₀ : ∀ i k : Fin 4, i ≠ k → d₀ i * d₀ k ≠ 1 := by
    intro i k hik
    by_cases hi : i = 0
    · subst hi
      have hk : k ≠ 0 := by rintro rfl; exact hik rfl
      simp only [d₀, if_pos rfl, if_neg hk]
      rw [hlinv]
      exact hl2inv
    · by_cases hk : k = 0
      · subst hk
        simp only [d₀, if_neg hi, if_pos rfl]
        rw [mul_comm, hlinv]
        exact hl2inv
      · simp only [d₀, if_neg hi, if_neg hk]
        rw [← pow_two]
        exact hl2
  have hd₁ : ∀ i k : Fin 4, i ≠ k → d₁ i * d₁ k ≠ 1 := by
    intro i k hik
    by_cases hi : i = 1
    · subst hi
      have hk : k ≠ 1 := by rintro rfl; exact hik rfl
      simp only [d₁, if_pos rfl, if_neg hk]
      rw [hlinv]
      exact hl2inv
    · by_cases hk : k = 1
      · subst hk
        simp only [d₁, if_neg hi, if_pos rfl]
        rw [mul_comm, hlinv]
        exact hl2inv
      · simp only [d₁, if_neg hi, if_neg hk]
        rw [← pow_two]
        exact hl2
  have hfix_t : ∀ (t : SUid (unitaryInvolution E 2 n) 4) (d : Fin 4 → E),
      (∀ v : Fin 4 → E, t • v = fun i => d i * v i) →
      (∀ i k : Fin 4, i ≠ k → d i * d k ≠ 1) →
      ∀ v : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K,
        (((Φ (ι t) : ↥(StatedOmega (StatedQuadMinus 3 K b c))) :
          GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v = v → v = 0 := by
    intro t d ht hd v hv
    have h1 : ρ (ι t) v = v := by
      rw [← hΦ (ι t) v]
      exact hv
    have h2 : D.sixRho (ι t) (ψ v) = ψ v := by
      rw [← hρψ (ι t) v]
      exact congrArg ψ h1
    have hXalt : IsAltMat (((ψ v : D.sixSpace) : Matrix (Fin 4) (Fin 4) E)) :=
      (D.mem_sixSpace.mp (ψ v).2).1
    have h3 : ((ι t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) *
        ((ψ v : D.sixSpace) : Matrix (Fin 4) (Fin 4) E) *
          ((ι t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ =
        ((ψ v : D.sixSpace) : Matrix (Fin 4) (Fin 4) E) := by
      have h := congrArg Subtype.val h2
      simpa [EvenNormPlane.coe_sixRho] using h
    let X : Matrix (Fin 4) (Fin 4) E := ((ψ v : D.sixSpace) : Matrix (Fin 4) (Fin 4) E)
    let Q : Matrix (Fin 4) (Fin 4) E := (↑(P⁻¹) : Matrix (Fin 4) (Fin 4) E)
    let Y : Matrix (Fin 4) (Fin 4) E := Q * X * Qᵀ
    let T : Matrix (Fin 4) (Fin 4) E := ((t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)
    have hXY : (↑P : Matrix (Fin 4) (Fin 4) E) * Y * (↑P : Matrix (Fin 4) (Fin 4) E)ᵀ = X := by
      calc (↑P : Matrix (Fin 4) (Fin 4) E) * Y * (↑P : Matrix (Fin 4) (Fin 4) E)ᵀ
          = (↑P : Matrix (Fin 4) (Fin 4) E) *
              (Q * X * Qᵀ) * (↑P : Matrix (Fin 4) (Fin 4) E)ᵀ := rfl
        _ = ((↑P : Matrix (Fin 4) (Fin 4) E) * Q) * X *
              (Qᵀ * (↑P : Matrix (Fin 4) (Fin 4) E)ᵀ) := by
              simp only [Matrix.mul_assoc]
        _ = ((↑P : Matrix (Fin 4) (Fin 4) E) * Q) * X *
              (((↑P : Matrix (Fin 4) (Fin 4) E) * Q))ᵀ := by rw [Matrix.transpose_mul]
        _ = 1 * X * 1 := by rw [hpq, Matrix.transpose_one]
        _ = X := by rw [one_mul, mul_one]
    have hYalt : IsAltMat Y := by
      have h := (char_two_alternating_four_Pfaffian_identities (F := E)).2.2.2.2 (P⁻¹) X hXalt
      simpa [Y, Q] using h.1
    have htdiag : T = Matrix.diagonal d := by
      ext i k
      dsimp only [T]
      have h := congrFun (ht (Pi.single k 1)) i
      rw [smul_def, Matrix.mulVec_single_one, Matrix.col_apply] at h
      rw [h]
      simp [Matrix.diagonal, Pi.single_apply]
    have hqg : Q * ((ι t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) =
        T * Q := by
      have hqgGL : P⁻¹ * (ι t) = t * P⁻¹ := by
        rw [hιP]
        group
      have h := congrArg (fun g : GL (Fin 4) E => (g : Matrix (Fin 4) (Fin 4) E)) hqgGL
      simpa [Q] using h
    have hYeq : T * Y * Tᵀ = Y := by
      calc T * Y * Tᵀ
          = (T * Q) * X *
              (T * Q)ᵀ := by
              simp only [Y, Matrix.mul_assoc, Matrix.transpose_mul]
        _ = (Q * ((ι t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)) * X *
              (Q * ((ι t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E))ᵀ := by rw [hqg]
        _ = Q * (((ι t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E) * X *
              ((ι t : GL (Fin 4) E) : Matrix (Fin 4) (Fin 4) E)ᵀ) * Qᵀ := by
              simp only [Matrix.mul_assoc, Matrix.transpose_mul]
        _ = Q * X * Qᵀ := by rw [h3]
        _ = Y := rfl
    have hYzero : Y = 0 := by
      ext i k
      rw [Matrix.zero_apply]
      by_cases hik : i = k
      · subst hik
        exact hYalt.2 i
      · have hentry := congrFun (congrFun hYeq i) k
        rw [htdiag, Matrix.diagonal_transpose] at hentry
        simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hentry
        have hentry' : (d i * d k) * Y i k = Y i k := by
          calc (d i * d k) * Y i k = d i * Y i k * d k := by ring
            _ = Y i k := hentry
        have hzero : (d i * d k - 1) * Y i k = 0 := by
          rw [sub_mul, one_mul, hentry', sub_self]
        exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (hd i k hik))
    have hX0 : X = 0 := by
      rw [← hXY, hYzero]
      simp
    have hψv : ψ v = 0 := Subtype.ext hX0
    exact ψ.injective (by simpa using hψv)
  have ht₀' : ∀ v : Fin 4 → E, t₀ • v = fun i => d₀ i * v i := by
    intro v
    rw [ht₀]
    funext i
    by_cases hi : i = 0 <;> simp [d₀, hi]
  have ht₁' : ∀ v : Fin 4 → E, t₁ • v = fun i => d₁ i * v i := by
    intro v
    rw [ht₁]
    funext i
    by_cases hi : i = 1 <;> simp [d₁, hi]
  let S : Set (SUid (unitaryInvolution E 2 n) 4) :=
    {g | Commute g t₀ ∨ Commute g t₁}
  have hgen : (⊤ : Subgroup (SUid (unitaryInvolution E 2 n) 4)) ≤
      Subgroup.closure S :=
    le_closure_commute_su4 hσu h3 ht₀ ht₁
  let T₀ : Set ↥(StatedOmega (StatedQuadMinus 3 K b c)) := {γ₀, γ₁}
  let f : SUid (unitaryInvolution E 2 n) 4 →* ↥(StatedOmega (StatedQuadMinus 3 K b c)) :=
    (ι.trans Φ).toMonoidHom
  have hfγ₀ : f t₀ = γ₀ := rfl
  have hfγ₁ : f t₁ = γ₁ := rfl
  have himage : f '' S ⊆ {g | ∃ γ ∈ T₀, Commute g γ} := by
    rintro _ ⟨s, hs, rfl⟩
    rcases hs with hs | hs
    · refine ⟨γ₀, by simp [T₀], ?_⟩
      simpa [hfγ₀] using hs.map f
    · refine ⟨γ₁, by simp [T₀], ?_⟩
      simpa [hfγ₁] using hs.map f
  have hgen_top : Subgroup.closure S = ⊤ := top_le_iff.mp hgen
  refine ⟨T₀, ⟨γ₀, by simp [T₀]⟩, ?_, ?_, ?_, ?_⟩
  · rintro γ (rfl | rfl)
    · have hordγ : orderOf (Φ (ι t₀)) = orderOf t₀ :=
        (orderOf_injective Φ.toMonoidHom Φ.injective (ι t₀)).trans
          (orderOf_injective ι.toMonoidHom ι.injective t₀)
      rw [hordγ]
      exact hoddl.of_dvd_nat ho₀
    · have hordγ : orderOf (Φ (ι t₁)) = orderOf t₁ :=
        (orderOf_injective Φ.toMonoidHom Φ.injective (ι t₁)).trans
          (orderOf_injective ι.toMonoidHom ι.injective t₁)
      rw [hordγ]
      exact hoddl.of_dvd_nat ho₁
  · rintro γ (rfl | rfl) v hv
    · exact hfix_t t₀ d₀ ht₀' hd₀ v hv
    · exact hfix_t t₁ d₁ ht₁' hd₁ v hv
  · rintro γ (rfl | rfl) γ' (rfl | rfl)
    · exact Commute.refl _
    · exact (hcomm.map ι).map Φ
    · exact ((hcomm.map ι).map Φ).symm
    · exact Commute.refl _
  · have htop : (⊤ : Subgroup ↥(StatedOmega (StatedQuadMinus 3 K b c))) =
        (Subgroup.closure S).map f := by
      rw [hgen_top, Subgroup.map_top_of_surjective f (ι.trans Φ).surjective]
    rw [htop, MonoidHom.map_closure]
    exact Subgroup.closure_mono himage

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
