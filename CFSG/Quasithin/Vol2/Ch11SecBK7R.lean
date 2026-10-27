module

public import CFSG.Quasithin.Vol2.Ch11SecBK7Q
public import CFSG.Quasithin.Vol2.KGNatSL3Real

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix Matrix.SpecialLinearGroup
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.JonesParshall (SL3 sl3Diag sl3Diag_coe sl3Diag_ne_zero)

namespace K7

variable {K : Type} [Field K]

theorem diag_sub_surj {d : Fin 3 → K} (hd : ∀ k, d k ≠ 1) (x : Fin 3 → K) :
    ∃ y, diagonal d *ᵥ y - y = x := by
  refine ⟨fun k => x k / (d k - 1), funext fun k => ?_⟩
  rw [Pi.sub_apply, mulVec_diagonal]
  have : d k - 1 ≠ 0 := sub_ne_zero.mpr (hd k)
  field_simp

theorem diag_fix_eq_zero {d : Fin 3 → K} (hd : ∀ k, d k ≠ 1) {y : Fin 3 → K}
    (hy : diagonal d *ᵥ y = y) : y = 0 := by
  funext k
  have h := congrFun hy k
  rw [mulVec_diagonal] at h
  have h' : (d k - 1) * y k = 0 := by linear_combination h
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr (hd k))

theorem sl3Diag_pow_eq_one [Fintype K] {d : Fin 3 → K} (h : d 0 * d 1 * d 2 = 1) :
    sl3Diag d h ^ (Fintype.card K - 1) = 1 := by
  apply Subtype.ext
  change ((sl3Diag d h : SL3 K) : Matrix (Fin 3) (Fin 3) K) ^ (Fintype.card K - 1) = 1
  rw [sl3Diag_coe, diagonal_pow, ← diagonal_one]
  congr 1
  funext k
  exact FiniteField.pow_card_sub_one_eq_one _ (sl3Diag_ne_zero h k)

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem eq_bot_of_sl3 [Finite K] [CharP K 2] [Finite W] {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (hcomm : commV H = ⊤) (hW : ∀ w : W, w ^ 2 = 1) : Z = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have hc2 : c⁻¹ ^ 2 ≠ 1 := by
    intro h
    have h1 : (c⁻¹ - 1) ^ 2 = 0 := by
      linear_combination h + (1 - c⁻¹) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact hc1 (inv_eq_one.mp (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h1)))
  set d : Fin 3 → K := ![c, c, c⁻¹ ^ 2] with hd
  set d' : Fin 3 → K := ![c⁻¹ ^ 2, c, c] with hd'
  have h : d 0 * d 1 * d 2 = 1 := by simp [hd]; field_simp
  have h' : d' 0 * d' 1 * d' 2 = 1 := by simp [hd']; field_simp
  have hd1 : ∀ k, d k ≠ 1 := by intro k; fin_cases k <;> [exact hc1; exact hc1; exact hc2]
  have hd'1 : ∀ k, d' k ≠ 1 := by intro k; fin_cases k <;> [exact hc2; exact hc1; exact hc1]
  set ρ : SL3 K → MulAut W := fun A => ((rho3 π A : ↥H) : MulAut W) with hρ
  have hρmul : ∀ A B, ρ (A * B) = ρ A * ρ B := fun A B => by
    simp only [hρ, map_mul, Subgroup.coe_mul]
  have hρH : ∀ A, ρ A ∈ H := fun A => (rho3 π A).2
  have hact : ∀ A w, f (ρ A w) = (A : Matrix (Fin 3) (Fin 3) K) *ᵥ f w := fun A w =>
    IsCoord.act3 hf A w
  set D := ρ (sl3Diag d h) with hD
  set D' := ρ (sl3Diag d' h') with hD'
  have hodd : Odd (Fintype.card K - 1) := by
    have h2 : 2 ∣ Fintype.card K :=
      (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    have h1 : 1 ≤ Fintype.card K := Fintype.card_pos
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hDk : D ^ (Fintype.card K - 1) = 1 := by
    rw [hD, hρ, ← Subgroup.coe_pow, ← map_pow, sl3Diag_pow_eq_one, map_one, Subgroup.coe_one]
  have hD'k : D' ^ (Fintype.card K - 1) = 1 := by
    rw [hD', hρ, ← Subgroup.coe_pow, ← map_pow, sl3Diag_pow_eq_one, map_one, Subgroup.coe_one]
  set U := (commHom D).range with hU
  set U' := (commHom D').range with hU'
  have hUZ : U ⊓ Z = ⊥ := range_commHom_inf D hodd hDk hW (hZ _ (hρH _))
  have hU'Z : U' ⊓ Z = ⊥ := range_commHom_inf D' hodd hD'k hW (hZ _ (hρH _))
  have hcomm_apply : ∀ (A B : MulAut W), A * B = B * A → ∀ w,
      A (commHom B w) = commHom B (A w) := by
    intro A B hAB w
    rw [commHom_apply, commHom_apply, map_mul, map_inv, ← MulAut.mul_apply, hAB,
      MulAut.mul_apply]
  have hdiag_comm : ∀ (e e' : Fin 3 → K) (he : e 0 * e 1 * e 2 = 1)
      (he' : e' 0 * e' 1 * e' 2 = 1), sl3Diag e he * sl3Diag e' he' = sl3Diag e' he' * sl3Diag e he
      := by
    intro e e' he he'
    apply Subtype.ext
    change diagonal e * diagonal e' = diagonal e' * diagonal e
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _
  have hDD : D * D' = D' * D := by rw [hD, hD', ← hρmul, ← hρmul, hdiag_comm]
  have hfixU : ∀ (e : Fin 3 → K) (he : e 0 * e 1 * e 2 = 1), (∀ k, e k ≠ 1) →
      ∀ {M : Subgroup W}, M ⊓ Z = ⊥ → ∀ m ∈ M, ρ (sl3Diag e he) m = m → m = 1 := by
    intro e he he1 M hMZ m hm hfix
    have h1 : f m = 0 := diag_fix_eq_zero he1 (by
      have := congrArg f hfix
      rwa [hact, sl3Diag_coe] at this)
    have h2 : m ∈ M ⊓ Z := ⟨hm, (hf.ker m).mp h1⟩
    rw [hMZ] at h2
    exact h2
  have hU'le : U' ≤ U := le_range_commHom D (by
    rintro _ ⟨w, rfl⟩
    exact ⟨D w, (hcomm_apply D D' hDD w).symm⟩) (hfixU d h hd1 hU'Z)
  have hUle : U ≤ U' := le_range_commHom D' (by
    rintro _ ⟨w, rfl⟩
    exact ⟨D' w, (hcomm_apply D' D hDD.symm w).symm⟩) (hfixU d' h' hd'1 hUZ)
  have hinv : ∀ A : SL3 K, ∀ u ∈ U, ρ A u ∈ U := by
    intro A
    refine sl3_induction (P := fun A => ∀ u ∈ U, ρ A u ∈ U) ?_ h h' rfl rfl ?_ ?_ A
    · intro A B hA hB u hu
      rw [hρmul, MulAut.mul_apply]
      exact hA _ (hB u hu)
    · intro A hA u hu
      obtain ⟨w, rfl⟩ := hu
      have hAD : ρ A * D = D * ρ A := by rw [hD, ← hρmul, ← hρmul, hA]
      exact ⟨ρ A w, (hcomm_apply (ρ A) D hAD w).symm⟩
    · intro A hA u hu
      obtain ⟨w, rfl⟩ := hUle hu
      have hAD : ρ A * D' = D' * ρ A := by rw [hD', ← hρmul, ← hρmul, hA]
      exact hU'le ⟨ρ A w, (hcomm_apply (ρ A) D' hAD w).symm⟩
  have hsurj : ∀ w : W, ∃ u ∈ U, w * u⁻¹ ∈ Z := by
    intro w
    obtain ⟨y, hy⟩ := diag_sub_surj hd1 (f w)
    obtain ⟨w', hw'⟩ := hf.surj y
    refine ⟨commHom D w', ⟨w', rfl⟩, (hf.eq_iff _ _).mp ?_⟩
    rw [commHom_apply, hf.map_mul_inv, hD, hact, sl3Diag_coe, hw', hy]
  have hle : commV H ≤ U := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, hk, w, rfl⟩
    obtain ⟨A, hA⟩ := (rho3_bijective hf).2 ⟨k, hk⟩
    have hk' : k = ρ A := by
      show k = ((rho3 π A : ↥H) : MulAut W)
      rw [hA]
    obtain ⟨u, hu, hz⟩ := hsurj w
    have e : k w * w⁻¹ = k u * u⁻¹ := by
      have hw : w = (w * u⁻¹) * u := by rw [inv_mul_cancel_right]
      rw [hw, map_mul, hZ k hk _ hz, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
    rw [e, hk']
    exact U.mul_mem (hinv A u hu) (U.inv_mem hu)
  rw [eq_bot_iff]
  intro z hz
  have h2 : z ∈ U ⊓ Z := ⟨hle (hcomm ▸ Subgroup.mem_top z), hz⟩
  rwa [hUZ] at h2

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
