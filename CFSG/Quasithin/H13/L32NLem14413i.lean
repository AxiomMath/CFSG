module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.A6Realize
public import CFSG.Quasithin.H13.L32ANotation
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6
open CFSG.Quasithin.H13.L32A
open scoped IsMulCommutative

@[expose] def uVec3' : Fin 2 → Fin 3 → ZMod 2 := ![![1, 0, 1], ![0, 1, 1]]

@[expose] def M3' (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => uVec3' j (σ⁻¹ (Fin.castSucc i))

theorem M3'_det : ∀ σ : Equiv.Perm (Fin 3), (M3' σ).det = 1 := by decide

theorem M3'_one : M3' 1 = 1 := by decide

theorem M3'_mul : ∀ σ τ : Equiv.Perm (Fin 3), M3' (σ * τ) = M3' σ * M3' τ := by decide

theorem M3'_injective : ∀ σ τ : Equiv.Perm (Fin 3), M3' σ = M3' τ → σ = τ := by decide

theorem M3'_surjective : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    ∃ σ : Equiv.Perm (Fin 3), M3' σ = (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by decide

@[expose] def s3Hom' : Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun σ := ⟨M3' σ, M3'_det σ⟩
  map_one' := Subtype.ext M3'_one
  map_mul' σ τ := Subtype.ext (M3'_mul σ τ)

@[expose] noncomputable def s3Equiv' :
    Equiv.Perm (Fin 3) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective s3Hom' ⟨fun σ τ h => M3'_injective σ τ (congrArg Subtype.val h), fun A => by
    obtain ⟨σ, hσ⟩ := M3'_surjective A
    exact ⟨σ, Subtype.ext hσ⟩⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quasithinO2QuotientIso_of_perm3 {H : Subgroup G}
    (e : OTwoQuot H ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    quasithinO2QuotientIso H (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  refine ⟨((s3Equiv'.prodCongr s3Equiv').toMonoidHom.comp e.toMonoidHom).comp
    (QuotientGroup.mk' _), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H)
      (e.symm ((s3Equiv'.prodCongr s3Equiv').symm y))
    refine ⟨x, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, hx, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]

theorem exists_card_eq_of_iso {Y : Subgroup G} {K : Type*} [Group K]
    (h : quasithinO2QuotientIso Y K) : ∃ a : ℕ, Nat.card Y = Nat.card K * 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hs, hk⟩ := h
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥Y) (r := 2)).exists_card_eq
  refine ⟨a, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hs).toEquiv, hk, ha]

theorem card_SL22 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 36 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card]
  decide +kernel

theorem not_seven_dvd (b : ℕ) : ¬ 7 ∣ 36 * 2 ^ b := by
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num)).mp h with h | h
  · norm_num at h
  · exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h) (by norm_num)

theorem not_nine_dvd (c : ℕ) : ¬ 9 ∣ 168 * 2 ^ c := by
  intro h
  have hc : Nat.Coprime 9 (2 ^ c) := Nat.Coprime.pow_right c (by norm_num)
  have := hc.dvd_of_dvd_mul_right h
  norm_num at this

theorem not_nine_dvd' (n : ℕ) : ¬ 9 ∣ 3 * 2 ^ n := by
  intro h
  have hc : Nat.Coprime 9 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  have := hc.dvd_of_dvd_mul_right h
  norm_num at this

omit [Finite G] in
theorem not_le_of_relIndex_three {Y T : Subgroup G} (hY : (pCoreOf 2 Y).relIndex Y = 3)
    (hT : IsPGroup 2 T) : ¬ Y ≤ T := by
  intro hle
  have hYp : Y ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl (Subgroup.le_normalizer)
      (hT.to_le hle)
  rw [Subgroup.relIndex_eq_one.mpr hYp] at hY
  omega

theorem card_of_relIndex_three {Y : Subgroup G} (hY : (pCoreOf 2 Y).relIndex Y = 3) :
    ∃ m : ℕ, Nat.card Y = 3 * 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y).exists_card_eq
  have h := Subgroup.relIndex_mul_card (pCoreOf 2 Y) Y
  rw [inf_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 Y), hY, hm] at h
  exact ⟨m, h.symm⟩

end CFSG.Quasithin.H13.L14413
