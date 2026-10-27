module

public import CFSG.Quasithin.Vol2.KGNatSL2Nat
public import CFSG.Quasithin.Vol2.Ch11SecHFacts

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.CGT.Timmesfeld75
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped MatrixGroups

theorem factSL2NatBorel_holds : Ch11.SecH.FactSL2NatBorel := by
  intro F _ _ n hn hF W _ _ hW H U π hπ S hS y hyH hyN hodd
  have : CharP F 2 := charP_two_of_card (by omega) hF
  obtain ⟨f, hf⟩ := exists_isSecCoord hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_utri hf hS
  obtain ⟨hinj, hsurj⟩ := rho2_bijective hf
  obtain ⟨A, hA⟩ := hsurj ⟨y, hyH⟩
  obtain rfl : y = ((rho2 π A : ↥H) : MulAut W) := by rw [hA]
  have hmemS : ∀ h : SL(2, F), ((rho2 π (g * h * g⁻¹) : ↥H) : MulAut W) ∈ S ↔ h ∈ utri F := by
    intro h
    refine ⟨fun hh => ?_, fun hh => (hg _).mpr ⟨h, hh, rfl⟩⟩
    obtain ⟨v, hv, hveq⟩ := (hg _).mp hh
    rwa [mul_left_cancel (mul_right_cancel (hinj (Subtype.ext hveq)))]
  set b := g⁻¹ * A * g with hbdef
  have hbN : b ∈ Subgroup.normalizer (utri F : Set SL(2, F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [← hmemS h, ← hmemS (b * h * b⁻¹),
      show g * (b * h * b⁻¹) * g⁻¹ = A * (g * h * g⁻¹) * A⁻¹ by rw [hbdef]; group,
      map_mul (rho2 π) (A * (g * h * g⁻¹)) A⁻¹, map_mul (rho2 π) A (g * h * g⁻¹),
      map_inv (rho2 π) A]
    exact Subgroup.mem_normalizer_iff.mp hyN _
  rw [normalizer_utri_eq_borel] at hbN
  have hb10 : b 1 0 = 0 := hbN
  have hdet : b 0 0 * b 1 1 = 1 := by
    have h := sl2_det b
    rw [hb10, mul_zero, sub_zero] at h
    exact h
  set ge : Fin 2 → F := (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] with hge
  have hge0 : ge ≠ 0 := sl2_e0_ne_zero g
  have hAx : ∀ x : Fin 2 → F, (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x =
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ((b : Matrix (Fin 2) (Fin 2) F) *ᵥ
        (((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ x)) := by
    intro x
    rw [← conjSL_mulVec, show g * b * g⁻¹ = A by rw [hbdef]; group]
  have hAge : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ ge = b 0 0 • ge := by
    rw [hAx, hge, sl_inv_mul_mulVec, mulVec_e0, hb10, ← Matrix.mulVec_smul]
    congr 1
    ext i
    fin_cases i <;> simp
  have hyU : ∀ u ∈ U, ((rho2 π A : ↥H) : MulAut W) u ∈ U := fun u hu => hf.stab _ hyH u hu
  obtain ⟨μ, hμU, hμ⟩ := exists_scalar_ext hW hf.map_mul hf.ker hf.surj (b 1 1)
  refine ⟨μ, hμU, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh u hu
    obtain ⟨C, hC⟩ := hsurj ⟨h, hh⟩
    obtain rfl : h = ((rho2 π C : ↥H) : MulAut W) := by rw [hC]
    refine hf.inj (hμU _ (hf.stab _ hh u hu)) (hf.stab _ hh _ (hμU u hu)) ?_
    rw [hμ _ (hf.stab _ hh u hu), hf.act2 C hu, hf.act2 C (hμU u hu), hμ u hu,
      Matrix.mulVec_smul]
  · choose uOf huOf hfuOf using fun t : F => hf.surj (t • ge)
    rw [← hF]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun t : F =>
      (⟨uOf t, huOf t, (fixed2_iff hf hg (huOf t)).mpr ⟨t, hfuOf t⟩⟩ :
        {u : W // u ∈ U ∧ ∀ s ∈ S, s u = u})) ⟨fun t t' h => ?_, ?_⟩)
    · have h1 := congrArg (fun x : {u : W // u ∈ U ∧ ∀ s ∈ S, s u = u} => f x.1) h
      simp only [hfuOf] at h1
      exact smul_left_injective F hge0 h1
    · rintro ⟨u, hu, hfix⟩
      obtain ⟨t, ht⟩ := (fixed2_iff hf hg hu).mp hfix
      exact ⟨t, Subtype.ext (hf.inj (huOf t) hu ((hfuOf t).trans ht.symm))⟩
  · intro u hu hfix
    obtain ⟨t, ht⟩ := (fixed2_iff hf hg hu).mp hfix
    rw [← hge] at ht
    refine hf.inj (hμU _ (hyU u hu)) hu ?_
    rw [hμ _ (hyU u hu), hf.act2 A hu, ht, Matrix.mulVec_smul, hAge, smul_smul, smul_smul,
      show b 1 1 * t * b 0 0 = t * (b 0 0 * b 1 1) by ring, hdet, mul_one]
  · intro u hu s hs
    have hw : ((rho2 π A : ↥H) : MulAut W) u * (μ u)⁻¹ ∈ U :=
      U.mul_mem (hyU u hu) (U.inv_mem (hμU u hu))
    obtain ⟨z, hz⟩ : ∃ z : Fin 2 → F, f u = (g : Matrix (Fin 2) (Fin 2) F) *ᵥ z :=
      ⟨_, (sl_mul_inv_mulVec g (f u)).symm⟩
    refine ((fixed2_iff hf hg hw).mpr ⟨(b 0 0 - b 1 1) * z 0 + b 0 1 * z 1, ?_⟩) s hs
    rw [hf.map_mul_inv (hyU u hu) (hμU u hu), hf.act2 A hu, hμ u hu, hz, hAx,
      sl_inv_mul_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
    congr 1
    ext i
    fin_cases i
    · simp
      ring
    · simp [hb10]
  · intro hcent u hu
    obtain ⟨u₀, hu₀, hfu₀⟩ := hf.surj ge
    have hfix₀ : ∀ s ∈ S, s u₀ = u₀ := (fixed2_iff hf hg hu₀).mpr ⟨1, by rw [one_smul, hfu₀]⟩
    have h1 := congrArg f (hcent u₀ hu₀ hfix₀)
    rw [hf.act2 A hu₀, hfu₀, hAge] at h1
    have hlam : b 0 0 = 1 := smul_left_injective F hge0 (h1.trans (one_smul F ge).symm)
    have hsq : b ^ 2 = 1 := isElemAbelian_utri.2 _ ⟨hb10, hlam⟩
    have hA2 : A ^ 2 = 1 := by
      rw [show A = g * b * g⁻¹ by rw [hbdef]; group, conj_pow, hsq, mul_one, mul_inv_cancel]
    have hy2 : ((rho2 π A : ↥H) : MulAut W) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hA2, map_one, OneMemClass.coe_one]
    have hy1 : ((rho2 π A : ↥H) : MulAut W) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy2) with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    rw [hy1]
    rfl

end CFSG.Quasithin.Vol2.KGNat
