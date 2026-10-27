module

public import CFSG.Quasithin.Vol2.Ch11SecO2F
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalGroup
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp qSp nSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torus lam sl2W sl2Diag
  lam_sl2Diag sl2W_mul_sl2Diag commute_lam_lam coe_lam coe_sl2W_inv pairMat)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (eq_map_psiSp_of_sylow inf_normalizer_eq_sp
  exists_eq_map_torus_sp Usp_eq_unipotent)
open scoped IsMulCommutative commutatorElement Pointwise

namespace O2

variable {K : Type} [Field K]

theorem torusHom_eq_lam (t : Fin 2 → Kˣ) :
    (torusHom t : StatedSp 2 K) = lam 0 (sl2Diag (t 0)) * lam 1 (sl2Diag (t 1)) := by
  rw [lam_sl2Diag, lam_sl2Diag, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp

theorem weyl_conj_torusHom (t : Fin 2 → Kˣ) :
    lam (0 : Fin 2) sl2W * (torusHom t : StatedSp 2 K) * (lam (0 : Fin 2) sl2W)⁻¹ =
      (torusHom ![(t 0)⁻¹, t 1] : StatedSp 2 K) := by
  have h1 : (lam (0 : Fin 2) sl2W : StatedSp 2 K) * lam 0 (sl2Diag (t 0)) =
      lam 0 (sl2Diag (t 0)⁻¹) * lam 0 sl2W := by
    rw [← map_mul, ← map_mul, sl2W_mul_sl2Diag]
  have h2 : Commute (lam (0 : Fin 2) sl2W : StatedSp 2 K) (lam 1 (sl2Diag (t 1))) :=
    commute_lam_lam (by decide) sl2W (sl2Diag (t 1))
  rw [torusHom_eq_lam, torusHom_eq_lam, ← mul_assoc, h1,
    mul_assoc _ (lam (0 : Fin 2) sl2W : StatedSp 2 K) _, h2.eq, ← mul_assoc, mul_inv_cancel_right]
  simp

theorem mulVec_of_mem_Usp {x : StatedSp 2 K} (hx : x ∈ Usp K) (v : Fin 2 ⊕ Fin 2 → K) :
    (mat 2 K x *ᵥ v) (.inr 0) = v (.inr 0) ∧ mat 2 K x *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0 := by
  obtain ⟨a, b, c, r, rfl⟩ := hx
  rw [map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, nSp_mulVec, qSp_mulVec,
    nSp_mulVec, qSp_mulVec]
  refine ⟨by simp [vec4], vec4_eq ?_ ?_ ?_ ?_⟩ <;> simp [vec4]

end O2

open O2 in
theorem factSp4Opp_holds : FactSp4Opp := by
  intro G _ _ T L I n V₁ V₃ X hS hk hV₁ hV₃ hX
  have := SecO1.isMulCommutative hS
  obtain ⟨K, _, _, _, hK, π, f, hf, g, -, hg, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  have hinj := SecO1.IsCoord.injective_of_bot hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := SecO1.isHall_autOn_cartan hS hX
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x₀, hx₀, hDx⟩ := exists_eq_map_torus_sp hf g hD
  rw [← Usp_eq_unipotent] at hx₀
  set h₀ := g * x₀ with hh₀
  set w : StatedSp 2 K := lam (0 : Fin 2) sl2W with hw
  have hXL : X ≤ L := fun x hx => (hX.1 hx).1
  have hXV : X ≤ Subgroup.normalizer (fsuV T I : Set G) := hXL.trans hS.le_normalizer
  obtain ⟨y₀, hy₀, hy₀V, hy₀eq⟩ := SecA.mem_autOn_iff.mp (π (h₀ * w * h₀⁻¹)).2
  have hO2 : IsPGroup 2 (pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hOL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hCV := SecO1.inf_centralizer_eq hS
  have hconjX : X.map (MulAut.conj y₀).toMonoidHom ≤ X ⊔ pCoreOf 2 L := by
    rintro _ ⟨x, hx, rfl⟩
    have hxV := hXV hx
    have h1 : SecA.conjV (fsuV T I) x hxV ∈ (torus 2 K).map (psiSp π h₀) := by
      rw [← hDx]
      exact SecA.conjV_mem_autOn hx hxV
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := h1
    have h2 : psiSp π h₀ (torusHom ![(t 0)⁻¹, t 1]) ∈ autOn X (fsuV T I) := by
      rw [hDx]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    obtain ⟨x', hx', hx'V, hx'eq⟩ := SecA.mem_autOn_iff.mp h2
    have hyx : y₀ * x * y₀⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hy₀V hxV) (Subgroup.inv_mem _ hy₀V)
    have h3 : SecA.conjV (fsuV T I) (y₀ * x * y₀⁻¹) hyx = SecA.conjV (fsuV T I) x' hx'V := by
      rw [← hx'eq, ← weyl_conj_torusHom t, ← hw,
        SecA.conjV_mul _ (Subgroup.mul_mem _ hy₀V hxV) (Subgroup.inv_mem _ hy₀V),
        SecA.conjV_mul _ hy₀V hxV, SecA.conjV_inv _ hy₀V, ← hy₀eq, ← ht, psiSp_apply, psiSp_apply,
        show h₀ * (w * torusHom t * w⁻¹) * h₀⁻¹ =
          h₀ * w * h₀⁻¹ * (h₀ * torusHom t * h₀⁻¹) * (h₀ * w * h₀⁻¹)⁻¹ by group]
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have h4 : x'⁻¹ * (y₀ * x * y₀⁻¹) ∈ pCoreOf 2 L := by
      rw [← hCV]
      refine ⟨L.mul_mem (L.inv_mem (hXL hx')) (L.mul_mem (L.mul_mem hy₀ (hXL hx))
        (L.inv_mem hy₀)), Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h5 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) h3
      simp only [SecA.conjV_apply_coe] at h5
      calc v * (x'⁻¹ * (y₀ * x * y₀⁻¹))
          = x'⁻¹ * (x' * v * x'⁻¹) * x' * (x'⁻¹ * (y₀ * x * y₀⁻¹)) := by group
        _ = x'⁻¹ * (y₀ * x * y₀⁻¹ * v * (y₀ * x * y₀⁻¹)⁻¹) * x' *
            (x'⁻¹ * (y₀ * x * y₀⁻¹)) := by rw [h5]
        _ = x'⁻¹ * (y₀ * x * y₀⁻¹) * v := by group
    have := Subgroup.mul_mem_sup hx' h4
    simpa [MulAut.conj_apply] using this
  have hOX : pCoreOf 2 L ⊓ X = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hX.2.1)
  have hdec : ∀ z ∈ X ⊔ pCoreOf 2 L, ∃ q ∈ pCoreOf 2 L, ∃ m ∈ X, q * m = z := by
    intro z hz
    have h1 : z ∈ ((pCoreOf 2 L : Set G) * (X : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ X (hXL.trans hLO), sup_comm]
      exact hz
    obtain ⟨q, hq, m, hm, hqm⟩ := Set.mem_mul.mp h1
    exact ⟨q, hq, m, hm, hqm⟩
  have hcardS : Nat.card (X.map (MulAut.conj y₀).toMonoidHom) = Nat.card X :=
    Subgroup.card_map_of_injective (f := (MulAut.conj y₀).toMonoidHom) (MulAut.conj y₀).injective
  obtain ⟨o, ho, hoX⟩ := CFSG.LieType.Chevalley.EvenOddRadical.exists_conj_le_of_complement hO2
    le_sup_right (sup_le (hXL.trans hLO) Subgroup.le_normalizer) hOX hdec hconjX
    (by rw [hcardS, ← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hX.2.1)
  have hyN : o * y₀ ∈ Subgroup.normalizer (X : Set G) := by
    have h1 : X.map (MulAut.conj (o * y₀)).toMonoidHom =
        (X.map (MulAut.conj y₀).toMonoidHom).map (MulAut.conj o).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      group
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    show X.map (MulAut.conj (o * y₀)).toMonoidHom = X
    rw [h1]
    refine Subgroup.eq_of_le_of_card_ge hoX (le_of_eq ?_)
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj o).toMonoidHom) (MulAut.conj o).injective,
      hcardS]
  have hoV : o ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    have h1 : o ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by rw [hCV]; exact ho
    exact h1.2
  have hyL : o * y₀ ∈ L := L.mul_mem (hOL ho) hy₀
  have hyV := hS.le_normalizer hyL
  have hyact : SecA.conjV (fsuV T I) (o * y₀) hyV =
      ((π (h₀ * w * h₀⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
    rw [hy₀eq]
    ext v
    rw [SecA.conjV_apply_coe, SecA.conjV_apply_coe]
    have hw' : y₀ * (v : G) * y₀⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.mp hy₀V v).mp v.2
    have hc := Subgroup.mem_centralizer_iff.mp hoV _ hw'
    calc o * y₀ * (v : G) * (o * y₀)⁻¹ = o * (y₀ * (v : G) * y₀⁻¹) * o⁻¹ := by group
      _ = y₀ * (v : G) * y₀⁻¹ * o * o⁻¹ := by rw [← hc]
      _ = y₀ * (v : G) * y₀⁻¹ := by group
  have hw0 : (mat 2 K w⁻¹ *ᵥ vec4 1 0 0 0) (.inr 0) = -1 := by
    rw [hw, ← map_inv, mat_apply, coe_lam, coe_sl2W_inv]
    simp [pairMat, Matrix.mulVec, dotProduct, vec4]
  have e2 : mat 2 K g⁻¹ *ᵥ (mat 2 K (h₀ * w * h₀⁻¹)⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) =
      mat 2 K x₀ *ᵥ (mat 2 K w⁻¹ *ᵥ (mat 2 K x₀⁻¹ *ᵥ vec4 1 0 0 0)) := by
    rw [show (h₀ * w * h₀⁻¹)⁻¹ = g * (x₀ * w⁻¹ * x₀⁻¹) * g⁻¹ by rw [hh₀]; group, conj_mulVec_sp,
      mat_inv_mulVec, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hu1 : (mat 2 K g⁻¹ *ᵥ (mat 2 K (h₀ * w * h₀⁻¹)⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)))
      (.inr 0) = -1 := by
    rw [e2, (mulVec_of_mem_Usp (inv_mem hx₀) 0).2, (mulVec_of_mem_Usp hx₀ _).1, hw0]
  refine ⟨o * y₀, hyL, hyN, eq_bot_iff.mpr ?_⟩
  rintro x ⟨hx1, hx3⟩
  have hxV := conj_le (SecA.IsVi.le_fsuV hV₁) hyV hx1
  obtain ⟨c, hc⟩ := (mem_conj_v1_iff (hV₁g V₁ hV₁) hyV hyact ⟨x, hxV⟩).mp hx1
  have h3 := (mem_iff_of_eq (hV₃g V₃ hV₃) ⟨x, hxV⟩).mp hx3
  rw [mem_spHyp, hc, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hu1, mul_neg, mul_one,
    neg_eq_zero] at h3
  rw [Subgroup.mem_bot]
  have h4 : f ⟨x, hxV⟩ = f 1 := by rw [hc, h3, zero_smul, hf.map_one]
  exact congrArg Subtype.val (hinj h4)

end CFSG.Quasithin.Vol2.Ch11.SecF
