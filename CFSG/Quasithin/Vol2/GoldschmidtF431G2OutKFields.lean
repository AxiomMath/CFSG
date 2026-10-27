module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutK
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentZc
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutCent
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFusPar

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.QuasithinUnique CFSG.GH74.GLS.Stage4.Hex

section Fields


variable {K : Type} [Field K] [Finite K] [CharP K 2] {A : LieAmalgamExt (C K)}

theorem centerOf_perfectCore_N_eq {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) {ψ : ↥A.K} {α : MulAut (C K)}
    (P : OutProps (iK A hgen) ψ α) {N : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    centerOf (perfectCore N) = (Xc K).map (iK A hgen) := by
  rw [centerOf_perfectCore_eq hn hK hgen P hN]
  exact congrArg (Subgroup.map (iK A hgen)) (Cent.centerOf_perfectCore_Pr_eq hn hK)

theorem z_mem_centerOf_perfectCore {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) {ψ : ↥A.K} {α : MulAut (C K)}
    (P : OutProps (iK A hgen) ψ α) {N : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    iK A hgen (xc 1) ∈ centerOf (perfectCore N) := by
  rw [centerOf_perfectCore_N_eq hn hK hgen P hN]
  exact Subgroup.mem_map_of_mem _ (xc_mem_Xc 1)

theorem centerOf_outS_le {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hgen : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K) {ψ : ↥A.K} {α : MulAut (C K)}
    (P : OutProps (iK A hgen) ψ α) {N : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    centerOf (outS hgen) ≤ centerOf (perfectCore N) := by
  have hinj : Function.Injective (iK A hgen) := iK_injective A hgen center_C_eq_bot'
  rw [show outS hgen = (U K).map (iK A hgen) from rfl, centerOf_map_inj _ hinj,
    centerOf_perfectCore_N_eq hn hK hgen P hN]
  refine Subgroup.map_mono ?_
  intro g hg
  exact center_U hg.1 (Subgroup.mem_centralizer_iff.1 hg.2)

theorem center_T_of {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁)
    {N : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    ∀ w ∈ outT (h.inn_le_K hn hK) (psiK h hσ₁),
      (∀ y ∈ outT (h.inn_le_K hn hK) (psiK h hσ₁), y * w = w * y) → w ≠ 1 →
      ∃ m ∈ N, m * iK A (h.inn_le_K hn hK) (xc 1) * m⁻¹ = w := by
  intro w hw hc hw1
  have hgenK := h.inn_le_K hn hK
  have hinjC : Function.Injective (MulAut.conj : C K →* MulAut (C K)) :=
    conj_injective_of_center center_C_eq_bot'
  obtain ⟨u, hu, σ, hσ, hwu⟩ := (mem_outT_iff hn hK h hσ₁ hgen w).1 hw
  have key : ∀ u' ∈ U K, u' * u = u * (fieldAut K σ) u' := by
    intro u' hu'
    have hS : iK A hgenK u' ∈ outT hgenK (psiK h hσ₁) :=
      Subgroup.mem_sup_left (Subgroup.mem_map_of_mem _ hu')
    have h2 := congrArg (fun y : ↥A.K => (y : MulAut (C K))) (hc _ hS)
    simp only [Subgroup.coe_mul, iK_coe, hwu] at h2
    have e1 : fieldAut K σ * MulAut.conj u' =
        MulAut.conj ((fieldAut K σ) u') * fieldAut K σ := by
      have := aut_conj_conj (fieldAut K σ) u'
      calc fieldAut K σ * MulAut.conj u'
          = (fieldAut K σ * MulAut.conj u' * (fieldAut K σ)⁻¹) * fieldAut K σ := by group
        _ = _ := by rw [this]
    have e : MulAut.conj (u' * u) * fieldAut K σ =
        MulAut.conj (u * (fieldAut K σ) u') * fieldAut K σ := by
      calc MulAut.conj (u' * u) * fieldAut K σ
          = MulAut.conj u' * (MulAut.conj u * fieldAut K σ) := by rw [map_mul, mul_assoc]
        _ = MulAut.conj u * fieldAut K σ * MulAut.conj u' := h2
        _ = MulAut.conj u * (fieldAut K σ * MulAut.conj u') := by rw [mul_assoc]
        _ = MulAut.conj u * (MulAut.conj ((fieldAut K σ) u') * fieldAut K σ) := by rw [e1]
        _ = MulAut.conj (u * (fieldAut K σ) u') * fieldAut K σ := by rw [map_mul, mul_assoc]
    exact hinjC (mul_right_cancel e)
  have hσ1 : σ = 1 := by
    refine RingEquiv.ext fun s => ?_
    obtain ⟨α, ρ, μ, ν, β, γ, hu'⟩ := exists_nf hu
    have h1 := key (xa s) (xa_mem_U s)
    rw [show fieldAut K σ (xa s) = xa (σ s) from fieldAut_xe σ rA s, xa_eq_nf, xa_eq_nf, hu',
      nf_mul, nf_mul] at h1
    have h2 := (nf_eq_iff.1 h1).1
    show σ s = s
    linear_combination (-1 : K) * h2
  subst hσ1
  have hwi : w = iK A hgenK u := Subtype.ext (by rw [hwu, map_one, mul_one]; rfl)
  have hcomm : ∀ h' ∈ U K, h' * u = u * h' := by
    intro h' hh'
    have := key h' hh'
    simpa using this
  have huX : u ∈ Xc K := center_U hu hcomm
  have hu1 : u ≠ 1 := fun h1 => hw1 (by rw [hwi, h1, map_one])
  obtain ⟨d, hd, hdu⟩ := torus_trans_Xc u huX hu1
  refine ⟨iK A hgenK d, (hN _).2 ⟨d, torusSub_le_Pmin _ hd, 1, Subgroup.one_mem _, ?_⟩, ?_⟩
  · rw [map_one, mul_one]
    rfl
  · rw [hwi, ← hdu, ← map_mul, ← map_inv, ← map_mul]

end Fields

end CFSG.Quasithin.H13.F431.G2.OutK
