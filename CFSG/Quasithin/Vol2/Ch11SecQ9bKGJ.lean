module

public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGI
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4E
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4F
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4I
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.Quasithin.Vol2.Ch11.SecS CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.KGNat (IsCoord charP_two_of_card four_le_card exists_isCoord
  linModelNat exists_sylow_eq_conj_Usp psiSp psiSp_apply psiSp_injective
  exists_eq_pre_of_isFlagW_sp eq_std_of_stable_sp map_stabilizer_eq perfectCore_map flag_one_eq
  spLine spHyp gmapSp spJ commutant_statedSp orth_of_semilinear_normalizing)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

namespace C11P9B

variable {K : Type} [Field K] {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem normalizing_coord (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) {τ : MulAut W}
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hTf : ∀ w, T (f w) = f (τ w)) :
    ∀ γ : StatedSp 2 K, ∃ γ' : StatedSp 2 K, ∀ x,
      T (mat 2 K γ *ᵥ x) = mat 2 K γ' *ᵥ T x := by
  intro γ
  obtain ⟨γ', hγ'⟩ : ∃ γ' : StatedSp 2 K,
      π γ' = ⟨τ * ((π γ : ↥H) : MulAut W) * τ⁻¹, hτH _ (π γ).2⟩ := hf.onto _
  have h1 : ((π γ' : ↥H) : MulAut W) = τ * ((π γ : ↥H) : MulAut W) * τ⁻¹ :=
    congrArg Subtype.val hγ'
  refine ⟨γ', fun x => ?_⟩
  obtain ⟨w, rfl⟩ := hf.surj x
  rw [← hf.act4, hTf, hTf, ← hf.act4, h1]
  simp [MulAut.mul_apply]

theorem torusHom_mulVec_e0 (t : Fin 2 → Kˣ) :
    mat 2 K (torusHom t) *ᵥ Pi.single (.inl 0) 1 = (t 0 : K) • Pi.single (.inl 0) 1 := by
  rw [show mat 2 K (torusHom t) = spMat (torusHom t) from rfl, spMat_torusHom]
  funext a
  rw [Matrix.mulVec_diagonal]
  rcases a with i | i <;> fin_cases i <;> simp

theorem frob_mem_pCoreOf_Q0 [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    (hK4 : ∃ s : Finset K, s.card = 4) (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (g : StatedSp 2 K) {τ : MulAut W} {T T' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)}
    (hTf : ∀ w, T (f w) = f (τ w)) (hT'f : ∀ w, T' (f w) = f (τ⁻¹ w)) {σ : K →+* K}
    (hT : ∀ (c : K) x, T (c • x) = σ c • T x) (hsq : ∀ c, σ c = c ^ 2)
    (horth' : ∀ x y, Matrix.toBilin' (spJ K) x y = 0 →
      Matrix.toBilin' (spJ K) (T' x) (T' y) = 0)
    (hU : τ ∈ stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))
    {t : Fin 2 → Kˣ} (ht : t 1 = 1) {Y₁ : StatedSp 2 K} (hY₁Q : Y₁ ∈ Q2 K 0)
    (hY₁ : psiSp π g Y₁ = τ * psiSp π g (torusHom t) * τ⁻¹) :
    Y₁ * torusHom t ∈ pCoreOf 2 (Q2 K 0) := by
  have hTT' : ∀ x, T (T' x) = x := fun x => by
    obtain ⟨w, rfl⟩ := hf.surj x
    rw [hT'f, hTf, MulAut.apply_inv_self]
  have he₀ : (Pi.single (.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ∈ spLine K :=
    ⟨by simp, by simp, by simp⟩
  obtain ⟨l1, l2, l3⟩ := conjT_mem_spLine hf g hT'f (Subgroup.inv_mem _ hU) he₀
  set c := conjT T' g (Pi.single (.inl 0) 1) (.inl 0) with hc
  have hlam : conjT T' g (Pi.single (.inl 0) 1) = c • Pi.single (.inl 0) 1 := by
    funext a
    rcases a with i | i <;> fin_cases i <;> simp [hc, l1, l2, l3]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 := conjT_conjT hTT' g (Pi.single (.inl 0) 1)
    rw [hlam, h0, zero_smul, map_zero] at h1
    have := congrFun h1 (.inl 0)
    simp at this
  have hback : conjT T g (c • Pi.single (.inl 0) 1) = Pi.single (.inl 0) 1 := by
    rw [← hlam, conjT_conjT hTT']
  have hY₁e : mat 2 K Y₁ *ᵥ Pi.single (.inl 0) 1 = (t 0 : K) ^ 2 • Pi.single (.inl 0) 1 := by
    rw [mat_conj_apply hf g hTf hT'f hY₁, hlam, Matrix.mulVec_smul, torusHom_mulVec_e0, smul_comm,
      conjT_smul hT, hback, hsq]
  have hχ1 : mat 2 K Y₁ (.inl 0) (.inl 0) = (t 0 : K) ^ 2 := by
    have := congrFun hY₁e (.inl 0)
    rw [mulVec_e0_apply] at this
    simpa using this
  have hfix : ∀ y ∈ spHyp K, mat 2 K Y₁ *ᵥ y - y ∈ spLine K := by
    intro y hy
    have hz : conjT T' g y ∈ spHyp K :=
      mem_spHyp_of_orth (fun x y h => conjT_orth horth' g h) hc0 hlam hy
    have hDz : mat 2 K (torusHom t) *ᵥ conjT T' g y - conjT T' g y ∈ spLine K := by
      rw [show mat 2 K (torusHom t) = spMat (torusHom t) from rfl, spMat_torusHom]
      refine ⟨?_, ?_, ?_⟩ <;>
        simp [Matrix.mulVec_diagonal, ht, CFSG.Quasithin.Vol2.KGNat.mem_spHyp.mp hz]
    have h1 := conjT_mem_spLine hf g hTf hU hDz
    rw [map_sub, conjT_conjT hTT'] at h1
    rw [mat_conj_apply hf g hTf hT'f hY₁]
    exact h1
  have hb1 := hfix (Pi.single (.inl 1) 1) (by simp [CFSG.Quasithin.Vol2.KGNat.mem_spHyp])
  have hb2 := hfix (Pi.single (.inr 1) 1) (by simp [CFSG.Quasithin.Vol2.KGNat.mem_spHyp])
  have hent : ∀ (a b : Fin 2 ⊕ Fin 2),
      (mat 2 K Y₁ *ᵥ (Pi.single b 1 : Fin 2 ⊕ Fin 2 → K) - (Pi.single b 1 : Fin 2 ⊕ Fin 2 → K)) a =
        mat 2 K Y₁ a b - (Pi.single b (1 : K) : Fin 2 ⊕ Fin 2 → K) a :=
    fun a b => by simp [Pi.single_apply]
  have e11 : mat 2 K Y₁ (.inl 1) (.inl 1) = 1 := by
    have h := hb1.1
    rw [hent] at h
    simp only [Pi.single_eq_same] at h
    linear_combination h
  have e21 : mat 2 K Y₁ (.inr 1) (.inl 1) = 0 := by
    have h := hb1.2.2
    rw [hent] at h
    simpa using h
  have e12 : mat 2 K Y₁ (.inl 1) (.inr 1) = 0 := by
    have h := hb2.1
    rw [hent] at h
    simpa using h
  have e22 : mat 2 K Y₁ (.inr 1) (.inr 1) = 1 := by
    have h := hb2.2.2
    rw [hent] at h
    simp only [Pi.single_eq_same] at h
    linear_combination h
  have hblk : blkIdx (sigma2 0) (mat 2 K Y₁) = 1 := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, e11, e21, e12, e22]
  have hY : Y₁ * torusHom t ∈ Q2 K 0 := (Q2 K 0).mul_mem hY₁Q (torusHom_mem_Q2 0 t)
  rw [mem_pCoreOf_Q0_iff hK4]
  refine ⟨hY, ?_, ?_⟩
  · rw [entry_mul_Q0 (torusHom_mem_Q2 0 t)]
    have h3 := congrArg Units.val (pow_three_units hK (t 0))
    have h4 : spMat (torusHom t) (.inl 0) (.inl 0) = (t 0 : K) := by
      rw [spMat_torusHom]
      simp
    rw [show spMat Y₁ (.inl 0) (.inl 0) = mat 2 K Y₁ (.inl 0) (.inl 0) from rfl, hχ1, h4]
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h3
    rw [← h3]
    ring
  · have e : (⟨Y₁ * torusHom t, hY⟩ : ↥(Q2 K 0)) = ⟨Y₁, hY₁Q⟩ * ⟨torusHom t, torusHom_mem_Q2 0 t⟩ :=
      rfl
    rw [e, map_mul, blkQ_torusHom_zero, ht, Units.val_one, inv_one, Units.val_one]
    have hb : blkQ 0 ⟨Y₁, hY₁Q⟩ = 1 := by
      rw [blkQ_apply]
      exact hblk
    rw [hb, Matrix.one_mul]
    ext i k
    fin_cases i <;> fin_cases k <;> simp

end C11P9B

open C11P9B in
theorem factFieldAutPointSp4_holds : FactFieldAutPointSp4 := by
  intro K _ _ hK W _ _ hW H Z π hπ _ P hP U₁ hU₁ D hD
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have : CharP K 2 := charP_two_of_card (by omega) hK'
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four
    (four_le_card le_rfl hK')
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK' (by omega) hf hP
  rw [eq_map_psiSp_of_sylow hg, inf_normalizer_eq_sp hf g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torus_sp hf g hD
  have hg' := sylow_conj_mul_sp hg (Usp_eq_unipotent (K := K) ▸ hx)
  rw [← hK] at hU₁
  obtain ⟨S₁, hS₁, hc₁, rfl⟩ := exists_eq_pre_of_isFlagW_sp hW hf hg' hU₁
  have e₁ : S₁ = spLine K := (eq_std_of_stable_sp hS₁).1 (by rw [hc₁, pow_one])
  subst e₁
  set ψ := psiSp π (g * x) with hψdef
  have hψ : Function.Injective ψ := psiSp_injective hf (g * x)
  have hQ : H ⊓ stabW (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup) = (Q2 K 0).map ψ := by
    rw [← map_stabilizer_eq hf (g * x) (spLine K), ← flag_one_eq]
    rfl
  have hΓ₁ : gammaW H (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup) =
      (perfectCore (Q2 K 0)).map ψ := by
    rw [gammaW, hQ, perfectCore_map _ hψ]
  have hC₁ : centW D (gammaW H (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup)) =
      ((tSb K).map torusHom).map ψ := by
    rw [centW, hDx, hΓ₁, pCoreOf_map_of_injective _ hψ, map_inf_sectionCentralizer _ hψ,
      torus_inf_sc0 hK4]
  intro τ hτH hτZ hτU _ hout d hd
  have hτ : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (hτZ z).mp hz
  have hτ' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz => ((Subgroup.inv_mem _ hτZ) z).mp hz
  have hτ'' : ∀ z ∈ Z, τ⁻¹⁻¹ z ∈ Z := by simpa using hτ
  have hτH' := conj_inv_mem_of_conj_mem hτH
  have hτH'' : ∀ h ∈ H, τ⁻¹⁻¹ * h * τ⁻¹ ∈ H := by simpa using hτH
  have hx₀ : (Pi.single (.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h => by
    simpa using congrFun h (.inl 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) hx₀ τ hτ hτ'
    hτH'
  obtain ⟨σ', hσ'⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) hx₀ τ⁻¹ hτ'
    hτ'' hτH''
  have horth := orth_of_semilinear_normalizing hσ
    (normalizing_coord hf hτH (hf.autMap_apply τ hτ))
  have horth' := orth_of_semilinear_normalizing hσ'
    (normalizing_coord hf hτH' (hf.autMap_apply τ⁻¹ hτ'))
  rcases ringHom_eq_id_or_sq hK σ with hid | hsq
  · exfalso
    have hT : ∀ (c : K) x, hf.autMap τ hτ (c • x) = c • hf.autMap τ hτ x := fun c x => by
      rw [hσ, hid]
    have hTT' : ∀ x, hf.autMap τ hτ (hf.autMap τ⁻¹ hτ' x) = x := fun x => by
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [hf.autMap_apply, hf.autMap_apply, MulAut.apply_inv_self]
    have hT'T : ∀ x, hf.autMap τ⁻¹ hτ' (hf.autMap τ hτ x) = x := fun x => by
      obtain ⟨w, rfl⟩ := hf.surj x
      rw [hf.autMap_apply, hf.autMap_apply, MulAut.inv_apply_self]
    have hT' : ∀ (c : K) x, hf.autMap τ⁻¹ hτ' (c • x) = c • hf.autMap τ⁻¹ hτ' x :=
      fun c x => by
        conv_lhs => rw [← hTT' x, ← hT, hT'T]
    have hτN : ∀ X ∈ perfectCore (Q2 K 0), ∃ X' ∈ perfectCore (Q2 K 0),
        ψ X' = τ * ψ X * τ⁻¹ := by
      intro X hX
      have h1 := conj_mem_gammaW hτH hτU (hΓ₁ ▸ ⟨X, hX, rfl⟩ : ψ X ∈ gammaW H _)
      rw [hΓ₁] at h1
      obtain ⟨X', hX', h2⟩ := h1
      exact ⟨X', hX', h2⟩
    obtain ⟨γ, hγ, hall⟩ := inner_of_linear_sp hK4 hf (g * x) (hf.autMap_apply τ hτ)
      (hf.autMap_apply τ⁻¹ hτ') hT hT' horth horth' hτU hτN
    rw [hΓ₁] at hout
    obtain ⟨y, hy, hnot⟩ := hout γ hγ
    rw [pCoreOf_map_of_injective _ hψ] at hnot
    exact hnot (hall y hy)
  · rw [hC₁] at hd
    obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hd
    have ht1 : t 1 = 1 := mem_tSb.mp ht
    have hdQ : ψ (torusHom t) ∈ H ⊓ stabW (hf.pre (gmapSp (g * x) (spLine K)).toAddSubgroup) := by
      rw [hQ]
      exact ⟨_, torusHom_mem_Q2 0 t, rfl⟩
    have h1 := conj_mem_inf_stabW hτH hτU hdQ
    rw [hQ] at h1
    obtain ⟨Y₁, hY₁Q, hY₁⟩ := h1
    have hY := frob_mem_pCoreOf_Q0 hK hK4 hf (g * x) (hf.autMap_apply τ hτ)
      (hf.autMap_apply τ⁻¹ hτ') hσ hsq horth' hτU ht1 hY₁Q hY₁
    rw [hQ, pCoreOf_map_of_injective _ hψ]
    exact ⟨Y₁ * torusHom t, hY, by rw [map_mul, hY₁]⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
