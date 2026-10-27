module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityLines
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityPair

public section

namespace CFSG.RankThree.PartOne.KCUnitaryGt

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.PartOne.KCUnitaryLines
  CFSG.RankThree.PartOne.KCUnitaryFrame CFSG.RankThree.PartOne.KCUnitaryBlock
  CFSG.RankThree.PartOne.KCUnitaryPair

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem psi_eq_one_of_scalar (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (M : primeFormUnitary h (idGram K n)) (c : K)
    (hM : ∀ v : Fin n → K, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) :
    primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, RingEquiv.refl K⟩ = 1 := by
  have hMeq : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c • (1 : Matrix (Fin n) (Fin n) K) := by
    apply Matrix.toLin'.injective
    apply (Pi.basisFun K (Fin n)).ext
    intro j
    simp only [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact hM _
  let i0 : Fin n := ⟨0, by omega⟩
  have he : idForm h n (Pi.single i0 1) (Pi.single i0 1) = 1 := by
    rw [idForm, gramForm_single]
    simp [idGram]
  have hcn : h.bar c * c = 1 := by
    have h1 := (mem_sesqUnitaryGroup.mp (toLinU_mem M)) (Pi.single i0 1) (Pi.single i0 1)
    rw [KCUnitaryBlock.toLinU_apply_eq, hM, he] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, he, mul_one,
      RingHom.id_apply] at h1
    rw [mul_comm]
    exact h1
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hcn
    exact zero_ne_one hcn
  have hnorm : h.norm ((Units.mk0 c hc0 : Kˣ) : K) = 1 := by
    change c * h.bar c = 1
    rw [mul_comm]
    exact hcn
  have hker : primeFormConjHom h (idGram K n) M = 1 := by
    refine (primeFormConjHom_eq_one_iff_of_ne hn hne M).mpr
      ⟨Units.mk0 c hc0, (pow_succ_eq_one_iff_norm h _).mpr hnorm, ?_⟩
    apply Units.ext
    rw [hMeq]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [primeFormPsi_apply, hker, one_mul]
  exact map_one _

theorem tau_eq_one_of_big_line (F : NonsplitFacts h n p Ahat) (S : PlaneSetup h n p Ahat)
    {L : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥)
    (hbig : 3 ≤ Module.finrank K ↥(fixedSpace (planeRep h n Ahat) ⊤ ⊔
      lineSpace (planeRep h n Ahat) (idForm h n) L))
    (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hblock : ∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    τ = RingEquiv.refl K := by
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have hex : ∃ t : ↥Ahat, t ∈ L ∧ t ≠ 1 := by
    have h1 : Nontrivial ↥L :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hL]; exact S.prime.one_lt)
    obtain ⟨t, ht⟩ := exists_ne (1 : ↥L)
    exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
  obtain ⟨t, htL, ht1⟩ := hex
  have hx1 : t.1 ≠ 1 := fun h' => ht1 (Subtype.ext h')
  obtain ⟨hmem, hgood⟩ := isGoodBlock_X_sub_one F hL hVL htL ht1
  have H := (S.planeData t.2).primaryData
  have hW := primaryComponent_X_sub_one_eq F hL htL ht1
  have hsep := separatingLeft_primaryComponent_selfDual H hmem
    (dualPoly_X_sub_C_one h.bar)
  rw [← hW] at hbig
  obtain ⟨b, hbW, hbON⟩ := exists_orthonormal_triple (h := h) hsep hbig
  have heig : ∀ i, xlin h n t.1 (b i) = (1 : K) • b i := fun i =>
    mem_primaryComponent_X_sub_C.mp (hbW i)
  have hexc := finrank_X_sub_one_not_exceptional F hL hVL htL ht1
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hT : ∀ i j : Fin 3, i ≠ j → ∀ c : Kˣ, h.norm (c : K) = 1 →
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (torusMat h (b i) (b j) c).map τ =
        torusMat h (b i) (b j) c * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := fun i j hij =>
    torus_comm_of_good_eigenpair S t.2 (μ := 1) (by simp) (hbON.pair hij) (heig i) (heig j) hexc
      M τ (fun i' g hg => hblock t.1 t.2 hx1 i' g hg)
  exact tau_eq_one_of_torus h (M := ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (M : GL (Fin n) K).isUnit (hbON.pair h01) (hbON.pair h02)
    (hbON.linearIndependent_triple h01 h02 h12) (hT 0 1 h01) (hT 0 2 h02)

theorem exists_global_scalar (F : NonsplitFacts h n p Ahat) (S : PlaneSetup h n p Ahat)
    (M : primeFormUnitary h (idGram K n))
    (hMx : ∀ x ∈ Ahat, M * liftUnitary x = liftUnitary x * M)
    (hMb : ∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      M * g = g * M) :
    ∃ c : K, ∀ v : Fin n → K, ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  classical
  have hdec := F.decomp
  have hp := S.prime
  set ρ := planeRep h n Ahat with hρ
  obtain ⟨L₀, M₀, hL₀, hM₀, hne, hV₀, hVM₀⟩ := hdec.exists_two_active
  obtain ⟨c₀, hc₀⟩ := exists_scalar_on_sup F S hL₀ hV₀ M hMx hMb
  have hall : ∀ L : Subgroup ↥Ahat, Nat.card L = p → lineSpace ρ (idForm h n) L ≠ ⊥ →
      ∀ v ∈ fixedSpace ρ ⊤ ⊔ lineSpace ρ (idForm h n) L,
        ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c₀ • v := by
    intro L hL hVL v hv
    obtain ⟨c, hc⟩ := exists_scalar_on_sup F S hL hVL M hMx hMb
    suffices hcc : c = c₀ by rw [← hcc]; exact hc v hv
    by_cases hLL : L = L₀
    · subst hLL
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVL
      have h1 := hc w (Submodule.mem_sup_right hw)
      have h2 := hc₀ w (Submodule.mem_sup_right hw)
      exact smul_left_injective K hw0 (h1.symm.trans h2)
    · by_cases hV0 : fixedSpace ρ ⊤ = ⊥
      · obtain ⟨x, hx, hx1, a, -, ⟨u, huL, hua, hu0⟩, ⟨w, hwL, hwa, hw0⟩⟩ :=
          exists_mixing_factor S hdec (F.not_dvd hp) hL₀ hL (fun h' => hLL h'.symm) hV₀ hVL
        obtain ⟨c', hc'⟩ := exists_eScalar_of_commute_block S hx a M (hMx x hx) (hMb x hx hx1 a)
        have hYu : ((toLinU h n M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)) u = c₀ • u := by
          rw [KCUnitaryBlock.toLinU_apply_eq]
          exact hc₀ u (Submodule.mem_sup_right huL)
        have hYw : ((toLinU h n M : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)) w = c • w := by
          rw [KCUnitaryBlock.toLinU_apply_eq]
          exact hc w (Submodule.mem_sup_right hwL)
        exact (eq_of_eScalar hc' hua hwa hu0 hw0 hYu hYw).symm
      · obtain ⟨v₀, hv₀, hv₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
        have h1 := hc v₀ (Submodule.mem_sup_left hv₀)
        have h2 := hc₀ v₀ (Submodule.mem_sup_left hv₀)
        exact smul_left_injective K hv₀0 (h1.symm.trans h2)
  refine ⟨c₀, fun v => ?_⟩
  have hmem : v ∈ (⊤ : Submodule K (Fin n → K)) := Submodule.mem_top
  rw [← hdec.sup_eq_top] at hmem
  have hker : (⨆ i, decompFamily ρ (idForm h n) p i) ≤
      LinearMap.ker (Matrix.toLin' ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
        c₀ • LinearMap.id) := by
    refine iSup_le fun i => ?_
    rcases i with _ | ⟨L, hL⟩
    · intro u hu
      change u ∈ fixedSpace ρ ⊤ at hu
      have := hc₀ u (Submodule.mem_sup_left hu)
      simpa [sub_eq_zero] using this
    · intro u hu
      change u ∈ lineSpace ρ (idForm h n) L at hu
      by_cases hVL : lineSpace ρ (idForm h n) L = ⊥
      · rw [hVL, Submodule.mem_bot] at hu
        simp [hu]
      · have := hall L hL hVL u (Submodule.mem_sup_right hu)
        simpa [sub_eq_zero] using this
  have := hker hmem
  simpa [sub_eq_zero] using this

end CFSG.RankThree.PartOne.KCUnitaryGt
