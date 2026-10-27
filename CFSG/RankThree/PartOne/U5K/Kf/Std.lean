module

public import CFSG.RankThree.PartOne.U5K.Kf.HypMain
public import CFSG.RankThree.PartOne.U5K.Kf.StdLemmas
public import CFSG.RankThree.PartOne.U5K.Hyp.Transport
public import CFSG.RankThree.PartOne.S12.Sec1514Five
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG CFSG.RankThree.PartOne CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.RankThree.PartOne.KCEvenUnitaryFiveBridge

section Transport

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

omit [Finite G] [Finite G'] in
theorem map_map_symm_equiv (θ : G ≃* G') (S : Subgroup G) :
    (S.map θ.toMonoidHom).map θ.symm.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have : θ.symm.toMonoidHom.comp θ.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id]

omit [Finite G] in
theorem transport_back (θ : G ≃* G') {H Ab B : Subgroup G} {Th : Subgroup G'}
    (hT : IsSylowOf 2 Th (H.map θ.toMonoidHom))
    (hA : Ab.map θ.toMonoidHom ≤ Subgroup.centralizer (omegaOneCenterIn Th : Set G'))
    (hB : B.map θ.toMonoidHom ≤ Subgroup.normalizer (pushingUpS Th : Set G')) :
    ∃ T : Subgroup G, IsSylowOf 2 T H ∧
      Ab ≤ Subgroup.centralizer (omegaOneCenterIn T : Set G) ∧
      B ≤ Subgroup.normalizer (pushingUpS T : Set G) := by
  refine ⟨Th.map θ.symm.toMonoidHom, ?_, ?_, ?_⟩
  · have := Sec9B.isSylowOf_map (f := θ.symm.toMonoidHom) θ.symm.injective hT
    rwa [map_map_symm_equiv] at this
  · intro ρ hρ
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hinj : Function.Injective (θ.symm.toMonoidHom.comp Th.subtype) :=
      θ.symm.injective.comp Th.subtype_injective
    rw [← Sec1514Five.map_omegaOneCenterIn θ.symm.toMonoidHom hinj] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have h1 := Subgroup.mem_centralizer_iff.1 (hA (Subgroup.mem_map_of_mem _ hρ)) z' hz'
    apply θ.injective
    simp only [map_mul, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1 ⊢
    exact h1
  · intro ρ hρ
    have hinj : Function.Injective (θ.symm.toMonoidHom.comp Th.subtype) :=
      θ.symm.injective.comp Th.subtype_injective
    rw [← map_pushingUpS θ.symm.toMonoidHom hinj]
    have h1 := hB (Subgroup.mem_map_of_mem _ hρ)
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro g
    have h2 := h1 (θ g)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    simpa [map_mul, map_inv] using h2

end Transport

section Main

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem exists_gam_of_unitary {R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K}
    (hR : IsHypTransport h R) (X : primeFormUnitary h (idGram K 5)) :
    ∃ x : Gam h, Phi h x = MulAut.congr (hypToPrimeForm h hR).symm
        (primeFormConjHom h (idGram K 5) X) ∧ x.1.right = 1 ∧
      lmat x = transportInv h R * ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * R := by
  refine ⟨linearToSemilinear h (toSimilitude h hR X), ?_, rfl, rfl⟩
  rw [mulAut_congr_conj_eq h hR X]
  rfl

theorem eigen_of_diag {P X : primeFormUnitary h (idGram K 5)} {μ : Fin 5 → K}
    (hd : (((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal μ)
    (w : Fin 5 → K) (s : K) (hw : Matrix.diagonal μ *ᵥ w = s • w) :
    ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ
        (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w) =
      s • (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ w) := by
  have e : (P : GL (Fin 5) K) * ((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
      (X : GL (Fin 5) K) * (P : GL (Fin 5) K) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have e' := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K)) e
  simp only [Units.val_mul] at e'
  rw [hd] at e'
  rw [Matrix.mulVec_mulVec, ← e', ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]

theorem bar_mul_eq_one_of_diag {P X : primeFormUnitary h (idGram K 5)} {μ : Fin 5 → K}
    (hd : (((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal μ) (s : Fin 5) :
    h.bar (μ s) * μ s = 1 := by
  have hm := mem_primeFormUnitary.1 (P⁻¹ * X * P).2
  rw [hd] at hm
  have := congrFun (congrFun hm s) s
  simpa [idGram, Matrix.diagonal_map, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal] using this

theorem col_eq_mul_wvec (P : Matrix (Fin 5) (Fin 5) K) (ι : HypIndex 2 1 ≃ Fin 5) (u c : K)
    (x : HypIndex 2 1) : (P * wmat ι u c) *ᵥ Pi.single x 1 = P *ᵥ wvec ι u c x := by
  rw [← Matrix.mulVec_mulVec, wmat_mulVec_single]

theorem exists_T_std (hq : 3 ≤ 2 ^ f) (hZ : Subgroup.center (primeFormP h (idGram K 5)) = ⊥)
    (P : primeFormUnitary h (idGram K 5)) (ι : HypIndex 2 1 ≃ Fin 5)
    {H Ab B : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hH : (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range ≤ H)
    (hAb : ∀ ρ₀ ∈ Ab, ∃ (X : primeFormUnitary h (idGram K 5)) (μ : Fin 5 → K),
      primeFormConjHom h (idGram K 5) X = ρ₀ ∧
      (((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal μ ∧ μ (ι (.inl 0)) = μ (ι (.inr (.inr 0))))
    (hB : ∀ ρ₀ ∈ B, ∃ (X : primeFormUnitary h (idGram K 5)) (μ : Fin 5 → K),
      primeFormConjHom h (idGram K 5) X = ρ₀ ∧
      (((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal μ ∧
        μ (ι (.inl 0)) = μ (ι (.inr (.inr 0))) ∧ μ (ι (.inl 1)) = μ (ι (.inr (.inr 1)))) :
    ∃ T : Subgroup (MulAut (primeFormP h (idGram K 5))), IsSylowOf 2 T H ∧
      Ab ≤ Subgroup.centralizer (omegaOneCenterIn T : Set (MulAut (primeFormP h (idGram K 5)))) ∧
      B ≤ Subgroup.normalizer (pushingUpS T : Set (MulAut (primeFormP h (idGram K 5)))) := by
  classical
  have hfin := h.finite
  obtain ⟨u, hu⟩ := exists_bar_mul_eq_neg_one h
  obtain ⟨c, hc⟩ := exists_add_bar_eq_neg_one h
  have hR0 : IsHypTransport (r := 2) (ε := 1) h (wmat ι u c) := isHypTransport_wmat h ι hu hc
  have hR : IsHypTransport (r := 2) (ε := 1) h
      (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * wmat ι u c) :=
    isHypTransport_mul_unitary h hR0 P
  set R : Matrix (Fin (2 * 2 + 1)) (HypIndex 2 1) K :=
    ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * wmat ι u c with hRdef
  set ιR : hypPSU h 2 1 ≃* primeFormP h (idGram K 5) := hypToPrimeForm h hR with hιR
  set θ : MulAut (primeFormP h (idGram K 5)) ≃* MulAut (hypPSU h 2 1) :=
    MulAut.congr ιR.symm with hθ
  have hZh : Subgroup.center (hypPSU h 2 1) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hz' : ιR z ∈ Subgroup.center (primeFormP h (idGram K 5)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      obtain ⟨y', rfl⟩ := ιR.surjective y
      rw [← map_mul, ← map_mul, hz y']
    rw [hZ, Subgroup.mem_bot] at hz'
    simpa using congrArg ιR.symm hz'
  have hfinh : Finite (MulAut (hypPSU h 2 1)) := finite_mulAut_hyp h
  have hfinP : Finite (MulAut (primeFormP h (idGram K 5))) := Finite.of_equiv _ θ.symm.toEquiv
  have hPi : Pi h ≤ H.map θ.toMonoidHom := by
    rintro _ ⟨z, rfl⟩
    refine ⟨MulAut.conj (ιR z), hH ⟨ιR z, rfl⟩, ?_⟩
    have := mulAut_congr_conj ιR.symm (ιR z)
    exact this.trans (by rw [MulEquiv.symm_apply_apply])
  have hAb' : ∀ ρ ∈ Ab.map θ.toMonoidHom, ∃ x : Gam h, Phi h x = ρ ∧ x.1.right = 1 ∧ ∃ α : K,
      (∀ r : HypIndex 2 1, lmat x r (Sum.inl 0) = if r = Sum.inl 0 then α else 0) ∧
      h.bar α * α = 1 ∧ ((lmat x).map h.bar)ᵀ * hypGram 2 1 K * lmat x = hypGram 2 1 K := by
    rintro _ ⟨ρ₀, hρ₀, rfl⟩
    obtain ⟨X, μ, hXρ, hd, hμ⟩ := hAb ρ₀ hρ₀
    obtain ⟨x, hx1, hx2, hx3⟩ := exists_gam_of_unitary h hR X
    refine ⟨x, ?_, hx2, μ (ι (.inl 0)), ?_, bar_mul_eq_one_of_diag h hd _, ?_⟩
    · rw [hx1, hXρ]
      rfl
    · intro r
      have hXs := eigen_of_diag h hd (wvec ι u c (.inl 0)) (μ (ι (.inl 0)))
        (diag_mulVec_wvec_inl ι u c μ 0 hμ)
      rw [← col_eq_mul_wvec _ ι u c] at hXs
      have hc := congrFun (col_transport h hR hXs) r
      rw [hx3]
      have h2 : ((transportInv h R * ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * R) *ᵥ
          Pi.single (Sum.inl 0) 1) r =
          (transportInv h R * ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * R) r
            (Sum.inl 0) := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [h2] at hc
      rw [hc]
      by_cases hr : r = Sum.inl 0
      · subst hr; simp
      · simp [hr]
    · have := transportGLInv_gram h hR X
      rw [coe_transportGLInv] at this
      rw [hx3]
      exact this
  have hB' : ∀ ρ ∈ B.map θ.toMonoidHom, ∃ x : Gam h, Phi h x = ρ ∧ x.1.right = 1 ∧
      ∃ (A : Matrix (Fin 2) (Fin 2) K) (d : K), IsUnit A.det ∧ h.bar d * d = 1 ∧
        lmat x = oddDiag h A d := by
    rintro _ ⟨ρ₀, hρ₀, rfl⟩
    obtain ⟨X, μ, hXρ, hd, hμ0, hμ1⟩ := hB ρ₀ hρ₀
    obtain ⟨x, hx1, hx2, hx3⟩ := exists_gam_of_unitary h hR X
    let s : HypIndex 2 1 → K := fun y => match y with
      | .inl a => μ (ι (.inl a))
      | .inr (.inl k) => μ (ι (.inr (.inl k)))
      | .inr (.inr a) => μ (ι (.inl a))
    have hs : ∀ y, ((X : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ (R *ᵥ Pi.single y 1) =
        s y • (R *ᵥ Pi.single y 1) := by
      intro y
      rw [hRdef, col_eq_mul_wvec]
      rcases y with a | k | a
      · fin_cases a
        · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inl ι u c μ 0 hμ0)
        · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inl ι u c μ 1 hμ1)
      · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inr_inl ι u c μ k)
      · fin_cases a
        · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inr_inr ι u c μ 0 hμ0)
        · exact eigen_of_diag h hd _ _ (diag_mulVec_wvec_inr_inr ι u c μ 1 hμ1)
    have hn : ∀ y, h.bar (s y) * s y = 1 := by
      intro y
      rcases y with a | k | a <;> exact bar_mul_eq_one_of_diag h hd _
    have hdiag := transport_eq_diagonal h hR s hs
    have hoD := diagonal_eq_oddDiag h s (fun a => rfl) hn
    refine ⟨x, ?_, hx2, Matrix.diagonal fun a : Fin 2 => s (.inl a), s (.inr (.inl 0)), ?_,
      hn (.inr (.inl 0)), ?_⟩
    · rw [hx1, hXρ]
      rfl
    · rw [Matrix.det_diagonal]
      refine isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
      exact right_ne_zero_of_mul_eq_one (hn (.inl a))
    · rw [hx3, hdiag, hoD]
  obtain ⟨Th, hTh, hA, hBn⟩ := exists_T_hyp hZh hq hPi hAb' hB'
  exact transport_back θ hTh hA hBn

end Main

end CFSG.RankThree.PartOne.U5K.Kf
