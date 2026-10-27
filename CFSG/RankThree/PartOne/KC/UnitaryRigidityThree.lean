module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityMixTau
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityPair
public import CFSG.RankThree.PartOne.KC.UnitaryRigidityLines

public section

namespace CFSG.RankThree.PartOne.KCUnitaryThree

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.PartOne.KCUnitaryLines
  CFSG.RankThree.PartOne.KCUnitaryFrame CFSG.RankThree.PartOne.KCUnitaryBlock
  CFSG.RankThree.PartOne.KCUnitaryPair CFSG.RankThree.PartOne.KCUnitaryMixTau
  CFSG.RankThree.PartOne.KCGeneric CFSG.RankThree.PartOne.KCUnitaryCoord

section Bar

variable {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def barEquiv : K ≃+* K :=
  RingEquiv.ofBijective h.bar ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩

theorem barEquiv_apply (c : K) : barEquiv h c = h.bar c := rfl

theorem eq_barEquiv_of_inv_on_norm_one {τ : K ≃+* K}
    (hτ : ∀ c : Kˣ, h.norm (c : K) = 1 → τ (c : K) = (c : K)⁻¹) : τ = barEquiv h := by
  have h1 : τ.trans (barEquiv h) = RingEquiv.refl K := by
    refine eq_one_of_fixes_norm_one h _ fun v hv => ?_
    have hbar : h.bar (v : K) = (v : K)⁻¹ := by
      have : (v : K) * h.bar (v : K) = 1 := hv
      exact eq_inv_of_mul_eq_one_right this
    show h.bar (τ (v : K)) = v
    rw [hτ v hv, map_inv₀, hbar, inv_inv]
  refine RingEquiv.ext fun c => ?_
  have h2 := congrArg (fun σ : K ≃+* K => σ c) h1
  simp only [RingEquiv.trans_apply, RingEquiv.refl_apply, barEquiv_apply] at h2
  rw [barEquiv_apply]
  calc τ c = h.bar (h.bar (τ c)) := (h.bar_bar _).symm
    _ = h.bar c := by rw [h2]

end Bar

section Dichotomy

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem eq_neg_one_of_eq_inv {v : K} (hv0 : v ≠ 0) (hv1 : v ≠ 1) (hvv : v = v⁻¹) :
    v = -1 := by
  have h2 : (v - 1) * (v + 1) = 0 := by
    have h3 : v * v = 1 := by
      calc v * v = v * v⁻¹ := by rw [← hvv]
        _ = 1 := mul_inv_cancel₀ hv0
    linear_combination h3
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hv1
  · exact eq_neg_of_add_eq_zero_left h3

theorem tau_dichotomy_of_torus_pair (hq : 2 ≤ ℓ ^ f) {M : Matrix (Fin n) (Fin n) K}
    (hM : IsUnit M) {τ : K ≃+* K} {b₀ b₁ : Fin n → K} (hb : IsONPair h b₀ b₁)
    (hT : ∀ c : Kˣ, h.norm (c : K) = 1 →
      M * (torusMat h b₀ b₁ c).map τ = torusMat h b₀ b₁ c * M) :
    τ = RingEquiv.refl K ∨ ∀ c : Kˣ, h.norm (c : K) = 1 → τ (c : K) = (c : K)⁻¹ := by
  set γ := semilinRep M (τ : K →+* K) with hγ
  have hγinj : Function.Injective γ := semilinRep_injective hM _
  have hind := hb.linearIndependent
  have key : ∀ c : Kˣ, h.norm (c : K) = 1 → (c : K) ≠ (c : K)⁻¹ →
      ((∃ d : K, d ≠ 0 ∧ γ b₀ = d • b₀) ∧ τ (c : K) = c) ∨
        ((∃ d : K, d ≠ 0 ∧ γ b₀ = d • b₁) ∧ τ (c : K) = (c : K)⁻¹) := by
    intro c hc hne
    have hc1 : (c : K) ≠ 1 := by
      intro h1
      apply hne
      rw [h1, inv_one]
    have hτc : (τ : K →+* K) (c : K) ≠ 1 := by
      intro h1
      apply hc1
      apply τ.injective
      rw [map_one]
      exact h1
    exact semilinear_eigenvector_of_torus_pair γ hγinj hind (Matrix.toLin' (torusMat h b₀ b₁ c))
      (fun v => by rw [Matrix.toLin'_apply]; exact torus_range_mem_span h b₀ b₁ _ v)
      (by rw [Matrix.toLin'_apply]; exact torus_apply_first h hb _)
      (by rw [Matrix.toLin'_apply]; exact torus_apply_second h hb _) hne hτc
      (fun v => by
        simp only [Matrix.toLin'_apply]
        exact semilinRep_mulVec_comm _ (hT c hc) v)
  obtain ⟨ζ, hζ1, hζ2⟩ := exists_norm_one_sq_ne_one h hq
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hζn : h.norm ((Units.mk0 ζ hζ0 : Kˣ) : K) = 1 := by
    change ζ * h.bar ζ = 1
    rw [mul_comm]
    exact hζ1
  have hζne : ((Units.mk0 ζ hζ0 : Kˣ) : K) ≠ ((Units.mk0 ζ hζ0 : Kˣ) : K)⁻¹ := by
    intro h1
    apply hζ2
    have : ζ * ζ = 1 := by
      calc ζ * ζ = ζ * ζ⁻¹ := by
            conv_lhs => rw [show ζ = ζ⁻¹ from h1]
            rw [← show ζ = ζ⁻¹ from h1]
        _ = 1 := mul_inv_cancel₀ hζ0
    rw [sq]
    exact this
  rcases key _ hζn hζne with ⟨⟨d, hd, hγd⟩, -⟩ | ⟨⟨d, hd, hγd⟩, -⟩
  · left
    refine eq_one_of_fixes_norm_one h τ fun v hv => ?_
    by_cases hv1 : (v : K) = 1
    · rw [hv1, map_one]
    by_cases hvv : (v : K) = (v : K)⁻¹
    · rw [eq_neg_one_of_eq_inv v.ne_zero hv1 hvv, map_neg, map_one]
    · rcases key v hv hvv with ⟨-, h'⟩ | ⟨⟨d', hd', hγd'⟩, -⟩
      · exact h'
      · exfalso
        have h5 : d • b₀ = d' • b₁ := hγd.symm.trans hγd'
        have := (LinearIndependent.pair_iff.mp hind) d (-d') (by
          rw [neg_smul, h5, add_neg_cancel])
        exact hd this.1
  · right
    intro v hv
    by_cases hv1 : (v : K) = 1
    · rw [hv1, map_one, inv_one]
    by_cases hvv : (v : K) = (v : K)⁻¹
    · rw [eq_neg_one_of_eq_inv v.ne_zero hv1 hvv, map_neg, map_one, inv_neg, inv_one]
    · rcases key v hv hvv with ⟨⟨d', hd', hγd'⟩, -⟩ | ⟨-, h'⟩
      · exfalso
        have h5 : d' • b₀ = d • b₁ := hγd'.symm.trans hγd
        have := (LinearIndependent.pair_iff.mp hind) d' (-d) (by
          rw [neg_smul, h5, add_neg_cancel])
        exact hd' this.1
      · exact h'

end Dichotomy

section Assembly

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

theorem exists_ne_one_mem_line (S : PlaneSetup h n p Ahat) {L : Subgroup ↥Ahat}
    (hL : Nat.card L = p) : ∃ t : ↥Ahat, t ∈ L ∧ t ≠ 1 := by
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have h1 : Nontrivial ↥L :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hL]; exact S.prime.one_lt)
  obtain ⟨t, ht⟩ := exists_ne (1 : ↥L)
  exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩

theorem tau_eq_one_of_two_dim_lines (F : NonsplitFacts h n p Ahat) (S : PlaneSetup h n p Ahat)
    (hsmall : ∀ L : Subgroup ↥Ahat, Nat.card L = p →
      lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥ →
      Module.finrank K ↥(fixedSpace (planeRep h n Ahat) ⊤ ⊔
        lineSpace (planeRep h n Ahat) (idForm h n) L) ≤ 2)
    (M : primeFormUnitary h (idGram K n)) (τ : K ≃+* K)
    (hcent : ∀ x ∈ Ahat,
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) (liftUnitary x) =
      primeFormConjHom h (idGram K n) (liftUnitary x) *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩)
    (hblock : ∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩ *
        primeFormConjHom h (idGram K n) g =
      primeFormConjHom h (idGram K n) g *
        primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := n)) ⟨M, τ⟩) :
    τ = RingEquiv.refl K := by
  classical
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have hdec := F.decomp
  have hp := S.prime
  set ρ := planeRep h n Ahat with hρ
  obtain ⟨L₀, L₁, hL₀, hL₁, hLne, hV₀, hV₁⟩ := hdec.exists_two_active
  obtain ⟨t, htL, ht1⟩ := exists_ne_one_mem_line S hL₀
  have hx1 : t.1 ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have hfin2 : Module.finrank K ↥(lineSpace ρ (idForm h n) L₀) = 2 := by
    have h1 : 2 ≤ Module.finrank K ↥(lineSpace ρ (idForm h n) L₀) :=
      F.two_le_finrank hL₀ hV₀
    have h2 : Module.finrank K ↥(fixedSpace ρ ⊤ ⊔ lineSpace ρ (idForm h n) L₀) ≤ 2 :=
      hsmall L₀ hL₀ hV₀
    have h3 : Module.finrank K ↥(lineSpace ρ (idForm h n) L₀) ≤
        Module.finrank K ↥(fixedSpace ρ ⊤ ⊔ lineSpace ρ (idForm h n) L₀) :=
      Submodule.finrank_mono le_sup_right
    omega
  have he2 : ordNegQ ℓ f p = 2 := by
    have hd : ordNegQ ℓ f p ∣ Module.finrank K ↥(lineSpace ρ (idForm h n) L₀) :=
      hdec.dvd_finrank L₀ hL₀
    rw [hfin2] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    have := F.e_gt
    omega
  obtain ⟨hpq1, hq3⟩ := F.e_two he2
  obtain ⟨hmem, hgood⟩ := isGoodBlock_X_sub_one F hL₀ hV₀ htL ht1
  have H := (S.planeData t.2).primaryData
  have hW := primaryComponent_X_sub_one_eq F hL₀ htL ht1
  have hsep := separatingLeft_primaryComponent_selfDual H hmem (dualPoly_X_sub_C_one h.bar)
  have hdim : 2 ≤ Module.finrank K ↥(primaryComponent (xlin h n t.1) (X - C 1)) := by
    have h3 : Module.finrank K ↥(lineSpace ρ (idForm h n) L₀) ≤
        Module.finrank K ↥(primaryComponent (xlin h n t.1) (X - C 1)) := by
      rw [hW]
      exact Submodule.finrank_mono le_sup_right
    omega
  obtain ⟨b, hbW, hbON⟩ := exists_orthonormal_family (m := 2) (h := h) hsep hdim
  have heig : ∀ i, xlin h n t.1 (b i) = (1 : K) • b i := fun i =>
    mem_primaryComponent_X_sub_C.mp (hbW i)
  have hexc := finrank_X_sub_one_not_exceptional F hL₀ hV₀ htL ht1
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hT := torus_comm_of_good_eigenpair S t.2 (μ := 1) (by simp) (hbON.pair h01) (heig 0)
    (heig 1) hexc M τ (fun i' g hg => hblock t.1 t.2 hx1 i' g hg)
  rcases tau_dichotomy_of_torus_pair h (by omega) (M := ((M : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) (M : GL (Fin n) K).isUnit (hbON.pair h01) hT with hτ | hτ
  · exact hτ
  have hτbar : τ = barEquiv h := eq_barEquiv_of_inv_on_norm_one h hτ
  obtain ⟨x, hx, hx1', a, ha1, ⟨u, huL, hua, hu0⟩, ⟨w, hwL, hwa, hw0⟩⟩ :=
    exists_mixing_factor S hdec (F.not_dvd hp) hL₀ hL₁ hLne hV₀ hV₁
  have hdvd : (a.1 : K[X]) ∣ X ^ p - 1 := primaryFactor_dvd_pow_sub_one S ⟨x, hx⟩ a.1.2
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_dvd_sub h hp hpq1
  obtain ⟨μ, haμ, hμp⟩ := exists_eq_X_sub_C hp hζ (monic_of_mem_primaryFactors a.1.2)
    (irreducible_of_mem_primaryFactors a.1.2) hdvd
  have hμ1 : μ ≠ 1 := fun h1 => ha1 (by rw [haμ, h1])
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hμp
    exact zero_ne_one hμp
  have hμq : μ ^ (ℓ ^ f) = μ := by
    obtain ⟨k, hk⟩ := hpq1
    have hpos : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have hq1 : ℓ ^ f = p * k + 1 := by omega
    rw [hq1, pow_succ, pow_mul, hμp, one_pow, one_mul]
  have hbarμ : h.bar μ = μ := by rw [h.bar_apply]; exact hμq
  have hτμ : τ μ = μ := by rw [hτbar, barEquiv_apply, hbarμ]
  have hbar0 : h.bar μ ≠ 0 := (map_ne_zero h.bar).mpr hμ0
  have hμinv : μ ≠ μ⁻¹ := by
    intro h1
    have hsq : μ ^ 2 = 1 := by
      calc μ ^ 2 = μ * μ := sq μ
        _ = μ * μ⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel₀ hμ0
    have : Fact p.Prime := ⟨hp⟩
    have hord : orderOf μ = p := orderOf_eq_prime hμp hμ1
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hord ▸ orderOf_dvd_of_pow_eq_one hsq)
    apply F.not_dvd hp
    rw [hp2] at hpq1 ⊢
    omega
  have hne' : (a.1 : K[X]) ≠ dualPoly h.bar (a.1 : K[X]) := by
    rw [haμ, KCUnitaryBlock.dualPoly_X_sub_C hbar0, hbarμ]
    intro h1
    apply hμinv
    have := congrArg (fun q : K[X] => q.coeff 0) h1
    simpa using this
  have hMx := matrix_comm_of_plane S hx M τ (hcent x hx)
  have hstab : ∀ v ∈ primaryComponent (xlin h n x) (a.1 : K[X]),
      semilinRep ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (τ : K →+* K) v ∈
        primaryComponent (xlin h n x) (a.1 : K[X]) := by
    intro v hv
    rw [haμ] at hv ⊢
    have hv' : xlin h n x v = μ • v := mem_primaryComponent_X_sub_C.mp hv
    refine mem_primaryComponent_X_sub_C.mpr ?_
    have h2 := semilinRep_mulVec_comm (τ : K →+* K) hMx v
    change _ = ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ _ at h2
    show ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ _ = _
    rw [← h2]
    change semilinRep _ _ (xlin h n x v) = _
    rw [hv', map_smulₛₗ]
    exact congrArg (· • _) hτμ
  have : Fact (Irreducible (a.1 : K[X])) := ⟨irreducible_of_mem_primaryFactors a.1.2⟩
  have hind := linearIndependent_pair_of_disjoint (T := xlin h n x) (a := (a.1 : K[X]))
    (S₁ := lineSpace ρ (idForm h n) L₀) (S₂ := lineSpace ρ (idForm h n) L₁)
    (fun s hs => lineSpace_stable S ⟨x, hx⟩ hs) (fun s hs => lineSpace_stable S ⟨x, hx⟩ hs)
    (disjoint_lineSpace hdec hL₀ hL₁ hLne) huL hwL hua hwa hu0 hw0
  exact tau_eq_one_of_transvection S hx a hne' hua hwa hu0 hind M τ hstab
    (hblock x hx hx1' a)

end Assembly

end CFSG.RankThree.PartOne.KCUnitaryThree
