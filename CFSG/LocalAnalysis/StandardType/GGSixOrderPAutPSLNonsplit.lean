module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestMain

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace OrdPNS

section Units

variable {K : Type} [Field K] [Finite K] {n ℓ : ℕ}

theorem exists_gl_set (hℓ : 0 < ℓ) (S : Set (Matrix (Fin n) (Fin n) K))
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) :
    ∃ T : Set (GL (Fin n) K), (∀ g ∈ T, (g : Matrix (Fin n) (Fin n) K) ∈ S) ∧
      Nat.card S ≤ Nat.card T := by
  have hu : ∀ x : S, IsUnit (x : Matrix (Fin n) (Fin n) K) := fun x =>
    IsUnit.of_pow_eq_one (hSp x.1 x.2) hℓ.ne'
  refine ⟨Set.range fun x : S => (hu x).unit, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [IsUnit.unit_spec]
    exact x.2
  · refine Nat.card_le_card_of_injective (fun x => ⟨(hu x).unit, x, rfl⟩) fun x y hxy => ?_
    have h1 := congrArg (fun g : Set.range fun x : S => (hu x).unit =>
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hxy
    simp only [IsUnit.unit_spec] at h1
    exact Subtype.ext h1

end Units

section Conj

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs G₀ : Subgroup G} {m f : ℕ} {F : Type}
  [Field F] [Finite F] [CharP F 2] {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}

omit [CharP F 2] in
theorem eq_one_of_mem_center {u : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F - 1) (hz : u ∈ Subgroup.center _) (hu : u ^ p = 1) : u = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h1 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin (m + 1)) F =>
    (Matrix.SpecialLinearGroup.toGL x : GL (Fin (m + 1)) F)) hu
  have hr1 : r = 1 := by
    refine eq_one_of_pow_eq_one hp hpF ?_
    have h2 := congrArg (fun x : GL (Fin (m + 1)) F => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      0 0) h1
    simp only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one, one_apply_eq] at h2
    have h3 : ((Matrix.SpecialLinearGroup.toGL u : GL (Fin (m + 1)) F) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) F) = scalar (Fin (m + 1)) r := hr.symm
    rw [h3, ← map_pow, scalar_apply, diagonal_apply_eq] at h2
    exact h2
  ext i j
  rw [← hr, hr1, map_one]
  rfl

theorem exists_conj_of_elemAbelian
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (hpF : ¬ p ∣ Nat.card F - 1) {F' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)}
    (hF' : IsElemAbelian p F') (hcard : p ^ ((m + 1) / ordQ F p) ≤ Nat.card F') {y : G}
    (hy : ∀ u ∈ F', y * ψ u = ψ u * y) :
    ∃ m' ∈ Subgroup.normalizer (G₀ : Set G), m'⁻¹ * y * m' ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hp := hS.prime
  have hinj : Function.Injective (ψ.comp F'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (eq_one_of_mem_center hp hpF (hker hu) (hF'.2 u u.2))
  have hEcard : Nat.card (F'.map ψ) = Nat.card F' := by
    have hr : (ψ.comp F'.subtype).range = F'.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hEel : IsElemAbelian p (F'.map ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, z, hz, rfl⟩ := b
      apply Subtype.ext
      change ψ x * ψ z = ψ z * ψ x
      rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hF' hx hz]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hF'.2 x hx, map_one]
  have hEM : F'.map ψ ≤ Subgroup.normalizer (G₀ : Set G) := by
    rintro _ ⟨x, -, rfl⟩
    exact Subgroup.le_normalizer (hrange ▸ ⟨x, rfl⟩)
  refine exists_conj_mem_centralizer_of_card hS hEM hEel
    ((card_bstar_le hS hpF).trans (hcard.trans hEcard.symm.le)) ?_
  rintro _ ⟨u, hu, rfl⟩
  exact hy u hu

omit [Finite G] [Finite F] [CharP F 2] in
theorem conj_psi (u v : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    (ψ u)⁻¹ * ψ v * ψ u = ψ (InnerDiagA.conjSL (Matrix.SpecialLinearGroup.toGL u⁻¹) v) := by
  have h : InnerDiagA.conjSL (Matrix.SpecialLinearGroup.toGL u⁻¹) v = u⁻¹ * v * u := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [RootPlaneA.toGL_conjSL, map_mul, map_mul, map_inv, inv_inv]
  rw [h, map_mul, map_mul, map_inv]

theorem exists_conj_mem_centralizer_inner
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (hpF : ¬ p ∣ Nat.card F - 1) {y : G} (hyp : y ^ p = 1)
    (hy : GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ y) :
    ∃ m' ∈ Subgroup.normalizer (G₀ : Set G), m'⁻¹ * y * m' ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hp := hS.prime
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hpK : (p : F) ≠ 0 := natCast_ne_zero_of_charTwo hp hS.ne_two
  obtain ⟨A, hA⟩ := RootPlaneA.exists_gl_of_psiInnerDiag hm hker hy
  obtain ⟨A', hA'p, hA'⟩ :=
    OrdPRest.exists_pow_eq_one hker hA hyp fun c _ => exists_pow_eq hp hpF c
  obtain ⟨S, hSc, hSp, hSA, hScard⟩ := exists_card_ge_pow_ordQ_matrix (K := F) (n := m + 1) hp
    hpK (A' : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (by rw [← Units.val_pow_eq_pow_val, hA'p, Units.val_one])
  obtain ⟨T, hTS, hTcard⟩ := exists_gl_set hp.pos S hSp
  obtain ⟨F', hF'el, hF'card, -, hF'A, -⟩ := exists_elemAbelian_of_set hp hpF T
    (fun x hx z hz => Units.ext (hSc _ (hTS x hx) _ (hTS z hz)).eq)
    (fun x hx => Units.ext (by rw [Units.val_pow_eq_pow_val, hSp _ (hTS x hx), Units.val_one]))
  refine exists_conj_of_elemAbelian hS hpF hF'el (hScard.trans (hTcard.trans hF'card)) ?_
  intro u hu
  have hcomm := hF'A A' (fun x hx => Units.ext (hSA _ (hTS x hx)).eq) u⁻¹ (F'.inv_mem hu)
  exact OrdPRest.commute_of_conj hCψ hA' (conj_psi u) hcomm.eq.symm

theorem exists_conj_mem_centralizer_field
    (hS : GGSixFusionSetting p Bs G₀ (SpecialLinear.rootDatum m F) .PSL (m + 1) f ψ)
    (hpF : ¬ p ∣ Nat.card F - 1) {y : G} (hyM : y ∈ Subgroup.normalizer (G₀ : Set G))
    (hyp : y ^ p = 1) (hyI : ¬ GGPsiInnerDiag (SpecialLinear.rootDatum m F) ψ y) :
    ∃ m' ∈ Subgroup.normalizer (G₀ : Set G), m'⁻¹ * y * m' ∈ Subgroup.centralizer (Bs : Set G) := by
  obtain ⟨⟨-, hrank⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hm : 2 ≤ m := hrank
  have hn : 3 ≤ m + 1 := by omega
  have hp := hS.prime
  have hp2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hpK : (p : F) ≠ 0 := natCast_ne_zero_of_charTwo hp hp2
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  set N := Subgroup.normalizer (ψ.range : Set G) with hN
  set φN := ψ.range.normalizerMonoidHom
  have hφN : Function.Injective φN := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hCψ,
      Subgroup.bot_subgroupOf]
  set Θ := AutPSL.projEquiv (m := m) (K := F) hker hCψ
  set χ : N →* MulAut (projectiveSL (m + 1) F) := (MulAut.congr Θ).symm.toMonoidHom.comp φN
  have hχ : Function.Injective χ := (MulAut.congr Θ).symm.injective.comp hφN
  have hχα : ∀ (b : N) (u u' : Matrix.SpecialLinearGroup (Fin (m + 1)) F),
      ψ u' = (b : G) * ψ u * (b : G)⁻¹ → χ b (proj (m + 1) F u) = proj (m + 1) F u' := by
    intro b u u' hu
    change Θ.symm (φN b (Θ (proj (m + 1) F u))) = proj (m + 1) F u'
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    change (b : G) * ψ u * (b : G)⁻¹ = ψ u'
    rw [hu]
  have hχA : ∀ (b : N) (A : GL (Fin (m + 1)) F),
      (∀ u, (b : G) * ψ u * (b : G)⁻¹ = ψ (InnerDiagA.conjSL A u)) →
        χ b = conjAut (m + 1) F A := by
    intro b A hA
    ext x
    obtain ⟨u, rfl⟩ := proj_surjective (m + 1) F x
    rw [hχα b u _ (hA u).symm, conjAut_proj, RootPlaneA.slConjugation_eq_conjSL]
  have hψN : ∀ s : Matrix.SpecialLinearGroup (Fin (m + 1)) F, ψ s ∈ N := fun s =>
    Subgroup.le_normalizer ⟨s, rfl⟩
  have hχψ : ∀ s : Matrix.SpecialLinearGroup (Fin (m + 1)) F,
      χ ⟨ψ s, hψN s⟩ = conjAut (m + 1) F (Matrix.SpecialLinearGroup.toGL s) := by
    intro s
    refine hχA ⟨ψ s, hψN s⟩ _ fun u => ?_
    change ψ s * ψ u * (ψ s)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hyN : y ∈ N := by
    rw [hN, hrange]
    exact hyM
  set y' : N := ⟨y, hyN⟩ with hy'
  have hχp : χ y' ^ p = 1 := by
    rw [← map_pow]
    have : y' ^ p = 1 := Subtype.ext hyp
    rw [this, map_one]
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) hn).2 (χ y')
  have hε0 : ε = 0 := HypSixTypeA.graph_exp_eq_zero hn (hp.odd_of_ne_two hp2) hε
    (by rw [← hαeq]; exact hχp)
  subst hε0
  rw [pow_zero, mul_one] at hαeq
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hαeq
    apply hyI
    refine OrdPRest.ggPsiInnerDiag_of_conjAut hm hyN (A := A⁻¹) fun u u' hu => ?_
    have h1 := hχα y' u' u (by
      change ψ u = y * ψ u' * y⁻¹
      rw [hu]
      group)
    rw [hαeq] at h1
    rw [map_inv]
    change (conjAut (m + 1) F A).symm (proj (m + 1) F u) = proj (m + 1) F u'
    rw [MulEquiv.symm_apply_eq]
    exact h1.symm
  have h1 := ProjectivePlane.conjAut_mul_fieldAut_pow σ A p
  rw [← hαeq, hχp] at h1
  obtain ⟨hσp, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1.symm
  have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨H, d, hH⟩ := OrdPRest.exists_hilbert90 (by omega) hσo A hc.symm
  have hyH := OrdPRest.conjAut_mul_fieldAut_eq_conj' A H σ d hH
  rw [← hαeq] at hyH
  obtain ⟨S, hSc, hSp, hSσ, hScard⟩ :=
    exists_card_ge_pow_ordQ_fixed (K := F) (n := m + 1) hp hpK hσo
  obtain ⟨T, hTS, hTcard⟩ := exists_gl_set hp.pos S hSp
  obtain ⟨F₀, hF₀el, hF₀card, -, -, hF₀σ⟩ := exists_elemAbelian_of_set hp hpF T
    (fun x hx z hz => Units.ext (hSc _ (hTS x hx) _ (hTS z hz)).eq)
    (fun x hx => Units.ext (by rw [Units.val_pow_eq_pow_val, hSp _ (hTS x hx), Units.val_one]))
  have hσfix := hF₀σ (σ : F →+* F) fun x hx => Units.ext (by
    change ((x : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map σ = x
    exact hSσ _ (hTS x hx))
  set F' := F₀.map (InnerDiagA.conjSL H) with hF'
  have hcinj : Function.Injective (InnerDiagA.conjSL H) := by
    intro u v huv
    apply Matrix.SpecialLinearGroup.toGL_injective
    have h2 := congrArg Matrix.SpecialLinearGroup.toGL huv
    rw [RootPlaneA.toGL_conjSL, RootPlaneA.toGL_conjSL] at h2
    exact mul_left_cancel (mul_right_cancel h2)
  have hF'el : IsElemAbelian p F' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, x, hx, rfl⟩ := a
      obtain ⟨_, z, hz, rfl⟩ := b
      apply Subtype.ext
      change InnerDiagA.conjSL H x * InnerDiagA.conjSL H z =
        InnerDiagA.conjSL H z * InnerDiagA.conjSL H x
      rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hF₀el hx hz]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hF₀el.2 x hx, map_one]
  have hF'card : Nat.card F₀ = Nat.card F' :=
    (Subgroup.card_map_of_injective hcinj).symm
  refine exists_conj_of_elemAbelian hS hpF hF'el
    (hScard.trans (hTcard.trans (hF₀card.trans hF'card.le))) ?_
  rintro _ ⟨u, hu, rfl⟩
  have hfu : fieldAut (m + 1) F σ * conjAut (m + 1) F (Matrix.SpecialLinearGroup.toGL u) =
      conjAut (m + 1) F (Matrix.SpecialLinearGroup.toGL u) * fieldAut (m + 1) F σ := by
    rw [fieldAut_mul_conjAut]
    congr 2
    have h3 : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (σ : F →+* F) u) =
        GeneralLinearGroup.map (σ : F →+* F) (Matrix.SpecialLinearGroup.toGL u) := by
      ext i j
      rfl
    rw [← h3, hσfix u hu]
  have key : χ y' * χ ⟨ψ (InnerDiagA.conjSL H u), hψN _⟩ =
      χ ⟨ψ (InnerDiagA.conjSL H u), hψN _⟩ * χ y' := by
    rw [hχψ, RootPlaneA.toGL_conjSL, map_mul, map_mul, map_inv, hyH]
    calc conjAut (m + 1) F H * fieldAut (m + 1) F σ * (conjAut (m + 1) F H)⁻¹ *
          (conjAut (m + 1) F H * conjAut (m + 1) F (Matrix.SpecialLinearGroup.toGL u) *
            (conjAut (m + 1) F H)⁻¹) =
        conjAut (m + 1) F H * (fieldAut (m + 1) F σ *
          conjAut (m + 1) F (Matrix.SpecialLinearGroup.toGL u)) * (conjAut (m + 1) F H)⁻¹ := by
          group
      _ = conjAut (m + 1) F H * (conjAut (m + 1) F (Matrix.SpecialLinearGroup.toGL u) *
          fieldAut (m + 1) F σ) * (conjAut (m + 1) F H)⁻¹ := by rw [hfu]
      _ = _ := by group
  have hzb : y' * ⟨ψ (InnerDiagA.conjSL H u), hψN _⟩ = ⟨ψ (InnerDiagA.conjSL H u), hψN _⟩ * y' :=
    hχ (by rw [map_mul, map_mul, key])
  exact congrArg Subtype.val hzb

end Conj

end OrdPNS

section Family

theorem ggOrdPInnerConjPSLNonsplit_holds : GGOrdPInnerConjPSLNonsplit := by
  intro G _ _ p Bs G₀ n f ψ hS _ hpq y _ hyo hy
  obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  exact OrdPNS.exists_conj_mem_centralizer_inner (F := GaloisField 2 f) hS hpF hyp hy

theorem ggOrdPFieldConjPSLNonsplit_holds : GGOrdPFieldConjPSLNonsplit := by
  intro G _ _ p Bs G₀ n f ψ hS _ hpq y hyM hyo _ hyI
  obtain ⟨⟨hadm, -⟩, -, -, -⟩ := hS.presents
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hyp : y ^ p = 1 := hyo ▸ pow_orderOf_eq_one y
  exact OrdPNS.exists_conj_mem_centralizer_field (F := GaloisField 2 f) hS hpF hyM hyp hyI

theorem ggOrdPInnerConjAt_PSL : GGOrdPInnerConjAt .PSL :=
  ggOrdPInnerConjAt_PSL_of_nonsplit ggOrdPInnerConjPSLNonsplit_holds

theorem ggOrdPFieldConjAt_PSL : GGOrdPFieldConjAt .PSL :=
  ggOrdPFieldConjAt_PSL_of_nonsplit ggOrdPFieldConjPSLNonsplit_holds

theorem ggSixLSixElevenKGInput_of_rest_PSL_holds
    (h1 : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPInnerConjAt t)
    (h2 : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPFieldConjAt t)
    (h3 : ∀ t, (t = .PSU ∨ t = .E6 ∨ t = .twistedE6) → GGOrdPOutdiagAt t)
    (h4 : ∀ t, ¬ GGOrdPSmallTag t → t ≠ .PSL → GGOrdPGraphAt t) (h5 : GGOrdPTrialityInput) :
    GGSixLSixElevenKGInput :=
  ggSixLSixElevenKGInput_of_rest_PSL ggOrdPInnerConjPSLNonsplit_holds
    ggOrdPFieldConjPSLNonsplit_holds h1 h2 h3 h4 h5

end Family

end CFSG.StandardType
