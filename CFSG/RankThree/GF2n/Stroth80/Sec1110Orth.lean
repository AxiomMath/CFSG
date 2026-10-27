module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110L4
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatField
public import CFSG.RankThree.GF2n.Stroth80.Sec5SL
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm
public import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Adapters.RankTwoModelTransports CFSG.ClassicalInvolution.Upgrade
open scoped commutatorElement Matrix

section OrthogonalHelpers

variable {K : Type} [Field K]

theorem statedOmega_mem_orthogonalGroup {m : ℕ} {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus m K)) :
    toLinEquiv (Fin m ⊕ Fin m) K A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := by
  have hA' : toLinEquiv (Fin m ⊕ Fin m) K A ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)⁆ :=
    Subgroup.mem_comap.mp ((statedOmega_eq_comap (coe_quadPlus m K)).le hA)
  exact Subgroup.commutator_le_self _ hA'

theorem statedOmega_quadPlus_mulVec {m : ℕ} {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus m K)) (v : Fin m ⊕ Fin m → K) :
    quadPlus m K ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v) = quadPlus m K v := by
  have h := map_of_mem (statedOmega_mem_orthogonalGroup hA) v
  rwa [toLinEquiv_apply] at h

theorem statedOmega_polar_mulVec {m : ℕ} {A : GL (Fin m ⊕ Fin m) K}
    (hA : A ∈ StatedOmega (StatedQuadPlus m K)) (v w : Fin m ⊕ Fin m → K) :
    polar (quadPlus m K) ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v)
        ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w) =
      polar (quadPlus m K) v w := by
  have h := polar_map_of_mem (statedOmega_mem_orthogonalGroup hA) v w
  rwa [toLinEquiv_apply, toLinEquiv_apply] at h

theorem exists_eq_smul_polarBilin_quadPlus_of_invariant
    (B' : LinearMap.BilinForm K (Fin 3 ⊕ Fin 3 → K))
    (hB'inv : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K), ∀ u w,
      B' ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ u)
          ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ w) = B' u w)
    (hB'nd : ∀ u, (∀ w, B' u w = 0) → u = 0) :
    ∃ c : K, c ≠ 0 ∧ ∀ u w, B' u w = c * polar (quadPlus 3 K) u w := by
  classical
  let Bstd : LinearMap.BilinForm K (Fin 3 ⊕ Fin 3 → K) := polarBilin (quadPlus 3 K)
  have hBstd : Bstd.Nondegenerate := by
    change (polarBilin (quadPlus 3 K)).Nondegenerate
    exact nondegenerate_polarBilin_quadPlus 3 K
  let At : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
    (Bstd.toDual hBstd).symm.toLinearMap ∘ₗ B'
  have hRiesz : ∀ u w, Bstd (At u) w = B' u w := by
    intro u w
    exact LinearMap.BilinForm.apply_toDual_symm_apply (B := Bstd) (hB := hBstd) (B' u) w
  have hAinv : ∀ A : GL (Fin 3 ⊕ Fin 3) K, ∀ y : Fin 3 ⊕ Fin 3 → K,
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
          (((A⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ y) = y := by
    intro A y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hAt_comm : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K), ∀ u,
      At ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ u) =
        (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ At u := by
    intro A hA u
    refine sub_eq_zero.mp (hBstd.1 (At ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ u) -
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ At u) fun w => ?_)
    have h1 : Bstd (At ((A : Matrix _ _ K) *ᵥ u)) w = B' ((A : Matrix _ _ K) *ᵥ u) w :=
      hRiesz _ _
    have h2 : Bstd ((A : Matrix _ _ K) *ᵥ At u) w =
        Bstd (At u) (((A⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) *ᵥ w) := by
      have h := statedOmega_polar_mulVec hA (At u)
        (((A⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) *ᵥ w)
      simpa [Bstd, hAinv A w] using h
    have h3 : Bstd (At u) (((A⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) *ᵥ w) =
        B' u (((A⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) *ᵥ w) := hRiesz _ _
    have h4 : B' u (((A⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) *ᵥ w) =
        B' ((A : Matrix _ _ K) *ᵥ u) w := by
      have h := hB'inv A hA u (((A⁻¹ : GL (Fin 3 ⊕ Fin 3) K) : Matrix _ _ K) *ᵥ w)
      rw [hAinv A w] at h
      exact h.symm
    rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]
  obtain ⟨c, hc⟩ := addCommutantScalar_statedOmegaPlus (m := 3) (K := K) (by norm_num)
    At.toAddMonoidHom hAt_comm
  have hc' : ∀ u, At u = c • u := fun u => hc u
  have hBrel : ∀ u w, B' u w = c * Bstd u w := by
    intro u w
    calc B' u w = Bstd (At u) w := (hRiesz u w).symm
      _ = Bstd (c • u) w := by rw [hc' u]
      _ = c * Bstd u w := by
        rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hc0 : c ≠ 0 := by
    intro hc0
    have hzero : ∀ u w, B' u w = 0 := fun u w => by rw [hBrel u w, hc0, zero_mul]
    have hne : (Pi.single (Sum.inl (0 : Fin 3)) (1 : K) : Fin 3 ⊕ Fin 3 → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl (0 : Fin 3))
      simpa using this
    exact hne (hB'nd _ fun w => hzero _ w)
  exact ⟨c, hc0, fun u w => by rw [hBrel u w]; rfl⟩

theorem eq_smul_of_polarBilin_eq_smul_of_statedOmega_invariant [Finite K] [CharP K 2]
    {Q₂ : QuadraticForm K (Fin 3 ⊕ Fin 3 → K)} {c : K}
    (hpolar : polarBilin Q₂ = c • polarBilin (quadPlus 3 K))
    (hinv : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K), ∀ v,
      Q₂ ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) = Q₂ v) :
    Q₂ = c • quadPlus 3 K := by
  classical
  let sqrt : K ≃+* K := (frobeniusEquiv K 2).symm
  have hsqrt_sq : ∀ x : K, (sqrt x) ^ 2 = x := by
    intro x
    have h := (frobeniusEquiv K 2).apply_symm_apply x
    rwa [frobeniusEquiv_def] at h
  have hsqrt_sq_apply : ∀ x : K, sqrt (x ^ 2) = x := by
    intro x
    rw [← frobeniusEquiv_def (R := K) (p := 2) x, RingEquiv.symm_apply_apply]
  let D : (Fin 3 ⊕ Fin 3 → K) → K := fun v => Q₂ v - c * quadPlus 3 K v
  have hDadd : ∀ u w, D (u + w) = D u + D w := by
    intro u w
    have h1 : Q₂ (u + w) = Q₂ u + Q₂ w + polar Q₂ u w := QuadraticMap.map_add Q₂ u w
    have h2 : quadPlus 3 K (u + w) =
        quadPlus 3 K u + quadPlus 3 K w + polar (quadPlus 3 K) u w :=
      QuadraticMap.map_add (quadPlus 3 K) u w
    have hp : polar Q₂ u w = c * polar (quadPlus 3 K) u w := by
      have := congrArg (fun B => B u w) hpolar
      simpa [LinearMap.smul_apply, smul_eq_mul] using this
    simp only [D, h1, h2, hp]
    ring
  have hDsmul : ∀ a v, D (a • v) = a ^ 2 * D v := by
    intro a v
    have h1 : Q₂ (a • v) = a ^ 2 * Q₂ v := by
      rw [QuadraticMap.map_smul, smul_eq_mul]
      ring
    have h2 : quadPlus 3 K (a • v) = a ^ 2 * quadPlus 3 K v := by
      rw [QuadraticMap.map_smul, smul_eq_mul]
      ring
    simp only [D, h1, h2]
    ring
  have hDinv : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K), ∀ v,
      D ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) = D v := by
    intro A hA v
    have h1 := hinv A hA v
    have h2 := statedOmega_quadPlus_mulVec hA v
    simp only [D, h1, h2]
  let L : (Fin 3 ⊕ Fin 3 → K) →ₗ[K] K :=
    { toFun := fun v => sqrt (D v)
      map_add' := fun u w => by rw [hDadd, map_add]
      map_smul' := fun a v => by
        rw [hDsmul, map_mul, hsqrt_sq_apply, smul_eq_mul, RingHom.id_apply] }
  have hL_inv : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K), ∀ v,
      L ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) = L v := by
    intro A hA v
    change sqrt (D ((A : Matrix _ _ K) *ᵥ v)) = sqrt (D v)
    rw [hDinv A hA v]
  have hLzero : L = 0 := by
    by_contra hLne
    have hfin : Module.finrank K (Fin 3 ⊕ Fin 3 → K) = 6 := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    have hker_ne : LinearMap.ker L ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (V := (Fin 3 ⊕ Fin 3 → K)) (V₂ := K) (by
        rw [hfin, Module.finrank_self]; norm_num)
    have hP : ∃ P : Fin 2 → HypPair (quadPlus 3 K), ∀ i j, i ≠ j → (P i).Orth (P j) := by
      refine ⟨![plusPair K (0 : Fin 3), plusPair K 1], ?_⟩
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact plusPair_orth (by decide)
      · exact plusPair_orth (by decide)
      · exact absurd rfl hij
    have hker_inv : ∀ g ∈ elementaryGroup (quadPlus 3 K), ∀ x ∈ LinearMap.ker L,
        g x ∈ LinearMap.ker L := by
      intro g hg x hx
      rw [LinearMap.mem_ker] at hx ⊢
      have hA : (toLinEquiv (Fin 3 ⊕ Fin 3) K).symm g ∈ StatedOmega (StatedQuadPlus 3 K) := by
        rw [statedOmega_quadPlus_eq_map (K := K) (n := 3) (by norm_num)]
        exact Subgroup.mem_map_of_mem _ hg
      have hval : ((toLinEquiv (Fin 3 ⊕ Fin 3) K).symm g : GL (Fin 3 ⊕ Fin 3) K) *ᵥ x = g x := by
        rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
      rw [← hval, hL_inv _ hA, hx]
    rcases submodule_eq_bot_or_top_of_elementaryGroup_invariant
      (nondegenerate_polarBilin_quadPlus 3 K) hP (LinearMap.ker L) hker_inv with hbot | htop
    · exact hker_ne hbot
    · apply hLne
      refine LinearMap.ext fun x => ?_
      have hx : L x = 0 := by
        have hmem : x ∈ LinearMap.ker L := by
          rw [htop]
          exact Submodule.mem_top
        simpa using hmem
      simpa using hx
  have hDzero : ∀ v, D v = 0 := by
    intro v
    have h : L v = 0 := by rw [hLzero]; rfl
    change sqrt (D v) = 0 at h
    rw [← map_zero sqrt] at h
    exact sqrt.injective h
  ext v
  have h := hDzero v
  simp only [D, QuadraticMap.smul_apply, smul_eq_mul] at h
  exact sub_eq_zero.mp h

end OrthogonalHelpers

section Main

variable {G : Type} [Group G] [Finite G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem orthogonalModuleRep_of_chain (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀) {X₁ X₂ : Subgroup G} (hX₂ : X₂ = Q) (hX₁ : X₁ = Z)
    (nat : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) X₂ X₁ (XbarPreCenter M Q Z B)) :
    OrthogonalModuleRep (Q := Q) (Z := Z) (K := K) M₀
      (R := XbarPre M Q Z B) (N := XbarPreCenter M Q Z B) := by
  classical
  have nat' : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) Q Z (XbarPreCenter M Q Z B) := by
    simpa [hX₂, hX₁] using nat
  obtain ⟨n₀, k₀, hnZ, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := by
    haveI : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := n₀) (by
      rw [← Nat.card_eq_fintype_card, hD.card, hnZ])
  obtain ⟨φ₀, hφrange, hφker, hact⟩ := nat'
  obtain ⟨hnorm, hZnorm, ψ, hψ⟩ := hact
  haveI := hZnorm
  have hcentral : ∀ g : ↥(XbarPre M Q Z B), ∀ z ∈ Z,
      (g : G) * z * (g : G)⁻¹ = z := by
    intro g z hz
    have := Subgroup.mem_centralizer_iff.mp (XbarPre_le_H0 hc g.2).2 z hz
    rw [← this]
    group
  have hexT : ∀ g : ↥(XbarPre M Q Z B), ∃ T : M₀.E ≃ₗ[K] M₀.E,
      (∀ x ∈ Q, M₀.π ((g : G) * x * (g : G)⁻¹) = T (M₀.π x)) ∧
      (∀ e, M₀.Qf (T e) = M₀.Qf e) ∧
      ∀ e f, M₀.B (T e) (T f) = M₀.B e f :=
    fun g => hD.linear_of_centralizes (XbarPre_le_H0 hc g.2).1 (hcentral g)
  let Tof (g : ↥(XbarPre M Q Z B)) : M₀.E ≃ₗ[K] M₀.E := Classical.choose (hexT g)
  have hTofπ : ∀ (g : ↥(XbarPre M Q Z B)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = Tof g (M₀.π x) :=
    fun g x hx => (Classical.choose_spec (hexT g)).1 x hx
  have hTofQ : ∀ (g : ↥(XbarPre M Q Z B)) (e : M₀.E),
      M₀.Qf (Tof g e) = M₀.Qf e :=
    fun g e => (Classical.choose_spec (hexT g)).2.1 e
  have hTofB : ∀ (g : ↥(XbarPre M Q Z B)) (e f : M₀.E),
      M₀.B (Tof g e) (Tof g f) = M₀.B e f :=
    fun g e f => (Classical.choose_spec (hexT g)).2.2 e f
  have himgQ : M₀.img Q = ⊤ := by
    ext e
    exact ⟨fun _ => AddSubgroup.mem_top e, fun _ => by
      obtain ⟨x, hxQ, hx⟩ := M₀.π_surj e
      exact ⟨x, hxQ, hxQ, hx⟩⟩
  have hcardι : Nat.card M₀.E = Nat.card (Fin 3 ⊕ Fin 3 → K) := by
    have h1 : Nat.card Q = Nat.card (↥Q ⧸ Z.subgroupOf Q) * Nat.card Z := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf Q),
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD.reg.V_le).toEquiv]
    have h2 : Nat.card Q = Nat.card Z * Nat.card M₀.E := by
      rw [M₀.card_eq (S := Q) (le_refl Q) hD.reg.V_le, himgQ,
        Nat.card_congr (AddSubgroup.topEquiv (G := M₀.E)).toEquiv]
    have h3 : Nat.card (↥Q ⧸ Z.subgroupOf Q) = Nat.card (Fin 3 ⊕ Fin 3 → K) :=
      Nat.card_congr ψ.toEquiv
    have hZpos : 0 < Nat.card Z := by rw [hnZ]; positivity
    have heq : Nat.card Z * Nat.card (Fin 3 ⊕ Fin 3 → K) = Nat.card Z * Nat.card M₀.E := by
      rw [← h2, h1, h3, mul_comm]
    exact (Nat.mul_left_cancel hZpos heq).symm
  obtain ⟨ιmap, hιmap_apply, hιmap_inj⟩ :=
    exists_Vt_transport (M₀ := M₀) (V := Q) (le_refl Q) ψ
  haveI : Finite M₀.E := Module.finite_of_finite K
  haveI : Fintype M₀.E := Fintype.ofFinite _
  haveI : Fintype (Fin 3 ⊕ Fin 3 → K) := Fintype.ofFinite _
  have hcardF : Fintype.card (Fin 3 ⊕ Fin 3 → K) = Fintype.card M₀.E := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardι.symm
  let eqv : (Fin 3 ⊕ Fin 3 → K) ≃ M₀.E := Fintype.equivOfCardEq hcardF
  have hιmap_inj' : Function.Injective ιmap := by
    intro a b hab
    have h : ιmap (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hιmap_inj (a - b) h)
  have hsurj : Function.Surjective ιmap :=
    (Finite.injective_iff_surjective_of_equiv eqv).mp hιmap_inj'
  let Ψa : M₀.E ≃+ (Fin 3 ⊕ Fin 3 → K) :=
    (AddEquiv.ofBijective ιmap ⟨hιmap_inj', hsurj⟩).symm
  have hΨa_apply : ∀ u, Ψa (ιmap u) = u := fun u => AddEquiv.symm_apply_apply _ u
  have hΨπ : ∀ v : ↥Q, Ψa (M₀.π v) = secVec ψ v := by
    intro v
    have h := congrArg Ψa (hιmap_apply v)
    rw [hΨa_apply] at h
    exact h.symm
  have hS : ∀ (c : K) (e : M₀.E), e ∈ M₀.img Q → c • e ∈ M₀.img Q := by
    intro c e he
    obtain ⟨x, hxQ, -, hx⟩ := M₀.mem_img.mp he
    obtain ⟨y, hyQ, hy⟩ := M₀.π_surj (c • M₀.π x)
    rw [← hx, ← hy]
    exact M₀.pi_mem_img hyQ hyQ
  have hlin : ∀ r ∈ XbarPre M Q Z B, ∃ T : M₀.E →ₗ[K] M₀.E,
      ∀ x ∈ Q, M₀.π (r * x * r⁻¹) = T (M₀.π x) :=
    fun r hr => ⟨Tof ⟨r, hr⟩, hTofπ ⟨r, hr⟩⟩
  haveI : Nonempty (Fin 3 ⊕ Fin 3) := ⟨Sum.inl 0⟩
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_natural (K' := K) (V := Q) rfl M₀ (le_refl Q)
    (addCommutantScalar_statedOmegaPlus (m := 3) (K := K) (by norm_num)) hS hlin φ₀ hφrange
    hnorm ψ hψ
  have hΨsmul : ∀ (c : K) (e : M₀.E), Ψa (c • e) = θ c • Ψa e := by
    intro c e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    obtain ⟨y, hyQ, hy⟩ := M₀.π_surj (c • M₀.π x)
    rw [← hy, hΨπ ⟨y, hyQ⟩, hΨπ ⟨x, hxQ⟩]
    exact hθ c ⟨x, hxQ⟩ ⟨y, hyQ⟩ hy
  let f : M₀.E →ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
    { toFun := fun e i => θ.symm (Ψa e i)
      map_add' := fun a b => by
        ext i
        simp [map_add]
      map_smul' := fun c e => by
        ext i
        rw [hΨsmul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [RingEquiv.map_mul, RingEquiv.symm_apply_apply, RingHom.id_apply] }
  have hf_left : Function.LeftInverse
      (fun u : Fin 3 ⊕ Fin 3 → K => Ψa.symm (fun i => θ (u i))) f := by
    intro e
    apply Ψa.injective
    rw [AddEquiv.apply_symm_apply]
    ext i
    simp [f]
  have hf_right : Function.RightInverse
      (fun u : Fin 3 ⊕ Fin 3 → K => Ψa.symm (fun i => θ (u i))) f := by
    intro u
    ext i
    simp [f]
  let e₀ : M₀.E ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
    LinearEquiv.ofBijective f ⟨hf_left.injective, hf_right.surjective⟩
  have he₀ : ∀ e, e₀ e = fun i => θ.symm (Ψa e i) := fun e => rfl
  let φ' : ↥(XbarPre M Q Z B) →* GL (Fin 3 ⊕ Fin 3) K :=
    (glCongr θ.symm).toMonoidHom.comp φ₀
  have hφ'range : φ'.range = StatedOmega (StatedQuadPlus 3 K) := by
    dsimp only [φ']
    rw [MonoidHom.range_comp, hφrange,
      map_statedOmega θ.symm (statedQuadPlus_comp (K := K) (n := 3) θ.symm)]
  have hφ'ker : φ'.ker = (XbarPreCenter M Q Z B).subgroupOf (XbarPre M Q Z B) := by
    simpa [φ', hφker] using MonoidHom.ker_mulEquiv_comp φ₀ (glCongr θ.symm)
  have hact₀ : ∀ (g : ↥(XbarPre M Q Z B)) (x : G), x ∈ Q →
      e₀ (M₀.π ((g : G) * x * (g : G)⁻¹)) =
        ((φ' g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
          e₀ (M₀.π x) := by
    intro g x hx
    have hx' : (g : G) * x * (g : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hnorm g.2) x).mp hx
    have hψg := hψ g ⟨x, hx⟩ ⟨(g : G) * x * (g : G)⁻¹, hx'⟩ rfl
    have h1 : e₀ (M₀.π ((g : G) * x * (g : G)⁻¹)) =
        θ.symm ∘ secVec ψ ⟨(g : G) * x * (g : G)⁻¹, hx'⟩ := by
      rw [he₀, hΨπ ⟨_, hx'⟩]
      rfl
    have h2 : e₀ (M₀.π x) = θ.symm ∘ secVec ψ ⟨x, hx⟩ := by
      rw [he₀, hΨπ ⟨x, hx⟩]
      rfl
    rw [h1, h2]
    have hψg' : secVec ψ ⟨(g : G) * x * (g : G)⁻¹, hx'⟩ =
        (φ₀ g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ secVec ψ ⟨x, hx⟩ := hψg
    rw [hψg']
    exact (glCongr_mulVec θ.symm (φ₀ g) (secVec ψ ⟨x, hx⟩)).symm
  let B' : LinearMap.BilinForm K (Fin 3 ⊕ Fin 3 → K) :=
    M₀.B.compl₁₂ e₀.symm.toLinearMap e₀.symm.toLinearMap
  have hB'apply : ∀ u w, B' u w = M₀.B (e₀.symm u) (e₀.symm w) := fun u w => rfl
  have hB'inv : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K), ∀ u w,
      B' ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ u)
          ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ w) = B' u w := by
    intro A hA u w
    have hArange : A ∈ φ'.range := by rw [hφ'range]; exact hA
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hArange
    have hzu : e₀.symm ((A : Matrix _ _ K) *ᵥ u) = Tof g (e₀.symm u) := by
      have h1 : e₀ (Tof g (e₀.symm u)) = (A : Matrix _ _ K) *ᵥ u := by
        obtain ⟨x, hxQ, hx⟩ := M₀.π_surj (e₀.symm u)
        rw [← hx, ← hTofπ g x hxQ, ← hg]
        simpa [hx] using hact₀ g x hxQ
      rw [← h1, LinearEquiv.symm_apply_apply]
    have hzw : e₀.symm ((A : Matrix _ _ K) *ᵥ w) = Tof g (e₀.symm w) := by
      have h1 : e₀ (Tof g (e₀.symm w)) = (A : Matrix _ _ K) *ᵥ w := by
        obtain ⟨x, hxQ, hx⟩ := M₀.π_surj (e₀.symm w)
        rw [← hx, ← hTofπ g x hxQ, ← hg]
        simpa [hx] using hact₀ g x hxQ
      rw [← h1, LinearEquiv.symm_apply_apply]
    rw [hB'apply, hB'apply, hzu, hzw, hTofB]
  have hB'nd : ∀ u, (∀ w, B' u w = 0) → u = 0 := by
    intro u hu
    have h1 : e₀.symm u = 0 := M₀.nondeg _ fun z => by
      have h := hu (e₀ z)
      rw [hB'apply, LinearEquiv.symm_apply_apply] at h
      exact h
    exact e₀.symm.injective (by simpa using h1)
  obtain ⟨c, hc0, hBrel⟩ :=
    exists_eq_smul_polarBilin_quadPlus_of_invariant B' hB'inv hB'nd
  let Q₂ : QuadraticForm K (Fin 3 ⊕ Fin 3 → K) := M₀.toQuadraticForm.comp e₀.symm.toLinearMap
  have hQ₂apply : ∀ u, Q₂ u = M₀.Qf (e₀.symm u) := fun u => rfl
  have hpolarQ₂ : polarBilin Q₂ = B' := by
    refine LinearMap.ext₂ ?_
    intro u w
    rw [show Q₂ = M₀.toQuadraticForm.comp e₀.symm.toLinearMap from rfl,
      QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply]
    change polar M₀.toQuadraticForm (e₀.symm u) (e₀.symm w) = B' u w
    rw [Tim79.QuadModel.polar_toQuadraticForm]
    exact (hB'apply u w).symm
  have hQ₂inv : ∀ A ∈ StatedOmega (StatedQuadPlus 3 K), ∀ v,
      Q₂ ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v) = Q₂ v := by
    intro A hA v
    have hArange : A ∈ φ'.range := by rw [hφ'range]; exact hA
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hArange
    have hzu : e₀.symm ((A : Matrix _ _ K) *ᵥ v) = Tof g (e₀.symm v) := by
      have h1 : e₀ (Tof g (e₀.symm v)) = (A : Matrix _ _ K) *ᵥ v := by
        obtain ⟨x, hxQ, hx⟩ := M₀.π_surj (e₀.symm v)
        rw [← hx, ← hTofπ g x hxQ, ← hg]
        simpa [hx] using hact₀ g x hxQ
      rw [← h1, LinearEquiv.symm_apply_apply]
    simp only [hQ₂apply, hzu, hTofQ]
  have hQ₂ : Q₂ = c • quadPlus 3 K :=
    eq_smul_of_polarBilin_eq_smul_of_statedOmega_invariant
      (by
        refine LinearMap.ext₂ ?_
        intro u w
        rw [hpolarQ₂, hBrel]
        simp [LinearMap.smul_apply, smul_eq_mul]) hQ₂inv
  let lam : K := (frobeniusEquiv K 2).symm c
  have hlam_sq : lam ^ 2 = c := by
    have h := (frobeniusEquiv K 2).apply_symm_apply c
    rwa [frobeniusEquiv_def] at h
  have hlam0 : lam ≠ 0 := by
    intro h
    apply hc0
    rw [← hlam_sq, h]
    ring
  let efin : M₀.E ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K) :=
    { toFun := fun v => lam • e₀ v
      invFun := fun u => lam⁻¹ • e₀.symm u
      left_inv := fun v => by
        change lam⁻¹ • e₀.symm (lam • e₀ v) = v
        rw [map_smul, LinearEquiv.symm_apply_apply, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
      right_inv := fun u => by
        change lam • e₀ (lam⁻¹ • e₀.symm u) = u
        rw [map_smul, LinearEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
      map_add' := fun v w => by rw [map_add, smul_add]
      map_smul' := fun a v => by
        change lam • e₀ (a • v) = a • (lam • e₀ v)
        rw [map_smul, smul_smul, smul_smul, mul_comm] }
  have hefin_quad : ∀ v, quadPlus 3 K (efin v) = M₀.Qf v := by
    intro v
    have hQ₂v : M₀.Qf v = c * quadPlus 3 K (e₀ v) := by
      have h := congrArg (fun Q => Q (e₀ v)) hQ₂
      simpa [Q₂, Tim79.QuadModel.toQuadraticForm_apply, QuadraticMap.smul_apply,
        smul_eq_mul] using h
    have hq : quadPlus 3 K (e₀ v) = c⁻¹ * M₀.Qf v := by
      rw [hQ₂v, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    change quadPlus 3 K (lam • e₀ v) = M₀.Qf v
    rw [QuadraticMap.map_smul, smul_eq_mul, hq, ← pow_two, hlam_sq, ← mul_assoc,
      mul_inv_cancel₀ hc0, one_mul]
  have hefin_act : ∀ (g : ↥(XbarPre M Q Z B)) (x : G), x ∈ Q →
      efin (M₀.π ((g : G) * x * (g : G)⁻¹)) =
        ((φ' g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
          efin (M₀.π x) := by
    intro g x hx
    change lam • e₀ (M₀.π ((g : G) * x * (g : G)⁻¹)) =
      ((φ' g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ
        (lam • e₀ (M₀.π x))
    rw [hact₀ g x hx, Matrix.mulVec_smul]
  exact ⟨φ', hφ'range, hφ'ker, efin, hefin_quad, hefin_act⟩

theorem l4Orthogonal_case_false_of_chain (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    (hD : GlobalModelData M Q Z γ M₀)
    {X₁ X₂ : Subgroup G} (hX₂ : X₂ = Q) (hX₁ : X₁ = Z)
    (nat : NaturalRep (ι := Fin 3 ⊕ Fin 3) K (StatedOmega (StatedQuadPlus 3 K))
      (XbarPre M Q Z B) X₂ X₁ (XbarPreCenter M Q Z B)) : False :=
  l4Orthogonal_case_false_of_orthogonalModuleRep hc hw hn hD hX₂ hX₁ nat
    (orthogonalModuleRep_of_chain hc hw hn hD hX₂ hX₁ nat)

end Main

end CFSG.RankThree.GF2n.Stroth80
