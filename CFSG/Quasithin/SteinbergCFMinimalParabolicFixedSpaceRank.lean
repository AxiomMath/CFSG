module

public import CFSG.Quasithin.SteinbergBQBinaryPlaneCodimension
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathSolvable
public import CFSG.RankThree.FFModules.ChiefFactors
public import CFSG.Quasithin.H13.A7SharedSolvableOvergroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathAct

public section

namespace CFSG.Quasithin.SteinbergCF

open Module CFSG.QuasithinUnique.Setup.Offender

theorem card_mul_card_fixSub_le_of_planes {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {r : ℕ} {W₀ : Submodule (ZMod 2) V} {I : Fin r → Submodule (ZMod 2) V}
    (hdim : ∀ i, finrank (ZMod 2) (I i) = 2) (hindep : iSupIndep I) (hsup : ⨆ i, I i = W₀)
    (E : Subgroup (W₀ ≃ₗ[ZMod 2] W₀)) (hE : IsElementaryAbelian 2 E)
    (hperm : ∀ e ∈ E, ∀ i, ∃ j, ∀ w : W₀, ((e w : W₀) : V) ∈ I j ↔ (w : V) ∈ I i) :
    Nat.card E * Nat.card (fixSub (MonoidHom.id (W₀ ≃ₗ[ZMod 2] W₀)) E) ≤ Nat.card W₀ := by
  classical
  have hle : ∀ i, I i ≤ W₀ := fun i => hsup ▸ le_iSup I i
  set I' : Fin r → Submodule (ZMod 2) W₀ := fun i => (I i).comap W₀.subtype with hI'
  have hmap : ∀ i, (I' i).map W₀.subtype = I i := fun i => by
    rw [hI', Submodule.map_comap_subtype, inf_eq_right.mpr (hle i)]
  have hdim' : ∀ i, finrank (ZMod 2) (I' i) = 2 := fun i => by
    have h := ((I' i).equivMapOfInjective W₀.subtype W₀.subtype_injective).finrank_eq
    rw [hmap i, hdim i] at h
    exact h
  have hindep' : iSupIndep I' := by
    intro i
    have h := hindep i
    rw [disjoint_iff] at h ⊢
    rw [eq_bot_iff]
    intro x hx
    have hx1 : (x : V) ∈ I i := hx.1
    have hx2 : (x : V) ∈ ⨆ j, ⨆ (_ : j ≠ i), I j := by
      have h2 : (⨆ j, ⨆ (_ : j ≠ i), I' j).map W₀.subtype ≤ ⨆ j, ⨆ (_ : j ≠ i), I j := by
        rw [Submodule.map_iSup]
        refine iSup_mono fun j => ?_
        rw [Submodule.map_iSup]
        exact iSup_mono fun _ => (hmap j).le
      exact h2 ⟨x, hx.2, rfl⟩
    have h3 : (x : V) ∈ I i ⊓ ⨆ j, ⨆ (_ : j ≠ i), I j := ⟨hx1, hx2⟩
    rw [h, Submodule.mem_bot] at h3
    rw [Submodule.mem_bot]
    exact Subtype.ext h3
  have hsup' : ⨆ i, I' i = ⊤ := by
    apply Submodule.map_injective_of_injective W₀.subtype_injective
    rw [Submodule.map_iSup, Submodule.map_subtype_top]
    simp_rw [hmap]
    exact hsup
  have hint : DirectSum.IsInternal I' :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep' hsup'
  set φ : W₀ ≃ₗ[ZMod 2] ((i : Fin r) → I' i) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap I') hint).symm.trans
      (DirectSum.linearEquivFunOnFintype (ZMod 2) (Fin r) fun i => ↥(I' i)) with hφ
  have hφs : ∀ i (x : I' i), φ (x : W₀) = Pi.single i x := by
    intro i x
    have h1 : (LinearEquiv.ofBijective (DirectSum.coeLinearMap I') hint).symm (x : W₀) =
        DirectSum.lof (ZMod 2) (Fin r) (fun i => ↥(I' i)) i x := by
      rw [LinearEquiv.symm_apply_eq]
      exact (DirectSum.coeLinearMap_of I' i x).symm
    rw [hφ, LinearEquiv.trans_apply, h1, DirectSum.linearEquivFunOnFintype_lof]
  set Pw := (i : Fin r) → I' i
  let ψ : (W₀ ≃ₗ[ZMod 2] W₀) →* LinearMap.GeneralLinearGroup (ZMod 2) Pw :=
    { toFun := fun e => (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Pw).symm
        (φ.symm.trans (e.trans φ))
      map_one' := by
        apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Pw).injective
        rw [MulEquiv.apply_symm_apply, map_one]
        ext w
        simp
      map_mul' := fun e f => by
        apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Pw).injective
        rw [MulEquiv.apply_symm_apply, map_mul, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply]
        ext w
        simp }
  have hψ : ∀ e w, ((ψ e : LinearMap.GeneralLinearGroup (ZMod 2) Pw) : Pw →ₗ[ZMod 2] Pw) w =
      φ (e (φ.symm w)) := fun e w => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro e he
    ext w
    have h := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) Pw =>
      ((u : LinearMap.GeneralLinearGroup (ZMod 2) Pw) : Pw →ₗ[ZMod 2] Pw) (φ w)) he
    simp only [hψ, LinearEquiv.symm_apply_apply] at h
    simpa using φ.injective h
  set E'' := E.map ψ with hE''
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEp : ∀ a ∈ E, a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian (A := E) a ha
  have hE''e : IsElementaryAbelian 2 E'' :=
    { toIsMulCommutative := ⟨⟨fun a b => by
        obtain ⟨x, hx, hxa⟩ := a.2
        obtain ⟨y, hy, hyb⟩ := b.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
          hEc x hx y hy]⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨x, hx, hxa⟩ := a.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxa, ← map_pow, hEp x hx, map_one] }
  have hperm'' : ∀ e ∈ E'', ∀ i, ∃ j, (SteinbergBQ.BinaryPlanes.plane (fun i => ↥(I' i)) i).map
      ((e : LinearMap.GeneralLinearGroup (ZMod 2) Pw) : Pw →ₗ[ZMod 2] Pw) =
        SteinbergBQ.BinaryPlanes.plane (fun i => ↥(I' i)) j := by
    rintro _ ⟨e, he, rfl⟩ i
    obtain ⟨j, hj⟩ := hperm e he i
    refine ⟨j, le_antisymm ?_ ?_⟩
    · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      rw [hψ]
      have hx : φ.symm (Pi.single i x) = (x : W₀) := by
        rw [LinearEquiv.symm_apply_eq, hφs]
      have hex : ((e (x : W₀) : W₀) : V) ∈ I j := (hj x).mpr x.2
      have hex' : (e (x : W₀) : W₀) ∈ I' j := hex
      refine ⟨⟨e (x : W₀), hex'⟩, ?_⟩
      show Pi.single j _ = _
      rw [LinearMap.single_apply, ← hφs j ⟨e (x : W₀), hex'⟩]
      simp only [hx]
    · rintro _ ⟨z, rfl⟩
      have hez : ((e (e.symm (z : W₀)) : W₀) : V) ∈ I j := by
        rw [LinearEquiv.apply_symm_apply]
        exact z.2
      have hyi : ((e.symm (z : W₀) : W₀) : V) ∈ I i := (hj _).mp hez
      refine ⟨φ (e.symm (z : W₀)), ⟨⟨e.symm (z : W₀), hyi⟩, ?_⟩, ?_⟩
      · show Pi.single i _ = _
        rw [← hφs i ⟨e.symm (z : W₀), hyi⟩]
      · rw [hψ, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
        show φ (z : W₀) = LinearMap.single (ZMod 2) (fun i => ↥(I' i)) j z
        rw [hφs, LinearMap.single_apply]
  set C'' : Submodule (ZMod 2) Pw :=
    (fixSub (MonoidHom.id (W₀ ≃ₗ[ZMod 2] W₀)) E).map (φ : W₀ →ₗ[ZMod 2] Pw) with hC''
  have hC''mem : ∀ w, w ∈ C'' ↔ ∀ e ∈ E'',
      ((e : LinearMap.GeneralLinearGroup (ZMod 2) Pw) : Pw →ₗ[ZMod 2] Pw) w = w := by
    intro w
    constructor
    · rintro ⟨v, hv, rfl⟩ _ ⟨e, he, rfl⟩
      rw [hψ]
      have := (mem_fixSub.mp hv) e he
      simp only [MonoidHom.id_apply] at this
      simp [this]
    · intro h
      refine ⟨φ.symm w, mem_fixSub.mpr fun e he => ?_, by simp⟩
      have h1 := h (ψ e) ⟨e, he, rfl⟩
      rw [hψ] at h1
      have h2 := congrArg φ.symm h1
      simpa using h2
  have hbound := SteinbergBQ.BinaryPlanes.card_mul_card_fixed_le_card hdim' E'' hperm'' C''
    hC''mem
  have hcE : Nat.card E'' = Nat.card E :=
    Subgroup.card_map_of_injective hψinj
  have hcC : Nat.card C'' = Nat.card (fixSub (MonoidHom.id (W₀ ≃ₗ[ZMod 2] W₀)) E) :=
    Nat.card_congr ((fixSub (MonoidHom.id (W₀ ≃ₗ[ZMod 2] W₀)) E).equivMapOfInjective
      (φ : W₀ →ₗ[ZMod 2] Pw) φ.injective).symm.toEquiv
  have hcW : Nat.card Pw = Nat.card W₀ := Nat.card_congr φ.symm.toEquiv
  rw [hcE, hcC, hcW] at hbound
  exact hbound

theorem eq_top_of_invariant_of_irreducible {H W : Type*} [Group H] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W) [ρ.IsIrreducible]
    (U : Submodule (ZMod 2) W) (hU : ∀ g : H, ∀ u ∈ U, ρ g u ∈ U) {x : W} (hx : x ≠ 0)
    (hxU : x ∈ U) : U = ⊤ := by
  let U' : Subrepresentation ρ := ⟨U, fun g _ hu => hU g _ hu⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top U' with h | h
  · exfalso
    have : x ∈ U'.toSubmodule := hxU
    rw [h] at this
    exact hx ((Submodule.mem_bot _).mp this)
  · have : U'.toSubmodule = ⊤ := by rw [h]; rfl
    exact this

theorem isElementaryAbelian_range {p : ℕ} {X Y : Type*} [Group X] [Group Y] (E : Subgroup X)
    [hE : IsElementaryAbelian p E] (f : ↥E →* Y) : IsElementaryAbelian p f.range :=
  { toIsMulCommutative := ⟨⟨fun a b => by
      obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul,
        hE.toIsMulCommutative.is_comm.comm x y]⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      obtain ⟨x, hx⟩ := a.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx, ← map_pow,
        Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hE.exponent_dvd_p x, map_one] }

theorem rep_apply_apply_eq {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (g p : H) (w : W) :
    ρ p (ρ g w) = ρ g (ρ (g⁻¹ * p * g) w) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply (ρ g), ← map_mul,
    show g * (g⁻¹ * p * g) = p * g by group]

theorem forall_apply_eq_of_isPGroup {H K W : Type*} [Group H] [Group K] [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] [Nontrivial W] (ρ : Representation (ZMod 2) H W)
    [ρ.IsIrreducible] (σ : Representation (ZMod 2) K W) {P : Subgroup K} (hP : IsPGroup 2 P)
    (hconj : ∀ g : H, ∀ p ∈ P, ∃ q ∈ P, ∀ w, σ p (ρ g w) = ρ g (σ q w)) :
    ∀ p ∈ P, ∀ w, σ p w = w := by
  obtain ⟨x, hx0, hx⟩ := CFSG.RankThree.FFModules.exists_fixed_ne_zero_of_isPGroup σ hP
  have hU := eq_top_of_invariant_of_irreducible ρ (Representation.invariants (σ.comp P.subtype))
    (fun g u hu q => by
      obtain ⟨q', hq', hqq'⟩ := hconj g q q.2
      have h1 := hu ⟨q', hq'⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h1 ⊢
      rw [hqq', h1]) hx0 (fun q => hx q q.2)
  intro p hp w
  have hw : w ∈ Representation.invariants (σ.comp P.subtype) := hU ▸ Submodule.mem_top
  exact hw ⟨p, hp⟩

open CFSG.QuasithinUnique in
theorem card_mul_card_fixSub_le_of_minimal_parabolic {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] {H T M E : Subgroup (W ≃ₗ[ZMod 2] W)}
    (hsolv : Group.IsSolvable ↥H)
    (hO2 : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N →
      N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (W ≃ₗ[ZMod 2] W), T ≤ Y → Y < H → Y ≤ M)
    (hEH : E ≤ H) (hEel : IsElementaryAbelian 2 E) :
    Nat.card E * Nat.card (fixSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) E) ≤ Nat.card W := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hEne : E ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot, one_mul] at hlt
    exact absurd (Nat.card_le_card_of_injective _ Subtype.val_injective) (not_le.mpr hlt)
  obtain ⟨-, r, -, L, S, I, P, hd⟩ :=
    CFSG.QuasithinUnique.Setup.Wreath.solvable_minimal_parabolic_S3_wreath hsolv hO2 hT hTn hTM
      hMH hmax hEH hEne hEel hlt.le
  obtain ⟨hW, hrange⟩ := hd.image_eq
  set W₁ := commGL ((CFSG.fittingSubgroup ↥H).map H.subtype) ⊤ with hW₁
  have hWE : QuasithinUnique.Setup.Offender.IsInvariant (MonoidHom.id (W ≃ₗ[ZMod 2] W)) E W₁ :=
    fun e he => hW e (hEH he)
  set res := Setup.Layer.resSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) E W₁ hWE with hres
  have hres_apply : ∀ (e : E) (w : W₁), ((res e w : W₁) : W) = (e : W ≃ₗ[ZMod 2] W) w :=
    fun e w => Setup.Layer.resSub_apply _ _ _ _ e w
  have hinj : Function.Injective res := by
    rw [injective_iff_map_eq_one]
    intro e he
    apply Subtype.ext
    apply hd.faithful e (hEH e.2)
    intro w hw
    have := congrArg (fun f : W₁ ≃ₗ[ZMod 2] W₁ => ((f ⟨w, hw⟩ : W₁) : W)) he
    simpa [hres_apply] using this
  have hE₁el : IsElementaryAbelian 2 res.range := isElementaryAbelian_range E res
  have hperm : ∀ e ∈ res.range, ∀ i, ∃ j, ∀ w : W₁, ((e w : W₁) : W) ∈ I j ↔ (w : W) ∈ I i := by
    rintro _ ⟨e, rfl⟩ i
    have hmem : res e ∈ (Setup.Layer.resSub (MonoidHom.id _) H W₁ hW).range :=
      ⟨⟨e, hEH e.2⟩, LinearEquiv.ext fun w => Subtype.ext (by
        rw [Setup.Layer.resSub_apply, hres_apply]; rfl)⟩
    rw [hrange] at hmem
    obtain ⟨σ, -, hσ⟩ := hmem
    exact ⟨σ i, hσ i⟩
  have hbound := card_mul_card_fixSub_le_of_planes hd.finrank_I hd.I_indep hd.W_eq.symm res.range
    hE₁el hperm
  have hcE : Nat.card res.range = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  set X := fixSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) E with hX
  have hfix : (fixSub (MonoidHom.id (W₁ ≃ₗ[ZMod 2] W₁)) res.range).map W₁.subtype = X ⊓ W₁ := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨mem_fixSub.mpr fun e he => ?_, w.2⟩
      have := (mem_fixSub.mp hw) (res ⟨e, he⟩) ⟨⟨e, he⟩, rfl⟩
      have h2 := congrArg Subtype.val this
      simp only [MonoidHom.id_apply] at h2
      rw [hres_apply] at h2
      exact h2
    · rintro ⟨hv, hv₁⟩
      refine ⟨⟨v, hv₁⟩, mem_fixSub.mpr ?_, rfl⟩
      rintro _ ⟨e, rfl⟩
      apply Subtype.ext
      simp only [MonoidHom.id_apply]
      rw [hres_apply]
      exact (mem_fixSub.mp hv) e e.2
  have hc₁ : finrank (ZMod 2) (fixSub (MonoidHom.id (W₁ ≃ₗ[ZMod 2] W₁)) res.range) =
      finrank (ZMod 2) ↥(X ⊓ W₁) := by
    rw [← hfix, Submodule.finrank_map_subtype_eq]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq X W₁
  have hle := Submodule.finrank_le (X ⊔ W₁)
  have hcard : ∀ (U : Type _) [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U],
      Nat.card U = 2 ^ finrank (ZMod 2) U := fun U _ _ _ => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcE, hcard ↥(fixSub (MonoidHom.id (W₁ ≃ₗ[ZMod 2] W₁)) res.range), hcard W₁, hc₁] at hbound
  rw [hcard X, hcard W] at hlt
  have h1 : Nat.card E * 2 ^ finrank (ZMod 2) X * 2 ^ finrank (ZMod 2) W₁ ≤
      2 ^ finrank (ZMod 2) W * 2 ^ finrank (ZMod 2) W₁ :=
    calc Nat.card E * 2 ^ finrank (ZMod 2) X * 2 ^ finrank (ZMod 2) W₁
        = Nat.card E * 2 ^ (finrank (ZMod 2) X + finrank (ZMod 2) W₁) := by rw [pow_add, mul_assoc]
      _ ≤ Nat.card E * 2 ^ (finrank (ZMod 2) W + finrank (ZMod 2) ↥(X ⊓ W₁)) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by omega))
      _ = Nat.card E * 2 ^ finrank (ZMod 2) ↥(X ⊓ W₁) * 2 ^ finrank (ZMod 2) W := by
          rw [pow_add]; ring
      _ ≤ 2 ^ finrank (ZMod 2) W₁ * 2 ^ finrank (ZMod 2) W := Nat.mul_le_mul_right _ hbound
      _ = 2 ^ finrank (ZMod 2) W * 2 ^ finrank (ZMod 2) W₁ := mul_comm _ _
  have h2 := Nat.le_of_mul_le_mul_right h1 (pow_pos two_pos _)
  omega

open CFSG.QuasithinUnique in
theorem solvable_minimal_parabolic_irreducible_factor_fixed_space_rank {H : Type*} [Group H]
    [Finite H] (hsolv : Group.IsSolvable H) (T : Sylow 2 H) (hTn : ¬ (T : Subgroup H).Normal)
    {M : Subgroup H} (hM : IsCoatom M) (hTM : (T : Subgroup H) ≤ M)
    (huniq : ∀ Y : Subgroup H, IsCoatom Y → (T : Subgroup H) ≤ Y → Y = M)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) [ρ.IsIrreducible] (hρ : ∃ g, ρ g ≠ 1) :
    ρ.ker ⊓ T = CFSG.pCore 2 H ∧ CFSG.pCore 2 (H ⧸ ρ.ker) = ⊥ ∧
      ∀ A : Subgroup H, A ≤ T → IsElementaryAbelian 2 A →
        Nat.log 2 ((CFSG.pCore 2 H).relIndex A) ≤
          finrank (ZMod 2) (W ⧸ Representation.invariants (ρ.comp A.subtype)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Nontrivial W := by
    obtain ⟨g, hg⟩ := hρ
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hg (LinearMap.ext fun w => Subsingleton.elim _ _)
  set C := ρ.ker with hC
  set Q := CFSG.pCore 2 H with hQ
  have hQC : Q ≤ C := by
    intro n hn
    have h := forall_apply_eq_of_isPGroup ρ ρ (P := Q) CFSG.pCore_isPGroup fun g p hp =>
      ⟨g⁻¹ * p * g, by simpa using (CFSG.pCore_normal (p := 2) (G := H)).conj_mem p hp g⁻¹,
        fun w => rep_apply_apply_eq ρ g p w⟩
    exact MonoidHom.mem_ker.mpr (LinearMap.ext (h n hn))
  have hO2bar : CFSG.pCore 2 (H ⧸ C) = ⊥ := by
    set ρbar : Representation (ZMod 2) (H ⧸ C) W := QuotientGroup.lift C ρ le_rfl with hρbar
    have hρbar_mk : ∀ g : H, ρbar g = ρ g := fun g => QuotientGroup.lift_mk _ _ _
    have h := forall_apply_eq_of_isPGroup ρ ρbar (P := CFSG.pCore 2 (H ⧸ C))
      CFSG.pCore_isPGroup fun g p hp =>
      ⟨(g : H ⧸ C)⁻¹ * p * g, by
        have := (CFSG.pCore_normal (p := 2) (G := H ⧸ C)).conj_mem p hp (g : H ⧸ C)⁻¹
        rwa [inv_inv] at this,
        fun w => by
          rw [← hρbar_mk g]
          exact rep_apply_apply_eq ρbar (g : H ⧸ C) p w⟩
    rw [eq_bot_iff]
    intro p hp
    rw [Subgroup.mem_bot]
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
    rw [QuotientGroup.eq_one_iff]
    have h1 : ρbar g = 1 := LinearMap.ext (h _ hp)
    rw [hρbar_mk] at h1
    exact MonoidHom.mem_ker.mpr h1
  have hCM : C ≤ M := by
    by_contra hCM
    have hCT : C ⊔ (T : Subgroup H) = ⊤ := by
      by_contra hne
      obtain ⟨Y, hY, hle⟩ := (eq_top_or_exists_le_coatom (C ⊔ (T : Subgroup H))).resolve_left hne
      have hYM := huniq Y hY (le_sup_right.trans hle)
      exact hCM (hYM ▸ le_sup_left.trans hle)
    have hmapT : (T : Subgroup H).map (QuotientGroup.mk' C) = ⊤ := by
      have := congrArg (Subgroup.map (QuotientGroup.mk' C)) hCT
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)] at this
    have hN : ((T : Subgroup H).map (QuotientGroup.mk' C)).Normal := by
      rw [hmapT]
      infer_instance
    have htop : (T : Subgroup H).map (QuotientGroup.mk' C) ≤ CFSG.pCore 2 (H ⧸ C) :=
      le_sSup ⟨hN, T.isPGroup'.map _⟩
    rw [hmapT, hO2bar] at htop
    obtain ⟨g, hg⟩ := hρ
    have h1 : (g : H ⧸ C) = 1 := (Subgroup.mem_bot).mp (htop (Subgroup.mem_top _))
    exact hg (MonoidHom.mem_ker.mp ((QuotientGroup.eq_one_iff g).mp h1))
  obtain ⟨p, -, -, P, -, -, -, -, hPT, -, -, -, -, hcore⟩ :=
    CFSG.Quasithin.H13.A7.A7_solvable_unique_Sylow_overgroup_structure hsolv T hTn hM hTM huniq
  have hCπ : C.map (QuotientGroup.mk' Q) ≤ P := by
    have : (C.map (QuotientGroup.mk' Q)).Normal :=
      (MonoidHom.normal_ker ρ).map _ (QuotientGroup.mk'_surjective Q)
    have h1 : C.map (QuotientGroup.mk' Q) ≤ (M.map (QuotientGroup.mk' Q)).normalCore :=
      Subgroup.normal_le_normalCore.mpr (Subgroup.map_mono hCM)
    rw [hcore] at h1
    exact h1.trans (Subgroup.map_subtype_le _)
  have hQT : Q ≤ T := CFSG.pCore_isPGroup.le_sylow_of_normal T
  have hCT : C ⊓ T = Q := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQC hQT)
    have h1 : QuotientGroup.mk' Q x ∈ P ⊓ (T : Subgroup H).map (QuotientGroup.mk' Q) :=
      ⟨hCπ ⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
    rw [hPT, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  refine ⟨hCT, hO2bar, fun A hAT hA => ?_⟩
  set ρGL : H →* (W ≃ₗ[ZMod 2] W) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp ρ.asGroupHom
    with hρGL
  have hρGLa : ∀ g w, ρGL g w = ρ g w := fun g w => rfl
  have hker : ρGL.ker = C := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact LinearMap.ext fun w => by rw [← hρGLa, h]; rfl
    · intro h
      exact LinearEquiv.ext fun w => by rw [hρGLa, h]; rfl
  have := hsolv
  have hsolv₀ : Group.IsSolvable ↥ρGL.range :=
    Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective ρGL)
  have hO2₀ : ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ ρGL.range → (N.subgroupOf ρGL.range).Normal →
      IsPGroup 2 N → N = ⊥ := by
    intro N hNH hNn hN2
    have h := forall_apply_eq_of_isPGroup ρ LinearEquiv.automorphismGroup.toLinearMapMonoidHom
      hN2 fun g e he => by
        have hmem : (⟨e, hNH he⟩ : ρGL.range) ∈ N.subgroupOf ρGL.range := he
        have h1 := hNn.conj_mem _ hmem (⟨ρGL g, g, rfl⟩ : ρGL.range)⁻¹
        rw [Subgroup.mem_subgroupOf] at h1
        refine ⟨(ρGL g)⁻¹ * e * ρGL g, by simpa using h1, fun w => ?_⟩
        show e (ρGL g w) = ρGL g (((ρGL g)⁻¹ * e * ρGL g) w)
        simp only [LinearEquiv.mul_apply]
        exact (LinearEquiv.apply_symm_apply (ρGL g) _).symm
    rw [eq_bot_iff]
    intro e he
    rw [Subgroup.mem_bot]
    exact LinearEquiv.ext (h e he)
  have heq : ((T : Subgroup H).map ρGL).subgroupOf ρGL.range =
      (T : Subgroup H).map ρGL.rangeRestrict := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨t, ht, hty⟩
      exact ⟨t, ht, Subtype.ext hty⟩
    · rintro ⟨t, ht, hty⟩
      exact ⟨t, ht, congrArg Subtype.val hty⟩
  have hT₀ : IsSylowTwoOf ((T : Subgroup H).map ρGL) ρGL.range := by
    refine ⟨Subgroup.map_le_range _ _, T.isPGroup'.map ρGL, ?_⟩
    rw [heq]
    intro hdvd
    exact T.not_dvd_index
      (hdvd.trans (Subgroup.index_map_dvd _ (MonoidHom.rangeRestrict_surjective ρGL)))
  have hTn₀ : ¬ (((T : Subgroup H).map ρGL).subgroupOf ρGL.range).Normal := by
    rw [heq]
    intro hn
    have h1 := hn.comap ρGL.rangeRestrict
    rw [Subgroup.comap_map_eq, MonoidHom.ker_rangeRestrict, hker] at h1
    have := h1
    have hfr₀ := Sylow.normalizer_sup_eq_top' (N := (T : Subgroup H) ⊔ C) T le_sup_left
    have hfr : Subgroup.normalizer ((T : Subgroup H) : Set H) ⊔ C = ⊤ := by
      rw [eq_top_iff, ← hfr₀]
      exact sup_le le_sup_left (sup_le (Subgroup.le_normalizer.trans le_sup_left) le_sup_right)
    apply hTn
    rw [← Subgroup.normalizer_eq_top_iff]
    by_contra hne
    obtain ⟨Y, hY, hle⟩ :=
      (eq_top_or_exists_le_coatom (Subgroup.normalizer (T : Set H))).resolve_left hne
    have hYM := huniq Y hY (Subgroup.le_normalizer.trans hle)
    rw [hYM] at hle
    apply hM.1
    rw [eq_top_iff, ← hfr]
    exact sup_le hle hCM
  have hMH₀ : M.map ρGL < ρGL.range := by
    refine lt_of_le_of_ne (Subgroup.map_le_range _ _) fun h => hM.1 ?_
    rw [eq_top_iff]
    intro g _
    have hg : g ∈ (M.map ρGL).comap ρGL := by
      rw [h]
      exact Subgroup.mem_comap.mpr ⟨g, rfl⟩
    rwa [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hCM] at hg
  have hmax₀ : ∀ Y : Subgroup (W ≃ₗ[ZMod 2] W), (T : Subgroup H).map ρGL ≤ Y → Y < ρGL.range →
      Y ≤ M.map ρGL := by
    intro Y hTY hYH
    have hTY' : (T : Subgroup H) ≤ Y.comap ρGL := Subgroup.map_le_iff_le_comap.mp hTY
    have hY' : Y.comap ρGL ≠ ⊤ := by
      intro htop
      apply hYH.not_ge
      rintro _ ⟨g, rfl⟩
      have : g ∈ Y.comap ρGL := htop ▸ Subgroup.mem_top g
      exact this
    obtain ⟨Z, hZ, hle⟩ := (eq_top_or_exists_le_coatom (Y.comap ρGL)).resolve_left hY'
    have hZM := huniq Z hZ (hTY'.trans hle)
    intro y hy
    obtain ⟨g, rfl⟩ := hYH.le hy
    exact ⟨g, hZM ▸ hle hy, rfl⟩
  have := hA
  have hbound := card_mul_card_fixSub_le_of_minimal_parabolic hsolv₀ hO2₀ hT₀ hTn₀
    (Subgroup.map_mono hTM) hMH₀ hmax₀ (Subgroup.map_le_range ρGL A)
    (Setup.Layer.isElementaryAbelian_map ρGL A)
  have hcardE : Nat.card (A.map ρGL) = Q.relIndex A := by
    have h1 := CFSG.QuasithinUnique.Setup.Wreath.card_map_mul_card_inf_ker ρGL A
    have h2 := Subgroup.relIndex_mul_card Q A
    have h3 : A ⊓ ρGL.ker = Q ⊓ A := by
      rw [hker, ← hCT, inf_assoc, inf_eq_right.mpr hAT, inf_comm]
    rw [h3] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  have hfixeq : fixSub (MonoidHom.id (W ≃ₗ[ZMod 2] W)) (A.map ρGL) =
      Representation.invariants (ρ.comp A.subtype) := by
    ext w
    rw [mem_fixSub, Representation.mem_invariants]
    constructor
    · intro h a
      exact h (ρGL a) ⟨a, a.2, rfl⟩
    · rintro h _ ⟨a, ha, rfl⟩
      exact h ⟨a, ha⟩
  rw [hcardE, hfixeq] at hbound
  set X := Representation.invariants (ρ.comp A.subtype) with hX
  have hq := Submodule.finrank_quotient_add_finrank X
  have hcard : ∀ (U : Type _) [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U],
      Nat.card U = 2 ^ finrank (ZMod 2) U := fun U _ _ _ => by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard ↥X, hcard W, ← hq, pow_add] at hbound
  have h1 : Q.relIndex A ≤ 2 ^ finrank (ZMod 2) (W ⧸ X) :=
    Nat.le_of_mul_le_mul_right hbound (pow_pos two_pos _)
  calc Nat.log 2 (Q.relIndex A) ≤ Nat.log 2 (2 ^ finrank (ZMod 2) (W ⧸ X)) :=
        Nat.log_mono_right h1
    _ = finrank (ZMod 2) (W ⧸ X) := Nat.log_pow one_lt_two _

end CFSG.Quasithin.SteinbergCF
