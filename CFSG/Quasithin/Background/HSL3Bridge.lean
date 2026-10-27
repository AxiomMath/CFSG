module

public import CFSG.Quasithin.Background.HSL3Beta
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearAut
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.Quasithin

namespace H

namespace SL3Pair

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped Matrix

variable {K : Type} [Field K]

theorem exists_eq_stdAut [Finite K] (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) K)) :
    ∃ (A : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 ∧
      α = CFSG.QuasithinUnique.K1.stdAut A σ ε := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hθ⟩ := hgen (descendAut 3 K α)
  refine ⟨A, σ, ε, hε, ?_⟩
  set β := CFSG.QuasithinUnique.K1.stdAut A σ ε with hβ
  have h2 : descendAut 3 K α = descendAut 3 K β := by
    rw [hθ, hβ, CFSG.QuasithinUnique.K1.descendAut_stdAut]
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := 3) le_rfl
  have key : ∀ s, (β s)⁻¹ * α s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    intro s
    have h1 := congrArg (fun f : MulAut (projectiveSL 3 K) => f (proj 3 K s)) h2
    simp only [descendAut_proj] at h1
    rw [← scalars_eq_center]
    exact proj_eq_proj_iff.mp h1.symm
  let d : Matrix.SpecialLinearGroup (Fin 3) K →*
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
    { toFun := fun x => ⟨(β x)⁻¹ * α x, key x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (β (x * y))⁻¹ * α (x * y) = ((β x)⁻¹ * α x) * ((β y)⁻¹ * α y)
        have hcx := Subgroup.mem_center_iff.mp (key x) (β y)⁻¹
        calc (β (x * y))⁻¹ * α (x * y)
            = (β y)⁻¹ * ((β x)⁻¹ * α x) * α y := by rw [map_mul, map_mul]; group
          _ = ((β x)⁻¹ * α x) * (β y)⁻¹ * α y := by rw [hcx]
          _ = ((β x)⁻¹ * α x) * ((β y)⁻¹ * α y) := by rw [mul_assoc] }
  have h1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative d
  refine MulEquiv.ext fun x => ?_
  have h3 : (β x)⁻¹ * α x = 1 := by
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K →*
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) => (g x : _)) h1
    simpa [d] using this
  exact (inv_mul_eq_one.mp h3).symm

@[expose] noncomputable def slEquiv (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(StatedSL 3 K) :=
  MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toGL).codRestrict (StatedSL 3 K) fun g =>
      mem_statedSL_iff.mpr g.2)
    ⟨fun _ _ hgh => Matrix.SpecialLinearGroup.toGL_injective (congrArg Subtype.val hgh),
      fun γ => ⟨⟨(γ : GL (Fin 3) K), mem_statedSL_iff.mp γ.2⟩, Subtype.ext (Units.ext rfl)⟩⟩

theorem coe_slEquiv (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    (((slEquiv K g : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) := rfl

theorem coe_slEquiv_inv (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((((slEquiv K g : ↥(StatedSL 3 K)) : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := rfl

theorem exists_mulEquiv_of_realizesVia_sub {ι : Type} [Fintype ι] [DecidableEq ι]
    (Γ : Subgroup (GL ι K)) {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U : Subgroup V} {π : ↥Γ →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U ⊥ π) :
    ∃ e : ↥U ≃* StdMod ι K, ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      e ⟨_, hu⟩ = natAct Γ γ (e u) := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := h
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.mp ((hβk u).mp hu))
  let q : ↥(⊤ : Subgroup (StdMod ι K)) ⧸
      (⊥ : Subgroup (StdMod ι K)).subgroupOf (⊤ : Subgroup (StdMod ι K)) ≃* StdMod ι K :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let e : ↥U ≃* StdMod ι K := (MulEquiv.ofBijective β ⟨hβi, hβs⟩).trans q
  refine ⟨e, fun γ u hu => ?_⟩
  have hqs : ∀ x, x = (QuotientGroup.mk ⟨q x, trivial⟩ : ↥(⊤ : Subgroup (StdMod ι K)) ⧸
      (⊥ : Subgroup (StdMod ι K)).subgroupOf (⊤ : Subgroup (StdMod ι K))) := fun x => by
    induction x using QuotientGroup.induction_on with
    | H m => rfl
  have h1 : β u = QuotientGroup.mk ⟨e u, trivial⟩ := hqs _
  have h2 := hβe γ u ⟨e u, trivial⟩ hu trivial h1
  exact congrArg q h2

variable [Finite K] [CharP K 2]

@[expose] noncomputable def twistAut (A : GL (Fin 3) K) (σ : K ≃+* K) :
    MulAut (StdMod (Fin 3) K) :=
  (fieldMap σ)⁻¹ * matAut A⁻¹

omit [Finite K] [CharP K 2] in
theorem twistAut_mul (A g : GL (Fin 3) K) (σ : K ≃+* K) :
    twistAut A σ * matAut (A * mapGL σ g * A⁻¹) = matAut g * twistAut A σ := by
  have h1 : matAut (A * mapGL σ g * A⁻¹) = matAut A * matAut (mapGL σ g) * (matAut A)⁻¹ := by
    show matHom (A * mapGL σ g * A⁻¹) = matHom A * matHom (mapGL σ g) * (matHom A)⁻¹
    rw [map_mul, map_mul, map_inv]
  have h2 : matAut A⁻¹ = (matAut A)⁻¹ := by
    show matHom A⁻¹ = (matHom A)⁻¹
    rw [map_inv]
  rw [twistAut, h1, h2, ← fieldMap_conj_matAut]
  group

omit [CharP K 2] in
theorem exists_pair_model {V : Type*} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} {V₁ : Subgroup V}
    (hreal : (FFModel.nat (StatedSL 3 K)).Realizes H V₁ ⊥) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) :
    ∃ e : V ≃* PairMod K, H.map (congrHom e) = pairSL K := by
  classical
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL 3 K) →* ↥H,
      (FFModel.nat (StatedSL 3 K)).RealizesVia H V₁ ⊥ π := hreal
  have hπs : Function.Surjective π := hπ.1
  have hU : ∀ h : ↥H, ∀ u ∈ V₁, (h : MulAut V) u ∈ V₁ := hπ.2.2.2.1
  obtain ⟨e₁, he₁⟩ := exists_mulEquiv_of_realizesVia_sub (StatedSL 3 K) hπ
  set V₂ := V₁.map φ.toMonoidHom with hV₂
  have hinv₁ : Pair.IsInv H V₁ := fun l hl w hw => hU ⟨l, hl⟩ w hw
  have hinv₂ : Pair.IsInv H V₂ := Pair.isInv_map hφ hinv₁
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply Subtype.ext
    apply Units.ext
    show ((γ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [Matrix.one_mulVec]
    obtain ⟨u, hu⟩ := e₁.surjective (Multiplicative.ofAdd v)
    have h1 := he₁ γ u (by rw [hγ]; exact u.2)
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), by rw [hγ]; exact u.2⟩ : ↥V₁) = u := by
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (u : V) = u
      rw [hγ]
      rfl
    rw [h2, hu] at h1
    exact (congrArg Multiplicative.toAdd h1).symm
  have hφi : φ⁻¹ ∈ Subgroup.normalizer (H : Set (MulAut V)) := Subgroup.inv_mem _ hφ
  let πe : ↥(StatedSL 3 K) ≃* ↥H := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  let cφ : MulAut ↥H := H.normalizerMonoidHom ⟨φ⁻¹, hφi⟩
  have hcφ : ∀ h : ↥H, ((cφ h : ↥H) : MulAut V) = φ⁻¹ * h * φ := fun h => by
    change φ⁻¹ * (h : MulAut V) * φ⁻¹⁻¹ = _
    rw [inv_inv]
  let α' : MulAut ↥(StatedSL 3 K) := (MulAut.congr πe.symm) cφ
  have hα' : ∀ γ, ((π (α' γ) : ↥H) : MulAut V) = φ⁻¹ * (π γ : MulAut V) * φ := fun γ => by
    have : π (α' γ) = cφ (π γ) := by
      change πe (πe.symm (cφ (πe γ))) = cφ (π γ)
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [this, hcφ]
  let α'' : MulAut (Matrix.SpecialLinearGroup (Fin 3) K) := (MulAut.congr (slEquiv K).symm) α'
  obtain ⟨A, σ, ε, hε, hα⟩ := exists_eq_stdAut α''
  have hα'' : ∀ γ, α' γ = slEquiv K (CFSG.QuasithinUnique.K1.stdAut A σ ε
      ((slEquiv K).symm γ)) := fun γ => by
    rw [← hα]
    change α' γ = slEquiv K ((slEquiv K).symm (α' (slEquiv K ((slEquiv K).symm γ))))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  let iφ : ↥V₁ ≃* ↥V₂ := Subgroup.equivMapOfInjective V₁ φ.toMonoidHom φ.injective
  let e₂ : ↥V₂ ≃* StdMod (Fin 3) K := (iφ.symm.trans e₁).trans (twistAut A σ)
  have hiφ : ∀ v : ↥V₁, ((iφ v : ↥V₂) : V) = φ v := fun v => rfl
  have hgen : ∀ (γ : ↥(StatedSL 3 K)) (g : GL (Fin 3) K),
      α' γ = A * mapGL σ g * A⁻¹ → ∀ (w : ↥V₂) (hw : ((π γ : ↥H) : MulAut V) (w : V) ∈ V₂),
        e₂ ⟨_, hw⟩ = matAut g (e₂ w) := by
    intro γ g hg w hw
    set v := iφ.symm w with hv
    have hwv : (w : V) = φ v := by rw [← hiφ, hv, MulEquiv.apply_symm_apply]
    have hmem : ((π (α' γ) : ↥H) : MulAut V) (v : V) ∈ V₁ := hU _ v v.2
    have hsymm : iφ.symm ⟨_, hw⟩ = ⟨_, hmem⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show ((π γ : ↥H) : MulAut V) (w : V) = φ (((π (α' γ) : ↥H) : MulAut V) (v : V))
      rw [hα', hwv]
      show _ = φ (φ⁻¹ (((π γ : ↥H) : MulAut V) (φ (v : V))))
      rw [MulAut.apply_inv_self]
    have h1 : e₂ ⟨_, hw⟩ = twistAut A σ (e₁ ⟨_, hmem⟩) := by
      change twistAut A σ (e₁ (iφ.symm ⟨_, hw⟩)) = _
      rw [hsymm]
    rw [h1, he₁ (α' γ) v hmem]
    change twistAut A σ (matAut (α' γ : GL (Fin 3) K) (e₁ v)) = matAut g (twistAut A σ (e₁ v))
    rw [hg, ← MulAut.mul_apply, twistAut_mul, MulAut.mul_apply]
  have hform0 : ε = 0 → ∀ γ : ↥(StatedSL 3 K), α' γ = A * mapGL σ (γ : GL (Fin 3) K) * A⁻¹ := by
    intro hε0 γ
    rw [hα'']
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_mapGL, coe_slEquiv, hε0,
      CFSG.QuasithinUnique.K1.coe_stdAut_zero]
    conv_rhs => rw [← MulEquiv.apply_symm_apply (slEquiv K) γ, coe_slEquiv]
  have hform1 : ε = 1 → ∀ γ : ↥(StatedSL 3 K),
      α' γ = A * mapGL σ (dualGL (γ : GL (Fin 3) K)) * A⁻¹ := by
    intro hε1 γ
    rw [hα'']
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_mapGL, coe_slEquiv, hε1,
      CFSG.QuasithinUnique.K1.coe_stdAut_one, coe_dualGL]
    conv_rhs => rw [← MulEquiv.apply_symm_apply (slEquiv K) γ, coe_slEquiv_inv]
  have hε1 : ε = 1 := by
    by_contra hne
    have hε0 : ε = 0 := by omega
    apply hniso
    refine ⟨e₁.trans e₂.symm, fun l hl w hw => ?_⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨l, hl⟩
    have hl' : l = ((π γ : ↥H) : MulAut V) := by rw [hγ]
    subst hl'
    have hw2 : ((π γ : ↥H) : MulAut V) ((e₂.symm (e₁ w) : ↥V₂) : V) ∈ V₂ :=
      hinv₂ _ (π γ).2 _ (e₂.symm (e₁ w)).2
    have h1 := hgen γ γ (hform0 hε0 γ) (e₂.symm (e₁ w)) hw2
    rw [MulEquiv.apply_symm_apply] at h1
    change ((e₂.symm (e₁ ⟨_, hw⟩) : ↥V₂) : V) = _
    rw [he₁ γ w hw, show natAct (StatedSL 3 K) γ (e₁ w) = matAut (γ : GL (Fin 3) K) (e₁ w)
      from rfl, ← h1, MulEquiv.symm_apply_apply]
    rfl
  have hgen₂ : ∀ (γ : ↥(StatedSL 3 K)) (w : ↥V₂)
      (hw : ((π γ : ↥H) : MulAut V) (w : V) ∈ V₂),
      e₂ ⟨_, hw⟩ = matAut (dualGL (γ : GL (Fin 3) K)) (e₂ w) := fun γ =>
    hgen γ _ (hform1 hε1 γ)
  let μ : ↥V₁ × ↥V₂ →* V := V₁.subtype.coprod V₂.subtype
  have hμ : Function.Bijective μ := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      have h' : (a : V) * b = c * d := h
      obtain ⟨h1, h2⟩ := Pair.decomp_unique hinf a.2 b.2 c.2 d.2 h'
      exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
    · intro v
      obtain ⟨a, ha, b, hb, hab⟩ := Pair.exists_decomp hsup v
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  let dec : (↥V₁ × ↥V₂) ≃* V := MulEquiv.ofBijective μ hμ
  let e : V ≃* PairMod K := dec.symm.trans (MulEquiv.prodCongr e₁ e₂)
  refine ⟨e, ?_⟩
  have hpair : ∀ γ : ↥(StatedSL 3 K), congrHom e ((π γ : ↥H) : MulAut V) = pairHom γ := by
    intro γ
    refine MulEquiv.ext fun x => ?_
    rw [congrHom_apply, pairHom_apply, pairAut_apply]
    set a := e₁.symm x.1 with ha
    set b := e₂.symm x.2 with hb
    have hx : e.symm x = (a : V) * b := rfl
    rw [hx, map_mul]
    have ha' : ((π γ : ↥H) : MulAut V) (a : V) ∈ V₁ := hU _ a a.2
    have hb' : ((π γ : ↥H) : MulAut V) (b : V) ∈ V₂ := hinv₂ _ (π γ).2 b b.2
    have hdec : dec.symm (((π γ : ↥H) : MulAut V) (a : V) * ((π γ : ↥H) : MulAut V) (b : V)) =
        (⟨_, ha'⟩, ⟨_, hb'⟩) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change MulEquiv.prodCongr e₁ e₂ (dec.symm _) = _
    rw [hdec]
    change (e₁ ⟨_, ha'⟩, e₂ ⟨_, hb'⟩) = _
    rw [he₁ γ a ha', hgen₂ γ b hb', ha, hb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    rfl
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨γ, hγ⟩ := hπs ⟨h, hh⟩
    have : h = ((π γ : ↥H) : MulAut V) := by rw [hγ]
    rw [this, hpair]
    exact pairHom_mem_pairSL γ.2
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨_, (π ⟨γ, hγ⟩).2, hpair ⟨γ, hγ⟩⟩

theorem H4_1_SL3Pair {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} {n : ℕ} (hn : 2 ≤ n) (hreal : BinaryNaturalSL H V₁ ⊥ 3 n) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) (hHM : H ≤ M)
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    CFSG.Open.pRank 2 M ≤ 2 * n ∧ ¬ IsFOneModule M ∧ alphaH M = 1 ∧
      (HypBang M → ((4 * n : ℕ) : ℕ∞) ≤ betaH M) := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ n) hK
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e.toEquiv
  have h1 : pairSL K ≤ M.map (congrHom e) := he ▸ Subgroup.map_mono hHM
  have h2 : M.map (congrHom e) ≤ pairNorm K := by
    have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
          Set (MulAut (PairMod K))) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    rw [pairNorm, ← he, ← h3]
    exact Subgroup.map_mono hMN
  refine ⟨?_, ?_, ?_, fun hB => ?_⟩
  · rw [← pRank_two_map_congrHom e]
    exact pRank_le hn hK h2
  · rw [← isFOneModule_map_congrHom e]
    exact not_isFOneModule hn hK h2
  · rw [← alphaH_map_congrHom e]
    exact alphaH_eq_one hn hK h2
  · rw [← betaH_map_congrHom e]
    exact le_betaH hn hK h1 h2 ((hypBang_map_congrHom e).mpr hB)

end SL3Pair

end H

end CFSG.Quasithin
