module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.StandardType.TableCRes

section Setup

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_langSetup_of_elem_untw
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (y : ↥(adjointGroup τ K)) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : ↥(adjointGroup τ K) →* ModGL τ (AlgebraicClosure K)),
      S.D.q = 2 ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ S.D.q) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧
      Function.Injective ι ∧ ι.range = S.Γ := by
  classical
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h <;> simp [h]
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with h | h | h | h <;> exact single_edge_perfect τ K (by simp [h])
  have hmon : MonomialToralAt τ p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five
      (by rcases hτ with h | h | h | h <;> simp [h]) hp hp2
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have h5K : ¬ 5 ∣ Nat.card K := by
    rw [hK]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).1
      (Nat.prime_five.dvd_of_dvd_pow h)
    omega
  obtain ⟨S, a, ι, hq, hFr, -, -, -, hinj, hrange, -⟩ :=
    exists_langSetup_of_inner_untw_of_prime hτ' hp hpK Nat.prime_five h5K (Or.inl le_rfl) hmon
      hperf (MulAut.conj y) (y : ModGL τ K)
      (baseChangeGL_mem_adjointGroup _ y.2) (fun c => by simp) (by
        rw [← Subgroup.coe_pow, hyp]; rfl) (fun h => hy1 (Subtype.ext h))
  refine ⟨S, ι, hq.trans hK, ?_, hinj, hrange⟩
  obtain ⟨Fr, hFr1, hFr2⟩ := hFr
  exact ⟨Fr, fun c => by rw [hq]; exact hFr1 c, hFr2⟩

end Setup

section Main

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem exists_uframe_untw
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D : Subgroup X} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) τ (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S : LangSetup τ (AlgebraicClosure K) 5), S.D.q = 2 ^ f ∧
      (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ S.D.q) ∧
        S.D.Φ = Units.map (entrywiseHom Fr)) ∧ Nonempty (GGTCUFrame S.Γ G₀ B) := by
  classical
  obtain ⟨K, instF, instFin, hKcard, ⟨eK⟩⟩ := hmod
  have : CharP K 2 := charP_two_of_finite_field_card_two_pow hKcard
  have hZadj : Subgroup.center ↥(adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  let θ : (↥G₀ ⧸ Subgroup.center ↥G₀) ≃* ↥(adjointGroup τ K) :=
    eK.trans ((QuotientGroup.quotientMulEquivOfEq hZadj).trans QuotientGroup.quotientBot)
  have hcl : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥ := by
    have h1 := Subgroup.map_center_eq θ
    rw [hZadj] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ θ.injective).1 h1
  obtain ⟨ν, hνinj, hνact⟩ := exists_inner_hom_of_faithful_inner hBN hin hfaith hcl
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    have h2 := hp.two_le
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  let b₀ : ↥B := ⟨(x : X), hDB x.2⟩
  have hb₀1 : b₀ ≠ 1 := by
    intro h
    apply hx1
    have h' : (x : X) = 1 := congrArg (fun z : ↥B => (z : X)) h
    exact Subtype.ext h'
  have hb₀p : b₀ ^ p = 1 := Subtype.ext (hBel.2 (x : X) (hDB x.2))
  have hy1 : θ (ν b₀) ≠ 1 := fun h => hb₀1 (hνinj (θ.injective (by rw [h, map_one, map_one])))
  have hyp : θ (ν b₀) ^ p = 1 := by rw [← map_pow, ← map_pow, hb₀p, map_one, map_one]
  obtain ⟨S, ι, hq, hFr, hinj, hrange⟩ :=
    exists_langSetup_of_elem_untw hτ hKcard hp hp2 (θ (ν b₀)) hy1 hyp
  exact ⟨K, instF, instFin, inferInstance, S, hq, hFr, ⟨⟨ν, hνinj, hνact,
    θ.trans ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩⟩⟩

theorem exists_torus_uframe_untw
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B : Subgroup X} [Finite B] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S : LangSetup τ (AlgebraicClosure K) 5)
    (fr : GGTCUFrame S.Γ G₀ B) (hBel : IsElemAbelian p B) (htor : UToralAt τ p (Nat.card B)) :
    ∃ S₁ : LangSetup τ (AlgebraicClosure K) 5, S₁.D.q = S.D.q ∧ S₁.D.Φ = S.D.Φ ∧
      (∃ w : WeylGroup τ, S₁.D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) ∧
      ∃ fr₁ : GGTCUFrame S₁.Γ G₀ B, fr₁.BLang ≤ S₁.D.torus := by
  classical
  have : Finite fr.BLang := Finite.of_equiv _ (MonoidHom.ofInjective fr.toLang_injective).toEquiv
  have hBΓ : fr.BLang ≤ S.Γ := by
    rintro _ ⟨b, rfl⟩
    exact (fr.Θ (fr.ν b)).2
  have hΓmodel : S.Γ ≤ S.D.model := by
    change ⁅S.D.model, S.D.model⁆ ≤ S.D.model
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
  have hBmodel : fr.BLang ≤ S.D.model := hBΓ.trans hΓmodel
  have hBadj : fr.BLang ≤ adjointGroup τ (AlgebraicClosure K) := hBmodel.trans inf_le_left
  have hBimgel : IsElemAbelian p fr.BLang := fr.isElemAbelian_BLang hBel
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨g, hg, hgx⟩ := htor K fr.BLang hBadj hBimgel fr.card_BLang
  obtain ⟨g₁, hg₁, S₁, hΦ₁, hq₁, hstep, hw, htorus, -, -⟩ :=
    ggTCInputG3Toral_holds τ (AlgebraicClosure K) 5 S hτ p hp hp2 fr.BLang hBmodel hBimgel
      ⟨g, hg, hgx⟩
  have hΓ := gamma_eq_map_of_step S S₁ hg₁ hstep
  let e : ↥S.Γ ≃* ↥S₁.Γ :=
    (MulEquiv.subgroupMap (MulAut.conj g₁⁻¹) S.Γ).trans (MulEquiv.subgroupCongr hΓ.symm)
  refine ⟨S₁, hq₁, hΦ₁, hw, fr.mapEquivΓ e, ?_⟩
  rintro _ ⟨b, rfl⟩
  have hlang : (fr.mapEquivΓ e).toLang b = g₁⁻¹ * fr.toLang b * g₁ := by
    change (MulAut.conj g₁⁻¹) ((fr.Θ (fr.ν b) : ↥S.Γ) : ModGL τ (AlgebraicClosure K)) = _
    rw [MulAut.conj_apply, inv_inv]
    rfl
  rw [hlang]
  exact htorus _ ⟨b, rfl⟩

theorem uframe_data
    {τ : Tag} (hField : UFieldInput τ) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} [Finite B] {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) τ (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hcent : B ⊓ Subgroup.centralizer (J : Set X) = D)
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htor : UToralAt τ p (Nat.card B)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S₁ : LangSetup τ (AlgebraicClosure K) 5) (fr₁ : GGTCUFrame S₁.Γ G₀ B),
      S₁.D.q = 2 ^ f ∧ fr₁.BLang ≤ S₁.D.torus ∧
      (∃ w : WeylGroup τ, ∀ γ, IsRoot τ γ → S₁.ρ γ = w • γ) ∧
      ∃ (a : ↥(fr₁.DLang D) → Fin τ.rank → (AlgebraicClosure K)ˣ)
        (i : KernelComponent (famCharHom a)),
        (∀ u : ↥(fr₁.DLang D), (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ (a u)) ∧
        (∀ u j, a u j ^ p = 1) ∧
        fr₁.JLang J ≤ rootSpan τ (AlgebraicClosure K) (famOrbit S₁.ρ a i) ∧
        2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) ∧
        IsRootComponent (componentRoots (famCharHom a) i) ∧
        (∀ γ ∈ componentRoots (famCharHom a) i,
          ∀ δ ∈ (S₁.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' componentRoots (famCharHom a) i,
            iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ)) ∧
        Nat.card B ≤ p ^ (2 + Module.finrank ℤ (Submodule.span ℤ
          (componentRoots (famCharHom a) i))) ∧
        2 * Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) ≤ τ.rank := by
  classical
  obtain ⟨K, instF, instFin, instChar, S, hq, hFr, ⟨fr⟩⟩ :=
    exists_uframe_untw hτ hp hp2 hmod hBN hin hfaith hBel hDB hDcard
  obtain ⟨S₁, hq₁, hΦ₁, hw, fr₁, hBT⟩ := exists_torus_uframe_untw hτ hp hp2 S fr hBel htor
  have hqq : S₁.D.q = 2 ^ f := hq₁.trans hq
  obtain ⟨Fr, hFr1, hFr2⟩ := hFr
  obtain ⟨w, hn⟩ := hw
  have hρ : ∀ γ, IsRoot τ γ → S₁.ρ γ = w • γ := fun γ hγ =>
    S₁.rho_eq_smul_of_frob (Fr := Fr) (fun c => by rw [hq₁]; exact hFr1 c)
      (by rw [hΦ₁]; exact hFr2) hn hγ
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite fr₁.BLang := Finite.of_equiv _ (MonoidHom.ofInjective fr₁.toLang_injective).toEquiv
  have hD₁B : fr₁.DLang D ≤ fr₁.BLang := fr₁.DLang_le_BLang
  have hpar : ∀ u : fr₁.DLang D, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hBT (hD₁B u.2)).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit τ (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hBT (hD₁B u.2)
  have hrange : (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u)) =
      ((fr₁.DLang D : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (fr₁.DLang D : Set (ModGL τ (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JLang J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u))) := by
    rw [hrange]
    exact fr₁.isComponentOf_JLang hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DLang D) a haT hap (fr₁.JLang J) hcomp
  rw [hqq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt hJ.2.2 (fr₁.nonempty_equiv_JLang hJG hJ.2.2).some hfield hF
  have hC := fr₁.le_DLang_of_commute hJG hJ.2.2.1 hcent
  have hcard := card_le_of_famChar S₁ fr₁.BLang (fr₁.DLang D) (fr₁.JLang J) hBT hBel₁.2 hD₁B a i
    hspan hC
  have horth : ∀ γ ∈ componentRoots (famCharHom a) i,
      ∀ δ ∈ (S₁.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' componentRoots (famCharHom a) i,
        iform γ δ = 0 ∧ ¬ IsRoot τ (γ + δ) := by
    obtain ⟨j, hj⟩ := exists_image_component_of_stable (famCharHom a)
      (fun γ hγ => rho_mem_kernelRoots_famChar S₁ a haT hγ) S₁.frob.iform_eq i
    have hij : i ≠ j := by
      rintro rfl
      exact image_ne_of_two_le_componentOrbitLength h2 hj
    intro γ hγ δ hδ
    rw [hj] at hδ
    refine ⟨iform_eq_zero_of_mem_componentRoots' hij hγ hδ, ?_⟩
    obtain ⟨hγk, hγi⟩ := hγ
    obtain ⟨hδk, hδi⟩ := hδ
    have := not_isRoot_of_mk_ne (χ := famCharHom a) (α := ⟨γ, hγk⟩) (β := ⟨δ, hδk⟩)
      (by rw [hγi, hδi]; exact hij) one_pos one_pos
    simpa using this
  refine ⟨K, instF, instFin, instChar, S₁, fr₁, hqq, hBT, ⟨w, hρ⟩, a, i, ha, hap, hspan, h2,
    isRootComponent_componentRoots i, horth, ?_, two_mul_finrank_le_of_orbit S₁ a haT i h2⟩
  calc Nat.card B = Nat.card fr₁.BLang := fr₁.card_BLang.symm
    _ ≤ Nat.card (fr₁.DLang D) *
        p ^ Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i)) := hcard
    _ = p ^ (2 + Module.finrank ℤ (Submodule.span ℤ (componentRoots (famCharHom a) i))) := by
      rw [fr₁.card_DLang hDB, hDcard, pow_add]

end Main

end CFSG.StandardType.TableCRes
