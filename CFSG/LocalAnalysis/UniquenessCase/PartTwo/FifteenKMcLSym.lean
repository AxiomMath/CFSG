module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLDefs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import CFSG.Quasithin.Background.B5FinPerm
public import CFSG.Quasithin.Background.B4Models

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.ComponentClassification.OutcomeLocal

private theorem s15k_mclsym_permAct_allOnes (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    G6.permAct m σ (G6.allOnes m) = G6.allOnes m := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  rfl

private theorem s15k_mclsym_allOnes_not_mem_coreMod {m : ℕ} (hm : Odd m) :
    G6.allOnes m ∉ G6.coreMod m := by
  intro hmem
  rw [G6.mem_coreMod] at hmem
  have h1 : ∑ i : Fin m, Multiplicative.toAdd (G6.allOnes m) i = (m : ZMod 2) := by
    simp [G6.allOnes]
  rw [h1, ZMod.natCast_eq_zero_iff_even] at hmem
  exact (Nat.not_even_iff_odd.2 hm) hmem

private noncomputable def s15k_mclsym_coordEquiv (m : ℕ) :
    ↥(FFModel.symDn m).sec ≃* Multiplicative (sumZero m) where
  toFun x :=
    Multiplicative.ofAdd ⟨Multiplicative.toAdd (x.1 : G6.PermMod m), mem_sumZero.mpr x.2⟩
  invFun y :=
    ⟨Multiplicative.ofAdd (Multiplicative.toAdd y).1,
      G6.mem_coreMod.mpr (Multiplicative.toAdd y).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl
  map_mul' x y := rfl

private theorem s15k_mclsym_coordEquiv_apply (m : ℕ) (x : ↥(FFModel.symDn m).sec) :
    s15k_mclsym_coordEquiv m x =
      Multiplicative.ofAdd ⟨Multiplicative.toAdd (x.1 : G6.PermMod m), mem_sumZero.mpr x.2⟩ :=
  rfl

private theorem s15k_mclsym_permAct_mem_ker (m : ℕ) (γ : Equiv.Perm (Fin m))
    {x : G6.PermMod m}
    (hx : x ∈ Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m) :
    G6.permAct m γ x ∈ Subgroup.zpowers (G6.allOnes m) ⊓ G6.coreMod m := by
  rw [Subgroup.mem_inf] at hx ⊢
  refine ⟨?_, G6.permAct_mem_coreMod γ hx.2⟩
  rw [B5FinPerm.mem_zpowers_allOnes_iff] at hx ⊢
  rcases hx.1 with h1 | h1
  · exact Or.inl (by rw [h1, map_one])
  · exact Or.inr (by rw [h1, s15k_mclsym_permAct_allOnes])

theorem s15k_mcl_perm_hom {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (β : D.V ≃ₗ[ZMod 2] M)
    {m : ℕ} (τ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) M)
    (h : D.ρ.range.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      τ.range) :
    ∃ π : Equiv.Perm (Fin m) →* ↥J, Function.Surjective π ∧
      ∀ σ : Equiv.Perm (Fin m),
        LinearMap.GeneralLinearGroup.congrLinearEquiv β (D.ρ (π σ)) = τ σ := by
  let c : LinearMap.GeneralLinearGroup (ZMod 2) D.V →*
      LinearMap.GeneralLinearGroup (ZMod 2) M :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom
  let φ : ↥J →* LinearMap.GeneralLinearGroup (ZMod 2) M := c.comp D.ρ
  have hcinj : Function.Injective c :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv β).injective
  have hφinj : Function.Injective φ := fun a b hab => D.inj (hcinj hab)
  have hrange : φ.range = τ.range := by
    change (c.comp D.ρ).range = τ.range
    rw [MonoidHom.range_comp, h]
  let Φ : ↥J ≃* φ.range := MonoidHom.ofInjective hφinj
  let e : φ.range ≃* τ.range := MulEquiv.subgroupCongr hrange
  let π : Equiv.Perm (Fin m) →* ↥J :=
    Φ.symm.toMonoidHom.comp (e.symm.toMonoidHom.comp τ.rangeRestrict)
  refine ⟨π, ?_, ?_⟩
  · exact Φ.symm.surjective.comp (e.symm.surjective.comp (MonoidHom.rangeRestrict_surjective τ))
  · intro σ
    change φ (π σ) = τ σ
    have h2 : φ (π σ) = ((e.symm (τ.rangeRestrict σ) : φ.range) :
        LinearMap.GeneralLinearGroup (ZMod 2) M) :=
      MonoidHom.apply_ofInjective_symm hφinj _
    rw [h2, MulEquiv.subgroupCongr_symm_apply]
    rfl

private theorem s15k_mclsym_realizes {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} (D : McRep J R) {m : ℕ} {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    (β : D.V ≃ₗ[ZMod 2] N)
    (τ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) N)
    (h : D.ρ.range.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = τ.range)
    (q : ↥(FFModel.symDn m).sec →* Multiplicative N) (hq : Function.Surjective q)
    (hq_ker : ∀ x : ↥(FFModel.symDn m).sec,
      q x = 1 ↔ x.1 ∈ (FFModel.symDn m).ker)
    (hq_act : ∀ (σ : Equiv.Perm (Fin m)) (x : ↥(FFModel.symDn m).sec),
      q ⟨G6.permAct m σ x.1, G6.permAct_mem_coreMod σ x.2⟩ =
        Multiplicative.ofAdd ((τ σ : N →ₗ[ZMod 2] N)
          (Multiplicative.toAdd (q x)))) :
    SymmetricNatural J R ⊥ m := by
  obtain ⟨π, hπ, hπτ⟩ := s15k_mcl_perm_hom D β τ h
  refine ⟨π, hπ, bot_le, inf_le_right, (fun h u hu => D.stable (h : MulAut W) h.2 u hu), ?_,
    G6.permAct_mem_coreMod, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ x hx
    exact s15k_mclsym_permAct_mem_ker m γ hx
  · have hker : (FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec = q.ker := by
      apply Subgroup.ext
      intro x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact (hq_ker x).symm
    let qEquiv : ↥(FFModel.symDn m).sec ⧸
        (FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec ≃* Multiplicative N :=
      QuotientGroup.liftEquiv ((FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec)
        (φ := q) hq hker
    let φN : Multiplicative D.V ≃* Multiplicative N :=
      AddEquiv.toMultiplicative β.toAddEquiv
    let Ψ : ↥R →* ↥(FFModel.symDn m).sec ⧸
        (FFModel.symDn m).ker.subgroupOf (FFModel.symDn m).sec :=
      qEquiv.symm.toMonoidHom.comp (φN.toMonoidHom.comp D.e.toMonoidHom)
    have hΨ : ∀ y : ↥R, qEquiv (Ψ y) = φN (D.e y) := fun _ => by simp [Ψ]
    have hmk : ∀ y : ↥(FFModel.symDn m).sec, qEquiv (QuotientGroup.mk y) = q y :=
      fun _ => by simp [qEquiv]
    refine ⟨Ψ, ?_, ?_, ?_⟩
    · exact qEquiv.symm.surjective.comp (φN.surjective.comp D.e.surjective)
    · intro u
      rw [Subgroup.mem_bot]
      constructor
      · intro hu
        have h1 : φN (D.e u) = 1 := by
          have := congrArg qEquiv hu
          simpa [hΨ u] using this
        have h2 : D.e u = 1 := φN.injective (by rw [h1, map_one])
        have h3 : u = 1 := D.e.injective (by rw [h2, map_one])
        simpa using congrArg Subtype.val h3
      · intro hu
        have hu1 : u = 1 := Subtype.ext (by simpa using hu)
        rw [hu1]
        exact map_one Ψ
    · intro γ u x hu hx hux
      let γ' : Equiv.Perm (Fin m) := γ
      apply qEquiv.injective
      rw [hΨ, hmk]
      change φN (D.e ⟨((π γ' : ↥J) : MulAut W) (u : W), hu⟩) =
        q ⟨G6.permAct m γ' x.1, hx⟩
      have hqact : q ⟨G6.permAct m γ' x.1,
          G6.permAct_mem_coreMod γ' x.2⟩ =
          Multiplicative.ofAdd ((τ γ' : N →ₗ[ZMod 2] N)
            (Multiplicative.toAdd (q x))) := hq_act γ' x
      have hDu : D.e ⟨((π γ' : ↥J) : MulAut W) (u : W), hu⟩ =
          Multiplicative.ofAdd ((D.ρ (π γ') : D.V →ₗ[ZMod 2] D.V)
            (Multiplicative.toAdd (D.e u))) := D.hρ (π γ') u hu
      have h0 : q x = φN (D.e u) := by rw [← hmk x, ← hux, hΨ u]
      have hx' : q x = Multiplicative.ofAdd (β (Multiplicative.toAdd (D.e u))) := by
        rw [h0]
        simp [φN]
      have ht : Multiplicative.toAdd (q x) = β (Multiplicative.toAdd (D.e u)) := by
        rw [hx']
        rfl
      have hβτ : β ((D.ρ (π γ') : D.V →ₗ[ZMod 2] D.V)
            (Multiplicative.toAdd (D.e u))) =
          (τ γ' : N →ₗ[ZMod 2] N) (β (Multiplicative.toAdd (D.e u))) := by
        have h1 := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) N =>
            (f : N →ₗ[ZMod 2] N) (β (Multiplicative.toAdd (D.e u)))) (hπτ γ')
        simpa [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply] using h1
      rw [hDu, hqact]
      rw [show φN (Multiplicative.ofAdd ((D.ρ (π γ') : D.V →ₗ[ZMod 2] D.V)
            (Multiplicative.toAdd (D.e u)))) =
          Multiplicative.ofAdd (β ((D.ρ (π γ') : D.V →ₗ[ZMod 2] D.V)
            (Multiplicative.toAdd (D.e u)))) by simp [φN]]
      rw [hβτ, ← ht]

theorem s15k_mcl_sym_odd {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) (hev : Even (Module.finrank (ZMod 2) D.V))
    (h2 : 2 ≤ Module.finrank (ZMod 2) D.V)
    (β : D.V ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) D.V + 1))
    (h : D.ρ.range.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (sumZeroRep (Module.finrank (ZMod 2) D.V + 1)).range) :
    ∃ m : ℕ, 3 ≤ m ∧ SymmetricNatural J R ⊥ m := by
  let m := Module.finrank (ZMod 2) D.V + 1
  have hodd : Odd m := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k, by omega⟩
  refine ⟨m, by omega, ?_⟩
  let q : ↥(FFModel.symDn m).sec →* Multiplicative (sumZero m) :=
    (s15k_mclsym_coordEquiv m).toMonoidHom
  refine s15k_mclsym_realizes D β (sumZeroRep m) h q (s15k_mclsym_coordEquiv m).surjective ?_ ?_
  · intro x
    have hq1 : q x = 1 ↔ x = 1 := by
      constructor
      · intro hx
        exact (s15k_mclsym_coordEquiv m).injective hx
      · intro hx
        rw [hx, map_one]
    rw [hq1]
    constructor
    · intro hx
      rw [hx]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    · intro hx
      obtain ⟨hz, hc⟩ := Subgroup.mem_inf.mp hx
      have hz' : x.1 = 1 ∨ x.1 = G6.allOnes m := B5FinPerm.mem_zpowers_allOnes_iff.mp hz
      rcases hz' with hz' | hz'
      · exact Subtype.ext hz'
      · exact absurd (show G6.allOnes m ∈ G6.coreMod m from hz' ▸ hc)
          (s15k_mclsym_allOnes_not_mem_coreMod hodd)
  · intro σ x
    let v : G6.PermMod m := x.1
    have hv : v ∈ G6.coreMod m := x.2
    let y : ↥(FFModel.symDn m).sec :=
      ⟨G6.permAct m σ v, G6.permAct_mem_coreMod σ hv⟩
    have hkey : Multiplicative.toAdd (s15k_mclsym_coordEquiv m y) =
        sumZeroEquiv σ (Multiplicative.toAdd (s15k_mclsym_coordEquiv m x)) := by
      rw [s15k_mclsym_coordEquiv_apply, s15k_mclsym_coordEquiv_apply]
      apply Subtype.ext
      funext i
      change Multiplicative.toAdd (G6.permAct m σ x.1) i =
        Multiplicative.toAdd x.1 (σ⁻¹ i)
      exact G6.permAct_apply m σ x.1 i
    change q y = Multiplicative.ofAdd
      ((sumZeroRep m σ : sumZero m →ₗ[ZMod 2] sumZero m) (Multiplicative.toAdd (q x)))
    rw [show q y = s15k_mclsym_coordEquiv m y from rfl,
      show q x = s15k_mclsym_coordEquiv m x from rfl]
    apply Multiplicative.toAdd.injective
    rw [hkey]
    rfl

theorem s15k_mcl_sym_even {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R) (hev : Even (Module.finrank (ZMod 2) D.V))
    (h2 : 2 ≤ Module.finrank (ZMod 2) D.V)
    (β : D.V ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) D.V + 2) ⧸
      onesLine (Module.finrank (ZMod 2) D.V + 2))
    (h : D.ρ.range.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
      (heartRep (Module.finrank (ZMod 2) D.V + 2)).range) :
    ∃ m : ℕ, 3 ≤ m ∧ SymmetricNatural J R ⊥ m := by
  let m := Module.finrank (ZMod 2) D.V + 2
  refine ⟨m, by omega, ?_⟩
  let q : ↥(FFModel.symDn m).sec →* Multiplicative (sumZero m ⧸ onesLine m) :=
    { toFun := fun x => Multiplicative.ofAdd (Submodule.Quotient.mk (p := onesLine m)
        ⟨Multiplicative.toAdd (x.1 : G6.PermMod m), mem_sumZero.mpr x.2⟩)
      map_one' := rfl
      map_mul' := fun x y => rfl }
  refine s15k_mclsym_realizes D β (heartRep m) h q ?_ ?_ ?_
  · intro y
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective (p := onesLine m) (Multiplicative.toAdd y)
    let x0 : ↥(FFModel.symDn m).sec :=
      ⟨Multiplicative.ofAdd (v : Fin m → ZMod 2),
        G6.mem_coreMod.mpr (by
          change ∑ i, (v : Fin m → ZMod 2) i = 0
          exact v.2)⟩
    refine ⟨x0, ?_⟩
    exact Multiplicative.toAdd.injective (by
      change Submodule.Quotient.mk (p := onesLine m) v = Multiplicative.toAdd y
      exact hv)
  · intro x
    have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    constructor
    · intro hx
      have h1 : Submodule.Quotient.mk (p := onesLine m)
          ⟨Multiplicative.toAdd x.1, mem_sumZero.mpr x.2⟩ = 0 := by
        have h2 : Multiplicative.toAdd (q x) = 0 := by rw [hx]; rfl
        rwa [show Multiplicative.toAdd (q x) = Submodule.Quotient.mk (p := onesLine m)
            ⟨Multiplicative.toAdd x.1, mem_sumZero.mpr x.2⟩ from rfl] at h2
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨c, hc⟩ := mem_onesLine.mp h1
      have hc' : Multiplicative.toAdd x.1 = fun _ => c := hc
      refine Subgroup.mem_inf.mpr ⟨?_, x.2⟩
      rcases hc2 c with hc0 | hc1
      · exact B5FinPerm.mem_zpowers_allOnes_iff.mpr (Or.inl (by
          rw [← ofAdd_toAdd x.1, hc', hc0]; rfl))
      · exact B5FinPerm.mem_zpowers_allOnes_iff.mpr (Or.inr (by
          rw [← ofAdd_toAdd x.1, hc', hc1]; rfl))
    · intro hx
      obtain ⟨hz, hc⟩ := Subgroup.mem_inf.mp hx
      have hz' : x.1 = 1 ∨ x.1 = G6.allOnes m := B5FinPerm.mem_zpowers_allOnes_iff.mp hz
      have hconst : ∃ c : ZMod 2, Multiplicative.toAdd x.1 = fun _ => c := by
        rcases hz' with hz | hz
        · refine ⟨0, ?_⟩
          rw [hz]
          funext i
          rfl
        · refine ⟨1, ?_⟩
          rw [hz]
          funext i
          rfl
      obtain ⟨c, hc'⟩ := hconst
      have hmem : (⟨Multiplicative.toAdd x.1, mem_sumZero.mpr x.2⟩ : sumZero m) ∈ onesLine m :=
        mem_onesLine.mpr ⟨c, by
          ext i
          exact congrFun hc' i⟩
      rw [show q x = Multiplicative.ofAdd (Submodule.Quotient.mk (p := onesLine m)
          ⟨Multiplicative.toAdd x.1, mem_sumZero.mpr x.2⟩) from rfl,
        show Submodule.Quotient.mk (p := onesLine m)
          ⟨Multiplicative.toAdd x.1, mem_sumZero.mpr x.2⟩ = 0 from by
            rw [Submodule.Quotient.mk_eq_zero]; exact hmem]
      rfl
  · intro σ x
    let v : G6.PermMod m := x.1
    have hv : v ∈ G6.coreMod m := x.2
    let y : ↥(FFModel.symDn m).sec :=
      ⟨G6.permAct m σ v, G6.permAct_mem_coreMod σ hv⟩
    have hkey : Multiplicative.toAdd (q y) =
        (heartRep m σ : (sumZero m ⧸ onesLine m) →ₗ[ZMod 2] (sumZero m ⧸ onesLine m))
          (Multiplicative.toAdd (q x)) := by
      rw [show Multiplicative.toAdd (q x) = Submodule.Quotient.mk (p := onesLine m)
          ⟨Multiplicative.toAdd v, mem_sumZero.mpr hv⟩ from rfl]
      rw [show Multiplicative.toAdd (q y) = Submodule.Quotient.mk (p := onesLine m)
          ⟨Multiplicative.toAdd (G6.permAct m σ v),
            mem_sumZero.mpr (G6.permAct_mem_coreMod σ hv)⟩ from rfl]
      rw [heartRep_apply_mk]
      apply congrArg (Submodule.Quotient.mk (p := onesLine m))
      apply Subtype.ext
      funext i
      simp only [G6.permAct_apply, coe_sumZeroEquiv, permCoord_apply]
    apply Multiplicative.toAdd.injective
    exact hkey

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
