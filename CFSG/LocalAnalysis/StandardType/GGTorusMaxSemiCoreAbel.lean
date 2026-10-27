module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import CFSG.LocalAnalysis.StandardType.GGTorusMaxSemiWeights

public section

namespace CFSG.StandardType.FrameRoute

private theorem commutator_le_of_index_le_two {G : Type*} [Group G]
    {K : Subgroup G} (h0 : K.index ≠ 0) (h : K.index ≤ 2) : commutator G ≤ K := by
  rcases (by omega : K.index = 1 ∨ K.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]
    exact le_top
  · rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ∀ x y : G, x * y ∈ K ↔ (x ∈ K ↔ y ∈ K) :=
      fun x y => Subgroup.mul_mem_iff_of_index_two h2
    rw [commutatorElement_def, key, key, key, inv_mem_iff, inv_mem_iff]
    tauto

private lemma mulAut_congr_conjNormal_coe {F : Type} [Field F] {d : ℕ} {M : Type} [Group M]
    {E M0 : Subgroup M} [E.Normal] {ρ : ↥M0 →* GL (Fin d) F} (hρ : Function.Injective ρ)
    (x : ↥M0) (a : ↥((E.subgroupOf M0).map ρ)) :
    (((MulAut.congr (Subgroup.equivMapOfInjective (E.subgroupOf M0) ρ hρ))
        (MulAut.conjNormal x)) a : GL (Fin d) F) = ρ x * (a : GL (Fin d) F) * (ρ x)⁻¹ := by
  have h1 : ((MulAut.congr (Subgroup.equivMapOfInjective (E.subgroupOf M0) ρ hρ))
        (MulAut.conjNormal x)) a =
      (Subgroup.equivMapOfInjective (E.subgroupOf M0) ρ hρ)
        ((MulAut.conjNormal x)
          ((Subgroup.equivMapOfInjective (E.subgroupOf M0) ρ hρ).symm a)) := rfl
  rw [h1, Subgroup.coe_equivMapOfInjective_apply, MulAut.conjNormal_apply]
  have hb : ρ ↑(((Subgroup.equivMapOfInjective (E.subgroupOf M0) ρ hρ)).symm a)
      = (a : GL (Fin d) F) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply (E.subgroupOf M0) ρ hρ
      ((Subgroup.equivMapOfInjective (E.subgroupOf M0) ρ hρ).symm a),
      MulEquiv.apply_symm_apply]
  simp only [map_mul, map_inv, hb]

theorem tmSemi_core_abelian {F : Type} [Field F] [Finite F] [CharP F 2] (d : ℕ)
    {W : Type} [Group W] (hW1 : commutator W ≠ ⊥)
    (hW2 : ∀ n ≤ d, ∀ f : ↥(commutator W) →* Equiv.Perm (Fin n), f = 1)
    {M : Type} [Group M] [Finite M] (E M0 : Subgroup M) [E.Normal]
    (hEM0 : E ≤ M0) (hM0 : M0.index ≤ 2) (hEodd : Odd (Nat.card E))
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hcent : ∀ x : M, (∀ e ∈ E, x * e = e * x) → x ∈ E)
    (π : M →* W) (hπs : Function.Surjective π) (hπk : π.ker = E)
    (ρ : ↥M0 →* GL (Fin d) F) (hρ : Function.Injective ρ) :
    False := by
  let E' : Subgroup ↥M0 := E.subgroupOf M0
  have hE'norm : E'.Normal := inferInstance
  let C : Subgroup (GL (Fin d) F) := E'.map ρ
  have hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hab (a' : M) ha' (b' : M) hb')
  have hcardE' : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM0).toEquiv
  have hCodd : Odd (Nat.card C) := by
    show Odd (Nat.card (E'.map ρ))
    rw [Subgroup.card_map_of_injective hρ, hcardE']
    exact hEodd
  obtain ⟨Λ, hΛcard, _hΛeig, hΛsep, hΛstab⟩ := tmWt_weights d C hCab hCodd
  let eE : ↥E' ≃* ↥C := Subgroup.equivMapOfInjective E' ρ hρ
  let τ : ↥M0 →* MulAut ↥C :=
    (MulAut.congr eE).toMonoidHom.comp (MulAut.conjNormal (H := E'))
  have hτ : ∀ (x : ↥M0) (a : ↥C),
      ((τ x a : ↥C) : GL (Fin d) F) = ρ x * (a : GL (Fin d) F) * (ρ x)⁻¹ := by
    intro x a
    exact mulAut_congr_conjNormal_coe hρ x a
  have hτ_conj : ∀ (g : ↥M0) (b : ↥E'),
      (τ g) (eE b) = eE ⟨g * (b : ↥M0) * g⁻¹, hE'norm.conj_mem (b : ↥M0) b.2 g⟩ := by
    intro g b
    apply Subtype.ext
    simp only [eE]
    rw [hτ g (Subgroup.equivMapOfInjective E' ρ hρ b),
      Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_equivMapOfInjective_apply]
    simp only [map_mul, map_inv]
  let smulFn : ↥M0 → ↥Λ → ↥Λ := fun x χ =>
    ⟨χ.1.comp (τ x⁻¹).toMonoidHom,
      hΛstab (ρ x⁻¹) (τ x⁻¹) (fun a => hτ x⁻¹ a) χ.1 χ.2⟩
  have hsmulFn : ∀ (x : ↥M0) (χ : ↥Λ), (smulFn x χ).1 = χ.1.comp (τ x⁻¹).toMonoidHom :=
    fun _ _ => rfl
  have hsmulFn_one : ∀ χ : ↥Λ, smulFn 1 χ = χ := by
    intro χ
    apply Subtype.ext
    rw [hsmulFn, inv_one, map_one]
    ext a
    simp
  have hsmulFn_mul : ∀ (x y : ↥M0) (χ : ↥Λ), smulFn (x * y) χ = smulFn x (smulFn y χ) := by
    intro x y χ
    apply Subtype.ext
    rw [hsmulFn, hsmulFn, hsmulFn]
    ext a
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.mul_apply,
      mul_inv_rev, map_mul]
  let actFun : ↥M0 → Equiv.Perm ↥Λ := fun x =>
    { toFun := smulFn x
      invFun := smulFn x⁻¹
      left_inv := fun χ => by
        show smulFn x⁻¹ (smulFn x χ) = χ
        rw [← hsmulFn_mul, inv_mul_cancel, hsmulFn_one]
      right_inv := fun χ => by
        show smulFn x (smulFn x⁻¹ χ) = χ
        rw [← hsmulFn_mul, mul_inv_cancel, hsmulFn_one] }
  let act : ↥M0 →* Equiv.Perm ↥Λ :=
    { toFun := actFun
      map_one' := Equiv.ext (fun χ => by simpa [actFun] using hsmulFn_one χ)
      map_mul' := fun x y => Equiv.ext (fun χ => by simpa [actFun] using hsmulFn_mul x y χ) }
  have hact_apply : ∀ (x : ↥M0) (χ : ↥Λ), act x χ = smulFn x χ := fun _ _ => rfl
  have hτ1 : ∀ x ∈ E', τ x = 1 := by
    intro x hx
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [hτ x a]
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 a.2
    simp only [MulAut.one_apply]
    rw [← hba]
    have hxb : x * b * x⁻¹ = b := by
      have hcomm : (x : M) * (b : M) = (b : M) * (x : M) := hab (x : M) hx (b : M) hb
      apply Subtype.ext
      rw [show ((x * b * x⁻¹ : ↥M0) : M) = (x : M) * (b : M) * (x : M)⁻¹ from rfl,
        hcomm]
      group
    have := congrArg ρ hxb
    simpa only [map_mul, map_inv] using this
  have hact_le : E' ≤ act.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Equiv.ext
    intro χ
    apply Subtype.ext
    rw [hact_apply, hsmulFn, show τ x⁻¹ = 1 from hτ1 x⁻¹ (E'.inv_mem hx)]
    rfl
  have hker_le : act.ker ≤ E' := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    change (x : M) ∈ E
    apply hcent (x : M)
    intro e he
    have hfix : ∀ χ : ↥Λ, smulFn x χ = χ := by
      intro χ
      have h := congrArg (fun p : Equiv.Perm ↥Λ => p χ) hx
      rw [hact_apply] at h
      simpa using h
    have hfixχ : ∀ (χ : ↥Λ) (b : ↥E'),
        χ.1 (eE ⟨x⁻¹ * (b : ↥M0) * x, by simpa using hE'norm.conj_mem (b : ↥M0) b.2 x⁻¹⟩) = χ.1 (eE b) := by
      intro χ b
      have h := congrArg (fun χ : ↥Λ => χ.1 (eE b)) (hfix χ)
      have hxsmul : (smulFn x χ).1 (eE b) =
          χ.1 (eE ⟨x⁻¹ * (b : ↥M0) * x, by simpa using hE'norm.conj_mem (b : ↥M0) b.2 x⁻¹⟩) := by
        rw [hsmulFn, MonoidHom.comp_apply]
        congr 1
        simpa using hτ_conj x⁻¹ b
      rw [hxsmul] at h
      exact h
    let b0 : ↥E' := ⟨⟨e, hEM0 he⟩, he⟩
    let b1 : ↥E' := ⟨x * (b0 : ↥M0) * x⁻¹, hE'norm.conj_mem (b0 : ↥M0) b0.2 x⟩
    have hkey : ∀ χ ∈ Λ, (χ : ↥C →* (AlgebraicClosure F)ˣ)
        ((eE b1) * (eE b0)⁻¹) = 1 := by
      intro χ hχ
      have hb := hfixχ ⟨χ, hχ⟩ b1
      have hbb : (⟨x⁻¹ * (b1 : ↥M0) * x, by simpa using hE'norm.conj_mem (b1 : ↥M0) b1.2 x⁻¹⟩ : ↥E') = b0 := by
        apply Subtype.ext
        show x⁻¹ * (x * (b0 : ↥M0) * x⁻¹) * x = (b0 : ↥M0)
        group
      rw [hbb] at hb
      rw [map_mul, map_inv, hb]
      simp
    have hd1 : (eE b1) * (eE b0)⁻¹ = 1 := hΛsep _ hkey
    have hb1b0 : b1 = b0 := by
      have h := congrArg eE.symm hd1
      rw [map_mul, map_inv, map_one, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h
      rwa [mul_inv_eq_one] at h
    have hMe : (x : M) * e * (x : M)⁻¹ = e := by
      have h := congrArg (fun y : ↥E' => (y : M)) hb1b0
      simpa [b1, b0] using h
    have hcomm : (x : M) * e = e * (x : M) := by
      have h := congrArg (· * (x : M)) hMe
      simpa [mul_assoc] using h
    exact hcomm
  have hactker : act.ker = E' := le_antisymm hker_le hact_le
  have hHindex : (M0.map π).index ≤ 2 := by
    rw [Subgroup.index_map_eq (H := M0) (f := π) hπs (by rw [hπk]; exact hEM0)]
    exact hM0
  have hHindex0 : (M0.map π).index ≠ 0 := by
    rw [Subgroup.index_map_eq (H := M0) (f := π) hπs (by rw [hπk]; exact hEM0)]
    exact Subgroup.index_ne_zero_of_finite
  have hcommW : commutator W ≤ M0.map π := commutator_le_of_index_le_two hHindex0 hHindex
  let φ : ↥M0 →* W := π.comp M0.subtype
  have hφker : φ.ker = E' := by
    ext x
    rw [MonoidHom.mem_ker]
    change π (x : M) = 1 ↔ (x : M) ∈ E
    rw [← MonoidHom.mem_ker, hπk]
  have hφrange : φ.range = M0.map π := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := QuotientGroup.quotientKerEquivRange φ
  let iso : (↥M0 ⧸ φ.ker) ≃* ↥(M0.map π) :=
    e.trans (MulEquiv.subgroupCongr hφrange)
  have hHN : φ.ker ≤ act.ker := by rw [hφker, hactker]
  let actH : ↥(M0.map π) →* Equiv.Perm ↥Λ :=
    (QuotientGroup.lift φ.ker act hHN).comp iso.symm
  let incl : ↥(commutator W) →* ↥(M0.map π) := Subgroup.inclusion hcommW
  have hcardΛ : Nat.card ↥Λ = Λ.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  let P : Equiv.Perm ↥Λ ≃* Equiv.Perm (Fin Λ.card) :=
    (Finite.equivFinOfCardEq hcardΛ).permCongrHom
  let f : ↥(commutator W) →* Equiv.Perm (Fin Λ.card) :=
    P.toMonoidHom.comp (actH.comp incl)
  have hiso_mk : ∀ x : ↥M0, (iso (QuotientGroup.mk x) : W) = φ x := by
    intro x
    show (e (QuotientGroup.mk x) : W) = φ x
    rfl
  have hf_inj : ∀ w : ↥(commutator W), f w = 1 → w = 1 := by
    intro w hw
    have hP1 : actH (incl w) = 1 := by
      have h := congrArg (fun p : Equiv.Perm (Fin Λ.card) => P.symm p) hw
      simpa [f] using h
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective φ.ker (iso.symm (incl w))
    have hact1 : act x = 1 := by
      have h := hP1
      rw [show actH (incl w) = QuotientGroup.lift φ.ker act hHN (iso.symm (incl w)) from rfl,
        ← hx] at h
      simpa using h
    have hxE : x ∈ E' := by
      have h : x ∈ act.ker := by simpa [MonoidHom.mem_ker] using hact1
      rwa [hactker] at h
    have hxφ : φ x = 1 := by
      have h : x ∈ φ.ker := by rw [hφker]; exact hxE
      simpa [MonoidHom.mem_ker] using h
    have hx' : iso (QuotientGroup.mk x) = incl w := by
      have hxmk : QuotientGroup.mk x = iso.symm (incl w) := by simpa using hx
      rw [hxmk, MulEquiv.apply_symm_apply]
    have hco : (incl w : W) = 1 := by
      rw [← hx', hiso_mk, hxφ]
    have hw1 : incl w = 1 := Subtype.ext hco
    have hincl : incl w = incl 1 := by rw [hw1, map_one]
    exact Subgroup.inclusion_injective hcommW hincl
  have hf1 : f = 1 := hW2 Λ.card hΛcard f
  have hbot : commutator W = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have h : f ⟨w, hw⟩ = 1 := by rw [hf1]; rfl
    simpa using hf_inj ⟨w, hw⟩ h
  exact hW1 hbot

end CFSG.StandardType.FrameRoute

end
