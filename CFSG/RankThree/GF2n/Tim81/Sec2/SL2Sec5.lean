module

public import CFSG.CGT.Timmesfeld75.L2Orbit
public import CFSG.CGT.Timmesfeld75.Sec3TwelveAlg
public import CFSG.RankThree.GF2n.Tim81.Sec2.NatSumRecog
public import CFSG.RankThree.GF2n.Tim81.Sec2.InvolutionModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped MatrixGroups
open Matrix
open CFSG.CGT.Timmesfeld75
open CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.Timmesfeld
open CFSG.Timmesfeld.RankOne
open CFSG.Timmesfeld.ARS.NaturalModule
open CFSG.Timmesfeld.Bridge.NatSum
open NatSumModel

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

private def conjAut (g : SL(2, F)) (θ : MulAut SL(2, F)) : MulAut SL(2, F) :=
  MulAut.conj g⁻¹ * θ * MulAut.conj g

private theorem conjAut_apply (g : SL(2, F)) (θ : MulAut SL(2, F)) (x : SL(2, F)) :
    conjAut g θ x = g⁻¹ * θ (g * x * g⁻¹) * g := by
  simp [conjAut, MulAut.conj_apply, mul_assoc]

private theorem conjAut_map_of_map (θ : MulAut SL(2, F)) (g : SL(2, F))
    {A U : Subgroup SL(2, F)} (hA : A = conjSubgroup g U) (hθ : A.map θ.toMonoidHom = A) :
    U.map (conjAut g θ).toMonoidHom = U := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    have hgy : g * y * g⁻¹ ∈ A := by
      rw [hA]
      exact conj_mem_conjSubgroup g hy
    have hθy : θ (g * y * g⁻¹) ∈ A :=
      (mem_iff_of_map_mulEquiv_eq θ hθ (g * y * g⁻¹)).2 hgy
    change conjAut g θ y ∈ U
    rw [conjAut_apply]
    exact mem_conjSubgroup.1 (hA ▸ hθy)
  · intro hz
    have hgz : g * z * g⁻¹ ∈ A := by
      rw [hA]
      exact conj_mem_conjSubgroup g hz
    have hgz' : g * z * g⁻¹ ∈ A.map θ.toMonoidHom := by
      rw [hθ]
      exact hgz
    obtain ⟨a, haA, haθ⟩ := Subgroup.mem_map.1 hgz'
    have ha : a ∈ conjSubgroup g U := hA ▸ haA
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 ha
    have hyeq' : g * y * g⁻¹ = a := by simpa [MulAut.conj_apply] using hyeq
    have haθ' : θ a = g * z * g⁻¹ := by simpa using haθ
    refine Subgroup.mem_map.2 ⟨y, hy, ?_⟩
    change conjAut g θ y = z
    rw [conjAut_apply]
    calc g⁻¹ * θ (g * y * g⁻¹) * g = g⁻¹ * θ a * g := by rw [hyeq']
      _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [haθ']
      _ = z := by group

private theorem conjAut_fixes_of_fixes (θ : MulAut SL(2, F)) (g : SL(2, F))
    {A U : Subgroup SL(2, F)} (hA : A = conjSubgroup g U)
    (hfix : ∀ a ∈ A, θ a = a) : ∀ u ∈ U, conjAut g θ u = u := by
  intro u hu
  have hgu : g * u * g⁻¹ ∈ A := by
    rw [hA]
    exact conj_mem_conjSubgroup g hu
  rw [conjAut_apply]
  rw [hfix _ hgu]
  group

private theorem conjAut_eq_one_iff (g : SL(2, F)) (θ : MulAut SL(2, F)) :
    conjAut g θ = 1 ↔ θ = 1 := by
  constructor
  · intro h
    have hginv : MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹ := map_inv _ g
    calc θ = MulAut.conj g * conjAut g θ * MulAut.conj g⁻¹ := by
          simp only [conjAut, hginv]
          group
      _ = 1 := by rw [h, hginv]; group
  · rintro rfl
    simp [conjAut]

private theorem conjAut_injective (g : SL(2, F)) :
    Function.Injective (conjAut g) := by
  intro θ₁ θ₂ h
  have h' : conjAut g (θ₁ * θ₂⁻¹) = 1 := by
    have hginv : MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹ := map_inv _ g
    rw [show conjAut g (θ₁ * θ₂⁻¹) = conjAut g θ₁ * (conjAut g θ₂)⁻¹ by
      simp only [conjAut, hginv]
      group]
    rw [h, mul_inv_cancel]
  exact mul_inv_eq_one.1 ((conjAut_eq_one_iff g (θ₁ * θ₂⁻¹)).1 h')

private theorem conjAut_mul_self (g : SL(2, F)) (θ : MulAut SL(2, F))
    (hθ : θ * θ = 1) : conjAut g θ * conjAut g θ = 1 := by
  have hginv : MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹ := map_inv _ g
  simp only [conjAut, hginv]
  calc (MulAut.conj g)⁻¹ * θ * MulAut.conj g * ((MulAut.conj g)⁻¹ * θ * MulAut.conj g)
      = (MulAut.conj g)⁻¹ * (θ * θ) * MulAut.conj g := by group
    _ = 1 := by rw [hθ]; group

private theorem conjAut_comm (g : SL(2, F)) (θ₁ θ₂ : MulAut SL(2, F))
    (hc : θ₁ * θ₂ = θ₂ * θ₁) : conjAut g θ₁ * conjAut g θ₂ = conjAut g θ₂ * conjAut g θ₁ := by
  have hginv : MulAut.conj g⁻¹ = (MulAut.conj g)⁻¹ := map_inv _ g
  simp only [conjAut, hginv]
  calc (MulAut.conj g)⁻¹ * θ₁ * MulAut.conj g * ((MulAut.conj g)⁻¹ * θ₂ * MulAut.conj g)
      = (MulAut.conj g)⁻¹ * (θ₁ * θ₂) * MulAut.conj g := by group
    _ = (MulAut.conj g)⁻¹ * (θ₂ * θ₁) * MulAut.conj g := by rw [hc]
    _ = (MulAut.conj g)⁻¹ * θ₂ * MulAut.conj g * ((MulAut.conj g)⁻¹ * θ₁ * MulAut.conj g) := by
          group

private theorem uElt_eq_utriElt (t : F) : uElt t = utriElt t := rfl

private theorem upperRootGroup_eq_utri : upperRootGroup F = utri F := by
  ext g
  change g ∈ (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.upperUnipotent
    (F := F)).range ↔ g ∈ utri F
  rw [mem_rootGroup_iff, mem_utri_iff]
  exact exists_congr fun t => by rw [uElt_eq_utriElt]

theorem exists_conj_utri_of_exp_two (A : Subgroup SL(2, F))
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F) :
    ∃ x : SL(2, F), A = conjSubgroup x (utri F) := by
  have hcard : Nat.card A = Nat.card F := by
    rw [hA, Nat.card_eq_fintype_card]
  obtain ⟨x, hx⟩ := eq_conj_rootGroup A hA2 hcard
  refine ⟨x, ?_⟩
  ext g
  rw [mem_conjSubgroup]
  rw [← upperRootGroup_eq_utri]
  exact hx g

namespace MulAut

theorem eq_one_or_eq_of_two_sylow {A A' : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F) (hA'2 : ∀ a ∈ A', a * a = 1)
    (hA' : Nat.card A' = Fintype.card F) (hne : A ≠ A') {θ₁ θ₂ : MulAut SL(2, F)}
    (h₁ : A.map θ₁.toMonoidHom = A) (h₁' : A'.map θ₁.toMonoidHom = A')
    (h₂ : A.map θ₂.toMonoidHom = A) (h₂' : A'.map θ₂.toMonoidHom = A')
    (hθ₁ : θ₁ * θ₁ = 1) (hθ₂ : θ₂ * θ₂ = 1) (hc : θ₁ * θ₂ = θ₂ * θ₁) :
    θ₁ = 1 ∨ θ₂ = 1 ∨ θ₁ = θ₂ := by
  obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
  obtain ⟨y, hAy⟩ := exists_conj_utri_of_exp_two A' hA'2 hA'
  have hneconj : conjSubgroup x (utri F) ≠ conjSubgroup y (utri F) := by
    intro h
    exact hne (hAx.trans (h.trans hAy.symm))
  obtain ⟨g, hgx, hgy⟩ := exists_conj_utri_ltri_of_ne hneconj
  have hAg : A = conjSubgroup g (utri F) := hAx.trans hgx
  have hAg' : A' = conjSubgroup g (ltri F) := hAy.trans hgy
  let Θ₁ := conjAut g θ₁
  let Θ₂ := conjAut g θ₂
  have hU₁ : (utri F).map Θ₁.toMonoidHom = utri F :=
    conjAut_map_of_map θ₁ g hAg h₁
  have hL₁ : (ltri F).map Θ₁.toMonoidHom = ltri F :=
    conjAut_map_of_map θ₁ g hAg' h₁'
  have hU₂ : (utri F).map Θ₂.toMonoidHom = utri F :=
    conjAut_map_of_map θ₂ g hAg h₂
  have hL₂ : (ltri F).map Θ₂.toMonoidHom = ltri F :=
    conjAut_map_of_map θ₂ g hAg' h₂'
  have hΘ₁ : ∀ x, Θ₁ (Θ₁ x) = x := by
    intro x
    have := congrArg (fun φ : MulAut SL(2, F) => φ x) (conjAut_mul_self g θ₁ hθ₁)
    simpa [Θ₁] using this
  have hΘ₂ : ∀ x, Θ₂ (Θ₂ x) = x := by
    intro x
    have := congrArg (fun φ : MulAut SL(2, F) => φ x) (conjAut_mul_self g θ₂ hθ₂)
    simpa [Θ₂] using this
  have hΘc : ∀ x, Θ₁ (Θ₂ x) = Θ₂ (Θ₁ x) := by
    intro x
    have := congrArg (fun φ : MulAut SL(2, F) => φ x) (conjAut_comm g θ₁ θ₂ hc)
    simpa using this
  have hres := eq_or_eq_one_of_commute_involutions Θ₁ Θ₂
    (mem_iff_of_map_mulEquiv_eq Θ₁ hU₁) (mem_iff_of_map_mulEquiv_eq Θ₁ hL₁)
    (mem_iff_of_map_mulEquiv_eq Θ₂ hU₂) (mem_iff_of_map_mulEquiv_eq Θ₂ hL₂)
    hΘ₁ hΘ₂ hΘc
  rcases hres with h1 | h2 | h12
  · left
    have hΘ : Θ₁ = 1 := MulEquiv.ext h1
    have hθ : θ₁ = 1 := (conjAut_eq_one_iff g θ₁).1 (by simpa [Θ₁] using hΘ)
    exact hθ
  · right; left
    have hΘ : Θ₂ = 1 := MulEquiv.ext h2
    exact (conjAut_eq_one_iff g θ₂).1 (by simpa [Θ₂] using hΘ)
  · right; right
    have hΘ : Θ₁ = Θ₂ := MulEquiv.ext h12
    exact conjAut_injective g (by simpa [Θ₁, Θ₂] using hΘ)

theorem eq_one_of_fix_sylow {A A' : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F) (hA'2 : ∀ a ∈ A', a * a = 1)
    (hA' : Nat.card A' = Fintype.card F) (hne : A ≠ A') {θ : MulAut SL(2, F)}
    (hθA : ∀ a ∈ A, θ a = a) (hθA' : A'.map θ.toMonoidHom = A') : θ = 1 := by
  obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
  obtain ⟨y, hAy⟩ := exists_conj_utri_of_exp_two A' hA'2 hA'
  have hneconj : conjSubgroup x (utri F) ≠ conjSubgroup y (utri F) := by
    intro h
    exact hne (hAx.trans (h.trans hAy.symm))
  obtain ⟨g, hgx, hgy⟩ := exists_conj_utri_ltri_of_ne hneconj
  have hAg : A = conjSubgroup g (utri F) := hAx.trans hgx
  have hAg' : A' = conjSubgroup g (ltri F) := hAy.trans hgy
  let Θ := conjAut g θ
  have hfixU : ∀ u ∈ utri F, Θ u = u := conjAut_fixes_of_fixes θ g hAg hθA
  have hU : (utri F).map Θ.toMonoidHom = utri F := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      change Θ u ∈ utri F
      rw [hfixU u hu]
      exact hu
    · intro hz
      exact Subgroup.mem_map.2 ⟨z, hz, hfixU z hz⟩
  have hL : (ltri F).map Θ.toMonoidHom = ltri F := conjAut_map_of_map θ g hAg' hθA'
  obtain ⟨c, σ, hc⟩ := exists_eq_torusElt_conj_sl2FieldAut_of_map_eq Θ hU hL
  have hfixs : ∀ s : F, (c : F) ^ 2 * σ s = s := by
    intro s
    have h1 := hc (utriElt s)
    rw [sl2FieldAut_utriElt, torusElt_mul_utriElt_mul_inv] at h1
    have h2 := hfixU (utriElt s) (utriElt_mem_utri s)
    exact utriElt_injective (h1.symm.trans h2)
  have hc2 : (c : F) ^ 2 = 1 := by simpa using hfixs 1
  have hc1 : c = 1 := Units.ext (CharTwo.sq_injective (by simpa using hc2))
  have hσ : σ = RingEquiv.refl F := by
    ext s
    have := hfixs s
    rw [hc1] at this
    simpa using this
  have hΘ : Θ = 1 := by
    apply MulEquiv.ext
    intro z
    rw [hc z, hc1, hσ, sl2FieldAut_refl, torusElt_one]
    simp
  exact (conjAut_eq_one_iff g θ).1 (by simpa [Θ] using hΘ)

end MulAut

section NatSum

variable {N : Type} [AddCommGroup N] [Module (ZMod 2) N]

private noncomputable def addEquivToLinear {k : ℕ} (φ : N ≃+ (Fin k → Fin 2 → F)) :
    N ≃ₗ[ZMod 2] (Fin k → Fin 2 → F) :=
  LinearEquiv.ofBijective (AddMonoidHom.toZModLinearMap 2 φ.toAddMonoidHom) φ.bijective

theorem map_fixedSub_eq_of_intertwines {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {σ : Representation (ZMod 2) SL(2, F) N}
    {τ : Representation (ZMod 2) SL(2, F) V} (e : N ≃ₗ[ZMod 2] V)
    (he : ∀ g n, e (σ g n) = τ g (e n)) (S : Subgroup SL(2, F)) :
    (fixedSub σ S).map e.toLinearMap = fixedSub τ S := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    change ∀ g ∈ S, τ g (e u) = e u
    intro g hg
    rw [← he]
    exact congrArg e (hu g hg)
  · intro hv
    refine ⟨e.symm v, ?_, by simp⟩
    change ∀ g ∈ S, σ g (e.symm v) = e.symm v
    intro g hg
    apply e.injective
    rw [he, e.apply_symm_apply]
    exact hv g hg

private theorem map_commSub_eq_of_intertwines {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {σ : Representation (ZMod 2) SL(2, F) N}
    {τ : Representation (ZMod 2) SL(2, F) V} (e : N ≃ₗ[ZMod 2] V)
    (he : ∀ g n, e (σ g n) = τ g (e n)) (S : Subgroup SL(2, F)) :
    (commSub σ S).map e.toLinearMap = commSub τ S := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    refine commSub_induction σ S (P := fun u => e u ∈ commSub τ S) ?_ ?_ ?_ hu
    · intro a ha u
      have h : e ((σ a - 1) u) = (τ a - 1) (e u) := by
        simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, he]
      rw [h]
      exact range_le_commSub ha ⟨e u, rfl⟩
    · simp
    · intro x y hx hy
      rw [map_add]
      exact (commSub τ S).add_mem hx hy
  · intro v hv
    have hv' : e.symm v ∈ commSub σ S := by
      refine commSub_induction τ S (P := fun v => e.symm v ∈ commSub σ S) ?_ ?_ ?_ hv
      · intro a ha u
        have h2 : e.symm ((τ a - 1) u) = (σ a - 1) (e.symm u) := by
          apply e.injective
          simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, he,
            e.apply_symm_apply]
        rw [h2]
        exact range_le_commSub ha ⟨e.symm u, rfl⟩
      · simp
      · intro x y hx hy
        rw [map_add]
        exact (commSub σ S).add_mem hx hy
    exact Submodule.mem_map.mpr ⟨e.symm v, hv', by simp⟩

theorem mem_fixedSub_utri_natSumRep_iff (k : ℕ) {v : Fin k → Fin 2 → F} :
    v ∈ fixedSub (natSumRep F k) (utri F) ↔ ∀ i, v i 1 = 0 := by
  rw [CFSG.RankThree.GF2n.Tim77.utri_eq_upperUnipotent, mem_fixedSub]
  constructor
  · intro hv i
    refine (forall_upperElt_mulVec_eq_iff (v i)).1 fun t => ?_
    have h := hv (upperElt F t) ((mem_upperUnipotent_iff F).2 ⟨t, rfl⟩)
    have h2 := congrFun h i
    simpa [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec'] using h2
  · intro hv u hu
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).1 hu
    ext i j
    rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec', upperElt_mulVec]
    fin_cases j <;> simp [hv i]

theorem ltri_eq_lowerUnipotent (F : Type) [Field F] : ltri F = lowerUnipotent F := by
  ext g
  rw [mem_ltri_iff, CFSG.Timmesfeld.RankOne.mem_lowerUnipotent_iff F]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, Subtype.ext (by simp [ltriElt, CFSG.Timmesfeld.RankOne.lowerElt])⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, Subtype.ext (by simp [ltriElt, CFSG.Timmesfeld.RankOne.lowerElt])⟩

private theorem mem_fixedSub_ltri_natSumRep_iff (k : ℕ) {v : Fin k → Fin 2 → F} :
    v ∈ fixedSub (natSumRep F k) (ltri F) ↔ ∀ i, v i 0 = 0 := by
  rw [ltri_eq_lowerUnipotent, mem_fixedSub]
  constructor
  · intro hv i
    refine (forall_lowerElt_mulVec_eq_iff (v i)).1 fun t => ?_
    have h := hv (lowerElt F t) ((mem_lowerUnipotent_iff F).2 ⟨t, rfl⟩)
    have h2 := congrFun h i
    simpa [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec'] using h2
  · intro hv u hu
    obtain ⟨t, rfl⟩ := (mem_lowerUnipotent_iff F).1 hu
    ext i j
    rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec', lowerElt_mulVec]
    fin_cases j <;> simp [hv i]

end NatSum

private theorem upperElt_eq_utriElt (t : F) : upperElt F t = utriElt t := rfl

private theorem fixedSub_zpowers_upperElt_eq (k : ℕ) {t : F} (ht : t ≠ 0) :
    fixedSub (natSumRep F k) (Subgroup.zpowers (upperElt F t)) =
      fixedSub (natSumRep F k) (utri F) := by
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mem_fixedSub_utri_natSumRep_iff]
    intro i
    have h := mem_fixedSub.1 hv _ (Subgroup.mem_zpowers (upperElt F t))
    have h2 := congrFun h i
    have h' : (upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ (v i) = v i := by
      simpa [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec'] using h2
    rw [upperElt_mulVec] at h'
    have h0 := congrFun h' 0
    simp only [Matrix.cons_val_zero, Matrix.head_cons] at h0
    exact (mul_eq_zero.mp (by linear_combination h0)).resolve_left ht
  · intro v hv
    rw [mem_fixedSub]
    intro g hg
    exact mem_fixedSub.1 hv g (Subgroup.zpowers_le.mpr (by
      rw [CFSG.RankThree.GF2n.Tim77.utri_eq_upperUnipotent]
      exact (mem_upperUnipotent_iff F).2 ⟨t, rfl⟩) hg)

private theorem commSub_zpowers_upperElt_eq (k : ℕ) {t : F} (ht : t ≠ 0) :
    commSub (natSumRep F k) (Subgroup.zpowers (upperElt F t)) =
      fixedSub (natSumRep F k) (utri F) := by
  rw [commSub_zpowers_eq_range (natSumRep F k) (upperElt_mul_self (K := F) t)]
  refine le_antisymm ?_ ?_
  · rintro v ⟨w, rfl⟩
    rw [mem_fixedSub_utri_natSumRep_iff]
    intro i
    have h : ((natSumRep F k (upperElt F t) - 1) w) i =
        ![t * (w i) 1, 0] := by
      rw [show ((natSumRep F k (upperElt F t) - 1) w) i =
          (upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ (w i) - w i by
        simp [LinearMap.sub_apply, Module.End.one_apply, natSumRep_apply, Pi.smul_apply,
          smul_eq_mulVec']]
      rw [upperElt_mulVec_sub]
    rw [h]
    simp
  · intro v hv
    have hv' : ∀ i, v i 1 = 0 := (mem_fixedSub_utri_natSumRep_iff k).1 hv
    let w : Fin k → Fin 2 → F := fun i => (v i 0 / t) • (Pi.single 1 1 : Fin 2 → F)
    refine LinearMap.mem_range.mpr ⟨w, ?_⟩
    ext i j
    have h : ((natSumRep F k (upperElt F t) - 1) w) i =
        ![t * (w i) 1, 0] := by
      rw [show ((natSumRep F k (upperElt F t) - 1) w) i =
          (upperElt F t : Matrix (Fin 2) (Fin 2) F) *ᵥ (w i) - w i by
        simp [LinearMap.sub_apply, Module.End.one_apply, natSumRep_apply, Pi.smul_apply,
          smul_eq_mulVec']]
      rw [upperElt_mulVec_sub]
    rw [h]
    fin_cases j <;> simp [w, hv' i, mul_div_cancel₀ (v i 0) ht]

private theorem fixedSub_utri_inf_fixedSub_ltri_eq_bot (k : ℕ) :
    fixedSub (natSumRep F k) (utri F) ⊓ fixedSub (natSumRep F k) (ltri F) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  have h1 := (mem_fixedSub_utri_natSumRep_iff k).1 hv.1
  have h2 := (mem_fixedSub_ltri_natSumRep_iff k).1 hv.2
  funext i j
  fin_cases j <;> simp [h1 i, h2 i]

private theorem fixedSub_utri_sup_fixedSub_ltri_eq_top (k : ℕ) :
    fixedSub (natSumRep F k) (utri F) ⊔ fixedSub (natSumRep F k) (ltri F) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  let u : Fin k → Fin 2 → F := fun i j => if j = 0 then v i 0 else 0
  let w : Fin k → Fin 2 → F := fun i j => if j = 0 then 0 else v i 1
  have hu : u ∈ fixedSub (natSumRep F k) (utri F) :=
    (mem_fixedSub_utri_natSumRep_iff k).2 fun i => by simp [u]
  have hw : w ∈ fixedSub (natSumRep F k) (ltri F) :=
    (mem_fixedSub_ltri_natSumRep_iff k).2 fun i => by simp [w]
  refine Submodule.mem_sup.2 ⟨u, hu, w, hw, ?_⟩
  funext i j
  fin_cases j <;> simp [u, w]

theorem IsNatSumModule.fixedSub_zpowers_eq {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) SL(2, F) N} (hσ : IsNatSumModule σ)
    {A : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F)
    {a : SL(2, F)} (ha : a ∈ A) (ha1 : a ≠ 1) :
    fixedSub σ (Subgroup.zpowers a) = fixedSub σ A ∧
      commSub σ (Subgroup.zpowers a) = fixedSub σ A := by
  obtain ⟨k, φ, hφ⟩ := hσ
  let e := natSumRep F k
  let φl : N ≃ₗ[ZMod 2] (Fin k → Fin 2 → F) := addEquivToLinear φ
  have hφ' : ∀ g n, φl (σ g n) = e g (φl n) := by
    intro g n
    funext i
    rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec']
    exact hφ g n i
  obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
  have hax : x⁻¹ * a * x ∈ utri F := by
    have hmem : a ∈ conjSubgroup x (utri F) := hAx ▸ ha
    exact mem_conjSubgroup.mp hmem
  obtain ⟨t, ht⟩ := mem_utri_iff.1 hax
  have ht0 : t ≠ 0 := by
    intro h0
    apply ha1
    rw [show a = x * (x⁻¹ * a * x) * x⁻¹ by group, ht, h0, utriElt_zero]
    group
  have hax' : x⁻¹ * a * x = upperElt F t := by rw [ht, upperElt_eq_utriElt]
  have haeq : a = x * upperElt F t * x⁻¹ := by
    rw [← hax']
    group
  have hAcoord : fixedSub e A = (fixedSub e (utri F)).map (e x) := by
    rw [hAx]
    simpa [conjSubgroup] using fixedSub_map_conj e x (utri F)
  have hazcoord : fixedSub e (Subgroup.zpowers a) = (fixedSub e (utri F)).map (e x) := by
    rw [haeq, fixedSub_zpowers_conj e x (upperElt F t),
      fixedSub_zpowers_upperElt_eq k ht0]
  have hcommcoord : commSub e (Subgroup.zpowers a) = (fixedSub e (utri F)).map (e x) := by
    rw [haeq, commSub_zpowers_conj e x (upperElt F t),
      commSub_zpowers_upperElt_eq k ht0]
  constructor
  · apply Submodule.map_injective_of_injective φl.injective
    rw [map_fixedSub_eq_of_intertwines φl hφ' A,
      map_fixedSub_eq_of_intertwines φl hφ' (Subgroup.zpowers a), hAcoord, hazcoord]
  · apply Submodule.map_injective_of_injective φl.injective
    rw [map_commSub_eq_of_intertwines φl hφ' (Subgroup.zpowers a),
      map_fixedSub_eq_of_intertwines φl hφ' A, hcommcoord, hAcoord]

theorem IsNatSumModule.fixedSub_inf_sup {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) SL(2, F) N} (hσ : IsNatSumModule σ)
    {A A' : Subgroup SL(2, F)} (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F)
    (hA'2 : ∀ a ∈ A', a * a = 1) (hA' : Nat.card A' = Fintype.card F) (hne : A ≠ A') :
    fixedSub σ A ⊓ fixedSub σ A' = ⊥ ∧ fixedSub σ A ⊔ fixedSub σ A' = ⊤ := by
  obtain ⟨k, φ, hφ⟩ := hσ
  let e := natSumRep F k
  let φl : N ≃ₗ[ZMod 2] (Fin k → Fin 2 → F) := addEquivToLinear φ
  have hφ' : ∀ g n, φl (σ g n) = e g (φl n) := by
    intro g n
    funext i
    rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec']
    exact hφ g n i
  obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
  obtain ⟨y, hAy⟩ := exists_conj_utri_of_exp_two A' hA'2 hA'
  have hneconj : conjSubgroup x (utri F) ≠ conjSubgroup y (utri F) := by
    intro h
    exact hne (hAx.trans (h.trans hAy.symm))
  obtain ⟨g, hgx, hgy⟩ := exists_conj_utri_ltri_of_ne hneconj
  have hAg : A = conjSubgroup g (utri F) := hAx.trans hgx
  have hAg' : A' = conjSubgroup g (ltri F) := hAy.trans hgy
  have hAcoord : fixedSub e A = (fixedSub e (utri F)).map (e g) := by
    rw [hAg]
    simpa [conjSubgroup] using fixedSub_map_conj e g (utri F)
  have hA'coord : fixedSub e A' = (fixedSub e (ltri F)).map (e g) := by
    rw [hAg']
    simpa [conjSubgroup] using fixedSub_map_conj e g (ltri F)
  have hinj : Function.Injective (e g) := fun u v huv => by
    have := congrArg (e g⁻¹) huv
    simpa using this
  have hinf : fixedSub e A ⊓ fixedSub e A' = ⊥ := by
    rw [hAcoord, hA'coord, ← Submodule.map_inf (e g) hinj,
      fixedSub_utri_inf_fixedSub_ltri_eq_bot, Submodule.map_bot]
  have hsup : fixedSub e A ⊔ fixedSub e A' = ⊤ := by
    rw [hAcoord, hA'coord, ← Submodule.map_sup,
      fixedSub_utri_sup_fixedSub_ltri_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr fun w => ⟨e g⁻¹ w, by simp⟩
  constructor
  · apply Submodule.map_injective_of_injective φl.injective
    rw [Submodule.map_inf φl.toLinearMap φl.injective,
      map_fixedSub_eq_of_intertwines φl hφ' A,
      map_fixedSub_eq_of_intertwines φl hφ' A', hinf, Submodule.map_bot]
  · apply Submodule.map_injective_of_injective φl.injective
    rw [Submodule.map_sup,
      map_fixedSub_eq_of_intertwines φl hφ' A,
      map_fixedSub_eq_of_intertwines φl hφ' A', hsup,
      Submodule.map_top, LinearMap.range_eq_top.mpr φl.surjective]

private theorem hquad_natSumRep (k : ℕ) :
    ∀ (s t : F) (v : Fin k → Fin 2 → F),
      natSumRep F k (upperElt F s) (natSumRep F k (upperElt F t) v - v) =
        natSumRep F k (upperElt F t) v - v := by
  intro s t v
  ext i j
  simp only [natSumRep_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mulVec', upperElt_mulVec]
  fin_cases j <;> simp

private theorem hfix_natSumRep (k : ℕ) :
    ∀ v : Fin k → Fin 2 → F, (∀ x : SL(2, F), x • v = v) → v = 0 := by
  intro v hv
  funext i j
  have h1 : v i 1 = 0 :=
    (forall_upperElt_mulVec_eq_iff (v i)).1 fun t => by
      have h := congrFun (hv (upperElt F t)) i
      simpa [Pi.smul_apply, smul_eq_mulVec'] using h
  have h0 : v i 0 = 0 :=
    (forall_lowerElt_mulVec_eq_iff (v i)).1 fun t => by
      have h := congrFun (hv (lowerElt F t)) i
      simpa [Pi.smul_apply, smul_eq_mulVec'] using h
  fin_cases j <;> simp [h0, h1]

private theorem hquad_of_isNatSumModule {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) SL(2, F) N} (hσ : IsNatSumModule σ) :
    ∀ (s t : F) (v : N),
      σ (upperElt F s) (σ (upperElt F t) v - v) = σ (upperElt F t) v - v := by
  obtain ⟨k, φ, hφ⟩ := hσ
  let e := natSumRep F k
  let φl : N ≃ₗ[ZMod 2] (Fin k → Fin 2 → F) := addEquivToLinear φ
  have hφ' : ∀ g n, φl (σ g n) = e g (φl n) := by
    intro g n
    funext i
    rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec']
    exact hφ g n i
  intro s t v
  apply φl.injective
  have h1 : φl (σ (upperElt F s) (σ (upperElt F t) v - v)) =
      e (upperElt F s) (e (upperElt F t) (φl v) - φl v) := by
    rw [hφ', map_sub, hφ']
  rw [h1, hquad_natSumRep k s t (φl v)]
  have h2 : φl (σ (upperElt F t) v - v) =
      e (upperElt F t) (φl v) - φl v := by
    rw [map_sub, hφ']
  rw [h2]

private theorem hfix_of_isNatSumModule {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) SL(2, F) N} (hσ : IsNatSumModule σ) :
    ∀ v : N, (∀ x : SL(2, F), σ x v = v) → v = 0 := by
  obtain ⟨k, φ, hφ⟩ := hσ
  let e := natSumRep F k
  let φl : N ≃ₗ[ZMod 2] (Fin k → Fin 2 → F) := addEquivToLinear φ
  have hφ' : ∀ g n, φl (σ g n) = e g (φl n) := by
    intro g n
    funext i
    rw [natSumRep_apply, Pi.smul_apply, smul_eq_mulVec']
    exact hφ g n i
  intro v hv
  apply φl.injective
  rw [map_zero]
  refine hfix_natSumRep k (φl v) fun x => ?_
  change natSumRep F k x (φl v) = φl v
  rw [← hφ' x v]
  exact congrArg φl (hv x)

private theorem mem_fixedUpper_iff_mem_fixedSub_utri {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] [DistribMulAction SL(2, F) N]
    (σ : Representation (ZMod 2) SL(2, F) N) (hσ : ∀ g v, σ g v = g • v) :
    ∀ v : N, v ∈ fixedUpper F N ↔ v ∈ fixedSub σ (utri F) := by
  intro v
  rw [mem_fixedUpper, mem_fixedSub, CFSG.RankThree.GF2n.Tim77.utri_eq_upperUnipotent]
  constructor
  · intro hv g hg
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff F).1 hg
    rw [hσ]
    exact hv t
  · intro hv t
    rw [← hσ]
    exact hv (upperElt F t) ((mem_upperUnipotent_iff F).2 ⟨t, rfl⟩)

private theorem natCard_eq_pow_mul_natCard_ker {T : Type} [AddCommGroup T] [Module F T]
    [Finite T] (ψ : T →ₗ[F] T) :
    Nat.card T = Nat.card F ^ Module.finrank F (LinearMap.range (ψ - 1)) *
      Nat.card (LinearMap.ker (ψ - 1)) := by
  haveI : Module.Finite F T := Module.Finite.of_finite
  have hT : Nat.card T = Nat.card F ^ Module.finrank F T :=
    Module.natCard_eq_pow_finrank (K := F) (V := T)
  have hK : Nat.card (LinearMap.ker (ψ - 1)) =
      Nat.card F ^ Module.finrank F (LinearMap.ker (ψ - 1)) :=
    Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker (ψ - 1))
  have hrank := LinearMap.finrank_range_add_finrank_ker (ψ - 1)
  rw [hT, ← hrank, pow_add, hK]

section FixedUpperKer

variable {N : Type} [AddCommGroup N] [Module (ZMod 2) N] [DistribMulAction SL(2, F) N]
variable [Module F (fixedUpper F N)]

private theorem natCard_ker_eq_inter (φT : fixedUpper F N →ₗ[F] fixedUpper F N)
    (φ : N →ₗ[ZMod 2] N) (hφT : ∀ u, (φT u : N) = φ u) :
    Nat.card (LinearMap.ker (φT - 1)) =
      Nat.card ↥(AddSubgroup.toZModSubmodule 2 (fixedUpper F N) ⊓
        LinearMap.ker (φ - LinearMap.id)) := by
  refine Nat.card_congr
    { toFun := fun u =>
        ⟨u.1.1, (AddSubgroup.mem_toZModSubmodule 2).2 ((mem_fixedUpper).1 u.1.2), ?_⟩
      invFun := fun v =>
        ⟨⟨v.1, (mem_fixedUpper).2 ((AddSubgroup.mem_toZModSubmodule 2).1 v.2.1)⟩, ?_⟩
      left_inv := fun u => rfl
      right_inv := fun v => rfl }
  · show (φ - (LinearMap.id : N →ₗ[ZMod 2] N)) (u.1.1 : N) = 0
    have hu : φT u.1 = u.1 := sub_eq_zero.mp u.2
    have hu' : φ (u.1.1 : N) = u.1.1 := by
      rw [← hφT u.1]
      exact congrArg Subtype.val hu
    change φ (u.1.1 : N) - u.1.1 = 0
    rw [hu', sub_self]
  · apply Subtype.ext
    have hmem : v.1 ∈ fixedUpper F N :=
      (mem_fixedUpper).2 ((AddSubgroup.mem_toZModSubmodule 2).1 v.2.1)
    change (φT ⟨v.1, hmem⟩ : N) - v.1 = 0
    have hv : φ (v.1 : N) = v.1 := by
      have h : (φ - (LinearMap.id : N →ₗ[ZMod 2] N)) (v.1 : N) = 0 := v.2.2
      have h' := sub_eq_zero.mp h
      simpa [LinearMap.sub_apply, LinearMap.id_apply] using h'
    rw [hφT, hv, sub_self]

end FixedUpperKer

private theorem exists_card_fixedSub_utri_eq {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) SL(2, F) N} (hSum : IsNatSumModule σ)
    (φ : N →ₗ[ZMod 2] N) (hφ : ∀ g n, φ (σ g n) = σ g (φ n)) :
    ∃ r : ℕ, Nat.card ↥(fixedSub σ (utri F)) =
      Fintype.card F ^ r * Nat.card ↥(fixedSub σ (utri F) ⊓
        LinearMap.ker (φ - LinearMap.id)) := by
  classical
  letI : DistribMulAction SL(2, F) N := DistribMulAction.compHom N σ
  have hquad : ∀ (s t : F) (v : N),
      upperElt F s • (upperElt F t • v - v) = upperElt F t • v - v :=
    hquad_of_isNatSumModule hSum
  have hfix : ∀ v : N, (∀ x : SL(2, F), x • v = v) → v = 0 :=
    hfix_of_isNatSumModule hSum
  obtain ⟨k, φc, hφc⟩ := hSum
  haveI : Finite N := Finite.of_injective φc φc.injective
  letI : Module F (fixedUpper F N) := moduleFixedUpper hquad hfix
  let T := fixedUpper F N
  have hφT_mem : ∀ u : T, φ u ∈ T := by
    intro u
    rw [mem_fixedUpper]
    intro t
    have hu : upperElt F t • (u : N) = u := (mem_fixedUpper).1 u.2 t
    change σ (upperElt F t) (φ u) = φ u
    rw [← hφ]
    exact congrArg φ hu
  let φT : T →ₗ[F] T :=
    { toFun := fun u => ⟨φ u, hφT_mem u⟩
      map_add' := by
        intro u v
        apply Subtype.ext
        exact map_add φ (u : N) v
      map_smul' := by
        intro c u
        apply Subtype.ext
        by_cases hc : c = 0
        · subst c
          simp
        · let a : Fˣ := Units.mk0 c hc
          have hu := natVec_eq_diagElt_smul hquad hfix u.2 a
          have hφu := natVec_eq_diagElt_smul hquad hfix (hφT_mem u) a
          change φ (natVec (u : N) (a : F)) = natVec (φ u) (a : F)
          rw [hu, hφu]
          change φ (σ (diagElt a) (u : N)) = σ (diagElt a) (φ u)
          rw [hφ] }
  let K := LinearMap.ker (φT - 1)
  refine ⟨Module.finrank F (LinearMap.range (φT - 1)), ?_⟩
  have hT_eq : Nat.card ↥(fixedSub σ (utri F)) = Nat.card T :=
    Nat.card_congr (Equiv.subtypeEquivRight
      (fun v => (mem_fixedUpper_iff_mem_fixedSub_utri σ (fun _ _ => rfl) v).symm))
  have hUpperSub : AddSubgroup.toZModSubmodule 2 T = fixedSub σ (utri F) := by
    ext v
    rw [AddSubgroup.mem_toZModSubmodule 2]
    exact mem_fixedUpper_iff_mem_fixedSub_utri σ (fun _ _ => rfl) v
  have hK_eq : Nat.card K = Nat.card ↥(fixedSub σ (utri F) ⊓
      LinearMap.ker (φ - LinearMap.id)) := by
    rw [← hUpperSub]
    exact natCard_ker_eq_inter φT φ (fun u => rfl)
  rw [hT_eq, ← hK_eq, natCard_eq_pow_mul_natCard_ker φT, Nat.card_eq_fintype_card]

private theorem conjEnd_commutes {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
    {σ : Representation (ZMod 2) SL(2, F) N} (φ : N →ₗ[ZMod 2] N)
    (hφ : ∀ g n, φ (σ g n) = σ g (φ n)) (x : SL(2, F)) :
    ∀ g n, ((σ x⁻¹).comp (φ.comp (σ x))) (σ g n) =
      σ g (((σ x⁻¹).comp (φ.comp (σ x))) n) := by
  intro g n
  change (σ x⁻¹ * φ * σ x * σ g) n = (σ g * (σ x⁻¹ * φ * σ x)) n
  have hcomm : φ * σ (x * g * x⁻¹) = σ (x * g * x⁻¹) * φ := by
    ext m
    exact hφ (x * g * x⁻¹) m
  calc
    (σ x⁻¹ * φ * σ x * σ g) n
        = (σ x⁻¹ * φ * (σ x * σ g)) n := by rw [mul_assoc]
    _ = (σ x⁻¹ * φ * σ (x * g)) n := by rw [map_mul]
    _ = (σ x⁻¹ * φ * (σ (x * g * x⁻¹) * σ x)) n := by
          rw [show σ (x * g) = σ (x * g * x⁻¹) * σ x by
            rw [← map_mul]
            congr 1
            group]
    _ = (σ x⁻¹ * (φ * σ (x * g * x⁻¹)) * σ x) n := by simp only [mul_assoc]
    _ = (σ x⁻¹ * (σ (x * g * x⁻¹) * φ) * σ x) n := by rw [hcomm]
    _ = (σ x⁻¹ * σ (x * g * x⁻¹) * φ * σ x) n := by simp only [mul_assoc]
    _ = (σ (x⁻¹ * (x * g * x⁻¹)) * φ * σ x) n := by rw [← map_mul]
    _ = (σ (g * x⁻¹) * φ * σ x) n := by
          congr 2
          group
    _ = (σ g * σ x⁻¹ * φ * σ x) n := by rw [map_mul]
    _ = (σ g * (σ x⁻¹ * φ * σ x)) n := by simp only [mul_assoc]

theorem IsNatSumModule.exists_card_fixedSub_eq {N : Type} [AddCommGroup N]
    [Module (ZMod 2) N] {σ : Representation (ZMod 2) SL(2, F) N}
    (hσ : IsNatSumModule σ) {A : Subgroup SL(2, F)}
    (hA2 : ∀ a ∈ A, a * a = 1) (hA : Nat.card A = Fintype.card F)
    (φ : N →ₗ[ZMod 2] N) (hφ : ∀ g n, φ (σ g n) = σ g (φ n)) :
    ∃ r : ℕ, Nat.card ↥(fixedSub σ A) =
      Fintype.card F ^ r * Nat.card ↥(fixedSub σ A ⊓
        LinearMap.ker (φ - LinearMap.id)) := by
  obtain ⟨x, hAx⟩ := exists_conj_utri_of_exp_two A hA2 hA
  let φ' : N →ₗ[ZMod 2] N := (σ x⁻¹).comp (φ.comp (σ x))
  have hφ' : ∀ g n, φ' (σ g n) = σ g (φ' n) := conjEnd_commutes φ hφ x
  obtain ⟨r, hr⟩ := exists_card_fixedSub_utri_eq hσ φ' hφ'
  have hinj : Function.Injective (σ x) := fun u v h => by
    have := congrArg (σ x⁻¹) h
    simpa using this
  have hfixA : fixedSub σ A = (fixedSub σ (utri F)).map (σ x) := by
    rw [hAx]
    simpa [conjSubgroup] using fixedSub_map_conj σ x (utri F)
  have hcardC : Nat.card ↥(fixedSub σ A) = Nat.card ↥(fixedSub σ (utri F)) := by
    rw [hfixA]
    exact (Nat.card_congr (Submodule.equivMapOfInjective (σ x) hinj
      (fixedSub σ (utri F))).toEquiv).symm
  have hKmap : (fixedSub σ (utri F) ⊓ LinearMap.ker (φ' - LinearMap.id)).map (σ x) =
      fixedSub σ A ⊓ LinearMap.ker (φ - LinearMap.id) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hfixA]
        exact Submodule.mem_map.2 ⟨u, hu.1, rfl⟩
      · show (φ - (LinearMap.id : N →ₗ[ZMod 2] N)) (σ x u) = 0
        have hu_ker : (φ' - (LinearMap.id : N →ₗ[ZMod 2] N)) u = 0 := hu.2
        have hu' : φ' u = u := by
          have h := sub_eq_zero.mp hu_ker
          simpa [LinearMap.sub_apply, LinearMap.id_apply] using h
        change φ (σ x u) - σ x u = 0
        have hcomp : φ (σ x u) = σ x (φ' u) := by
          rw [show φ' u = σ x⁻¹ (φ (σ x u)) from rfl]
          change (φ * σ x) u = (σ x * σ x⁻¹) ((φ * σ x) u)
          rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [hcomp, hu', sub_self]
    · intro hv
      have hvC : v ∈ (fixedSub σ (utri F)).map (σ x) := hfixA ▸ hv.1
      obtain ⟨u, huT, rfl⟩ := Submodule.mem_map.1 hvC
      refine Submodule.mem_map.2 ⟨u, ⟨huT, ?_⟩, rfl⟩
      show (φ' - (LinearMap.id : N →ₗ[ZMod 2] N)) u = 0
      have hφv : φ (σ x u) = σ x u := by
        have h : (φ - (LinearMap.id : N →ₗ[ZMod 2] N)) (σ x u) = 0 := hv.2
        have h' := sub_eq_zero.mp h
        simpa [LinearMap.sub_apply, LinearMap.id_apply] using h'
      change σ x⁻¹ (φ (σ x u)) - u = 0
      rw [hφv]
      simp
  have hcardK : Nat.card ↥(fixedSub σ (utri F) ⊓ LinearMap.ker (φ' - LinearMap.id)) =
      Nat.card ↥(fixedSub σ A ⊓ LinearMap.ker (φ - LinearMap.id)) := by
    rw [← hKmap]
    exact Nat.card_congr (Submodule.equivMapOfInjective (σ x) hinj
      (fixedSub σ (utri F) ⊓ LinearMap.ker (φ' - LinearMap.id))).toEquiv
  refine ⟨r, ?_⟩
  rw [hcardC, ← hcardK]
  exact hr

end CFSG.RankThree.GF2n.Tim81.Sec2
