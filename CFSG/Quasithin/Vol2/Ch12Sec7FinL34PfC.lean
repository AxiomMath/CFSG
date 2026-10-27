module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfA
public import CFSG.Quasithin.Vol2.Ch5Sec1L34TCInv
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.RankThree.PartOne.KFCL.L4Block
public import CFSG.Quasithin.Vol2.Ch5Sec1L34TCModel

public section

namespace CFSG.Quasithin.H13.L34Br

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter
open CFSG.Quasithin.H13.KGL34P CFSG.Quasithin.H13.TorusComm

section Model

variable {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 4)
include hk

theorem chiP_sq_of_nf_one {α : MulAut (projectiveSL 3 k)} {A : GL (Fin 3) k} {b : ZMod 2}
    (hnf : α = nf (frobeniusEquiv k 2) A 1 b)
    (hαU : ∀ u ∈ projUnitriangular 3 k, α u ∈ projUnitriangular 3 k) :
    ∀ u : projUpperTriangular 3 k, ∃ h : α u ∈ projUpperTriangular 3 k,
      chiP (⟨α u, h⟩ : projUpperTriangular 3 k) = chiP u ^ 2 := by
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  rcases zmod_two_cases b with rfl | rfl
  · have hα : α = LinearFlag.conjAut 3 k A * fieldAut 3 k (frobeniusEquiv k 2) := by
      rw [hnf]
      simp [nf, val_one_two]
    have hAU : ∀ u ∈ projUnitriangular 3 k,
        LinearFlag.conjAut 3 k A u ∈ projUnitriangular 3 k := by
      intro u hu
      have hff : ∀ v, fieldAut 3 k (frobeniusEquiv k 2) (fieldAut 3 k (frobeniusEquiv k 2) v)
          = v := fun v => by
        rw [← MulAut.mul_apply, fieldAut_sigma_mul_self hσ hk, MulAut.one_apply]
      have h1 : LinearFlag.conjAut 3 k A u =
          α (fieldAut 3 k (frobeniusEquiv k 2) u) := by
        rw [hα, MulAut.mul_apply, hff]
      rw [h1]
      exact hαU _ (fieldAut_mem_projUnitriangular _ hu)
    obtain ⟨x, g, hg, hdec⟩ := exists_decomp hAU
    intro u
    have h1 : α u = (LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g))
        (fieldAut 3 k (frobeniusEquiv k 2) u) := by
      rw [hα, MulAut.mul_apply, hdec]
    have hm := decomp_mem_projUpper x hg (fieldAut_mem_projUpper (frobeniusEquiv k 2) u.2)
    refine ⟨h1 ▸ hm, ?_⟩
    have e : (⟨α u, h1 ▸ hm⟩ : projUpperTriangular 3 k) = ⟨_, hm⟩ := Subtype.ext h1
    rw [e, chiP_decomp x hg ⟨_, fieldAut_mem_projUpper (frobeniusEquiv k 2) u.2⟩,
      chiP_fieldAut hσ]
  · have hα : α = LinearFlag.conjAut 3 k (A * w0GL⁻¹) * nf (frobeniusEquiv k 2) w0GL 1 1 := by
      rw [hnf]
      simp only [nf, val_one_two, pow_one, map_mul, map_inv]
      group
    have h0U : ∀ u ∈ projUnitriangular 3 k,
        (nf (frobeniusEquiv k 2) w0GL 1 1)⁻¹ u ∈ projUnitriangular 3 k := by
      intro u hu
      have hmap := map_projUnitriangular_eq (β := nf (frobeniusEquiv k 2) w0GL 1 1)
        (fun v hv => alpha0_mem_projUnitriangular hv)
      rw [← hmap] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      simpa using hv
    have hAU : ∀ u ∈ projUnitriangular 3 k,
        LinearFlag.conjAut 3 k (A * w0GL⁻¹) u ∈ projUnitriangular 3 k := by
      intro u hu
      have h1 : LinearFlag.conjAut 3 k (A * w0GL⁻¹) u =
          α ((nf (frobeniusEquiv k 2) w0GL 1 1)⁻¹ u) := by
        rw [hα, MulAut.mul_apply, MulAut.apply_inv_self]
      rw [h1]
      exact hαU _ (h0U u hu)
    obtain ⟨x, g, hg, hdec⟩ := exists_decomp hAU
    intro u
    have h1 : α u = (LinearFlag.conjAut 3 k (diagGL x) * MulAut.conj (proj 3 k g))
        (nf (frobeniusEquiv k 2) w0GL 1 1 u) := by
      rw [hα, MulAut.mul_apply, hdec]
    have hm := decomp_mem_projUpper x hg (alpha0_mem_projUpperTriangular (σ :=
      frobeniusEquiv k 2) u.2)
    refine ⟨h1 ▸ hm, ?_⟩
    have e : (⟨α u, h1 ▸ hm⟩ : projUpperTriangular 3 k) = ⟨_, hm⟩ := Subtype.ext h1
    rw [e, chiP_decomp x hg ⟨_, alpha0_mem_projUpperTriangular u.2⟩, chiP_alpha0 hσ]

theorem exists_not_mem_of_nf_one {α : MulAut (projectiveSL 3 k)} {A : GL (Fin 3) k}
    {b : ZMod 2} (hnf : α = nf (frobeniusEquiv k 2) A 1 b)
    (hαU : ∀ u ∈ projUnitriangular 3 k, α u ∈ projUnitriangular 3 k) :
    ∃ d ∈ Subgroup.normalizer (projUnitriangular 3 k : Set (projectiveSL 3 k)),
      α d * d⁻¹ ∉ projUnitriangular 3 k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ω, hω3, hω2⟩ := exists_primitive_cube_root hk
  have hb0 : proj 3 k (torusDiag ω hω3) ∈ projUpperTriangular 3 k :=
    ⟨_, torusDiag_mem_upper hω3, rfl⟩
  obtain ⟨h, hχ⟩ := chiP_sq_of_nf_one hk hnf hαU ⟨_, hb0⟩
  refine ⟨_, by rw [normalizer_projUnitriangular 2]; exact hb0, fun hmem => ?_⟩
  have hB : α (proj 3 k (torusDiag ω hω3)) * (proj 3 k (torusDiag ω hω3))⁻¹ ∈
      projUpperTriangular 3 k :=
    (projUpperTriangular 3 k).mul_mem h ((projUpperTriangular 3 k).inv_mem hb0)
  have h1 := (chiP_eq_one_iff hk ⟨_, hB⟩).2 hmem
  have e : (⟨_, hB⟩ : projUpperTriangular 3 k) =
      ⟨_, h⟩ * (⟨_, hb0⟩ : projUpperTriangular 3 k)⁻¹ := rfl
  rw [e, map_mul, map_inv, hχ, sq, mul_inv_cancel_right] at h1
  exact chiP_torusDiag_ne_one hω3 hω2 hb0 h1

theorem exists_psi :
    ∃ ψ : MulAut (projectiveSL 3 k) →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2),
      (∀ (A : GL (Fin 3) k) (a b : ZMod 2),
        ψ (nf (frobeniusEquiv k 2) A a b) = (Multiplicative.ofAdd a, Multiplicative.ofAdd b)) ∧
      ∀ α : MulAut (projectiveSL 3 k), α * α = 1 → ψ α = 1 →
        α ∈ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hk
  refine ⟨(SemidirectProduct.rightHom).comp Ψ, fun A a b => ?_, fun α hα hψ => ?_⟩
  · rw [MonoidHom.comp_apply, hΨ, SemidirectProduct.rightHom_eq_right]
  · obtain ⟨⟨A, a, b⟩, rfl⟩ := exists_nf hσ hk α
    rw [MonoidHom.comp_apply, hΨ, SemidirectProduct.rightHom_eq_right] at hψ
    simp only [Prod.mk_eq_one, ofAdd_eq_one] at hψ
    obtain ⟨rfl, rfl⟩ := hψ
    rw [nf_zero_zero] at hα ⊢
    rw [conjAut_mem_range_conj_iff hk]
    have h1 := congrArg Ψ hα
    rw [map_one, map_mul, ← nf_zero_zero (frobeniusEquiv k 2) A, hΨ] at h1
    have h2 := congrArg SemidirectProduct.left h1
    simp only [SemidirectProduct.mul_left, SemidirectProduct.one_left] at h2
    rw [inversionAction_apply] at h2
    simp only [add_zero, ↓reduceIte] at h2
    have h3 := units_pow_three hk (GeneralLinearGroup.det A)
    calc GeneralLinearGroup.det A = GeneralLinearGroup.det A ^ 3 *
        (GeneralLinearGroup.det A * GeneralLinearGroup.det A)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem isPSL_fixSub_of_graph
    {ψ : MulAut (projectiveSL 3 k) →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)}
    (hψ : ∀ (A : GL (Fin 3) k) (a b : ZMod 2),
      ψ (nf (frobeniusEquiv k 2) A a b) = (Multiplicative.ofAdd a, Multiplicative.ofAdd b))
    {α : MulAut (projectiveSL 3 k)} (hα : α * α = 1)
    (hψα : ψ α = (1, Multiplicative.ofAdd 1)) : IsPSL 2 2 2 ↥(fixSub α) := by
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  have hc : ∀ H : GL (Fin 3) k, ψ (LinearFlag.conjAut 3 k H) = 1 := fun H => by
    rw [← nf_zero_zero (frobeniusEquiv k 2) H, hψ]
    rfl
  have hconj : ∀ (H : GL (Fin 3) k) (β : MulAut (projectiveSL 3 k)),
      ψ (LinearFlag.conjAut 3 k H * β * (LinearFlag.conjAut 3 k H)⁻¹) = ψ β := fun H β => by
    rw [map_mul, map_mul, mul_comm (ψ _) (ψ β), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
  have hf : ψ (fieldAut 3 k (frobeniusEquiv k 2)) = (Multiplicative.ofAdd 1, 1) := by
    rw [← nf_one_zero (σ := frobeniusEquiv k 2), hψ]
    rfl
  have hd : ψ (dualAut 3 k) = (1, Multiplicative.ofAdd 1) := by
    rw [← nf_zero_one (σ := frobeniusEquiv k 2), hψ]
    rfl
  have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  rcases CFSG.RankThree.PartTwo.KFacts.L34.involution_cases_card hk hσ hα with
    ⟨x, rfl⟩ | ⟨⟨H, rfl⟩, -⟩ | ⟨⟨H, rfl⟩, -⟩ | ⟨⟨H, rfl⟩, -⟩
  · exfalso
    obtain ⟨g, rfl⟩ := proj_surjective 3 k x
    rw [← conjAut_toGL, hc] at hψα
    exact hne (congrArg Prod.snd hψα).symm
  · exfalso
    rw [hconj, hf] at hψα
    exact hne (congrArg Prod.fst hψα)
  · set c := LinearFlag.conjAut 3 k H with hc
    rw [show fixSub (c * dualAut 3 k * c⁻¹) = GL3TwoFixedModel.autFixed (c * dualAut 3 k * c⁻¹)
        from rfl, CFSG.RankThree.PartTwo.KFacts.L34.autFixed_conj]
    have h60 := CFSG.RankThree.PartTwo.KFacts.L34.card_autFixed_dualAut hk
    obtain ⟨e⟩ := CFSG.RankThree.PartTwo.KFacts.L34.nonempty_autFixed_dualAut_equiv hk
    have h4 : 4 ≤ Nat.card k := by rw [hk]
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) k) :=
      CFSG.RankThree.PartOne.KFCL.L4.sl2_isSimpleGroup h4
    have hs : IsSimpleGroup ↥(GL3TwoFixedModel.autFixed (dualAut 3 k)) :=
      MulEquiv.isSimpleGroup (e.trans
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k).symm)
    have hP := isPSL_two_two_two_of_simple h60
    exact isPSL_of_mulEquiv hP (Subgroup.equivMapOfInjective _ _ c.injective)
  · exfalso
    rw [hconj, CFSG.RankThree.PartTwo.KFacts.L34.betaAut, map_mul, hf, hd] at hψα
    exact hne (congrArg Prod.fst hψα)

end Model

theorem l34OutData_of {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2) {S₀ : Subgroup X}
    (hS₀ : QuasithinUnique.IsSylowTwoOf S₀ ⊤) : L34OutData X S₀ := by
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS₀
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨ψ, hψ, hinn⟩ := exists_psi hk
  set c := MulAut.congr e with hcdef
  have hcapp : ∀ (α : MulAut X) (y : projectiveSL 3 k), c α y = e (α (e.symm y)) :=
    fun _ _ => rfl
  have hcconj : ∀ x : X, c (MulAut.conj x) = MulAut.conj (e x) := fun x => by
    ext y
    rw [hcapp, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hψc : ∀ p : projectiveSL 3 k, ψ (MulAut.conj p) = 1 := fun p => by
    obtain ⟨g, rfl⟩ := proj_surjective 3 k p
    rw [← conjAut_toGL, ← nf_zero_zero (frobeniusEquiv k 2), hψ]
    rfl
  have hsq : ∀ α : MulAut X, α * α = 1 → c α * c α = 1 := fun α hα => by
    rw [← map_mul, hα, map_one]
  refine ⟨ψ.comp c.toMonoidHom, fun x => ?_, fun α hα hψα => ?_, fun α hα hψα => ?_,
    fun α hαS hψα => ?_⟩
  · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcconj, hψc]
  · obtain ⟨p, hp⟩ := hinn (c α) (hsq α hα) hψα
    refine ⟨e.symm p, c.injective ?_⟩
    rw [hcconj, MulEquiv.apply_symm_apply]
    exact hp.symm
  · have h := isPSL_fixSub_of_graph hk hψ (hsq α hα) hψα
    have hmap : (fixSub α).map e.toMonoidHom = fixSub (c α) := by
      ext y
      rw [Subgroup.mem_map_equiv, mem_fixSub, mem_fixSub, hcapp]
      constructor
      · intro hy
        rw [hy, MulEquiv.apply_symm_apply]
      · intro hy
        have := congrArg e.symm hy
        rwa [MulEquiv.symm_apply_apply] at this
    refine isPSL_of_mulEquiv h ?_
    exact (MulEquiv.subgroupCongr hmap.symm).trans
      (Subgroup.equivMapOfInjective _ _ e.injective).symm
  ·
    have hU : ∀ u ∈ projUnitriangular 3 k, c α u ∈ projUnitriangular 3 k := by
      intro u hu
      rw [← he] at hu ⊢
      obtain ⟨x, hx, rfl⟩ := hu
      refine ⟨α x, ?_, ?_⟩
      · rw [← hαS]
        exact ⟨x, hx, rfl⟩
      · rw [hcapp]
        simp
    obtain ⟨⟨A, a, b⟩, hnf⟩ := exists_nf hσ hk (c α)
    have ha : a = 1 := by
      have h1 : (ψ (c α)).1 = Multiplicative.ofAdd 1 := hψα
      rw [hnf, hψ] at h1
      exact Multiplicative.ofAdd.injective h1
    subst ha
    obtain ⟨d, hd, hdU⟩ := exists_not_mem_of_nf_one hk hnf hU
    refine ⟨e.symm d, ?_, fun hmem => hdU ?_⟩
    · have hN := Subgroup.map_equiv_normalizer_eq S₀ e
      rw [he] at hN
      rw [← hN] at hd
      obtain ⟨x, hx, rfl⟩ := hd
      simpa using hx
    · rw [← he]
      refine ⟨_, hmem, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hcapp]

end CFSG.Quasithin.H13.L34Br
