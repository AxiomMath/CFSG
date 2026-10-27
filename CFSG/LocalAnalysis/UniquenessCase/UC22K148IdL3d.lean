module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceIrreducibleModulesFlag
public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.Open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open Module CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
open scoped Matrix

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem statedSL_three_zmod_two_eq_top : StatedSL 3 (ZMod 2) = ⊤ := by
  refine eq_top_iff.2 fun A _ => Subgroup.subset_closure ?_
  show (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1
  have hu : IsUnit (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
  rcases zmod_two_eq_zero_or_one (A : Matrix (Fin 3) (Fin 3) (ZMod 2)).det with h | h
  · rw [h] at hu
    exact absurd hu not_isUnit_zero
  · exact h

theorem eq_zero_of_forall_apply_eq {w : Fin 3 → ZMod 2}
    (h : ∀ g : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), g w = w) : w = 0 := by
  by_contra hw
  obtain ⟨w', hw'⟩ := exists_not_mem_span_singleton (Module.finrank_fin_fun (ZMod 2)) w
  have hw'0 : w' ≠ 0 := fun h0 => hw' (h0 ▸ Submodule.zero_mem _)
  obtain ⟨g, hg⟩ := exists_linearEquiv_apply_eq (Module.finrank_fin_fun (ZMod 2)) hw hw'0
  exact hw' (by rw [← hg, h g]; exact Submodule.mem_span_singleton_self w)

theorem eq_zero_of_forall_dualRep_eq {f : Module.Dual (ZMod 2) (Fin 3 → ZMod 2)}
    (h : ∀ g : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), dualRep (Fin 3 → ZMod 2) g f = f) :
    f = 0 := by
  by_contra hf
  have hd : finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 3 := by
    rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  obtain ⟨f', hf'⟩ := exists_not_mem_span_singleton hd f
  have hf'0 : f' ≠ 0 := fun h0 => hf' (h0 ▸ Submodule.zero_mem _)
  obtain ⟨g, hg⟩ := exists_dualRep_eq (Module.finrank_fin_fun (ZMod 2)) hf hf'0
  exact hf' (by rw [← hg, h g]; exact Submodule.mem_span_singleton_self f)

theorem natL3_of_linear {L : Subgroup G} {A B : Submodule (ZMod 2) V} (hA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A)
    (hB : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L B) (hBA : B ≤ A) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 3) (θ : ↥L ≃* (W ≃ₗ[ZMod 2] W))
    (φ : V →ₗ[ZMod 2] W) (h0 : ∀ x ∈ B, φ x = 0) (hker : ∀ x ∈ A, φ x = 0 → x ∈ B)
    (hsurj : ∀ w, ∃ x ∈ A, φ x = w) (hequi : ∀ (h : ↥L) (x : V), x ∈ A → φ (ρ h x) = θ h (φ x)) :
    NatL3 ρ L A B := by
  classical
  let β : Module.Basis (Fin 3) (ZMod 2) W := Module.finBasisOfFinrankEq (ZMod 2) W hW
  have hbij : Function.Bijective (FixedCodim.toGL β) :=
    (FixedCodim.toGL_injective β).bijective_of_nat_card_le
      (by rw [FixedCodim.card_GL3, natCard_linearEquiv hW])
  let eSL : GL (Fin 3) (ZMod 2) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr statedSL_three_zmod_two_eq_top.symm)
  let φG : ↥L ≃* ↥(StatedSL 3 (ZMod 2)) := θ.trans ((MulEquiv.ofBijective _ hbij).trans eSL)
  refine ⟨hA, hB, hBA, φG, (β.equivFun.toLinearMap ∘ₗ φ).toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro x hx
    show β.equivFun (φ x) = 0
    rw [h0 x hx, map_zero]
  · intro x hx h
    have h1 : β.equivFun (φ x) = 0 := h
    exact hker x hx ((LinearEquiv.map_eq_zero_iff _).1 h1)
  · intro y
    obtain ⟨x, hx, hxy⟩ := hsurj (β.equivFun.symm y)
    exact ⟨x, hx, by show β.equivFun (φ x) = y; rw [hxy, LinearEquiv.apply_symm_apply]⟩
  · intro h x hx
    show β.equivFun (φ (ρ h x)) = _ *ᵥ β.equivFun (φ x)
    rw [hequi h x hx, FixedCodim.equivFun_apply_toGL]
    rfl

variable {L : Subgroup G} {U : Submodule (ZMod 2) V}
  {κ : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* ↥L}
  {ρ₁ : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ↥U}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {eW : ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) ≃* (W ≃ₗ[ZMod 2] W)}

theorem natL3_of_surjective (hUL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U)
    (hρ₁ : ∀ g (u : ↥U), ((ρ₁ g u : ↥U) : V) = ρ (κ g : G) u) (hW : finrank (ZMod 2) W = 3)
    {φ : ↥U →ₗ[ZMod 2] W} (hφ : ∀ g u, φ (ρ₁ g u) = eW g (φ u)) (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = Representation.invariants ρ₁) :
    NatL3 ρ L U (U ⊓ fixSub ρ L) := by
  classical
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype _)
  have hru : ∀ (u : V) (hu : u ∈ U), r u = ⟨u, hu⟩ := fun u hu => LinearMap.congr_fun hr ⟨u, hu⟩
  have hfix : ∀ (u : V) (hu : u ∈ U), φ ⟨u, hu⟩ = 0 ↔ u ∈ fixSub ρ L := by
    intro u hu
    rw [← LinearMap.mem_ker, hker, Representation.mem_invariants]
    constructor
    · intro h l hl
      have h1 := congrArg Subtype.val (h (κ.symm ⟨l, hl⟩))
      rw [hρ₁, MulEquiv.apply_symm_apply] at h1
      exact h1
    · intro h g
      exact Subtype.ext (by rw [hρ₁]; exact h _ (κ g).2)
  refine natL3_of_linear hUL (fun l hl z hz => by rw [hz.2 l hl]; exact hz) inf_le_left hW
    (κ.symm.trans eW) (φ ∘ₗ r) ?_ ?_ ?_ ?_
  · intro x hx
    show φ (r x) = 0
    rw [hru x hx.1]
    exact (hfix x hx.1).2 hx.2
  · intro x hx h
    have h1 : φ (r x) = 0 := h
    rw [hru x hx] at h1
    exact ⟨hx, (hfix x hx).1 h1⟩
  · intro w
    obtain ⟨u, rfl⟩ := hsurj w
    exact ⟨u, u.2, by show φ (r u) = φ u; rw [hru u u.2]⟩
  · intro h x hx
    have hhx : ρ h x ∈ U := hUL h h.2 x hx
    have h1 : (⟨ρ h x, hhx⟩ : ↥U) = ρ₁ (κ.symm h) ⟨x, hx⟩ :=
      Subtype.ext (by rw [hρ₁, MulEquiv.apply_symm_apply])
    show φ (r (ρ h x)) = eW (κ.symm h) (φ (r x))
    rw [hru _ hhx, hru x hx, h1, hφ]

theorem natL3_bot_of_section (hρ₁ : ∀ g (u : ↥U), ((ρ₁ g u : ↥U) : V) = ρ (κ g : G) u)
    (hW : finrank (ZMod 2) W = 3) {ι : W →ₗ[ZMod 2] ↥U} {π : ↥U →ₗ[ZMod 2] W}
    (hπι : ∀ w, π (ι w) = w) (hι : ∀ g w, ι (eW g w) = ρ₁ g (ι w)) :
    NatL3 ρ L (LinearMap.range (U.subtype ∘ₗ ι)) ⊥ := by
  classical
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective U.subtype (Submodule.ker_subtype _)
  have hru : ∀ u : ↥U, r u = u := fun u => LinearMap.congr_fun hr u
  have hact : ∀ (h : ↥L) (w : W), ρ h ((ι w : ↥U) : V) = ((ι (eW (κ.symm h) w) : ↥U) : V) := by
    intro h w
    rw [hι, hρ₁, MulEquiv.apply_symm_apply]
  refine natL3_of_linear ?_ (fun l _ z hz => by
      rw [(Submodule.mem_bot _).1 hz, map_zero]; exact Submodule.zero_mem _)
    bot_le hW (κ.symm.trans eW) (π ∘ₗ r) ?_ ?_ ?_ ?_
  · rintro l hl _ ⟨w, rfl⟩
    exact ⟨eW (κ.symm ⟨l, hl⟩) w, (hact ⟨l, hl⟩ w).symm⟩
  · intro x hx
    rw [(Submodule.mem_bot _).1 hx, map_zero]
  · rintro _ ⟨w, rfl⟩ h
    have h1 : π (r ((ι w : ↥U) : V)) = 0 := h
    rw [hru, hπι] at h1
    rw [Submodule.mem_bot]
    show ((ι w : ↥U) : V) = 0
    rw [h1, map_zero, Submodule.coe_zero]
  · intro w
    exact ⟨((ι w : ↥U) : V), ⟨w, rfl⟩, by show π (r ((ι w : ↥U) : V)) = w; rw [hru, hπι]⟩
  · rintro h _ ⟨w, rfl⟩
    show π (r (ρ h ((ι w : ↥U) : V))) = eW (κ.symm h) (π (r ((ι w : ↥U) : V)))
    rw [hact, hru, hru, hπι, hπι]

theorem secSum_of_equiv (hρ₁ : ∀ g (u : ↥U), ((ρ₁ g u : ↥U) : V) = ρ (κ g : G) u)
    (hW : finrank (ZMod 2) W = 3)
    {σ : Representation (ZMod 2) ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) W}
    (hσ : ∀ g w, σ g w = eW g w) (hσ0 : ∀ w, (∀ g, eW g w = w) → w = 0) (Φ : ρ₁.Equiv (σ.prod σ)) :
    U ⊓ fixSub ρ L = ⊥ ∧ SecSum (fun A B => NatL3 ρ L A B) 2 U ⊥ := by
  classical
  set e := Φ.toLinearEquiv with he
  have hΦ : ∀ g u, e (ρ₁ g u) = (eW g (e u).1, eW g (e u).2) := fun g u => by
    have h1 := LinearMap.congr_fun (Φ.toIntertwiningMap.isIntertwining' g) u
    have h2 : e (ρ₁ g u) = (σ g (e u).1, σ g (e u).2) := h1
    rw [h2, hσ, hσ]
  have hΦs : ∀ g p, e.symm (eW g p.1, eW g p.2) = ρ₁ g (e.symm p) := fun g p => by
    apply e.injective
    rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hval : ∀ u : ↥U, (u : V) = ((e.symm ((e u).1, 0) : ↥U) : V) + ((e.symm (0, (e u).2) : ↥U) : V) := by
    intro u
    rw [← Submodule.coe_add, ← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta,
      LinearEquiv.symm_apply_apply]
  refine ⟨?_, ![LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ LinearMap.inl (ZMod 2) W W)),
    LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ LinearMap.inr (ZMod 2) W W))], ?_, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huU, hufix⟩ := Submodule.mem_inf.1 hu
    have hinv : ∀ g, ρ₁ g ⟨u, huU⟩ = ⟨u, huU⟩ := fun g => Subtype.ext (by rw [hρ₁]; exact hufix _ (κ g).2)
    have h1 : ∀ g, eW g (e ⟨u, huU⟩).1 = (e ⟨u, huU⟩).1 ∧ eW g (e ⟨u, huU⟩).2 = (e ⟨u, huU⟩).2 := by
      intro g
      have h2 := hΦ g ⟨u, huU⟩
      rw [hinv] at h2
      exact ⟨(congrArg Prod.fst h2).symm, (congrArg Prod.snd h2).symm⟩
    have h3 : e ⟨u, huU⟩ = 0 :=
      Prod.ext (hσ0 _ fun g => (h1 g).1) (hσ0 _ fun g => (h1 g).2)
    rw [Submodule.mem_bot]
    have h4 : (⟨u, huU⟩ : ↥U) = 0 := (LinearEquiv.map_eq_zero_iff e).1 h3
    exact congrArg Subtype.val h4
  · intro i
    refine ⟨bot_le, ?_, ?_⟩
    · fin_cases i <;> (rintro _ ⟨w, rfl⟩; exact Submodule.coe_mem _)
    · fin_cases i
      · exact natL3_bot_of_section hρ₁ hW (π := LinearMap.fst (ZMod 2) W W ∘ₗ e.toLinearMap)
          (fun w => by simp) (fun g w => by
            show e.symm (eW g w, 0) = ρ₁ g (e.symm (w, 0))
            rw [← hΦs g (w, 0), map_zero])
      · exact natL3_bot_of_section hρ₁ hW (π := LinearMap.snd (ZMod 2) W W ∘ₗ e.toLinearMap)
          (fun w => by simp) (fun g w => by
            show e.symm (0, eW g w) = ρ₁ g (e.symm (0, w))
            rw [← hΦs g (0, w), map_zero])
  ·
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i <;> (rintro _ ⟨w, rfl⟩; exact Submodule.coe_mem _)
    · intro u hu
      have h1 : u = ((e.symm ((e ⟨u, hu⟩).1, 0) : ↥U) : V) + ((e.symm (0, (e ⟨u, hu⟩).2) : ↥U) : V) :=
        hval ⟨u, hu⟩
      rw [h1]
      exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem 0 ⟨(e ⟨u, hu⟩).1, rfl⟩)
        (Submodule.mem_iSup_of_mem 1 ⟨(e ⟨u, hu⟩).2, rfl⟩)
  ·
    have hdisj : ∀ (w w' : W), ((e.symm (w, 0) : ↥U) : V) = ((e.symm (0, w') : ↥U) : V) →
        ((e.symm (w, 0) : ↥U) : V) = 0 := by
      intro w w' h
      have h1 : e.symm (w, 0) = e.symm (0, w') := Subtype.ext h
      have h2 : ((w, 0) : W × W) = (0, w') := e.symm.injective h1
      have h3 : w = 0 := congrArg Prod.fst h2
      rw [h3, Prod.mk_zero_zero, map_zero, Submodule.coe_zero]
    intro i
    fin_cases i
    · rintro x ⟨⟨w, rfl⟩, hx⟩
      have hle : (⨆ j ∈ {j : Fin 2 | j ≠ 0}, ![LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ
          LinearMap.inl (ZMod 2) W W)), LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ
          LinearMap.inr (ZMod 2) W W))] j) ≤
          LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ LinearMap.inr (ZMod 2) W W)) := by
        refine iSup₂_le fun j hj => ?_
        fin_cases j
        · exact absurd rfl hj
        · exact le_rfl
      obtain ⟨w', hw'⟩ := hle hx
      rw [Submodule.mem_bot]
      exact hdisj w w' hw'.symm
    · rintro x ⟨⟨w', rfl⟩, hx⟩
      have hle : (⨆ j ∈ {j : Fin 2 | j ≠ 1}, ![LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ
          LinearMap.inl (ZMod 2) W W)), LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ
          LinearMap.inr (ZMod 2) W W))] j) ≤
          LinearMap.range (U.subtype ∘ₗ (e.symm.toLinearMap ∘ₗ LinearMap.inl (ZMod 2) W W)) := by
        refine iSup₂_le fun j hj => ?_
        fin_cases j
        · exact le_rfl
        · exact absurd rfl hj
      obtain ⟨w, hw⟩ := hle hx
      rw [Submodule.mem_bot]
      have h1 := hdisj w w' hw
      rw [← hw]
      exact h1

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
