module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4PinnedFrame
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialUnitaryOrbit
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore

theorem retTriD4_model_eq
    {SK : LangSetup Tag.D4 GGL 5} {h : ℕ} (hSKΦ : SK.D.Φ = triPsi h 1)
    {K : Type} [Group K] (hperf : Group.IsPerfect K) (ιA : K →* ModGL Tag.D4 GGL)
    (hιA : ιA.range = adjointGroup Tag.D4 GGL ⊓ (triPsi h 1).eqLocus (MonoidHom.id _)) :
    SK.D.model = ιA.range.map (MulAut.conj SK.D.g0⁻¹).toMonoidHom ∧ SK.Γ = SK.D.model := by
  classical
  have hfix : SK.D.fix = ιA.range := by
    unfold LangDatum.fix
    rw [hSKΦ, ← hιA]
  have hmodel : SK.D.model = ιA.range.map (MulAut.conj SK.D.g0⁻¹).toMonoidHom := by
    rw [LangDescent.model_eq SK.D, hfix]
  have hperfRange : ⁅ιA.range, ιA.range⁆ = ιA.range := by
    rw [← map_commutator_eq K ιA, hperf.commutator_eq_top, ← MonoidHom.range_eq_map ιA]
  refine ⟨hmodel, ?_⟩
  unfold LangSetup.Γ LangDatum.Γ
  rw [hmodel, ← Subgroup.map_commutator (f := (MulAut.conj SK.D.g0⁻¹).toMonoidHom), hperfRange]

theorem retTriD4_component_eq
    {τ : Tag} (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a))
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (SK : LangSetup Tag.D4 GGL 5)
    (hY : ∀ y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      S.D.step y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i))
    (Ξ : ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i)) ≃* ↥(adjointGroup Tag.D4 GGL))
    (hstep : ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i)),
      (Ξ ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) = SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL)) :
    (∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i)),
      y ∈ S.D.model ↔ (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ SK.D.model) ∧
    (Group.IsPerfect ↥SK.D.model →
      rationalComponent S.ρ S.Γ (rootCharHom a) i =
        rootSpan τ GGL (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
  classical
  let Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i
  let U : Subgroup (ModGL τ GGL) := rootSpan τ GGL Ψ
  have hs1 : componentOrbitLength S.ρ Ψ = 1 := hs
  have hρΨ : S.ρ '' Ψ = Ψ := by
    have hne : {s : ℕ | 0 < s ∧
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : componentOrbitLength S.ρ Ψ = 0 := by
        unfold componentOrbitLength
        rw [hemp, Nat.sInf_empty]
      rw [hs1] at h0
      exact Nat.one_ne_zero h0
    have himg : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' Ψ = Ψ := by
      rw [← hs1]
      exact (Nat.sInf_mem hne).2
    simpa using himg
  have hroot : ∀ γ ∈ Ψ, IsRoot τ γ := fun γ hγ => isRoot_of_mem_componentRoots hγ
  have hmodel_iff : ∀ (y : ModGL τ GGL) (hy : y ∈ U),
      y ∈ S.D.model ↔ (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈ SK.D.model := by
    intro y hy
    have hyadj : y ∈ adjointGroup τ GGL := rootSpan_le_adjointGroup GGL Ψ hy
    rw [LangDatum.mem_model, LangDatum.mem_model]
    constructor
    · rintro ⟨-, hstep_y⟩
      refine ⟨(Ξ ⟨y, hy⟩).2, ?_⟩
      change SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) =
        (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL)
      rw [← hstep y hy]
      exact congrArg (fun u : ↥U => (Ξ u : ModGL Tag.D4 GGL)) (Subtype.ext hstep_y)
    · rintro ⟨-, hstepKy⟩
      refine ⟨hyadj, ?_⟩
      have hsub : (Ξ ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) =
          (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) := by
        rw [hstep y hy]
        exact hstepKy
      change S.D.step y = y
      exact congrArg Subtype.val (Ξ.injective (Subtype.ext hsub))
  refine ⟨hmodel_iff, ?_⟩
  intro hperfK
  let H : Subgroup ↥U := S.D.model.subgroupOf U
  have hmap : H.map Ξ.toMonoidHom =
      SK.D.model.subgroupOf (adjointGroup Tag.D4 GGL) := by
    ext x
    constructor
    · rintro ⟨y, hyH, rfl⟩
      exact (hmodel_iff y.1 y.2).1 hyH
    · intro hx
      obtain ⟨y, hyx⟩ := Ξ.surjective x
      have hyxval : (Ξ y : ModGL Tag.D4 GGL) = x.1 := congrArg Subtype.val hyx
      refine ⟨y, ?_, hyx⟩
      show y.1 ∈ S.D.model
      exact (hmodel_iff y.1 y.2).2 (by
        rw [hyxval]
        exact Subgroup.mem_subgroupOf.1 hx)
  have hperfH : Group.IsPerfect ↥H := by
    have hK : Group.IsPerfect ↥SK.D.model := hperfK
    let e : ↥H ≃* ↥SK.D.model :=
      (Subgroup.equivMapOfInjective H Ξ.toMonoidHom Ξ.injective).trans
        ((MulEquiv.subgroupCongr hmap).trans
          (Subgroup.subgroupOfEquivOfLe
            (inf_le_left : SK.D.model ≤ adjointGroup Tag.D4 GGL)))
    exact @Group.IsPerfect.ofSurjective ↥SK.D.model ↥H _ _
      (e.symm : ↥SK.D.model →* ↥H) hK e.symm.surjective
  let Y : Subgroup (ModGL τ GGL) := U ⊓ S.D.model
  have hYH : H = Y.subgroupOf U := by
    show S.D.model.subgroupOf U = (U ⊓ S.D.model).subgroupOf U
    rw [Subgroup.inf_subgroupOf_left]
  have hperfY : Group.IsPerfect ↥Y := by
    have hH : Group.IsPerfect ↥H := hperfH
    let e : ↥H ≃* ↥Y :=
      (MulEquiv.subgroupCongr hYH).trans
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : Y ≤ U))
    exact @Group.IsPerfect.ofSurjective ↥H ↥Y _ _
      (e : ↥H →* ↥Y) hH e.surjective
  have hcommY : ⁅Y, Y⁆ = Y := by
    have h1 : ⁅Y, Y⁆ = (commutator ↥Y).map Y.subtype := by
      rw [commutator_def, Subgroup.map_commutator (f := Y.subtype)]
      simp only [← MonoidHom.range_eq_map Y.subtype, Subgroup.range_subtype]
    calc ⁅Y, Y⁆ = (commutator ↥Y).map Y.subtype := h1
      _ = (⊤ : Subgroup ↥Y).map Y.subtype := by rw [hperfY.commutator_eq_top]
      _ = Y := by rw [← MonoidHom.range_eq_map Y.subtype, Subgroup.range_subtype]
  have hY_le_Γ : Y ≤ S.Γ := by
    have h := Subgroup.commutator_mono (inf_le_right : Y ≤ S.D.model)
      (inf_le_right : Y ≤ S.D.model)
    rw [hcommY] at h
    exact h
  have hrr : rationalRoots S.ρ (rootCharHom a) i = Ψ := by
    have hρk : ∀ k : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' Ψ = Ψ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show (S.ρ : (Fin τ.rank → ℤ) → _)^[k + 1] =
            S.ρ ∘ (S.ρ : (Fin τ.rank → ℤ) → _)^[k] from
          funext fun x => Function.iterate_succ_apply' _ _ _]
        rw [Set.image_comp, ih, hρΨ]
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      have hmem : (S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' Ψ := Set.mem_image_of_mem _ hδ
      simpa only [hρk k] using hmem
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  have hspan : rationalSpan S.ρ S.Γ (rootCharHom a) i = Y := by
    rw [rationalSpan, hrr]
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, Subgroup.commutator_le_self S.D.model hx.2⟩
    · intro x hx
      exact ⟨hx.1, hY_le_Γ hx⟩
  unfold rationalComponent
  rw [hspan, hcommY]

theorem retTriD4_torus_mem
    {τ : Tag} (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a))
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1)
    (SK : LangSetup Tag.D4 GGL 5) {h : ℕ} (hSKΦ : SK.D.Φ = triPsi h 1)
    (hY : ∀ y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i),
      S.D.step y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i))
    (Ξ : ↥(rootSpan τ GGL (componentRoots (rootCharHom a) i)) ≃* ↥(adjointGroup Tag.D4 GGL))
    (hstep : ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i)),
      (Ξ ⟨S.D.step y, hY y hy⟩ : ModGL Tag.D4 GGL) = SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL))
    {b : ModGL τ GGL} (hb : b ∈ S.D.torus) {t : ModGL Tag.D4 GGL}
    (ht : t ∈ torusGroup Tag.D4 GGL)
    (hbt : ∀ (y : ModGL τ GGL) (hy : y ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i))
      (hby : b * y * b⁻¹ ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i)),
      (Ξ ⟨b * y * b⁻¹, hby⟩ : ModGL Tag.D4 GGL) = t * (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * t⁻¹) :
    t ∈ SK.D.torus := by
  classical
  have hΦ : SK.D.Φ = triPsi h 1 := hSKΦ
  let Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i
  let U : Subgroup (ModGL τ GGL) := rootSpan τ GGL Ψ
  have hs1 : componentOrbitLength S.ρ Ψ = 1 := hs
  have hρΨ : S.ρ '' Ψ = Ψ := by
    have hne : {s : ℕ | 0 < s ∧
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : componentOrbitLength S.ρ Ψ = 0 := by
        unfold componentOrbitLength
        rw [hemp, Nat.sInf_empty]
      rw [hs1] at h0
      exact Nat.one_ne_zero h0
    have himg : (S.ρ : (Fin τ.rank → ℤ) → _)^[1] '' Ψ = Ψ := by
      rw [← hs1]
      exact (Nat.sInf_mem hne).2
    simpa using himg
  have hroot : ∀ γ ∈ Ψ, IsRoot τ γ := fun γ hγ => isRoot_of_mem_componentRoots hγ
  have hbT : b ∈ torusGroup τ GGL :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hb).1
  have hbstep : S.D.step b = b :=
    (LangDatum.mem_model S.D).1 (LangDatum.torus_le_model S.D hb) |>.2
  have hnormT : b ∈ Subgroup.normalizer (U : Set (ModGL τ GGL)) :=
    torusGroup_le_normalizer_rootSpan (K := GGL) hroot hbT
  have hconj_mem : ∀ y ∈ U, b * y * b⁻¹ ∈ U := by
    intro y hy
    exact (Subgroup.mem_normalizer_iff.1 hnormT y).1 hy
  have hmapU_le : U.map S.D.step ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact hY y hy
  have hU_le_mapU : U ≤ U.map S.D.step := by
    have hγle : ∀ γ ∈ Ψ, rootSubgroup τ GGL γ ≤ U.map S.D.step := by
      intro γ hγ
      have hγ' : γ ∈ S.ρ '' Ψ := by rw [hρΨ]; exact hγ
      obtain ⟨δ, hδ, rfl⟩ := hγ'
      rw [← S.frob.map_rootSubgroup δ (hroot δ hδ)]
      exact Subgroup.map_mono (le_iSup₂_of_le δ hδ le_rfl)
    show rootSpan τ GGL Ψ ≤ U.map S.D.step
    unfold rootSpan
    exact iSup₂_le hγle
  have hsurj : ∀ z ∈ adjointGroup Tag.D4 GGL, ∃ (y : ModGL τ GGL) (hy : y ∈ U),
      SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) = z := by
    intro z hz
    obtain ⟨u, hu⟩ := Ξ.surjective ⟨z, hz⟩
    obtain ⟨y, hy, hystep⟩ := Subgroup.mem_map.1 (hU_le_mapU u.2)
    refine ⟨y, hy, ?_⟩
    have hsub : (⟨S.D.step y, hY y hy⟩ : ↥U) = u := Subtype.ext hystep
    rw [← hstep y hy, hsub]
    exact congrArg Subtype.val hu
  have hkey : ∀ (y : ModGL τ GGL) (hy : y ∈ U),
      t * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * t⁻¹ =
        SK.D.step t * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) *
          (SK.D.step t)⁻¹ := by
    intro y hy
    have hby : b * y * b⁻¹ ∈ U := hconj_mem y hy
    have hbs : b * S.D.step y * b⁻¹ ∈ U := hconj_mem (S.D.step y) (hY y hy)
    have hz : S.D.step (b * y * b⁻¹) = b * S.D.step y * b⁻¹ := by
      rw [map_mul, map_mul, map_inv, hbstep]
    have hA : (Ξ ⟨S.D.step (b * y * b⁻¹), hY _ hby⟩ : ModGL Tag.D4 GGL) =
        SK.D.step t * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) *
          (SK.D.step t)⁻¹ := by
      rw [hstep (b * y * b⁻¹) hby, hbt y hy hby]
      simp only [map_mul, map_inv]
    have hB : (Ξ ⟨S.D.step (b * y * b⁻¹), hY _ hby⟩ : ModGL Tag.D4 GGL) =
        t * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * t⁻¹ := by
      have hsub : (⟨S.D.step (b * y * b⁻¹), hY _ hby⟩ : ↥U) =
          ⟨b * S.D.step y * b⁻¹, hbs⟩ := Subtype.ext hz
      rw [hsub, hbt (S.D.step y) (hY y hy) hbs, hstep y hy]
    exact hB.symm.trans hA
  let c : ModGL Tag.D4 GGL := t⁻¹ * SK.D.step t
  have hcomm : ∀ (y : ModGL τ GGL) (hy : y ∈ U),
      c * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) =
        SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * c := by
    intro y hy
    have h := hkey y hy
    have hconj : c * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * c⁻¹ =
        SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) := by
      calc t⁻¹ * SK.D.step t * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) *
            (t⁻¹ * SK.D.step t)⁻¹
          = t⁻¹ * (SK.D.step t * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) *
              (SK.D.step t)⁻¹) * t := by group
        _ = t⁻¹ * (t * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * t⁻¹) * t := by
              rw [← h]
        _ = SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) := by group
    calc c * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL)
        = (c * SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * c⁻¹) * c := by group
      _ = SK.D.step (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) * c := by rw [hconj]
  have hcomm_adj : ∀ z ∈ adjointGroup Tag.D4 GGL, c * z = z * c := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hsurj z hz
    exact hcomm y hy
  have htA : t ∈ adjointGroup Tag.D4 GGL := torusGroup_le_adjointGroup ht
  have hc : c ∈ adjointGroup Tag.D4 GGL :=
    (adjointGroup Tag.D4 GGL).mul_mem ((adjointGroup Tag.D4 GGL).inv_mem htA)
      (torusGroup_le_adjointGroup (step_mem_torusGroup (S := SK) ht))
  have hcent : (⟨c, hc⟩ : adjointGroup Tag.D4 GGL) ∈
      Subgroup.center (adjointGroup Tag.D4 GGL) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm_adj g.1 g.2).symm
  rw [center_adjointGroup_eq_bot_field Tag.D4 GGL, Subgroup.mem_bot] at hcent
  have hc1 : c = 1 := congrArg Subtype.val hcent
  change t ∈ torusGroup Tag.D4 GGL ∧ SK.D.n * SK.D.Φ t * SK.D.n⁻¹ = t
  refine ⟨ht, ?_⟩
  have hinv : t⁻¹ * SK.D.step t = 1 := hc1
  exact (inv_mul_eq_one.mp hinv).symm

end CFSG.StandardType.RCKRP

end
