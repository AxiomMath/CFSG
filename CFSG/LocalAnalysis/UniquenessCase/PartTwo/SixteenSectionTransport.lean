module

public import CFSG.Quasithin.Background.F918V3QD1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

theorem realizes_map_of_surjective_of_inf_ker_le
    {W W' : Type} [CommGroup W] [CommGroup W'] {Dm : FFModel}
    {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    {U Z : Subgroup W}
    (hR : Dm.Realizes H U Z) (ρ : W →* W')
    (hρ : Function.Surjective ρ) (hker : U ⊓ ρ.ker ≤ Z)
    (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (he : ∀ (h : ↥H) (w : W),
      ρ ((h : MulAut W) w) = (θ h : MulAut W') (ρ w)) :
    Dm.Realizes H' (U.map ρ) (Z.map ρ) := by
  classical
  let C : Subgroup W := ρ.ker
  let q₀ : W →* W ⧸ C := QuotientGroup.mk' C
  have hXC : H ≤ stabSub C := by
    intro h hh
    rw [mem_stabSub]
    intro w
    show ρ ((h : MulAut W) w) = 1 ↔ ρ w = 1
    rw [he ⟨h, hh⟩ w]
    constructor
    · intro h1
      exact (θ ⟨h, hh⟩ : MulAut W').injective (by rw [h1, map_one])
    · intro h1
      rw [h1, map_one]
  obtain ⟨π, hπ⟩ := hR
  obtain ⟨π', hπ'⟩ :=
    CFSG.Quasithin.v3qd_realizesVia_autQuot (X := H) (C := C) (U := U) (Z := Z) hXC hπ hker
  let e : (W ⧸ C) ≃* W' := QuotientGroup.quotientKerEquivOfSurjective (φ := ρ) hρ
  have he_mk : ∀ w : W, e (q₀ w) = ρ w := fun w => QuotientGroup.kerLift_mk (φ := ρ) w
  let α : MulAut (W ⧸ C) ≃* MulAut W' := MulAut.congr e
  have hα : ∀ (φ : MulAut (W ⧸ C)) (q : W ⧸ C), α φ (e q) = e (φ q) := by
    intro φ q
    change e (φ (e.symm (e q))) = e (φ q)
    rw [MulEquiv.symm_apply_apply]
  have hkey : ∀ (g : stabSub C) (hg : (g : MulAut W) ∈ H),
      α (quotHom C g) = (θ ⟨(g : MulAut W), hg⟩ : MulAut W') := by
    intro g hg
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective C (e.symm q)
    have hq : e (q₀ w) = q := by rw [hw, MulEquiv.apply_symm_apply]
    have hquot : ∀ (g : stabSub C) (w : W), quotHom C g (q₀ w) = q₀ ((g : MulAut W) w) := fun _ _ => rfl
    rw [← hq, hα, hquot, he_mk, he_mk, he ⟨(g : MulAut W), hg⟩]
  have hmap : (autQuot H C).map α.toMonoidHom = H' := by
    ext φ
    constructor
    · intro hφ
      rw [Subgroup.mem_map] at hφ
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      rw [mem_autQuot] at hψ
      obtain ⟨g, hgH, hgψ⟩ := hψ
      rw [← hgψ]
      exact (hkey g hgH) ▸ (θ ⟨(g : MulAut W), hgH⟩).2
    · intro hφ
      rw [Subgroup.mem_map]
      obtain ⟨h, hh⟩ := hθ ⟨φ, hφ⟩
      refine ⟨quotHom C ⟨(h : MulAut W), hXC h.2⟩, mem_autQuot.2
        ⟨⟨(h : MulAut W), hXC h.2⟩, h.2, rfl⟩, ?_⟩
      change α (quotHom C ⟨(h : MulAut W), hXC h.2⟩) = φ
      rw [hkey ⟨(h : MulAut W), hXC h.2⟩ h.2]
      exact congrArg Subtype.val hh
  let θ' : ↥(autQuot H C) ≃* ↥H' :=
    (MulEquiv.subgroupMap α (autQuot H C)).trans (MulEquiv.subgroupCongr hmap)
  have hθ' : Function.Surjective θ' := θ'.surjective
  have heq : ∀ (h : ↥(autQuot H C)) (w : W ⧸ C),
      e ((h : MulAut (W ⧸ C)) w) = ((θ' h : ↥H') : MulAut W') (e w) := by
    intro h w
    have hcoe : ((θ' h : ↥H') : MulAut W') = α h := rfl
    rw [hcoe]
    exact (hα (h : MulAut (W ⧸ C)) w).symm
  have hker_e : e.toMonoidHom.ker ≤ Z.map q₀ := by
    rw [MonoidHom.ker_eq_bot _ (show Function.Injective e.toMonoidHom from e.injective)]
    exact bot_le
  have h1 : Dm.RealizesVia H' ((U.map q₀).map e.toMonoidHom)
      ((Z.map q₀).map e.toMonoidHom) (θ'.toMonoidHom.comp π') :=
    s16k_realizesVia_map hπ' e.toMonoidHom hker_e θ'.toMonoidHom hθ' heq
  have hcomp : e.toMonoidHom.comp q₀ = ρ := MonoidHom.ext he_mk
  refine ⟨θ'.toMonoidHom.comp π', ?_⟩
  rw [Subgroup.map_map, Subgroup.map_map, hcomp] at h1
  exact h1

theorem sumOfNat_comap_of_injective
    {X W : Type} [CommGroup X] [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {k : ℕ}
    (hS : SumOfNat N H U Z k) (φ : X →* W) (hφ : Function.Injective φ)
    (hU : U ≤ φ.range) :
    SumOfNat (fun _ J C => N H (J.map φ) (C.map φ)) ⊥
      (U.comap φ) (Z.comap φ) k := by
  obtain ⟨I, hZI, hind, hsup, hNI⟩ := hS
  have hZU : Z ≤ U := hsup ▸ le_sup_left
  have hIU : ∀ i, I i ≤ U := fun i => hsup ▸ le_sup_of_le_right (le_iSup I i)
  refine ⟨fun i => (I i).comap φ, fun i => Subgroup.comap_mono (hZI i), ?_, ?_, ?_⟩
  · intro i
    have hm : ((I i).comap φ ⊓ (Z.comap φ ⊔
        ⨆ (j : Fin k) (_ : j ≠ i), (I j).comap φ)).map φ ≤ (Z.comap φ).map φ := by
      have hI : ∀ j, Subgroup.map φ (Subgroup.comap φ (I j)) = I j :=
        fun j => Subgroup.map_comap_eq_self (f := φ) (H := I j) ((hIU j).trans hU)
      have hZ : Subgroup.map φ (Subgroup.comap φ Z) = Z :=
        Subgroup.map_comap_eq_self (f := φ) (H := Z) (hZU.trans hU)
      rw [Subgroup.map_inf _ _ φ hφ, Subgroup.map_sup, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup, hI, hZ]
      exact hind i
    rw [Subgroup.map_le_iff_le_comap] at hm
    rwa [Subgroup.comap_map_eq_self_of_injective hφ (Z.comap φ)] at hm
  · apply Subgroup.map_injective (f := φ) hφ
    rw [Subgroup.map_sup, Subgroup.map_iSup]
    have hZ : Subgroup.map φ (Subgroup.comap φ Z) = Z :=
      Subgroup.map_comap_eq_self (f := φ) (H := Z) (hZU.trans hU)
    have hI : ∀ i, Subgroup.map φ (Subgroup.comap φ (I i)) = I i :=
      fun i => Subgroup.map_comap_eq_self (f := φ) (H := I i) ((hIU i).trans hU)
    have hU' : Subgroup.map φ (Subgroup.comap φ U) = U :=
      Subgroup.map_comap_eq_self (f := φ) (H := U) hU
    rw [hZ, hU', iSup_congr hI]
    exact hsup
  · intro i
    rw [Subgroup.map_comap_eq, Subgroup.map_comap_eq, inf_eq_right.mpr ((hIU i).trans hU),
      inf_eq_right.mpr (hZU.trans hU)]
    exact hNI i

theorem sumOfNat_map_of_inf_ker_le
    {W W' : Type} [CommGroup W] [CommGroup W']
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    {N' : Subgroup (MulAut W') → Subgroup W' → Subgroup W' → Prop}
    {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut W')}
    {U Z : Subgroup W} {k : ℕ}
    (hS : SumOfNat N H U Z k) (ρ : W →* W')
    (hker : U ⊓ ρ.ker ≤ Z)
    (hN : ∀ I : Subgroup W, Z ≤ I → I ≤ U →
      N H I Z → N' H' (I.map ρ) (Z.map ρ)) :
    SumOfNat N' H' (U.map ρ) (Z.map ρ) k := by
  have hZU : Z ≤ U := by
    obtain ⟨I, hZI, -, hsup, -⟩ := hS
    exact hsup ▸ le_sup_left
  let φ : ↥U →* W := U.subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hφrange : U ≤ φ.range := by
    rw [Subgroup.range_subtype]
  have hS' : SumOfNat (fun _ J C => N H (J.map φ) (C.map φ)) ⊥
      (U.comap φ) (Z.comap φ) k := sumOfNat_comap_of_injective hS φ hφ hφrange
  have hker' : (ρ.comp φ).ker ≤ Z.comap φ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap]
    exact hker ⟨x.2, hx⟩
  have htop : ((U.comap φ).map (ρ.comp φ)) = U.map ρ := by
    rw [← Subgroup.map_map, Subgroup.map_comap_eq_self (f := φ) (H := U) hφrange]
  have hden : ((Z.comap φ).map (ρ.comp φ)) = Z.map ρ := by
    rw [← Subgroup.map_map, Subgroup.map_comap_eq_self (f := φ) (H := Z) (hZU.trans hφrange)]
  have hN' : ∀ I' : Subgroup ↥U, Z.comap φ ≤ I' →
      N H (I'.map φ) ((Z.comap φ).map φ) →
      N' H' (I'.map (ρ.comp φ)) ((Z.comap φ).map (ρ.comp φ)) := by
    intro I' hI' hNI'
    have hZI : Z ≤ I'.map φ := by
      rw [← Subgroup.map_comap_eq_self (f := φ) (H := Z) (hZU.trans hφrange)]
      exact Subgroup.map_mono hI'
    have hIU : I'.map φ ≤ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hNI'' : N H (I'.map φ) Z := by
      rwa [Subgroup.map_comap_eq_self (f := φ) (H := Z) (hZU.trans hφrange)] at hNI'
    have hres := hN (I'.map φ) hZI hIU hNI''
    have e1 : (I'.map φ).map ρ = I'.map (ρ.comp φ) := Subgroup.map_map (K := I') ρ φ
    rw [e1, ← hden] at hres
    exact hres
  have hres := s16k_sumOfNat_map hS' (ρ.comp φ) hker' hN'
  rwa [htop, hden] at hres

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
