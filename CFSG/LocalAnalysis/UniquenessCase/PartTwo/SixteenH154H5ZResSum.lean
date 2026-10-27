module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSecA
public import CFSG.Quasithin.EmptyFaithful.S151bModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16h_realizes_autSub {V : Type} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)}
    {U I Z : Subgroup V} (hHU : H ≤ stabSub U) (hIU : I ≤ U) (hZI : Z ≤ I)
    (h : D.Realizes H I Z) :
    D.Realizes (autSub H U) (I.subgroupOf U) (Z.subgroupOf U) := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨hπsurj, -, hker, hInvU, hInvZ, hsecinv, hkerinv, β, hβsurj, hβker, hβeq⟩ := hπ
  let incl : ↥H →* ↥(stabSub U) := Subgroup.inclusion hHU
  let φ : ↥H →* ↥(autSub H U) :=
    ((resHom U).comp incl).codRestrict (autSub H U) fun x => by
      exact Subgroup.mem_map.mpr
        ⟨incl x, Subgroup.mem_subgroupOf.mpr (by
          rw [Subgroup.coe_inclusion]
          exact x.2), rfl⟩
  let π' : D.Gam →* ↥(autSub H U) := φ.comp π
  have hπ'_apply : ∀ (γ : D.Gam) (u : ↥U),
      (((π' γ : ↥(autSub H U)) : MulAut ↥U) u : V) =
        ((π γ : ↥H) : MulAut V) (u : V) := by
    intro γ u
    change ((resHom U (incl (π γ)) u : ↥U) : V) = ((π γ : ↥H) : MulAut V) (u : V)
    rw [resHom_apply]
    rfl
  have hπ'surj : Function.Surjective π' := by
    intro y
    have hy : y.1 ∈ (H.subgroupOf (stabSub U)).map (resHom U) := by
      simpa [autSub] using y.2
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    have hgH : (g : MulAut V) ∈ H := Subgroup.mem_subgroupOf.mp hg
    obtain ⟨γ, hγ⟩ := hπsurj ⟨(g : MulAut V), hgH⟩
    refine ⟨γ, ?_⟩
    apply Subtype.ext
    change resHom U (incl (π γ)) = y.1
    rw [hγ, show incl ⟨(g : MulAut V), hgH⟩ = g from Subtype.ext rfl, hgy]
  refine ⟨π', hπ'surj, Subgroup.subgroupOf_mono U hZI, hker, ?_, ?_, hsecinv, hkerinv, ?_⟩
  · intro h' u hu
    obtain ⟨g, hgH, hg_eq⟩ := mem_autSub.mp h'.2
    rw [← hg_eq]
    rw [Subgroup.mem_subgroupOf]
    have hI := hInvU ⟨(g : MulAut V), hgH⟩ u.1 (Subgroup.mem_subgroupOf.mp hu)
    simpa [resHom_apply] using hI
  · intro h' z hz
    obtain ⟨g, hgH, hg_eq⟩ := mem_autSub.mp h'.2
    rw [← hg_eq]
    rw [Subgroup.mem_subgroupOf]
    have hZ := hInvZ ⟨(g : MulAut V), hgH⟩ z.1 (Subgroup.mem_subgroupOf.mp hz)
    simpa [resHom_apply] using hZ
  · let e : ↥(I.subgroupOf U) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIU
    refine ⟨β.comp e.toMonoidHom, ?_, ?_, ?_⟩
    · simpa using hβsurj.comp e.surjective
    · intro u
      show β (e u) = 1 ↔ ((e u : ↥I) : V) ∈ Z
      exact hβker (e u)
    · intro γ u m hu hm hβu
      let w : ↥U := ((π' γ : ↥(autSub H U)) : MulAut ↥U) (u : ↥U)
      have hβu' : β (e u) = QuotientGroup.mk m := hβu
      have hu' : ((π γ : ↥H) : MulAut V) ((e u : ↥I) : V) ∈ I := by
        change ((π γ : ↥H) : MulAut V) ((u : ↥U) : V) ∈ I
        have h2 : (w : V) ∈ I := Subgroup.mem_subgroupOf.mp hu
        rwa [show (w : V) = ((π γ : ↥H) : MulAut V) ((u : ↥U) : V) from
          hπ'_apply γ (u : ↥U)] at h2
      have heq : e ⟨w, hu⟩ =
          ⟨((π γ : ↥H) : MulAut V) ((e u : ↥I) : V), hu'⟩ := by
        apply Subtype.ext
        show (w : V) = ((π γ : ↥H) : MulAut V) ((u : ↥U) : V)
        exact hπ'_apply γ (u : ↥U)
      calc (β.comp e.toMonoidHom) ⟨w, hu⟩
          = β (e ⟨w, hu⟩) := rfl
        _ = β ⟨((π γ : ↥H) : MulAut V) ((e u : ↥I) : V), hu'⟩ := congrArg β heq
        _ = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩ := hβeq γ (e u) m hu' hm hβu'

theorem s16h_L3_res_sum {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L)) :
    ∃ k : ℕ, k ≤ 3 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (autSub L (commSub ⊤ L)) ⊤ (fixV (autSub L (commSub ⊤ L))) k := by
  obtain ⟨k, hk, -, I, hZI, hind, hsup, hnat⟩ := h
  let U : Subgroup W := commSub ⊤ L
  let Z : Subgroup W := commSub ⊤ L ⊓ fixV L
  have hZU : Z ≤ U := inf_le_left
  have hIU : ∀ j, I j ≤ U := fun j =>
    (le_iSup I j).trans (le_sup_right.trans (le_of_eq hsup))
  have hstable : StableUnder L U := fun g hg u hu =>
    commSub_top_stable151b (X := L) (g := g)
      (fun x hx => L.mul_mem (L.mul_mem hg hx) (L.inv_mem hg)) u hu
  have hLstab : L ≤ stabSub U := s16h_le_stabSub_of_stable hstable
  have hfix : Z.subgroupOf U = fixV (autSub L U) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [mem_fixV_autSub]
      intro g hg _
      exact mem_fixV.mp hx.2 g hg
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x.2, mem_fixV.mpr fun g hg => mem_fixV_autSub.mp hx g hg (hLstab hg)⟩
  refine ⟨k, hk, fun i => (I i).subgroupOf U, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← hfix]
    exact Subgroup.subgroupOf_mono U (hZI i)
  · intro i
    rw [← hfix]
    have hsub : (I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j)).subgroupOf U =
        (I i).subgroupOf U ⊓
          (Z.subgroupOf U ⊔ ⨆ (j : Fin k) (_ : j ≠ i), (I j).subgroupOf U) := by
      rw [← Subgroup.comap_subtype
            ((I i) ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j)) U,
        Subgroup.comap_inf]
      simp only [Subgroup.comap_subtype]
      rw [Subgroup.subgroupOf_sup hZU (iSup_le fun j => iSup_le fun _ => hIU j),
        s16h_subgroupOf_iSup_ne hIU i]
    rw [← hsub]
    exact Subgroup.subgroupOf_mono U (hind i)
  · rw [← hfix]
    have hgen : Z.subgroupOf U ⊔ ⨆ i, (I i).subgroupOf U = ⊤ := by
      calc Z.subgroupOf U ⊔ ⨆ i, (I i).subgroupOf U
          = (Z ⊔ ⨆ i, I i).subgroupOf U := by
            rw [Subgroup.subgroupOf_sup hZU (iSup_le fun j => hIU j), s16h_subgroupOf_iSup hIU]
        _ = U.subgroupOf U := by rw [hsup]
        _ = ⊤ := Subgroup.subgroupOf_self U
    exact hgen
  · intro i
    obtain ⟨K, hK, hKf, hKcard, hreal⟩ := hnat i
    refine ⟨K, hK, hKf, hKcard, ?_⟩
    rw [← hfix]
    exact s16h_realizes_autSub hLstab (hIU i) (hZI i) hreal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
