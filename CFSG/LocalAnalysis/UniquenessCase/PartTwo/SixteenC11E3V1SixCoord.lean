module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixModel
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Quasithin.H13.VolIAltCoverSixData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s1611e3_six_coord {V : Type} [CommGroup V] {H : Subgroup (MulAut V)}
    (h : FFModel.Realizes (CFSG.Quasithin.H13.altCoreModel 6) H ⊤ ⊥) :
    ∃ (π : ↥(alternatingGroup (Fin 6)) →* ↥H) (Ψ : SixE6 ≃* V), Function.Surjective π ∧
      ∀ (a : ↥(alternatingGroup (Fin 6))) (x : SixE6),
        Ψ (CFSG.Quasithin.H13.VolI.act6 a x) = ((π a : ↥H) : MulAut V) (Ψ x) := by
  obtain ⟨π, hR⟩ := h
  obtain ⟨hπs, -, -, -, -, -, -, β, hβs, hβk, hβe⟩ := hR
  let D := CFSG.Quasithin.H13.altCoreModel 6
  let q : ↥D.sec ⧸ D.ker.subgroupOf D.sec ≃* ↥D.sec :=
    (QuotientGroup.quotientMulEquivOfEq (by exact Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot
  have hqmk : ∀ m : ↥D.sec, q (QuotientGroup.mk m) = m := fun _ => rfl
  let Φ : V →* SixE6 := q.toMonoidHom.comp (β.comp (Subgroup.topEquiv.symm).toMonoidHom)
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : q (β (Subgroup.topEquiv.symm v)) = 1 := hv
    have hβ1 : β (Subgroup.topEquiv.symm v) = 1 := q.injective (by rw [hv', map_one])
    have h2 : ((Subgroup.topEquiv.symm v : ↥(⊤ : Subgroup V)) : V) ∈ (⊥ : Subgroup V) :=
      (hβk _).1 hβ1
    rw [Subgroup.mem_bot] at h2
    have hu : Subgroup.topEquiv.symm v = 1 := Subtype.ext (by simpa using h2)
    have hv1 : v = 1 := by
      have hc := congrArg Subgroup.topEquiv hu
      simpa using hc
    exact hv1
  have hΦsurj : Function.Surjective Φ := by
    intro y
    obtain ⟨a, ha⟩ := q.surjective y
    obtain ⟨u, hu⟩ := hβs a
    obtain ⟨v, hv⟩ := (Subgroup.topEquiv.symm).surjective u
    exact ⟨v, by
      show q (β (Subgroup.topEquiv.symm v)) = y
      rw [hv, hu, ha]⟩
  let e : V ≃* SixE6 := MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  refine ⟨π, e.symm, hπs, ?_⟩
  intro a x
  let x' : ↥D.sec := x
  have hwe : e (e.symm x) = x := MulEquiv.apply_symm_apply e x
  have hβu : β (Subgroup.topEquiv.symm (e.symm x)) = QuotientGroup.mk x' := by
    apply q.injective
    rw [hqmk]
    show q (β (Subgroup.topEquiv.symm (e.symm x))) = x'
    rw [show q (β (Subgroup.topEquiv.symm (e.symm x))) = e (e.symm x) from rfl, hwe]
  have h1 : β (Subgroup.topEquiv.symm (((π a : ↥H) : MulAut V) (e.symm x))) =
      QuotientGroup.mk (CFSG.Quasithin.H13.VolI.act6 a x') := by
    have hb := hβe a (Subgroup.topEquiv.symm (e.symm x)) x' (Subgroup.mem_top _)
      (G6.permAct_mem_coreMod (a : Equiv.Perm (Fin 6)) x'.2) hβu
    rw [Subgroup.topEquiv_symm_apply_coe] at hb
    rw [show Subgroup.topEquiv.symm (((π a : ↥H) : MulAut V) (e.symm x)) =
      ⟨((π a : ↥H) : MulAut V) (e.symm x), Subgroup.mem_top _⟩ from rfl]
    exact hb.trans (congrArg QuotientGroup.mk (Subtype.ext rfl))
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  symm
  show q (β (Subgroup.topEquiv.symm (((π a : ↥H) : MulAut V) (e.symm x)))) =
    CFSG.Quasithin.H13.VolI.act6 a x
  rw [h1]
  exact hqmk _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
