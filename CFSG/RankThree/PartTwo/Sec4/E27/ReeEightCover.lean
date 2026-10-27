module

public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEightModel
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Generic

public noncomputable section

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits HuppertReeEight
open CFSG.RankThree.PartTwo.Sec19.TrialityTwo

namespace CFSG.RankThree.PartTwo.Sec4.E27.ReeEight


theorem coverCheck_spec (h : coverCheck () = true) :
    (∀ d ∈ planeData, lettersOK 4 d.u = true ∧ lettersOK 4 d.v = true ∧
      isPairE (aArr d.u) (aArr d.v) = true) ∧
    ∀ x ∈ sylArrs (), oneE x = false → ∀ y ∈ sylArrs (), oneE y = false →
      memE (powsE x) y = true ∨ commE x y = false ∨
        ∃ d ∈ planeData, memE (planeE (aArr d.u) (aArr d.v)) x = true ∧
          memE (planeE (aArr d.u) (aArr d.v)) y = true := by
  simp only [coverCheck, Bool.and_eq_true, List.all_eq_true, List.mem_filter, Bool.not_eq_true',
    Bool.or_eq_true, List.any_eq_true, List.mem_map] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun d hd => ?_, fun x hx hx1 y hy hy1 => ?_⟩
  · have := h1 d hd
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := h2 x ⟨hx, hx1⟩ y ⟨hy, hy1⟩
    rcases this with (hm | hn) | ⟨P, ⟨d, hd, rfl⟩, hP⟩
    · exact Or.inl hm
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr ⟨d, hd, hP⟩)

theorem planeCover_of_sylow_check (hs : sylowCheck () = true) (hc : coverCheck () = true)
    {E : Subgroup ↥titsA} (hES : E ≤ sylGrp) (hE : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) :
    ∃ d ∈ planeData, valA d.u ∈ E ∧ valA d.v ∈ E := by
  obtain ⟨hpl, hcov⟩ := coverCheck_spec hc
  obtain ⟨-, hlet, -, -, -⟩ := sylowCheck_spec hs
  obtain ⟨x, y, hxE, hyE, hx1, hx3, hy3, hxy, hyset, hEeq⟩ := exists_gen_pair hE hcard
  obtain ⟨wx, hwx, rfl⟩ := (mem_sylGrp_iff hs).1 (hES hxE)
  obtain ⟨wy, hwy, rfl⟩ := (mem_sylGrp_iff hs).1 (hES hyE)
  have hrx := rep_valA (hlet wx hwx)
  have hry := rep_valA (hlet wy hwy)
  have hy1 : valA wy ≠ 1 := fun h1 => hyset (Or.inl h1)
  have hox : oneE (aArr wx) = false := Bool.eq_false_iff.2 fun h0 => hx1 ((oneE_iff hrx).1 h0)
  have hoy : oneE (aArr wy) = false := Bool.eq_false_iff.2 fun h0 => hy1 ((oneE_iff hry).1 h0)
  rcases hcov _ (List.mem_map.2 ⟨wx, hwx, rfl⟩) hox _ (List.mem_map.2 ⟨wy, hwy, rfl⟩) hoy with
    hm | hn | ⟨d, hd, hpx, hpy⟩
  · exact absurd ((memE_pows_iff hrx hry).1 hm) hyset
  · have := (commE_iff hrx hry).2 hxy
    rw [hn] at this
    exact absurd this (by simp)
  · obtain ⟨hlu, hlv, hpair⟩ := hpl d hd
    have hru := rep_valA hlu
    have hrv := rep_valA hlv
    obtain ⟨hu1, hu3, hv3, huv, hvn⟩ := (isPairE_iff hru hrv).1 hpair
    obtain ⟨i1, j1, -, -, hxij⟩ := memE_planeE hru hrv hrx hpx
    obtain ⟨i2, j2, -, -, hyij⟩ := memE_planeE hru hrv hry hpy
    have hxP : valA wx ∈ Subgroup.closure {valA d.u, valA d.v} := by
      rw [hxij]
      exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
        (pow_mem (Subgroup.subset_closure (by simp)) _)
    have hyP : valA wy ∈ Subgroup.closure {valA d.u, valA d.v} := by
      rw [hyij]
      exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
        (pow_mem (Subgroup.subset_closure (by simp)) _)
    have hle : E ≤ Subgroup.closure {valA d.u, valA d.v} := by
      rw [hEeq, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact hxP
      · exact hyP
    obtain ⟨-, -, hcardP⟩ := CFSG.AGLEmbedding.ChevOuter.closure_pair (valA d.u) (valA d.v) hu3 hv3
      huv (hind_of_pair hu1 hu3 hv3 hvn)
    have hEP : E = Subgroup.closure {valA d.u, valA d.v} :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardP, hcard])
    refine ⟨d, hd, ?_, ?_⟩
    · rw [hEP]
      exact Subgroup.subset_closure (by simp)
    · rw [hEP]
      exact Subgroup.subset_closure (by simp)

theorem planeCover_of_checks (hs : sylowCheck () = true) (hc : coverCheck () = true)
    {E : Subgroup ↥titsA} (hE : CFSG.IsElementaryAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) :
    ∃ g : ↥titsA, ∃ d ∈ planeData, g⁻¹ * valA d.u * g ∈ E ∧ g⁻¹ * valA d.v * g ∈ E := by
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hcard
  obtain ⟨g, hg⟩ := exists_conj_le_sylow (card_sylGrp_eq hs) hE3
  obtain ⟨hE', hcard'⟩ := isElementaryAbelian_map_conj hE hcard g
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ sylGrp := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using hg z hz
  obtain ⟨d, hd, h1, h2⟩ := planeCover_of_sylow_check hs hc hle hE' hcard'
  refine ⟨g, d, hd, ?_, ?_⟩
  · obtain ⟨z, hz, hzeq⟩ := h1
    have : g⁻¹ * valA d.u * g = z := by
      rw [← hzeq]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [this]
  · obtain ⟨z, hz, hzeq⟩ := h2
    have : g⁻¹ * valA d.v * g = z := by
      rw [← hzeq]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [this]

end CFSG.RankThree.PartTwo.Sec4.E27.ReeEight
