module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_ker_barSubBar2HomOfHyp125_le_center (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hne : barSub V₀ V h.isElemAbelian K ≠ ⊥) :
    (barSubBar2HomOfHyp125 h hK).ker ≤ Subgroup.center (Bar2 K) := by
  let f : Bar2 K →* ↥(barSub V₀ V h.isElemAbelian K) := barSubBar2HomOfHyp125 h hK
  have hf : Function.Surjective f := barSubBar2HomOfHyp125_surjective h hK
  have hkerne : f.ker ≠ ⊤ := by
    intro htop
    have hf1 : f = 1 := MonoidHom.ker_eq_top_iff.mp htop
    have hrange : f.range = ⊥ := by rw [hf1]; exact MonoidHom.range_one
    have htop' : (⊤ : Subgroup ↥(barSub V₀ V h.isElemAbelian K)) = ⊥ := by
      rw [← MonoidHom.range_eq_top.mpr hf, hrange]
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥(barSub V₀ V h.isElemAbelian K)) ∈
        (⊤ : Subgroup ↥(barSub V₀ V h.isElemAbelian K)) := Subgroup.mem_top _
    rw [htop'] at hx'
    have h1 : (⟨x, hx⟩ : ↥(barSub V₀ V h.isElemAbelian K)) = 1 := Subgroup.mem_bot.mp hx'
    simpa using congrArg Subtype.val h1
  show f.ker ≤ Subgroup.center (Bar2 K)
  exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
    hK.2.2 f.ker hkerne

theorem s16h_exists_central_cover_map (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {K : Subgroup G} (hK : K ∈ calC D.M) (hne : barSub V₀ V h.isElemAbelian K ≠ ⊥) :
    ∃ f : Bar2 K →* ↥(barSub V₀ V h.isElemAbelian K),
      Function.Surjective f ∧ f.ker ≤ Subgroup.center (Bar2 K) :=
  ⟨barSubBar2HomOfHyp125 h hK, barSubBar2HomOfHyp125_surjective h hK,
    s16h_ker_barSubBar2HomOfHyp125_le_center D h hK hne⟩

theorem s16h_pRank_cover_le_one_of_cyclic_sylow (D : Data G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hne : barSub V₀ V h.isElemAbelian K ≠ ⊥) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hcyc : ∀ Q : Sylow q ↥(barSub V₀ V h.isElemAbelian K),
      IsCyclic ↥(Q : Subgroup ↥(barSub V₀ V h.isElemAbelian K))) :
    CFSG.Open.pRank q K ≤ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Group.IsPerfect (Bar2 K) := ⟨hK.2.2.1⟩
  let f : Bar2 K →* ↥(barSub V₀ V h.isElemAbelian K) := barSubBar2HomOfHyp125 h hK
  have hf : Function.Surjective f := barSubBar2HomOfHyp125_surjective h hK
  have hfker : f.ker ≤ Subgroup.center (Bar2 K) :=
    s16h_ker_barSubBar2HomOfHyp125_le_center D h hK hne
  have hN2 : ¬ q ∣ Nat.card ↥f.ker := by
    intro hdvd
    obtain ⟨C⟩ := (inferInstance : Nonempty (Sylow q ↥f.ker))
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q ↥(barSub V₀ V h.isElemAbelian K)))
    have hCbot : (C : Subgroup ↥f.ker) = ⊥ :=
      CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot f hf hfker C Q (hcyc Q)
    exact (Sylow.ne_bot_of_dvd_card C hdvd) hCbot
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  have hstep2 : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K ⧸ f.ker)) =
      CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K)) :=
    CFSG.SectionRank.pRank_quotient_eq (p := q) f.ker hN2
  have hstep3 : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K ⧸ f.ker)) =
      CFSG.Open.pRank q (⊤ : Subgroup ↥(barSub V₀ V h.isElemAbelian K)) := by
    have e1 : CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K ⧸ f.ker)) =
        CFSG.Open.pRank q (⊤ : Subgroup ↥f.range) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := q) hq.one_lt
        (QuotientGroup.quotientKerEquivRange f)
    have e2 : CFSG.Open.pRank q (⊤ : Subgroup ↥f.range) =
        CFSG.Open.pRank q (⊤ : Subgroup ↥(barSub V₀ V h.isElemAbelian K)) := by
      rw [hrange]
      exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := q) hq.one_lt
        (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(barSub V₀ V h.isElemAbelian K)) ≃*
          ↥(barSub V₀ V h.isElemAbelian K))
    exact e1.trans e2
  have hstep4 : CFSG.Open.pRank q (⊤ : Subgroup ↥(barSub V₀ V h.isElemAbelian K)) ≤ 1 :=
    CFSG.QuasithinUnique.Id2519.pRank_le_one_of_sylow_cyclic hq hcyc
  calc CFSG.Open.pRank q K
      = CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K)) :=
        (UC22.pRank_bar2_eq_of_odd hq hq2).symm
    _ = CFSG.Open.pRank q (⊤ : Subgroup (Bar2 K ⧸ f.ker)) := hstep2.symm
    _ = CFSG.Open.pRank q (⊤ : Subgroup ↥(barSub V₀ V h.isElemAbelian K)) := hstep3
    _ ≤ 1 := hstep4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
