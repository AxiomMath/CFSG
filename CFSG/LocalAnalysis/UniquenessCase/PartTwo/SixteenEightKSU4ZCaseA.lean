module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23AEquivStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSULift
public import CFSG.Quasithin.Background.F918V2BB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_imgTil_v1Sub_eq_fixV (h : S16gRowCtx D ⊥ V L hV) :
    imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) = fixV (lBar ⊥ V hV L) := by
  have hLne : barSub ⊥ V hV L ≠ ⊥ := fun hb => by
    haveI := h.quasi.2.toNontrivial
    haveI : Nontrivial ↥(lBar ⊥ V hV L) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(lBar ⊥ V hV L))).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).1 ‹_› hb
  have hfix0 := s15_semiBot_imgTil_v1Sub_eq_fixV h.std.h1217 h.setting.hyp151 hLne
  have hsup : (⨆ m : D.M, barSub ⊥ V hV (conjSubgroup L (m : G))) = barSub ⊥ V hV L := by
    refine le_antisymm (iSup_le fun m => ?_) ?_
    · have hm : (m : G) ∈ stabTil ⊥ V :=
        le_stabTil h.setting.hyp151.hyp125.pairFacts.le_normalizer
          h.setting.hyp151.hyp125.pairFacts.le_normalizer₀ m.2
      have hg : actTil ⊥ V hV ⟨(m : G), hm⟩ ∈ Mbar D.M ⊥ V hV :=
        actTil_mem_barSub ⊥ V hV m.2 hm
      have hmap := Subgroup.mem_normalizer_iff_map_conj_eq.1
        (h.mBar_le_normalizer ((Mbar D.M ⊥ V hV).inv_mem hg))
      rw [s15_Infra_barSub_conjSubgroup ⊥ V hV hm L]
      exact le_of_eq hmap
    · have h1 : barSub ⊥ V hV (conjSubgroup L (1 : G)) = barSub ⊥ V hV L := by
        rw [conjSubgroup_one]
      rw [← h1]
      exact le_iSup (fun m : D.M => barSub ⊥ V hV (conjSubgroup L (m : G))) (1 : D.M)
  rw [hsup] at hfix0
  exact hfix0

theorem s16k_natSUn_lStar_of_lBar (h : S16gRowCtx D ⊥ V L hV)
    (hN : NatSUn (lBar ⊥ V hV L) (commSub ⊤ (lBar ⊥ V hV L))
      (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) 4 1) :
    NatSUn (lStar D.M ⊥ V hV L) ⊤ ⊥ 4 1 := by
  obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := hN
  letI : Field K := hKfield
  letI : Finite K := hKfin
  simp only [pow_one] at hR
  have hR' : (FFModel.nat (StatedSU 4 2 K)).Realizes (lBar ⊥ V hV L) ⊤
      (fixV (lBar ⊥ V hV L)) := by
    simpa only [h.comm_top, top_inf_eq] using hR
  obtain ⟨f, θ, hf_mk, hf_equiv⟩ :=
    c23a_equiv_star D h.std.h1217 h.setting.hyp151 hV h.setting.hyp151.le rfl
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := mkTil_surjective (v1Sub D.M ⊥ V hV L) V hV y
    exact ⟨mkTil ⊥ V hV x, hf_mk x⟩
  have hf_ker_img : f.ker = imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L) := by
    ext q
    rw [MonoidHom.mem_ker]
    constructor
    · intro hq
      obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
      rw [hf_mk] at hq
      exact ⟨x, (mem_modNull (v1Sub D.M ⊥ V hV L) V hV x).1
        ((QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M ⊥ V hV L) V hV) x).1 hq), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hf_mk]
      exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M ⊥ V hV L) V hV) x).2
        ((mem_modNull (v1Sub D.M ⊥ V hV L) V hV x).2 hx)
  have hf_ker : f.ker = fixV (lBar ⊥ V hV L) :=
    hf_ker_img.trans (s16k_imgTil_v1Sub_eq_fixV h)
  let U : Subgroup (Vtil ⊥ V hV) := ⊤
  let q : ↥U →* vStar D.M ⊥ V hV L := f.comp U.subtype
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, hw⟩ := hf_surj y
    exact ⟨⟨w, Subgroup.mem_top w⟩, hw⟩
  have hqk : ∀ u : ↥U, q u = 1 ↔ (u : Vtil ⊥ V hV) ∈ fixV (lBar ⊥ V hV L) := by
    intro u
    change f (u : Vtil ⊥ V hV) = 1 ↔ (u : Vtil ⊥ V hV) ∈ fixV (lBar ⊥ V hV L)
    rw [← MonoidHom.mem_ker, hf_ker]
  have heq : ∀ (a : ↥(lBar ⊥ V hV L)) (u : ↥U)
      (hu : ((a : MulAut (Vtil ⊥ V hV)) (u : Vtil ⊥ V hV)) ∈ U),
      q ⟨(a : MulAut (Vtil ⊥ V hV)) (u : Vtil ⊥ V hV), hu⟩ =
        ((θ a : ↥(lStar D.M ⊥ V hV L)) : MulAut (vStar D.M ⊥ V hV L)) (q u) := by
    intro a u _
    exact hf_equiv a (u : Vtil ⊥ V hV)
  obtain ⟨π, hπ⟩ := hR'
  have hdesc := Z391.realizesVia_descend (D := FFModel.nat (StatedSU 4 2 K))
    θ.toMonoidHom θ.surjective q hq hqk heq hπ
  exact ⟨K, hKfield, hKfin, hKcard, ⟨θ.toMonoidHom.comp π, hdesc⟩⟩

theorem s16k_su4z_sig_eq_three (h : S16gRowCtx D V₀ V L hV)
    (hN : NatSUn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 1)
    (hσ : 3 ∈ D.sig) : D.sig = {3} := by
  obtain ⟨K, hKfield, hKfin, hKcard, hR⟩ := hN
  letI : Field K := hKfield
  letI : Finite K := hKfin
  simp only [pow_one] at hR
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  obtain ⟨ρ, hρ, hρN⟩ := h.exists_embedding hR
  ext q
  constructor
  · intro hq
    by_contra hq3
    rw [Set.mem_singleton_iff] at hq3
    have hqp : q.Prime := (D.sig_prime q hq).1
    have hq2 : q ≠ 2 := (D.sig_prime q hq).2
    have hq5 : 5 ≤ q := hqp.five_le_of_ne_two_of_ne_three hq2 hq3
    exact h.false_of_fixNc hR hq
      (s16k_fixNc_statedSU_of_pRank hK4 (by norm_num) hqp hq5 ρ hρ hρN
        (h.three_le_pRank hq))
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact hσ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
