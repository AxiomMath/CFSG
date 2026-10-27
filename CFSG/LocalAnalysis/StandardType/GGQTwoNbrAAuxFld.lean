module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

theorem qTwoNbrA_hasLabel_of_lieModel {R : Type} [Group R] {t : ℕ} (ht : 4 ≤ t)
    (hR : LieModel R .PSU t 2 1) : GGHasLabel (⟨.twA, t - 1, 1⟩ : LargeEvenLabel) R := by
  have hS : CFSG.Open.StatedClassicalModel R .PSU t 2 1 := hR.statedClassicalModel (by decide)
  have ht0 : 0 < t := by omega
  dsimp only [GGHasLabel, LargeEvenRawDatum]
  rw [show t - 1 + 1 = t from Nat.succ_pred_eq_of_pos ht0]
  exact recipeUnitary_of_statedClassicalModel hS

theorem qTwoNbrA_labJ_n {R : Type} [Group R] (hRig : GGLabelRigidInput) {t : ℕ} (ht : 4 ≤ t)
    (hR : LieModel R .PSU t 2 1) {labJ : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hhas : GGHasLabel labJ R) : labJ.n = 1 := by
  have hνΛ : LargeEvenInLambda2 (⟨.twA, t - 1, 1⟩ : LargeEvenLabel) := by
    unfold LargeEvenInLambda2
    refine ⟨le_refl 1, ?_, ?_⟩
    · change 2 ≤ t - 1
      omega
    · intro h
      change t - 1 = 2 at h
      change 2 ≤ 1
      omega
  have hν : GGHasLabel (⟨.twA, t - 1, 1⟩ : LargeEvenLabel) R :=
    qTwoNbrA_hasLabel_of_lieModel ht hR
  have hIso : GGLabelIso (⟨.twA, t - 1, 1⟩ : LargeEvenLabel) labJ :=
    hRig _ _ R hνΛ hΛ hν hhas
  rcases GGLabelIso.n_cases hIso with h | h | h
  · simpa using h.symm
  · have htag := h.1
    change (.twA : LargeEvenLieTag) = .twD at htag
    cases htag
  · change 1 = 2 * labJ.n at h
    have hpos : 1 ≤ labJ.n := hΛ.1
    omega

theorem qTwoNbrA_tcj_nbr (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {B Bs L D J : Subgroup G} {x : G} (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr 3 B x D J y K) (hJK : J ≤ K) (hInn : GGInnerDiagOn Bs K)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K)) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) := by
  have hxB : x ∈ B := hcfg.1.2.2.2.2.2.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hxB
  have hx1 : x ^ 3 = 1 := hcfg.2.1.2.1.2 x hxBs
  have hM0 := ggInnerDiagOn_relabel hRig hInn hlab hhas
  have hM := ggMarking_and_labelAll_dep
    (fun lab hlab => hTCJ 3 Nat.prime_three (by norm_num) lab hlab) hM0
  have hKperf : commutator ↥K = ⊤ := hM0.1
  obtain ⟨lab', hlab', hhas', R, _, I, F, θ, ⟨⟨hEq, hNK, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hNK hxBs
  have hep : K.normalizerMonoidHom ⟨x, hxN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hxBs)
  let ψ : ↥K →* R :=
    (θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥K := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : K ⧸ Subgroup.center K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥K, φ (ψ l) = ψ (K.normalizerMonoidHom ⟨x, hxN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (K.normalizerMonoidHom ⟨x, hxN⟩ l) ?_⟩
    show ((K.normalizerMonoidHom ⟨x, hxN⟩ l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hcfg hnbr hJK
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  let eJ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
      ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK) (Subgroup.map_center_eq _)
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥K ψ hψsurj hψker hKperf (K.normalizerMonoidHom ⟨x, hxN⟩) hep hφe
      (J.subgroupOf K) hJcomp
  refine ⟨labJ, hlabJ, ?_, ggHasLabel_of_mulEquiv eJ hhasJ⟩
  rw [← hEq]
  exact hdvd

end CFSG.StandardType.QTwo

end
