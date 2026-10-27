module

public import CFSG.LocalAnalysis.StandardType.GGForkA8TablePClauses
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem ggNbr_label_J_of_tcj_and {G : Type} [Group G] [Finite G] (hTCJ : GGTCJKnown) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) {Q : LargeEvenLabel → LargeEvenRawCont}
    (hQ : ∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll lab (Q lab)) :
    commutator ↥L = ⊤ ∧
      ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧ LargeEvenSplit p lab ∧
        GGHasLabel lab (L ⧸ Subgroup.center L) ∧ LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
        GGHasLabel labJ (J ⧸ Subgroup.center J) ∧
        ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : L ⧸ Subgroup.center L ≃* R)
          (hBN : B ≤ Subgroup.normalizer (L : Set G)),
          (∀ b : B, ggBeta L θ hBN b ∈ I) ∧ Q lab R I F := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSS.2.2.2.1.1
  have hy : y ∈ B := hnb.1.2.1
  have hMark : GGInnerDiagOnLab (fun _ _ => True) p B L :=
    ggInnerDiagOnLab_of_cover (fun _ _ _ _ => trivial) hT
  have hLperf : commutator ↥L = ⊤ := hMark.1
  have hM := ggMarking_and_labelAll_dep
    (fun lab hlab => largeEvenLabelAll_and (hTCJ p hp hp2 lab hlab) (hQ lab hlab)) hMark
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨-, hsplit, hNL, hind⟩, hTC, hQ'⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNL hy
  have hy1 : y ^ p = 1 := hBel.2 y hy
  have hep : L.normalizerMonoidHom ⟨y, hyN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hy1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind y⁻¹ (B.inv_mem hy)
  let ψ : ↥L →* R := (θ : L ⧸ Subgroup.center L →* R).comp (QuotientGroup.mk' (Subgroup.center L))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥L := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : L ⧸ Subgroup.center L) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (L.normalizerMonoidHom ⟨y, hyN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (L.normalizerMonoidHom ⟨y, hyN⟩ l) ?_⟩
    show ((L.normalizerMonoidHom ⟨y, hyN⟩ l : ↥L) : G) = y⁻¹⁻¹ * (l : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hDy : D = Subgroup.closure {x, y} := hnb.2.1
  have hcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  rw [hDy, ggInf_centralizer_pair hLx] at hcomp
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hyN hcomp
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥L ψ hψsurj hψker hLperf _ hep hφe (J.subgroupOf L) hJcomp
  have hhasJ' : GGHasLabel labJ (J ⧸ Subgroup.center J) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL)
      (Subgroup.map_center_eq _)) hhasJ
  refine ⟨hLperf, lab, labJ, hlab, hsplit, hhas, hlabJ, hdvd, hhasJ', ?_⟩
  exact ⟨R, inferInstance, I, F, θ, hNL, fun b => ggBeta_mem L θ hNL hind b, hQ'⟩

end CFSG.StandardType

end
