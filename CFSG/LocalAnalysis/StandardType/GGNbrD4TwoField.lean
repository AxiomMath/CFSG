module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOrthLabel
public import CFSG.LocalAnalysis.StandardType.GGTCJLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import Certificates.Certificate1952
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate8117
public import Certificates.Certificate10050
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate18000
public import Certificates.Certificate19953
import CFSG.LocalAnalysis.StandardType.GGTCJDatum
import CFSG.LocalAnalysis.StandardType.GGTCJCoverGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.GLTheoremA (canonLabel)


theorem ggOrthEnnola_component_label_field
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hRig : GGLabelRigidInput) {Bs X J : Subgroup G} {x : G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hrow : ∀ lab, S p lab → ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)
    (hmark : GGInnerDiagOnLabel S p Bs X) (hx : x ∈ Bs) (hxp : x ^ p = 1)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G))) :
    ∃ lab labJ : LargeEvenLabel, LargeEvenInLambda2 lab ∧ S p lab ∧
      GGHasLabel lab (X ⧸ Subgroup.center X) ∧ LargeEvenInLambda2 labJ ∧
      (canonLabel labJ).n = lab.n ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) := by
  classical
  have hM := ggMarking_and_labelAll_dep
    (fun lab hlab => TCJ.ggTCJ_datum_marking hlab) hmark
  obtain ⟨-, lab, hlab, hraw⟩ := hM
  have hhasX : GGHasLabel lab (X ⧸ Subgroup.center X) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro _ _ _ _ ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  obtain ⟨R, hR, I, F, hs, hna, θ, ⟨⟨hS, hN, hind⟩, hdatum⟩⟩ :=
    largeEvenRawDatum_exists hraw
  letI : Group R := hR
  letI : Finite R := hdatum.1
  letI : IsSimpleGroup R := hs
  have hcen : Subgroup.center R = ⊥ :=
    center_eq_bot_of_isSimpleGroup_of_nonabelian hna
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := hN hx
  let α : MulAut ↥X := X.normalizerMonoidHom ⟨x, hxN⟩
  have hα : α ^ p = 1 := by
    change X.normalizerMonoidHom ⟨x, hxN⟩ ^ p = 1
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (X : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hxp)
    rw [h1, map_one]
  let ψ : ↥X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hker : ψ.ker ≤ Subgroup.center ↥X := by
    intro l hl
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : X ⧸ Subgroup.center X) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hx)
  have hφind : ∀ l : ↥X, φ (ψ l) = ψ (α l) := by
    intro l
    apply hφ l (α l)
    change ((X.normalizerMonoidHom ⟨x, hxN⟩ l : ↥X) : G) =
      x⁻¹⁻¹ * (l : G) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hφKind := (hdatum.2 hna).2 φ hφI
  have hJα := ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hJ
  obtain ⟨labJ, hlabJ, hfield, hhasJ⟩ :=
    TCJ.ggTCJ_cover_prop ψ hψ hker α hα φ hφind
      (fun Y _ => ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
        (canonLabel labJ).n = lab.n ∧ GGHasLabel labJ Y)
      (fun _ _ _ _ e h => by
        obtain ⟨labJ, hlabJ, hn, hh⟩ := h
        exact ⟨labJ, hlabJ, hn, ggHasLabel_of_mulEquiv e hh⟩)
      (fun hφp K hK => by
        obtain ⟨labJ, hlabJ, hhas⟩ := TCJ.tcj_component_hasLabel p hp hp2 lab φ K
          hlab hcen hφKind hφp hK
        have hfield := TCJ.tcjOrth_ennola_n_eq_of_ggLabelRigidInput hRig R p φ K lab labJ
          (hrow lab hS) hp hp2 hcen hφKind hφp hhas
          (by simpa only [← TCJ.tcj_ggFixSub_eq_fixSubgroup] using hK)
        exact ⟨labJ, hlabJ, hfield, TCJ.tcj_ggHasLabel_of_hasLabel hhas⟩)
      (J.subgroupOf X) hJα
  have hJX : J ≤ X := hJ.1.trans inf_le_left
  refine ⟨lab, labJ, hlab, hS, hhasX, hlabJ, hfield, ?_⟩
  exact ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJX)
    (Subgroup.map_center_eq _)) hhasJ

theorem GGConfig.not_unitary_higher_of_D4two_component
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {X : Subgroup G}
    (hnb : GGNbr 3 B x D J y X)
    (hmarkX : GGInnerDiagOnLabel
      (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) 3 Bs X)
    (hmarkL : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ 2 ≤ lab.n) 3 Bs L)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G))) : False := by
  obtain ⟨labL, labJL, hlabL, hrowL, -, hlabJL, hdiv, hhasJL⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hmarkL hnb
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx : x ∈ Bs := hcfg.2.1.1 hSS.2.1
  have hxp : x ^ 3 = 1 := hSS.1.1.2 x hSS.2.1
  obtain ⟨labX, labJX, -, hrowX, -, hlabJX, hfield, hhasJX⟩ :=
    ggOrthEnnola_component_label_field Nat.prime_three (by decide) hRig
      (fun _ hl => Or.inl hl.1) hmarkX hx hxp hJ
  have hiso := hRig labJL labJX (J ⧸ Subgroup.center J) hlabJL hlabJX hhasJL hhasJX
  have hcanon := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso
  have hone : (canonLabel labJL).n = 1 :=
    (congrArg LargeEvenLabel.n hcanon).trans (hfield.trans hrowX.2.1)
  have hLone : labL.n = 1 := Nat.dvd_one.mp (hone ▸
    hdiv.trans (TCJ.tcjLabel_n_dvd_canonLabel_n hlabJL))
  have := hrowL.2
  omega

end CFSG.StandardType

end
