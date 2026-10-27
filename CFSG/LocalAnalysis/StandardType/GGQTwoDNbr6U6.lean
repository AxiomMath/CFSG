module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrEsu
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrU6
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrUnit
public import Certificates.Certificate1002
public import Certificates.Certificate1003
public import Certificates.Certificate1009
public import Certificates.Certificate10010
public import Certificates.Certificate10011
public import Certificates.Certificate10015
public import Certificates.Certificate10016
public import Certificates.Certificate10017
public import Certificates.Certificate10018
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosAdapterAux
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Steinberg Matrix

variable {G : Type} [Group G] [Finite G]

section

theorem qtwoDNbr6_u6 (hC : GGSecFiveNSCornerInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) {m : ℕ} (hm : 6 ≤ m ∨ B < Bs) (hcard : Nat.card ↥Bs = 3 ^ m)
    (hFix : QTwoDFixBound Bs X m)
    (hodd6 : m = 6 → B = Bs → GGInnerDiagOnLabel (fun p lab =>
      ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X →
        Odd (Nat.card (Subgroup.center ↥X)))
    (hmark : GGInnerDiagOnLabel (fun p lab =>
      ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X) :
    QTwoDL1Chart 3 B Bs X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨K, hKf, hKfin, lab, m', θ, hK, -, hmrank, hSide, -, hperf, -, hBsN, hbs⟩ :=
    ggNSLieN3A_esuCore hmark (fun p lab hl => hl.1)
  haveI : CharP K 2 := charP_of_card_sq (p := 2) (f := lab.n) hK
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, hn, hr5⟩ := hSide
  change n = 1 at hn
  change rank = 5 at hr5
  change m' = rank + 1 at hmrank
  subst hn
  subst hr5
  have hm6 : m' = 6 := by omega
  subst hm6
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK
  have hBBs : B ≤ Bs := hconf.2.1.1
  have hodd : Odd (Nat.card (Subgroup.center ↥X)) := by
    rcases hBBs.lt_or_eq with hlt | hBeq
    · exact hconf.odd_card_center_of_B_lt_Bs hlt hBsN
    · rcases hm with hm | hlt
      · refine hodd6 ?_ hBeq hmark
        by_contra hne
        have h7 : 3 ^ 7 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
        have htor := qtwoDNbr_u6_toral hcfg hnbr hK' θ hperf hBsN hbs
        rw [hcard] at htor
        have h57 : 3 ^ 5 * 9 ≤ 3 ^ 5 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
          calc 3 ^ 5 * 9 = 3 ^ 7 := by norm_num
            _ ≤ 3 ^ m := h7
            _ ≤ _ := htor
        have h9 := Nat.le_of_mul_le_mul_left h57 (by norm_num)
        have h3 := ggNSPosPD_routeCfg_cent_K (ggRouteCfg_prime hcfg).1 hnbr
        rw [hBeq] at h3
        omega
      · exact absurd hBeq hlt.ne
  obtain ⟨ψ, hker, hrange, hacts⟩ := qtwoDNbr_u6_cover hK' θ hperf hodd hbs hBsN
  exact qtwoDNbr_unit_of_cover hC hcfg hnbr hcard hFix hK' (by norm_num) hker hrange
    (by norm_num) hacts

end

section

open CFSG.Blueprint in
theorem qtwoDNbr6_esu_or (hC : GGSecFiveNSCornerInput) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {y : G} {X : Subgroup G}
    (hnbr : GGNbr 3 B x D J y X) (hJX : J ≤ X) {m : ℕ} (hm : 6 ≤ m ∨ B < Bs)
    (hcard : Nat.card ↥Bs = 3 ^ m) (hFix : QTwoDFixBound Bs X m)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ESU p lab ∧ lab.n = 1) 3 Bs X) :
    QTwoDL1Chart 3 B Bs X ∨ (m = 6 ∧ B = Bs ∧ GGInnerDiagOnLabel (fun p lab =>
      ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) 3 Bs X) := by
  classical
  have hconf : GGConfig 3 B Bs x L D J := hcfg.1.1
  have h2 : GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 3) ∨
      ((ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) ∨
        (ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank ≠ 3 ∧ lab.rank ≠ 5))) 3 Bs X :=
    hmark.mono' fun lab ⟨hl, hn⟩ => by
      by_cases h3 : lab.rank = 3
      · exact Or.inl ⟨hl, hn, h3⟩
      · by_cases h5 : lab.rank = 5
        · exact Or.inr (Or.inl ⟨hl, hn, h5⟩)
        · exact Or.inr (Or.inr ⟨hl, hn, h3, h5⟩)
  rcases GGInnerDiagOnLabel.elim_or h2 with h3 | h56
  ·
    exfalso
    obtain ⟨K, hKf, hKfin, lab, m', θ, hK, -, hmrank, hSide, -, hperf, -, hBsN, -⟩ :=
      ggNSLieN3A_esuCore h3 (fun p lab hl => hl.1)
    obtain ⟨tag, rank, n⟩ := lab
    obtain ⟨-, hn, hr3⟩ := hSide
    change n = 1 at hn
    change rank = 3 at hr3
    change m' = rank + 1 at hmrank
    subst hn
    subst hr3
    have hm4 : m' = 4 := by omega
    subst hm4
    have hKd : LieModel (↥X ⧸ Subgroup.center ↥X) .PSU 4 2 1 :=
      qtwoDNbr_lieModel_of_su hK (le_refl 4) le_rfl θ
    have hxB : x ∈ B := hconf.1.2.2.2.2.2.2.1.2.1
    have hxBs : x ∈ Bs := hconf.2.1.1 hxB
    have hx3 : x ^ 3 = 1 := hconf.2.1.2.1.2 x hxBs
    exact qTwoNbrLabel_four_false hnbr hxBs hx3 hperf hBsN
      (ggIsComponentOf_inf_centralizer_nbr hconf hnbr hJX) hKd
  · rcases GGInnerDiagOnLabel.elim_or h56 with h5 | h6
    · by_cases h6B : m = 6 ∧ B = Bs
      · exact Or.inr ⟨h6B.1, h6B.2, h5⟩
      · exact Or.inl (qtwoDNbr6_u6 hC hcfg hnbr hm hcard hFix
          (fun hm6 hBeq _ => absurd ⟨hm6, hBeq⟩ h6B) h5)
    · exact Or.inl (qtwoDNbr_unit hC hcfg hnbr hcard hFix h6)

end

end CFSG.StandardType.QTwo

end
