module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace HJRes148


theorem normalizer_le_normalizer_zpowers_d (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, hLbeq, -, hdL, S, hdS, hSd⟩ := hc
  have hLb : Lb ∈ lA A b := hLbeq ▸ Set.mem_singleton Lb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hLb.1 hJq
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hW, -⟩ | ⟨-, hW, -⟩
  ·
    intro w hw
    have hwb : w ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      have h2 : (Subgroup.zpowers b).map (MulAut.conj w).toMonoidHom ∈ omegaA A :=
        (map_conj_mem_omegaA_iff hw).mpr hbΩ
      rw [h1, Set.mem_singleton_iff] at h2
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    have hbo : orderOf b = 3 := by
      have h3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
      rwa [Nat.card_zpowers] at h3
    have hbL : b ∉ Lb := (j2_point_facts hdata hJ).1
    have hdb : d ∉ Subgroup.zpowers b := by
      intro hd
      have hd' : d ∈ Lb ⊓ Subgroup.zpowers b := ⟨hdL, hd⟩
      rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hbo hbL,
        Subgroup.mem_bot] at hd'
      exact hd1 hd'
    have hwL : w ∈ Subgroup.normalizer (Lb : Set G) :=
      normalizer_inf_le_of_mem hLb.1 hLb.2.1 hLb.2.2.1 hdA hdL hdb ⟨hwb, hw⟩
    have hwdA : w * d * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw d).mp hdA
    have hwdL : w * d * w⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp hwL d).mp hdL
    have hwd1 : w * d * w⁻¹ ≠ 1 := by
      intro h0
      apply hd1
      calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
        _ = 1 := by rw [h0]; group
    have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
    have hzz := Item134SylowBarProof.zpowers_eq_of_central_of_quot_j2 h415 hJ hAp hdA hwdA hdL
      hwdL hd1 hwd1 ⟨S, hdS, hSd⟩
      (Item134SylowBarProof.central_conj hwL hdL ⟨S, hdS, hSd⟩ hwdL)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Subgroup.zpowers d).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers d
    rw [MonoidHom.map_zpowers]
    exact hzz.symm
  · exact hW
  · exact hW

end HJRes148

end CFSG.RankThree.PartTwo.Sec14
