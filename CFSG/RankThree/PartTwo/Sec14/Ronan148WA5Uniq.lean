module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec14.Ronan148JUniqueD
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_zpowers_of_theta
    (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {c₁ d₁ : G} {L₁ : Subgroup G}
    (hc₁ : Subgroup.zpowers c₁ ∈ omegaA A) (hL₁ : L₁ ∈ lA A c₁)
    (hJ : Nonempty (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁ ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hd₁A : d₁ ∈ A) (hd₁1 : d₁ ≠ 1) (hcent : IsThreeCentralIn L₁ d₁) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d₁ : Set G) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨hdL, S, hdS, hSd⟩ := hcent
  have hc₁A : c₁ ∈ A := (zpowers_mem_omegaA_iff.mp hc₁).1
  have hc₁3 : Nat.card (Subgroup.zpowers c₁) = 3 := (zpowers_mem_omegaA_iff.mp hc₁).2.1
  have hc₁1 : c₁ ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc₁3
    omega
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L₁) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd₁1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d₁} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd₁1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd₁1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hc₁A hd₁A hc₁1 hL₁.1 hJq
  have hdata : Sec13Data G A c₁ L₁ :=
    { h.toSec13Data with zpowers_mem_omegaA := hc₁, mem_lA := hL₁ }
  rcases h134 G A c₁ L₁ hdata hJ d₁ hd₁A hd₁1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hW, -⟩ | ⟨-, hW, -⟩
  ·
    intro w hw
    have hwc : w ∈ Subgroup.normalizer (Subgroup.zpowers c₁ : Set G) := by
      have h2 : (Subgroup.zpowers c₁).map (MulAut.conj w).toMonoidHom ∈ omegaA A :=
        (map_conj_mem_omegaA_iff hw).mpr hc₁
      rw [h1, Set.mem_singleton_iff] at h2
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    have hco : orderOf c₁ = 3 := by rwa [Nat.card_zpowers] at hc₁3
    have hcL : c₁ ∉ L₁ := (j2_point_facts hdata hJ).1
    have hdc : d₁ ∉ Subgroup.zpowers c₁ := by
      intro hd
      have hd' : d₁ ∈ L₁ ⊓ Subgroup.zpowers c₁ := ⟨hdL, hd⟩
      rw [Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hco hcL,
        Subgroup.mem_bot] at hd'
      exact hd₁1 hd'
    have hwL : w ∈ Subgroup.normalizer (L₁ : Set G) :=
      normalizer_inf_le_of_mem hL₁.1 hL₁.2.1 hL₁.2.2.1 hd₁A hdL hdc ⟨hwc, hw⟩
    have hwdA : w * d₁ * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw d₁).mp hd₁A
    have hwdL : w * d₁ * w⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp hwL d₁).mp hdL
    have hwd1 : w * d₁ * w⁻¹ ≠ 1 := by
      intro h0
      apply hd₁1
      calc d₁ = w⁻¹ * (w * d₁ * w⁻¹) * w := by group
        _ = 1 := by rw [h0]; group
    have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
    have hzz := Item134SylowBarProof.zpowers_eq_of_central_of_quot_j2 h415 hJ hAp hd₁A hwdA hdL
      hwdL hd₁1 hwd1 ⟨S, hdS, hSd⟩
      (Item134SylowBarProof.central_conj hwL hdL ⟨S, hdS, hSd⟩ hwdL)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show (Subgroup.zpowers d₁).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers d₁
    rw [MonoidHom.map_zpowers]
    exact hzz.symm
  · exact hW
  · exact hW

theorem zpowers_eq_of_theta_conj
    (h415 : Sec4.Item4_15) {A B Lb L₁ : Subgroup G} {b d c₁ d₁ : G}
    (hA : Late.IsE27 A) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (hL₁ : L₁ ∈ lA A c₁)
    (hJ₁ : Nonempty (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁ ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hd₁A : d₁ ∈ A) (hd₁1 : d₁ ≠ 1) (hcent₁ : IsThreeCentralIn L₁ d₁)
    {w : G} (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hbw : Subgroup.zpowers c₁ = Subgroup.zpowers (w * b * w⁻¹)) :
    Subgroup.zpowers d = Subgroup.zpowers d₁ := by
  obtain ⟨-, hdB, -, hd1, -⟩ := Main148.lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hL₁' : L₁ ∈ lA A (w * b * w⁻¹) := lA_eq_of_zpowers_eq hbw ▸ hL₁
  have hwi : w⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ hw
  have hL₁b : L₁.map (MulAut.conj w⁻¹).toMonoidHom ∈ lA A b := by
    have h := (map_conj_mem_lA_iff (L := L₁) (c := w * b * w⁻¹) hwi).mpr hL₁'
    have e : w⁻¹ * (w * b * w⁻¹) * w⁻¹⁻¹ = b := by group
    rwa [e] at h
  rw [hc.2.2.1, Set.mem_singleton_iff] at hL₁b
  have hL₁eq : L₁ = Lb.map (MulAut.conj w).toMonoidHom := by
    rw [← hL₁b, Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
      Function.comp_apply, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨x, hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  have hcent : IsThreeCentralIn Lb d := hc.2.2.2.2
  have hcent' := Item148PtRes.isThreeCentralIn_map_conj hcent w
  rw [← hL₁eq] at hcent'
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hwdA : w * d * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw d).mp hdA
  have hwd1 : w * d * w⁻¹ ≠ 1 := by
    intro h0
    apply hd1
    calc d = w⁻¹ * (w * d * w⁻¹) * w := by group
      _ = 1 := by rw [h0]; group
  obtain ⟨hwdL, hc1⟩ := hcent'
  obtain ⟨hd₁L, hc2⟩ := hcent₁
  have h1 := Item134SylowBarProof.zpowers_eq_of_central_of_quot_j2 h415 hJ₁ hAp hwdA hd₁A hwdL
    hd₁L hwd1 hd₁1 hc1 hc2
  have h2 : Subgroup.zpowers (w * d * w⁻¹) = Subgroup.zpowers d := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWd hw)
    rw [MonoidHom.map_zpowers] at h
    exact h
  rw [← h2, h1]

theorem zpowers_eq_of_isLBConfig_of_theta
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {c₁ d₁ : G} {L₁ : Subgroup G}
    (hc₁ : Subgroup.zpowers c₁ ∈ omegaA A) (hL₁ : L₁ ∈ lA A c₁)
    (hJ₁ : Nonempty (↥L₁ ⧸ aschbacherSolvableCore 3 ↥L₁ ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hd₁A : d₁ ∈ A) (hd₁1 : d₁ ≠ 1) (hcent₁ : IsThreeCentralIn L₁ d₁) :
    Subgroup.zpowers d = Subgroup.zpowers d₁ := by
  by_contra hne
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  have hW := HJRes148.normalizer_le_normalizer_zpowers_d h134 h48 h hB hc
  have hW' := normalizer_le_normalizer_zpowers_of_theta h134 h48 h hc₁ hL₁ hJ₁ hd₁A hd₁1 hcent₁
  have hc0 := hc
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨-, hdB, -, -, -⟩ := Main148.lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨hBbd, hbΩ, hLbeq, -, hdL, S, hdS, hSd⟩ := hc
  have hLb : Lb ∈ lA A b := hLbeq ▸ Set.mem_singleton Lb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
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
    ⟨-, -, h1⟩ | ⟨-, -, -, -, h9, -, hΩ⟩ | ⟨-, -, hΩ, -⟩
  ·
    apply hne
    have hc₁' := hc₁
    rw [h1, Set.mem_singleton_iff] at hc₁'
    refine zpowers_eq_of_theta_conj h415 hA hB hc0 hL₁ hJ₁ hd₁A hd₁1 hcent₁
      (Subgroup.normalizer (A : Set G)).one_mem hW ?_
    rw [hc₁']
    congr 1
    group
  ·
    have hor := fun {x : G} (hxA : x ∈ A) (hx1 : x ≠ 1) =>
      Ronan148J.orbitIn_eq_singleton_or_nine_le hA h9 hdA hd₁A hd1 hd₁1 hne hW hW' hxA hx1
    have hfinΩ : (omegaA A).Finite := Set.toFinite _
    rcases hΩ with ⟨hΩeq, hΩ3⟩ | ⟨-, -, -, -, a, ha, had, hΩeq, hΩ6, -⟩
    · rcases hor hbA hb1 with h1 | h1
      · rw [hΩeq, h1, Set.ncard_singleton] at hΩ3
        omega
      · rw [hΩeq] at hΩ3
        omega
    · have ha1 : a ≠ 1 := fun h0 => had (h0 ▸ Subgroup.one_mem _)
      have hle1 : (orbitIn (oThreeWPre A) (Subgroup.zpowers b)).ncard ≤ (omegaA A).ncard :=
        Set.ncard_le_ncard (hΩeq ▸ Set.subset_union_left) hfinΩ
      have hle2 : (orbitIn (oThreeWPre A) (Subgroup.zpowers a)).ncard ≤ (omegaA A).ncard :=
        Set.ncard_le_ncard (hΩeq ▸ Set.subset_union_right) hfinΩ
      rcases hor hbA hb1 with h1 | h1
      · rcases hor ha.1 ha1 with h2 | h2
        · rw [hΩeq, h1, h2] at hΩ6
          have := Set.ncard_union_le ({Subgroup.zpowers b} : Set (Subgroup G))
            {Subgroup.zpowers a}
          rw [hΩ6, Set.ncard_singleton, Set.ncard_singleton] at this
          omega
        · omega
      · omega
  ·
    apply hne
    have hc₁' := hc₁
    rw [hΩ] at hc₁'
    obtain ⟨w, hw, hbw⟩ := hc₁'
    refine zpowers_eq_of_theta_conj h415 hA hB hc0 hL₁ hJ₁ hd₁A hd₁1 hcent₁ hw hW ?_
    rw [hbw, MonoidHom.map_zpowers]
    rfl

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
