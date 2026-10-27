module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WOmega134
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofPoints
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1511Point

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]


theorem isHJPoint_of_isThreeCentralIn (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {b d : G} {Lb : Subgroup G}
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b)
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hd : IsThreeCentralIn Lb d) :
    ∀ F ∈ omegaA A, Sec14.Ronan148W.IsHJPoint A F := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨hdL, S, hdS, hSd⟩ := hd
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hbo : orderOf b = 3 := by
    have h3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
    rwa [Nat.card_zpowers] at h3
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hbo
    omega
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hLb.1 hJq
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  have hbHJ : Sec14.Ronan148W.IsHJPoint A (Subgroup.zpowers b) := ⟨b, rfl, Lb, hLb, hJ⟩
  have hPN : oThreeWPre A ≤ Subgroup.normalizer (A : Set G) := fun w hw =>
    (Holds134.mem_oThreeWPre_iff.mp hw).1
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hWd, hab, h9, -, hΩ⟩ | ⟨-, hWd, hΩ, h12⟩
  · intro F hF
    rw [h1] at hF
    rw [Set.mem_singleton_iff] at hF
    rw [hF]
    exact hbHJ
  · intro F hF
    rcases hΩ with ⟨h3, -⟩ | ⟨I, -, -, -, a, -, -, hΩe, -, La, hLaeq, hLaJ⟩
    · rw [h3] at hF
      obtain ⟨w, hw, rfl⟩ := hF
      exact Sec14.Ronan148W.hjPoint_conj hbHJ (hPN hw)
    · rw [hΩe] at hF
      rcases hF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
      · exact Sec14.Ronan148W.hjPoint_conj hbHJ (hPN hw)
      · exact Sec14.Ronan148W.hjPoint_conj
          ⟨a, rfl, La, hLaeq ▸ Set.mem_singleton La, hLaJ⟩ (hPN hw)
  · intro F hF
    rw [hΩ] at hF
    obtain ⟨w, hw, rfl⟩ := hF
    exact Sec14.Ronan148W.hjPoint_conj hbHJ hw

theorem false_of_isThreeCentralIn (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    {b d : G} {Lb : Subgroup G}
    (hbΩ : Subgroup.zpowers b ∈ omegaA A) (hLb : Lb ∈ lA A b)
    (hJ : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hd : IsThreeCentralIn Lb d) : False := by
  have hpoint := isHJPoint_of_isThreeCentralIn h134 h48 h hbΩ hLb hJ hdA hd1 hd
    (Subgroup.zpowers c) h.zpowers_mem_omegaA
  obtain ⟨x, hx, Lx, hLx, hJx⟩ := hpoint
  have h3 : 3 ∣ Nat.card L :=
    (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi he hiso).trans
      (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L))
  have hLxL : Lx = L := Proof1515.eq_of_mem_lA_of_zpowers_eq h h3 hx.symm hLx
  rw [hLxL] at hJx
  obtain ⟨ψ⟩ := hJx
  exact KFacts.KS14.ks17J2NotList.1 p e (Proof1515.isoLThreePi_congr ψ hiso)

end CFSG.RankThree.PartTwo.Sec15.Proof1511Point
