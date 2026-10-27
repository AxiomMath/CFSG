module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec13.Item134HoldsTools
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

@[expose] def IsHJPoint (A : Subgroup G) (F : Subgroup G) : Prop :=
  ∃ x : G, F = Subgroup.zpowers x ∧ ∃ Lx ∈ lA A x,
    Nonempty (↥Lx ⧸ aschbacherSolvableCore 3 ↥Lx ≃* CFSG.Blueprint.NativeSporadic.J2)

theorem nonempty_quot_map_conj {L : Subgroup G} (w : G)
    (hj : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Nonempty (↥(L.map (MulAut.conj w).toMonoidHom) ⧸
      aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w).toMonoidHom) ≃*
        CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨φ⟩ := hj
  let e : ↥L ≃* ↥(L.map (MulAut.conj w).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj w).injective
  have hmap : (aschbacherSolvableCore 3 ↥L).map e.toMonoidHom =
      aschbacherSolvableCore 3 ↥(L.map (MulAut.conj w).toMonoidHom) :=
    CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e
  exact ⟨(QuotientGroup.congr _ _ e hmap).symm.trans φ⟩

theorem hjPoint_conj {A F : Subgroup G} (hF : IsHJPoint A F) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    IsHJPoint A (F.map (MulAut.conj w).toMonoidHom) := by
  obtain ⟨x, rfl, Lx, hLx, hj⟩ := hF
  refine ⟨w * x * w⁻¹, ?_, Lx.map (MulAut.conj w).toMonoidHom,
    (map_conj_mem_lA_iff hw).mpr hLx, nonempty_quot_map_conj w hj⟩
  rw [MonoidHom.map_zpowers]
  rfl


theorem omega_cases_of_lbConfig (h134 : Item134) (h48 : Sec4.Item4_8)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G}
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    omegaA A = {Subgroup.zpowers b} ∨
      ((∀ e ∈ Subgroup.zpowers d, Subgroup.zpowers (b * e) ∈ omegaA A) ∧
        ∀ F ∈ omegaA A, IsHJPoint A F) := by
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
  have hbHJ : IsHJPoint A (Subgroup.zpowers b) := ⟨b, rfl, Lb, hLb, hJ⟩
  have hPN : oThreeWPre A ≤ Subgroup.normalizer (A : Set G) := fun w hw =>
    (Holds134.mem_oThreeWPre_iff.mp hw).1
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, hWd, hab, h9, -, hΩ⟩ | ⟨-, hWd, hΩ, h12⟩
  · exact Or.inl h1
  · refine Or.inr ⟨(Sec15.Proof152ResW.omegaA_facts_of_case2 hA hbA hb1 hdA hd1 hdb hWd hab h9
      ?_).2, ?_⟩
    · rcases hΩ with h3 | ⟨I, -, -, -, a, haAK, had, hΩe, h6, -⟩
      · exact Or.inl h3
      · exact Or.inr ⟨a, haAK.1, had, hΩe, h6⟩
    · intro F hF
      rcases hΩ with ⟨h3, -⟩ | ⟨I, -, -, -, a, -, -, hΩe, -, La, hLaeq, hLaJ⟩
      · rw [h3] at hF
        obtain ⟨w, hw, rfl⟩ := hF
        exact hjPoint_conj hbHJ (hPN hw)
      · rw [hΩe] at hF
        rcases hF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
        · exact hjPoint_conj hbHJ (hPN hw)
        · exact hjPoint_conj ⟨a, rfl, La, hLaeq ▸ Set.mem_singleton La, hLaJ⟩ (hPN hw)
  · refine Or.inr ⟨(Sec15.Proof152ResW.omegaA_facts_of_case3 hA hbA hb1 hdA hd1 hdb hWd hΩ
      h12).2, ?_⟩
    intro F hF
    rw [hΩ] at hF
    obtain ⟨w, hw, rfl⟩ := hF
    exact hjPoint_conj hbHJ hw

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
