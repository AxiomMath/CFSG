module

public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec16.Item163ProofY4
import CFSG.RankThree.PartTwo.Sec16.Item162Proof
import CFSG.RankThree.PartTwo.Sec16.Item163StepsPtProofTools
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS

@[expose] def Step163U35K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Case1514Three A (lB A) c L Y →
      ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ L,
        w ∉ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G) ∧
        ∃ b ∈ A ⊓ L, b ≠ 1 ∧
          (∃ R ∈ invariantPiSubgroups (Y ⊓ L ⊓ Subgroup.centralizer ({b} : Set G)) A (piOf 2),
            R ≠ ⊥) ∧
          ∀ R ∈ invariantPiSubgroups
              (Y.map (MulAut.conj w).toMonoidHom ⊓ L ⊓ Subgroup.centralizer ({b} : Set G)) A
              (piOf 2), R = ⊥

@[expose] def Step163U35Conj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), MeetsY4 A (lB A) L Y →
      Case1514Three A (lB A) c L Y →
      ∀ w ∈ Subgroup.normalizer (A : Set G) ⊓ L,
        w ∉ Subgroup.normalizer ((Y ⊓ L : Subgroup G) : Set G) →
          ∃ x ∈ xA A, Y.map (MulAut.conj w).toMonoidHom = Y.map (MulAut.conj x).toMonoidHom

@[expose] def Step163MeetsPoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    (∀ (e : G) (Le : Subgroup G), Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
      IsEmpty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2)) →
    ∀ Y ∈ scriptY0Star A (lB A), ∃ (e : G) (Le : Subgroup G), Subgroup.zpowers e ∈ omegaA A ∧
      Le ∈ lA A e ∧ MeetsY4 A (lB A) Le Y

@[expose] def Step163PtA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ (a : G) (La : Subgroup G),
      Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a → MeetsY4 A (lB A) La Y →
      Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A a →
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) →
        ∃ (a' : G) (La' : Subgroup G), Subgroup.zpowers a' ∈ omegaA A ∧ La' ∈ lA A a' ∧
          La' = (Y ⊓ La') ⊔ CFSG.Open.pCoreOf 2 La'

@[expose] def Step163YaA7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0Star A (lB A), ∀ (a : G) (La : Subgroup G),
      Subgroup.zpowers a ∈ omegaA A → La ∈ lA A a →
      Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* alternatingGroup (Fin 7)) →
      WStarS4 A → TransOmegaThree A a →
      (Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10))) →
      La = (Y ⊓ La) ⊔ CFSG.Open.pCoreOf 2 La → CFSG.Open.pCoreOf 2 La ≠ ⊥ →
        ∃ Ya ∈ scriptY0Star A (lB A), La ≤ Ya ∧ (Ya ≠ Y → QTwoNe A Ya Y)

section Tools

variable {G : Type} [Group G] [Finite G]

theorem exists_point_meetsY4
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L) (h1514 : Item1514HJR)
    (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R)
    (hM : Step163MeetsPoint) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    ∃ (e : G) (Le : Subgroup G), Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
      MeetsY4 A (lB A) Le Y := by
  by_cases hHJ : ∃ (e : G) (Le : Subgroup G), Subgroup.zpowers e ∈ omegaA A ∧ Le ∈ lA A e ∧
      Nonempty (↥Le ⧸ aschbacherSolvableCore 3 ↥Le ≃* CFSG.Blueprint.NativeSporadic.J2)
  · obtain ⟨e, Le, he, hLe, hJ⟩ := hHJ
    have he' : Sec15R G A e Le := sec15R_of_point h he hLe
    have hLeY : Le ≤ Y := le_of_j2 he' hJ (fun c' L' hR' hJ' => h1514 G A c' L' hR' hJ')
      (h1523 G A e Le he') (h153 G A e Le he') (hobs G A e Le he') (h1411 G A e Le he') hY
    exact ⟨e, Le, he, hLe, meetsY4_of_j2 he' hJ (h1523 G A e Le he') hY hLeY⟩
  · exact hM G A c L h (fun e Le he hLe => not_nonempty_iff.mp fun hJ =>
      hHJ ⟨e, Le, he, hLe, hJ⟩) Y hY

omit [Finite G] in
theorem omegaA_ne_singleton_of_trans {A : Subgroup G} {a c : G} (hT : TransOmegaThree A a) :
    omegaA A ≠ {Subgroup.zpowers c} := by
  intro hΩ
  have h1 := hT.1
  rw [hΩ, Set.ncard_singleton] at h1
  omega

end Tools

theorem step163U35_of (hK : Step163U35K) (hC : Step163U35Conj) : Step163U35 := by
  intro G _ _ A c L h Y hY hm h3
  obtain ⟨w, hw, hwY, b, hb, -, ⟨R, hR, hR1⟩, hnone⟩ := hK G A c L h Y hY hm h3
  obtain ⟨x, hx, hxY⟩ := hC G A c L h Y hY hm h3 w hw hwY
  have hxC : x ∈ Subgroup.centralizer (A : Set G) := pPrimeCoreOf_le 3 _ hx
  have hxL : x ∈ Subgroup.normalizer (L : Set G) :=
    xA_le_normalizer_of_mem_lA h h.zpowers_mem_omegaA h.mem_lA hx
  have hxb : x * b = b * x := (Subgroup.mem_centralizer_iff.mp hxC b hb.1).symm
  apply hR1
  refine (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj x).injective).mp
    (hnone _ ⟨?_, isPiSubgroup_map_mulEquiv (MulAut.conj x) hR.2.1, ?_⟩)
  ·
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨⟨hrY, hrL⟩, hrb⟩ := hR.1 hr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hxY]
      exact Subgroup.mem_map_of_mem _ hrY
    · exact (Subgroup.mem_normalizer_iff.mp hxL r).mp hrL
    · have hrb' : r * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp hrb
      show (MulAut.conj x) r ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
      have hcx : Commute x b := hxb
      have hcr : Commute r b := hrb'
      exact ((hcx.mul_left hcr).mul_left hcx.inv_left).eq
  ·
    rw [← Subgroup.map_equiv_normalizer_eq, ← Late.map_conj_eq_of_mem_normalizer
      (Subgroup.centralizer_le_normalizer _ hxC)]
    exact Subgroup.map_mono hR.2.2

theorem step163Pt_of (h1514 : Item1514R) (h1523 : Item1523R) (hM : Step163MeetsPoint)
    (hA7 : Step163PtA7) : Step163Pt := by
  intro G _ _ A c L h hP1 Y hY
  by_cases hHJ : ∃ (a : G) (La : Subgroup G), Subgroup.zpowers a ∈ omegaA A ∧ La ∈ lA A a ∧
      Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.J2)
  · obtain ⟨a, La, ha, hLa, hJ⟩ := hHJ
    exact ⟨a, La, ha, hLa, (h1523 G A a La (sec15R_of_point h ha hLa) hJ Y hY).2⟩
  · obtain ⟨e, Le, he, hLe, hm⟩ := hM G A c L h (fun e Le he hLe => not_nonempty_iff.mp
      fun hJ => hHJ ⟨e, Le, he, hLe, hJ⟩) Y hY
    rcases h1514 G A e Le (sec15R_of_point h he hLe) Y hY hm with ⟨-, hcov, -⟩ |
        ⟨h7, hW, hT, hY'⟩ | h3
    · rw [inf_comm Le Y] at hcov
      exact ⟨e, Le, he, hLe, hcov⟩
    · exact hA7 G A c L h Y hY e Le he hLe hm h7 hW hT hY'
    · exact (hP1 e Le Y he hLe hY hm h3).elim

theorem step163Ya_of
    (h1514 : Item1514R) (h1523 : Item1523R) (h153 : Item153MainR) (hobs : Claim153ObsR)
    (h1411 : Item1411_1R) (h142 : Concl142R) (hM : Step163MeetsPoint) (hA7 : Step163YaA7) :
    Step163Ya := by
  intro G _ _ A c L h Y hY a La ha hLa hcov hO
  have ha' : Sec15R G A a La := sec15R_of_point h ha hLa
  by_cases hΩa : omegaA A = {Subgroup.zpowers a}
  · exact ⟨Y, hY, le_of_cover_of_omegaA_eq_singleton ha' hΩa (h142 G A a La ha')
      (h153 G A a La ha') (hobs G A a La ha') (h1411 G A a La ha') hY hcov,
      fun hne => (hne rfl).elim⟩
  · obtain ⟨e, Le, he, hLe, hm⟩ := exists_point_meetsY4 h (fun G _ _ A c' L' hR' _ =>
      h1514 G A c' L' hR') h1523 h153 hobs h1411 hM hY
    have hne : omegaA A ≠ {Subgroup.zpowers e} := fun hΩ => hΩa (by
      have hae : Subgroup.zpowers a = Subgroup.zpowers e := by
        have := hΩ ▸ ha
        exact this
      rw [hΩ, hae])
    rcases h1514 G A e Le (sec15R_of_point h he hLe) Y hY hm with ⟨-, -, hΩ, -⟩ |
        ⟨h7, hW, hT, hY'⟩ | ⟨-, -, -, hΩ, -⟩
    · exact (hne hΩ).elim
    · obtain ⟨w, hw, haw⟩ := hT.2 (Subgroup.zpowers a) ha
      have hLw : Le.map (MulAut.conj w).toMonoidHom = La :=
        map_conj_eq_of_zpowers ha' he hLe hw haw
      exact hA7 G A c L h Y hY a La ha hLa (nonempty_a7_of_map_conj hLw h7) hW
        (transOmegaThree_of_conj hw hT haw) hY' hcov hO
    · exact (hne hΩ).elim

end CFSG.RankThree.PartTwo.Sec16
