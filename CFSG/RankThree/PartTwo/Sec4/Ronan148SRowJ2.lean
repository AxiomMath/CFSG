module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SSylow
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SCenter

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

theorem card_inf_centralizer_of_isHeisThree {S : Type} [Group S] {P : Subgroup S}
    (hP : IsHeisThree P) :
    Nat.card (P ⊓ Subgroup.centralizer (P : Set S) : Subgroup S) = 3 := by
  obtain ⟨hext3, -, -⟩ := hP
  obtain ⟨-, -, -, hZ3⟩ := hext3
  have hcen : (P ⊓ Subgroup.centralizer (P : Set S)).subgroupOf P = Subgroup.center P := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_center_iff]
    constructor
    · rintro ⟨-, h⟩ g
      exact Subtype.ext (h (g : S) g.2)
    · intro h
      refine ⟨x.2, fun h' hh' => ?_⟩
      exact congrArg Subtype.val (h ⟨h', hh'⟩)
  have h1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : P ⊓ Subgroup.centralizer (P : Set S) ≤ P)).toEquiv
  rw [hcen, hZ3] at h1
  exact h1.symm

theorem typeOrders425_J2_ge : ∀ x ∈ typeOrders425 604800 85, 1080 ≤ x := by
  decide +kernel

section SurvJ2


theorem survJ2_of {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.J2) :
    SurvJ2 S := by
  intro s K hc
  have hSc : Nat.card S = 604800 := by
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_nativeJ2]
  have h81 : ¬ 81 ∣ Nat.card S := by
    rw [hSc]
    norm_num
  obtain ⟨P, -, hsP, hPC⟩ := exists_sylow_le h81 hc.orderOf_eq hc.mem hc.le_centralizer
    hc.isQuasisimple hc.isType
  set Z : Subgroup S := (P : Subgroup S) ⊓ Subgroup.centralizer ((P : Subgroup S) : Set S)
    with hZdef
  have hsZ : s ∈ Z := Subgroup.mem_inf.mpr ⟨hsP, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (hPC hh)⟩
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, -⟩, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 S ⟨e⟩ P Z hZdef _ rfl
  have hZcard : Nat.card Z = 3 := card_inf_centralizer_of_isHeisThree hHeis
  have hZeq : Subgroup.zpowers s = Z := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsZ)
    exact le_of_eq (by rw [Nat.card_zpowers, hc.orderOf_eq, hZcard])
  have hKle : K ≤ Subgroup.centralizer (Z : Set S) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ Subgroup.zpowers s := by
      rw [hZeq]
      exact hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz'
    have hkc : Commute k s := Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer hk)
    exact ((hkc.zpow_right n).eq).symm
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ 604800 :=
    (card_theta_quot_dvd K).trans ((Subgroup.card_subgroup_dvd_card K).trans (dvd_of_eq hSc))
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hc.isQuasisimple)
    (M := 604800) (B := 85) (by norm_num) (by norm_num) hc.isType hdvd
  have hKge : 1080 ≤ Nat.card K :=
    (typeOrders425_J2_ge _ hmem).trans (Nat.le_of_dvd Nat.card_pos (card_theta_quot_dvd K))
  have hCcard : Nat.card (Subgroup.centralizer (Z : Set S)) = 1080 :=
    KFacts.KS14.card_eq_of_isExtOf_alternating_six hext
  have hKeq : K = Subgroup.centralizer (Z : Set S) := by
    apply Subgroup.eq_of_le_of_card_ge hKle
    rw [hCcard]
    exact hKge
  exact isExtOf_congr (MulEquiv.subgroupCongr hKeq.symm) hext

end SurvJ2

section RowJ2

theorem rowOf425_j2
    : RowOf425 (Spor .J2) := by
  rintro S _ _ _ _ ⟨φ⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.J2 ≃* Spor .J2 := b
  have φJ : S ≃* Blueprint.NativeSporadic.J2 := φ.trans b'.symm
  have hSc : Nat.card S = 604800 := by
    rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2]
  have hZS : ∀ (L : Type) [Group L] [Finite L], SectionFourHyp L → IsQuasisimple L →
      IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* S) →
      Subgroup.center L = ⊥ := by
    intro L _ _ hS hL hZ3 ⟨e⟩
    exact center_eq_bot_of_card hS hL hZ3 (N := 604800)
      (by rw [Nat.card_congr e.toEquiv, hSc])
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSL_j2)
      (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) KFacts.KS14.checkSU_j2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact row425_of_survJ2 hZS ⟨φJ⟩ (survJ2_of φJ)

end RowJ2

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
