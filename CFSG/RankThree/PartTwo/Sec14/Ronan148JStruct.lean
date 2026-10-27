module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148JComp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MInd
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofImg
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148J

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
  Ronan148M

variable {G : Type} [Group G] [Finite G] {A Y : Subgroup G} [(ker148 A Y).Normal]

theorem img148_deltaZero_le_of_hyperplanes {LB : Subgroup G → Subgroup G}
    (hA : Late.IsE27 A) {T : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}
    (h : ∀ E : Subgroup G, IsHyperplane A E → ∀ R ∈ scriptQZero A LB,
      R ≤ Y ⊓ Subgroup.centralizer (E : Set G) → img148 A Y R ≤ T) :
    img148 A Y (deltaZero A LB Y) ≤ T := by
  set T' : Subgroup G := (T.comap (QuotientGroup.mk' (ker148 A Y))).map (Y ⊔ A).subtype
    with hT'
  have hle : deltaZero A LB Y ≤ T' := by
    rw [deltaZero_eq_iSup hA Y]
    refine iSup₂_le fun E hE => sSup_le fun R hR => ?_
    obtain ⟨hR0, hRY⟩ := hR
    intro g hg
    have hgM : g ∈ Y ⊔ A := Subgroup.mem_sup_left (hRY hg).1
    exact ⟨⟨g, hgM⟩, h E hE R hR0 hRY (mem_img148_iff.mpr ⟨g, hgM, hg, rfl⟩), rfl⟩
  intro x hx
  obtain ⟨g, hgM, hgD, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨m, hm, hmg⟩ := hle hgD
  have : m = ⟨g, hgM⟩ := Subtype.ext hmg
  rw [← this]
  exact hm

theorem le_deltaZero_centPre148 {LB : Subgroup G → Subgroup G} {J R : Subgroup G}
    (hR : R ∈ scriptQZero A LB) (hRY : R ≤ Y)
    (hRc : img148 A Y R ≤ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    R ≤ deltaZero A LB (centPre148 A Y J) := by
  refine le_deltaZero hR fun g hg => mem_centPre148_iff.mpr ⟨hRY hg, hRc ?_⟩
  exact mem_img148_iff.mpr ⟨g, Subgroup.mem_sup_left (hRY hg), hg, rfl⟩

omit [Finite G] in
theorem coprime_card_img148 {R : Subgroup G} (hR : ¬ 3 ∣ Nat.card R) :
    Nat.Coprime 3 (Nat.card (img148 A Y R)) := by
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hR ?_
  refine h3.trans ((Subgroup.card_map_dvd _ _).trans ?_)
  rw [← Subgroup.card_map_of_injective (Y ⊔ A).subtype_injective, Subgroup.subgroupOf_map_subtype]
  exact Subgroup.card_dvd_of_le inf_le_left

omit [Finite G] in
theorem img148_le_centralizer {R E : Subgroup G} (hRE : R ≤ Subgroup.centralizer (E : Set G)) :
    img148 A Y R ≤ Subgroup.centralizer (img148 A Y E : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨g, hgM, hgR, rfl⟩ := mem_img148_iff.mp hx
  obtain ⟨e, heM, heE, rfl⟩ := mem_img148_iff.mp hy
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hRE hgR) e heE

theorem card_img148_of_le {E : Subgroup G} (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hEA : E ≤ A) :
    Nat.card (img148 A Y E) = Nat.card E := by
  unfold img148
  rw [card_map_eq_of_ker148 fun x hx h1 => ?_]
  · exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEA.trans le_sup_right)).toEquiv
  · rw [mk'_ker148_eq_one_iff] at h1
    exact Subtype.ext (eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h1
      (k := 1) (by rw [pow_one]; exact hA3 _ (hEA (Subgroup.mem_subgroupOf.mp hx))))

theorem img148_hyperplane_max (hA : Late.IsE27 A) {E : Subgroup G} (hE : IsHyperplane A E) :
    img148 A Y E ≤ img148 A Y A ∧ img148 A Y E ≠ img148 A Y A ∧
      ∀ H : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y), img148 A Y E ≤ H → H ≤ img148 A Y A →
        H = img148 A Y E ∨ H = img148 A Y A := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hE9 : Nat.card (img148 A Y E) = 9 := by
    rw [card_img148_of_le hA3 hE.1]
    have h := hE.2
    rw [hA.2] at h
    omega
  have hA27 : Nat.card (img148 A Y A) = 27 := (card_img148_of_le (Y := Y) hA3 le_rfl).trans hA.2
  refine ⟨img148_mono hE.1, fun h => by rw [h] at hE9; omega, fun H hEH hHA => ?_⟩
  have h1 : Nat.card (img148 A Y E) ∣ Nat.card H := Subgroup.card_dvd_of_le hEH
  have h2 : Nat.card H ∣ Nat.card (img148 A Y A) := Subgroup.card_dvd_of_le hHA
  rw [hE9] at h1
  rw [hA27] at h2
  have hH : Nat.card H = 9 ∨ Nat.card H = 27 := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num] at h2
    obtain ⟨i, hi, hiH⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
    rw [hiH] at h1 ⊢
    interval_cases i
    · norm_num at h1
    · norm_num at h1
    · left; norm_num
    · right; norm_num
  rcases hH with h9 | h27
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hEH (by rw [h9, hE9])).symm
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hHA (by rw [h27, hA27]))

theorem img148_le_normalizer_of_component (hA : Late.IsE27 A) {LB : Subgroup G → Subgroup G}
    {J R : Subgroup G} (hR : R ∈ scriptQZero A LB)
    (hJc : IsComponent (img148 A Y J)) {j : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hjJ : j ∈ img148 A Y J) (hjA : j ∈ img148 A Y A)
    (hjZ : ∃ y ∈ img148 A Y J, j * y ≠ y * j) :
    img148 A Y R ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  obtain ⟨hRπ, hAR, -⟩ := mem_scriptQ_iff.mp hR.1
  have hR3 : ¬ 3 ∣ Nat.card R := (isPiSubgroup_piCompl_iff Nat.prime_three R).mp hRπ
  have hj3 : j ^ 3 = 1 := (img148_isE27 (Y := Y) hA).1.2 j hjA
  exact le_normalizer_of_mem_component hJc hjJ hjZ hj3 (coprime_card_img148 hR3)
    (img148_le_normalizer hAR hjA)

theorem img148_deltaZero_le_sup_centPre148 (hA : Late.IsE27 A) {LB : Subgroup G → Subgroup G}
    {J : Subgroup G} (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hJc : IsComponent (img148 A Y J)) {j : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hjJ : j ∈ img148 A Y J) (hjA : j ∈ img148 A Y A)
    (hjZ : ∃ y ∈ img148 A Y J, j * y ≠ y * j)
    (hCD : img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ⊔
      img148 A Y A ⊓ img148 A Y J = img148 A Y A) :
    img148 A Y (deltaZero A LB Y) ≤
      img148 A Y J ⊔ img148 A Y (deltaZero A LB (centPre148 A Y J)) := by
  have hAab : ∀ x ∈ img148 A Y A, ∀ y ∈ img148 A Y A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((img148_isE27 (Y := Y) hA).1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAJα : img148 A Y A ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hnorm : ∀ {E C : Subgroup (↥(Y ⊔ A) ⧸ ker148 A Y)}, E ≤ img148 A Y A →
      C ≤ img148 A Y A → E ≤ Subgroup.normalizer (C : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    intro E C hE hC e he
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [hAab e (hE he) c (hC hc), mul_inv_cancel_right]
      exact hc
    · intro hc
      have hcA : c ∈ img148 A Y A := by
        have := (img148 A Y A).mul_mem ((img148 A Y A).mul_mem
          ((img148 A Y A).inv_mem (hE he)) (hC hc)) (hE he)
        simpa [mul_assoc] using this
      rwa [hAab e (hE he) c hcA, mul_inv_cancel_right] at hc
  refine img148_deltaZero_le_of_hyperplanes hA fun E hE R hR hRYE => ?_
  have hRY : R ≤ Y := hRYE.trans inf_le_left
  have hRM : R ≤ Y ⊔ A := hRY.trans le_sup_left
  have hRJ := img148_le_normalizer_of_component hA hR hJc hjJ hjA hjZ
  have hRA : img148 A Y R ≤ ⁅img148 A Y R, img148 A Y A⁆ := by
    rw [← HJRes2.img148_commutator_eq hRM le_sup_right, ← hR.2]
  have hRE : img148 A Y R ≤
      Subgroup.centralizer (img148 A Y E : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_centralizer (hRYE.trans inf_le_right)
  obtain ⟨hEA, hEne, hmax⟩ := img148_hyperplane_max (Y := Y) hA hE
  rcases sup_eq_or_sup_eq hEA hEne hmax inf_le_left inf_le_left hCD with hC | hD
  ·
    refine le_sup_of_le_right (img148_mono ?_)
    refine le_deltaZero_centPre148 hR hRY ?_
    refine le_centralizer_of_forall_inv_mul_mem hRJ (hEA.trans hAJα) hRA hRE fun a ha => ?_
    obtain ⟨e, he, hc⟩ := exists_inv_mul_mem_of_mem_sup (hnorm hEA inf_le_left)
      (hC.symm ▸ ha)
    exact ⟨e, he, hc.2⟩
  ·
    refine le_sup_of_le_left ?_
    refine le_of_forall_inv_mul_mem hAJα hRJ hRA fun a ha => ?_
    obtain ⟨e, he, hu⟩ := exists_inv_mul_mem_of_mem_sup (hnorm hEA inf_le_left)
      (hD.symm ▸ ha)
    refine ⟨e, hEA he, ?_, hu.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (hRE hr) e he).symm

end CFSG.RankThree.PartTwo.Sec14.Ronan148J
