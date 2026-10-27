module

public import CFSG.RankThree.PartTwo.Sec21.Item22Sec7
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
public import CFSG.RankThree.PartOne.S12.AmbientTransport
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartOne.CTP.ExtB

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL specialLinearGroupEquivStatedSL)
open CFSG.RankThree.PartOne (CentrallyLThree CTTorusCondition chainAdj ExtCurtisTitsA
  ExtCurtisTitsCThreeSp ExtCurtisTitsBThree ExtCurtisTitsCThreeU)

theorem two_le_of_pos_of_even {m : ℕ} (hm0 : 0 < m) (hm : Even m) : 2 ≤ m := by
  obtain ⟨k, rfl⟩ := hm
  omega

theorem three_dvd_two_pow_sub_one_of_even {m : ℕ} (hm : Even m) : 3 ∣ 2 ^ m - 1 := by
  obtain ⟨k, rfl⟩ := hm
  have h := Nat.sub_dvd_pow_sub_pow 4 1 k
  have h4 : (4 : ℕ) ^ k = 2 ^ (k + k) := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [one_pow, h4, show (4 : ℕ) - 1 = 3 by norm_num] at h
  exact h

theorem statedClassicalModel_psl_of_mulEquiv_projSL {X : Type} [Group X] {n a : ℕ} (hn : 2 ≤ n)
    (ha : 1 ≤ a) (hna : n = 2 → 2 ≤ a) (e : X ≃* projSL n (GaloisField 2 a)) :
    StatedClassicalModel X .PSL n 2 a := by
  have h4 : n = 2 → 4 ≤ 2 ^ a := fun h =>
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (hna h)
  refine ⟨⟨Nat.prime_two, ha, hn, ?_, ?_⟩, GaloisField 2 a, inferInstance, inferInstance,
    GaloisField.card 2 a (by omega), ⟨e.trans ?_⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    have := h4 h.1
    omega
  · intro h
    simp only [Prod.mk.injEq] at h
    have := h4 h.1
    omega
  · exact ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSL n _)).trans
      (MulEquiv.subgroupCongr (PartOne.projImage_statedSL_eq_projSL n _))).symm

theorem statedClassicalModel_psp_of_mulEquiv_projSp {X : Type} [Group X] {a : ℕ} (ha : 2 ≤ a)
    (e : X ≃* projSp 2 (GaloisField 2 a)) : StatedClassicalModel X .PSp 2 2 a :=
  PartOne.statedClassicalModel_of_equiv e.symm (statedClassicalModel_projSp_two ha)

theorem statedClassicalModel_psu_of_mulEquiv_projSU {X : Type} [Group X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* projSU 4 2 a) : StatedClassicalModel X .PSU 4 2 a :=
  PartOne.statedClassicalModel_of_equiv e.symm (statedClassicalModel_projSU le_rfl ha)

variable {G : Type} [Group G]

theorem centrallyLThree_of_isSLThree {Y : Subgroup G} {n : ℕ} (hn : 1 ≤ n) (h : IsSLThree Y n) :
    CentrallyLThree n Y := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl ⟨GaloisField 2 n, inferInstance, inferInstance, GaloisField.card 2 n (by omega),
      ⟨e.trans (specialLinearGroupEquivStatedSL 3 _)⟩⟩
  · exact Or.inr (statedClassicalModel_psl_of_mulEquiv_projSL (by norm_num) hn (by omega) e)

theorem sup_three_eq_iSup {α : Type*} [CompleteLattice α] (K : Fin 3 → α) :
    K 0 ⊔ K 1 ⊔ K 2 = ⨆ i, K i := by
  refine le_antisymm (sup_le (sup_le (le_iSup K 0) (le_iSup K 1)) (le_iSup K 2))
    (iSup_le fun i => ?_)
  fin_cases i
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem vec_three_eq {α : Type*} (K : Fin 3 → α) : ![K 0, K 1, K 2] = K := by
  funext i
  fin_cases i <;> rfl

theorem chainAdj_fin_three {i j : Fin 3} (h : chainAdj i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  revert h
  revert i j
  unfold chainAdj
  decide

theorem IsChainSystem.commuting {r : ℕ} {E : Subgroup G} {K : Fin r → Subgroup G}
    (hK : IsChainSystem r E K) {i j : Fin r} (hij : i ≠ j) (hadj : ¬ chainAdj i j) :
    K i ≤ Subgroup.centralizer (K j : Set G) ∧ K i ⊓ K j = ⊥ := by
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have h1 : i.val + 1 ≠ j.val := fun h => hadj (Or.inl h)
  have h2 : j.val + 1 ≠ i.val := fun h => hadj (Or.inr h)
  rcases Nat.lt_or_gt_of_ne hv with hlt | hlt
  · have hlt' : i.val + 1 < j.val := by omega
    exact ⟨fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (hK.commute i j hlt' x hx y hy).symm, hK.inf_eq_bot i j hlt'⟩
  · have hlt' : j.val + 1 < i.val := by omega
    exact ⟨fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hK.commute j i hlt' y hy x hx, by rw [inf_comm]; exact hK.inf_eq_bot j i hlt'⟩

theorem IsChainSystem.commuting_zero_two {E : Subgroup G} {K : Fin 3 → Subgroup G}
    (hK : IsChainSystem 3 E K) : K 0 ≤ Subgroup.centralizer (K 2 : Set G) ∧ K 0 ⊓ K 2 = ⊥ :=
  hK.commuting (by decide) (by unfold chainAdj; decide)

theorem relIndex_inf_eq_of_card_eq [Finite G] {E C : Subgroup G} {k : ℕ}
    (h : Nat.card E = k * Nat.card (E ⊓ C : Subgroup G)) : (E ⊓ C).relIndex E = k := by
  have h1 := Subgroup.relIndex_mul_card (E ⊓ C) E
  rw [inf_of_le_left (inf_le_left : E ⊓ C ≤ E)] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h)

theorem IsChainSystem.ctTorusCondition [Finite G] {r : ℕ} {E : Subgroup G}
    {K : Fin r → Subgroup G} (hK : IsChainSystem r E K) : CTTorusCondition 3 E K :=
  ⟨fun i => ⟨hK.split i, relIndex_inf_eq_of_card_eq (hK.index i)⟩, fun i j hij =>
    relIndex_inf_eq_of_card_eq (by rw [hK.index₂ i j hij]; norm_num)⟩

theorem IsChainSystem.center_eq_bot [Finite G] {r : ℕ} {E : Subgroup G}
    {K : Fin r → Subgroup G} (hK : IsChainSystem r E K) (i : Fin r)
    (hX : IsSimpleGroup ↥(⨆ i, K i)) : Subgroup.center ↥(⨆ i, K i) = ⊥ := by
  rcases hX.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(⨆ i, K i)) with h | h
  · exact h
  · exfalso
    have hle : E ≤ Subgroup.centralizer (K i : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hc : (⟨x, hK.le hx⟩ : ↥(⨆ i, K i)) ∈ Subgroup.center ↥(⨆ i, K i) := by
        rw [h]
        exact Subgroup.mem_top _
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, le_iSup K i hy⟩)
    have h3 := hK.index i
    rw [inf_eq_left.mpr hle] at h3
    have hpos : 0 < Nat.card E := Nat.card_pos
    omega

theorem nonempty_quotient_center_mulEquiv_of_center_eq_bot {X Y : Type} [Group X] [Group Y]
    (hZ : Subgroup.center X = ⊥) (e : X ≃* Y) : Nonempty (X ⧸ Subgroup.center X ≃* Y) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩

section Cases

variable [Finite G] {E : Subgroup G} {K : Fin 3 → Subgroup G} {m : ℕ}

theorem curtisTitsRankThree_A_of (hA : ExtCurtisTitsA) (hm0 : 0 < m) (hm : Even m)
    (hK : IsChainSystem 3 E K) (hK2 : ∀ i, Nonempty (K i ≃* projSL 2 (GaloisField 2 m)))
    (h01 : IsSLThree (K 0 ⊔ K 1) m) (h12 : IsSLThree (K 1 ⊔ K 2) m) :
    Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
      projSL 4 (GaloisField 2 m)) := by
  have hm2 := two_le_of_pos_of_even hm0 hm
  have hadj : ∀ i j : Fin 3, chainAdj i j → CentrallyLThree m ↥(K i ⊔ K j) := by
    intro i j h
    rcases chainAdj_fin_three h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact centrallyLThree_of_isSLThree (by omega) h01
    · rw [sup_comm]
      exact centrallyLThree_of_isSLThree (by omega) h01
    · exact centrallyLThree_of_isSLThree (by omega) h12
    · rw [sup_comm]
      exact centrallyLThree_of_isSLThree (by omega) h12
  have hmod := (PartOne.extCurtisTitsA_ambient hA (I := ⨆ i, K i) le_rfl hm2 Nat.prime_three
    (three_dvd_two_pow_sub_one_of_even hm) (isElementaryAbelian_of_isElemAbelian hK.elem) hK.le
    (le_iSup K) rfl
    (fun i => statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => hm2)
      (hK2 i).some)
    (fun _ _ hij hna => hK.commuting hij hna) hadj hK.ctTorusCondition).1
  exact PartOne.projSL_of_statedClassicalModel hmod

theorem curtisTitsRankThree_Sp_of (hSp : ExtCurtisTitsCThreeSp) (hm0 : 0 < m) (hm : Even m)
    (hK : IsChainSystem 3 E K) (hK2 : ∀ i, Nonempty (K i ≃* projSL 2 (GaloisField 2 m)))
    (h01 : IsSLThree (K 0 ⊔ K 1) m)
    (h12 : Nonempty ((K 1 ⊔ K 2 : Subgroup G) ≃* projSp 2 (GaloisField 2 m))) :
    Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
      projSp 3 (GaloisField 2 m)) := by
  have hm2 := two_le_of_pos_of_even hm0 hm
  have hpsl : ∀ i, StatedClassicalModel ↥(K i) .PSL 2 2 m := fun i =>
    statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => hm2) (hK2 i).some
  have hmod : StatedClassicalModel ↥(⨆ i, K i) .PSp 3 2 m :=
    PartOne.extCurtisTitsCThreeSp_ambient hSp hm2 Nat.prime_three
      (three_dvd_two_pow_sub_one_of_even hm) (isElementaryAbelian_of_isElemAbelian hK.elem)
      hK.le (le_iSup K 0) (le_iSup K 1) (le_iSup K 2) (sup_three_eq_iSup K) (hpsl 0) (hpsl 1)
      (hpsl 2) hK.commuting_zero_two (centrallyLThree_of_isSLThree (by omega) h01)
      (statedClassicalModel_psp_of_mulEquiv_projSp hm2 h12.some)
      (by rw [vec_three_eq K]; exact hK.ctTorusCondition)
  have hZ := hK.center_eq_bot 0
    (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ _ _ _ hmod)
  obtain ⟨e⟩ := PartOne.projSp_of_statedClassicalModel hmod
  exact nonempty_quotient_center_mulEquiv_of_center_eq_bot hZ e

theorem curtisTitsRankThree_B_of (hB : ExtCurtisTitsBThree) (hm0 : 0 < m) (hm : Even m)
    (hK : IsChainSystem 3 E K) (h0 : Nonempty (K 0 ≃* projSL 2 (GaloisField 2 m)))
    (h1 : Nonempty (K 1 ≃* projSL 2 (GaloisField 2 m)))
    (h2 : Nonempty (K 2 ≃* projSL 2 (GaloisField 2 (2 * m))))
    (h01 : IsSLThree (K 0 ⊔ K 1) m) (h12 : Nonempty ((K 1 ⊔ K 2 : Subgroup G) ≃* projSU 4 2 m))
    (hstd : ¬ E ⊓ K 1 ≤ Subgroup.centralizer (K 2 : Set G)) :
    ∃ b c : GaloisField 2 m, (∀ s : GaloisField 2 m, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
        projOmegaMinus 3 (GaloisField 2 m) b c) := by
  have hm2 := two_le_of_pos_of_even hm0 hm
  have hmod : StatedClassicalModel ↥(⨆ i, K i) .POmegaMinus 4 2 m :=
    PartOne.extCurtisTitsBThree_ambient hB hm2 Nat.prime_three
      (three_dvd_two_pow_sub_one_of_even hm) (isElementaryAbelian_of_isElemAbelian hK.elem)
      hK.le (le_iSup K 0) (le_iSup K 1) (le_iSup K 2) (sup_three_eq_iSup K)
      (statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => hm2) h0.some)
      (statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => hm2) h1.some)
      (statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => by omega)
        h2.some)
      hK.commuting_zero_two (centrallyLThree_of_isSLThree (by omega) h01)
      (statedClassicalModel_psu_of_mulEquiv_projSU (by omega) h12.some)
      (by rw [vec_three_eq K]; exact hK.ctTorusCondition) hstd
  have hZ := hK.center_eq_bot 0
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus _ _ _ _
      hmod).2
  obtain ⟨b, c, hirr, ⟨e⟩⟩ := PartOne.projOmegaMinus_of_statedClassicalModel hmod
  exact ⟨b, c, hirr, nonempty_quotient_center_mulEquiv_of_center_eq_bot hZ e⟩

theorem curtisTitsRankThree_U_of (hU : ExtCurtisTitsCThreeU) (hm0 : 0 < m) (hm : Even m)
    (hK : IsChainSystem 3 E K) (h0 : Nonempty (K 0 ≃* projSL 2 (GaloisField 2 (2 * m))))
    (h1 : Nonempty (K 1 ≃* projSL 2 (GaloisField 2 (2 * m))))
    (h2 : Nonempty (K 2 ≃* projSL 2 (GaloisField 2 m))) (h01 : IsSLThree (K 0 ⊔ K 1) (2 * m))
    (h12 : Nonempty ((K 1 ⊔ K 2 : Subgroup G) ≃* projSU 4 2 m))
    (hstd : ¬ E ⊓ K 2 ≤ Subgroup.centralizer (K 1 : Set G)) :
    Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
      projSU 6 2 m) := by
  have hm2 := two_le_of_pos_of_even hm0 hm
  exact PartOne.projSU_of_statedClassicalModel
    (PartOne.extCurtisTitsCThreeU_ambient hU hm2 Nat.prime_three
      (three_dvd_two_pow_sub_one_of_even hm) (isElementaryAbelian_of_isElemAbelian hK.elem)
      hK.le (le_iSup K 0) (le_iSup K 1) (le_iSup K 2) (sup_three_eq_iSup K)
      (statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => by omega)
        h0.some)
      (statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => by omega)
        h1.some)
      (statedClassicalModel_psl_of_mulEquiv_projSL le_rfl (by omega) (fun _ => hm2) h2.some)
      hK.commuting_zero_two (centrallyLThree_of_isSLThree (by omega) h01)
      (statedClassicalModel_psu_of_mulEquiv_projSU (by omega) h12.some)
      (by rw [vec_three_eq K]; exact hK.ctTorusCondition) hstd)

end Cases

theorem curtisTitsRankThree_of_ext (hA : ExtCurtisTitsA) (hSp : ExtCurtisTitsCThreeSp)
    (hB : ExtCurtisTitsBThree) (hU : ExtCurtisTitsCThreeU) : CurtisTitsRankThree := by
  intro G _ _ E K m hm0 hm hK
  exact ⟨curtisTitsRankThree_A_of hA hm0 hm hK, curtisTitsRankThree_Sp_of hSp hm0 hm hK,
    curtisTitsRankThree_B_of hB hm0 hm hK, curtisTitsRankThree_U_of hU hm0 hm hK⟩

theorem curtisTitsRankThree_of
    (hU : ExtCurtisTitsCThreeU) : CurtisTitsRankThree :=
  curtisTitsRankThree_of_ext PartOne.CTP.extCurtisTitsA PartOne.CTP.extCurtisTitsCThreeSp
    PartOne.CTP.extCurtisTitsBThree hU

end CFSG.RankThree.PartTwo.Sec21
