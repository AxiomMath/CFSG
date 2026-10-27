module

public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
public import CFSG.RankThree.PartTwo.KFacts.KP14MonomialStructure
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions IsThreeFourPlusTranspositions)

variable {G : Type} [Group G]

theorem dStar_subset_wStar (A : Subgroup G) : dStar A ⊆ wStar A := fun _ hφ => by
  obtain ⟨-, X, -, hφX⟩ := hφ
  exact starOf_le_wStar A X hφX

theorem closure_dStar_le_wStar (A : Subgroup G) : Subgroup.closure (dStar A) ≤ wStar A :=
  (Subgroup.closure_le _).mpr (dStar_subset_wStar A)

theorem conj_mem_dStar_of_mem_wStar [Finite G] {A : Subgroup G} {g : MulAut A}
    (hg : g ∈ wStar A) {φ : MulAut A} (hφ : φ ∈ dStar A) : g * φ * g⁻¹ ∈ dStar A := by
  obtain ⟨w, rfl⟩ := hg
  exact conj_mem_dStar w hφ

theorem not_isMulCommutative_perm_three : ¬ IsMulCommutative (Equiv.Perm (Fin 3)) := by
  intro h
  have := h.is_comm.comm (Equiv.swap 0 1) (Equiv.swap 1 2)
  revert this
  decide

theorem not_isMulCommutative_dihedral_four : ¬ IsMulCommutative (DihedralGroup 4) := by
  intro h
  have := h.is_comm.comm (DihedralGroup.r 1) (DihedralGroup.sr 0)
  revert this
  decide

theorem isMulCommutative_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsMulCommutative X) : IsMulCommutative Y :=
  ⟨⟨fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.is_comm.comm _ _⟩⟩

theorem rank3II_22_7_of (h2131 : Item2131One) (h221 : Item221) (h222 : Item222)
    (h225 : Item225) :
    ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
      Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
        (Nonempty (Subgroup.closure (dStar A) ≃* Equiv.Perm (Fin 4)) ∧
            IsThreeTranspositions (dStarIn A) ∧
            (∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ∃ g ∈ Subgroup.closure (dStar A), g * φ * g⁻¹ = ψ) ∧
            ∃ n : ℕ, 0 < n ∧ Nonempty (L ≃* SL3 n)) ∨
          (Subgroup.closure (dStar A) = wStar A ∧ Nonempty (wStar A ≃* (ℤˣ × Equiv.Perm (Fin 4)))) := by
  intro G _ _ A E U c L hpair hA27
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : IsMulCommutative A := hAe.1
  obtain ⟨f, hWf, G₀, hG₀W, ⟨eG₀⟩⟩ := h2131 G A E U c L hpair hA27
  obtain ⟨-, ⟨φ0, hφ0L, hφ0D⟩, hcase⟩ := h222 G A E U c L hpair
  have hDW := dStar_subset_wStar A
  have hinj := coordGL_injective f
  have hG₀m : G₀.map (coordGL f) ≤ monomial := (Subgroup.map_mono hG₀W).trans hWf
  let eG₀' : G₀.map (coordGL f) ≃* alternatingGroup (Fin 4) :=
    (G₀.equivMapOfInjective _ hinj).symm.trans eG₀
  have hDm : ∀ d ∈ dStar A, coordGL f d ∈ monomial := fun d hd => hWf ⟨d, hDW hd, rfl⟩
  have hDr : ∀ d ∈ dStar A, IsReflectionOn d := fun d hd => hd.1
  have hinv : ∀ g ∈ G₀, ∀ d ∈ dStar A, g * d * g⁻¹ ∈ dStar A :=
    fun g hg d hd => conj_mem_dStar_of_mem_wStar (hG₀W hg) hd
  have hcase0 := hcase φ0 hφ0L hφ0D
  obtain ⟨s, hsL, hsD, t, htL, htD, hst⟩ : ∃ s ∈ starOf A L, s ∈ dStar A ∧
      ∃ t ∈ starOf A L, t ∈ dStar A ∧ s * t ≠ t * s := by
    by_contra hcon
    push Not at hcon
    have hcomm : ((starOf A L : Set (MulAut A)) ∩ dStar A).Pairwise Commute :=
      fun x hx y hy _ => hcon x hx.1 hx.2 y hy.1 hy.2
    have hab : IsMulCommutative (starOf A L) := by
      have h1 := Subgroup.isMulCommutative_closure hcomm
      have hgen := (h222 G A E U c L hpair).1
      rw [← hgen] at h1
      exact h1
    rcases hcase0 with ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, n, -, -, -, -, ⟨e⟩⟩ |
        ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, -, -, ⟨e⟩⟩ | ⟨h81, -⟩
    · exact not_isMulCommutative_perm_three (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · exact not_isMulCommutative_dihedral_four (isMulCommutative_of_mulEquiv e hab)
    · rw [hA27] at h81
      norm_num at h81
  have himg := image_eq_swapRefl_or_eq_monoRefl hAc f hG₀m eG₀' hDm hDr hinv
    ⟨s, hsD, t, htD, hst⟩
  have hmapcl : (Subgroup.closure (dStar A)).map (coordGL f) =
      Subgroup.closure (coordGL f '' dStar A) := MonoidHom.map_closure _ _
  rcases himg with hsw | hmo
  ·
    left
    rw [hsw] at hmapcl
    have hDsw : ∀ d ∈ dStar A, coordGL f d ∈ swapRefl := fun d hd => hsw ▸ ⟨d, hd, rfl⟩
    let e1 : Subgroup.closure (dStar A) ≃* Subgroup.closure swapRefl :=
      ((Subgroup.closure (dStar A)).equivMapOfInjective _ hinj).trans
        (MulEquiv.subgroupCongr hmapcl)
    have hord : ∀ x ∈ dStar A, ∀ y ∈ dStar A, orderOf (x * y) ≤ 3 := by
      intro x hx y hy
      rw [← orderOf_injective (coordGL f) hinj, map_mul]
      have hx2 : coordGL f x * coordGL f x = 1 := by
        rw [← map_mul, ← pow_two, ← (hDr x hx).1, pow_orderOf_eq_one, map_one]
      have hy2 : coordGL f y * coordGL f y = 1 := by
        rw [← map_mul, ← pow_two, ← (hDr y hy).1, pow_orderOf_eq_one, map_one]
      rcases swapRefl_commute_or_cube (hDsw x hx) (hDsw y hy) with hc | h3
      · have h2 : (coordGL f x * coordGL f y) ^ 2 = 1 := by
          rw [pow_two, mul_assoc, ← mul_assoc (coordGL f y), ← hc, mul_assoc, hy2, mul_one,
            hx2]
        exact (orderOf_le_of_pow_eq_one (by norm_num) h2).trans (by norm_num)
      · exact orderOf_le_of_pow_eq_one (by norm_num) h3
    refine ⟨⟨e1.trans swapReflEquiv⟩, ?_, ?_, ?_⟩
    ·
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · intro g x hx
        exact conj_mem_dStar_of_mem_wStar (closure_dStar_le_wStar A g.2) hx
      · intro x hx
        rw [← Subgroup.orderOf_coe]
        exact (hDr _ hx).1
      · exact Subgroup.closure_closure_coe_preimage
      · intro x hx y hy
        rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
        exact (hord _ hx _ hy).trans (by norm_num)
      · intro x hx y hy h4
        rw [← Subgroup.orderOf_coe, Subgroup.coe_mul] at h4
        have := hord _ hx _ hy
        omega
      · intro x hx y hy
        rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
        exact hord _ hx _ hy
    ·
      intro φ hφ ψ hψ
      obtain ⟨g', hg', hconj⟩ := exists_conj_swapRefl (hDsw ψ hψ) (hDsw φ hφ)
      rw [← hmapcl] at hg'
      obtain ⟨g, hg, rfl⟩ := hg'
      refine ⟨g, hg, hinj ?_⟩
      rw [map_mul, map_mul, map_inv]
      exact hconj
    ·
      have hst3 : orderOf (s * t) = 3 := by
        have h3 := hord s hsD t htD
        have hs2 : s * s = 1 := by
          rw [← pow_two, ← (hDr s hsD).1, pow_orderOf_eq_one]
        have ht2 : t * t = 1 := by
          rw [← pow_two, ← (hDr t htD).1, pow_orderOf_eq_one]
        have hne1 : orderOf (s * t) ≠ 1 := by
          intro h1
          apply hst
          have h1' : s * t = 1 := orderOf_eq_one_iff.mp h1
          have : s = t := by
            calc s = s * (t * t) := by rw [ht2, mul_one]
              _ = (s * t) * t := by group
              _ = t := by rw [h1', one_mul]
          rw [this]
        have hne2 : orderOf (s * t) ≠ 2 := by
          intro h2
          apply hst
          have h2' : s * t * (s * t) = 1 := by
            rw [← pow_two, ← h2, pow_orderOf_eq_one]
          have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2
          have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
          have := eq_inv_of_mul_eq_one_left h2'
          rw [mul_inv_rev, hsi, hti] at this
          exact this
        have hpos := orderOf_pos (s * t)
        omega
      have h3L : 3 ∣ Nat.card (starOf A L) := by
        have hmem : s * t ∈ starOf A L := (starOf A L).mul_mem hsL htL
        have := orderOf_dvd_natCard (⟨s * t, hmem⟩ : starOf A L)
        rwa [Subgroup.orderOf_mk, hst3] at this
      obtain ⟨n, hn0, hneven, ⟨eL⟩⟩ : ∃ n : ℕ, 0 < n ∧ Even n ∧
          Nonempty (lBar L ≃* SL3 n) := by
        rcases hcase0 with ⟨-, n, hn0, hneven, he, -, -⟩ | ⟨-, n, -, -, -, -, ⟨e⟩⟩ |
            ⟨-, n, -, -, -, -, ⟨e⟩⟩ | ⟨-, -, -, ⟨e⟩⟩ | ⟨h81, -⟩
        · exact ⟨n, hn0, hneven, he⟩
        · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card] at h3L
          norm_num at h3L
        · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card] at h3L
          norm_num at h3L
        · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card] at h3L
          norm_num at h3L
        · rw [hA27] at h81
          norm_num at h81
      have hLc : L ∈ thetaComponentsAt 3 c :=
        (lZeroStarAt_subset A c) (mem_lThreeStarPairs_iff.mp hpair.mem_pair).2.2.1
      have hperf : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hLc
      have hfin := fun (h : inSubgroup (aschbacherSolvableCore 3) L = ⊥) =>
        (⟨n, hn0, ⟨(mulEquiv_lBar_of_theta_eq_bot h).trans eL⟩⟩ :
          ∃ n : ℕ, 0 < n ∧ Nonempty (L ≃* SL3 n))
      rcases h221 G A E U c L hpair with ⟨h81, -⟩ | ⟨-, h221'⟩
      · rw [hA27] at h81
        norm_num at h81
      rcases h221' with ⟨m, hm0, hmeven, eSp | eU | eSL⟩ | eU5 | ⟨hSL34, -⟩
      · have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hmeven; omega
        have := isSimpleGroup_projSp_two hm2
        exact hfin (inSubgroup_theta_eq_bot_of_mulEquiv hperf eSp.some)
      · have := isSimpleGroup_projSU (m := 4) (n := m) le_rfl hm0
        exact hfin (inSubgroup_theta_eq_bot_of_mulEquiv hperf eU.some)
      · exact ⟨m, hm0, eSL⟩
      · have := isSimpleGroup_projSU (m := 5) (n := 2) (by norm_num) (by norm_num)
        exact hfin (inSubgroup_theta_eq_bot_of_mulEquiv hperf eU5.some)
      · exact hfin (h225 G A E U c L hpair hSL34)
  ·
    right
    rw [hmo, closure_monoRefl] at hmapcl
    have hWD : wStar A ≤ Subgroup.closure (dStar A) := by
      rw [← Subgroup.map_le_map_iff_of_injective hinj, hmapcl]
      exact hWf
    have heq : Subgroup.closure (dStar A) = wStar A :=
      le_antisymm (closure_dStar_le_wStar A) hWD
    refine ⟨heq, ⟨((wStar A).equivMapOfInjective _ hinj).trans
      ((MulEquiv.subgroupCongr (by rw [← heq, hmapcl])).trans monomialEquiv)⟩⟩

end CFSG.RankThree.PartTwo.Sec21
