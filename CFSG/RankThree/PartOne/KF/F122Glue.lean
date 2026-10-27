module

public import CFSG.RankThree.PartOne.KF.Reduction123
public import CFSG.RankThree.PartOne.KF.F122Lift
public import CFSG.RankThree.PartOne.KF.F122Outer
public import CFSG.RankThree.PartOne.KF.ClsBasic
public import CFSG.RankThree.PartOne.S10.PlaneAuxiliary

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

@[expose] def KF122PSLTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L : Subgroup G), p.Prime → 5 ≤ p →
    CFSG.IsQuasisimple L → (∃ n : ℕ, StatedClassicalModel ↥L .PSL n 2 1) →
    ∀ x : G, x ∈ Subgroup.normalizer (L : Set G) → x ^ p = 1 →
      x ∈ L ⊔ Subgroup.centralizer (L : Set G)

@[expose] def KF122Row (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L : Subgroup G), p.Prime → 5 ≤ p →
    RowModel p L r → LocalRankLeTwo p (↥L ⧸ Subgroup.center ↥L) →
    ∀ α : MulAut (↥L ⧸ Subgroup.center ↥L), α ^ p = 1 →
      α ∉ innerAut (↥L ⧸ Subgroup.center ↥L) →
      LocalRankAut p (↥L ⧸ Subgroup.center ↥L) α → False

@[expose] def KF122RowW (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L : Subgroup G), p.Prime → 5 ≤ p →
    RowModel p L r → LocalRankLeTwo p (↥L ⧸ Subgroup.center ↥L) →
    ∀ α : MulAut (↥L ⧸ Subgroup.center ↥L), α ^ p = 1 →
      α ∉ innerAut (↥L ⧸ Subgroup.center ↥L) →
      ∃ (i : MulAut (↥L ⧸ Subgroup.center ↥L)) (j : ℕ),
        i ∈ innerAut (↥L ⧸ Subgroup.center ↥L) ∧
          ¬ LocalRankAut p (↥L ⧸ Subgroup.center ↥L) (i * α ^ j)

theorem KF122Row.toW {r : ℕ} (h : KF122Row r) : KF122RowW r := by
  intro G _ _ p L hp hp5 hmodel hle α hαp hαinn
  refine ⟨1, 1, Subgroup.one_mem _, fun hra => ?_⟩
  rw [one_mul, pow_one] at hra
  exact h G p L hp hp5 hmodel hle α hαp hαinn hra

theorem kf122_of_rows (hc : KF123Classify) (hpsl2 : KF122PSLTwo)
    (hrows : ∀ r : ℕ, 1 ≤ r → r ≤ 12 → r ≠ 11 → KF122RowW r) : KF122 := by
  classical
  intro G _ _ p hp hp5 L hq hLie hZ hrk hev hplane x hx hxp hxL
  by_cases hL2 : ∃ n : ℕ, StatedClassicalModel ↥L .PSL n 2 1
  · exact absurd (hpsl2 G p L hp hp5 hq hL2 x hx hxp) hxL
  · push Not at hL2
    obtain ⟨A₀, hA₀L, hA₀e, hA₀c, hS⟩ := hplane
    have hA₀C : A₀ ≤ Subgroup.centralizer (A₀ : Set G) := by
      intro a ha b hb
      exact congrArg Subtype.val (hA₀e.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
    obtain ⟨F, hF, hmax⟩ := (Set.toFinite
      {F : Subgroup G | F ≤ L ∧ IsElementaryAbelian p F ∧
        F ≤ Subgroup.centralizer (A₀ : Set G) ∧ A₀ ≤ F}).exists_maximalFor id _
      ⟨A₀, hA₀L, hA₀e, hA₀C, le_rfl⟩
    obtain ⟨hFL, hFe, hFC, hAF⟩ := hF
    have hT : Table123Generic p L A₀ F :=
      { prime := hp
        five_le := hp5
        quasisimple := hq
        evenLie := hLie
        evenRank_le := hev
        center_pPrime := hZ
        localRank_eq := hrk
        not_PSL_two := hL2
        A₀_le := hA₀L
        A₀_elem := hA₀e
        A₀_card := hA₀c
        A₀_invariant := hS
        F_le := hFL
        F_elem := hFe
        A₀_le_F := hAF
        F_le_centralizer := hFC
        F_max := fun F' hF'L hF'e hF'C hFF' =>
          le_antisymm (hmax ⟨hF'L, hF'e, hF'C, hAF.trans hFF'⟩ hFF') hFF' }
    obtain ⟨r, hr1, hr12, hr11, hmodel⟩ := hc G p L A₀ F hT
    set α := centerQuotientConj L ⟨x, hx⟩ with hα
    have hαp : α ^ p = 1 := centerQuotientConj_pow hx hxp
    have hαinn : α ∉ innerAut (↥L ⧸ Subgroup.center ↥L) := by
      rintro ⟨q, hq'⟩
      exact hxL (mem_sup_of_inner hq.1 hx hq'.symm)
    have hLR2 : LocalRankLeTwo p (↥L ⧸ Subgroup.center ↥L) := by
      intro R hR hRc U hU1 hU2 hRU
      have h3 := CFSG.RankThree.PartTwo.Census.le_localRank_of_le_normalizer hp hU1 hU2
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp hR) hRc hRU
      have h4 := hT.localRank_quot_le
      omega
    by_contra hlt
    obtain ⟨i, j, hi, hβ⟩ := hrows r hr1 hr12 hr11 G p L hp hp5 hmodel hLR2 α hαp hαinn
    obtain ⟨t, rfl⟩ := hi
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective t
    apply hβ
    intro hβp hβinn R hRe hRc hRfix U hU1 hU2 hUinv hRU
    have hβ1 : MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * α ^ j ≠ 1 := fun h =>
      hβinn (h ▸ Subgroup.one_mem _)
    obtain ⟨x', hx'N, hx'mem, hx'p, k, hk, hΦ⟩ :=
      exists_lift_pElement hp hq.1 hZ hx hxp l j hβp hβ1
    have hx'L : x' ∉ L := by
      intro hx'L
      have h1 : (MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * α ^ j) ^ k ∈
          innerAut (↥L ⧸ Subgroup.center ↥L) := by
        rw [← hΦ, centerQuotientConj_of_mem (⟨x', hx'L⟩ : L)]
        exact ⟨_, rfl⟩
      obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk).symm hp.one_lt
      apply hβinn
      have h2 : ((MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * α ^ j) ^ k) ^ m =
          MulAut.conj (l : ↥L ⧸ Subgroup.center ↥L) * α ^ j := by
        rw [← pow_mul, pow_eq_pow_mod _ hβp, hm, pow_one]
      rw [← h2]
      exact Subgroup.pow_mem _ h1 m
    have h3 := three_le_localRank_of_fixed_plane hp hZ hx'N hx'p hx'L R hRe hRc
      (fun r hr => by rw [hΦ]; exact pow_apply_eq_of_fix (hRfix r hr) k)
      U hU1 hU2 (fun u hu => by rw [hΦ]; exact pow_apply_mem_of_inv hUinv k u hu) hRU
    have hle : L ⊔ Subgroup.zpowers x' ≤ L ⊔ Subgroup.zpowers x :=
      sup_le le_sup_left ((Subgroup.zpowers_le).mpr hx'mem)
    exact hlt (h3.trans (PlaneAux.localRank_le_of_injective hp (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)))

end CFSG.RankThree.PartOne
