module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import CFSG.LocalAnalysis.WeakClosure81.EightFour
public import CFSG.HardMathSupport.Solomon.Coordinator.B0TSylow
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal.TwoGroupNormalizerMaxLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.RankThreeUC.SourceSetting
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1611_normalizer_le_of_noncyclic (D : Data G) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : Hyp125 D V₀ V) {p : ℕ} (hp : p ∈ D.sig) {X : Subgroup G}
    (hXM : X ≤ D.M) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X)
    (hXW : X ≤ normalizer (E3.wClos V 0 D.T : Set G)) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hVT : V ≤ D.T := TwelveTwentyTwo.le_T_of_hyp125 h
  have hVW : V ≤ E3.wClos V 0 D.T := by
    rw [wClos_zero_eq_iSup hV]
    exact le_iSup₂_of_le (1 : G) (by rwa [conjSubgroup_one]) (by rw [conjSubgroup_one])
  have hne : E3.wClos V 0 D.T ≠ ⊥ := fun hbot =>
    h.inCalV.1 (le_bot_iff.1 (hbot ▸ hVW))
  have h2 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    IsPGroup.to_le (TwelveTwentyTwo.isPGroup_T D) (wClos_zero_le V D.T)
  exact TwoGroupNormalizerMaxLocal.normalizer_le_of_maxTwoLocalsContaining_eq_singleton hne h2
    hXW (h61 p hp X hXM hXp hXc)

theorem s16c1611_ctilde_normal (D : Data G) {V₀ V : Subgroup G}
    (hP : PairFacts D.M V₀ V) :
    ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := by
  have hC_le_M : F11.CTilde D.M V₀ V ≤ D.M := uc22p22q_ctilde_le
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_M]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨uc22p22q_ctilde_conj_mem hP.le_normalizer hP.le_normalizer₀ hm,
    fun hc => by
      have h := uc22p22q_ctilde_conj_mem hP.le_normalizer hP.le_normalizer₀
        (D.M.inv_mem hm) hc
      simpa [mul_assoc] using h⟩

theorem s16c1611_wClos_normalizer (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V)
    (hA : ∀ g : G, conjSubgroup V g ≤ D.T → conjSubgroup V g ≤ F11.CTilde D.M V₀ V) :
    D.M ⊓ normalizer ((D.T ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G) ≤
      normalizer (E3.wClos V 0 D.T : Set G) := by
  let Q₀ : Subgroup G := D.T ⊓ F11.CTilde D.M V₀ V
  have hWQ : E3.wClos V 0 D.T = E3.wClos V 0 Q₀ := by
    refine le_antisymm ?_ ?_
    · rw [wClos_zero_eq_iSup hV, wClos_zero_eq_iSup hV]
      refine iSup₂_le fun g hg => le_iSup₂_of_le g (le_inf hg (hA g hg)) le_rfl
    · rw [wClos_zero_eq_iSup hV, wClos_zero_eq_iSup hV]
      refine iSup₂_le fun g hg => le_iSup₂_of_le g (fun x hx => (hg hx).1) le_rfl
  intro n hn
  rw [← conjSubgroup_eq_iff_mem_normalizer, hWQ]
  refine wClos_zero_isWeaklyClosedIn hV n ?_
  calc conjSubgroup (E3.wClos V 0 Q₀) n ≤ conjSubgroup Q₀ n :=
        Subgroup.map_mono (wClos_zero_le V Q₀)
    _ = Q₀ := conjSubgroup_eq_iff_mem_normalizer.mpr hn.2

theorem s16c1611_frattini (D : Data G) {V₀ V : Subgroup G}
    [((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] :
    D.M ≤ (D.M ⊓ normalizer ((D.T ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G)) ⊔
      F11.CTilde D.M V₀ V := by
  let Q₀ : Subgroup G := D.T ⊓ F11.CTilde D.M V₀ V
  let N₀ : Subgroup G := D.M ⊓ normalizer (Q₀ : Set G)
  have hC_le_M : F11.CTilde D.M V₀ V ≤ D.M := uc22p22q_ctilde_le
  obtain ⟨Q, hQ⟩ := D.sylowM
  have hfr : Subgroup.normalizer ((((Q : Subgroup ↥D.M) ⊓
      (F11.CTilde D.M V₀ V).subgroupOf D.M : Subgroup ↥D.M)) : Set ↥D.M) ⊔
        (F11.CTilde D.M V₀ V).subgroupOf D.M = ⊤ := by
    obtain ⟨P, hP_map⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_sylow_inf_normal Q
      ((F11.CTilde D.M V₀ V).subgroupOf D.M)
    simpa [hP_map] using
      Sylow.normalizer_sup_eq_top (N := (F11.CTilde D.M V₀ V).subgroupOf D.M) (P := P)
  have hPmap : (((Q : Subgroup ↥D.M) ⊓ (F11.CTilde D.M V₀ V).subgroupOf D.M).map
      D.M.subtype) = Q₀ := by
    rw [Subgroup.map_inf _ _ D.M.subtype D.M.subtype_injective, hQ,
      Subgroup.map_subgroupOf_eq_of_le hC_le_M]
  have hnorm_le : (Subgroup.normalizer (((Q : Subgroup ↥D.M) ⊓
      (F11.CTilde D.M V₀ V).subgroupOf D.M))).map D.M.subtype ≤ N₀ := by
    refine le_inf ?_ ?_
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      exact y.2
    · calc (Subgroup.normalizer (((Q : Subgroup ↥D.M) ⊓
            (F11.CTilde D.M V₀ V).subgroupOf D.M))).map D.M.subtype
          ≤ Subgroup.normalizer ((((Q : Subgroup ↥D.M) ⊓
            (F11.CTilde D.M V₀ V).subgroupOf D.M).map D.M.subtype)) :=
            Subgroup.le_normalizer_map (H := ((Q : Subgroup ↥D.M) ⊓
              (F11.CTilde D.M V₀ V).subgroupOf D.M)) D.M.subtype
      _ = Subgroup.normalizer (Q₀ : Set G) := by rw [hPmap]
  have hfr' := congrArg (Subgroup.map D.M.subtype) hfr
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.map_subgroupOf_eq_of_le hC_le_M] at hfr'
  have hsup : N₀ ⊔ F11.CTilde D.M V₀ V = D.M := by
    refine le_antisymm (sup_le inf_le_left hC_le_M) ?_
    calc D.M = (Subgroup.normalizer (((Q : Subgroup ↥D.M) ⊓
          (F11.CTilde D.M V₀ V).subgroupOf D.M))).map D.M.subtype ⊔
          F11.CTilde D.M V₀ V := hfr'.symm
      _ ≤ N₀ ⊔ F11.CTilde D.M V₀ V := sup_le (hnorm_le.trans le_sup_left) le_sup_right
  exact hsup.symm.le

theorem s16c1611_exists_noncyclic_le_normalizer (D : Data G) (hin : In10 D)
    {V₀ V : Subgroup G} (h125 : Hyp125 D V₀ V) (hcardV₀ : Nat.card V₀ ≤ 4) {p : ℕ}
    (hp : p ∈ D.sig) :
    ∃ X : Subgroup G,
      X ≤ D.M ⊓ normalizer ((D.T ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G) ∧
      IsPGroup p X ∧ ¬ IsCyclic X := by
  have hP : PairFacts D.M V₀ V := h125.pairFacts
  haveI hCn : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    s16c1611_ctilde_normal D hP
  let Q₀ : Subgroup G := D.T ⊓ F11.CTilde D.M V₀ V
  let N₀ : Subgroup G := D.M ⊓ normalizer (Q₀ : Set G)
  have hM_le : D.M ≤ N₀ ⊔ F11.CTilde D.M V₀ V :=
    s16c1611_frattini D (V₀ := V₀) (V := V)
  have hprime : p.Prime := (D.sig_prime p hp).1
  have h11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 hin.h127 h125
  have hCrank : CFSG.Open.pRank p (F11.CTilde D.M V₀ V) ≤ 1 :=
    uc22p22q_pRank_ctilde_le_one D hin.h61 h11 hcardV₀ hp
  have h3rank : 3 ≤ CFSG.Open.pRank p D.M := hin.hx.three_le p hp
  have hMBrank : CFSG.Open.pRank p D.M - 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) :=
    uc22p22q_pRank_sub_one_le (M := D.M) (C := F11.CTilde D.M V₀ V) (p := p) hprime hCrank
  have h2MB : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) := by omega
  obtain ⟨E, -, hEea, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hprime
      (⊤ : Subgroup (F11.MBar11 D.M V₀ V))
  have hEp : IsPGroup p E := hEea.isPGroup
  have hEc : ¬ IsCyclic E := by
    intro hcyc
    have hexp : Monoid.exponent E ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hEea.2 x x.2)
    rw [IsCyclic.exponent_eq_card, hEcard] at hexp
    have hle : p ^ CFSG.Open.pRank p (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) ≤ p :=
      Nat.le_of_dvd hprime.pos hexp
    have hp2 : p ^ 2 ≤ p := (Nat.pow_le_pow_right hprime.pos h2MB).trans hle
    have hlt : p < p ^ 2 := by nlinarith [hprime.two_le]
    exact absurd hp2 (not_le.mpr hlt)
  let g : ↥N₀ →* F11.MBar11 D.M V₀ V :=
    (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)).comp
      (Subgroup.inclusion inf_le_left)
  have hg : Function.Surjective g := by
    have hC_le_M : F11.CTilde D.M V₀ V ≤ D.M := uc22p22q_ctilde_le
    have hnormC : D.M ≤ normalizer (F11.CTilde D.M V₀ V : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_M).mp hCn
    have hNC : N₀ ≤ normalizer (F11.CTilde D.M V₀ V : Set G) := inf_le_left.trans hnormC
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective
      ((F11.CTilde D.M V₀ V).subgroupOf D.M) y
    have hmul : (m : G) ∈ ((N₀ : Set G) * (F11.CTilde D.M V₀ V : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right N₀ (F11.CTilde D.M V₀ V) hNC]
      exact hM_le m.2
    obtain ⟨n, hnN, c, hcC, hnc⟩ := Set.mem_mul.1 hmul
    refine ⟨⟨n, hnN⟩, ?_⟩
    have hcM : c ∈ D.M := hC_le_M hcC
    have hnM : n ∈ D.M := hnN.1
    have hmn : (⟨n, hnM⟩ : ↥D.M) * ⟨c, hcM⟩ = m := Subtype.ext hnc
    have hck : QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)
        (⟨c, hcM⟩ : ↥D.M) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
      exact hcC
    change QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)
        (⟨n, hnM⟩ : ↥D.M) =
      QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M) m
    rw [← hmn, map_mul, hck, mul_one]
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨X, -, hXp, hXc⟩ := SpLift.exists_noncyclic_pSubgroup_le g hg (p := p)
    (K := ⊤) (E := E) (by rw [Subgroup.index_top]; exact fun h => hprime.not_dvd_one h) hEp hEc
  exact ⟨X.map N₀.subtype, Subgroup.map_subtype_le (H := N₀) X,
    hXp.map N₀.subtype, SpLift.not_isCyclic_map N₀.subtype N₀.subtype_injective hXc⟩

theorem s16c1611_normalizer_le_of_reduction (D : Data G) (hin : In10 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (hA : ∀ g : G, conjSubgroup V g ≤ D.T → conjSubgroup V g ≤ F11.CTilde D.M V₀ V) :
    normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have h125 : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  have hP : PairFacts D.M V₀ V := h125.pairFacts
  have hVab : IsElemAbelian 2 V := h125.isElemAbelian
  have hcardV₀ : Nat.card V₀ ≤ 4 := by
    rw [card_eq_two_pow_mSub hP.elemAbelian₀.isPGroup]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hc.setting.hyp16.small
      _ = 4 := by norm_num
  have hNle := s16c1611_wClos_normalizer D (V₀ := V₀) (V := V) hVab hA
  obtain ⟨p, hp⟩ := hin.hx.sig_nonempty
  obtain ⟨X, hXN, hXp, hXc⟩ :=
    s16c1611_exists_noncyclic_le_normalizer D hin h125 hcardV₀ hp
  exact s16c1611_normalizer_le_of_noncyclic D hin.h61 hV h125 hp
    (hXN.trans inf_le_left) hXp hXc (hXN.trans hNle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
