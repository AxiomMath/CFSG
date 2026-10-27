module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts
public import CFSG.Quasithin.Vol2.Ch11SecDGroup
public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecAVi
public import CFSG.Quasithin.Vol2.Ch11StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem centralizer_le_normalizer_zpowers (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  intro x hx
  have hxz : Commute x z := Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp [(hxz.zpow_right k).eq]⟩
  · rintro ⟨k, hk⟩
    dsimp only at hk
    refine ⟨k, ?_⟩
    have h1 : x * z ^ k * x⁻¹ = z ^ k := by simp [(hxz.zpow_right k).eq]
    calc z ^ k = x⁻¹ * (x * z ^ k * x⁻¹) * x := by group
      _ = x⁻¹ * (x * g * x⁻¹) * x := by rw [h1, hk]
      _ = g := by group

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem not_le_centralizer_of_isHStar (h331 : Stmt3_3_1) (h : Hyp11 G T L I n)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) {z : G}
    (hzV : z ∈ fsuV T I) (hzL : z ∈ Subgroup.centralizer (L : Set G))
    (hzT : z ∈ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) :
    ¬ H ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hHz
  have hP : IsPGroup 2 (Subgroup.zpowers z) :=
    (SecA.isPGroup_fsuV h).to_le ((Subgroup.zpowers_le).mpr hzV)
  have hP1 : Subgroup.zpowers z ≠ ⊥ := fun h0 =>
    hz1 (Subgroup.mem_bot.mp (h0 ▸ Subgroup.mem_zpowers z))
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    refine sup_le (fun l hl => centralizer_le_normalizer_zpowers z ?_)
      (fun t ht => centralizer_le_normalizer_zpowers z ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzL l hl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT t ht)
  exact hH.2.1 ((hHz.trans (centralizer_le_normalizer_zpowers z)).trans
    (SecA.normalizer_le_of_isPGroup h331 h hP hP1 hLT))

theorem cV_eq_bot (h331 : Stmt3_3_1) (hG2 : SecA.FactG2DerivedOrder) (h1103 : Stmt11_0_3)
    (h1132 : Stmt11_3_2) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  by_contra hne
  obtain ⟨H, hH⟩ := SecA.exists_isHStar h331 h
  have hk : KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n := by
    rcases (h1103 G T L I n h).2.2.1 with ⟨hbot, -⟩ | ⟨hk, -⟩
    · exact absurd hbot hne
    · exact hk
  have hn := h.one_lt
  have hnot : ¬ KindSL3 L (fsuV T I) n := fun hs =>
    hk.elim (SecA.kind_not_SL3_Sp4 (by omega) hs) (SecA.kind_not_SL3_G2 hG2 (by omega) hs)
  have hUT : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ T :=
    inf_le_left.trans (SecA.fsuV_le_T h)
  have hUn : T ≤ Subgroup.normalizer
      ((fsuV T I ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf (SecA.T_le_normalizer_fsuV T I)
      (fun t ht => SecA.mem_normalizer_centralizer (h.normal ht))
  obtain ⟨z, ⟨hzV, hzL⟩, hz1, hzT⟩ :=
    SecD.exists_mem_centralizer_ne_one h.fsu.sylow.1 hUT hUn hne
  have hmoves : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro hc
    have hzZ : z ∈ quasithinOmegaOneCenter T :=
      Subgroup.subset_closure ⟨⟨SecA.fsuV_le_T h hzV, hzT⟩, (SecA.isElemAbelian_fsuV h).2 z hzV⟩
    have hZH := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc hzZ
    refine not_le_centralizer_of_isHStar h331 h hH hzV hzL hzT hz1 fun x hx => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hZH x hx)
  exact hne (h1132 G T L I n V₁ H h hV₁ ⟨hH, hmoves, fun hs => absurd hs hnot⟩).2.2.1

theorem exists_conj_eq (hF : VecTransFacts) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ∀ v ∈ fsuV T I, ∀ w ∈ fsuV T I, v ≠ 1 → w ≠ 1 → ∃ l ∈ L, l * v * l⁻¹ = w := by
  intro v hv w hw hv1 hw1
  obtain ⟨_, -, -, -, hk⟩ := h1102 G T L I n h
  have hsq : ∀ x : ↥(fsuV T I), x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV h).2 x x.2)
  have hn : 2 ≤ n := h.one_lt
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) := ⟨x.2, hx⟩
    rw [hcV] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx'))
  have hv1' : (⟨v, hv⟩ : ↥(fsuV T I)) ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
  have hw1' : (⟨w, hw⟩ : ↥(fsuV T I)) ≠ 1 := fun h1 => hw1 (congrArg Subtype.val h1)
  have key : ∃ g ∈ autOn L (fsuV T I), g ⟨v, hv⟩ = ⟨w, hw⟩ := by
    rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ |
        ⟨-, -, -, -, -, K, _, _, hK, π, hπ⟩
    · rw [hZ] at hπ
      exact hF.sl3 K n hn hK _ hsq _ π hπ _ _ hv1' hw1'
    · rw [hZ] at hπ
      exact hF.sp4 K n hn hK _ hsq _ π hπ _ _ hv1' hw1'
    · rw [hZ] at hπ
      exact hF.g2 K n hn hK _ hsq _ π hπ _ _ hv1' hw1'
  obtain ⟨g, hg, hgv⟩ := key
  obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hg
  refine ⟨l, hl, ?_⟩
  have hval := congrArg Subtype.val hgv
  rwa [SecA.conjV_apply_coe] at hval

theorem stmt11_4_1_one (hF : VecTransFacts) (h331 : Stmt3_3_1) (hG2 : SecA.FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1132 : Stmt11_3_2) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
      ∀ v ∈ fsuV T I, ∀ w ∈ fsuV T I, v ≠ 1 → w ≠ 1 → ∃ l ∈ L, l * v * l⁻¹ = w := by
  have hcV := cV_eq_bot h331 hG2 h1103 h1132 h hV₁
  exact ⟨hcV, exists_conj_eq hF h1102 h hcV⟩

end CFSG.Quasithin.Vol2.Ch11.SecE
