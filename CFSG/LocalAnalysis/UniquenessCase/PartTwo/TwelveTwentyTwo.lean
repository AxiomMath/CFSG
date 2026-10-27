module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveTwentyTwo

theorem xCond1218_anti {M V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {j j' : ℕ}
    {X : Subgroup G} (hjj : j' ≤ j) (h : XCond1218 M V₀ V hV j X) :
    XCond1218 M V₀ V hV j' X := by
  rcases h with h | ⟨p, hp, hpX, h | h | h⟩
  · exact Or.inl h
  · exact Or.inr ⟨p, hp, hpX, Or.inl h⟩
  · refine Or.inr ⟨p, hp, hpX, Or.inr (Or.inl ?_)⟩
    have : 2 ^ j' ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjj
    omega
  · exact Or.inr ⟨p, hp, hpX, Or.inr (Or.inr h)⟩

theorem inF_mono {Q : Type} [Group Q] [Finite Q] {j j' : ℕ} (hjj : j ≤ j') {K : Subgroup Q}
    (h : F12.InF j K) : F12.InF j' K := by
  intro T hT Ω hΩ hne h1
  have h0 := h T hT Ω hΩ hne h1
  have hTK : T ≤ K := (CFSG.ABGLocalTools.isSylowOf_iff.1 hT).1
  have hle : F12.eGenP j K T Ω ≤ F12.eGenP j' K T Ω := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun L hL => ?_
    refine le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le L ?_ le_rfl))
    obtain ⟨h1, h2, h3, h4⟩ := hL
    refine ⟨h1, h2, h3, ?_⟩
    have hp : 2 ^ j ≤ 2 ^ j' := Nat.pow_le_pow_right (by norm_num) hjj
    rcases h4 with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a, b.trans hp⟩
    · exact Or.inr ⟨a, b.trans hp⟩
  have hEK : F12.eGenP j' K T Ω ≤ K :=
    iSup₂_le fun A _ => iSup_le fun _ => iSup₂_le fun L hL => hL.1
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨e, he, t, ht, rfl⟩
    exact K.mul_mem (hEK he) (hTK ht)
  · rw [← h0]
    exact Set.mul_subset_mul hle subset_rfl

theorem inFSq_mono {j j' : ℕ} (hjj : j ≤ j') {H : Subgroup G} (h : InFSq j H) :
    InFSq j' H := by
  exact inF_mono hjj h

theorem exists_ne_one_mem_inf_center {T W : Subgroup G} (hT : IsPGroup 2 T) (hWT : W ≤ T)
    (hTW : T ≤ normalizer (W : Set G)) (hW : W ≠ ⊥) :
    ∃ z ∈ W, (∀ t ∈ T, z * t = t * z) ∧ z ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥T := hT.isNilpotent
  haveI : (W.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWT).2 hTW
  have hW' : W.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hW
    have hmap := Subgroup.subgroupOf_map_subtype W T
    rw [h0, Subgroup.map_bot, inf_eq_left.2 hWT] at hmap
    exact hmap.symm
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hW')
  refine ⟨z, Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hz).1, fun t ht => ?_, ?_⟩
  · have := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 hz).2 ⟨t, ht⟩
    exact (congrArg Subtype.val this).symm
  · intro h1
    apply hz1
    exact Subtype.ext (Subtype.ext h1)

theorem centralizersUnique_of_hyp125 {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) : CentralizersUnique D.M D.T := by
  rcases h.1 with ⟨-, h0⟩ | ⟨-, hcu, -⟩
  · exact absurd h0 hV₀
  · exact hcu

theorem le_T_of_hyp125 {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) : V ≤ D.T := by
  exact uc22p22p_le_T_of_inCalV D h.inCalV

theorem isPGroup_T (D : Data G) : IsPGroup 2 D.T := by
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).2.1

theorem centralizer_cClos_le {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) (j : ℕ) : centralizer (E3.cClos V j D.T : Set G) ≤ D.M := by
  have hcu := centralizersUnique_of_hyp125 h hV₀
  have hVT := le_T_of_hyp125 h
  have hT1 : D.T ≠ ⊥ := fun e => h.inCalV.1 (le_bot_iff.1 (e ▸ hVT))
  obtain ⟨z, hzT, hzc, hz1⟩ :=
    exists_ne_one_mem_inf_center (isPGroup_T D) le_rfl Subgroup.le_normalizer hT1
  have hzC : z ∈ E3.cClos V j D.T := by
    refine Subgroup.mem_inf.2 ⟨hzT, ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    exact (hzc w (E3.wClos_le j D.T hw)).symm
  refine (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzC)).trans ?_
  exact (hcu z hzT hzc hz1).1

theorem exists_not_le_normalizer_of_uniqueMax {M W : Subgroup G} {Δ : Finset (Subgroup G)}
    (hU : UniqueMax M (⨆ H ∈ Δ, H)) (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hN : ¬ normalizer (W : Set G) ≤ M) : ∃ H ∈ Δ, ¬ H ≤ normalizer (W : Set G) := by
  by_contra hc
  apply hN
  refine uc22p22p_le_of_uniqueMax hU ⟨W, hW, hW2, rfl⟩ ?_
  refine iSup₂_le fun H hH => ?_
  by_contra h'
  exact hc ⟨H, hH, h'⟩

theorem le_conjSubgroup_of_le_centralizer_cClos {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {s : ℕ} (hs : s < rk ↥V) {R : Subgroup G}
    (hR : R ≤ centralizer (E3.cClos V s D.T : Set G)) {g : G}
    (hg : g ∈ normalizer (E3.wClos V s D.T : Set G)) : R ≤ conjSubgroup D.M g := by
  have hcu := centralizersUnique_of_hyp125 h hV₀
  have hV := h.isElemAbelian
  have hVT := le_T_of_hyp125 h
  have hWT : E3.wClos V s D.T ≤ D.T := E3.wClos_le s D.T
  have hW1 : E3.wClos V s D.T ≠ ⊥ := E3.wClos_ne_bot hV hVT hs
  have hTW : D.T ≤ normalizer (E3.wClos V s D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos D.T)
  obtain ⟨z, hzW, hzc, hz1⟩ := exists_ne_one_mem_inf_center (isPGroup_T D) hWT hTW hW1
  have hzZ : z ∈ centerOf (E3.wClos V s D.T) :=
    Subgroup.mem_inf.2 ⟨hzW, mem_centralizer_iff.2 fun w hw => (hzc w (hWT hw)).symm⟩
  have hgZ : g⁻¹ ∈ normalizer (centerOf (E3.wClos V s D.T) : Set G) :=
    E3.normalizer_le_normalizer_centerOf _ (Subgroup.inv_mem _ hg)
  have hy : g⁻¹ * z * g ∈ centerOf (E3.wClos V s D.T) := by
    have := (mem_normalizer_iff.1 hgZ z).1 hzZ
    simpa using this
  have hyC : g⁻¹ * z * g ∈ E3.cClos V s D.T := centerOf_wClos_le_cClos_self s D.T hy
  intro x hx
  rw [mem_conjSubgroup_iff]
  have hxy : (g⁻¹ * z * g) * x = x * (g⁻¹ * z * g) := (mem_centralizer_iff.1 (hR hx)) _ hyC
  apply (hcu z (hWT hzW) hzc hz1).1
  rw [mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff.1 hw]
  calc z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [hxy]
    _ = g * x * g⁻¹ * z := by group

end TwelveTwentyTwo

section Certified

theorem TwelveTwentyTwo.twelve_eighteen_two_three (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {i n : ℕ} {X : Subgroup G} (hXM : X ≤ D.M)
    (hXn : D.M ≤ normalizer (X : Set G)) (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥)
    (hb : bBar X D.M V₀ V h.isElemAbelian < mBar D.M V₀ V h.isElemAbelian - (i + n))
    (hab : XCond1218 D.M V₀ V h.isElemAbelian (i + n) X) {H S : Subgroup G}
    (hS : IsSylowIn 2 S H) :
    (E1.InE n H →
        (H ⊓ normalizer (E3.wClos V i S : Set G)) ⊔
          (H ⊓ centralizer (E3.cClos V (i + n) S : Set G)) = H) ∧
      (InFSq n H →
        H ≤ normalizer (E3.wClos V i S : Set G) ∨
          ⁅E3.cClos V (i + n) S, twoResidual H⁆ = ⊥) := by
  have hemp := twelve_eighteen_empty D hx h61 h127 h1114 h162 hTor h1482 h hV₀ hXM hXn hX1 hb
    hab
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀
  have hH := hW.hyp6H
  have hV := h.isElemAbelian
  have hjm : i + n < mBar D.M V₀ V hH.elemAbelian := by
    have : 0 < mBar D.M V₀ V hV - (i + n) := lt_of_le_of_lt (Nat.zero_le _) hb
    omega
  have hkr : ((i + n : ℕ) : ℕ∞) < rMV D.M V := by
    by_cases hm1 : 1 < mBar D.M V₀ V hV
    · have h1 := h162 D V₀ V hW hx h61 hV₀ hm1
      refine lt_of_lt_of_le ?_ h1
      exact_mod_cast (by omega : i + n < mBar D.M V₀ V hV + mSub V₀)
    · have h0 : i + n = 0 := by omega
      rw [h0]
      exact lt_of_lt_of_le (by norm_num)
        (TwelveEighteen.one_le_rMV (B2F.isPGroup_of_isElemAbelian hV) hH.normalizer_eq)
  have hno : ∀ g : G, ¬ InCalO1 (i + n) D.M V₀ V g := fun g hg => hemp g hg.1
  exact ⟨fun hE => TwelveEighteen.six_thirteen_two_of_no_calO1_gen hH hV₀ le_rfl hkr hjm hno hS hE,
    fun hF => TwelveEighteen.twelve_eighteen_three_of_no_calO1 hH hV₀ le_rfl hkr hjm hno hS hF⟩

theorem twelve_twentyTwo_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {X : Subgroup G} (hXM : X ≤ D.M) (hXn : D.M ≤ normalizer (X : Set G))
    (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥) {i : ℕ}
    (hm : bBar X D.M V₀ V h.isElemAbelian + (i + D.k) < mBar D.M V₀ V h.isElemAbelian)
    (hab : XCond1218 D.M V₀ V h.isElemAbelian (i + D.k) X) :
    ¬ normalizer (E3.wClos V i D.T : Set G) ≤ D.M := by
  obtain ⟨H₀, hmin⟩ := h.exists_hyp124Min
  have hE : E1.InE D.k H₀ := h126 H₀ hmin
  have hT : IsSylowIn 2 D.T H₀ := TwelveShort.isSylowIn_of_le D hmin.1.1
  have hgen := (TwelveTwentyTwo.twelve_eighteen_two_three D hx h61 h127 h1114 h162 hTor h1482 h
    hV₀ hXM hXn hX1 (by omega) hab hT).1 hE
  have hC : H₀ ⊓ centralizer (E3.cClos V (i + D.k) D.T : Set G) ≤ D.M :=
    inf_le_right.trans (TwelveTwentyTwo.centralizer_cClos_le h hV₀ _)
  intro hN
  apply hmin.1.2.1
  rw [← hgen]
  exact sup_le (inf_le_right.trans hN) hC

theorem twelve_twentyTwo_three (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {X : Subgroup G} (hXM : X ≤ D.M) (hXn : D.M ≤ normalizer (X : Set G))
    (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥) {Δ : Finset (Subgroup G)}
    (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H))
    (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSq (ι H) H)
    (hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g)
    (hab : XCond1218 D.M V₀ V h.isElemAbelian (D.k + Δ.sup ι) X) :
    mBar D.M V₀ V h.isElemAbelian ≤ bBar X D.M V₀ V h.isElemAbelian + (D.k + Δ.sup ι) := by
  by_contra hlt
  have hlt' : bBar X D.M V₀ V h.isElemAbelian + (D.k + Δ.sup ι) <
      mBar D.M V₀ V h.isElemAbelian := not_le.1 hlt
  have hV := h.isElemAbelian
  have hk := TwelveShort.one_le_k D
  have hrk : mBar D.M V₀ V hV ≤ rk ↥V := mBar_le_rk hV h.pairFacts.le
  have hN0 : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    twelve_twentyTwo_two D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀ hXM hXn hX1 (by omega)
      (TwelveTwentyTwo.xCond1218_anti (by omega) hab)
  have hNi : ¬ normalizer (E3.wClos V (Δ.sup ι) D.T : Set G) ≤ D.M :=
    twelve_twentyTwo_two D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀ hXM hXn hX1 (by omega)
      (TwelveTwentyTwo.xCond1218_anti (by omega) hab)
  have hVT := TwelveTwentyTwo.le_T_of_hyp125 h
  have hW0 : E3.wClos V 0 D.T ≠ ⊥ := E3.wClos_ne_bot hV hVT (by omega)
  have hW02 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    (TwelveTwentyTwo.isPGroup_T D).to_le (E3.wClos_le 0 D.T)
  obtain ⟨H, hH, hHN⟩ :=
    TwelveTwentyTwo.exists_not_le_normalizer_of_uniqueMax hΔU hW0 hW02 hN0
  have hTH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D (hΔ H hH).1
  have hF : InFSq (Δ.sup ι) H := TwelveTwentyTwo.inFSq_mono (Finset.le_sup hH) (hι H hH)
  have h3 := (TwelveTwentyTwo.twelve_eighteen_two_three D hx h61 h127 h1114 h162 hTor h1482 h
    hV₀ hXM hXn hX1 (i := 0) (n := Δ.sup ι) (by omega)
    (TwelveTwentyTwo.xCond1218_anti (by omega) hab) hTH).2 hF
  rw [zero_add] at h3
  have hC := h3.resolve_left hHN
  rw [Subgroup.commutator_comm] at hC
  have hR : twoResidual H ≤ centralizer (E3.cClos V (Δ.sup ι) D.T : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 hNi
  exact hO2 H hH g hgM
    (TwelveTwentyTwo.le_conjSubgroup_of_le_centralizer_cClos h hV₀ (by omega) hR hgN)

theorem twelve_twentyTwo_three_two (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {X : Subgroup G} (hXM : X ≤ D.M)
    (hXn : D.M ≤ normalizer (X : Set G)) (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥)
    {Δ : Finset (Subgroup G)} (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M)
    (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H)) (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSq (ι H) H)
    (hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g)
    (hmax : Δ.sup ι = 1) (hab : XCond1218 D.M V₀ V h.isElemAbelian (D.k + Δ.sup ι) X)
    (hmj : D.k + Δ.sup ι < mBar D.M V₀ V h.isElemAbelian) :
    mBar D.M V₀ V h.isElemAbelian ≤ bBar X D.M V₀ V h.isElemAbelian + 1 := by
  by_contra hlt
  have hlt' : bBar X D.M V₀ V h.isElemAbelian + 1 < mBar D.M V₀ V h.isElemAbelian :=
    not_le.1 hlt
  have hV := h.isElemAbelian
  have hk := TwelveShort.one_le_k D
  have hrk : mBar D.M V₀ V hV ≤ rk ↥V := mBar_le_rk hV h.pairFacts.le
  rw [hmax] at hab hmj
  have hN1 : ¬ normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M :=
    twelve_ten_one D hx h61 h66 h127 h1114 h183 h hV₀ ((h.mBarGT_iff_lt_mBar _).2 hmj)
  have hN0 : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    fun h0 => hN1 ((normalizer_wClos_anti hV (Nat.zero_le 1) (by omega)).trans h0)
  have hVT := TwelveTwentyTwo.le_T_of_hyp125 h
  have hW0 : E3.wClos V 0 D.T ≠ ⊥ := E3.wClos_ne_bot hV hVT (by omega)
  have hW02 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    (TwelveTwentyTwo.isPGroup_T D).to_le (E3.wClos_le 0 D.T)
  obtain ⟨H, hH, hHN⟩ :=
    TwelveTwentyTwo.exists_not_le_normalizer_of_uniqueMax hΔU hW0 hW02 hN0
  have hTH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D (hΔ H hH).1
  have hF : InFSq 1 H :=
    TwelveTwentyTwo.inFSq_mono ((Finset.le_sup hH).trans hmax.le) (hι H hH)
  have h3 := (TwelveTwentyTwo.twelve_eighteen_two_three D hx h61 h127 h1114 h162 hTor h1482 h
    hV₀ hXM hXn hX1 (i := 0) (n := 1) (by omega)
    (TwelveTwentyTwo.xCond1218_anti (by omega) hab) hTH).2 hF
  rw [zero_add] at h3
  have hC := h3.resolve_left hHN
  rw [Subgroup.commutator_comm] at hC
  have hR : twoResidual H ≤ centralizer (E3.cClos V 1 D.T : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 hN1
  exact hO2 H hH g hgM
    (TwelveTwentyTwo.le_conjSubgroup_of_le_centralizer_cClos h hV₀ (by omega) hR hgN)

theorem twelve_twentyTwo_four (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {X : Subgroup G} (hXM : X ≤ D.M) (hXn : D.M ≤ normalizer (X : Set G))
    (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥) {Δ : Finset (Subgroup G)}
    (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H))
    (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSq (ι H) H)
    (hab : XCond1218 D.M V₀ V h.isElemAbelian (D.k + Δ.sum ι) X) :
    mBar D.M V₀ V h.isElemAbelian ≤ bBar X D.M V₀ V h.isElemAbelian + (D.k + Δ.sum ι) := by
  classical
  by_contra hlt
  have hlt' : bBar X D.M V₀ V h.isElemAbelian + (D.k + Δ.sum ι) <
      mBar D.M V₀ V h.isElemAbelian := not_le.1 hlt
  have hV := h.isElemAbelian
  have hk := TwelveShort.one_le_k D
  have hrk : mBar D.M V₀ V hV ≤ rk ↥V := mBar_le_rk hV h.pairFacts.le
  have hVT := TwelveTwentyTwo.le_T_of_hyp125 h
  have hT2 := TwelveTwentyTwo.isPGroup_T D
  have hNn : ¬ normalizer (E3.wClos V (Δ.sum ι) D.T : Set G) ≤ D.M :=
    twelve_twentyTwo_two D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀ hXM hXn hX1 (by omega)
      (by rwa [Nat.add_comm])
  let P : Finset (Subgroup G) → Prop := fun Γ =>
    ∀ H ∈ Γ, twoResidual H ≤ centralizer (E3.cClos V (Γ.sum ι) D.T : Set G)
  have hP0 : (∅ : Finset (Subgroup G)) ∈ Δ.powerset.filter P :=
    Finset.mem_filter.2 ⟨Finset.empty_mem_powerset Δ, fun H hH => absurd hH (Finset.notMem_empty H)⟩
  obtain ⟨Γ, hΓmem, hΓmax⟩ := Finset.exists_max_image (Δ.powerset.filter P) Finset.card ⟨∅, hP0⟩
  obtain ⟨hΓΔ, hΓP⟩ := Finset.mem_filter.1 hΓmem
  have hΓΔ' : Γ ⊆ Δ := Finset.mem_powerset.1 hΓΔ
  have hΓn : Γ.sum ι ≤ Δ.sum ι := Finset.sum_le_sum_of_subset hΓΔ'
  by_cases hall : ∀ H ∈ Δ, H ∉ Γ → H ≤ normalizer (E3.wClos V (Γ.sum ι) D.T : Set G)
  · set W := E3.wClos V (Γ.sum ι) D.T with hW
    have hW1 : W ≠ ⊥ := E3.wClos_ne_bot hV hVT (by omega)
    have hWT : W ≤ D.T := E3.wClos_le _ D.T
    have hZ1 : centerOf W ≠ ⊥ := E3.centerOf_ne_bot_of_isPGroup (hT2.to_le hWT) hW1
    have hZW : centerOf W ≤ W := inf_le_left
    have hZ2 : IsPGroup 2 (centerOf W) := hT2.to_le (hZW.trans hWT)
    have hTZ : D.T ≤ normalizer (centerOf W : Set G) :=
      (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos D.T)).trans
        (E3.normalizer_le_normalizer_centerOf W)
    have hΔZ : (⨆ H ∈ Δ, H) ≤ normalizer (centerOf W : Set G) := by
      refine iSup₂_le fun H hH => ?_
      by_cases hHΓ : H ∈ Γ
      · have hTH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D (hΔ H hH).1
        have hRZ : twoResidual H ≤ normalizer (centerOf W : Set G) :=
          ((hΓP H hHΓ).trans (Subgroup.centralizer_le (centerOf_wClos_le_cClos_self _ D.T))).trans
            (Subgroup.centralizer_le_normalizer _)
        rw [← sup_twoResidual_eq hTH]
        exact sup_le hTZ hRZ
      · exact (hall H hH hHΓ).trans (E3.normalizer_le_normalizer_centerOf W)
    have hNZ : normalizer (centerOf W : Set G) ≤ D.M :=
      uc22p22p_le_of_uniqueMax hΔU ⟨centerOf W, hZ1, hZ2, rfl⟩ hΔZ
    exact hNn ((normalizer_wClos_anti hV hΓn (by omega)).trans
      ((E3.normalizer_le_normalizer_centerOf W).trans hNZ))
  · obtain ⟨H, hH, hHΓ, hHN⟩ : ∃ H ∈ Δ, H ∉ Γ ∧
        ¬ H ≤ normalizer (E3.wClos V (Γ.sum ι) D.T : Set G) := by
      by_contra hc
      apply hall
      intro H hH hHΓ
      by_contra hHN
      exact hc ⟨H, hH, hHΓ, hHN⟩
    have hθΔ : insert H Γ ⊆ Δ := Finset.insert_subset hH hΓΔ'
    have hθsum : (insert H Γ).sum ι = Γ.sum ι + ι H := by
      rw [Finset.sum_insert hHΓ, Nat.add_comm]
    have hθn : Γ.sum ι + ι H ≤ Δ.sum ι := hθsum ▸ Finset.sum_le_sum_of_subset hθΔ
    have hTH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D (hΔ H hH).1
    have h3 := (TwelveTwentyTwo.twelve_eighteen_two_three D hx h61 h127 h1114 h162 hTor h1482
      h hV₀ hXM hXn hX1 (i := Γ.sum ι) (n := ι H) (by omega)
      (TwelveTwentyTwo.xCond1218_anti (by omega) hab) hTH).2 (hι H hH)
    have hC := h3.resolve_left hHN
    rw [Subgroup.commutator_comm] at hC
    have hRH : twoResidual H ≤ centralizer (E3.cClos V (Γ.sum ι + ι H) D.T : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
    have hθP : P (insert H Γ) := by
      intro H' hH'
      rw [hθsum]
      rcases Finset.mem_insert.1 hH' with rfl | hH'Γ
      · exact hRH
      · exact (hΓP H' hH'Γ).trans
          (Subgroup.centralizer_le (cClos_anti hV (Nat.le_add_right _ _) (by omega) D.T))
    have hcard := hΓmax (insert H Γ) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hθΔ, hθP⟩)
    rw [Finset.card_insert_of_notMem hHΓ] at hcard
    omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
