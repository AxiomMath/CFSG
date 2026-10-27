module

public import CFSG.RankThree.PartTwo.Sec14.Item14J2
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item149
public import CFSG.RankThree.PartTwo.Sec13.Statements
import CFSG.RankThree.PartTwo.Sec14.Item14Hyperplanes

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo.Sec13 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem lA_eq_of_zpowers_eq {A : Subgroup G} {b b' : G}
    (h : Subgroup.zpowers b = Subgroup.zpowers b') : lA A b = lA A b' := by
  have hC : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({b'} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq h
  have hT : thetaComponentsAt 3 b = thetaComponentsAt 3 b' := by
    have key : ∀ C₁ C₂ : Subgroup G, C₁ = C₂ →
        (fun L : Subgroup ↥C₁ => L.map C₁.subtype) '' thetaComponents 3 ↥C₁ =
          (fun L : Subgroup ↥C₂ => L.map C₂.subtype) '' thetaComponents 3 ↥C₂ := by
      rintro _ _ rfl
      rfl
    exact key _ _ hC
  have key : ∀ Z₁ Z₂ : Subgroup G, Z₁ = Z₂ → ∀ L : Subgroup G,
      (LocalRank.thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
          (Sec4.autThetaQuot (Subgroup.normalizer (Z₁ : Set G)) L)) ≠ ⊥ ↔
        LocalRank.thetaAlpha 3 ((Sec4.autThetaQuot A L).subgroupOf
          (Sec4.autThetaQuot (Subgroup.normalizer (Z₂ : Set G)) L)) ≠ ⊥) := by
    rintro _ _ rfl _
    rfl
  ext L
  simp only [lA, Set.mem_ofPred_eq, hT]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h ▸ h3, (key _ _ h L).mp h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h ▸ h3, (key _ _ h L).mpr h4⟩

theorem IsLBConfig.ne_one {A B L : Subgroup G} {b d : G} (hc : IsLBConfig A B b d L)
    (hB : IsHyperplane A B) (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) : b ≠ 1 ∧ d ≠ 1 := by
  obtain ⟨hBbd, -, -, -, -⟩ := hc
  have hB9 : Nat.card B = 9 := by
    have := hB.2
    rw [hA.2] at this
    omega
  have hcard3 : ∀ x : G, x ∈ A → Nat.card (Subgroup.zpowers x) ≤ 3 := fun x hx => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.1.2 x hx))
  have hbA : b ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d}))
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  constructor
  · rintro rfl
    have hBz : B = Subgroup.zpowers d := by
      rw [hBbd, Subgroup.zpowers_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact one_mem _
        · exact Subgroup.subset_closure rfl
      · exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl))
    have h3 := hcard3 d hdA
    rw [← hBz, hB9] at h3
    omega
  · rintro rfl
    have hBz : B = Subgroup.zpowers b := by
      rw [hBbd, Subgroup.zpowers_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact Subgroup.subset_closure rfl
        · exact one_mem _
      · exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    have h3 := hcard3 b hbA
    rw [← hBz, hB9] at h3
    omega

omit [Finite G] in
theorem closure_pair_eq_sup (x y : G) :
    Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem IsLBConfig.eq_of_zpowers_eq (h415 : Sec4.Item4_15) {A B B' L L' : Subgroup G}
    {b d b' d' : G} (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) (hc : IsLBConfig A B b d L)
    (hc' : IsLBConfig A B' b' d' L') (hB : IsHyperplane A B) (hB' : IsHyperplane A B')
    (hbb : Subgroup.zpowers b = Subgroup.zpowers b') : B = B' := by
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  obtain ⟨-, hd'1⟩ := hc'.ne_one hB' hA
  obtain ⟨hBbd, -, hLb, hJ2, hdL, S, hdS, hSd⟩ := hc
  obtain ⟨hB'bd, -, hL'b', -, hd'L', S', hd'S', hS'd'⟩ := hc'
  have hLL : L = L' := by
    have h := lA_eq_of_zpowers_eq (A := A) hbb
    rw [hLb, hL'b'] at h
    exact Set.singleton_injective h
  subst hLL
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hd'A : d' ∈ A := hB'.1 (hB'bd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b' rfl))
  have hdd := zpowers_eq_of_central_of_j2 h415 hJ2 hA.isPGroup hdA hd'A hdL hd'L' hd1 hd'1
    ⟨S, hdS, hSd⟩ ⟨S', hd'S', hS'd'⟩
  rw [hBbd, hB'bd, closure_pair_eq_sup, closure_pair_eq_sup, hbb, hdd]

theorem ncard_omegaA_le_twelve (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {B L' : Subgroup G} {b d : G} (hc : IsLBConfig A B b d L')
    (hB : IsHyperplane A B) : (omegaA A).ncard ≤ 12 := by
  have hA : CFSG.RankThree.PartTwo.Late.IsE27 A := h.isE27
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, hLb, ⟨e⟩, hdL, S, hdS, hSd⟩ := hc
  have hbA : b ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d}))
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hL'mem : L' ∈ lA A b := hLb ▸ Set.mem_singleton L'
  have hdata : Sec13Data G A b L' :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hL'mem }
  have hq := h135 G A b L' hdata h.hypS_or_hypT
  have hc0 : Subgroup.center (↥L' ⧸ CFSG.pCore 2 ↥L') = ⊥ := by
    have hmap := Subgroup.map_center_eq e
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  have hθ := aschbacherSolvableCore_eq_pCore_two hq hc0
  have hJ2θ : Nonempty (↥L' ⧸ LocalRank.aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans e⟩
  have hS := center_sylow_eq_zpowers_of_j2 h415 ⟨e⟩ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple h415 ⟨e⟩ hdL hd1 ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hL'mem.1 hJq
  rcases h134 G A b L' hdata hJ2θ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨-, -, h1⟩ | ⟨-, -, -, -, -, -, h2⟩ | ⟨-, -, -, h3⟩
  · rw [h1, Set.ncard_singleton]
    norm_num
  · rcases h2 with ⟨-, h⟩ | ⟨I, -, -, -, a, -, -, -, h, -⟩ <;> omega
  · omega

theorem exists_isHyperplane_lB_eq_bot (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ := by
  have hA : CFSG.RankThree.PartTwo.Late.IsE27 A := h.isE27
  by_contra hall
  push Not at hall
  have hcfg : ∀ B, IsHyperplane A B → ∃ b d L', IsLBConfig A B b d L' := fun B hB => by
    by_contra hno
    push Not at hno
    exact hall B hB (lB_eq_bot hno)
  choose! bB dB LB' hcfgB using hcfg
  obtain ⟨f, -, hf⟩ := exists_hyperplanes_thirteen hA
  have h12 := ncard_omegaA_le_twelve h134 h135 h48 h415 hJ2c h (hcfgB (f 0) (hf 0)) (hf 0)
  refine false_of_injOn_hyperplanes hA h12 (fun B => Subgroup.zpowers (bB B))
    (fun B hB => (hcfgB B hB).2.1) ?_
  intro B B' hB hB' heq
  exact IsLBConfig.eq_of_zpowers_eq h415 hA (hcfgB B hB) (hcfgB B' hB') hB hB' heq

theorem rank3II_14_5_of (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G)) :
    delta A (lB A) Y =
        deltaZero A (lB A) Y ⊔ (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) ∧
      deltaZero A (lB A) Y = ⁅delta A (lB A) Y, A⁆ ∧
      delta A (lB A) Y ≤ Subgroup.normalizer (deltaZero A (lB A) Y : Set G) :=
  rank3II_14_5_lB h.isE27 (exists_isHyperplane_lB_eq_bot h134 h135 h48 h415 hJ2c h) hY

theorem rank3II_15_1_of (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ Sec15.scriptY4 A (lB A)) :
    Y = deltaZero A (lB A) Y :=
  rank3II_15_1_lB h.isE27 (exists_isHyperplane_lB_eq_bot h134 h135 h48 h415 hJ2c h) hY

theorem rank3II_14_9_lB_of (h134 : Item134) (h135 : Item135) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h147 : Item147 A (lB A)) (h148 : Item148Normal A (lB A)) :
    Item149 A (lB A) :=
  rank3II_14_9_of h.isE27 (isNaturalFamily_lB A)
    (exists_isHyperplane_lB_eq_bot h134 h135 h48 h415 hJ2c h) h147 h148

end CFSG.RankThree.PartTwo.Sec14
