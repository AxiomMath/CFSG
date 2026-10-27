module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Transport
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIShortModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitarySpBlock
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.RCKK1IIISp CFSG.LieType.BorelTits CFSG.StandardType.ClassicalPosition

theorem spSiegel_map_of_linear_embedding
    {m n : ℕ} (ι : SpG m →* SpG n)
    (E : SpMod m →ₗ[GaloisField 2 1] SpMod n) (W : Submodule (GaloisField 2 1) (SpMod n))
    (hIso : ∀ x y, spB m x y = spB n (E x) (E y))
    (hAct : ∀ g x, spAct (ι g) (E x) = E (spAct g x))
    (hFix : ∀ g w, w ∈ W → spAct (ι g) w = w)
    (hSplit : ∀ v, ∃ x, ∃ w ∈ W, v = E x + w)
    (hOrth : ∀ x w, w ∈ W → spB n (E x) w = 0)
    {a b : SpMod m} {r : SpG m} (hr : SpSiegel a b r) :
    SpSiegel (E a) (E b) (ι r) := by
  intro v
  obtain ⟨x, w, hw, rfl⟩ := hSplit v
  rw [spAct_add, hAct, hFix r w hw, hr x, map_add, map_add, map_smul, map_smul,
    spB_add_right, spB_add_right, hOrth b w hw, hOrth a w hw, add_zero, add_zero,
    ← hIso b x, ← hIso a x]
  abel

theorem pure_shortRoot_fourGroup_of_fourAt
    {m : ℕ} {J V : Subgroup (SpG m)} {r : SpG m}
    (hFour : FourAt J V r)
    (hroot : ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y r) :
    ∀ v ∈ V, v ≠ 1 → ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y v := by
  obtain ⟨x, y, hxy, hr⟩ := hroot
  intro v hv hv1
  obtain ⟨j, hj, rfl⟩ := hFour.2.2.2.2.2 v hv hv1
  refine ⟨spAct j x, spAct j y, ?_, spSiegel_conj hr j⟩
  rw [spB_eq_spForm, spAct_eq_natRep, spAct_eq_natRep,
    isIsometric_natRep_statedSp m (GaloisField 2 1) j]
  simpa only [spB_eq_spForm] using hxy


section Certificates

theorem k2At_of_shortAt_selfDual_sp_block
    {n : ℕ} (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 1)))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 1))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 1)) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 2)
    {J V : Subgroup (SpG n)} {r : SpG n}
    (hJ : IsComponentOf J
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 1)).subtype) S e,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 1)).subtype) S e⁆)
    (hA6 : IsEmpty (↥J ≃* alternatingGroup (Fin 6)))
    (hFour : FourAt J V r) (hShort : ShortAt J r) :
    K2At (⊤ : Subgroup (SpG n)) V r := by
  obtain ⟨m, ι, E, W, hm1, hfield, hi, hrange, hE, hIso, hAct, hFix, hSplit, hOrth⟩ :=
    exists_linearBlockModel_selfDual_PSp n 1 S hS he hadj hdeg hJ hA6
  have hcard : Nat.card (GaloisField 2 1) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [GaloisField.card 2 1 (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num
  have hm : 3 ≤ m := by
    rcases hfield with h4 | h3
    · omega
    · exact h3
  let ιJ : SpG m →* J := ι.codRestrict J (by
    intro g
    rw [← hrange]
    exact ⟨g, rfl⟩)
  have hsurj : Function.Surjective ιJ := by
    intro j
    have hj : (j : SpG n) ∈ ι.range := by rw [hrange]; exact j.2
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hj
    exact ⟨g, Subtype.ext hg⟩
  have hinj : Function.Injective ιJ := by
    intro x y h
    exact hi (congrArg Subtype.val h)
  let η : J ≃* SpG m := (MulEquiv.ofBijective ιJ ⟨hinj, hsurj⟩).symm
  obtain ⟨rJ, hrJ, hPos⟩ := hShort
  have hrJ1 : rJ ≠ 1 := by
    intro h1
    apply hFour.2.2.2.2.1
    rw [← hrJ, h1]
    rfl
  obtain ⟨a, b, hab, hr⟩ := rckSpSiegel_of_shortAt_model hm η hrJ1 hPos
  have hIR : ι (η rJ) = r := by
    change (ιJ (η rJ) : SpG n) = r
    rw [show ιJ (η rJ) = rJ from (MulEquiv.ofBijective ιJ ⟨hinj, hsurj⟩).apply_symm_apply rJ,
      hrJ]
  have hSiegel : SpSiegel (E a) (E b) r := by
    rw [← hIR]
    exact spSiegel_map_of_linear_embedding ι E W hIso hAct hFix hSplit hOrth hr
  have hPure := pure_shortRoot_fourGroup_of_fourAt hFour
    ⟨E a, E b, (hIso a b).symm.trans hab, hSiegel⟩
  have hmn := LinearMap.finrank_le_finrank_of_injective hE
  have hn : 3 ≤ n := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at hmn
    omega
  exact k2At_top_of_pure_shortRoot_fourGroup hn hFour.1 hFour.2.2.2.2.1 hFour.2.2.1
    hFour.2.2.2.1 hPure

theorem rckPosShort_map_mulEquiv
    {Jb U : Type} [Group Jb] [Group U] (η : Jb ≃* U) {r : Jb}
    {Vb : Subgroup (Jb ⧸ Subgroup.center Jb)}
    (h : RCKPosShort Jb (QuotientGroup.mk' (Subgroup.center Jb) r) Vb) :
    RCKPosShort U (QuotientGroup.mk' (Subgroup.center U) (η r)) ⊥ := by
  obtain ⟨t, m, g, β, R, htag, hg, hβ, hs, h2β, hvia, hmem⟩ := h
  obtain ⟨φ, hrange, hker, u, hR⟩ := hvia
  let φ' := η.toMonoidHom.comp φ
  let R' := R.map η.toMonoidHom
  refine ⟨t, m, g, β, R', htag, hg, hβ, hs, h2β, ?_, ?_⟩
  · refine ⟨φ', ?_, ?_, u, ?_⟩
    · change (η.toMonoidHom.comp φ).range = ⊤
      rw [MonoidHom.range_comp, hrange, Subgroup.map_top]
      exact η.range_eq_top
    · intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      exact η.injective (hy.trans (map_one η).symm)
    · simp only [φ', R', hR, ggRootSub, Subgroup.map_map]
      rfl
  · obtain ⟨s, hsR, hsEq⟩ := Subgroup.mem_map.mp hmem
    refine Subgroup.mem_map.mpr ⟨η s, Subgroup.mem_map_of_mem η.toMonoidHom hsR, ?_⟩
    let eQ := QuotientGroup.congr (Subgroup.center Jb) (Subgroup.center U) η
      (Subgroup.map_center_eq η)
    have hq := congrArg eQ hsEq
    simpa only [eQ, QuotientGroup.congr_mk'] using hq

theorem shortAt_map_mulEquiv
    {X U : Type} [Group X] [Group U] {K J : Subgroup X} {r : X}
    (η : K ≃* U) (hJK : J ≤ K) (h : ShortAt J r) :
    ShortAt ((J.subgroupOf K).map η.toMonoidHom) (η ⟨r, by
      obtain ⟨rJ, hrJ, _⟩ := h
      rw [← hrJ]
      exact hJK rJ.2⟩) := by
  let J' := (J.subgroupOf K).map η.toMonoidHom
  let eJ : J ≃* J' := (Subgroup.subgroupOfEquivOfLe hJK).symm.trans
    ((Subgroup.equivMapOfInjective (J.subgroupOf K) η.toMonoidHom η.injective))
  obtain ⟨rJ, hrJ, hPos⟩ := h
  refine ⟨eJ rJ, ?_, rckPosShort_map_mulEquiv eJ hPos⟩
  change η ((Subgroup.subgroupOfEquivOfLe hJK).symm rJ : K) = _
  congr 1
  apply Subtype.ext
  exact hrJ

end Certificates

theorem three_le_rank_of_pure_shortRoot_fourGroup
    {m : ℕ} {V : Subgroup (SpG m)} {r : SpG m}
    (hrV : r ∈ V) (hr1 : r ≠ 1) (hVab : CFSG.Open.IsElemAbelian 2 V)
    (hV4 : Nat.card V = 4)
    (hpure : ∀ v ∈ V, v ≠ 1 → ∃ x y : SpMod m, spB m x y = 0 ∧ SpSiegel x y v) :
    3 ≤ m := by
  obtain ⟨a, b, c, s, hsV, hsZ, hLI, hab, hac, hbc, hr, hs, hV⟩ :=
    exists_isotropic_triple_of_pure_shortRoot_fourGroup hrV hr1 hVab hV4 hpure
  let W := Submodule.span (GaloisField 2 1) (Set.range ![a, b, c])
  have hW : (spForm m (GaloisField 2 1)).IsTotallyIsotropic W := by
    rw [ReflForm.IsTotallyIsotropic, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    change ![a, b, c] i ∈ (spForm m (GaloisField 2 1)).perp W
    rw [ReflForm.mem_perp]
    intro y hy
    refine Submodule.span_induction
      (p := fun y _ => (spForm m (GaloisField 2 1)).β y (![a, b, c] i) = 0)
      ?_ ?_ ?_ ?_ hy
    · rintro z ⟨j, rfl⟩
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.cons_zero, Fin.cons_one, Fin.cons_succ, ← spB_eq_spForm]
      all_goals first | exact spB_self _ | exact hab | exact hac | exact hbc |
        exact spB_refl hab | exact spB_refl hac | exact spB_refl hbc
    · exact (spForm m (GaloisField 2 1)).β_zero_left _
    · intro x y _ _ hx hy
      rw [ReflForm.add_left, hx, hy, add_zero]
    · intro d x _ hx
      rw [ReflForm.smul_left, hx, mul_zero]
  have hdim : Module.finrank (GaloisField 2 1) W = 3 := by
    exact (finrank_span_eq_card hLI).trans (by simp)
  have hle : Module.finrank (GaloisField 2 1) W ≤
      Module.finrank (GaloisField 2 1) ((spForm m (GaloisField 2 1)).perp W) :=
    Submodule.finrank_mono hW
  have heq := (spForm m (GaloisField 2 1)).finrank_perp W
  have hM : Module.finrank (GaloisField 2 1) (SpMod m) = 2 * m := by
    simp [SpMod, Fintype.card_sum]
    omega
  rw [hdim] at hle
  rw [hdim, hM] at heq
  omega


@[expose] def FixedSpBlockAt
    {X : Type} [Group X] (K J : Subgroup X) : Prop :=
  ∃ (n : ℕ) (η : K ≃* SpG n)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 1)))
    (e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 1)),
    (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧
    IsPrimIdemIn (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e ∧
    formAdj (RingHom.id (GaloisField 2 1))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
        (GaloisField 2 1)) e = e ∧
    (blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 2 ∨
      (∀ s ∈ S, s ∈ CFSG.Open.StatedSp n (GaloisField 2 1)) ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e ∧
      blockDegree (Algebra.adjoin (GaloisField 2 1) (Units.val '' S)) e < 4) ∧
    IsComponentOf ((J.subgroupOf K).map η.toMonoidHom)
      ⁅glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 1)).subtype) S e,
        glBlockCentralizer ((CFSG.Open.StatedSp n (GaloisField 2 1)).subtype) S e⁆

section FixedBlockCertificates

theorem fourAt_subgroup_map_mulEquiv
    {X U : Type} [Group X] [Group U] {K J V : Subgroup X} {r : X}
    (η : K ≃* U) (hJK : J ≤ K) (hrK : r ∈ K) (h : FourAt J V r) :
    FourAt ((J.subgroupOf K).map η.toMonoidHom) ((V.subgroupOf K).map η.toMonoidHom)
      (η ⟨r, hrK⟩) := by
  obtain ⟨hrV, hVJ, hVab, hV4, hr1, hconj⟩ := h
  have hVK := hVJ.trans hJK
  refine ⟨Subgroup.mem_map_of_mem η.toMonoidHom hrV, ?_,
    (hVab.subgroupOf K).map η.toMonoidHom, ?_, ?_, ?_⟩
  · exact Subgroup.map_mono (Subgroup.subgroupOf_mono K hVJ)
  · rw [Subgroup.card_map_of_injective η.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv]
    exact hV4
  · intro h1
    exact hr1 (congrArg Subtype.val (η.injective (h1.trans (map_one η).symm)))
  · intro v hv hv1
    obtain ⟨vK, hvK, rfl⟩ := Subgroup.mem_map.mp hv
    have hv1' : (vK : X) ≠ 1 := by
      intro h1
      apply hv1
      rw [show vK = 1 from Subtype.ext h1, map_one]
    obtain ⟨j, hj, heq⟩ := hconj vK hvK hv1'
    refine ⟨η ⟨j, hJK hj⟩, Subgroup.mem_map_of_mem η.toMonoidHom hj, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg η (Subtype.ext heq)

theorem k2At_of_fixedSpBlockAt
    {X : Type} [Group X] [Finite X] {K J V : Subgroup X} {r : X}
    (hBlock : FixedSpBlockAt K J) (hJK : J ≤ K)
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r) (hShort : ShortAt J r)
    (hA6 : IsEmpty (↥J ≃* alternatingGroup (Fin 6))) : K2At K V r := by
  have hShort₀ := hShort
  obtain ⟨n, η, S, e, hS, he, hadj, hdeg, hJ⟩ := hBlock
  obtain ⟨rJ, hrJ, hPos⟩ := hShort
  have hrK : r ∈ K := by rw [← hrJ]; exact hJK rJ.2
  let J' := (J.subgroupOf K).map η.toMonoidHom
  let eJ : J ≃* J' := (Subgroup.subgroupOfEquivOfLe hJK).symm.trans
    (Subgroup.equivMapOfInjective (J.subgroupOf K) η.toMonoidHom η.injective)
  have hA6' : IsEmpty (J' ≃* alternatingGroup (Fin 6)) := ⟨fun e => hA6.false (eJ.trans e)⟩
  have hFour' := fourAt_subgroup_map_mulEquiv η hJK hrK hFour
  have hShort' := shortAt_map_mulEquiv η hJK hShort₀
  have hK2 : K2At (⊤ : Subgroup (SpG n)) ((V.subgroupOf K).map η.toMonoidHom)
      (η ⟨r, hrK⟩) := by
    rcases hdeg with hdeg | ⟨hSU, hodd, hdeg₁, hdeg₂⟩
    · exact k2At_of_shortAt_selfDual_sp_block S hS he hadj hdeg hJ hA6' hFour' hShort'
    · have hCore' := coreCommAt_subgroup_map_mulEquiv η hJK hrK hCore
      exact k2At_of_shortAt_selfDualTwo_sp_block S hSU hS hodd he hadj hdeg₁ hdeg₂ hJ
        hFour' hCore' hShort'
  apply k2At_of_mulEquiv η hrK (hFour.2.1.trans hJK)
  simpa only [K2At, top_inf_eq] using hK2

end FixedBlockCertificates

end CFSG.StandardType.RCKC1
