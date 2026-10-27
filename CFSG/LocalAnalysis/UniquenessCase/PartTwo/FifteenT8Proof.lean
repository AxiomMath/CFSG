module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8Xbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8Blocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private noncomputable def psiT8 (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G)) :
    ↥M →* MulAut (Vtil ⊥ V hV) :=
  (actTil ⊥ V hV).comp (Subgroup.inclusion (le_stabTil hM hM₀))

private theorem psiT8_range (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G)) :
    (psiT8 M V hV hM hM₀).range = Mbar M ⊥ V hV := by
  ext φ
  rw [MonoidHom.mem_range]
  change (∃ m : ↥M, psiT8 M V hV hM hM₀ m = φ) ↔ φ ∈ barSub ⊥ V hV M
  rw [mem_barSub]
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨Subgroup.inclusion (le_stabTil hM hM₀) m, by simpa using m.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨(g : G), hg⟩, congrArg (actTil ⊥ V hV) (Subtype.ext rfl)⟩

private theorem psiT8_ker (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G)) :
    (psiT8 M V hV hM hM₀).ker = (F11.CTilde M ⊥ V).subgroupOf M := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_cTilde_iff hV hM]
  constructor
  · intro h
    refine ⟨m.2, le_stabTil hM hM₀ m.2, ?_⟩
    change actTil ⊥ V hV (Subgroup.inclusion (le_stabTil hM hM₀) m) = 1
    exact h
  · rintro ⟨-, h, h1⟩
    change actTil ⊥ V hV (Subgroup.inclusion (le_stabTil hM hM₀) m) = 1
    rw [show actTil ⊥ V hV (Subgroup.inclusion (le_stabTil hM hM₀) m)
        = actTil ⊥ V hV ⟨(m : G), h⟩ from
      congrArg (actTil ⊥ V hV) (Subtype.ext rfl), h1]

private noncomputable def psiBarT8 (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G)) :
    ↥M →* ↥(Mbar M ⊥ V hV) :=
  (psiT8 M V hV hM hM₀).codRestrict (Mbar M ⊥ V hV) fun m => by
    rw [← psiT8_range M V hV hM hM₀]
    exact MonoidHom.mem_range.2 ⟨m, rfl⟩

private theorem psiBarT8_surjective (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G)) :
    Function.Surjective (psiBarT8 M V hV hM hM₀) := by
  intro y
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 (by
    rw [psiT8_range M V hV hM hM₀]
    exact y.2)
  exact ⟨m, Subtype.ext (by simpa [psiBarT8] using hm)⟩

private theorem psiBarT8_ker (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G)) :
    (F11.CTilde M ⊥ V).subgroupOf M = (psiBarT8 M V hV hM hM₀).ker := by
  simp only [psiBarT8]
  rw [MonoidHom.ker_codRestrict]
  exact (psiT8_ker M V hV hM hM₀).symm

private noncomputable def phiT8 (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G))
    [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal] :
    F11.MBar11 M ⊥ V ≃* ↥(Mbar M ⊥ V hV) :=
  QuotientGroup.liftEquiv ((F11.CTilde M ⊥ V).subgroupOf M)
    (psiBarT8_surjective M V hV hM hM₀) (psiBarT8_ker M V hV hM hM₀)

private theorem phiT8_mk (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G))
    [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal] (m : ↥M) :
    phiT8 M V hV hM hM₀ (QuotientGroup.mk m) = psiBarT8 M V hV hM hM₀ m :=
  QuotientGroup.liftEquiv_coe ((F11.CTilde M ⊥ V).subgroupOf M) _ _ m

private theorem phiT8_comp_mk' (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G))
    [hN : ((F11.CTilde M ⊥ V).subgroupOf M).Normal] :
    (phiT8 M V hV hM hM₀).toMonoidHom.comp
        (QuotientGroup.mk' ((F11.CTilde M ⊥ V).subgroupOf M)) =
      psiBarT8 M V hV hM hM₀ := by
  refine MonoidHom.ext fun m => ?_
  change (phiT8 M V hV hM hM₀) (QuotientGroup.mk m) = psiBarT8 M V hV hM hM₀ m
  exact phiT8_mk M V hV hM hM₀ m

private abbrev tilT8 (V : Subgroup G) (hV : IsElemAbelian 2 V) {v : G} (hv : v ∈ V) :
    Vtil ⊥ V hV :=
  mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩)

private abbrev stabT8 (V : Subgroup G) (hV : IsElemAbelian 2 V) {v : G} (hv : v ∈ V) :
    Subgroup (MulAut (Vtil ⊥ V hV)) :=
  MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) (tilT8 V hV hv)

private theorem psiBarT8_ceilt (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer ((⊥ : Subgroup G) : Set G))
    {v : G} (hv : v ∈ V) :
    ((F11.CElt M ⊥ v).subgroupOf M).map (psiBarT8 M V hV hM hM₀) =
      (stabT8 V hV hv).subgroupOf (Mbar M ⊥ V hV) := by
  ext φ
  simp only [stabT8, tilT8, Subgroup.mem_map, Subgroup.mem_subgroupOf,
    MulAction.mem_stabilizer_iff, MulAut.smul_def]
  constructor
  · rintro ⟨m, hmX, hφ⟩
    have hmc : (m : G) * v * (m : G)⁻¹ * v⁻¹ = 1 :=
      Subgroup.mem_bot.1 hmX.2.2
    rw [← hφ]
    show (psiT8 M V hV hM hM₀ m) (tilT8 V hV hv) = tilT8 V hV hv
    show actTil ⊥ V hV (Subgroup.inclusion (le_stabTil hM hM₀) m) (tilT8 V hV hv) =
      tilT8 V hV hv
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
    exact hmc
  · intro hfix
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.1 (by
      rw [psiT8_range M V hV hM hM₀]
      exact φ.2)
    refine ⟨m, ?_, ?_⟩
    · change (m : G) ∈ M ∧ (m : G) ∈ normalizer ((⊥ : Subgroup G) : Set G) ∧
        (m : G) * v * (m : G)⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G)
      refine ⟨m.2, ?_, ?_⟩
      · rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _
      · rw [Subgroup.mem_bot]
        have h2 : (psiT8 M V hV hM hM₀ m) (tilT8 V hV hv) = tilT8 V hV hv := by
          rw [hm]
          exact hfix
        change actTil ⊥ V hV (Subgroup.inclusion (le_stabTil hM hM₀) m)
            ((mkTil ⊥ V hV) (IntMod.mk hV ⟨v, hv⟩)) =
          (mkTil ⊥ V hV) (IntMod.mk hV ⟨v, hv⟩) at h2
        rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot] at h2
        exact h2
    · exact Subtype.ext (by simpa [psiBarT8] using hm)

private theorem subgroupOf_commutator_self {X : Type*} [Group X] (H : Subgroup X) :
    (⁅H, H⁆).subgroupOf H = ⁅(⊤ : Subgroup ↥H), ⊤⁆ := by
  ext x
  rw [Subgroup.mem_subgroupOf, ← Subgroup.map_subtype_commutator H, ← _root_.commutator_def,
    Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem openPRank_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (p : ℕ) (H : Subgroup X) :
    CFSG.Open.pRank p (H.map e.toMonoidHom) = CFSG.Open.pRank p H := by
  have h1 := CFSG.pRank_congr_of_mulEquiv
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective) p
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
  exact h1.symm

private theorem openPRank_subgroupOf_eq {X : Type*} [Group X] [Finite X] {p : ℕ}
    {H K : Subgroup X} (h : H ≤ K) :
    CFSG.Open.pRank p (H.subgroupOf K) = CFSG.Open.pRank p H := by
  have h1 := CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h) p
  simp only [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
  exact h1

theorem s15_T8_bridge (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMV : D.M ≤ normalizer (V : Set G)) [((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal]
    {N : Subgroup (MulAut (Vtil ⊥ V hV))} (hN : N ≤ Mbar D.M ⊥ V hV)
    (hNn : ∀ q ∈ Mbar D.M ⊥ V hV, ∀ x ∈ N, q * x * q⁻¹ ∈ N)
    (hNab : IsElemAbelian 3 N) {n : ℕ} (hNcard : Nat.card N = 3 ^ n)
    (hNc : N ≤ ⁅Mbar D.M ⊥ V hV, Mbar D.M ⊥ V hV⁆) {v : G} (hv : v ∈ V)
    (hrk : 1 < CFSG.Open.pRank 3 (N ⊓ MulAction.stabilizer (MulAut (Vtil ⊥ V hV))
      (mkTil ⊥ V hV (IntMod.mk hV ⟨v, hv⟩)))) :
    ∃ Xbar : Subgroup (F11.MBar11 D.M ⊥ V), Xbar.Normal ∧ IsElemAbelian 3 Xbar ∧
      Nat.card Xbar = 3 ^ n ∧ Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), ⊤⁆ ∧
      1 < CFSG.Open.pRank 3 (Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v)) := by
  have hMV₀ : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  set Φ := phiT8 D.M V hV hMV hMV₀ with hΦ
  set Xbar : Subgroup (F11.MBar11 D.M ⊥ V) :=
    (N.subgroupOf (Mbar D.M ⊥ V hV)).map Φ.symm.toMonoidHom with hXbar
  have hNnorm : (N.subgroupOf (Mbar D.M ⊥ V hV)).Normal := by
    refine ⟨fun x hx q => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      hNn (q : MulAut (Vtil ⊥ V hV)) q.2 (x : MulAut (Vtil ⊥ V hV)) hx
  have hXnorm : Xbar.Normal := by
    rw [hXbar]
    exact hNnorm.map Φ.symm.toMonoidHom Φ.symm.surjective
  have hXab : IsElemAbelian 3 Xbar := by
    rw [hXbar]
    exact (hNab.subgroupOf (Mbar D.M ⊥ V hV)).map Φ.symm.toMonoidHom
  have hXcard : Nat.card Xbar = 3 ^ n := by
    rw [hXbar, Subgroup.card_map_of_injective Φ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv]
    exact hNcard
  have hΦcomp : Φ.toMonoidHom.comp Φ.symm.toMonoidHom =
      MonoidHom.id (↥(Mbar D.M ⊥ V hV)) := by
    ext x
    simp
  have hXmap : Xbar.map Φ.toMonoidHom = N.subgroupOf (Mbar D.M ⊥ V hV) := by
    rw [hXbar, Subgroup.map_map, hΦcomp, Subgroup.map_id]
  have hcomp : Φ.toMonoidHom.comp
        (QuotientGroup.mk' ((F11.CTilde D.M ⊥ V).subgroupOf D.M)) =
      psiBarT8 D.M V hV hMV hMV₀ := by
    rw [hΦ]
    exact phiT8_comp_mk' D.M V hV hMV hMV₀
  have hmapX : (F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v)).map Φ.toMonoidHom =
      (stabT8 V hV hv).subgroupOf (Mbar D.M ⊥ V hV) := by
    simp only [F11.barImage11]
    rw [Subgroup.map_map, hcomp]
    exact psiBarT8_ceilt D.M V hV hMV hMV₀ hv
  have hcomm_le : N.subgroupOf (Mbar D.M ⊥ V hV) ≤
      (⁅Mbar D.M ⊥ V hV, Mbar D.M ⊥ V hV⁆).subgroupOf (Mbar D.M ⊥ V hV) :=
    fun x hx => hNc (Subgroup.mem_subgroupOf.1 hx)
  have hcommmap : ((⁅Mbar D.M ⊥ V hV, Mbar D.M ⊥ V hV⁆).subgroupOf
        (Mbar D.M ⊥ V hV)).map Φ.symm.toMonoidHom =
      ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), ⊤⁆ := by
    rw [subgroupOf_commutator_self, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr Φ.symm.surjective]
  have hXc : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M ⊥ V)), ⊤⁆ := by
    rw [hXbar]
    exact le_trans (Subgroup.map_mono hcomm_le) (le_of_eq hcommmap)
  set A : Subgroup (F11.MBar11 D.M ⊥ V) :=
    Xbar ⊓ F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v) with hA
  have hAmap : A.map Φ.toMonoidHom =
      (N.subgroupOf (Mbar D.M ⊥ V hV)) ⊓
        (stabT8 V hV hv).subgroupOf (Mbar D.M ⊥ V hV) := by
    rw [hA, Subgroup.map_inf Xbar (F11.barImage11 D.M ⊥ V (F11.CElt D.M ⊥ v))
      Φ.toMonoidHom Φ.injective, hXmap, hmapX]
  have hsub : (N.subgroupOf (Mbar D.M ⊥ V hV)) ⊓
        (stabT8 V hV hv).subgroupOf (Mbar D.M ⊥ V hV) =
      (N ⊓ stabT8 V hV hv).subgroupOf (Mbar D.M ⊥ V hV) := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hpA : CFSG.Open.pRank 3 A = CFSG.Open.pRank 3 (N ⊓ stabT8 V hV hv) := by
    calc CFSG.Open.pRank 3 A
        = CFSG.Open.pRank 3 (A.map Φ.toMonoidHom) :=
          (openPRank_map_mulEquiv Φ 3 A).symm
      _ = CFSG.Open.pRank 3 ((N.subgroupOf (Mbar D.M ⊥ V hV)) ⊓
            (stabT8 V hV hv).subgroupOf (Mbar D.M ⊥ V hV)) := by rw [hAmap]
      _ = CFSG.Open.pRank 3 ((N ⊓ stabT8 V hV hv).subgroupOf (Mbar D.M ⊥ V hV)) := by
            rw [hsub]
      _ = CFSG.Open.pRank 3 (N ⊓ stabT8 V hV hv) :=
          openPRank_subgroupOf_eq (p := 3) (fun x hx => hN hx.1)
  exact ⟨Xbar, hXnorm, hXab, hXcard, hXc, hpA.symm ▸ hrk⟩

theorem s15_T8_one (D : Data G) (h153 : R15_3 D) (h1217 : R1217 D) (h127 : R127 D)
    (h1110 : R1110W D) (h1219 : D.sig = D.sig1) : RT8One D := by
  intro V₀ V L h hL hV1 hs4 hγ u hu hu2 hsupp hfix a ha hc
  have hle : V₀ ≤ ⊥ := by
    have := s15_Infra_le_v1Sub D.M V₀ V h.hyp151.isElemAbelian L
    rwa [hV1] at this
  obtain rfl : V₀ = ⊥ := le_bot_iff.1 hle
  have hMV : D.M ≤ normalizer (V : Set G) := h.hyp151.hyp125.pairFacts.le_normalizer
  have hMV₀ : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) :=
    h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hus : u ∈ stabTil ⊥ V := le_stabTil hMV hMV₀ hu
  have hav : a ∈ V := ha
  have hz : a * u * a⁻¹ * u⁻¹ ∈ V := by
    have h1 : u * a⁻¹ * u⁻¹ ∈ V := (mem_normalizer_iff.1 (hMV hu) a⁻¹).1 (V.inv_mem hav)
    have h2 : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
    rw [h2]
    exact V.mul_mem hav h1
  have htr := s15_T8_transvection D h hL h1217 hV1 hu hu2 hfix ha hc
  have hcase := s15_T8_caseThree D h153 h hs4 htr
  obtain ⟨r, B, Y, J, hB, hA⟩ :=
    s15_T8_blocks D h1217 h hL hV1 hs4 hγ hcase hu hu2 hsupp hfix hus ha hz
  have hcount := s15_T8_fix_count hB hA
  obtain ⟨N, hNle, hNn, hNab, ⟨n, hn1, hNcard⟩, hNc, hrk⟩ := s15_T8_xbar hB hcount
  haveI : ((F11.CTilde D.M ⊥ V).subgroupOf D.M).Normal := UC22.cTilde_bot_normal D.M V hMV
  obtain ⟨Xbar, hXn, hXab, hXcard, hXc, hXrk⟩ :=
    s15_T8_bridge D h.hyp151.isElemAbelian hMV hNle hNn hNab hNcard hNc hz hrk
  have hHyp11 : F11.Hyp11 D ⊥ V := Hyp125.hyp11 h127 h.hyp151.hyp125
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (F11.O2p 3 D.M)
  have hmax := ((h1110 V hHyp11 3 Nat.prime_three (by norm_num) P hP).2.2 n hn1 Xbar hXn hXab
    hXcard hXc).2 h1219 (a * u * a⁻¹ * u⁻¹) hz hc hXrk
  exact (centralizer_le_of_uniqueMax D.maxLocal hc
    ⟨1, by simpa using h.hyp151.isElemAbelian.2 _ hz⟩ hmax).1

theorem rt8_of_inputs (D : Data G) (h153 : R15_3 D) (h1217 : R1217 D) (h127 : R127 D)
    (h1110 : R1110W D) (h1219 : D.sig = D.sig1) : RT8 D :=
  rt8_of_one (s15_T8_one D h153 h1217 h127 h1110 h1219)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
