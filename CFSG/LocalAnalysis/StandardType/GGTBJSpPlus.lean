module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlusSide
public import CFSG.LocalAnalysis.StandardType.GGTBJSpRow
public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGTBJFamilyStages
public import CFSG.LocalAnalysis.StandardType.GGTBJCount
public import CFSG.LocalAnalysis.StandardType.GGTBJSpCount
public import CFSG.LocalAnalysis.StandardType.GGTBJSpModelTwo
public import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit
public import CFSG.LieType.Steinberg.CentralExt.PSpEvenMultiplier
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.HardMathSupport.Solomon.Coordinator

theorem center_eq_bot_of_quot_psp_even
    {Y : Type} [Group Y] [Finite Y]
    (hY : commutator Y = ⊤) {K : Type} [Field K] [Finite K] [CharP K 2] {m f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hm : 2 ≤ m) (hmf : m ≤ 3 → 2 ≤ f)
    (e : Y ⧸ Subgroup.center Y ≃* LargeEvenProj (LargeEvenSpGroup K m)) :
    Subgroup.center Y = ⊥ := by
  classical
  haveI : Group.IsPerfect Y := ⟨hY⟩
  let q := CFSG.RankThree.PerfectCover.centralQuotientMap e
  have hq : Function.Surjective q := CFSG.RankThree.PerfectCover.centralQuotientMap_surjective e
  have hk : q.ker = Subgroup.center Y := CFSG.RankThree.PerfectCover.centralQuotientMap_ker e
  haveI : Finite (LargeEvenProj (LargeEvenSpGroup K m)) := Finite.of_surjective q hq
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSpGroup K m)) :=
    Group.IsPerfect.ofSurjective (f := q) hq
  haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier
      (LargeEvenProj (LargeEvenSpGroup K m))) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier inferInstance
  let ψ : CFSG.Open.griessHopfMultiplier (LargeEvenProj (LargeEvenSpGroup K m)) →* q.ker :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q hq hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toMonoidHom
  have hψ : Function.Surjective ψ :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q hq hk.le).comp
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).surjective
  have hdvd := Subgroup.card_dvd_of_surjective (f := ψ) hψ
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpClosed.psp_even_hopfMultiplier hK hf hm hmf
  have hodd : Odd (Nat.card K - 1) := by
    rw [hK]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hM1 : Nat.card (CFSG.Open.griessHopfMultiplier (LargeEvenProj (LargeEvenSpGroup K m))) =
      1 := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    exact Nat.coprime_two_left.mpr hodd
  rw [hk, hM1] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ (Nat.dvd_one.mp hdvd)

theorem ggSpPlus_labelAll {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (h : ggTBJSpPlusLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ m n : ℕ, 4 ≤ m ∧ GGTorusLift p m R ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (_ : CharP K 2) (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K m)), Nat.card K = 2 ^ n ∧
          p ∣ Nat.card K - 1 ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn⟩ := h
  intro Q hQ
  have key : ∀ (hQ' : LargeEvenRecipeSymplectic l (2 ^ n) false Q),
      LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧
        (∃ m n' : ℕ, 4 ≤ m ∧ GGTorusLift p m R ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
          (_ : CharP K 2) (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K m)), Nat.card K = 2 ^ n' ∧
            p ∣ Nat.card K - 1 ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R)) := by
    intro hQ'
    obtain ⟨K, _, _, hK, hQK⟩ := hQ'
    have hch : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by
      rw [hK]
      exact hpn
    have hl4 : 4 ≤ l := hl
    have : NeZero l := ⟨by omega⟩
    exact ⟨K, inferInstance, inferInstance, hK, hQK, l, n, hl4,
      TableBSymp.ggTorusLift_symplectic hp hp2 hpq (by omega), K,
      inferInstance, inferInstance, hch, MulEquiv.refl _, hK, hpq, TableBSymp.sp_I_subset_inn⟩
  rcases htag with h | h <;> dsimp only at h <;> subst h <;> exact key hQ

theorem fixSubgroup_ggGamma {G : Type} [Group G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (b : ↥Bs) :
    fixSubgroup (ggGamma X hN b) =
      (X ⊓ Subgroup.centralizer ({(b : G)} : Set G)).subgroupOf X := by
  ext l
  rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨l.2, ?_⟩
    have h' := congrArg Subtype.val h
    rw [ggGamma_coe] at h'
    calc (l : G) * b = (b * l * (b : G)⁻¹) * b := by rw [h']
      _ = b * l := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [ggGamma_coe, ← h]
    group

theorem isComponentOf_subgroupOf_fixSubgroup {G : Type} [Group G] {Bs X J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (b : ↥Bs)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer ({(b : G)} : Set G))) :
    CFSG.Open.IsComponentOf (J.subgroupOf X) (fixSubgroup (ggGamma X hN b)) := by
  rw [fixSubgroup_ggGamma]
  have hJopen := CFSG.Assembly.isComponentOf_iff_open.mp hJ
  have hJX : J ≤ X := hJ.1.trans inf_le_left
  exact ⟨Subgroup.comap_mono hJopen.1, hJopen.2.1.comap X.subtype,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJX) hJopen.2.2⟩

theorem iInf_stabilizer_subgroupOf_eq_ggFixingJ {G : Type} [Group G] {X J : Subgroup G}
    (A : Subgroup (MulAut ↥X)) :
    A ⊓ ⨅ j : ↥(J.subgroupOf X), MulAction.stabilizer (MulAut ↥X) (j : ↥X) = ggFixingJ X J A := by
  ext g
  simp only [ggFixingJ, Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨hgA, hg⟩
    exact ⟨hgA, fun l => hg ⟨l.1, Subgroup.mem_subgroupOf.2 l.2⟩⟩
  · rintro ⟨hgA, hg⟩
    exact ⟨hgA, fun j => hg ⟨j.1, Subgroup.mem_subgroupOf.1 j.2⟩⟩

theorem card_ggFixingJ_mul_le_of_rank {G : Type} [Group G] [Finite G] {p m : ℕ} (hp : p.Prime)
    (hm : 4 ≤ m) {Bs X J : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X)
    (hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3)
    (hCX : p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)))
    (hA : p ^ m ≤ Nat.card ↥(ggGamma X hN).range) :
    p ^ 2 * Nat.card ↥(ggFixingJ X J (ggGamma X hN).range) ≤
      Nat.card ↥(ggGamma X hN).range := by
  have h1 := card_ggFixingJ_mul_card_centralizer hN hJX
  have hpos : 0 < Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
    lt_of_lt_of_le hp.pos hCX
  have h5 : p ^ 5 ≤ p ^ m * p := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc p ^ 2 * Nat.card ↥(ggFixingJ X J (ggGamma X hN).range) *
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) =
      p ^ 2 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by rw [mul_assoc, h1]
    _ ≤ p ^ 2 * p ^ 3 := Nat.mul_le_mul_left _ hCJ
    _ = p ^ 5 := by ring
    _ ≤ p ^ m * p := h5
    _ ≤ Nat.card ↥(ggGamma X hN).range * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) :=
      Nat.mul_le_mul hA hCX

theorem prime_le_card_inf_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) {z : G} (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hzX : z ∈ Subgroup.centralizer (X : Set G)) :
    p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzo : orderOf z = p := orderOf_eq_prime (hBs.2 z hz) hz1
  have hle : Subgroup.zpowers z ≤ Bs ⊓ Subgroup.centralizer (X : Set G) :=
    (Subgroup.zpowers_le).mpr ⟨hz, hzX⟩
  calc p = Nat.card (Subgroup.zpowers z) := by rw [Nat.card_zpowers, hzo]
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem exists_spPlus_model_of_marking
    {G : Type} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hmark : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs X)
    (hTBof : ∀ (R : Type) [Group R] (θ : X ⧸ Subgroup.center X ≃* R) (I : Set (MulAut R))
      (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      (∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I) → ∀ (r : ℕ), GGTorusLift p r R →
        commutator X = ⊤ → GGTorusTBGroup p r R I X (ggQuotHom θ) (ggGamma X hN).range) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (ψ₀ : ↥X →* LargeEvenProj (LargeEvenSpGroup K m)),
      4 ≤ m ∧ p ∣ Nat.card K - 1 ∧ Subgroup.center ↥X = ⊥ ∧
        GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
          (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
            MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) ↥X ψ₀ (ggGamma X hN).range := by
  classical
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => ggTBJSpPlusLabel p lab)
    (fun lab _ hs => nbrC_labelAll_guard (ggSpPlus_labelAll hp hp2 hs))
    (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, m, nf, hm4, hlift, Kf, _, _, _, e, hKf, hpq,
    hIinn⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  have hTB := hTBof R θ I hBsN hBsI m hlift hXc
  have hTB' := GGTorusTBGroup.mulEquiv (I' := Set.range (MulAut.conj :
      LargeEvenProj (LargeEvenSpGroup Kf m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup Kf m)))) e (fun φ hφ => by
    obtain ⟨g, rfl⟩ := hIinn hφ
    exact ⟨e g, by
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]⟩) hTB
  have hf : 1 ≤ nf := by
    by_contra h0
    have h0' : nf = 0 := by omega
    have h2 : 2 ≤ Nat.card Kf := by
      haveI : Fintype Kf := Fintype.ofFinite Kf
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    rw [hKf, h0', pow_zero] at h2
    omega
  have hZ : Subgroup.center ↥X = ⊥ :=
    center_eq_bot_of_quot_psp_even hXc hKf hf (by omega) (fun h => by omega) (θ.trans e)
  exact ⟨m, Kf, inferInstance, inferInstance, inferInstance, hBsN,
    e.toMonoidHom.comp (ggQuotHom θ), hm4, hpq, hZ, hTB'⟩

theorem GGResHyp.bstar_eq_of_spPlus_L
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs L) :
    B = Bs := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨m, Kf, _, _, _, hN, ψ₀, hm4, hpq, _hZ, hTB⟩ :=
    exists_spPlus_model_of_marking hp hp2 hmark
      (fun _ _ θ _ hN hBsI _ hlift hXc => ggTorusTBGroup_of_L hcfg hXc θ hN hBsI hlift)
  haveI : NeZero m := ⟨by omega⟩
  exact (ggTBJ_sp_bstar_eq hp hp2 hcfg L hN hpq ψ₀ hTB).symm

theorem ggTBJLeft_spPlus_sideDatum_of_marking
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs L) :
    GGResSideDatum p Bs L J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨m, Kf, _, _, _, hN, ψ₀, hm4, hpq, hZ, hTB⟩ :=
    exists_spPlus_model_of_marking hp hp2 hmark
      (fun _ _ θ _ hN hBsI _ hlift hXc => ggTorusTBGroup_of_L hcfg hXc θ hN hBsI hlift)
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl).symm
  have hDgen : D = Subgroup.closure {x, y} := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hDgen]
    exact Subgroup.subset_closure (by simp)
  have hDB : D ≤ B := hcfg.2.2.1.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 (hDB hyD)
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  let y' : MulAut ↥L := ggGamma L hN ⟨y, hyBs⟩
  have hy1' : y' ≠ 1 := by
    intro h1
    have hyC : y ∈ Subgroup.centralizer (L : Set G) :=
      (ggGamma_eq_one_iff L hN ⟨y, hyBs⟩).mp h1
    have hyx : y ∈ Subgroup.zpowers x := by
      rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
      exact ⟨hDB hyD, hyC⟩
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hDgen, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact Subgroup.mem_zpowers g
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hyx
    have hle := Subgroup.card_le_of_le hDle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hx1] at hle
    have : 1 < p := hp.one_lt
    nlinarith
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hJcomp.1.trans inf_le_left
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({((⟨y, hyBs⟩ : ↥Bs) : G)} : Set G) := by
    rw [hDgen, Subgroup.centralizer_closure]
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hl, h⟩
      exact ⟨hl, fun g hg => h g (Or.inr hg)⟩
    · rintro ⟨hl, h⟩
      refine ⟨hl, fun g hg => ?_⟩
      rcases hg with rfl | rfl
      · exact Subgroup.mem_centralizer_iff.mp (hLx hl) g rfl
      · exact h g rfl
  have hJ' : CFSG.Open.IsComponentOf (J.subgroupOf L) (fixSubgroup y') :=
    isComponentOf_subgroupOf_fixSubgroup hN ⟨y, hyBs⟩ (hLD ▸ hJcomp)
  have hcount : p ^ 2 * Nat.card ↥((ggGamma L hN).range ⊓
      ⨅ j : ↥(J.subgroupOf L), MulAction.stabilizer (MulAut ↥L) (j : ↥L)) ≤
      Nat.card ↥(ggGamma L hN).range := by
    rw [iInf_stabilizer_subgroupOf_eq_ggFixingJ]
    exact ggTBJ_card_fixingJ_mul_le hcfg hN
  haveI : NeZero m := ⟨by omega⟩
  have hEq : Bs = B := ggTBJ_sp_bstar_eq hp hp2 hcfg L hN hpq ψ₀ hTB
  have hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 2 := by
    rw [hH.iOne_of_eq_bstar hEq.symm, hDcard]
  exact ggTBJ_sp_sideDatum_of_cover_of_centralizer_le_sq hp2 (by omega) hBs hSC hN hZ hpq ψ₀ hTB
    y' ⟨⟨y, hyBs⟩, rfl⟩ hy1'
    hJL hJ' hcount (prime_le_card_inf_centralizer hp hBs hxBs hx1 hxC)
    hCJ

theorem ggTBJLeft_spPlus_of_marking
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs L) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J :=
  Or.inl (ggTBJLeft_spPlus_sideDatum_of_marking hH hmark)

theorem GGResHyp.false_of_exact2_L_spSplit_four_five
    {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun p lab =>
      (lab.tag = .B ∨ lab.tag = .C) ∧ (4 ≤ lab.rank ∧ lab.rank ≤ 5) ∧
        p ∣ 2 ^ lab.n - 1) p Bs L)
    (h2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hsp : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs L :=
    hmark.mono_label fun lab ⟨htag, hrank, hdiv⟩ => ⟨htag, hrank.1, hdiv⟩
  exact not_ggResSideDatum_of_ggResLeviDatumExact2
    (ggTBJLeft_spPlus_sideDatum_of_marking hH hsp) h2

theorem ggTBJNbr_spPlus_of_marking
    (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel ggTBJSpPlusLabel p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨m, Kf, _, _, _, hN, ψ₀, hm4, hpq, hZ, hTB⟩ :=
    exists_spPlus_model_of_marking hp hp2 hmark
      (fun _ _ θ _ hN hBsI _ hlift hXc => ggTorusTBGroup_of_nbr hcfg hnb hXc θ hN hBsI hlift)
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hk) y rfl).symm
  have hDgen : D = Subgroup.closure {x, y} := hH.2.2.2.2.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  let y' : MulAut ↥K := ggGamma K hN ⟨x, hxBs⟩
  have hy1' : y' ≠ 1 := by
    intro h1
    have hxC : x ∈ Subgroup.centralizer (K : Set G) :=
      (ggGamma_eq_one_iff K hN ⟨x, hxBs⟩).mp h1
    have hxy : x ∈ Subgroup.zpowers y := by
      rw [← inf_centralizer_eq_zpowers_of_sHat hnb.1]
      exact ⟨hxB, hxC⟩
    have hDle : D ≤ Subgroup.zpowers y := by
      rw [hDgen, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact hxy
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact Subgroup.mem_zpowers y
    have hle := Subgroup.card_le_of_le hDle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 y hyBs) hy1] at hle
    have : 1 < p := hp.one_lt
    nlinarith
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  have hJ' : CFSG.Open.IsComponentOf (J.subgroupOf K) (fixSubgroup y') :=
    isComponentOf_subgroupOf_fixSubgroup hN ⟨x, hxBs⟩ hJcomp
  have hCK : p ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    prime_le_card_inf_centralizer hp hBs hyBs hy1 hyC
  have hcount : p ^ 2 * Nat.card ↥((ggGamma K hN).range ⊓
      ⨅ j : ↥(J.subgroupOf K), MulAction.stabilizer (MulAut ↥K) (j : ↥K)) ≤
      Nat.card ↥(ggGamma K hN).range := by
    rw [iInf_stabilizer_subgroupOf_eq_ggFixingJ]
    exact card_ggFixingJ_mul_le_of_rank hp hm4 hN hJK hcfg.card_bstar_inf_centralizer_J_le hCK
      hTB.2.2.2.2.2.1
  exact ggTBJ_sp_sideDatum_of_cover hp2 (by omega) hBs hSC hN hZ hpq ψ₀ hTB y' ⟨⟨x, hxBs⟩, rfl⟩ hy1'
    hJK hJ' hcount hCK hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJLeftOn_spPlus :
    GGTBJLeftOn ggTBJSpPlusLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hL _
  rcases ggTBJLeft_spPlus_of_marking hH hL with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJNbrOn_spPlus
    (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn ggTBJSpPlusLabel := by
  intro G _ _ p B Bs x L D J y K hH _ hK _
  rcases ggTBJNbr_spPlus_of_marking hI3 hH hK with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJOrderRestSplitAUnitSeven_of_restUnitSpPlus
    (hI3 : GGNbrSubcomponentInput)
    (h : GGTBJOrderRestSplitAUnitSpPlusInput) : GGTBJOrderRestSplitAUnitSevenInput :=
  GGTBJOrdinaryOutside.of_proved ggTBJLeftOn_spPlus (ggTBJNbrOn_spPlus hI3) h

end CFSG.StandardType

end
