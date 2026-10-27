module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aFix
public import CFSG.RankThree.PartOne.KF.BloomBasic
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Sylow
public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_eq_bot_of_mem_of_pow_eq_one {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (hcard : Nat.card W = 2 ^ 6)
    {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hL : IsPOnePlusTwo 3 ↥L) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {e : MulAut W} (heA : e ∈ A) (heq : e ^ q = 1) (he1 : e ≠ 1) :
    MonoidHom.eqLocus (e : W →* W) (MonoidHom.id W) = ⊥ := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hLcard : Nat.card ↥L = 27 := by rw [hL.2.1]; norm_num
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥L
  have heN : e ∈ Subgroup.normalizer (L : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa using hLn e heA
  let x0 : Subgroup.normalizer (L : Set (MulAut W)) := ⟨e, heN⟩
  let α : MulAut ↥L := Subgroup.normalizerMonoidHom L x0
  have hαq : α ^ q = 1 := by
    have hx0q : x0 ^ q = 1 := by
      apply Subtype.ext
      change e ^ q = 1
      exact heq
    rw [← map_pow, hx0q, map_one]
  have hα1 : α = 1 :=
    CFSG.RankThree.PartOne.KFBloom.aut_eq_one_of_card_27 hLcard hZcard hq5 α hαq
  have hcomm : ∀ ℓ ∈ L, e * ℓ = ℓ * e := by
    intro ℓ hℓ
    have h1 : α ⟨ℓ, hℓ⟩ = ⟨ℓ, hℓ⟩ := by rw [hα1]; rfl
    have h2 : ((α ⟨ℓ, hℓ⟩ : ↥L) : MulAut W) = ((⟨ℓ, hℓ⟩ : ↥L) : MulAut W) := by rw [h1]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    calc e * ℓ = (e * ℓ * e⁻¹) * e := by group
      _ = ℓ * e := by rw [h2]
  let U : Subgroup W := MonoidHom.eqLocus (e : W →* W) (MonoidHom.id W)
  have hUmem : ∀ u : W, u ∈ U ↔ e u = u := fun u => Iff.rfl
  have hUinv : ∀ ℓ ∈ L, ∀ u ∈ U, ℓ u ∈ U := by
    intro ℓ hℓ u hu
    rw [hUmem] at hu ⊢
    have h3 := congrArg (fun f : MulAut W => f u) (hcomm ℓ hℓ)
    simp only [MulAut.mul_apply] at h3
    rw [h3, hu]
  have hfix : ∀ ℓ' : ↥L, ℓ' ∈ Subgroup.center ↥L → ℓ' ≠ 1 →
      ∀ u ∈ U, (ℓ' : MulAut W) u = u → u = 1 :=
    fun ℓ' hℓ' hℓ'1 u _ hu =>
      s16c167_central_fixed_point_free hW hcard hL hℓ' hℓ'1 hu
  rcases s16c167_invariant_eq_bot_or_card hW hcard hL U hUinv hfix with hbot | hcardU
  · exact hbot
  · exfalso
    have hUtop : U = ⊤ := Subgroup.eq_top_of_card_eq U (by rw [hcardU, hcard])
    apply he1
    apply MulEquiv.ext
    intro w
    have hw : w ∈ U := by rw [hUtop]; exact Subgroup.mem_top w
    rw [hUmem] at hw
    simpa using hw

theorem s168e3_pRank_lt_two_of_p1p2 [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hcard : Nat.card W = 2 ^ 6) {A L : Subgroup (MulAut W)} (hLA : L ≤ A)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L) (hL : IsPOnePlusTwo 3 ↥L)
    (hWL : commSub ⊤ L = ⊤) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    CFSG.Open.pRank q A < 2 := by
  classical
  by_contra hge
  have hge' : 2 ≤ CFSG.Open.pRank q A := not_lt.1 hge
  have hW' : ∀ x : W, x * x = 1 := fun x => by simpa [pow_two] using hW x
  have hq5 : 5 ≤ q := by
    by_contra h
    have h4 : q ≤ 4 := by omega
    have h2 : 2 ≤ q := hq.two_le
    interval_cases q
    · exact hq2 rfl
    · exact hq3 rfl
    · exact absurd hq (by norm_num)
  have hge'' : 2 ≤ CFSG.pRank q A := by
    rw [UC6.groupPRank_eq_pRank]
    exact hge'
  obtain ⟨E, hEA, hEel, hEcard⟩ :=
    c23_exists_elemAbelian_card_pow (p := q) (M := A) (k := 2) hq hge''
  have hfree : ∀ g : ↥E, g ≠ 1 → ∀ w : W, (g : MulAut W) w = w → w = 1 := by
    intro g hg1 w hw
    have hgA : (g : MulAut W) ∈ A := hEA g.2
    have hgq : (g : MulAut W) ^ q = 1 := hEel.2 (g : MulAut W) g.2
    have hg1' : (g : MulAut W) ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hUbot :=
      s168e3_eq_bot_of_mem_of_pow_eq_one hW' hcard hLA hLn hL hq hq5 hgA hgq hg1'
    have hwU : w ∈ MonoidHom.eqLocus ((g : MulAut W) : W →* W) (MonoidHom.id W) := hw
    rw [hUbot] at hwU
    simpa using hwU
  let X := {w : W // w ≠ 1}
  let act : ↥E → X → X := fun g x =>
    ⟨(g : MulAut W) x.1, fun h =>
      x.2 ((g : MulAut W).injective (h.trans (map_one (g : MulAut W)).symm))⟩
  letI : MulAction ↥E X :=
    { smul := act
      one_smul := fun x => by
        apply Subtype.ext
        change (act 1 x).1 = x.1
        rfl
      mul_smul := fun g h x => by
        apply Subtype.ext
        change (act (g * h) x).1 = (act g (act h x)).1
        rfl }
  have hstab : ∀ x : X, Nat.card (MulAction.stabilizer ↥E x) = 1 := by
    intro x
    have hbot : MulAction.stabilizer ↥E x = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      by_contra hg1
      have hfix : (g : MulAut W) x.1 = x.1 := by
        have hsm := (MulAction.mem_stabilizer_iff).mp hg
        have hval := congrArg Subtype.val hsm
        exact hval
      exact x.2 (hfree g hg1 x.1 hfix)
    rw [hbot, Subgroup.card_bot]
  have horb : ∀ x : X, q ^ 2 ∣ (MulAction.orbit ↥E x).ncard := by
    intro x
    have hidx : (MulAction.stabilizer ↥E x).index = (MulAction.orbit ↥E x).ncard :=
      MulAction.index_stabilizer ↥E x
    have hmul : (MulAction.stabilizer ↥E x).index = q ^ 2 := by
      have h := Subgroup.card_mul_index (MulAction.stabilizer ↥E x)
      rw [hstab x, one_mul, hEcard] at h
      exact h
    rw [← hidx, hmul]
  have hdiv : q ^ 2 ∣ Nat.card X :=
    CFSG.LargeExtraspecial.dvd_natCard_of_forall_dvd_ncard_orbit horb
  have hXcard : Nat.card X = 63 := by
    haveI := Fintype.ofFinite W
    show Nat.card {w : W // w ≠ 1} = 63
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun w : W => w = 1)]
    have h1 : Fintype.card {w : W // w = 1} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨1, rfl⟩, fun y => Subtype.ext y.2⟩
    rw [h1]
    have h2 : Fintype.card W = 64 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hcard
    rw [h2]
  rw [hXcard] at hdiv
  have hle : q ^ 2 ≤ 63 := Nat.le_of_dvd (by norm_num) hdiv
  have hq7 : q ≤ 7 := by
    by_contra h
    have h8 : 8 ≤ q := not_le.1 h
    have h8' : 8 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h8 2
    norm_num at h8'
    omega
  have hq67 : q = 5 ∨ q = 7 := by
    have h6 : q ≠ 6 := by
      intro h
      rw [h] at hq
      norm_num at hq
    omega
  rcases hq67 with h5 | h7
  · rw [h5] at hdiv; norm_num at hdiv
  · rw [h7] at hdiv; norm_num at hdiv

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
