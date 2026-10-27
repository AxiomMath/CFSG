module

public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
import CFSG.LocalAnalysis.StandardType.GGRealKGCoverComp
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenModel
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenLine
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenPair
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenCover
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitFive
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLUnitaryCubic
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

namespace RealKGUSplit

open Matrix CFSG.Assembly Multiplicative SpCoord CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.StandardType.SlNsRootGen CFSG.StandardType.SuSplitRootGen CFSG.StandardType.RealKGCover

section Monomial

variable {n r ε p : ℕ} {K : Type} [Field K]

private theorem splitEntries_eq_of_mul_eq {h : UnitaryFieldData 2 n K} {ζ : K}
    {g : hypSU h r ε} {t t' : Fin r → ZMod p}
    (hm : (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) * diagonal (splitEntries ζ t) =
      diagonal (splitEntries ζ t') * (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K))
    {x y : HypIndex r ε}
    (hxy : (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) y x ≠ 0) :
    splitEntries ζ t x = splitEntries ζ t' y := by
  have e := congrArg (fun M : Matrix (HypIndex r ε) (HypIndex r ε) K => M y x) hm
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at e
  exact mul_left_cancel₀ hxy (e.trans (mul_comm _ _))

theorem exists_signedPerm_of_normalizer (h : UnitaryFieldData 2 n K) (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin r → ZMod p) →* hypSU h r ε} (hτ : IsSplitTorus h ζ τ)
    (g : hypSU h r ε) (hg : ∀ t : Fin r → ZMod p, ∃ t', g * τ (ofAdd t) * g⁻¹ = τ (ofAdd t')) :
    ∃ (π : Equiv.Perm (Fin r)) (σ : Fin r → ZMod p), (∀ i, σ i = 1 ∨ σ i = -1) ∧
      ∀ t t' : Fin r → ZMod p, g * τ (ofAdd t) * g⁻¹ = τ (ofAdd t') →
        ∀ i, t' (π i) = σ i * t i := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  let u : Kˣ := (hζ.isUnit hp.ne_zero).unit
  have hu : (u : K) = ζ := (hζ.isUnit hp.ne_zero).unit_spec
  have huo : orderOf u = p :=
    (IsPrimitiveRoot.isUnit_unit (n := p) hp.ne_zero hζ).eq_orderOf.symm
  have hpow : ∀ a b : ZMod p, ζ ^ a.val = ζ ^ b.val → a = b := by
    intro a b hab
    have h1 : u ^ a.val = u ^ b.val := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]
      exact hab)
    have h2 := (pow_inj_mod (x := u)).mp h1
    rw [huo, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
    exact ZMod.val_injective p h2
  have hm : ∀ t t' : Fin r → ZMod p, g * τ (ofAdd t) * g⁻¹ = τ (ofAdd t') →
      (((g : hypSU h r ε) : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
          diagonal (splitEntries ζ t) =
        diagonal (splitEntries ζ t') *
          (((g : hypSU h r ε) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    intro t t' htt'
    have h1 : (g : GL (HypIndex r ε) K) * (τ (ofAdd t) : GL (HypIndex r ε) K) *
        (g : GL (HypIndex r ε) K)⁻¹ = (τ (ofAdd t') : GL (HypIndex r ε) K) :=
      congrArg (fun y : hypSU h r ε => (y : GL (HypIndex r ε) K)) htt'
    have h2 : (g : GL (HypIndex r ε) K) * (τ (ofAdd t) : GL (HypIndex r ε) K) =
        (τ (ofAdd t') : GL (HypIndex r ε) K) * (g : GL (HypIndex r ε) K) := by
      rw [← h1]
      group
    have h3 := congrArg (fun y : GL (HypIndex r ε) K =>
      (y : Matrix (HypIndex r ε) (HypIndex r ε) K)) h2
    simpa only [Units.val_mul, hτ t, hτ t'] using h3
  have hζ1 : ζ ≠ 1 := hζ.ne_one hp.one_lt
  have key : ∀ i : Fin r, ∃ j : Fin r, ∃ σ : ZMod p, (σ = 1 ∨ σ = -1) ∧
      ∀ t t' : Fin r → ZMod p, g * τ (ofAdd t) * g⁻¹ = τ (ofAdd t') → t' j = σ * t i := by
    intro i
    obtain ⟨y, hy⟩ :=
      ReflSp.exists_ne_zero_col ((g : hypSU h r ε) : GL (HypIndex r ε) K) (Sum.inl i)
    have hdiag : ∀ t t' : Fin r → ZMod p, g * τ (ofAdd t) * g⁻¹ = τ (ofAdd t') →
        splitEntries ζ t (Sum.inl i) = splitEntries ζ t' y := fun t t' htt' =>
      splitEntries_eq_of_mul_eq (hm t t' htt') hy
    rcases y with j | k | j
    · refine ⟨j, 1, Or.inl rfl, fun t t' htt' => ?_⟩
      have h1 := hdiag t t' htt'
      simp only [splitEntries] at h1
      rw [hpow _ _ h1.symm, one_mul]
    · exfalso
      obtain ⟨t', ht'⟩ := hg (Pi.single i 1)
      have h1 := hdiag _ _ ht'
      simp only [splitEntries, Pi.single_eq_same, ZMod.val_one, pow_one] at h1
      exact hζ1 h1
    · refine ⟨j, -1, Or.inr rfl, fun t t' htt' => ?_⟩
      have h1 := hdiag t t' htt'
      simp only [splitEntries] at h1
      rw [← hypEntries_neg hp hζ.pow_eq_one (t' j)] at h1
      have h3 : t i = -(t' j) := hpow _ _ h1
      rw [h3, neg_one_mul, neg_neg]
  choose j σ hσ hj using key
  have hjinj : Function.Injective j := by
    intro i i' hii'
    by_contra hne
    obtain ⟨t', ht'⟩ := hg (Pi.single i 1)
    have h1 := hj i _ _ ht'
    have h3 := hj i' _ _ ht'
    rw [Pi.single_eq_same, mul_one] at h1
    rw [Pi.single_eq_of_ne (Ne.symm hne), mul_zero, ← hii'] at h3
    have h2 : σ i = 0 := h1.symm.trans h3
    rcases hσ i with hh | hh <;> rw [hh] at h2
    · exact one_ne_zero h2
    · exact neg_ne_zero.mpr one_ne_zero h2
  exact ⟨Equiv.ofBijective j hjinj.bijective_of_finite, σ, hσ,
    fun t t' htt' i => hj i t t' htt'⟩

end Monomial

private theorem conj_injective_of_center {R : Type} [Group R] (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  intro x y hxy
  have hc : x⁻¹ * y ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun f : MulAut R => f z) hxy
    simp only [MulAut.conj_apply] at h1
    calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
      _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
      _ = x⁻¹ * y * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.mp hc

private theorem two_le_of_dvd {n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hpq : p ∣ 2 ^ n - 1) :
    2 ≤ n := by
  by_contra hlt
  have hn1 : n = 1 := by omega
  subst hn1
  have h1 : p ∣ 1 := by simpa using hpq
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem ggKGRootDatum_unitarySplit
    {K : Type} [Field K] [Finite K] {n d p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1)
    (hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤)
    (hlayer : ∀ a : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)), a ^ p = 1 →
      ∀ J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))), ⁅J, J⁆ = J →
      J ≤ Subgroup.centralizer ({a} : Set (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) →
        J ≤ LargeEvenLayer (Subgroup.centralizer
          ({a} : Set (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))))
    (r : ℕ) : GGKGRootDatum p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  intro E hE h3 _ hsc
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2n] at hpq
    exact Nat.two_not_dvd_two_mul_sub_one (n := 2 ^ (n - 1)) (by positivity) hpq
  have hn2 := two_le_of_dvd hp hn hpq
  have h4n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.snd heq
    simp only at this
    omega
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun h => by omega
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ :=
    TableBUE.center_proj_eq_bot hK hd hdq
  have hcinj := conj_injective_of_center hZ
  let A : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
    E.map MulAut.conj
  have hmemA : ∀ x, MulAut.conj x ∈ A ↔ x ∈ E := fun x =>
    ⟨fun h => by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
      rwa [← hcinj hyx], fun h => Subgroup.mem_map_of_mem _ h⟩
  have hAI : ∀ a ∈ A, ∃ φa ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)),
      ∀ l, φa ((MonoidHom.id (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) l) =
        (MonoidHom.id (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) (a l) := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨_, SCFourCover.mem_largeEvenMatConjImage_of_mem_innAutDerived hn hK hd hq
      (CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ ⟨x, rfl⟩),
      fun l => rfl⟩
  have h3A : p ^ 3 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective hcinj]
    exact h3
  have hscA : GGTorusSelfCent p A := by
    intro m hm hmp
    refine (hmemA m).mpr (hsc m (fun e he => ?_) hmp)
    have h := hm _ ((hmemA e).mpr he)
    rw [MulAut.conj_apply] at h
    calc m * e = e * m * e⁻¹ * e := by rw [h]
      _ = e * m := by group
  have hker0 : (MonoidHom.id (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).ker ≤
      Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
    rw [hx]
    exact Subgroup.one_mem _
  rcases (show d = 3 ∨ 4 ≤ d by omega) with rfl | hd4
  ·
    exfalso
    have hle := card_le_of_three hK hp hpq Function.surjective_id hker0 hperf
      (TableB.isElemAbelian_map hE _) hAI
    have h31 : p ^ 3 ≤ p ^ 1 := by rw [pow_one]; exact h3A.trans hle
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h31
    omega
  obtain ⟨s, ε, h, ζ, τ, φ, -, hε, hζ, -, hτ, hφs, hφker, hkerp, hM, hτc⟩ :=
    exists_isCoverTorusModel hK hd4 hp hpq Function.surjective_id hker0 hperf
      (TableB.isElemAbelian_map hE _) hAI hscA
  have : Finite (hypSU h s ε) := Subtype.finite
  have hpow1 : ∀ u : Multiplicative (Fin s → ZMod p), u ^ p = 1 := by
    intro u
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext k
    simp
  let τR : (Fin s → Multiplicative (ZMod p)) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    (φ.comp τ).comp (MulEquiv.funMultiplicative (Fin s) (ZMod p)).symm.toMonoidHom
  have hτapp : ∀ f, τR f = φ (τ (ofAdd fun k => toAdd (f k))) := fun f => rfl
  have hτinj : Function.Injective τR := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have h1 := hτc (ofAdd fun k => toAdd (f k)) (by
      rw [← hτapp, hf]
      exact Subgroup.one_mem _)
    funext k
    have h2 := congrFun (congrArg Multiplicative.toAdd h1) k
    exact Multiplicative.toAdd.injective (by simpa using h2)
  have hτE : τR.range = E := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      rw [← hmemA]
      exact (hM _).mpr ⟨_, rfl⟩
    · intro hx
      obtain ⟨t, ht⟩ := (hM _).mp ((hmemA x).mpr hx)
      exact ⟨fun k => ofAdd (toAdd t k), (hcinj ht).symm⟩
  have hlinv : ∀ (m : Fin s) (t : Fin s → ZMod p), (lineWeyl h ε m)⁻¹ * τ (ofAdd t) *
      lineWeyl h ε m = τ (ofAdd (negMap m t)) := by
    intro m t
    have h1 := lineWeyl_conj h hp hζ.pow_eq_one hτ m (negMap m t)
    rw [negMap_negMap] at h1
    rw [← h1]
    group
  have hfixset : ∀ i j : Fin s, (MulAut.conj (lineWeyl h ε j)).toMonoidHom ''
      torusFix τ (swapMap i j) = torusFix τ (sswapMap i j) := by
    intro i j
    ext x
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      have hu' : swapMap i j (toAdd u) = toAdd u := hu
      refine ⟨ofAdd (negMap j (toAdd u)), ?_, ?_⟩
      · change sswapMap i j (negMap j (toAdd u)) = negMap j (toAdd u)
        rw [sswapMap, negMap_negMap, hu']
      · have h1 := lineWeyl_conj h hp hζ.pow_eq_one hτ j (toAdd u)
        rw [ofAdd_toAdd] at h1
        exact h1.symm
    · rintro ⟨u, hu, rfl⟩
      have hu' : negMap j (swapMap i j (negMap j (toAdd u))) = toAdd u := hu
      refine ⟨τ (ofAdd (negMap j (toAdd u))), ⟨ofAdd (negMap j (toAdd u)), ?_, rfl⟩, ?_⟩
      · change swapMap i j (negMap j (toAdd u)) = negMap j (toAdd u)
        calc swapMap i j (negMap j (toAdd u))
            = negMap j (negMap j (swapMap i j (negMap j (toAdd u)))) := by rw [negMap_negMap]
          _ = negMap j (toAdd u) := by rw [hu']
      · change lineWeyl h ε j * τ (ofAdd (negMap j (toAdd u))) * (lineWeyl h ε j)⁻¹ = τ u
        rw [lineWeyl_conj h hp hζ.pow_eq_one hτ, negMap_negMap, ofAdd_toAdd]
  have hdata : ∀ i : OmPlusIdx s ⊕ Fin s, ∃ (w : hypSU h s ε) (B : Subgroup (hypSU h s ε))
      (fm : (Fin s → ZMod p) → Fin s → ZMod p),
      w ∈ B ∧ (∀ t, w * τ (ofAdd t) * w⁻¹ = τ (ofAdd (fm t))) ∧
      IsComponentOf B (Subgroup.centralizer (torusFix τ fm)) ∧ p ∣ Nat.card B ∧
      ∀ f : Fin s → Multiplicative (ZMod p), fm (fun k => toAdd (f k)) =
        fun k => toAdd (Sum.elim (omPlusRefl p) sgnAut i f k) := by
    rintro (⟨⟨⟨i, j⟩, hij⟩, b⟩ | m)
    · cases b
      · exact ⟨pairWeyl h ε i j, pairBlock h ε i j, swapMap i j, pairWeyl_mem_pairBlock h i j,
          pairWeyl_conj h hτ i j, isComponentOf_pairBlock h hp hp2 hζ hτ hε hij.ne,
          dvd_card_pairBlock h hp hζ hij.ne, fun f => coord_swap i j f⟩
      · let c := MulAut.conj (lineWeyl h ε j)
        refine ⟨lineWeyl h ε j * pairWeyl h ε i j * (lineWeyl h ε j)⁻¹,
          (pairBlock h ε i j).map c.toMonoidHom, sswapMap i j,
          ⟨pairWeyl h ε i j, pairWeyl_mem_pairBlock h i j, rfl⟩, fun t => ?_, ?_, ?_,
          fun f => coord_sswap hij f⟩
        · have e : lineWeyl h ε j * pairWeyl h ε i j * (lineWeyl h ε j)⁻¹ * τ (ofAdd t) *
              (lineWeyl h ε j * pairWeyl h ε i j * (lineWeyl h ε j)⁻¹)⁻¹ =
              lineWeyl h ε j * (pairWeyl h ε i j * ((lineWeyl h ε j)⁻¹ * τ (ofAdd t) *
                lineWeyl h ε j) * (pairWeyl h ε i j)⁻¹) * (lineWeyl h ε j)⁻¹ := by group
          rw [e, hlinv, pairWeyl_conj h hτ, lineWeyl_conj h hp hζ.pow_eq_one hτ]
          rfl
        · rw [← hfixset i j]
          refine isComponentOf_map_centralizer (p := p) c.surjective (fun z hz => ?_)
            (fun z hz _ => c.map_eq_one_iff.mp (MonoidHom.mem_ker.mp hz)) ?_
            (isComponentOf_pairBlock h hp hp2 hζ hτ hε hij.ne)
          · rw [c.map_eq_one_iff.mp (MonoidHom.mem_ker.mp hz)]
            exact Subgroup.one_mem _
          · rintro _ ⟨u, -, rfl⟩
            rw [← map_pow, hpow1, map_one]
        · rw [Subgroup.card_map_of_injective c.injective]
          exact dvd_card_pairBlock h hp hζ hij.ne
    · exact ⟨lineWeyl h ε m, lineBlock h m, negMap m, lineWeyl_mem_lineBlock h m,
        lineWeyl_conj h hp hζ.pow_eq_one hτ m, isComponentOf_lineBlock h hp hp2 hpq hζ hτ hε m,
        dvd_card_lineBlock h hp hζ hτ m, fun f => coord_neg m f⟩
  choose wS B fm hwB hw hcompB hdvdB hfm using hdata
  have h' : ∀ g : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
      ∃ (π : Equiv.Perm (Fin s)) (σ : Fin s → ZMod p), (∀ i, σ i = 1 ∨ σ i = -1) ∧
        ∀ f f', g * τR f * g⁻¹ = τR f' → ∀ i, toAdd (f' (π i)) = σ i * toAdd (f i) := by
    intro g hg
    obtain ⟨w, rfl⟩ := hφs g
    have hlift : ∀ t t' : Fin s → ZMod p,
        φ w * φ (τ (ofAdd t)) * (φ w)⁻¹ = φ (τ (ofAdd t')) →
          w * τ (ofAdd t) * w⁻¹ = τ (ofAdd t') := by
      intro t t' htt'
      set z := (τ (ofAdd t'))⁻¹ * (w * τ (ofAdd t) * w⁻¹) with hz
      have hzker : z ∈ φ.ker := by
        rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, htt',
          inv_mul_cancel]
      have hc : Commute (τ (ofAdd t')) z := Subgroup.mem_center_iff.mp (hφker hzker) _
      have heq : w * τ (ofAdd t) * w⁻¹ = τ (ofAdd t') * z := by rw [hz]; group
      have hzp : z ^ p = 1 := by
        have h1 : (w * τ (ofAdd t) * w⁻¹) ^ p = 1 := by
          rw [show w * τ (ofAdd t) * w⁻¹ = MulAut.conj w (τ (ofAdd t)) from rfl, ← map_pow,
            ← map_pow, hpow1, map_one, map_one]
        rwa [heq, hc.mul_pow, ← map_pow, hpow1, map_one, one_mul] at h1
      rw [heq, hkerp z hzker hzp, mul_one]
    have hgn : ∀ t : Fin s → ZMod p, ∃ t', w * τ (ofAdd t) * w⁻¹ = τ (ofAdd t') := by
      intro t
      have hmem : φ w * τR (fun k => ofAdd (t k)) * (φ w)⁻¹ ∈ E :=
        hg _ (by rw [← hτE]; exact ⟨_, rfl⟩)
      rw [← hτE] at hmem
      obtain ⟨f', hf'⟩ := hmem
      exact ⟨fun k => toAdd (f' k), hlift _ _ hf'.symm⟩
    obtain ⟨π, σ, hσ, hrel⟩ := exists_signedPerm_of_normalizer h hp hζ hτ w hgn
    exact ⟨π, σ, hσ, fun f f' hff' i => hrel _ _ (hlift _ _ hff') i⟩
  refine RealKGModelRoot.ggKGRootDatumAt_of_signedModel hp hp2 hτinj hτE hτinj hτE h'
    (fun i => φ (wS i)) (fun i => (B i).map φ) ?_ (fun i => Subgroup.mem_map_of_mem φ (hwB i)) ?_
    (fun i => dvd_card_map hp hkerp (hdvdB i)) fun a ha J hJ hJa => hlayer a (hE.2 a ha) J hJ hJa
  · intro i f
    rw [hτapp, hτapp, ← map_inv, ← map_mul, ← map_mul, hw i, hfm i f]
  · intro i
    have hset : τR '' {f | Sum.elim (omPlusRefl p) sgnAut i f = f} = φ '' torusFix τ (fm i) := by
      ext x
      constructor
      · rintro ⟨f, hf, rfl⟩
        refine ⟨τ (ofAdd fun k => toAdd (f k)), ⟨ofAdd fun k => toAdd (f k), ?_, rfl⟩, rfl⟩
        change fm i (fun k => toAdd (f k)) = fun k => toAdd (f k)
        rw [hfm i f]
        exact congrArg (fun f' : Fin s → Multiplicative (ZMod p) => fun k => toAdd (f' k)) hf
      · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨fun k => ofAdd (toAdd u k), ?_, rfl⟩
        have h2 := (hfm i (fun k => ofAdd (toAdd u k))).symm.trans hu
        funext k
        exact Multiplicative.toAdd.injective (congrFun h2 k)
    rw [hset]
    refine isComponentOf_map_centralizer hφs hφker hkerp ?_ (hcompB i)
    rintro _ ⟨u, -, rfl⟩
    rw [← map_pow, hpow1, map_one]

end RealKGUSplit

open CFSG CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem ggTorusRootSL2_uSplit
    {K : Type} [Field K] [Finite K] {n d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd3 : d = 3 → ¬ p ∣ d) (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1) (hd : 3 ≤ d)
    (hchev : IsChevSimple 2 (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    ∃ r, GGTorusLift p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) ∧
      GGTorusRootSL2 p r (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  have hn2 : n ≠ 1 := by
    rintro rfl
    have h1 : p ∣ 1 := by simpa using hpn
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have h2 : 2 ^ n = 2 ^ 1 := congrArg Prod.snd heq
    exact hn2 (Nat.pow_right_injective le_rfl h2)
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun h => hdq (by rw [h.1, h.2])
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpn
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ :=
    TableBUE.center_proj_eq_bot hK hd hdq
  have hIp := NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn hd hq hp hpq'
  have hcp : GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
    rcases (show d ≤ 4 ∨ 5 ≤ d by omega) with hd4 | hd5
    · refine StdSubRestU.ggCenterPrime_unitary hK hn hd hdq hp hp2 fun hpd => ?_
      interval_cases d
      · exact hd3 rfl hpd
      · exfalso
        have hpd2 : p ∣ 2 ^ 2 := by simpa using hpd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd2))
    · exact ggCenterPrime_psu_unitary hK hd5 (fun h => hn2 (congrArg Prod.snd h)) hp hpq' hZ
  have hS : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.isSimpleGroup_of_isChevSimple_two hchev
  have hnc : ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)), a * b ≠ b * a := by
    have := hS.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
    by_contra hcon
    push Not at hcon
    apply hx
    have hxc : x ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
      Subgroup.mem_center_iff.mpr fun z => hcon z x
    rw [hZ] at hxc
    exact Subgroup.mem_bot.mp hxc
  have hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤ := by
    rcases hS.eq_bot_or_eq_top_of_normal (commutator _) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hmem : ⁅a, b⁆ ∈ commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hmem
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp hmem)
    · exact h
  refine ⟨0, TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (by omega)), ?_⟩
  refine ggTorusRootSL2_of_rootDatum hp hIp hZ hcp ?_
  exact RealKGUSplit.ggKGRootDatum_unitarySplit hK hn hd hp hpn hperf
    (fun a hap J hJ hJa => ggKG_layer_of_chevSimple hS hnc hchev hp hp2 hap hJ hJa) 0

private theorem ggRealRootSL2On_unitarySplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp5, htag, hpn⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hl2 : 2 ≤ l := hlab.2.1
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hn2 : 2 ≤ n := RealKGUSplit.two_le_of_dvd hp hn hpn
  have hmark : MarkedModel ⟨.twA, l, n⟩
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) := by
    simp only [MarkedModel, markTag, markRank, markChar, markDeg]
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    have h2 : 2 ^ n = 2 ^ 1 := congrArg Prod.snd h
    have := Nat.pow_right_injective le_rfl h2
    omega
  have hp2 : p ≠ 2 := by omega
  have hd3 : l + 1 = 3 → ¬ p ∣ l + 1 := by
    intro h hpd
    rw [h] at hpd
    have := Nat.le_of_dvd (by norm_num) hpd
    omega
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusRootSL2_uSplit hp hp2 hd3 hK hn hpn (by omega)
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
        (isChevTwo_of_markedModel hmark))⟩

theorem ggRealRootSL2On_uSplit :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .uSplit p lab :=
  fun p lab hp hlab hl hs =>
    ggRealRootSL2On_unitarySplit p lab hp hlab hl ⟨hs.1, hs.2.1, hs.2.2.1⟩

theorem ggRealRootSL2On_uSplitDvd :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .uSplitDvd p lab :=
  fun p lab hp hlab hl hs =>
    ggRealRootSL2On_unitarySplit p lab hp hlab hl ⟨hs.1, hs.2.1, hs.2.2.1⟩

end CFSG.StandardType

end
