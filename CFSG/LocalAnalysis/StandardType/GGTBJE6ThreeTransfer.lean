module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeData
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeWeylIso
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeDatum
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus
public import CFSG.LieType.Chevalley.RootCharacterKernelProduct

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem e6c3t_cartan_symm (i j : Fin Tag.E6.rank) :
    Tag.cartan Tag.E6 i j = Tag.cartan Tag.E6 j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem e6c3t_cartan_mul_single (i k : Fin Tag.E6.rank) :
    (∑ l, Tag.cartan Tag.E6 i l * (Pi.single k 1 : Fin Tag.E6.rank → ℤ) l) =
      Tag.cartan Tag.E6 i k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    rw [Pi.single_eq_of_ne hl, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem e6c3t_cartan_sum_inv (w : WeylGroup Tag.E6) :
    ∀ i j : Fin Tag.E6.rank,
      (∑ l, Tag.cartan Tag.E6 j l *
          (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) l) =
        ∑ l, Tag.cartan Tag.E6 i l *
          (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l := by
  let P : WeylGroup Tag.E6 → Prop := fun w => ∀ i j : Fin Tag.E6.rank,
    (∑ l, Tag.cartan Tag.E6 j l *
        (w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) l) =
      ∑ l, Tag.cartan Tag.E6 i l *
        (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l
  refine weyl_induction P ?_ ?_ w
  · intro i j
    simp only [inv_one, one_smul]
    rw [e6c3t_cartan_mul_single j i, e6c3t_cartan_mul_single i j, e6c3t_cartan_symm i j]
  · intro m u ih i j
    have hinv : (simple Tag.E6 m * u)⁻¹ = u⁻¹ * simple Tag.E6 m := by
      rw [mul_inv_rev,
        inv_eq_of_mul_eq_one_right ((coxeterSystem Tag.E6).simple_mul_simple_self m)]
    have hL : (∑ l, Tag.cartan Tag.E6 j l *
        ((simple Tag.E6 m * u)⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) l) =
        (∑ l, Tag.cartan Tag.E6 i l *
            (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l) -
          Tag.cartan Tag.E6 m i *
            ∑ l, Tag.cartan Tag.E6 m l *
              (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l := by
      rw [hinv, mul_smul, simple_smul, reflect, e6c3t_cartan_mul_single m i, smul_sub,
        smul_comm (u⁻¹) (Tag.cartan Tag.E6 m i)]
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      congr 1
      · exact ih i j
      · rw [show (∑ x, Tag.cartan Tag.E6 j x *
              (Tag.cartan Tag.E6 m i • (u⁻¹ • (Pi.single m 1 : Fin Tag.E6.rank → ℤ))) x) =
              Tag.cartan Tag.E6 m i * ∑ x, Tag.cartan Tag.E6 j x *
                (u⁻¹ • (Pi.single m 1 : Fin Tag.E6.rank → ℤ)) x from by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => by
              simp only [Pi.smul_apply, smul_eq_mul]; ring]
        exact congrArg (fun z => Tag.cartan Tag.E6 m i * z) (ih m j)
    have hR : (∑ l, Tag.cartan Tag.E6 i l *
        ((simple Tag.E6 m * u) • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l) =
        (∑ l, Tag.cartan Tag.E6 i l *
            (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l) -
          (∑ l, Tag.cartan Tag.E6 m l *
              (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l) * Tag.cartan Tag.E6 i m := by
      rw [mul_smul, simple_smul, reflect]
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      congr 1
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ x, Tag.cartan Tag.E6 i x * ((∑ l, Tag.cartan Tag.E6 m l *
              (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l) *
                (Pi.single m 1 : Fin Tag.E6.rank → ℤ) x)) =
            (∑ l, Tag.cartan Tag.E6 m l *
              (u • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) l) *
              ∑ x, Tag.cartan Tag.E6 i x * (Pi.single m 1 : Fin Tag.E6.rank → ℤ) x from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring]
      rw [e6c3t_cartan_mul_single i m]
    rw [hL, hR, e6c3t_cartan_symm m i]
    ring

private theorem e6c3t_conj_simple_eq_of_smul {w : WeylGroup Tag.E6} {j k : Fin Tag.E6.rank}
    (hwj : w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = Pi.single k 1) :
    w * simple Tag.E6 j * w⁻¹ = simple Tag.E6 k := by
  apply ext_single
  intro i
  rw [smul_conj_simple w j (Pi.single i 1), hwj, simple_smul, reflect,
    e6c3t_cartan_mul_single k i]
  rw [e6c3t_cartan_sum_inv w i j, hwj, e6c3t_cartan_mul_single i k,
    e6c3t_cartan_symm i k]

private theorem e6c3t_rootReflection_single (k : Fin Tag.E6.rank) :
    rootReflection (Pi.single k 1 : Fin Tag.E6.rank → ℤ) = simple Tag.E6 k := by
  unfold rootReflection
  rw [dif_pos (isRoot_single Tag.E6 k)]
  exact e6c3t_conj_simple_eq_of_smul
    (Classical.choose_spec
      (Classical.choose_spec (isRoot_iff_exists_smul_single.1 (isRoot_single Tag.E6 k))))

private theorem e6c3t_excRefl_single (k : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    ExcSplitRootGen.excRefl (p := 3) (Pi.single k 1 : Fin Tag.E6.rank → ℤ) x =
      adRefl Tag.E6 3 k x := by
  rw [ExcSplitRootGen.excRefl, e6c3t_rootReflection_single k, adAct_simple]

theorem ggE6Three_coordData_of_frameA
    {G : Type} [Group G] [Finite G] {Bs J X : Subgroup G} {g : G}
    (hBs : IsElemAbelian 3 Bs)
    (hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ 3 = 1 → a ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hgBs : g ∈ Bs) (hJX : J ≤ X)
    (hgX : ∃ l ∈ X, g * l * g⁻¹ ≠ l)
    (hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G)))
    (hKer : ∀ n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)),
      ggTDρA hN n = 1 → ggTDρB X Bs n = 1)
    {κ : ↥(ggGamma X hN).range →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hF : GGE6ThreeFrameA (ggGamma X hN).range κ) {P : Subgroup ↥X → Prop}
    (hCall : ∀ (y : ↥(ggGamma X hN).range) (J' : Subgroup ↥X), y ≠ 1 →
      IsComponentOf J' (fixSubgroup (y : MulAut ↥X)) →
        GGE6ThreeClassA (ggGamma X hN).range κ y J' (P J')) :
    GGE6ThreeCoordData Bs X J g hgBs (P (J.subgroupOf X)) := by
  classical
  let γ := ggGamma X hN
  let cd : ↥Bs →* Multiplicative (Fin Tag.E6.rank → ZMod 3) := κ.comp γ.rangeRestrict
  have hcd_one : ∀ b : ↥Bs, cd b = 1 ↔ γ b = 1 := by
    intro b
    constructor
    · intro h
      have h' : κ (γ.rangeRestrict b) = κ 1 := by
        change cd b = κ 1
        rw [h, map_one]
      exact congrArg Subtype.val (hF.1 h')
    · intro h
      change κ (γ.rangeRestrict b) = 1
      rw [show γ.rangeRestrict b = 1 from Subtype.ext h, map_one]
  have hcd_of_mem : ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (X : Set G) → cd b = 1 :=
    fun b hb => (hcd_one b).2 ((ggGamma_eq_one_iff X hN b).2 hb)
  have hcd_range : cd.range = κ.range := by
    change (κ.comp γ.rangeRestrict).range = κ.range
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr γ.rangeRestrict_surjective]
    exact (MonoidHom.range_eq_map κ).symm
  have hrange : cd.range = ⊤ ∨
      ∀ x, Multiplicative.ofAdd x ∈ cd.range ↔ x ∈ NoOffRest.hypE6 := by
    rcases hF.2.1 with h | h
    · left; rwa [hcd_range]
    · right; intro x; rw [hcd_range]; exact h x
  have hgamma_rho : ∀ (n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (b : ↥Bs),
      γ (ggTDρB X Bs n b) =
        ((ggTDρA hN n ⟨γ b, ⟨b, rfl⟩⟩ : ↥(ggGamma X hN).range) : MulAut ↥X) := by
    intro n b
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    dsimp only [γ]
    simp only [ggGamma_coe, ggTDρB_apply, ggTDρA_apply, MulAut.mul_apply, MulAut.conj_apply,
      MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcd_rho : ∀ (n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (b : ↥Bs),
      cd (ggTDρB X Bs n b) = κ (ggTDρA hN n ⟨γ b, ⟨b, rfl⟩⟩) := by
    intro n b
    change κ (γ.rangeRestrict (ggTDρB X Bs n b)) = κ (ggTDρA hN n ⟨γ b, ⟨b, rfl⟩⟩)
    rw [show γ.rangeRestrict (ggTDρB X Bs n b) = ggTDρA hN n ⟨γ b, ⟨b, rfl⟩⟩ from
      Subtype.ext (hgamma_rho n b)]
  have hKer' : ∀ n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)),
      (∀ b : ↥Bs, cd (ggTDρB X Bs n b) = cd b) → ggTDρB X Bs n = 1 := by
    intro n hn
    apply hKer n
    apply MulEquiv.ext
    intro a
    obtain ⟨b, hb⟩ := a.2
    have ha : a = ⟨γ b, ⟨b, rfl⟩⟩ := Subtype.ext hb.symm
    rw [ha]
    have h1 := hn b
    rw [hcd_rho n b] at h1
    exact hF.1 (h1.trans (show cd b = κ ⟨γ b, ⟨b, rfl⟩⟩ from rfl))
  have hnorm : ∀ n : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)), ∃ u : WeylGroup Tag.E6,
      ∀ b : ↥Bs, cd (ggTDρB X Bs n b) =
        Multiplicative.ofAdd (adAct Tag.E6 3 u (Multiplicative.toAdd (cd b))) := by
    intro n
    obtain ⟨u, hu⟩ := hF.2.2.2 (⟨(n : G), n.2.1⟩ : ↥X)
      (conj_mem_normalizer_range_ggGamma hN n.2.1 n.2.2)
    refine ⟨u, fun b => ?_⟩
    have hcond : (γ (ggTDρB X Bs n b) : MulAut ↥X) =
        MulAut.conj (⟨(n : G), n.2.1⟩ : ↥X) * (γ b : MulAut ↥X) *
          (MulAut.conj (⟨(n : G), n.2.1⟩ : ↥X))⁻¹ := by
      rw [hgamma_rho n b, ggTDρA_apply]
    have h := hu ⟨γ b, ⟨b, rfl⟩⟩
      ⟨γ (ggTDρB X Bs n b), ⟨ggTDρB X Bs n b, rfl⟩⟩ hcond
    change κ (γ.rangeRestrict (ggTDρB X Bs n b)) =
      Multiplicative.ofAdd (adAct Tag.E6 3 u (Multiplicative.toAdd (κ (γ.rangeRestrict b))))
    rw [show γ.rangeRestrict (ggTDρB X Bs n b) =
          ⟨γ (ggTDρB X Bs n b), ⟨ggTDρB X Bs n b, rfl⟩⟩ from rfl,
        show γ.rangeRestrict b = ⟨γ b, ⟨b, rfl⟩⟩ from rfl, ← h, ofAdd_toAdd]
  choose n0 hn0 h0 using fun k =>
    hF.2.2.1 (Pi.single k 1) (isRoot_single Tag.E6 k)
  have hW0 : ∀ k, GGTorusWeylElt 3 (ggGamma X hN).range (n0 k) := fun k => (h0 k).1
  have hcoord0 : ∀ (k : Fin Tag.E6.rank) (a : ↥(ggGamma X hN).range),
      Multiplicative.toAdd (κ (ggConjAut (ggGamma X hN).range (hn0 k) a)) =
        ExcSplitRootGen.excRefl (p := 3) (Pi.single k 1) (Multiplicative.toAdd (κ a)) :=
    fun k a => (h0 k).2.2 a
  let nk : Fin 6 → ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) := fun k =>
    ⟨n0 k, (n0 k).2, mem_normalizer_of_ggTorusWeylElt hN hSC (hW0 k)⟩
  have hnk : ∀ (k : Fin 6) (b : ↥Bs), cd (ggTDρB X Bs (nk k) b) =
      Multiplicative.ofAdd (adRefl Tag.E6 3 k (Multiplicative.toAdd (cd b))) := by
    intro k b
    have hρ : ggTDρA hN (nk k) = ggConjAut (ggGamma X hN).range (hn0 k) := by
      apply MulEquiv.ext; intro a; apply Subtype.ext; rfl
    have hcdk := hcd_rho (nk k) b
    rw [hρ] at hcdk
    rw [hcdk, ← ofAdd_toAdd (κ (ggConjAut (ggGamma X hN).range (hn0 k)
        ⟨γ b, ⟨b, rfl⟩⟩)), hcoord0 k ⟨γ b, ⟨b, rfl⟩⟩, e6c3t_excRefl_single k]
    rw [show κ ⟨γ b, ⟨b, rfl⟩⟩ = cd b from rfl]
  obtain ⟨f, κW, hf, hκW, hcdW, hTD, hclos⟩ :=
    e6Three_exists_weylIso cd hrange hKer' hnorm nk hnk
  let φ : Fin 6 → MulAut ↥Bs := fun k => ggTDρB X Bs (nk k)
  have hadd : ∀ (k : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3),
      adRefl Tag.E6 3 k (adRefl Tag.E6 3 k x) = x := by
    intro k x
    have h : adRefl Tag.E6 3 k = adAct Tag.E6 3 (simple Tag.E6 k) := by
      funext y; exact (adAct_simple (τ := Tag.E6) (p := 3) k y).symm
    rw [h, ← adAct_mul, (coxeterSystem Tag.E6).simple_mul_simple_self k, adAct_one]
  have hφ2 : ∀ k, φ k * φ k = 1 := by
    intro k
    rw [← map_mul]
    apply hKer'
    intro b
    rw [map_mul, MulAut.mul_apply, hnk k (ggTDρB X Bs (nk k) b), hnk k b, toAdd_ofAdd,
      hadd k (Multiplicative.toAdd (cd b)), ofAdd_toAdd]
  have hfixZ : ∀ (k : Fin Tag.E6.rank) (z : ↥Bs), cd z = 1 → φ k z = z := by
    intro k z hz
    have hzC : (z : G) ∈ Subgroup.centralizer (X : Set G) :=
      (ggGamma_eq_one_iff X hN z).1 ((hcd_one z).1 hz)
    apply Subtype.ext
    rw [ggTDρB_apply]
    have hcomm : ((nk k : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G) * (z : G) =
        (z : G) * ((nk k : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G) :=
      Subgroup.mem_centralizer_iff.mp hzC _ (nk k).2.1
    calc ((nk k : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G) * (z : G) *
            ((nk k : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G)⁻¹
        = (z : G) * (((nk k : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G) *
            ((nk k : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G)⁻¹) := by
          rw [hcomm]; group
      _ = (z : G) := by group
  obtain ⟨V, hVadd, hVmod, ι, h, α, hlin, hrefl, hpair, hα⟩ :=
    e6Three_datum_of_coords hBs cd hrange φ hφ2 (fun k b => hnk k b) hfixZ
  have hcdg : cd ⟨g, hgBs⟩ ≠ 1 := by
    intro h1
    have h2 := (ggGamma_eq_one_iff X hN ⟨g, hgBs⟩).1 ((hcd_one ⟨g, hgBs⟩).1 h1)
    obtain ⟨l, hlX, hl⟩ := hgX
    exact hl (mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.mp h2 l hlX).symm)
  have hy : (ggGamma X hN).rangeRestrict ⟨g, hgBs⟩ ≠ 1 := by
    intro h1
    apply hcdg
    change κ ((ggGamma X hN).rangeRestrict ⟨g, hgBs⟩) = 1
    rw [h1, map_one]
  have hJ' : IsComponentOf (J.subgroupOf X)
      (fixSubgroup (((ggGamma X hN).rangeRestrict ⟨g, hgBs⟩ : ↥(ggGamma X hN).range) :
        MulAut ↥X)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr
      (isComponentOf_subgroupOf_fixSubgroup hN ⟨g, hgBs⟩ hcomp)
  obtain ⟨F, hFfield, ζ, hζ, hζo, i, hker, hreal, hD4⟩ := hCall _ _ hy hJ'
  unfold GGE6ThreeCoordData
  refine ⟨V, hVadd, hVmod, ι, φ, h, α, f, κW, cd, F, hFfield, ζ, hζ, hζo, hlin, hrefl, hpair,
    hf, hclos, hκW, hα, hrange, hcdW, hTD, hcd_of_mem, hcdg, i, ?_, ?_, hD4⟩
  ·
    intro b hb
    have hfix := hker ((ggGamma X hN).rangeRestrict b) hb
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h1 := congrArg Subtype.val (hfix ⟨j, hJX hj⟩ (Subgroup.mem_subgroupOf.2 hj))
    change ((ggGamma X hN b ⟨j, hJX hj⟩ : ↥X) : G) = j at h1
    rw [ggGamma_coe] at h1
    change (b : G) * j * (b : G)⁻¹ = j at h1
    calc j * (b : G) = ((b : G) * j * (b : G)⁻¹) * (b : G) := by rw [h1]
      _ = (b : G) * j := by group
  ·
    intro c hc
    obtain ⟨n, hn, hnJ, hW, hcoord⟩ := hreal c hc
    have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
      mem_normalizer_of_ggTorusWeylElt hN hSC hW
    have hnJ' : (n : G) ∈ J := Subgroup.mem_subgroupOf.1 hnJ
    refine ⟨⟨(n : G), hnJ', hnN⟩, fun b => ?_⟩
    have hρB : ggTDρB J Bs ⟨(n : G), hnJ', hnN⟩ b = ggTDρB X Bs ⟨(n : G), n.2, hnN⟩ b := by
      apply Subtype.ext
      rfl
    rw [hρB, hcd_rho ⟨(n : G), n.2, hnN⟩ b]
    have hρ : ggTDρA hN (⟨(n : G), n.2, hnN⟩ : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) =
        ggConjAut (ggGamma X hN).range hn := by
      apply MulEquiv.ext; intro a; apply Subtype.ext; rfl
    rw [hρ, ← ofAdd_toAdd (κ (ggConjAut (ggGamma X hN).range hn ⟨γ b, ⟨b, rfl⟩⟩)),
      hcoord ⟨γ b, ⟨b, rfl⟩⟩]
    rw [show κ ⟨γ b, ⟨b, rfl⟩⟩ = cd b from rfl]

end CFSG.StandardType

end
