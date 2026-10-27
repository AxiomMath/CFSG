module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameTransport
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
import CFSG.LocalAnalysis.AGLEmbedding.SymThreeCentralExt
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.Mathlib.GroupTheory.PermCenter
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

set_option linter.style.haveILetI false

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

private theorem DSdDAux_section_symThree {Q : Type} [Group Q] [Finite Q]
    (f : Q →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hc : ∀ k ∈ f.ker, ∀ q : Q, k * q = q * k) (hodd : Odd (Nat.card f.ker)) :
    ∃ σ : Equiv.Perm (Fin 3) →* Q, ∀ g, f (σ g) = g := by
  obtain ⟨T, hTn, ⟨eT⟩, hTi⟩ :=
    CFSG.AGLEmbedding.SymThreeCentralExt.exists_normal_symThree f hf hc hodd
  have hbot : T ⊓ f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxT, hxk⟩ := hx
    have hcen : eT ⟨x, hxT⟩ ∈ Subgroup.center (Equiv.Perm (Fin 3)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨t, rfl⟩ := eT.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc x hxk (t : Q)).symm
    rw [CFSG.center_perm_eq_bot_of_three_le_card (by simp), Subgroup.mem_bot] at hcen
    have hx1 : (⟨x, hxT⟩ : ↥T) = 1 := eT.injective (by simpa using hcen)
    simpa using congrArg Subtype.val hx1
  have hinj : Function.Injective (f.comp T.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : (x : Q) ∈ T ⊓ f.ker := ⟨x.2, hx⟩
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  have hcard : Nat.card ↥T = Nat.card (Equiv.Perm (Fin 3)) :=
    Nat.card_congr eT.toEquiv
  have hbij : Function.Bijective (f.comp T.subtype) :=
    Nat.bijective_iff_injective_and_card _ |>.mpr ⟨hinj, hcard⟩
  let e := MulEquiv.ofBijective (f.comp T.subtype) hbij
  refine ⟨T.subtype.comp e.symm.toMonoidHom, fun g => ?_⟩
  exact e.apply_symm_apply g

private theorem DSdDAux_center_sl2 {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h : (r - 1) ^ 2 = 0 := by
    linear_combination hr + (1 - r) * (CharP.cast_eq_zero K 2)
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)
  refine Subtype.ext ?_
  rw [← hrA, hr1, map_one]
  rfl

private theorem DSdDAux_sl2_equiv_perm {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨f⟩ := CFSG.BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two hK
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (DSdDAux_center_sl2 (K := K))).trans
    QuotientGroup.quotientBot).symm.trans f⟩

private theorem DSdDAux_section_sl2_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {E : Type} [Group E] [Finite E]
    {π : E →* Matrix.SpecialLinearGroup (Fin 2) K} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin 2) K →* E, ∀ g, π (σ g) = g := by
  obtain ⟨e⟩ := DSdDAux_sl2_equiv_perm hK
  let f : E →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp π
  have hf : Function.Surjective f := e.surjective.comp hπ
  have hker : f.ker = π.ker := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, map_eq_one_iff e e.injective]
  have hc : ∀ k ∈ f.ker, ∀ q : E, k * q = q * k := by
    intro k hk q
    exact (Subgroup.mem_center_iff.mp (hcen (hker ▸ hk)) q).symm
  have hodd' : Odd (Nat.card f.ker) := hker ▸ hodd
  obtain ⟨σ, hσ⟩ := DSdDAux_section_symThree f hf hc hodd'
  refine ⟨σ.comp e.toMonoidHom, fun g => ?_⟩
  have h : e (π ((σ.comp e.toMonoidHom) g)) = e g := by
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hσ (e g)
  exact e.injective h


end CFSG.StandardType.HdRo7D

namespace CFSG.StandardType.HdRo7D

open CFSG.SectionRank.EvenCover

private theorem DSdDAux_sl2_lift_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {E G : Type} [Group E] [Finite E] [Group G]
    {π : E →* G} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) (ρ : Matrix.SpecialLinearGroup (Fin 2) K →* G) :
    ∃ ρ' : Matrix.SpecialLinearGroup (Fin 2) K →* E, ∀ g, π (ρ' g) = ρ g := by
  let P := CFSG.SectionRank.EvenCover.pullback π ρ
  have hPπ : Function.Surjective (CFSG.SectionRank.EvenCover.pullbackFst π ρ) :=
    CFSG.SectionRank.EvenCover.pullbackFst_surjective hπ ρ
  have hPcen : (CFSG.SectionRank.EvenCover.pullbackFst π ρ).ker ≤ Subgroup.center P :=
    CFSG.SectionRank.EvenCover.pullbackFst_ker_le_center hcen ρ
  have hPodd : Odd (Nat.card (CFSG.SectionRank.EvenCover.pullbackFst π ρ).ker) :=
    Odd.of_dvd_nat hodd (CFSG.SectionRank.EvenCover.card_pullbackFst_ker_dvd π ρ)
  obtain ⟨σ, hσ⟩ := DSdDAux_section_sl2_two hK hPπ hPcen hPodd
  refine ⟨(MonoidHom.snd (Matrix.SpecialLinearGroup (Fin 2) K) E).comp (P.subtype.comp σ),
    fun g => ?_⟩
  exact DFunLike.congr_fun (CFSG.SectionRank.EvenCover.comp_snd_section σ hσ) g


end CFSG.StandardType.HdRo7D

namespace CFSG.StandardType.HdRo7D

open CFSG.LieType.Universal.Spin

private theorem DSdDAux_section_spinPlus {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) {E : Type} [Group E] [Finite E]
    {π : E →* spinGroup (quadPlus n K)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadPlus n K) →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨O⟩ := CFSG.LieType.Steinberg.nonempty_commOrder_ofCartan
    (plusDatum n K hn).isFiniteType (Dv := (plusDatum n K hn).divisible) rfl
  have hC : ¬ 2 ∣ Nat.card π.ker := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  let hE := CFSG.LieType.Steinberg.SpinPlus.chevalleyExtras hn O
    CFSG.LieType.Steinberg.SpinPlus.commC
    (CFSG.LieType.Steinberg.SpinPlus.commutatorFormula hn O)
  exact (CFSG.LieType.Steinberg.existsUnique_section_of_sl2_lift
    (CFSG.LieType.Steinberg.SpinPlus.isCTGroupDatum hn)
    (CFSG.LieType.Universal.Spin.plusDatum_steinbergExtras hn)
    hE.param hE.rankOne hπ hcen hC
    (fun ρ => DSdDAux_sl2_lift_two hK hπ hcen hodd ρ)).exists


end CFSG.StandardType.HdRo7D

namespace CFSG.StandardType.HdRo7D

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

private theorem DSdDAux_section_spinMinus {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {E : Type} [Group E] [Finite E]
    {π : E →* spinGroup (quadMinus n K b c)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    ∃ σ : spinGroup (quadMinus n K b c) →* E, ∀ g, π (σ g) = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  have hC : ¬ 2 ∣ Nat.card π.ker := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  refine (CFSG.LieType.Steinberg.existsUnique_section_of_rankOne_lift
    (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirr hγ) hπ hcen hC
    fun i => ?_).exists
  by_cases hi : i.val + 1 < n - 1
  · obtain ⟨ρ', hρ'⟩ := DSdDAux_sl2_lift_two hK hπ hcen hodd
      ((minusFrame n b c).longSL2 (succ_ne_of_lt n hi) true false)
    exact CFSG.LieType.Steinberg.exists_lift_of_injective
      (CFSG.LieType.Steinberg.SpinFrame.longSL2_injective _ _ _ _)
      (rankOne_minusRootGroup_of_lt n hirr hi).le hρ'
  · exact CFSG.LieType.Steinberg.exists_rankOne_lift_of_rankOneRels
      (minusDatum_steinbergExtras n hirr) i (shortRels n hirr i)
      (CFSG.LieType.Steinberg.mem_minusRootGroup_single_iff hirr hi)
      (CFSG.LieType.Steinberg.mem_minusRootGroup_neg_single_iff hirr hi)
      (CFSG.LieType.Steinberg.shortRels_x_injective hirr i)
      (fun t ht h1 => CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.shortRels_h_eq_one' hirr i ht h1) hπ hcen hC


end CFSG.StandardType.HdRo7D

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.OrthRest
open CFSG.LieType.Universal.Spin

private theorem DSdDAux_centerPrime_RPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) (hK : Nat.card K = 2) :
    GGCenterPrime p (OrthRest.RPlus K m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, hZ⟩ := OrthRest.spinPlus_bij (K := K) hm
  have : NeZero m := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus m K)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadPlus)
  refine (OrthRest.center_data (R := OrthRest.RPlus K m)
    (MulEquiv.ofBijective _ hbij) hZ ?_ hp hp2).2
  intro E _ _ π hπ hcen hC
  exact DSdDAux_section_spinPlus hm hK hπ hcen (Nat.coprime_two_left.mp hC)

private theorem DSdDAux_centerPrime_RMinus {K : Type} [Field K] [Finite K] [CharP K 2]
    {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m) (hK : Nat.card K = 2)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGCenterPrime p (OrthRest.RMinus K m b c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, hZ⟩ := OrthRest.spinMinus_bij (K := K) (n := m + 1) (by omega) hirr
  have : NeZero (m + 1) := ⟨by omega⟩
  have : Finite (spinGroup (quadMinus (m + 1) K b c)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _
      (CFSG.LieType.Universal.Spin.coe_ker_spinMatrix_quadMinus hirr)
  refine (OrthRest.center_data (R := OrthRest.RMinus K m b c)
    ((MulEquiv.ofBijective _ hbij).trans (omegaMinusProjEquiv (m + 1) b c).symm) hZ ?_ hp hp2).2
  intro E _ _ π hπ hcen hC
  exact DSdDAux_section_spinMinus (n := m + 1) (by omega) hK hirr hπ hcen
    (Nat.coprime_two_left.mp hC)


end CFSG.StandardType.HdRo7D

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

private theorem DSdDAux_innerAction {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {R : Type} [Group R] (θ : (↥X ⧸ Subgroup.center ↥X) ≃* R)
    (hperf : commutator ↥X = ⊤) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hind : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet R,
      LargeEvenInduces θ (fun l l' : ↥X => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    ∀ b ∈ Bs, ∃ g ∈ X, ∀ y ∈ X, b * y * b⁻¹ = g * y * g⁻¹ := by
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (X : Set G) := hnorm hb
  have hbNin : b⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).inv_mem hbN
  obtain ⟨φ, hφI, hφ⟩ := hind b hb
  rw [LargeEvenInnSet, Set.mem_range] at hφI
  obtain ⟨w, hw⟩ := hφI
  obtain ⟨lq, hlq⟩ := θ.surjective w
  obtain ⟨l₀, hl₀⟩ := QuotientGroup.mk_surjective lq
  have hlqw : θ (QuotientGroup.mk l₀) = w := by rw [hl₀, hlq]
  have hcong : ∀ z : ↥X,
      (QuotientGroup.mk (l₀ * z * l₀⁻¹) : ↥X ⧸ Subgroup.center ↥X) =
      (QuotientGroup.mk (⟨b⁻¹ * (z : G) * b,
        by simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hbNin (z : G)).mp z.2⟩ : ↥X) :
        ↥X ⧸ Subgroup.center ↥X) := by
    intro z
    refine θ.injective ?_
    have h1 := hφ z ⟨b⁻¹ * (z : G) * b,
      by simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hbNin (z : G)).mp z.2⟩ rfl
    rw [← hw] at h1
    rw [← h1, MulAut.conj_apply, ← hlqw]
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  refine ⟨(l₀ : G)⁻¹, X.inv_mem l₀.2, ?_⟩
  intro y hy
  let yL : ↥X := ⟨y, hy⟩
  let g : G := (l₀ : G) * b
  have hmem : g ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer l₀.2) hbN
  let a : MulAut ↥X := Subgroup.normalizerMonoidHom X ⟨g, hmem⟩
  have ha : ∀ z : ↥X, ((a z : ↥X) : G) = g * (z : G) * g⁻¹ :=
    fun z => Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨g, hmem⟩ z
  have hZ : ∀ z : ↥X, a z * z⁻¹ ∈ Subgroup.center ↥X := by
    intro z
    let a' : ↥X := ⟨g * (z : G) * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hmem (z : G)).mp z.2⟩
    have haz : a z = a' := Subtype.ext (ha z)
    have hbz : b * (z : G) * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hbN (z : G)).mp z.2
    have hc := hcong ⟨b * (z : G) * b⁻¹, hbz⟩
    rw [QuotientGroup.eq] at hc
    have hc' : a'⁻¹ * z ∈ Subgroup.center ↥X := by
      convert hc using 1
      apply Subtype.ext
      simp only [a', g, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h1 : a' * z⁻¹ = (a'⁻¹ * z)⁻¹ := by
      rw [show a' * z⁻¹ = (z * a'⁻¹)⁻¹ by group]
      congr 1
      have h := Subgroup.mem_center_iff.mp hc' a'⁻¹
      rw [mul_assoc] at h
      exact (mul_left_cancel h).symm
    rw [haz, h1]
    exact (Subgroup.center ↥X).inv_mem hc'
  have hg1 := hdRo7SULCoordAux_modCenter_eq_one hperf a hZ
  have hy1 : g * y * g⁻¹ = y := by
    have h := congrArg (fun f : MulAut ↥X => (f yL : G)) hg1
    simp only [MulAut.one_apply] at h
    rw [ha yL] at h
    exact h
  calc b * y * b⁻¹ = (l₀ : G)⁻¹ * (g * y * g⁻¹) * l₀ := by
        simp only [g]
        group
    _ = (l₀ : G)⁻¹ * y * l₀ := by rw [hy1]
    _ = (l₀ : G)⁻¹ * y * ((l₀ : G)⁻¹)⁻¹ := by group


end CFSG.StandardType.HdRo7D

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

private theorem DSdDAux_centerCoprime {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {R : Type} [Group R] {p : ℕ} (θ : (↥X ⧸ Subgroup.center ↥X) ≃* R)
    (hperf : commutator ↥X = ⊤) (hcpR : GGCenterPrime p R) :
    ¬ p ∣ Nat.card (Subgroup.center ↥X) := by
  have hψ : Function.Surjective (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))) :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))).ker ≤
      Subgroup.center ↥X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ θ.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  exact hcpR ↥X _ hψ hker hperf

private theorem DSdDAux_frame_plus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {G : Type} [Group G] [Finite G] {X : Subgroup G} {m : ℕ}
    (hm : 4 ≤ m)
    (θ : (↥X ⧸ Subgroup.center ↥X) ≃* OrthRest.RPlus K m)
    (hFr : DFrameOmegaLeaf) (hcop : ¬ 3 ∣ Nat.card (Subgroup.center ↥X)) :
    GGTorusOrthFrameSC 3 ↥X m := by
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hfin : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card (R := K) (η := Fin m ⊕ Fin m)]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hfrQ := hFr K (Fin m ⊕ Fin m → K) (TableBOrth.qPlusForm K m)
    (TableBOrth.nondegenerate_qPlusForm m) 3 Nat.prime_three (by norm_num) h3 m hfin hm
  have hfrR : GGTorusOrthFrameSC 3 (OrthRest.RPlus K m) m :=
    ggTorusOrthFrameSC_of_mulEquiv (OrthTorus.rPlusEquiv K (by omega)).symm hfrQ
  have hfrQuot : GGTorusOrthFrameSC 3 (↥X ⧸ Subgroup.center ↥X) m :=
    ggTorusOrthFrameSC_of_mulEquiv θ.symm hfrR
  exact ggTorusOrthFrameSC_of_centralCover Nat.prime_three
    (QuotientGroup.mk' (Subgroup.center ↥X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hcop hfrQuot

private theorem DSdDAux_frame_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {G : Type} [Group G] [Finite G] {X : Subgroup G} {m n : ℕ}
    (hn : n = m + 1)
    (hm : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (θ : (↥X ⧸ Subgroup.center ↥X) ≃* OrthRest.RMinus K m b c)
    (hFr : DFrameOmegaLeaf) (hcop : ¬ 3 ∣ Nat.card (Subgroup.center ↥X)) :
    GGTorusOrthFrameSC 3 ↥X n := by
  have h3 : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hfin : Module.finrank K (LargeEvenMinusIdx m → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card (R := K) (η := LargeEvenMinusIdx m)]
    simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
    omega
  have hfrQ := hFr K (LargeEvenMinusIdx m → K) (TableBOrth.qMinusForm K m b c)
    (TableBOrth.nondegenerate_qMinusForm m hirr) 3 Nat.prime_three (by norm_num) h3 n hfin hm
  have hfrR : GGTorusOrthFrameSC 3 (OrthRest.RMinus K m b c) n :=
    ggTorusOrthFrameSC_of_mulEquiv (OrthTorus.rMinusEquiv K m b c).symm hfrQ
  have hfrQuot : GGTorusOrthFrameSC 3 (↥X ⧸ Subgroup.center ↥X) n :=
    ggTorusOrthFrameSC_of_mulEquiv θ.symm hfrR
  exact ggTorusOrthFrameSC_of_centralCover Nat.prime_three
    (QuotientGroup.mk' (Subgroup.center ↥X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hcop hfrQuot


end CFSG.StandardType.HdRo7D

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

theorem d_sideData (hRig : GGLabelRigidInput) (hFr : DFrameOmegaLeaf) {G : Type} [Group G]
    [Finite G] {p : ℕ} (hp3 : p = 3) {Bs X : Subgroup G} (hM : GGInnerDiagOn Bs X)
    {lab : LargeEvenLabel} (hlabΛ : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) (htag : lab.tag = .D ∨ lab.tag = .twD)
    (hn : lab.n = 1) (hr : 4 ≤ lab.rank) :
    Bs ≤ Subgroup.normalizer (X : Set G) ∧
      (∀ b ∈ Bs, ∃ g ∈ X, ∀ y ∈ X, b * y * b⁻¹ = g * y * g⁻¹) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥X) ∧ GGTorusOrthFrameSC p ↥X lab.rank := by
  have hmark := ggInnerDiagOn_relabel hRig hM hlabΛ hhas
  obtain ⟨hperf, lab', hlab', hraw⟩ := hmark
  obtain ⟨R₀, iR₀, I₀, F₀, hsimple₀, hna₀, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hlab_eq : lab' = lab := hP₀.1
  rw [hlab_eq] at hraw
  rcases htag with hD | hD
  · have hr3 : lab.rank ≠ 3 := by omega
    simp only [CFSG.Assembly.LargeEvenRawDatumLegacy, hD, if_neg hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, hdata⟩ := hraw
    obtain ⟨-, -, θ, hP⟩ := hdata
    letI : Field K := hKfield
    letI : Finite K := hKfin
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (p := 2) (k := 1) Nat.prime_two (by norm_num) (by rw [hKcard, hn])
    have hK2 : Nat.card K = 2 := by
      rw [hKcard, hn]
      norm_num
    have hm4 : 4 ≤ lab.rank := by omega
    have hcpR : GGCenterPrime 3 (OrthRest.RPlus K lab.rank) :=
      DSdDAux_centerPrime_RPlus (K := K) (m := lab.rank) Nat.prime_three
        (by norm_num) (by omega) hK2
    have hcop3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥X) :=
      DSdDAux_centerCoprime (θ := θ) hperf hcpR
    have hcop : ¬ p ∣ Nat.card (Subgroup.center ↥X) := by rwa [hp3]
    have hinner := DSdDAux_innerAction (θ := θ) hperf hP.2.1 hP.2.2
    have hframe : GGTorusOrthFrameSC p ↥X lab.rank := by
      rw [hp3]
      exact DSdDAux_frame_plus hK2 hm4 θ hFr hcop3
    exact ⟨hP.2.1, hinner, hcop, hframe⟩
  · have hr2 : lab.rank ≠ 2 := by omega
    have hr3 : lab.rank ≠ 3 := by omega
    simp only [CFSG.Assembly.LargeEvenRawDatumLegacy, hD, if_neg hr2, if_neg hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, b, c, hirr, hdata⟩ := hraw
    obtain ⟨-, -, θ, hP⟩ := hdata
    letI : Field K := hKfield
    letI : Finite K := hKfin
    haveI : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (p := 2) (k := 1) Nat.prime_two (by norm_num) (by rw [hKcard, hn])
    have hK2 : Nat.card K = 2 := by
      rw [hKcard, hn]
      norm_num
    have hm3 : 3 ≤ lab.rank - 1 := by omega
    have hcpR : GGCenterPrime 3 (OrthRest.RMinus K (lab.rank - 1) b c) :=
      DSdDAux_centerPrime_RMinus (K := K) (m := lab.rank - 1) Nat.prime_three
        (by norm_num) hm3 hK2 hirr
    have hcop3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥X) :=
      DSdDAux_centerCoprime (θ := θ) hperf hcpR
    have hcop : ¬ p ∣ Nat.card (Subgroup.center ↥X) := by rwa [hp3]
    have hinner := DSdDAux_innerAction (θ := θ) hperf hP.2.1 hP.2.2
    have hframe : GGTorusOrthFrameSC p ↥X lab.rank := by
      rw [hp3]
      exact DSdDAux_frame_minus (K := K) (m := lab.rank - 1) (n := lab.rank) hK2
        (by omega) (by omega) hirr θ hFr hcop3
    exact ⟨hP.2.1, hinner, hcop, hframe⟩


end CFSG.StandardType.HdRo7D

