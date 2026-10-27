module

public import CFSG.OddTranspositions.PartThree.EightEight.Shapes
public import CFSG.OddTranspositions.PartThree.Ten.SetupQ
public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.EightEight.BlockRebase
import CFSG.OddTranspositions.PartThree.EightEight.FibreOddCore
import CFSG.OddTranspositions.PartThree.EightEight.TheoremWBlock
import CFSG.OddTranspositions.PartThree.EightEight.WreathBlocks
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourAut
import CFSG.OddTranspositions.PartThree.EightEight.WreathSwapClass
import CFSG.OddTranspositions.PartThree.EightEight.WreathTransversal
import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
import CFSG.OddTranspositions.PartThree.Ten.TenTwoQ

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartThree.WreathEndgame

theorem exists_forall_commute_coordHom_of_mem_swapSet {f n : ℕ} (hn : 3 ≤ n)
    {s : L2Wreath f n} (hs : s ∈ swapSet f n) :
    ∃ i₀ : Fin n, ∀ b, Commute (SetupQ.coordHom f n i₀ b) s := by
  obtain ⟨i, j, hij, hright, hleft, -⟩ := hs
  have hlt : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton,
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hi₀i : i₀ ≠ i := fun h => hi₀ (by simp [h])
  have hi₀j : i₀ ≠ j := fun h => hi₀ (by simp [h])
  refine ⟨i₀, fun b => TenTwoQ.commute_coordHom (hleft i₀ hi₀i hi₀j) ?_ b⟩
  rw [hright]
  exact Equiv.swap_apply_of_ne_of_ne hi₀i hi₀j

theorem exists_perfect_center_le_of_mem_swapSet {Hs : Type*} [Group Hs] [Finite Hs] {f n : ℕ}
    (hf : 2 ≤ f) (hn : 3 ≤ n) {E : Set Hs} (hE : IsOddTranspClass E) {q : Hs →* L2Wreath f n}
    (hq : Function.Surjective q) (hker : q.ker = Subgroup.center Hs) {v : Hs}
    (hv : q v ∈ swapSet f n) :
    ∃ R : Subgroup Hs, ⁅R, R⁆ = R ∧ Subgroup.center Hs ≤ R ∧ ∀ r ∈ R, Commute r v := by
  obtain ⟨i₀, hi₀⟩ := exists_forall_commute_coordHom_of_mem_swapSet hn hv
  exact ⟨SetupQ.coordComm q i₀, SetupQ.commutator_coordComm q hq hf hker i₀,
    TenTwoQ.center_le_coordComm_of_three_le hf hn hE hq hker i₀,
    TenTwoQ.commute_of_mem_coordComm_of_ker_eq hker i₀ hi₀⟩

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem transversalCover_w3 (hC : HypothesisC D) {f k : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {m : Halpha D hC.alpha}
    (huniq : ∀ p ∈ DstarH hC, ∃! r, r ∈ DstarH hC ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) r =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ∧ Commute r m) :
    Function.Surjective (((φ : _ →* L2Wreath f k).comp
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))).comp
        (transversalGroup (DstarH hC) m).subtype) ∧
      (((φ : _ →* L2Wreath f k).comp
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))).comp
        (transversalGroup (DstarH hC) m).subtype).ker =
        Subgroup.center (transversalGroup (DstarH hC) m) ∧
      IsOddTranspClass ((transversalGroup (DstarH hC) m).subtype ⁻¹'
        {p | p ∈ DstarH hC ∧ Commute p m}) := by
  let π : Halpha D hC.alpha →* L2Wreath f k :=
    (φ : _ →* L2Wreath f k).comp (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
  have hπ : Function.Surjective π := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have huniqπ : ∀ p ∈ DstarH hC, ∃! r, r ∈ DstarH hC ∧ π r = π p ∧ Commute r m := by
    intro p hp
    obtain ⟨r, hr, huniqr⟩ := huniq p hp
    refine ⟨r, ⟨hr.1, ?_, hr.2.2⟩, ?_⟩
    · exact congrArg (fun x => φ x) hr.2.1
    · intro q hq
      exact huniqr q ⟨hq.1, φ.injective hq.2.1, hq.2.2⟩
  refine ⟨?_, ?_, ?_⟩
  · exact surjective_transversalGroup hπ (DstarH_closure_eq_top hC)
      (fun p hp => (huniqπ p hp).exists)
  · exact ker_transversalGroup_eq_center hπ
      (WreathEndgame.center_eq_bot_of_equiv hf (MulEquiv.refl _))
      (fun g x hx => DstarH_conj_mem hC hx) (DstarH_closure_eq_top hC) huniqπ
  · exact isOddTranspClass_transversalGroup hπ
      ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩ huniqπ

private theorem exists_perfect_w3 (hC : HypothesisC D) {f k : ℕ} (hf : 2 ≤ f) (hk : 3 ≤ k)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {d m : Halpha D hC.alpha} (hd : d ∈ DstarH hC)
    (hdsw : φ (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) d) ∈ swapSet f k)
    (hdm : Commute d m) (hm : m ∈ transversalGroup (DstarH hC) m)
    (huniq : ∀ p ∈ DstarH hC, ∃! r, r ∈ DstarH hC ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) r =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ∧ Commute r m) :
    ∃ R : Subgroup G, ⁅R, R⁆ = R ∧ (∀ r ∈ R, Commute r (d : G)) ∧
      (∀ r ∈ R, Commute r (m : G)) ∧ (m : G) ∈ R := by
  let H₁ := transversalGroup (DstarH hC) m
  let π : Halpha D hC.alpha →* L2Wreath f k :=
    (φ : _ →* L2Wreath f k).comp (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
  have hcover := transversalCover_w3 hC hf φ huniq
  have hq : Function.Surjective (π.comp H₁.subtype) := hcover.1
  have hker : (π.comp H₁.subtype).ker = Subgroup.center H₁ := hcover.2.1
  have hE₁ : IsOddTranspClass (H₁.subtype ⁻¹' {p | p ∈ DstarH hC ∧ Commute p m}) := hcover.2.2
  let dH : H₁ := ⟨d, Subgroup.subset_closure ⟨hd, hdm⟩⟩
  have hdsw' : (π.comp H₁.subtype) dH ∈ swapSet f k := by
    simpa [π, dH] using hdsw
  obtain ⟨R₁, hR₁perf, hZ₁, hR₁d⟩ :=
    exists_perfect_center_le_of_mem_swapSet hf hk hE₁ hq hker hdsw'
  let mH : H₁ := ⟨m, hm⟩
  have hmH : mH ∈ Subgroup.center H₁ := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (transversalGroup_le_centralizer (DstarH hC) m x.2)
  let R : Subgroup G := (R₁.map H₁.subtype).map (Halpha D hC.alpha).subtype
  have hRperf : ⁅R, R⁆ = R := by
    change ⁅(R₁.map H₁.subtype).map (Halpha D hC.alpha).subtype,
      (R₁.map H₁.subtype).map (Halpha D hC.alpha).subtype⁆ =
      (R₁.map H₁.subtype).map (Halpha D hC.alpha).subtype
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, hR₁perf]
  have hRd : ∀ r ∈ R, Commute r (d : G) := by
    intro r hr
    obtain ⟨rH, hrH, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨r₁, hr₁, rfl⟩ := Subgroup.mem_map.mp hrH
    exact TenTwoQ.commute_coe_iff.mp (TenTwoQ.commute_coe_iff.mp (hR₁d r₁ hr₁))
  have hRm : ∀ r ∈ R, Commute r (m : G) := by
    intro r hr
    obtain ⟨rH, hrH, rfl⟩ := Subgroup.mem_map.mp hr
    obtain ⟨r₁, hr₁, rfl⟩ := Subgroup.mem_map.mp hrH
    exact TenTwoQ.commute_coe_iff.mp
      (TenTwoQ.commute_coe_iff.mp (Subgroup.mem_center_iff.mp hmH r₁))
  have hmR : (m : G) ∈ R := by
    refine Subgroup.mem_map.mpr ⟨(mH : Halpha D hC.alpha), ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨mH, hZ₁ hmH, rfl⟩
  exact ⟨R, hRperf, hRd, hRm, hmR⟩

theorem false_of_perfect_of_mul_mem_swapSet (hC : HypothesisC D) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) {d m : G} (hdρ : d ∈ ρ) {hC' : HypothesisC D}
    (hα' : hC'.alpha = ρ) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ' : (Halpha D hC'.alpha ⧸ CFSG.solvableRadical (Halpha D hC'.alpha)) ≃* L2Wreath f k)
    {t : Halpha D hC'.alpha} (ht : (t : G) = d * m)
    (htsw : φ' (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC'.alpha)) t) ∈ swapSet f k)
    {R : Subgroup G} (hR : ⁅R, R⁆ = R) (hRd : ∀ r ∈ R, Commute r d)
    (hRm : ∀ r ∈ R, Commute r m) (hmR : m ∈ R) : False := by
  have hRK : R ≤ Subgroup.normalizer (Halpha D hC'.alpha : Set G) := by
    intro r hr
    have hconv : r * d * r⁻¹ ∈ ρ := by
      have h : r * d * r⁻¹ = d := by
        rw [(hRd r hr).eq]
        group
      rwa [h]
    have hrN : r ∈ Subgroup.normalizer ρ :=
      Nine.mem_normalizer_block_of_conj_mem hC hρ hdρ hconv
    have h := normalizer_le_normalizer_Halpha hC.setup.normal hrN
    simpa [hα'] using h
  have hdK : ∀ y ∈ Halpha D hC'.alpha, Commute d y := by
    intro y hy
    rw [hα'] at hy
    exact TenTwoQ.commute_of_mem_Halpha_block hdρ hy
  have hRz : ∀ r ∈ R, Commute r (t : G) := by
    intro r hr
    rw [ht]
    exact (hRd r hr).mul_right (hRm r hr)
  have hnot := inv_mul_notMem_of_mem_swapSet (K := Halpha D hC'.alpha)
    (N := CFSG.solvableRadical (Halpha D hC'.alpha)) hf hk φ' hRK hR hdK htsw hRz
  apply hnot
  have hdm : (d : G)⁻¹ * (t : G) = m := by
    rw [ht]
    group
  rwa [hdm]

theorem not_isStarTriangle_of_l2Wreath (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    (x w y : G) : ¬ IsStarTriangle hC x w y := by
  intro hst
  have hA : FibresAnticlique D hC.alpha :=
    fibresAnticlique_of_isStarTriangle h86 h87 hC hrad hO4 hF hne hst
  obtain ⟨ht, ⟨n, hn, -, hord⟩, hx, hw, hy, -⟩ := hst
  let M := CFSG.solvableRadical (Halpha D hC.alpha)
  let z : Halpha D hC.alpha := ⟨(x * y * w) ^ n, mul_mul_pow_mem_Halpha hC hx hw hy n⟩
  have hzsw : φ (QuotientGroup.mk' M z) ∈ swapSet f k :=
    mem_swapSet_of_l2Wreath h86 h87 hC hrad hO4 hF hne hns hf hk φ ht hx hw hy hn hord rfl
  obtain ⟨d, hd, hdz'⟩ := exists_mem_DstarH_eq_of_mem_swapSet hC hns hf hk φ hzsw
  have hdz : QuotientGroup.mk' M d = QuotientGroup.mk' M z := φ.injective hdz'
  obtain ⟨hmM, hm2, -, hmd, -, -⟩ := mul_mem_solvableRadical_and_commute h86 h87 hC hrad hO4 hF
    hne ht hx hw hy hn hord ((mem_DstarH_iff hC).mp hd) rfl hdz
  let xH : Halpha D hC.alpha := ⟨x, Subgroup.subset_closure hx⟩
  have hact : ∀ p ∈ DstarH hC, QuotientGroup.mk' M p = QuotientGroup.mk' M xH →
      d * z * p * (d * z)⁻¹ = xH * p * xH⁻¹ := fun p hp hpx =>
    (conj_eq_conj_of_mk_eq_mk_x h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord rfl rfl hd hdz
      hp hpx).2
  have huniq : ∀ p ∈ DstarH hC, ∃! r, r ∈ DstarH hC ∧
      QuotientGroup.mk' M r = QuotientGroup.mk' M p ∧ Commute r (d * z) := fun p hp =>
    existsUnique_mem_fibre_commute hC hA hmM hm2 ((mem_DstarH_iff hC).mpr hx) hact hp
  have hdsw : φ (QuotientGroup.mk' M d) ∈ swapSet f k := by
    rw [hdz']
    exact hzsw
  obtain ⟨R, hR, hRd, hRm, hmR⟩ := exists_perfect_w3 hC hf (by omega) φ hd hdsw hmd.symm
    (closure_conjOrbit_le_transversalGroup h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord rfl hd
      hdz).2 huniq
  obtain ⟨hdx, hdw, hdy⟩ := commute_of_mk_eq_of_isTriangle h86 h87 hC hrad hO4 hF hne ht hx hw hy
    hn hord rfl hd hdz
  obtain ⟨ρ, hρ, hdρ, hxS, hwS, hyS⟩ := exists_mem_Dalpha_mem_DalphaStar_of_isTriangle h86 h87 hC
    hrad hO4 hF hne ht hx hw hy hd hdx hdy hdw
  obtain ⟨hC', φ', t, hα', htz, htsw⟩ := exists_rebase_of_l2Wreath h86 h87 hC hrad hO4 hF hne hns
    hf hk φ ht hρ.1 hxS hwS hyS hn hord
  have hd2 : (d : G) * d = 1 := by
    simpa using congrArg Subtype.val ((DstarH_isOddTransp hC).mul_self_eq_one hd)
  refine false_of_perfect_of_mul_mem_swapSet hC hρ.1 hdρ hα' hf hk φ'
    (m := ((d * z : Halpha D hC.alpha) : G)) ?_ htsw hR hRd hRm hmR
  rw [htz, Subgroup.coe_mul, ← mul_assoc, hd2, one_mul]

theorem not_isStarTriangle_of_l2Wreath_three (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 3)
    (x w y : G) : ¬ IsStarTriangle hC x w y :=
  not_isStarTriangle_of_l2Wreath h86 h87 hC hrad hO4 hF hns hne hf (Or.inl rfl) φ x w y

theorem starWreath_three_of (h86 : Lemma8_6) (h87 : Theorem8_7) : StarWreath 3 := by
  intro G _ _ D hC hrad _ hns hF hO4 hneQ f hf ⟨φ⟩ x w y hst
  have hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2 := by
    intro heq
    apply hneQ
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 1,
      ← map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 2, heq]
  exact not_isStarTriangle_of_l2Wreath_three h86 h87 hC hrad hO4 hF hns hne hf φ x w y hst

end CFSG.OddTranspositions.PartThree.EightEight
