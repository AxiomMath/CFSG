module

public import CFSG.LocalAnalysis.StandardType.GGF4N2RootAut
public import CFSG.LocalAnalysis.StandardType.GGF4N2ActualH0
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
import CFSG.LargeExtraspecial.S5Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
import CFSG.Quasithin.Recognition.St84.L2Group
import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5L2T
import CFSG.GroupTheory.DisjointSupCard
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.ComponentClassification.Foote47L216KernelFour
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.Quasithin.Vol2.Ch8Sec2L828USL2Card
import CFSG.ClassicalInvolution.WeakCT.Center
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTBlocks
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.N2PlaneGroup
import CFSG.LocalAnalysis.StandardType.GGF4N2MixedPower
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Gen
import CFSG.GroupTheory.ConjTransport
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.RankThree.PartOne.K159.PerfNormalizer
import CFSG.LocalAnalysis.StandardType.GGF4N2OmegaK
import CFSG.LocalAnalysis.StandardType.GGE0ShapeConjAux
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourEndsAbsorb
import CFSG.LocalAnalysis.StandardType.GGF4N2GoodLine
import CFSG.RankThree.PartOne.S12.Sec1511Y3

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem ggN2_mem_normalizer_of_commonComponent {d : G} {J M : Subgroup G}
    (hJd : CFSG.Open.IsComponentOf J (Subgroup.centralizer {d})) (hMJ : M ≤ J)
    (hMna : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) {g : G}
    (hgM : g ∈ Subgroup.centralizer (M : Set G)) (hgd : g ∈ Subgroup.centralizer {d}) :
    g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hJ' : CFSG.Open.IsComponentOf (J.map (MulAut.conj g).toMonoidHom)
      (Subgroup.centralizer {d}) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.IsComponentOf.map_conj hJd hgd
  obtain ⟨a, ha, b, hb, hab⟩ := hMna
  apply hab
  have hb' : b ∈ J.map (MulAut.conj g).toMonoidHom := by
    refine ⟨b, hMJ hb, ?_⟩
    have hgb : b * g = g * b := Subgroup.mem_centralizer_iff.mp hgM b hb
    change g * b * g⁻¹ = b
    rw [← hgb, mul_inv_cancel_right]
  exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hJd hJ' (fun h => hne h.symm)
    (hMJ ha) hb'

omit [Finite G] in
theorem ggN2_eq_one_of_commute_psl216 {I : Subgroup G}
    (eI : ↥I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :
    ∀ y ∈ I, (∀ z ∈ I, y * z = z * y) → y = 1 := by
  intro y hy hc
  have hcen : eI ⟨y, hy⟩ ∈ Subgroup.center
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨z, rfl⟩ := eI.surjective w
    rw [← map_mul, ← map_mul]
    exact congrArg eI (Subtype.ext (hc z z.2).symm)
  rw [CFSG.Quasithin.St84.psl2_center_eq_bot, Subgroup.mem_bot] at hcen
  have h1 : (⟨y, hy⟩ : I) = 1 := eI.injective (hcen.trans (map_one eI).symm)
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem ggN2_exists_five_normalizer_psl216 {I : Subgroup G}
    (eI : ↥I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) :
    ∃ c ∈ I, orderOf c = 5 ∧ ∃ U : Subgroup G, U ≤ I ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      c ∈ Subgroup.normalizer (U : Set G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨T⟩ :
      Nonempty (Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))) :=
    inferInstance
  obtain ⟨b, hbN, hb15, -, -, eT, μ, hμ, hrel⟩ :=
    CFSG.Quasithin.H13.exists_singer_coordinates_psl216 T
  have hiter : ∀ m : ℕ, ∀ x : GaloisField 2 4,
      ((eT (Multiplicative.ofAdd ((μ : GaloisField 2 4) ^ m * x)) :
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))) =
        b ^ m * (eT (Multiplicative.ofAdd x) : _) * (b ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', mul_assoc, hrel, ih, pow_succ']
      group
  have hb3 : b ^ 3 ≠ 1 := by
    intro h3
    have h := hiter 3 1
    simp only [h3, one_mul, inv_one, mul_one] at h
    have h' := eT.injective (Subtype.ext h)
    have h'' : (μ : GaloisField 2 4) ^ 3 = 1 := by
      have := congrArg Multiplicative.toAdd h'
      simpa using this
    have hμ3 : μ ^ 3 = 1 := Units.ext (by simpa using h'')
    have hdvd := orderOf_dvd_of_pow_eq_one hμ3
    rw [hμ] at hdvd
    norm_num at hdvd
  have hc5 : orderOf (b ^ 3) = 5 :=
    orderOf_eq_prime (by rw [← pow_mul]; exact hb15) hb3
  let ι : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4) →* G :=
    I.subtype.comp eI.symm.toMonoidHom
  have hι : Function.Injective ι := I.subtype_injective.comp eI.symm.injective
  have hιI : ∀ w, ι w ∈ I := fun w => (eI.symm w).2
  refine ⟨ι (b ^ 3), hιI _, by rw [orderOf_injective ι hι, hc5], (T : Subgroup _).map ι, ?_, ?_,
    T.isPGroup'.map ι, Subgroup.le_normalizer_map ι ⟨b ^ 3, Subgroup.pow_mem _ hbN 3, rfl⟩⟩
  · rintro _ ⟨w, -, rfl⟩
    exact hιI w
  · intro hU
    have hmem : ι (eT (Multiplicative.ofAdd 1)) ∈ (T : Subgroup _).map ι := ⟨_, (eT _).2, rfl⟩
    rw [hU, Subgroup.mem_bot] at hmem
    have h2 := hι (hmem.trans (map_one ι).symm)
    have h3 : eT (Multiplicative.ofAdd (1 : GaloisField 2 4)) = 1 := Subtype.ext h2
    have h4 := eT.injective (h3.trans (map_one eT).symm)
    exact one_ne_zero (Multiplicative.ofAdd.injective (h4.trans ofAdd_zero.symm))

theorem ggN2_le_normalizer_of_orbit {X I E : Subgroup G} (hI : CFSG.Open.IsComponentOf I X)
    (eI : ↥I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))
    (hE : IsPGroup 5 E) (hEX : E ≤ Subgroup.normalizer (X : Set G))
    (hrank : LargeEvenTwoLocalRank 5 G ≤ 4) :
    E ≤ Subgroup.normalizer (I : Set G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro δ hδ
  by_contra hδI
  let Ik : ℕ → Subgroup G := fun k => I.map (MulAut.conj (δ ^ k)).toMonoidHom
  have hmemIk : ∀ k g, g ∈ Ik k ↔ (δ ^ k)⁻¹ * g * δ ^ k ∈ I := by
    intro k g
    simp only [Ik, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have hI0 : Ik 0 = I := by
    ext g
    rw [hmemIk]
    simp
  have hcomp : ∀ k, CFSG.Open.IsComponentOf (Ik k) X := by
    intro k
    have hXk : X.map (MulAut.conj (δ ^ k)).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEX (E.pow_mem hδ k))
    have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
      (CFSG.Assembly.isComponentOf_iff_open.mpr hI) (MulAut.conj (δ ^ k)).toMonoidHom
      (MulAut.conj (δ ^ k)).injective
    rw [hXk] at h
    exact CFSG.Assembly.isComponentOf_iff_open.mp h
  obtain ⟨n, hn⟩ := hE ⟨δ, hδ⟩
  have hδn : δ ^ 5 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : ∀ m, 0 < m → m < 5 → Nat.Coprime m (orderOf δ) := by
    intro m hm0 hm5
    have h5 : Nat.Coprime m 5 := by interval_cases m <;> decide
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hδn) (h5.pow_right n)
  have hpowN : ∀ m, 0 < m → m < 5 → δ ^ m ∉ Subgroup.normalizer (I : Set G) := by
    intro m hm0 hm5 hmem
    obtain ⟨l, hl⟩ := exists_pow_eq_self_of_coprime (hcop m hm0 hm5)
    apply hδI
    rw [← hl]
    exact Subgroup.pow_mem _ hmem l
  have hne : ∀ i j, i < j → j < 5 → Ik i ≠ Ik j := by
    intro i j hij hj heq
    apply hpowN (j - i) (by omega) (by omega)
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    have hiff := (hmemIk i (δ ^ i * h * (δ ^ i)⁻¹)).symm.trans
      ((SetLike.ext_iff.mp heq _).trans (hmemIk j _))
    have e1 : (δ ^ i)⁻¹ * (δ ^ i * h * (δ ^ i)⁻¹) * δ ^ i = h := by group
    have e2 : (δ ^ j)⁻¹ * (δ ^ i * h * (δ ^ i)⁻¹) * δ ^ j =
        (δ ^ (j - i))⁻¹ * h * δ ^ (j - i) := by
      obtain ⟨m, rfl⟩ : ∃ m, j = i + m := ⟨j - i, by omega⟩
      rw [show i + m - i = m by omega, pow_add]
      group
    rw [e1, e2] at hiff
    exact hiff
  have hcommIk : ∀ i j, i < 5 → j < 5 → i ≠ j → ∀ a ∈ Ik i, ∀ b ∈ Ik j, a * b = b * a := by
    intro i j hi hj hij a ha b hb
    have hne' : Ik i ≠ Ik j := by
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · exact hne i j h hj
      · exact fun e => hne j i h hi e.symm
    exact CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne (hcomp i) (hcomp j) hne' ha hb
  have hZI := ggN2_eq_one_of_commute_psl216 eI
  have hZIk : ∀ k, ∀ y ∈ Ik k, (∀ z ∈ Ik k, y * z = z * y) → y = 1 := by
    intro k y hy hc
    have hy' := (hmemIk k y).mp hy
    have h1 : (δ ^ k)⁻¹ * y * δ ^ k = 1 := hZI _ hy' (fun z hz => by
      have hz' : δ ^ k * z * (δ ^ k)⁻¹ ∈ Ik k := (hmemIk k _).mpr (by
        rw [show (δ ^ k)⁻¹ * (δ ^ k * z * (δ ^ k)⁻¹) * δ ^ k = z by group]
        exact hz)
      have h := hc _ hz'
      calc (δ ^ k)⁻¹ * y * δ ^ k * z = (δ ^ k)⁻¹ * (y * (δ ^ k * z * (δ ^ k)⁻¹)) * δ ^ k := by
            group
        _ = (δ ^ k)⁻¹ * ((δ ^ k * z * (δ ^ k)⁻¹) * y) * δ ^ k := by rw [h]
        _ = z * ((δ ^ k)⁻¹ * y * δ ^ k) := by group)
    calc y = δ ^ k * ((δ ^ k)⁻¹ * y * δ ^ k) * (δ ^ k)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨c, hcI, hco, U, hUI, hU1, hU2, hcU⟩ := ggN2_exists_five_normalizer_psl216 eI
  let ck : ℕ → G := fun k => δ ^ k * c * (δ ^ k)⁻¹
  have hckIk : ∀ k, ck k ∈ Ik k := fun k => (hmemIk k _).mpr (by
    rw [show (δ ^ k)⁻¹ * (δ ^ k * c * (δ ^ k)⁻¹) * δ ^ k = c by group]
    exact hcI)
  have hck5 : ∀ k, ck k ^ 5 = 1 := by
    intro k
    simp only [ck]
    rw [conj_pow, ← hco, pow_orderOf_eq_one]
    group
  have hck1 : ∀ k, ck k ≠ 1 := by
    intro k h
    have hc1 : c = 1 := by
      calc c = (δ ^ k)⁻¹ * ck k * δ ^ k := by simp only [ck]; group
        _ = 1 := by rw [h]; group
    rw [hc1, orderOf_one] at hco
    norm_num at hco
  let A : ℕ → Subgroup G := fun m => ⨆ k ∈ Finset.range m, Subgroup.zpowers (ck k)
  have hAsucc : ∀ m, A (m + 1) = Subgroup.zpowers (ck m) ⊔ A m := by
    intro m
    simp only [A]
    rw [Finset.range_add_one, Finset.iSup_insert]
  have hAcent : ∀ m l, m ≤ l → l < 5 → A m ≤ Subgroup.centralizer (Ik l : Set G) := by
    intro m l hml hl
    refine iSup₂_le fun k hk => Subgroup.zpowers_le.mpr ?_
    rw [Finset.mem_range] at hk
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hcommIk l k hl (by omega) (by omega) z hz (ck k) (hckIk k)
  have hAel : ∀ m, m ≤ 5 → CFSG.Open.IsElemAbelian 5 (A m) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hA0 : A 0 = ⊥ := by simp [A]
      rw [hA0, ← Subgroup.zpowers_one_eq_bot]
      exact CFSG.Open.isElemAbelian_zpowers (one_pow 5)
    | succ m ih =>
      intro hm
      rw [hAsucc]
      refine CFSG.Open.IsElemAbelian.sup_of_commute
        (CFSG.Open.isElemAbelian_zpowers (hck5 m)) (ih (by omega)) ?_
      intro a ha b' hb'
      have ha' : a ∈ Ik m := (Subgroup.zpowers_le.mpr (hckIk m)) ha
      exact Subgroup.mem_centralizer_iff.mp (hAcent m m le_rfl (by omega) hb') a ha'
  have hAcard : ∀ m, m ≤ 5 → 5 ^ m ≤ Nat.card (A m) := by
    intro m
    induction m with
    | zero => intro _; rw [pow_zero]; exact Nat.card_pos
    | succ m ih =>
      intro hm
      rw [hAsucc]
      have hdisj : Disjoint (Subgroup.zpowers (ck m)) (A m) := by
        rw [Subgroup.disjoint_def]
        intro g hg hgA
        have hgI : g ∈ Ik m := (Subgroup.zpowers_le.mpr (hckIk m)) hg
        exact hZIk m g hgI (fun z hz =>
          (Subgroup.mem_centralizer_iff.mp (hAcent m m le_rfl (by omega) hgA) z hz).symm)
      have hcard := CFSG.GroupTheory.card_mul_card_le_card_sup_of_disjoint hdisj
      have hz5 : Nat.card (Subgroup.zpowers (ck m)) = 5 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hck5 m) (hck1 m)
      rw [hz5] at hcard
      calc 5 ^ (m + 1) = 5 * 5 ^ m := by ring
        _ ≤ 5 * Nat.card (A m) := Nat.mul_le_mul_left 5 (ih (by omega))
        _ ≤ _ := hcard
  have hAU : A 5 ≤ Subgroup.normalizer (U : Set G) := by
    refine iSup₂_le fun k hk => Subgroup.zpowers_le.mpr ?_
    rw [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simpa [ck] using hcU
    · have hcent : ck k ∈ Subgroup.centralizer (U : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have huI : u ∈ Ik 0 := by rw [hI0]; exact hUI hu
        exact hcommIk 0 k (by norm_num) hk (by omega) u huI (ck k) (hckIk k)
      exact Subgroup.centralizer_le_normalizer _ hcent
  have hAP : IsPGroup 5 (A 5) := fun g => ⟨1, Subtype.ext (by simpa using (hAel 5 le_rfl).2 g g.2)⟩
  obtain ⟨r, hr⟩ := hAP.exists_card_eq
  have hrle := le_twoLocalRank_of_normalizes Nat.prime_five hU1 hU2 (hAel 5 le_rfl) hAU hr
  have h55 := hAcard 5 le_rfl
  rw [hr] at h55
  have : 5 ^ 5 ≤ 5 ^ 4 := h55.trans (Nat.pow_le_pow_right (by norm_num) (hrle.trans hrank))
  norm_num at this

theorem ggN2_exists_weylInvolution {Bs I : Subgroup G}
    (eI : ↥I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4))
    (hBs : CFSG.Open.IsElemAbelian 5 Bs)
    (hBmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 5 = 1 → g ∈ Bs)
    (hBsI : Bs ≤ Subgroup.normalizer (I : Set G)) :
    ∃ p ∈ Bs ⊓ I, p ≠ 1 ∧ ∃ t ∈ I, t * t = 1 ∧ t * p * t⁻¹ = p⁻¹ ∧
      t ∈ Subgroup.normalizer (Bs : Set G) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hZ := ggN2_eq_one_of_commute_psl216 eI
  let α : ↥Bs →* MulAut ↥I := I.normalizerMonoidHom.comp (Subgroup.inclusion hBsI)
  have hα : ∀ (b : Bs) (x : I), ((α b x : I) : G) = (b : G) * x * (b : G)⁻¹ := fun b x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe I _ x
  have hinner : ∀ b : Bs, ∃ i : I, MulAut.conj i = α b := by
    intro b
    have h5 : (α b) ^ 5 = 1 := by
      rw [← map_pow, show b ^ 5 = 1 from Subtype.ext (hBs.2 b b.2), map_one]
    have hodd : Odd (orderOf (α b)) := by
      rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one h5) with h | h <;>
        rw [h] <;> decide
    exact CFSG.ComponentClassification.Foote47L216.psl216_equiv_all_odd_aut_inner eI (α b) hodd
  choose ι hι using hinner
  have hιact : ∀ (b : Bs) (x : I),
      (ι b : G) * x * (ι b : G)⁻¹ = (b : G) * x * (b : G)⁻¹ := by
    intro b x
    rw [← hα, ← hι b]
    rfl
  have hcentral : ∀ y : I, (∀ z : I, y * z = z * y) → y = 1 := fun y hy =>
    Subtype.ext (hZ y y.2 fun z hz => congrArg Subtype.val (hy ⟨z, hz⟩))
  have hιcomm : ∀ b b' : Bs, ι b * ι b' = ι b' * ι b := by
    intro b b'
    have hc : MulAut.conj (ι b * ι b' * (ι b)⁻¹ * (ι b')⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hι, hι, ← map_inv, ← map_inv, ← map_mul,
        ← map_mul, ← map_mul]
      rw [show b * b' * b⁻¹ * b'⁻¹ = 1 from
        Subtype.ext (by
          have := hBs.1.is_comm.comm b b'
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one]
          rw [show (b : G) * b' = b' * b from congrArg Subtype.val this]
          group), map_one]
    have h1 : ι b * ι b' * (ι b)⁻¹ * (ι b')⁻¹ = 1 := hcentral _ fun z => by
      have hz := congrArg (fun φ : MulAut I => φ z) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at hz
      calc _ * z = (ι b * ι b' * (ι b)⁻¹ * (ι b')⁻¹) * z *
            (ι b * ι b' * (ι b)⁻¹ * (ι b')⁻¹)⁻¹ * (ι b * ι b' * (ι b)⁻¹ * (ι b')⁻¹) := by group
        _ = z * _ := by rw [hz]
    calc ι b * ι b' = ι b * ι b' * (ι b)⁻¹ * (ι b')⁻¹ * (ι b' * ι b) := by group
      _ = ι b' * ι b := by rw [h1, one_mul]
  have hι5 : ∀ b : Bs, (ι b) ^ 5 = 1 := by
    intro b
    refine hcentral _ fun z => ?_
    have hz := congrArg (fun φ : MulAut I => φ z)
      (show MulAut.conj ((ι b) ^ 5) = 1 by
        rw [map_pow, hι, ← map_pow, show b ^ 5 = 1 from Subtype.ext (hBs.2 b b.2), map_one])
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    calc (ι b) ^ 5 * z = ((ι b) ^ 5 * z * ((ι b) ^ 5)⁻¹) * (ι b) ^ 5 := by group
      _ = z * (ι b) ^ 5 := by rw [hz]
  have hιBs : ∀ b : Bs, (ι b : G) ∈ Bs := by
    intro b
    refine hBmax _ ?_ (by simpa using congrArg Subtype.val (hι5 b))
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have h := hιact ⟨b', hb'⟩ (ι b)
    rw [show (ι ⟨b', hb'⟩ : G) * (ι b : G) * (ι ⟨b', hb'⟩ : G)⁻¹ = ι b by
      rw [← Subgroup.coe_mul, hιcomm, Subgroup.coe_mul, mul_inv_cancel_right]] at h
    calc b' * (ι b : G) = b' * (ι b : G) * b'⁻¹ * b' := by group
      _ = (ι b : G) * b' := by rw [← h]
  obtain ⟨c, hcI, hco, -⟩ := ggN2_exists_five_normalizer_psl216 eI
  have hnt : ∃ b : Bs, ι b ≠ 1 := by
    by_contra hall
    push Not at hall
    have hcC : c ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h := hιact ⟨b, hb⟩ ⟨c, hcI⟩
      rw [hall ⟨b, hb⟩] at h
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
      calc b * c = b * c * b⁻¹ * b := by group
        _ = c * b := by rw [← h]
    have hcBs := hBmax c hcC (by rw [← hco]; exact pow_orderOf_eq_one c)
    have hc1 := hZ c hcI fun z hz => by
      have h := hιact ⟨c, hcBs⟩ ⟨z, hz⟩
      rw [hall ⟨c, hcBs⟩] at h
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h
      calc c * z = c * z * c⁻¹ * c := by group
        _ = z * c := by rw [← h]
    rw [hc1, orderOf_one] at hco
    norm_num at hco
  obtain ⟨b₀, hb₀⟩ := hnt
  set p : G := (ι b₀ : G) with hp
  have hp1 : p ≠ 1 := fun h => hb₀ (Subtype.ext h)
  have hpBI : p ∈ Bs ⊓ I := ⟨hιBs b₀, (ι b₀).2⟩
  have hpo : orderOf p = 5 :=
    orderOf_eq_prime (by simpa [hp] using congrArg Subtype.val (hι5 b₀)) hp1
  have hBI : Bs ⊓ I = Subgroup.zpowers p := by
    have hP : IsPGroup 5 (Bs ⊓ I : Subgroup G) := fun g =>
      ⟨1, Subtype.ext (by simpa using hBs.2 g g.2.1)⟩
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : Nat.card (Bs ⊓ I : Subgroup G) ∣ 4080 := by
      rw [← CFSG.Quasithin.H13.ob5_card_PSL, ← Nat.card_congr eI.toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hle : Subgroup.zpowers p ≤ Bs ⊓ I := Subgroup.zpowers_le.mpr hpBI
    have h5 : 5 ∣ Nat.card (Bs ⊓ I : Subgroup G) := by
      rw [← hpo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hle
    have hk1 : k = 1 := by
      rw [hk] at hdvd h5
      rcases k with _ | _ | k
      · norm_num at h5
      · rfl
      · exfalso
        have : 5 ^ 2 ∣ 4080 := (pow_dvd_pow 5 (by omega : 2 ≤ k + 2)).trans hdvd
        norm_num at this
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hk, hk1, Nat.card_zpowers, hpo, pow_one]
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (eI ⟨p, (ι b₀).2⟩)
  obtain ⟨a, ha2, hax⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv x
  set t : G := (eI.symm (QuotientGroup.mk a) : G) with ht
  have htI : t ∈ I := (eI.symm _).2
  have htt : t * t = 1 := by
    rw [ht, ← Subgroup.coe_mul, ← map_mul, ← QuotientGroup.mk_mul, ha2, QuotientGroup.mk_one,
      map_one, Subgroup.coe_one]
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one]
    exact htt
  have htp : t * p * t⁻¹ = p⁻¹ := by
    rw [htinv]
    have hpe : p = (eI.symm (QuotientGroup.mk x) : G) := by
      rw [hx, MulEquiv.symm_apply_apply]
    rw [hpe, ht, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hax, QuotientGroup.mk_inv, map_inv,
      Subgroup.coe_inv]
  have htBs : ∀ b ∈ Bs, t * b * t⁻¹ ∈ Bs := by
    intro b hb
    have hιb : (ι ⟨b, hb⟩ : G) ∈ Subgroup.zpowers p := by
      rw [← hBI]
      exact ⟨hιBs _, (ι ⟨b, hb⟩).2⟩
    have hcomm : t * ((ι ⟨b, hb⟩ : G)⁻¹ * b) = ((ι ⟨b, hb⟩ : G)⁻¹ * b) * t := by
      have h := hιact ⟨b, hb⟩ ⟨t, htI⟩
      calc t * ((ι ⟨b, hb⟩ : G)⁻¹ * b) = (ι ⟨b, hb⟩ : G)⁻¹ * ((ι ⟨b, hb⟩ : G) * t *
            (ι ⟨b, hb⟩ : G)⁻¹) * b := by group
        _ = (ι ⟨b, hb⟩ : G)⁻¹ * (b * t * b⁻¹) * b := by rw [h]
        _ = ((ι ⟨b, hb⟩ : G)⁻¹ * b) * t := by group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hιb
    have htι : t * (ι ⟨b, hb⟩ : G) * t⁻¹ = (ι ⟨b, hb⟩ : G)⁻¹ := by
      rw [← hk, ← conj_zpow, htp, inv_zpow]
    have heq : t * b * t⁻¹ = (ι ⟨b, hb⟩ : G)⁻¹ * ((ι ⟨b, hb⟩ : G)⁻¹ * b) := by
      calc t * b * t⁻¹ = (t * (ι ⟨b, hb⟩ : G) * t⁻¹) * (t * ((ι ⟨b, hb⟩ : G)⁻¹ * b) * t⁻¹) := by
            group
        _ = (ι ⟨b, hb⟩ : G)⁻¹ * ((ι ⟨b, hb⟩ : G)⁻¹ * b) := by
            rw [htι, hcomm, mul_inv_cancel_right]
    rw [heq]
    exact Bs.mul_mem (Bs.inv_mem (hιBs _)) (Bs.mul_mem (Bs.inv_mem (hιBs _)) hb)
  refine ⟨p, hpBI, hp1, t, htI, htt, htp, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨htBs h, fun hh => ?_⟩
  have := htBs _ hh
  rwa [htinv, show t * (t * h * t) * t = h by
    rw [show t * (t * h * t) * t = (t * t) * h * (t * t) by group, htt, one_mul, mul_one]] at this

theorem ggN2_false_of_sStar_psl216 {B D J M L : Subgroup G} {x : G}
    (hS : LargeEvenSStar 5 B x L) (hBel : CFSG.Open.IsElemAbelian 5 B)
    (hBmax : ∀ g ∈ Subgroup.centralizer (B : Set G), g ^ 5 = 1 → g ∈ B)
    (hBsplit : B = D ⊔ (B ⊓ J)) (hDB : D ≤ B) (hxD : x ∈ D)
    (hDJ : D ≤ Subgroup.centralizer (J : Set G)) (hJL : J ≤ L) (hMJ : M ≤ J)
    (hMna : ∃ a ∈ M, ∃ b ∈ M, a * b ≠ b * a) (hrank : LargeEvenTwoLocalRank 5 G ≤ 4)
    (hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L))
    (hsolv : Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (M : Set G)))
    {I : Subgroup G} (hI : CFSG.Open.IsComponentOf I
      (LargeEvenPLayer 5 (Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer {x})))
    (eI : ↥I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set X := Subgroup.centralizer (M : Set G) ⊓ Subgroup.centralizer {x} with hXdef
  have hlayer : LargeEvenPLayer 5 X ≤ X := by
    rw [largeEvenPLayer_eq_lBalancePLayer]
    exact lBalancePLayer_le 5 X
  have hIX : I ≤ X := hI.1.trans hlayer
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : CFSG.Open.IsComponentOf L (Subgroup.centralizer {x}) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hS.2.2.2.1
  have hML : M ≤ L := hMJ.trans hJL
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := fun g hg =>
    ggN2_mem_normalizer_of_commonComponent hLx hML hMna (hIX hg).1 (hIX hg).2
  have hIperf : Group.IsPerfect ↥I := ⟨hI.2.2.1⟩
  have hIsup : I ≤ L ⊔ Subgroup.centralizer (L : Set G) :=
    CFSG.RankThree.PartOne.K159.le_sup_centralizer_of_outer_solvable hIperf hIL hOut
  have hCLM : Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer (M : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hML)
  have hIsup' : I ≤ (L ⊓ Subgroup.centralizer (M : Set G)) ⊔
      Subgroup.centralizer (L : Set G) := by
    intro i hi
    have hi' : i ∈ ((L ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := hIsup hi
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L _
      (Subgroup.centralizer_le_normalizer _)] at hi'
    obtain ⟨l, hl, c, hc, rfl⟩ := hi'
    have hlM : l ∈ Subgroup.centralizer (M : Set G) := by
      have h1 : l * c * c⁻¹ ∈ Subgroup.centralizer (M : Set G) :=
        mul_mem (hIX hi).1 (inv_mem (hCLM hc))
      simpa only [mul_inv_cancel_right] using h1
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hl, hlM⟩))
      (Subgroup.mem_sup_right hc)
  have hSN : L ⊓ Subgroup.centralizer (M : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    inf_le_left.trans (Subgroup.le_normalizer.trans
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L))
  have hICL : I ≤ Subgroup.centralizer (L : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.perfect_le_of_le_sup_of_isSolvable hIperf hsolv hSN
      hIsup'
  have hDX : D ≤ X := by
    intro e he
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_iff.mp (hDJ he) m (hMJ hm)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hBel.1.is_comm.comm (⟨e, hDB he⟩ : B) ⟨x, hDB hxD⟩)
  have hDN : D ≤ Subgroup.normalizer (LargeEvenPLayer 5 X : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨conj_mem_largeEvenPLayer (hDX he), fun ha => ?_⟩
    have := conj_mem_largeEvenPLayer (hDX (D.inv_mem he)) ha
    rwa [inv_inv, show e⁻¹ * (e * a * e⁻¹) * e = a by group] at this
  have hDp : IsPGroup 5 D := fun g =>
    ⟨1, Subtype.ext (by simpa using hBel.2 g (hDB g.2))⟩
  have hDI : D ≤ Subgroup.normalizer (I : Set G) :=
    ggN2_le_normalizer_of_orbit hI eI hDp hDN hrank
  have hBI : B ≤ Subgroup.normalizer (I : Set G) := by
    rw [hBsplit]
    refine sup_le hDI fun j hj => Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact (Subgroup.mem_centralizer_iff.mp (hICL hi) j (hJL hj.2)).symm
  obtain ⟨p, hpBI, hp1, -⟩ := ggN2_exists_weylInvolution eI hBel hBmax hBI
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx.1 hl)
  set H := B ⊓ Subgroup.centralizer (L : Set G) with hHdef
  have hHp : IsPGroup 5 H := fun g =>
    ⟨1, Subtype.ext (by simpa using hBel.2 g (Subgroup.mem_inf.mp g.2).1)⟩
  have hHcyc : IsCyclic ↥H := hS.2.2.2.2 H inf_le_right hHp
  have hxH : x ∈ H := Subgroup.mem_inf.mpr ⟨hDB hxD, hxL⟩
  have hpH : p ∈ H := Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hpBI).1,
    hICL (Subgroup.mem_inf.mp hpBI).2⟩
  have hp5 : orderOf p = 5 := orderOf_eq_prime (hBel.2 p (Subgroup.mem_inf.mp hpBI).1) hp1
  have hcardH : Nat.card ↥H ∣ 5 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one fun h =>
      Subtype.ext (by simpa using hBel.2 h (Subgroup.mem_inf.mp h.2).1)
  have hpHeq : Subgroup.zpowers p = H := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hpH)
    rw [Nat.card_zpowers, hp5]
    exact Nat.le_of_dvd (by norm_num) hcardH
  have hxp : x ∈ Subgroup.zpowers p := by
    rw [hpHeq]
    exact hxH
  have hxI : x ∈ I := (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hpBI).2) hxp
  exact hx1 (ggN2_eq_one_of_commute_psl216 eI x hxI fun z hz =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hIX hz).2).symm)

section LiteralM

open CFSG.ClassicalInvolution.WeakCT

private theorem ggN2_exists_mul_ne_mul_SL_two (F : Type) [Field F] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩,
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩, fun h => ?_⟩
  have h00 : ((!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F)) 0 0 =
      ((!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)) 0 0 :=
    congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

omit [Finite G] in
theorem ggN2_literalM_chart (ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G)
    (hψ : ψ.ker ≤ Subgroup.center _) {J : Subgroup G}
    (hJ : (ψ.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J) :
    (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ ≤ J ∧
      (∃ a ∈ (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ,
        ∃ b ∈ (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ, a * b ≠ b * a) ∧
      ∃ eJ : ↥J ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 2),
        ∀ m ∈ CFSG.RankThree.CALinearPlane.coordBlockSL (GaloisField 2 2)
          ({3}ᶜ : Finset (Fin 4)),
          (eJ.symm m : G) ∈ (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ := by
  classical
  subst hJ
  have hcomp : ∀ A : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2),
      blockSL (GaloisField 2 2) 6 4 0 (by norm_num) (blockSL (GaloisField 2 2) 4 3 0
        (by norm_num) A) = blockSL (GaloisField 2 2) 6 3 0 (by norm_num) A :=
    fun A => blockSL_comp_apply (by norm_num) (by norm_num) A
  have hcomp2 : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2),
      blockSL (GaloisField 2 2) 6 3 0 (by norm_num) (blockSL (GaloisField 2 2) 3 2 0
        (by norm_num) A) = blockSL (GaloisField 2 2) 6 2 0 (by norm_num) A :=
    fun A => blockSL_comp_apply (by norm_num) (by norm_num) A
  have hMJ : (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ ≤
      (ψ.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range := by
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    exact ⟨blockSL (GaloisField 2 2) 4 3 0 (by norm_num) A, by
      rw [MonoidHom.comp_apply, hcomp]⟩
  have hinj2 : Function.Injective (ψ.comp (blockSL (GaloisField 2 2) 6 2 0 (by norm_num))) :=
    comp_blockSL_injective hψ (by norm_num) (by norm_num)
  have hmem2 : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2),
      ψ (blockSL (GaloisField 2 2) 6 2 0 (by norm_num) A) ∈
        (blockSL (GaloisField 2 2) 6 3 0 (by norm_num)).range.map ψ := fun A =>
    ⟨blockSL (GaloisField 2 2) 6 3 0 (by norm_num) (blockSL (GaloisField 2 2) 3 2 0
      (by norm_num) A), ⟨_, rfl⟩, by rw [hcomp2]⟩
  obtain ⟨a, b, hab⟩ := ggN2_exists_mul_ne_mul_SL_two (GaloisField 2 2)
  refine ⟨hMJ, ⟨_, hmem2 a, _, hmem2 b, fun h => hab (hinj2 ?_)⟩, ?_⟩
  · simpa only [MonoidHom.comp_apply, map_mul] using h
  have hinj4 : Function.Injective (ψ.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))) :=
    comp_blockSL_injective hψ (by norm_num) (by norm_num)
  refine ⟨(MonoidHom.ofInjective hinj4).symm, fun m hm => ?_⟩
  have hm' : m ∈ (blockSL (GaloisField 2 2) 4 3 0 (by norm_num)).range := by
    rw [CFSG.SeitzReduction.LinearPilot.range_blockSL_eq,
      CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    rw [CFSG.RankThree.CALinearPlane.mem_coordBlockSL_iff] at hm
    have hcb : CFSG.SeitzReduction.LinearPilot.consecutiveBlock 4 0 3 =
        ({3}ᶜ : Finset (Fin 4)) := by decide
    rw [hcb]
    intro i j hij
    rw [hm i j hij, Matrix.one_apply]
  obtain ⟨A, rfl⟩ := hm'
  rw [MulEquiv.symm_symm, MonoidHom.ofInjective_apply, MonoidHom.comp_apply, hcomp]
  exact ⟨_, ⟨A, rfl⟩, rfl⟩

end LiteralM

section BadLine

theorem ggN2_noPSL216_x {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K)
    (hL : GGCentralImage .POmegaMinus 4 2 L) (hK : GGCentralImage .PSL 6 2 K)
    {ψ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (hψ : ψ.ker ≤ Subgroup.center _)
    (hJψ : (ψ.comp (CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 2) 6 4 0
      (by norm_num))).range = J)
    (I : Subgroup G) (hI : CFSG.Open.IsComponentOf I (LargeEvenPLayer 5
      (Subgroup.centralizer (((CFSG.ClassicalInvolution.WeakCT.blockSL (GaloisField 2 2) 6 3 0
        (by norm_num)).range.map ψ : Subgroup G) : Set G) ⊓ Subgroup.centralizer {x}))) :
    IsEmpty (↥I ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
  classical
  obtain ⟨hMJ, hMna, -, -⟩ := ggN2_literalM_chart ψ hψ hJψ
  obtain ⟨hsolv, -⟩ := ggF4N2_goodLines_isSolvable hR hL ψ hψ hJψ
  have hBs : B = Bs := ggF4N2_B_eq_Bs hR hL
  have hpre : LargeEvenStdSubPre 5 B x L D J := hR.1.2.2.1
  have hS : LargeEvenSStar 5 Bs x L := by
    have h := hR.1.1.2.2.2.2.2.2.1
    rwa [hBs] at h
  have hBel : CFSG.Open.IsElemAbelian 5 Bs := hR.1.2.1.2.1
  have hBmax : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 5 = 1 → g ∈ Bs := hR.1.2.1.2.2.2
  have hsplit : Bs = D ⊔ (Bs ⊓ J) := (ggF4N2J_original_torus_split hR hNbr hL hK).1
  have hDBs : D ≤ Bs := by simpa only [hBs] using hpre.1
  have hDcent : D = Bs ⊓ Subgroup.centralizer (J : Set G) := by
    simpa only [hBs] using hpre.2.2.2.2.2.2
  have hDJ : D ≤ Subgroup.centralizer (J : Set G) := by
    rw [hDcent]
    exact inf_le_right
  have hxD : x ∈ D := hpre.2.2.2.1
  have hJL : J ≤ L := hR.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hrank : LargeEvenTwoLocalRank 5 G ≤ 4 := (ggF4N2Rank hR hL).2.2.le
  have hOut := ggF4N2OmegaK_outer_solvable hL
  exact ⟨fun eI => ggN2_false_of_sStar_psl216 hS hBel hBmax hsplit hDBs hxD hDJ hJL hMJ hMna hrank
    hOut hsolv hI eI⟩

end BadLine

section MixedConsumer

open CFSG.RankThree.PartOne CFSG.ClassicalInvolution.WeakCT

theorem ggF4N2_mixed_hM {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K)
    (hF4 : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hinv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hxg : g * x * g⁻¹ = x)
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 6) (GaloisField 2 2) →* G}
    (h₁ : ψ₁.ker ≤ Subgroup.center _) (hK₁ : ψ₁.range = K)
    (hJ₁ : (ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))).range = J)
    (h₂ : ψ₂.ker ≤ Subgroup.center _) (hK₂ : ψ₂.range = K.map (MulAut.conj g).toMonoidHom)
    (hblock : ψ₂.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num)) =
      ψ₁.comp (blockSL (GaloisField 2 2) 6 4 0 (by norm_num))) :
    ∀ a ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₁,
      ∀ b ∈ (blockSL (GaloisField 2 2) 6 3 3 (by norm_num)).range.map ψ₂, a * b = b * a := by
  obtain ⟨-, -, -, -, -, -, hxline, -⟩ := ggF4N2_mixed_lines hR hNbr hL hK hF4 hgL hgN hinv hxg
  refine ggF4N2_mixed_hM_of_goodLine hR hNbr hL hK hF4 hgL hgN hinv hxg h₁ hK₁ hJ₁ h₂ hK₂ hblock
    fun I hI => ?_
  rw [← centralizer_singleton_eq_of_zpowers_eq hxline] at hI
  exact ggN2_noPSL216_x hR hNbr hL hK h₁ hJ₁ I hI

end MixedConsumer

end CFSG.StandardType

end
