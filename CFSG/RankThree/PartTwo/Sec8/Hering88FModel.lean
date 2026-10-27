module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FCore
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
import CFSG.RankThree.PartTwo.Sec8.HeringD4KF83
import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreClosed
public import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairModels

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem conj_mul_mul_conj_inv_of_fixed {M : Type*} [Group M] (φ : MulAut M) {g : M}
    (hg : φ g = g) : MulAut.conj g * φ * (MulAut.conj g)⁻¹ = φ := by
  have h := KFacts.mul_mulAutConj_mul_inv φ g
  rw [hg, mul_inv_eq_iff_eq_mul] at h
  rw [← h]
  group

theorem three_dvd_two_pow_add_one {m : ℕ} (hodd : Odd m) : 3 ∣ 2 ^ m + 1 := by
  obtain ⟨j, rfl⟩ := hodd
  rw [pow_succ, pow_mul]
  have h4 : (2 ^ 2) ^ j % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

section Generic

theorem classBDichotomy_of_model {G : Type} [Group G] [Finite G] {Y : Subgroup G} {c d : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hcd : c * d = d * c) (hd3 : d ^ 3 = 1)
    (hdin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hdne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) {m : ℕ}
    {M : Type} [Group M] [Finite M] (hZ : Subgroup.center M = ⊥)
    {H : Type} [Group H] [Finite H] (ι : H →* M) (hι : Function.Injective ι)
    (E : Y ⧸ aschbacherSolvableCore 3 Y ≃* M) (φ : MulAut M)
    (hφ : KFacts.inducedAutHom Y E ⟨c, hcN⟩ = φ) (hrange : ∀ z, z ∈ ι.range ↔ φ z = z)
    (P_S P_L : H → Prop)
    (hcls : ∀ w₀ : H, w₀ ^ 3 = 1 → w₀ ≠ 1 →
      ∃ c₀ : H, P_S (c₀ * w₀ * c₀⁻¹) ∨ P_L (c₀ * w₀ * c₀⁻¹))
    (hL : ∀ y : H, P_L y → y ^ 3 = 1 → y ≠ 1 →
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({ι y} : Set M)) ≃*
        projSL 2 (GaloisField 2 (3 * m))))
    (hS : ∀ y : H, P_S y → y ^ 3 = 1 → y ≠ 1 → IsQuasisimple (Subgroup.centralizer ({y} : Set H))) :
    ClassBDichotomy Y c d m := by
  classical
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  have hdin₁ : KFacts.IsInnerAut (KFacts.inducedAutHom Y E ⟨d, hdN⟩) := by
    rw [KFacts.inducedAutHom_apply, KFacts.isInnerAut_congr]
    exact hdin
  obtain ⟨w, hw, hw3, hw1, -⟩ := Item8KFacts3.exists_conj_residual E hZ hdN hd3 hdin₁ hdne
  have hcomm : KFacts.inducedAutHom Y E ⟨c, hcN⟩ * KFacts.inducedAutHom Y E ⟨d, hdN⟩ =
      KFacts.inducedAutHom Y E ⟨d, hdN⟩ * KFacts.inducedAutHom Y E ⟨c, hcN⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hcd)
  have hfix : φ w = w := by
    rw [hφ, ← hw] at hcomm
    have h1 := KFacts.mul_mulAutConj_mul_inv φ w
    rw [hcomm, mul_inv_cancel_right] at h1
    exact (hinj h1).symm
  obtain ⟨w₀, hw₀⟩ := (hrange w).mpr hfix
  have hw₀3 : w₀ ^ 3 = 1 := by
    apply hι
    rw [map_pow, hw₀, hw3, map_one]
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    apply hw1
    rw [← hw₀, map_one]
  obtain ⟨c₀, hc₀⟩ := hcls w₀ hw₀3 hw₀1
  set y₀ : H := c₀ * w₀ * c₀⁻¹ with hy₀
  have hy₀3 : y₀ ^ 3 = 1 := by
    rw [hy₀, conj_pow, hw₀3]
    group
  have hy₀1 : y₀ ≠ 1 := fun h => hw₀1 (by
    have : w₀ = c₀⁻¹ * y₀ * c₀ := by rw [hy₀]; group
    rw [this, h]
    group)
  clear_value y₀
  have hιc : φ (ι c₀) = ι c₀ := (hrange _).mp ⟨c₀, rfl⟩
  set E₂ : Y ⧸ aschbacherSolvableCore 3 Y ≃* M := E.trans (MulAut.conj (ι c₀)) with hE₂
  have hα₂ : KFacts.inducedAutHom Y E₂ ⟨c, hcN⟩ = φ := by
    rw [hE₂, Item8KFacts3.inducedAutHom_trans_conj, hφ]
    exact conj_mul_mul_conj_inv_of_fixed _ hιc
  have hdin₂ : KFacts.IsInnerAut (KFacts.inducedAutHom Y E₂ ⟨d, hdN⟩) := by
    rw [KFacts.inducedAutHom_apply, KFacts.isInnerAut_congr]
    exact hdin
  obtain ⟨w', hw', hw'3, hw'1, ⟨eW⟩⟩ := Item8KFacts3.exists_conj_residual E₂ hZ hdN hd3 hdin₂ hdne
  have hw'eq : w' = ι y₀ := by
    apply hinj
    rw [hw', hE₂, Item8KFacts3.inducedAutHom_trans_conj, ← hw, hy₀]
    simp only [map_mul, map_inv, hw₀]
  have hHmap : (barCentralizer (Subgroup.zpowers c) Y).map E₂.toMonoidHom = ι.range :=
    KFacts.map_barCentralizer_eq hcN E₂ ι.range (fun z => by
      rw [hα₂]
      exact hrange z)
  have hCmap : (barCentralizer (Subgroup.zpowers d) Y).map E₂.toMonoidHom =
      Subgroup.centralizer ({w'} : Set M) :=
    KFacts.map_barCentralizer_eq hdN E₂ _ (fun z => by
      rw [← hw', MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
        mul_inv_eq_iff_eq_mul]
      exact eq_comm)
  have hZmap : (barCentralizer (Subgroup.zpowers c) Y ⊓ barCentralizer (Subgroup.zpowers d) Y).map
      E₂.toMonoidHom = ι.range ⊓ Subgroup.centralizer ({w'} : Set M) := by
    rw [Subgroup.map_inf_eq _ _ _ E₂.injective, hHmap, hCmap]
  rcases hc₀ with hSy | hLy
  ·
    right
    have hq := hS y₀ hSy hy₀3 hy₀1
    set N := Subgroup.centralizer ({y₀} : Set H) with hN
    have hS1 : ι.range ⊓ Subgroup.centralizer ({w'} : Set M) = N.map ι := by
      ext x
      constructor
      · rintro ⟨⟨n, rfl⟩, hx⟩
        have hx' : ι n ∈ Subgroup.centralizer ({w'} : Set M) := hx
        refine ⟨n, ?_, rfl⟩
        show n ∈ N
        rw [hN, Subgroup.mem_centralizer_singleton_iff]
        rw [Subgroup.mem_centralizer_singleton_iff] at hx'
        apply hι
        rw [map_mul, map_mul, ← hw'eq]
        exact hx'
      · rintro ⟨n, hn, rfl⟩
        have hn' : n ∈ Subgroup.centralizer ({y₀} : Set H) := hn
        refine ⟨⟨n, rfl⟩, ?_⟩
        show ι n ∈ Subgroup.centralizer ({w'} : Set M)
        rw [Subgroup.mem_centralizer_singleton_iff] at hn' ⊢
        rw [hw'eq, ← map_mul, ← map_mul, hn']
    have hperf : Group.IsPerfect ↥(N.map ι) :=
      (LocalCores.isQuasisimple_of_mulEquiv (N.equivMapOfInjective ι hι) hq).1
    have hwN : w' ∈ N.map ι := ⟨y₀, Subgroup.mem_centralizer_singleton_iff.mpr rfl, hw'eq.symm⟩
    have hwres : w' ∈ inSubgroup perfectResidual (N.map ι) :=
      KFacts.le_inSubgroup_perfectResidual hperf le_rfl hwN
    have hmap := KFacts.map_inSubgroup_perfectResidual E₂
      (barCentralizer (Subgroup.zpowers c) Y ⊓ barCentralizer (Subgroup.zpowers d) Y)
    rw [hZmap, hS1] at hmap
    have hwmem : w' ∈ (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers c) Y ⊓
        barCentralizer (Subgroup.zpowers d) Y)).map E₂.toMonoidHom := by
      rw [hmap]
      exact hwres
    obtain ⟨z, hz, hzw⟩ := hwmem
    refine ⟨z, hz, ?_, ?_, ?_⟩
    · rintro rfl
      apply hw'1
      rw [← hzw]
      exact map_one _
    · apply E₂.injective
      change E₂ (z ^ 3) = E₂ 1
      rw [map_pow, map_one]
      exact (congrArg (· ^ 3) hzw).trans hw'3
    · intro y hy
      have hzw' : E₂ z = w' := hzw
      have hyw : E₂ y ∈ N.map ι := by
        have : E₂ y ∈ (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers c) Y ⊓
            barCentralizer (Subgroup.zpowers d) Y)).map E₂.toMonoidHom := ⟨y, hy, rfl⟩
        rw [hmap] at this
        exact Item87Proof.residual_le _ this
      rw [← hS1] at hyw
      have hcm : E₂ y * w' = w' * E₂ y := Subgroup.mem_centralizer_singleton_iff.mp
        (show E₂ y ∈ Subgroup.centralizer ({w'} : Set M) from hyw.2)
      apply E₂.injective
      rw [map_mul, map_mul, hzw']
      exact hcm.symm
  ·
    left
    subst hw'eq
    obtain ⟨e⟩ := hL y₀ hLy hy₀3 hy₀1
    exact ⟨eW.trans e⟩

end Generic


section G2Classes


theorem g2_classes_of_card {k₀ : Type} [Field k₀] [Finite k₀] {m : ℕ} (hm2 : 2 ≤ m)
    (hk : Nat.card k₀ = 2 ^ m) :
    ∀ w₀ : adjointGroup Tag.G2 k₀, w₀ ^ 3 = 1 → w₀ ≠ 1 → ∃ c₀ : adjointGroup Tag.G2 k₀,
      c₀ * w₀ * c₀⁻¹ ∈ Sec11.KS11Lie4Proof.g2ShortSL2 k₀ ∨
        c₀ * w₀ * c₀⁻¹ ∈ Sec11.KS11Lie4Proof.g2LongSL2 k₀ := fun w₀ hw₀3 hw₀1 =>
  Sec11.KS11Lie7Proof.g2ThreeConjSL2_holds k₀
    (by rw [Item8KFacts3.ringChar_eq_two_of_card hk]; decide)
    (hk ▸ Item8KFacts3.four_le_two_pow hm2) w₀ hw₀3 hw₀1

theorem g2_threeA_quasisimple_of_card {k₀ : Type} [Field k₀] [Finite k₀] {m : ℕ} (hm2 : 2 ≤ m)
    (hodd : Odd m) (hk : Nat.card k₀ = 2 ^ m) {y : adjointGroup Tag.G2 k₀}
    (hy : y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 k₀) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    IsQuasisimple (Subgroup.centralizer ({y} : Set (adjointGroup Tag.G2 k₀))) :=
  Sec11.KS11Lie7Proof.isQuasisimple_centralizer_threeA (hk ▸ three_dvd_two_pow_add_one hodd)
    (hk ▸ Item8KFacts3.four_le_two_pow hm2) hy hy3 hy1

theorem classBDichotomy_g2 {G : Type} [Group G] [Finite G] {Y : Subgroup G} {c d : G}
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hcd : c * d = d * c) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcout : Sec4.InducesOuterTheta c Y)
    (hdin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hdne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    {m : ℕ} (hm2 : 2 ≤ m) (hodd : Odd m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (3 * m))
    (E : Y ⧸ aschbacherSolvableCore 3 Y ≃* adjointGroup Tag.G2 K) :
    ClassBDichotomy Y c d m := by
  classical
  have hK2 : ringChar K = 2 := Item8KFacts3.ringChar_eq_two_of_card hK
  have hK3 : ringChar K ≠ 3 := by rw [hK2]; decide
  have hK4 : 4 ≤ Nat.card K := hK ▸ Item8KFacts3.four_le_two_pow (by omega)
  have hZ : Subgroup.center (adjointGroup Tag.G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hα3 : (KFacts.inducedAutHom Y E ⟨c, hcN⟩) ^ 3 = 1 :=
    KFacts.inducedAutHom_pow_eq_one Y E hcN hc3
  have hαout : ¬ KFacts.IsInnerAut (KFacts.inducedAutHom Y E ⟨c, hcN⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff Y E hcN).mpr hcout
  obtain ⟨σ, hσ3, k, hαk⟩ := KFacts.g2_order_three_field_descent hK3 hK4 hα3 hαout
  set E₁ : Y ⧸ aschbacherSolvableCore 3 Y ≃* adjointGroup Tag.G2 K :=
    E.trans (MulAut.conj k⁻¹) with hE₁
  have hα₁ : KFacts.inducedAutHom Y E₁ ⟨c, hcN⟩ = KFacts.g2FieldHom K σ := by
    rw [hE₁, Item8KFacts3.inducedAutHom_trans_conj, hαk, map_inv]
    group
  have : Finite (fixSubfield σ) := Subtype.finite
  have hcard : Nat.card (fixSubfield σ) = 2 ^ m := by
    have h := KFacts.card_fixSubfield_pow σ
    rw [hσ3, hK, pow_mul'] at h
    exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) h
  refine classBDichotomy_of_model hcN hdN hcd hd3 hdin hdne hZ (KFacts.g2Incl σ)
    (KFacts.g2Incl_injective σ) E₁ (KFacts.g2FieldHom K σ) hα₁
    (fun z => KFacts.mem_range_g2Incl_iff hK2 σ z)
    (fun y => y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 (fixSubfield σ))
    (fun y => y ∈ Sec11.KS11Lie4Proof.g2LongSL2 (fixSubfield σ))
    (g2_classes_of_card hm2 hcard) ?_ (fun y hy hy3 hy1 =>
      g2_threeA_quasisimple_of_card hm2 hodd hcard hy hy3 hy1)
  intro y hyM hy3 hy1
  have hyM' : KFacts.g2Incl σ y ∈ Sec11.KS11Lie4Proof.g2LongSL2 K :=
    Item83Proof.g2Incl_mem_g2LongSL2 σ hyM
  have hι3 : (KFacts.g2Incl σ y) ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hι1 : KFacts.g2Incl σ y ≠ 1 := fun h =>
    hy1 (KFacts.g2Incl_injective σ (h.trans (map_one _).symm))
  have heq := Item83Proof.inSubgroup_perfectResidual_centralizer_eq_g2ShortSL2 hK3 hK4 hyM' hι3 hι1
  obtain ⟨eS⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
  obtain ⟨eP⟩ := KFacts.nonempty_sl2_mulEquiv_projSL (F := K) hK
  exact ⟨(MulEquiv.subgroupCongr heq).trans (eS.symm.trans eP)⟩

end G2Classes

section D4


theorem inducedAutHom_trans_mulAut {G : Type} [Group G] [Finite G] {Y : Subgroup G} {M : Type*}
    [Group M] (E : Y ⧸ aschbacherSolvableCore 3 Y ≃* M) (φ : MulAut M)
    (x : Subgroup.normalizer (Y : Set G)) :
    KFacts.inducedAutHom Y (E.trans φ) x = φ * KFacts.inducedAutHom Y E x * φ⁻¹ := by
  rw [KFacts.inducedAutHom_apply, KFacts.inducedAutHom_apply, KFacts.congr_trans]
  ext m
  rfl

theorem ordG2_ne_ordPGU {q : ℕ} (hq : 4 ≤ q) :
    q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ≠ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
  intro h
  have hq3 : 64 ≤ q ^ 3 := calc
    64 = 4 ^ 3 := by norm_num
    _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hq2 : 16 ≤ q ^ 2 := calc
    16 = 4 ^ 2 := by norm_num
    _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  obtain ⟨a, ha⟩ : ∃ a, a = q ^ 3 := ⟨_, rfl⟩
  have h6 : q ^ 6 = a ^ 2 := by rw [ha]; ring
  rw [h6] at h
  rw [← ha] at hq3 h
  have hpos : 0 < a * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  have h' : a * (a ^ 2 - 1) = a + 1 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc a * (q ^ 2 - 1) * (a * (a ^ 2 - 1)) = a ^ 2 * (a ^ 2 - 1) * (q ^ 2 - 1) := by ring
      _ = a * (q ^ 2 - 1) * (a + 1) := by rw [h]
  have ha1 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [ha1] at h'
  nlinarith

theorem classBDichotomy_d4 {G : Type} [Group G] [Finite G] {Y : Subgroup G} {c d : G}
    (h47 : Sec4.Inputs47ClassesD4)
    (hcN : c ∈ Subgroup.normalizer (Y : Set G)) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hcd : c * d = d * c) (hc3 : c ^ 3 = 1) (hd3 : d ^ 3 = 1)
    (hcout : Sec4.InducesOuterTheta c Y)
    (hdin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hdne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1)
    {m : ℕ} (hm2 : 2 ≤ m) (hodd : Odd m) {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (hK : Nat.card K = (2 ^ m) ^ 3) (hσ : ∀ x, σ x = x ^ 2 ^ m)
    (E : Y ⧸ aschbacherSolvableCore 3 Y ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) m) :
    ClassBDichotomy Y c d m := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * m) := by rw [hK, ← pow_mul, mul_comm]
  have hK2 : ringChar K = 2 := Item8KFacts3.ringChar_eq_two_of_card hK3
  have hm1 : 1 ≤ m := by omega
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hα3 : (KFacts.inducedAutHom Y E ⟨c, hcN⟩) ^ 3 = 1 :=
    KFacts.inducedAutHom_pow_eq_one Y E hcN hc3
  have hαout : ¬ KFacts.IsInnerAut (KFacts.inducedAutHom Y E ⟨c, hcN⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff Y E hcN).mpr hcout
  rcases h47 m hodd K σ hK hσ _ hα3 hαout with ⟨β, hβ⟩ | ⟨γ, y, -, -, -, -, hPGU⟩
  ·
    set E₁ : Y ⧸ aschbacherSolvableCore 3 Y ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      E.trans β⁻¹ with hE₁
    obtain ⟨φ, hφ, hrange⟩ : ∃ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        KFacts.inducedAutHom Y E₁ ⟨c, hcN⟩ = φ ∧
          ∀ z, z ∈ (KFacts.trialityG2Incl σ hK2).range ↔ φ z = z := by
      rcases hβ with hβ | hβ
      · refine ⟨fieldActor σ σ, ?_, fun z => KFacts.mem_range_trialityG2Incl_iff σ hK2 z⟩
        rw [hE₁, inducedAutHom_trans_mulAut, hβ]
        group
      · refine ⟨(fieldActor σ σ)⁻¹, ?_, fun z => ?_⟩
        · rw [hE₁, inducedAutHom_trans_mulAut, hβ]
          group
        · rw [KFacts.mem_range_trialityG2Incl_iff σ hK2 z, MulAut.inv_apply,
            MulEquiv.symm_apply_eq, eq_comm]
    have hcard : Nat.card (fixSubfield σ) = 2 ^ m := KFacts.card_fixSubfield_of_cube hm1 hK hσ
    have P : Sec19.D4Par m K σ := ⟨hm1, hK, hσ⟩
    have : Finite (fixSubfield σ) := Subtype.finite
    refine classBDichotomy_of_model hcN hdN hcd hd3 hdin hdne hZ (KFacts.trialityG2Incl σ hK2)
      (KFacts.trialityG2Incl_injective σ hK2) E₁ φ hφ hrange
      (fun y => y ∈ Sec11.KS11Lie4Proof.g2ShortSL2 (fixSubfield σ))
      (fun y => y ∈ Sec11.KS11Lie4Proof.g2LongSL2 (fixSubfield σ))
      (g2_classes_of_card hm2 hcard) ?_ (fun y hy hy3 hy1 =>
        g2_threeA_quasisimple_of_card hm2 hodd hcard hy hy3 hy1)
    intro y hyM hy3 hy1
    exact HeringD4.residual_iota_of_mem_long P hK2 hyM hy3 hy1
  ·
    exfalso
    have hmap := KFacts.map_barCentralizer_eq hcN E
      (Sec4.autFix (KFacts.inducedAutHom Y E ⟨c, hcN⟩)) (fun z => Iff.rfl)
    let eH : ↥(barCentralizer (Subgroup.zpowers c) Y) ≃*
        ↥(Sec4.autFix (KFacts.inducedAutHom Y E ⟨c, hcN⟩)) :=
      (E.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
    obtain ⟨K', _, _, hK', ⟨eG⟩⟩ := hG2
    have h1 : Nat.card (barCentralizer (Subgroup.zpowers c) Y) = CFSG.Open.ordG2 (2 ^ m) := by
      rw [Nat.card_congr eG.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK']
    have h2 := CFSG.HardMathSupport.Lang.E27Lie.card_isoPGUThree hm1 hPGU
    rw [← Nat.card_congr eH.toEquiv, h1] at h2
    exact ordG2_ne_ordPGU (by calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2) h2

end D4

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
