module

public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLTools
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec12.KS128NotHJTools
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
public import CFSG.RankThree.PartTwo.Sec12.Item128Bar125
public import CFSG.RankThree.PartTwo.Sec12.KS128NotHJSLStatements

public section

namespace CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem exists_move (hM : KS128TypeCMove) {c : G} {L E : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    (hcL : c ∈ L) (hc1 : c ≠ 1) (hcC : c ∈ Sec4.thetaQuotCentralizer L)
    (hE : Late.IsE27 E) (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hcE : c ∈ E)
    {a : G} (haE : a ∈ E) (haL : a ∈ L) (haC : a ∉ Sec4.thetaQuotCentralizer L)
    (hB3 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3) :
    ∃ y ∈ Subgroup.normalizer (E : Set G), y * c = c * y ∧
      y * a * y⁻¹ * a⁻¹ ∈ Subgroup.zpowers c ∧ y * a * y⁻¹ ≠ a ∧
      ∀ f ∈ E, f ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c →
        y * f * y⁻¹ * f⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers c ∧
          y * f * y⁻¹ * f⁻¹ ∉ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hEc : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hE.1.2
  set φ : E →* MulAut (L ⧸ aschbacherSolvableCore 3 L) :=
    (thetaBarAct L).comp (Subgroup.inclusion hEN) with hφ
  have hφapp : ∀ (e : G) (he : e ∈ E), φ ⟨e, he⟩ = thetaBarAct L ⟨e, hEN he⟩ := fun _ _ => rfl
  have hker : ∀ (e : G) (he : e ∈ E), φ ⟨e, he⟩ = 1 ↔ e ∈ Sec4.thetaQuotCentralizer L :=
    fun e he => (mem_thetaQuotCentralizer_iff_thetaBarAct (hEN he)).symm
  have hBc : (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = Subgroup.zpowers c := by
    have hc3 : orderOf c = 3 := orderOf_eq_prime (hE3 c hcE) hc1
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨hcE, hcC⟩)) ?_).symm
    rw [hB3, Nat.card_zpowers, hc3]
  have hkerφ : φ.ker.map E.subtype = E ⊓ Sec4.thetaQuotCentralizer L := by
    ext x
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.2, (hker e e.2).mp he⟩
    · rintro ⟨hxE, hxC⟩
      exact ⟨⟨x, hxE⟩, (hker x hxE).mpr hxC, rfl⟩
  have hY9 : Nat.card φ.range = 9 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.ker = Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := by
      rw [← hkerφ, Subgroup.card_map_of_injective E.subtype_injective]
    rw [hB3] at h2
    rw [h2, Nat.card_congr (Equiv.refl E), hE.2] at h1
    omega
  have hYab : CFSG.Assembly.IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
    · obtain ⟨_, e₁, rfl⟩ := u
      obtain ⟨_, e₂, rfl⟩ := v
      apply Subtype.ext
      change φ e₁ * φ e₂ = φ e₂ * φ e₁
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hEc _ e₁.2 _ e₂.2)
    · rintro _ ⟨e, rfl⟩
      rw [← map_pow]
      have : e ^ 3 = 1 := Subtype.ext (by simpa using hE3 e e.2)
      rw [this, map_one]
  set ab := π ⟨a, haL⟩ with hab
  have hφa : φ ⟨a, haE⟩ = MulAut.conj ab := by
    rw [hφapp]
    exact thetaBarAct_of_mem haL
  have hconjY : MulAut.conj ab ∈ φ.range := ⟨⟨a, haE⟩, hφa⟩
  have hfix : ∀ σ ∈ φ.range, σ ab = ab := by
    rintro _ ⟨⟨e, he⟩, rfl⟩
    rw [hφapp, hab, thetaBarAct_mk]
    congr 1
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, hEc e he a haE, mul_inv_cancel_right]
  have habZ : ab ∉ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    intro hZ
    apply haC
    rw [← hker a haE, hφa]
    exact conj_eq_one_of_mem_center hZ
  have hab3 : ab ^ 3 = 1 := by
    rw [hab, ← map_pow]
    have : (⟨a, haL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hE3 a haE)
    rw [this, map_one]
  obtain ⟨u, hM1, hM1', hM2, hM3⟩ := hM _ (isQuasisimple_thetaQuot_of_mem hL) hSL ab habZ hab3
    φ.range hYab hY9 hconjY hfix
  set cb := π ⟨c, hcL⟩ with hcb
  have hinjS : Set.InjOn π (((E ⊓ L : Subgroup G).subgroupOf L : Subgroup L) : Set L) := by
    refine CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three ?_
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hE3 _ (Subgroup.mem_subgroupOf.mp x.2).1
  have hmemS : ∀ x : L, (x : G) ∈ E → x ∈ (E ⊓ L : Subgroup G).subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨hx, x.2⟩
  have hcb1 : cb ≠ 1 := by
    intro h1
    apply hc1
    have := hinjS (hmemS ⟨c, hcL⟩ hcE) (Subgroup.one_mem _) (by rw [map_one]; exact h1)
    exact congrArg Subtype.val this
  have hcbZ : cb ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
    mk_mem_center_of_mem_thetaQuotCentralizer (x := ⟨c, hcL⟩) hcC
  have hZc : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = Subgroup.zpowers cb := by
    have hcb3 : cb ^ 3 = 1 := by
      rw [hcb, ← map_pow]
      have : (⟨c, hcL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hE3 c hcE)
      rw [this, map_one]
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcbZ) ?_).symm
    rw [card_center_eq_three_of_isSLThreePi hSL, Nat.card_zpowers, orderOf_eq_prime hcb3 hcb1]
  set W := Subgroup.zpowers a ⊔ Subgroup.zpowers c with hW
  have hWE : W ≤ E := sup_le (Subgroup.zpowers_le.mpr haE) (Subgroup.zpowers_le.mpr hcE)
  have hWL : W ≤ L := sup_le (Subgroup.zpowers_le.mpr haL) (Subgroup.zpowers_le.mpr hcL)
  have hWim : Subgroup.zpowers ab ⊔ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≤
      (W.subgroupOf L).map π := by
    rw [hZc]
    refine sup_le (Subgroup.zpowers_le.mpr ⟨⟨a, haL⟩, ?_, rfl⟩)
      (Subgroup.zpowers_le.mpr ⟨⟨c, hcL⟩, ?_, rfl⟩)
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  obtain ⟨u₀, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 L) u
  obtain ⟨y, hyu, hyN⟩ := exists_lift_normalizer_of hE hEN hWE u₀ (fun e he =>
    hWim (hM2 _ ⟨⟨e, he⟩, rfl⟩))
  rw [← hπ] at hyu
  have hwL : ∀ e ∈ E, e * (y : G) * e⁻¹ * (y : G)⁻¹ ∈ L := fun e he => by
    have h1 : e * (y : G) * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hEN he) _).mp y.2
    exact L.mul_mem h1 (L.inv_mem y.2)
  have hwE : ∀ e ∈ E, e * (y : G) * e⁻¹ * (y : G)⁻¹ ∈ E := fun e he => by
    have h1 : (y : G) * e⁻¹ * (y : G)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hyN _).mp
      (E.inv_mem he)
    have e1 : e * (y : G) * e⁻¹ * (y : G)⁻¹ = e * ((y : G) * e⁻¹ * (y : G)⁻¹) := by group
    rw [e1]
    exact E.mul_mem he h1
  have hwπ : ∀ (e : G) (he : e ∈ E), π ⟨_, hwL e he⟩ = φ ⟨e, he⟩ (π u₀) * (π u₀)⁻¹ := by
    intro e he
    have h4 : (⟨_, hwL e he⟩ : L) = L.normalizerMonoidHom ⟨e, hEN he⟩ y * y⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
    rw [h4, map_mul, map_inv, hφapp, ← thetaBarAct_mk, hyu]
  have hwa : π ⟨_, hwL a haE⟩ = (π u₀ * ab * (π u₀)⁻¹ * ab⁻¹)⁻¹ := by
    rw [hwπ a haE, hφa, MulAut.conj_apply]
    group
  have hwaZ : π ⟨_, hwL a haE⟩ ∈ Subgroup.zpowers cb := by
    rw [hwa, ← hZc]
    exact inv_mem hM1
  have hwa1 : π ⟨_, hwL a haE⟩ ≠ 1 := by
    rw [hwa]
    intro h1
    apply hM1'
    have h2 := inv_eq_one.mp h1
    calc π u₀ * ab * (π u₀)⁻¹ = (π u₀ * ab * (π u₀)⁻¹ * ab⁻¹) * ab := by group
      _ = ab := by rw [h2, one_mul]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwaZ
  have hckE : (((⟨c, hcL⟩ : L) ^ k : L) : G) ∈ E := by
    rw [Subgroup.coe_zpow]
    exact E.zpow_mem hcE k
  have hck : (⟨_, hwL a haE⟩ : L) = (⟨c, hcL⟩ : L) ^ k :=
    hinjS (hmemS _ (hwE a haE)) (hmemS _ hckE) (by rw [map_zpow, ← hcb, hk])
  have hwa' : a * (y : G) * a⁻¹ * (y : G)⁻¹ = c ^ k := by
    have := congrArg Subtype.val hck
    simpa using this
  refine ⟨y, hyN, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : π ⟨_, hwL c hcE⟩ = π 1 := by
      rw [hwπ c hcE, (hker c hcE).mpr hcC, MulAut.one_apply, mul_inv_cancel, map_one]
    have h2 := hinjS (hmemS _ (hwE c hcE)) (Subgroup.one_mem _) h1
    have h3 : c * (y : G) * c⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val h2
    calc (y : G) * c = (c * (y : G) * c⁻¹ * (y : G)⁻¹)⁻¹ * c * y := by group
      _ = c * y := by rw [h3, inv_one, one_mul]
  ·
    have e1 : (y : G) * a * (y : G)⁻¹ * a⁻¹ = (a * (y : G) * a⁻¹ * (y : G)⁻¹)⁻¹ := by group
    rw [e1, hwa']
    exact inv_mem (Subgroup.zpow_mem_zpowers c k)
  ·
    intro h1
    apply hwa1
    have h2 : a * (y : G) * a⁻¹ * (y : G)⁻¹ = 1 := by
      calc a * (y : G) * a⁻¹ * (y : G)⁻¹ = ((y : G) * a * (y : G)⁻¹ * a⁻¹)⁻¹ := by group
        _ = 1 := by rw [h1, mul_inv_cancel, inv_one]
    have h3 : (⟨_, hwL a haE⟩ : L) = 1 := Subtype.ext h2
    rw [h3, map_one]
  ·
    intro f hfE hfW
    have hφf : φ ⟨f, hfE⟩ ∉ Subgroup.zpowers (MulAut.conj ab) := by
      intro hmem
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hfW
      have hmem' : f * (a ^ j)⁻¹ ∈ E := E.mul_mem hfE (E.inv_mem (E.zpow_mem haE j))
      have h1 : φ ⟨f * (a ^ j)⁻¹, hmem'⟩ = 1 := by
        have e1 : (⟨f * (a ^ j)⁻¹, hmem'⟩ : E) = ⟨f, hfE⟩ * ((⟨a, haE⟩ : E) ^ j)⁻¹ :=
          Subtype.ext (by simp)
        rw [e1, map_mul, map_inv, map_zpow, hφa, hj, mul_inv_cancel]
      have h3 : f * (a ^ j)⁻¹ ∈ Subgroup.zpowers c := by
        rw [← hBc]
        exact ⟨hmem', (hker _ hmem').mp h1⟩
      have e2 : f = (f * (a ^ j)⁻¹) * a ^ j := by group
      rw [e2]
      exact mul_mem (Subgroup.mem_sup_right h3)
        (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers a j))
    have hfr : φ ⟨f, hfE⟩ ∈ φ.range := ⟨_, rfl⟩
    have h3 := hM3 _ hfr hφf
    have h2 := hWim (hM2 _ hfr)
    rw [← hwπ f hfE] at h2 h3
    obtain ⟨w, hwW, hwe⟩ := h2
    have hww : w = ⟨_, hwL f hfE⟩ :=
      hinjS (hmemS _ (hWE (Subgroup.mem_subgroupOf.mp hwW))) (hmemS _ (hwE f hfE)) hwe
    have hwfW : f * (y : G) * f⁻¹ * (y : G)⁻¹ ∈ W := by
      have := Subgroup.mem_subgroupOf.mp hwW
      rwa [hww] at this
    have hwfc : f * (y : G) * f⁻¹ * (y : G)⁻¹ ∉ Subgroup.zpowers c := by
      intro hmem
      apply h3
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have e1 : (⟨_, hwL f hfE⟩ : L) = (⟨c, hcL⟩ : L) ^ j := Subtype.ext (by simp [hj])
      rw [e1, map_zpow, ← hcb, hZc]
      exact Subgroup.zpow_mem_zpowers cb j
    have e3 : (y : G) * f * (y : G)⁻¹ * f⁻¹ = (f * (y : G) * f⁻¹ * (y : G)⁻¹)⁻¹ := by group
    rw [e3]
    exact ⟨inv_mem hwfW, fun hmem => hwfc (by simpa using inv_mem hmem)⟩

theorem false_of_transitive (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    (hG1 : Gap125NonCentralBar) (hM : KS128TypeCMove) {A L : Subgroup G} {c : G}
    (h : Sec12StdBar G A c L) (hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L))
    {a : G} (ha3 : a ^ 3 = 1) (haC : a ∉ Sec4.thetaQuotCentralizer L) (haL : a ∈ L)
    {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) (haK : a ∉ K)
    {F : Subgroup G} (hFK : F ≤ K) (hF : CFSG.Assembly.IsElemAbelian 3 F) (hF9 : Nat.card F = 9)
    (hcF : c ∈ F)
    (hT : ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
      ∃ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) ∧ m * u * m⁻¹ = v) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL := h.mem_thetaComponentsAt
  have hcL := h.mem_L
  have hc1 := h.ne_one
  have hc3 : orderOf c = 3 := orderOf_eq_prime (h.isE27.1.2 c h.mem_A) hc1
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hL
  have hcC : c ∈ Sec4.thetaQuotCentralizer L := mem_thetaQuotCentralizer_of_central hcL hLc
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have haF : a ∉ F := fun h1 => haK (hFK h1)
  have hFa : ∀ y ∈ F, a * y = y * a := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKa (hFK hy))).symm
  obtain ⟨hEab, hE27⟩ := Sec13.isElemAbelian_zpowers_sup_of_card_nine ha3 haF le_rfl hF9
    (fun s hs => hF.2 s hs) hFa
  set E := Subgroup.zpowers a ⊔ F with hEdef
  have hE : Late.IsE27 E := ⟨hEab, hE27⟩
  have haE : a ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hFE : F ≤ E := le_sup_right
  have hcE : c ∈ E := hFE hcF
  have hEc : ∀ x ∈ E, ∀ z ∈ E, x * z = z * x := fun x hx z hz =>
    congrArg Subtype.val (hEab.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩)
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Sec13.centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx c hcE))
  have hEN : E ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hc3 hL hEp hEH
  have hmN : ∀ m ∈ K, m ∈ Subgroup.normalizer (F : Set G) →
      m ∈ Subgroup.normalizer (E : Set G) ∧ m * a = a * m := by
    intro m hmK hmF
    have hma : m * a = a * m := Subgroup.mem_centralizer_singleton_iff.mp (hKa hmK)
    refine ⟨?_, hma⟩
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hmF ⊢
    rw [hEdef, Subgroup.map_sup, hmF, MonoidHom.map_zpowers]
    congr 2
    change m * a * m⁻¹ = a
    rw [hma, mul_inv_cancel_right]
  obtain ⟨f₀, hf₀F, hf₀c⟩ : ∃ f₀ ∈ F, f₀ ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show F ≤ Subgroup.zpowers c from hcon)
    rw [hF9, Nat.card_zpowers, hc3] at this
    omega
  have hf₀1 : f₀ ≠ 1 := fun h1 => hf₀c (h1 ▸ Subgroup.one_mem _)
  obtain ⟨m₀, hm₀K, hm₀F, hm₀⟩ := hT c hcF hc1 f₀ hf₀F hf₀1
  have hU : ¬ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro hle
    apply hf₀c
    rw [← hm₀]
    exact (Subgroup.mem_normalizer_iff.mp (hle (hmN m₀ hm₀K hm₀F).1) c).mp
      (Subgroup.mem_zpowers c)
  have hBp : IsPGroup 3 (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) := hEp.to_le inf_le_left
  have hdvd : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨n, hn3, hn⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases n
  ·
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hc1 (by simpa [hn] using (Subgroup.mem_inf.mpr ⟨hcE, hcC⟩ :
      c ∈ E ⊓ Sec4.thetaQuotCentralizer L))
  ·
    rw [pow_one] at hn
    obtain ⟨y, hyN, hyc, hya, hya1, hyF⟩ :=
      exists_move hM hL hSL hcL hc1 hcC hE hEN hcE haE haL haC hn
    have hT' : ∀ u ∈ F, u ≠ 1 → ∀ v ∈ F, v ≠ 1 →
        ∃ m ∈ Subgroup.normalizer (E : Set G), m * a = a * m ∧ m * u * m⁻¹ = v := by
      intro u hu hu1 v hv hv1
      obtain ⟨m, hmK, hmF, hm⟩ := hT u hu hu1 v hv hv1
      exact ⟨m, (hmN m hmK hmF).1, (hmN m hmK hmF).2, hm⟩
    have hFW : ∀ f ∈ F, f ∉ Subgroup.zpowers c →
        f ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
      intro f hfF hfc hfW
      obtain ⟨i, j, rfl⟩ := Sec4.exists_zpow_mul_of_mem_sup (hEc a haE c hcE) hfW
      have hcj : (c ^ j)⁻¹ ∈ F := F.inv_mem (F.zpow_mem hcF j)
      rcases zpow_eq_one_or_eq_or_eq_inv ha3 i with h0 | h1 | h2
      · exact hfc (by rw [h0, one_mul]; exact Subgroup.zpow_mem_zpowers c j)
      · apply haF
        have := F.mul_mem hfF hcj
        rwa [h1, mul_inv_cancel_right] at this
      · apply haF
        have := F.inv_mem (F.mul_mem hfF hcj)
        rwa [h2, mul_inv_cancel_right, inv_inv] at this
    obtain ⟨hh, hhE, hhc⟩ := exists_conj_eq_of_moves hEc haE ha3 hFE hcF hc1 hT' hyN hyc hya
      hya1 (fun f hfF hfc => hyF f (hFE hfF) (hFW f hfF hfc)) hf₀F hf₀c
    have hEdec : ∀ e ∈ E, ∃ k : ℤ, ∃ f ∈ F, e = a ^ k * f := by
      intro e he
      obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (Subgroup.zpowers a) F (fun x hx z hz => hEc x (Subgroup.mem_sup_left hx) z (hFE hz))
      have he' : e ∈ ((Subgroup.zpowers a ⊔ F : Subgroup G) : Set G) := he
      rw [hset] at he'
      obtain ⟨x, hx, f, hf, rfl⟩ := he'
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ⟨k, f, hf, rfl⟩
    exact haC (le_thetaQuotCentralizer_of_conj_eq hK haK hFK hFE hEdec hEN hL hcL hcC hhE hhc
      haE)
  ·
    have hB9 : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 9 := by
      rw [hn]
      norm_num
    have hEsup : Subgroup.zpowers a ⊔ (E ⊓ Sec4.thetaQuotCentralizer L) = E :=
      eq_of_card_nine_lt hE27 (sup_le (Subgroup.zpowers_le.mpr haE) inf_le_left) le_sup_right hB9
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)) (fun h1 => haC h1.2)
    have hEL : E ≤ lcBar c L := by
      rw [← hEsup]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · have := KS128NotHJTC.mul_mem_lcBar hL haL (Subgroup.one_mem _) (Subgroup.one_mem _)
        simpa using this
      · intro x hx
        have := KS128NotHJTC.mul_mem_lcBar hL L.one_mem hx.2 (hEH hx.1)
        simpa using this
    have hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 :=
      card_center_eq_three_of_isSLThreePi hSL
    have hEL9 : Nat.card (E ⊓ L : Subgroup G) = 9 := by
      have hac : a ∉ Subgroup.zpowers c := fun h1 =>
        haC ((Subgroup.zpowers_le.mpr hcC) h1)
      have h9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers a : Subgroup G) = 9 :=
        Sec4.card_zpowers_sup_zpowers ha3 hc3 hac (hEc a haE c hcE)
      have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers a ≤ E ⊓ L :=
        sup_le (Subgroup.zpowers_le.mpr ⟨hcE, hcL⟩) (Subgroup.zpowers_le.mpr ⟨haE, haL⟩)
      have hge : 9 ≤ Nat.card (E ⊓ L : Subgroup G) := h9 ▸ Subgroup.card_le_of_le hle
      have hdvd' : Nat.card (E ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
        rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE27]
        exact Subgroup.card_dvd_of_le inf_le_left
      obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
      interval_cases j
      · rw [hj] at hge; norm_num at hge
      · rw [hj] at hge; norm_num at hge
      · rw [hj]; norm_num
      · exfalso
        have hEL' : E ⊓ L = E :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj, hE27]; norm_num)
        have h1 := card_inf_le_card_center_of_le_thetaQuotCentralizer hBp inf_le_right (L := L)
        have h2 : E ⊓ Sec4.thetaQuotCentralizer L ⊓ L = E ⊓ Sec4.thetaQuotCentralizer L :=
          inf_eq_left.mpr (inf_le_left.trans (hEL' ▸ inf_le_right))
        rw [h2, hB9, hZ] at h1
        norm_num at h1
    obtain ⟨P, hP, hPB⟩ := hG1 G A c L h (Or.inl hSL) E hE hEL hcE hB9 hEL9 hU
    have hbar : Sec12StdBar G E c L :=
      { toPartTwoStanding := h.toPartTwoStanding
        partTwoF_eq := h.partTwoF_eq
        isE27 := hE
        mem_A := hcE
        ne_one := hc1
        mem_thetaComponentsAt := hL
        mem_L := hcL
        card_B := hB9
        sup_eq := sup_eq_of_card_inf_nine hE hZ hB9 hEL9
        exists_sylow := ⟨P, hP, hPB⟩ }
    exact hU (normalizer_le_of_sec12StdBar_of_list h45 hK2 hbar (Or.inl hSL))
  ·
    have hEC : E ⊓ Sec4.thetaQuotCentralizer L = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hn, hE27]; norm_num)
    exact haC (hEC ▸ haE).2

end CFSG.RankThree.PartTwo.Sec12.KS128NotHJSL
