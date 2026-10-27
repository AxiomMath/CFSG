module

public import CFSG.Quasithin.Vol2.Ch12Sec5Lemmas
public import CFSG.Quasithin.Vol2.Ch12Sec5Tr2
public import CFSG.Quasithin.Vol2.KGFactOut
public import CFSG.Quasithin.Vol2.GoldschmidtP778A5Setup
public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.E2TwoC
public import CFSG.Quasithin.Background.E2TwoCLie
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.H13.NParamRootFourLift
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125
open scoped Pointwise

namespace S125Fin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem quot_pCore_equiv_of_quotSL {X Y V : Subgroup G} {d : ℕ}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G))) (hY : IsPGroup 2 ↥Y)
    (hOY : pCoreOf 2 X ≤ Y) (hq : QuotSL X Y V d) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hN, ⟨ψ⟩⟩ := hq
  let φ₀ : ↥X →* ↥(autOn X V) := (A4.actionOn V X hXV).codRestrict (autOn X V)
    (fun x => (A4.mem_autOn_iff hXV).mpr ⟨x, rfl⟩)
  have hφ₀s : Function.Surjective φ₀ := by
    rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff hXV).mp ha
    exact ⟨x, rfl⟩
  let φ : ↥X →* Matrix.SpecialLinearGroup (Fin d) (ZMod 2) :=
    ψ.toMonoidHom.comp ((QuotientGroup.mk' ((autOn Y V).subgroupOf (autOn X V))).comp φ₀)
  have hφs : Function.Surjective φ :=
    ψ.surjective.comp ((QuotientGroup.mk'_surjective _).comp hφ₀s)
  have hker : ∀ x : ↥X, φ x = 1 ↔ A4.actionOn V X hXV x ∈ autOn Y V := by
    intro x
    change ψ (QuotientGroup.mk' _ (φ₀ x)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl
  have hkerP : φ.ker = CFSG.pCore 2 ↥X := by
    apply le_antisymm
    · have hp : IsPGroup 2 ↥φ.ker := by
        intro x
        have hx : A4.actionOn V X hXV x ∈ autOn Y V := (hker x).mp x.2
        obtain ⟨y, hy⟩ := (A4.mem_autOn_iff hYV).mp hx
        obtain ⟨k, hk⟩ := hY y
        have h1 : A4.actionOn V X hXV ((x : ↥X) ^ 2 ^ k) = 1 := by
          have hk' : A4.actionOn V Y hYV (y ^ 2 ^ k) = 1 := by rw [hk, map_one]
          rw [map_pow, ← hy, ← map_pow]
          exact hk'
        have h2 : (((x : ↥X) ^ 2 ^ k : ↥X) : G) ∈ X ⊓ Subgroup.centralizer (V : Set G) :=
          ⟨((x : ↥X) ^ 2 ^ k).2, (A4.actionOn_eq_one_iff hXV _).mp h1⟩
        obtain ⟨m, hm⟩ := hC ⟨_, h2⟩
        refine ⟨k + m, Subtype.ext (Subtype.ext ?_)⟩
        have h3 := congrArg (fun z : ↥(X ⊓ Subgroup.centralizer (V : Set G)) => (z : G)) hm
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3 ⊢
        rw [pow_add, pow_mul]
        exact h3
      exact CFSG.LieType.BorelTits.le_pCore 2 inferInstance hp
    · intro x hx
      rw [MonoidHom.mem_ker, hker]
      have hxY : (x : G) ∈ Y := hOY ⟨x, by assumption, rfl⟩
      exact (A4.mem_autOn_iff hYV).mpr ⟨⟨x, hxY⟩, rfl⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerP.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

theorem lOne_quot_equiv (h1222 : Stmt12_2_2) {T L V : Subgroup G} {F : Frame125 T L V}
    (hH : Hyp125 G T L V) (h2 : Concl12_5_2 T L V F)
    (hTL₁ : T ≤ Subgroup.normalizer (li L F.V1 : Set G)) :
    Nonempty (↥(li L F.V1) ⧸ CFSG.pCore 2 ↥(li L F.V1) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hL₁L : li L F.V1 ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hXV : li L F.V1 ≤ Subgroup.normalizer (V : Set G) := hL₁L.trans hf.normalizes
  have hYV : ri T L F.V1 ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le hXV hf.T_le)
  have hC : IsPGroup 2 ↥(li L F.V1 ⊓ Subgroup.centralizer (V : Set G)) :=
    (S125Tr2.isPGroup_centralizer hH hf).to_le
      (inf_le_inf_right _ (hL₁L.trans le_sup_left))
  have hOY : pCoreOf 2 (li L F.V1) ≤ ri T L F.V1 :=
    E1.ThinA5.pCoreOf_le_pCoreOf le_sup_left (sup_le Subgroup.le_normalizer hTL₁)
  exact quot_pCore_equiv_of_quotSL hXV hYV hC (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    hOY h2.1.2.2.1

theorem le_sup_of_quot {G₁ L₁ T : Subgroup G} (hL₁G₁ : L₁ ≤ G₁)
    (hN : G₁ ≤ Subgroup.normalizer (L₁ : Set G)) (hT : QuasithinUnique.IsSylowTwoOf T G₁)
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    G₁ ≤ centralizerMod (pCoreOf 2 L₁) G₁ L₁ ⊔ (L₁ ⊔ T) := by
  intro x hx
  obtain ⟨d, hd, hdx⟩ := outFact1295_holds G G₁ L₁ T hL₁G₁ hN hT (Or.inl ⟨e⟩) x hx
  have hx' : x = d * (d⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hd) (Subgroup.mem_sup_right hdx)

theorem mem_pCoreOf_of_mem {G₁ L₁ : Subgroup G}
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) {x : G}
    (hx : x ∈ centralizerMod (pCoreOf 2 L₁) G₁ L₁) (hxL : x ∈ L₁) : x ∈ pCoreOf 2 L₁ := by
  have hZ := center_eq_bot_of_mulEquiv_sl (by norm_num) e
  have hc : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have h1 : (⟨(x : G) * l * x⁻¹ * (l : G)⁻¹, by
          have := l.2
          exact L₁.mul_mem (L₁.mul_mem (L₁.mul_mem hxL this) (L₁.inv_mem hxL))
            (L₁.inv_mem this)⟩ : ↥L₁) ∈ CFSG.pCore 2 ↥L₁ :=
        E1.ThinA5.mem_pCore_of_mem_pCoreOf le_rfl _ (hx.2.2 l l.2)
      have hnorm : (CFSG.pCore 2 ↥L₁).Normal := inferInstance
      have h2 := hnorm.conj_mem _ h1 (l * ⟨x, hxL⟩)⁻¹
      convert h2 using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact ⟨⟨x, hxL⟩, by assumption, rfl⟩

theorem isElemAbelian_sup_zpowers {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    {E : Subgroup Y} (hE : IsElemAbelian p E) {z : Y} (hz : z ^ p = 1) (hzE : z ∉ E)
    (hc : ∀ x ∈ E, x * z = z * x) :
    IsElemAbelian p (E ⊔ Subgroup.zpowers z) ∧
      Nat.card ↥(E ⊔ Subgroup.zpowers z) = Nat.card E * p := by
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hzo : orderOf z = p := orderOf_eq_prime hz hz1
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (E : Set Y) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun h hh => hc h hh)
  have hinf : Subgroup.zpowers z ⊓ E = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers z ⊓ E) ∣ p := by
      rw [← hzo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
    · exact Subgroup.card_eq_one.mp h
    · exfalso
      apply hzE
      have heq : Subgroup.zpowers z ⊓ E = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Nat.card_zpowers, hzo])
      have hle : Subgroup.zpowers z ≤ E := by
        rw [← heq]
        exact inf_le_right
      exact hle (Subgroup.mem_zpowers z)
  have hcard := QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hzo, sup_comm] at hcard
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left E (Subgroup.zpowers z) hN
  have hcz : ∀ a ∈ E, ∀ i : ℤ, Commute a (z ^ i) := fun a ha i =>
    (show Commute a z from hc a ha).zpow_right i
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => by
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hdecomp : ∀ x ∈ E ⊔ Subgroup.zpowers z, ∃ a ∈ E, ∃ i : ℤ, x = a * z ^ i := by
    intro x hx
    have hx' : x ∈ ((E : Set Y) * (Subgroup.zpowers z : Set Y)) := by rw [← hmul]; exact hx
    obtain ⟨a, ha, w, hw, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ⟨a, ha, i, rfl⟩
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, by rw [hcard, mul_comm]⟩
  · obtain ⟨a, ha, i, hai⟩ := hdecomp x x.2
    obtain ⟨b, hb, j, hbj⟩ := hdecomp y y.2
    change (x : Y) * y = y * x
    rw [hai, hbj]
    have h1 : a * z ^ i * (b * z ^ j) = a * b * (z ^ i * z ^ j) := by
      rw [mul_assoc a, ← mul_assoc (z ^ i), ← (hcz b hb i).eq, mul_assoc, mul_assoc]
    have h2 : b * z ^ j * (a * z ^ i) = b * a * (z ^ j * z ^ i) := by
      rw [mul_assoc b, ← mul_assoc (z ^ j), ← (hcz a ha j).eq, mul_assoc, mul_assoc]
    rw [h1, h2, hEc a ha b hb, (Commute.zpow_zpow_self z i j).eq]
  · obtain ⟨a, ha, i, rfl⟩ := hdecomp x hx
    rw [(hcz a ha i).mul_pow, hE.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hz, one_zpow]

@[expose] def sl3Three : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩

theorem orderOf_sl3Three : orderOf sl3Three = 3 :=
  orderOf_eq_prime (by decide) (by decide)

omit [Finite G] in
theorem exists_orderOf_eq_three {L₁ : Subgroup G} [Finite ↥L₁]
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ∃ z ∈ L₁, orderOf z = 3 := by
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm sl3Three)
  have h3 : 3 ∣ orderOf l := by
    have h1 := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L₁)) l
    rwa [QuotientGroup.mk'_apply, hl, MulEquiv.orderOf_eq, orderOf_sl3Three] at h1
  refine ⟨((l ^ (orderOf l / 3) : ↥L₁) : G), (l ^ (orderOf l / 3)).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (orderOf_pos l).ne' h3

theorem pRank_three_le_one {G₁ L₁ : Subgroup G} (hL₁G₁ : L₁ ≤ G₁)
    (hN : G₁ ≤ Subgroup.normalizer (L₁ : Set G)) (h2 : CFSG.Open.pRank 3 G₁ ≤ 2)
    (e : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    CFSG.Open.pRank 3 (centralizerMod (pCoreOf 2 L₁) G₁ L₁) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizerMod (pCoreOf 2 L₁) G₁ L₁ with hXdef
  set N := pCoreOf 2 L₁ with hNdef
  by_contra hlt
  have hr2 : 2 ≤ CFSG.Open.pRank 3 X := by omega
  obtain ⟨E, hEX, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) X
  have hEG₁ : E ≤ G₁ := hEX.trans (centralizerMod_le_left _ _ _)
  have hNL₁ : N ≤ L₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 L₁
  have hN2 : IsPGroup 2 ↥N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁
  have hNn : G₁ ≤ Subgroup.normalizer (N : Set G) := by
    have hchar : (CFSG.Open.pCore 2 ↥L₁).Characteristic := by
      infer_instance
    exact hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.Open.pCore 2 ↥L₁))
  set N' : Subgroup ↥G₁ := N.subgroupOf G₁ with hN'
  have hN'n : N'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hNL₁.trans hL₁G₁)).mpr hNn
  set π := QuotientGroup.mk' N' with hπ
  have hE3 : IsPGroup 3 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hEN : E ⊓ N = ⊥ :=
    disjoint_iff.mp (IsPGroup.disjoint_of_coprime hE3 hN2 (by norm_num))
  obtain ⟨z, hzL, hzo⟩ := exists_orderOf_eq_three e
  have hzN : z ∉ N := by
    intro hz
    obtain ⟨k, hk⟩ := hN2 ⟨z, hz⟩
    have hk' : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h3 := orderOf_dvd_of_pow_eq_one hk'
    rw [hzo] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  set E' : Subgroup ↥G₁ := E.subgroupOf G₁ with hE'
  let f : ↥E' →* ↥G₁ ⧸ N' := π.comp E'.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : π (x : ↥G₁) = 1 := hx
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
      at hx1
    have hxE : ((x : ↥G₁) : G) ∈ E := x.2
    have : ((x : ↥G₁) : G) ∈ E ⊓ N := ⟨hxE, hx1⟩
    rw [hEN, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext (Subtype.ext this))
  set Eb : Subgroup (↥G₁ ⧸ N') := E'.map π with hEb
  have hEbf : Eb = f.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEbc : Nat.card Eb = Nat.card E := by
    rw [hEbf, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG₁).toEquiv]
  have hEbe : IsElemAbelian 3 Eb := by
    have := hE.1
    have hE'e : IsElemAbelian 3 E' := ⟨inferInstance, fun x hx => Subtype.ext (hE.2 _ hx)⟩
    exact CFSG.SectionRank.isElemAbelian_map hE'e π
  set zb : ↥G₁ ⧸ N' := π ⟨z, hL₁G₁ hzL⟩ with hzb
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hL₁G₁ hzL⟩ : ↥G₁) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← hzo]
      exact pow_orderOf_eq_one z
    rw [this, map_one]
  have hzbE : zb ∉ Eb := by
    rintro ⟨y, hy, hyz⟩
    have hyz' : π (y⁻¹ * ⟨z, hL₁G₁ hzL⟩) = 1 := by rw [map_mul, map_inv, hyz, inv_mul_cancel]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
      at hyz'
    have hyE : (y : G) ∈ E := hy
    have hyL : (y : G) ∈ L₁ := by
      have h1 : ((y⁻¹ * ⟨z, hL₁G₁ hzL⟩ : ↥G₁) : G) ∈ L₁ := hNL₁ hyz'
      have h2 : (y : G) = z * (((y⁻¹ * ⟨z, hL₁G₁ hzL⟩ : ↥G₁) : G))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h2]
      exact L₁.mul_mem hzL (L₁.inv_mem h1)
    have hyN : (y : G) ∈ N := mem_pCoreOf_of_mem e (hEX hyE) hyL
    have hy1 : (y : G) = 1 := by
      have : (y : G) ∈ E ⊓ N := ⟨hyE, hyN⟩
      rwa [hEN, Subgroup.mem_bot] at this
    apply hzN
    have h3 : ((y⁻¹ * ⟨z, hL₁G₁ hzL⟩ : ↥G₁) : G) = z := by
      simp [hy1]
    rw [← h3]
    exact hyz'
  have hzbc : ∀ x ∈ Eb, x * zb = zb * x := by
    rintro _ ⟨y, hy, rfl⟩
    have hw := (hEX hy).2.2 z hzL
    have hg : (z * (y : G))⁻¹ ∈ G₁ := G₁.inv_mem (G₁.mul_mem (hL₁G₁ hzL) y.2)
    have h1 := (Subgroup.mem_normalizer_iff.mp (hNn hg) _).mp (N.inv_mem hw)
    rw [hzb, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, hN', Subgroup.mem_subgroupOf]
    convert h1 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
    group
  obtain ⟨hEz, hEzc⟩ := isElemAbelian_sup_zpowers hEbe hzb3 hzbE hzbc
  have hle := CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
    (le_top : Eb ⊔ Subgroup.zpowers zb ≤ ⊤)
    hEz (k := CFSG.Open.pRank 3 X + 1) (by rw [hEzc, hEbc, hEc, pow_succ])
  have hN'3 : ¬ 3 ∣ Nat.card ↥N' := by
    intro h3
    have hN'2 : IsPGroup 2 ↥N' :=
      hN2.of_equiv (Subgroup.subgroupOfEquivOfLe (hNL₁.trans hL₁G₁)).symm
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN'2
    rw [hk] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq N' hN'3, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    at hle
  omega

end S125Fin

end CFSG.Quasithin.H13
