module

public import CFSG.Quasithin.Vol2.Ch12Sec4G2NormZorn
public import CFSG.Quasithin.Vol2.Ch12Sec4L3Hyp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

@[expose] def InvolFact1248 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1242 G T L V →
    (Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) →
    ∀ t ∈ Subgroup.normalizer (L : Set G), t ∉ Subgroup.centralizer (V : Set G) →
      t ^ 2 ∈ Subgroup.centralizer (V : Set G) →
        (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V ≠ 2

namespace S1248

variable {G : Type} [Group G]

theorem map_fixV_conjAct {V : Subgroup G} [IsMulCommutative ↥V] {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) :
    (fixV (Subgroup.zpowers (conjAct V ⟨t, htV⟩))).map V.subtype =
      V ⊓ Subgroup.centralizer ({t} : Set G) := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.2, ?_⟩
    show (v : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : conjAct V ⟨t, htV⟩ v = v := hv _ (Subgroup.mem_zpowers _)
    have h2 := conjAct_coe_apply V ⟨t, htV⟩ v
    rw [h1] at h2
    calc (v : G) * t = t * v * t⁻¹ * t := by rw [← h2]
      _ = t * v := by group
  · rintro ⟨hxV, hxt⟩
    have hxt' : x ∈ Subgroup.centralizer ({t} : Set G) := hxt
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    show (⟨x, hxV⟩ : ↥V) ∈ fixV (Subgroup.zpowers (conjAct V ⟨t, htV⟩))
    rw [L3Hyp.mem_fixV_zpowers]
    apply Subtype.ext
    rw [conjAct_coe_apply]
    rw [Subgroup.mem_centralizer_singleton_iff] at hxt'
    change t * x * t⁻¹ = x
    calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [hxt']
      _ = x := by group

theorem relIndex_mul_card_fixV [Finite G] {V : Subgroup G} [IsMulCommutative ↥V] {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) :
    (V ⊓ Subgroup.centralizer ({t} : Set G)).relIndex V *
        Nat.card (fixV (Subgroup.zpowers (conjAct V ⟨t, htV⟩))) = Nat.card V := by
  have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer ({t} : Set G)) V
  rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer ({t} : Set G) ≤ V)] at h1
  have hc : Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) =
      Nat.card (fixV (Subgroup.zpowers (conjAct V ⟨t, htV⟩))) := by
    rw [← map_fixV_conjAct htV, Subgroup.card_map_of_injective V.subtype_injective]
  rw [hc] at h1
  exact h1

end S1248

theorem involFact1248_of
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242) (h12210 : Stmt12_2_10) :
    InvolFact1248 := by
  intro G _ _ T L V hcx hq t htM htC ht2
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hcx hq
  obtain ⟨hc, hcases⟩ := modules_cases_of_hyp1223 h1222 hyp
  have := hf.comm
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hf.normalizes
  have htV : t ∈ Subgroup.normalizer (V : Set G) := by rw [← hf.MN]; exact htM
  have hW : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hf.sq w w.2)
  have hVp : IsPGroup 2 V := hyp.sylow.1.to_le hf.le_T
  have hZ2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rw [hf.zV, Nat.card_zpowers, hf.order]
  have hcommGr : commV (autOn L V) = ⊤ := commV_autOn_eq_top hLV hf.commutator
  have hfixGr : Nat.card (fixV (autOn L V)) = 2 := by
    rw [fixV_autOn_eq hLV, card_subgroupOf_eq_card_inf, hZ2]
  set a := conjAct V ⟨t, htV⟩ with ha
  have ha1 : a ≠ 1 := fun h => htC (A4.conjAct_eq_one_iff.1 h)
  have ha2 : a ^ 2 = 1 := by
    rw [ha, ← map_pow]
    exact A4.conjAct_eq_one_iff.2 (by simpa using ht2)
  have hrel := S1248.relIndex_mul_card_fixV htV
  rw [← ha] at hrel
  intro h2
  rw [h2] at hrel
  have hidx4 : ∀ (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)),
      24 < Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) →
        4 < (V ⊓ Subgroup.centralizer (L : Set G)).relIndex V := fun hs h24 =>
    four_lt_relIndex_of_simple hLV hf.commutator hf.notCent hf.pCore hs h24
  have hcardV : ∀ (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)),
      24 < Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) → 8 < Nat.card V := by
    intro hs h24
    have h1 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (L : Set G)) V
    rw [inf_eq_left.2 (inf_le_left : V ⊓ Subgroup.centralizer (L : Set G) ≤ V), hZ2] at h1
    have := hidx4 hs h24
    omega
  rcases hq with h3 | hU
  ·
    obtain ⟨e⟩ := h3
    have hs3 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
      have := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
      exact e.isSimpleGroup
    have h168 := card_quot_of_sl_three ⟨e⟩
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hf.pCore hs3 hf.notCent
    have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
    have hGr : Nat.card (autOn L V) = 168 := by rw [Nat.card_congr eA.toEquiv, h168]
    have hV16 : Nat.card V = 2 ^ 4 := by
      have hle := hcases.1 ⟨e⟩
      have h8 := hcardV hs3 (by rw [h168]; norm_num)
      obtain ⟨n, hn⟩ := hVp.exists_card_eq
      rw [hn] at hle h8 ⊢
      have hn4 : n ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
      interval_cases n <;> first | rfl | norm_num at h8
    have hnat := binaryNaturalSL_of_card_sixteen hW hV16 hGrs hGr hcommGr hfixGr
    obtain ⟨D⟩ := hnat.toL3Coord
    have haX : a ∈ autOn L V :=
      Vol2.Ch10.SecD.mem_of_normalizes D hcommGr fun φ => conj_mem_autOn_iff htM htV φ
    have h16 : Nat.card ↥V = 16 := by rw [hV16]; norm_num
    have hind := Vol2.Ch10.SecD.isIndecompModule_of D hcommGr h16
    obtain ⟨-, -, -, h4⟩ := B4_8_2 hW h16 hnat hind
    have hrk := (h4 a haX ha1 ha2).2
    have hfix4 : Nat.card (fixV (Subgroup.zpowers a)) = 4 := by
      rw [CFSG.Quasithin.card_eq_two_pow hW, hrk]
      norm_num
    rw [hfix4, h16] at hrel
    omega
  ·
    have hsU : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.Timmesfeld.isSimpleGroup_of_lieModel hU
    have h6048 := card_of_lieModel_psu_three_three hU
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hLV hf.pCore hsU hf.notCent
    have hGrs : IsSimpleGroup (autOn L V) := eA.isSimpleGroup
    have hZL : autOn L V ⊓ Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) = ⊥ := by
      have hnab : ¬ ∀ a b : autOn L V, a * b = b * a := by
        intro hall'
        obtain ⟨-, -, a, b, hab'⟩ := hyp.quasisimple
        apply hab'
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
        have h1 : a' * b' = b' * a' := eA.symm.injective (by
          rw [map_mul, map_mul]
          exact hall' _ _)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h1]
      have hnorm : ((Subgroup.centralizer (autOn L V : Set (MulAut ↥V))).subgroupOf
          (autOn L V)).Normal := by
        refine ⟨fun n hn x => ?_⟩
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hn ⊢
        intro y hy
        have h1 := hn y hy
        have h2 := hn (x : MulAut ↥V) x.2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc y * (↑x * ↑n * (↑x)⁻¹) = y * (↑n * ↑x * (↑x)⁻¹) := by rw [← h2]
          _ = y * n := by group
          _ = n * y := h1
          _ = ↑n * ↑x * (↑x)⁻¹ * y := by group
          _ = ↑x * ↑n * (↑x)⁻¹ * y := by rw [h2]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.centralizer
          (autOn L V : Set (MulAut ↥V))).subgroupOf (autOn L V)) with hb | ht
      · refine eq_bot_iff.2 fun y hy => ?_
        have h1 : (⟨y, hy.1⟩ : autOn L V) ∈ (Subgroup.centralizer
            (autOn L V : Set (MulAut ↥V))).subgroupOf (autOn L V) :=
          Subgroup.mem_subgroupOf.2 hy.2
        rw [hb, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
      · exfalso
        apply hnab
        intro a b
        have h1 : a ∈ (Subgroup.centralizer (autOn L V : Set (MulAut ↥V))).subgroupOf
            (autOn L V) := ht ▸ Subgroup.mem_top a
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
        exact Subtype.ext (h1 b b.2).symm
    have hMC : autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V ⊓
        Subgroup.centralizer (autOn L V : Set (MulAut ↥V)) = ⊥ :=
      (h12210 G T L V hyp).1.trans hZL
    have hnat : G2NaturalDerived (autOn L V) ⊤ (fixV (autOn L V)) 1 := by
      rw [fixV_autOn_eq hLV]
      exact hcases.2.1 hU
    set X := autOn (Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V : Set G)) V
      with hXdef
    have hLX : autOn L V ≤ X := A4.autOn_mono (le_inf Subgroup.le_normalizer hLV)
    have hXN : X ≤ Subgroup.normalizer (autOn L V : Set (MulAut ↥V)) :=
      autOn_le_normalizer_autOn_of_le inf_le_left
    have haX : a ∈ X := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨htM, htV⟩)
    have hA2 : Nat.card (Subgroup.zpowers a) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha2 ha1]
    have hoff : IsFFStarOffender X (Subgroup.zpowers a) := by
      refine ⟨Subgroup.zpowers_le.2 haX, fun h => ha1 (Subgroup.zpowers_eq_bot.1 h), ?_, ?_⟩
      · refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
        · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
          rw [← zpow_add, ← zpow_add, add_comm]
        · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha2, one_zpow]
      · intro B hB
        have hdvd : Nat.card B ∣ 2 := hA2 ▸ Subgroup.card_dvd_of_le hB
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h1
        · rw [Subgroup.card_eq_one.1 h1, Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top,
            one_mul, hA2]
          omega
        · rw [Subgroup.eq_of_le_of_card_ge hB (by rw [h1, hA2])]
    have hB46 := b46OffenderCommEqFix ↥V hW X (autOn L V) hLX hXN hMC hcommGr hnat _ hoff
    have hcf := card_commV_mul_card_fixV hW a
    rw [hB46] at hcf
    have h8 := hcardV hsU (by rw [h6048]; norm_num)
    nlinarith

end CFSG.Quasithin.H13
