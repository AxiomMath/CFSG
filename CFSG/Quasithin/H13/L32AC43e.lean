module

public import CFSG.Quasithin.H13.L32AC43d
public import CFSG.Quasithin.Background.SmithB45U3Nat

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open hiding StatedSL StatedSU StatedSp StatedProj StatedClassicalModel
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem exists_pow_mem_autK {y : MulAut (Hat V H W)} (hy : y ∈ C.act.range) :
    ∃ e : ℕ, y ^ 2 ^ e ∈ C.autK := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (C.autK.subgroupOf C.act.range).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C.autK_le).mpr C.range_le_normalizer
  rw [C.range_eq_sup] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    C.autT_le_normalizer).mp hy
  obtain ⟨e, he⟩ := C.isPGroup_autT ⟨b, hb⟩
  have hb2 : b ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  refine ⟨e, ?_⟩
  have haR : a ∈ C.act.range := C.autK_le ha
  have hbR : b ∈ C.act.range := C.autT_le hb
  let π := QuotientGroup.mk' (C.autK.subgroupOf C.act.range)
  have h1 : π ⟨a * b, C.act.range.mul_mem haR hbR⟩ ^ 2 ^ e = 1 := by
    have ha1 : π ⟨a, haR⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    have e1 : (⟨a * b, C.act.range.mul_mem haR hbR⟩ : ↥C.act.range) = ⟨a, haR⟩ * ⟨b, hbR⟩ := rfl
    rw [e1, map_mul, ha1, one_mul, ← map_pow]
    have : (⟨b, hbR⟩ : ↥C.act.range) ^ 2 ^ e = 1 := Subtype.ext (by simpa using hb2)
    rw [this, map_one]
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem genFitting_eq (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    quasithinGenFitting C.act.range = C.autK := by
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have hq := C.isQuasisimple_autK h1222 h1332 h1334
  exact InternalSec.quasithinGenFitting_eq_of_two_pow C.autK_le
    (fun y hy l hl => (Subgroup.mem_normalizer_iff.mp (C.range_le_normalizer hy) l).mp hl)
    ⟨hq.1.commutator_eq_top, hq.2.1⟩ (fun y hy => C.exists_pow_mem_autK hy)
    (C.pCoreOf_range h1222 h1332 h1334)

theorem sqtkGroup_range (hA21 : AsA21SQTKSection) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : SQTKGroup ↥C.act.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Hat V H W)) := finite_mulAut
  have hH := sqtkGroup_of_setting C.S
  set Λ : Subgroup ↥C.act.range := C.autK.subgroupOf C.act.range with hΛ
  have hΛn : Λ.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C.autK_le).mpr C.range_le_normalizer
  have hΛq : CFSG.IsQuasisimple ↥Λ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe C.autK_le).symm
      (C.isQuasisimple_autK h1222 h1332 h1334)
  refine hA21 ↥H hH ⊤ ↥C.act.range (C.act.rangeRestrict.comp Subgroup.topEquiv.toMonoidHom)
    (fun y => by
      obtain ⟨x, hx⟩ := MonoidHom.rangeRestrict_surjective C.act y
      exact ⟨⟨x, trivial⟩, hx⟩) Λ
    (B5.layer_eq_top_of_quasisimple hΛq) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨e, he⟩ := C.exists_pow_mem_autK y.2
  refine ⟨e, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hΛ, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow]
  exact he

theorem b4Hyp (hA21 : AsA21SQTKSection) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (hirr : ∀ J : Subgroup (Hat V H W), (∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤) :
    B4Hyp C.act.range C.autK := by
  refine ⟨C.sqtkGroup_range hA21 h1222 h1332 h1334, (C.genFitting_eq h1222 h1332 h1334).symm,
    C.isQuasisimple_autK h1222 h1332 h1334, ?_⟩
  refine ⟨bot_lt_iff_ne_bot.mpr C.top_ne_bot, fun J hJ _ _ => hirr J fun l hl v hv => ?_⟩
  exact hJ ⟨l, hl⟩ v hv

theorem binaryNaturalSU3
    (hA21 : AsA21SQTKSection) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hirr : ∀ J : Subgroup (Hat V H W), (∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    (hU : IsPSU 3 2 3 (cStar K ⧸ Subgroup.center (cStar K))) {B : Subgroup G}
    (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    BinaryNaturalSU3 C.autK ⊤ ⊥ 3 := by
  have hHyp := C.b4Hyp hA21 h1222 h1332 h1334 hirr
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hU
  obtain ⟨φ⟩ := C.nonempty_quotCenter_autK h1222 h1332 h1334
  have hA := C.isA2_autE h1222 h1332 h1334 hB hBT
  have hAV : Nat.card (Hat V H W) ≤ Nat.card ↥(C.autE B) ^ 2 * Nat.card ↥(fixV (C.autE B)) := by
    have h1 := C.index_fixV_autE_le h1222 h1332 h1334 hB hBT
    have h2 := (fixV (C.autE B)).card_mul_index
    calc Nat.card (Hat V H W) = Nat.card ↥(fixV (C.autE B)) * (fixV (C.autE B)).index := h2.symm
      _ ≤ Nat.card ↥(fixV (C.autE B)) * Nat.card ↥(C.autE B) ^ 2 := Nat.mul_le_mul_left _ h1
      _ = Nat.card ↥(C.autE B) ^ 2 * Nat.card ↥(fixV (C.autE B)) := mul_comm _ _
  obtain ⟨t, htL, ht2, ht1, hidx⟩ := B45U3.exists_small_involution C.hexp hHyp (f := 3)
    (by norm_num) hF (φ.symm.trans e) hA hAV
  have hperf : Group.IsPerfect ↥C.autK := (C.isQuasisimple_autK h1222 h1332 h1334).1
  refine u3NaturalOfSmallDisplacement_holds 3 (by norm_num) F hF (Hat V H W) C.sec_sq C.autK
    hperf (fun U hU => hirr U hU) ⟨φ.symm.trans e⟩ ⟨t, htL, ht2, ht1, hidx⟩

end Top43

end CFSG.Quasithin.H13.L32A.C
