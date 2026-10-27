module

public import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeOdd
public import CFSG.GH74.GLS.Pattern
import CFSG.RankThree.PartTwo.Sec20.SimsAscBridgeHyp
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace AscBridge

variable {G : Type} [Group G] [Finite G]
variable {A M L N : Subgroup G} {c : G} {T : Subgroup G} {i j : Fin 4} {P X : Subgroup G}

@[expose] noncomputable def kToYAlpha (hKY : kTwenty M c ≤ yTwenty X c) :
    ↥(kTwenty M c) →* ↥(yAlpha M X T c) :=
  ((QuotientGroup.mk' (CFSG.pPrimeCore 3
      ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))).comp
    (Subgroup.inclusion (hKY.trans le_sup_left))).codRestrict (yAlpha M X T c)
    fun k => ⟨Subgroup.inclusion (hKY.trans le_sup_left) k, hKY k.2, rfl⟩

theorem coe_kToYAlpha_apply (hKY : kTwenty M c ≤ yTwenty X c) (k : ↥(kTwenty M c)) :
    ((kToYAlpha (T := T) hKY k : ↥(yAlpha M X T c)) : _) =
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))
        (Subgroup.inclusion (hKY.trans le_sup_left) k) := rfl

theorem ker_kToYAlpha_le (hset : Setting204 G A M L N c T i j P)
    (hKY : kTwenty M c ≤ yTwenty X c) :
    (kToYAlpha (T := T) hKY).ker ≤ CFSG.pCore 2 ↥(kTwenty M c) := by
  intro k hk
  have hk1 := congrArg Subtype.val hk
  rw [coe_kToYAlpha_apply, QuotientGroup.mk'_apply, Subgroup.coe_one,
    QuotientGroup.eq_one_iff] at hk1
  have hkK₀ : (k : G) ∈ kTwenty M c ⊓ oThreePrimeYR M X T c := ⟨k.2, ⟨_, hk1, rfl⟩⟩
  have hkO := inf_inSubgroup_pPrimeCore_le hset (hKY.trans le_sup_left) hkK₀
  exact (Subgroup.mem_map_iff_mem (kTwenty M c).subtype_injective).mp hkO

theorem isPerfect_range_kToYAlpha (hset : Setting204 G A M L N c T i j P)
    (hKY : kTwenty M c ≤ yTwenty X c) : Group.IsPerfect ↥(kToYAlpha (T := T) hKY).range := by
  haveI : Group.IsPerfect ↥(kTwenty M c) :=
    isPerfect_of_mem_oTwoComponentsIn hset.mem_oTwoComponentsIn
  exact Group.IsPerfect.range _

theorem map_range_kToYAlpha (hKY : kTwenty M c ≤ yTwenty X c) :
    (kToYAlpha (T := T) hKY).range.map (yAlpha M X T c).subtype = kAlpha M X T c := by
  ext z
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨Subgroup.inclusion (hKY.trans le_sup_left) k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩, rfl⟩

theorem exists_surjective_kBar (hset : Setting204 G A M L N c T i j P)
    (hKY : kTwenty M c ≤ yTwenty X c) :
    ∃ φ : ↥(kToYAlpha (T := T) hKY).range →*
        (↥(kTwenty M c) ⧸ CFSG.pCore 2 ↥(kTwenty M c)), Function.Surjective φ := by
  set ψ := kToYAlpha (T := T) hKY with hψ
  refine ⟨(QuotientGroup.map ψ.ker (CFSG.pCore 2 ↥(kTwenty M c)) (MonoidHom.id _)
    (ker_kToYAlpha_le hset hKY)).comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom,
    ?_⟩
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨(QuotientGroup.quotientKerEquivRange ψ) (QuotientGroup.mk k), ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

theorem range_kToYAlpha_ne_bot (hset : Setting204 G A M L N c T i j P)
    (hKY : kTwenty M c ≤ yTwenty X c) : (kToYAlpha (T := T) hKY).range ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hbot
  have hc3 := Res6.orderOf_c_of_setting204 hset
  have hcK : c ∈ kTwenty M c := self_mem_normalClosureIn M c
  have hmem : kToYAlpha (T := T) hKY ⟨c, hcK⟩ ∈ (kToYAlpha (T := T) hKY).range := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg Subtype.val hmem
  rw [coe_kToYAlpha_apply, QuotientGroup.mk'_apply, Subgroup.coe_one,
    QuotientGroup.eq_one_iff] at h1
  have hdvd : orderOf (Subgroup.inclusion (hKY.trans le_sup_left) ⟨c, hcK⟩ :
      ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) ∣
        Nat.card (CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) := by
    rw [← Subgroup.orderOf_mk _ h1]
    exact orderOf_dvd_natCard _
  have ho : orderOf (Subgroup.inclusion (hKY.trans le_sup_left) ⟨c, hcK⟩ :
      ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) = 3 := by
    rw [← orderOf_injective _ (Subgroup.subtype_injective _)]
    exact hc3
  rw [ho] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card hdvd

theorem yAlpha_normal (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G)) :
    (yAlpha M X T c).Normal := by
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  exact (yAlpha_normal_and_sup_eq_top
    (((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c))).1

section Act

variable [(yAlpha M X T c).Normal]

theorem conjNormal_yAlpha_injective
    (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a) :
    Function.Injective (MulAut.conjNormal :
      (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
        CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) →*
          MulAut ↥(yAlpha M X T c)) := by
  have hKTX : kTwenty M c ⊔ T ≤ X := fun x hx => hX.2 hx
  have hRY : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ Subgroup.normalizer (yTwenty X c : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hKTX).trans
      (le_normalizer_normalClosureIn X c)
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  have hC := centralizer_yAlpha_eq_bot hRY hZ
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgC : g ∈ Subgroup.centralizer (SetLike.coe (yAlpha M X T c)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg Subtype.val (DFunLike.congr_fun hg ⟨y, hy⟩)
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at h
    calc y * g = g * y * g⁻¹ * g := by rw [h]
      _ = g * y := by group
  rw [hC, Subgroup.mem_bot] at hgC
  exact hgC

theorem conjNormal_eq_conj (y : ↥(yAlpha M X T c)) :
    MulAut.conjNormal (H := yAlpha M X T c) (Subtype.val y) = MulAut.conj y := by
  ext z
  rw [MulAut.conjNormal_apply, MulAut.conj_apply]
  rfl

theorem rAut_inf_innAut_eq_bot (hX : X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G))
    [IsSimpleGroup ↥(yAlpha M X T c)] (hnab : ∃ a b : ↥(yAlpha M X T c), a * b ≠ b * a)
    (h : rAlpha M X T c ⊓ yAlpha M X T c = ⊥) :
    (rAlpha M X T c).map MulAut.conjNormal ⊓ (MulAut.conj : ↥(yAlpha M X T c) →* _).range =
      ⊥ := by
  have hinj := conjNormal_yAlpha_injective hX hnab
  rw [eq_bot_iff]
  rintro _ ⟨⟨r, hr, rfl⟩, ⟨y, hy⟩⟩
  rw [← conjNormal_eq_conj] at hy
  have hry : (y : _) = r := hinj hy
  have hrY : r ∈ rAlpha M X T c ⊓ yAlpha M X T c := ⟨hr, hry ▸ y.2⟩
  rw [h, Subgroup.mem_bot] at hrY
  rw [Subgroup.mem_bot, hrY, map_one]

theorem range_le_fixedSubgroup_of_commute (hKY : kTwenty M c ≤ yTwenty X c)
    (hcomm : ∀ k ∈ kAlpha M X T c, ∀ r ∈ rAlpha M X T c, k * r = r * k) :
    ∀ u ∈ (rAlpha M X T c).map MulAut.conjNormal,
      (kToYAlpha (T := T) hKY).range ≤ CFSG.GH74.GLS.fixedSubgroup ↥(yAlpha M X T c) u := by
  rintro _ ⟨r, hr, rfl⟩ _ ⟨k, rfl⟩
  show MulAut.conjNormal r (kToYAlpha hKY k) = kToYAlpha hKY k
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hk : Subtype.val (kToYAlpha (T := T) hKY k) ∈ kAlpha M X T c := by
    rw [← map_range_kToYAlpha hKY]
    exact ⟨_, ⟨k, rfl⟩, rfl⟩
  rw [← hcomm _ hk r hr, mul_inv_cancel_right]

theorem commute_of_mem_fixedSubgroup {r : ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
      CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))}
    {y : ↥(yAlpha M X T c)}
    (hy : y ∈ CFSG.GH74.GLS.fixedSubgroup ↥(yAlpha M X T c) (MulAut.conjNormal r)) :
    r * y = y * r := by
  have h : MulAut.conjNormal r y = y := hy
  have h' := congrArg Subtype.val h
  rw [MulAut.conjNormal_apply] at h'
  calc r * y = r * y * r⁻¹ * r := by group
    _ = y * r := by rw [h']

end Act

end AscBridge

end CFSG.RankThree.PartTwo.Sec20
