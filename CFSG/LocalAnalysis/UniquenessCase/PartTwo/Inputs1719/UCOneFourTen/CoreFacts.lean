module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.Star
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

namespace CoreSetup

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X} {n : ℕ}

theorem mem_calC (h : CoreSetup X K L T Y n) : L ∈ calC Y := by
  refine ⟨h.subnormal, h.perfect, ?_⟩
  have hS : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h.sz
  obtain ⟨a, b, hab⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h.sz
  have hq : CFSG.IsQuasisimple (Bar2 L) :=
    (@CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Bar2 L) _ hS ⟨a, b, hab⟩).1
  exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

theorem normalizer_le_normalizer (h : CoreSetup X K L T Y n) {A : Subgroup X} (hAL : A ≤ L)
    (hA : (Nat.card A).Prime) (hA2 : Nat.card A ≠ 2) :
    normalizer (A : Set X) ≤ normalizer (L : Set X) := by
  have hAN : normalizer (A : Set X) ≤ Y := h.normalizer_odd_le A hAL hA hA2
  have h1 := inf_normalizer_le_normalizer (M := Y) h.mem_calC h.sz hAL hA hA2
  rwa [inf_eq_right.mpr hAN] at h1

theorem centralizer_le_Y (h : CoreSetup X K L T Y n) : centralizer (L : Set X) ≤ Y :=
  centralizer_le_of_normalizer_le h.sz h.normalizer_odd_le

theorem T_ne_bot (h : CoreSetup X K L T Y n) : T ≠ ⊥ :=
  ne_bot_of_normalizer_le h.ne_top h.normalizer_le

theorem odd_three_le (h : CoreSetup X K L T Y n) : Odd n ∧ 3 ≤ n :=
  ⟨CFSG.LocalAnalysis.EvenBN.GMSK.odd_of_lieModel_twistedB2 h.sz,
    CFSG.LocalAnalysis.EvenBN.GMSK.three_le_of_lieModel_twistedB2 h.sz⟩

theorem T_le_normalizer (h : CoreSetup X K L T Y n) : T ≤ normalizer (L : Set X) := by
  obtain ⟨P, hP⟩ := h.sylow
  exact (hP ▸ Subgroup.map_subtype_le (P : Subgroup ↥(F08.CentOverO2 Y L))).trans
    (centOverO2_le_normalizer Y L)

theorem odd_card_center (h : CoreSetup X K L T Y n) : Odd (Nat.card (center ↥K)) :=
  odd_card_center_of_normal h.pCore_eq_bot h.normal

theorem inf_center_eq_bot (h : CoreSetup X K L T Y n) :
    L ⊓ (center ↥K).map K.subtype = ⊥ := by
  classical
  set Z : Subgroup X := (center ↥K).map K.subtype with hZdef
  have hZcard : Nat.card Z = Nat.card ↥(center ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hZodd : Odd (Nat.card Z) := by
    rw [hZcard]
    exact h.odd_card_center
  have hZcent : Z ≤ Subgroup.centralizer (L : Set X) := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, h.le hl⟩)
  have hcentL : (L ⊓ Z).subgroupOf L ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    have hxZ : (x : X) ∈ Z := (Subgroup.mem_subgroupOf.mp hx).2
    exact Subgroup.mem_centralizer_iff.mp (hZcent hxZ) (l : X) l.2
  have hcenterBar : Subgroup.center (Bar2 L) = ⊥ := by
    have hS : IsSimpleGroup (Bar2 L) :=
      CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h.sz
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Bar2 L)) with
      hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, b, hab⟩ :=
        CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h.sz
      exact hab (Subgroup.mem_center_iff.mp (htop ▸ Subgroup.mem_top b) a)
  have hcenterL_le : Subgroup.center ↥L ≤ CFSG.pCore 2 ↥L := by
    intro z hz
    have hzc : QuotientGroup.mk' (CFSG.pCore 2 ↥L) z ∈ Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
      show QuotientGroup.mk' (CFSG.pCore 2 ↥L) l *
          QuotientGroup.mk' (CFSG.pCore 2 ↥L) z =
        QuotientGroup.mk' (CFSG.pCore 2 ↥L) z *
          QuotientGroup.mk' (CFSG.pCore 2 ↥L) l
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hcenterBar] at hzc
    exact (QuotientGroup.eq_one_iff z).mp (Subgroup.mem_bot.mp hzc)
  have hNle : (L ⊓ Z).subgroupOf L ≤ CFSG.pCore 2 ↥L := hcentL.trans hcenterL_le
  have hcardN : Nat.card ↥((L ⊓ Z).subgroupOf L) = Nat.card ↥(L ⊓ Z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hdvd : Nat.card ↥((L ⊓ Z).subgroupOf L) ∣ Nat.card Z := by
    rw [hcardN]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hNodd : Odd (Nat.card ↥((L ⊓ Z).subgroupOf L)) := hZodd.of_dvd_nat hdvd
  have hNbot : (L ⊓ Z).subgroupOf L = ⊥ := by
    have hNp : IsPGroup 2 ↥((L ⊓ Z).subgroupOf L) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le hNle
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hNp.card_eq_or_dvd with h1 | h2dvd
    · exact (Subgroup.card_eq_one).mp h1
    · exact absurd h2dvd (by
        have hne : ¬ Even (Nat.card ↥((L ⊓ Z).subgroupOf L)) :=
          Nat.not_even_iff_odd.mpr hNodd
        exact fun h2 => hne (even_iff_two_dvd.mpr h2))
  have hsub : L ⊓ Z ≤ ⊥ := by
    intro x hx
    have hxN : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ Z).subgroupOf L := hx
    rw [hNbot] at hxN
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxN))
  exact le_bot_iff.mp hsub

theorem card_dvd_card_quotient_center (h : CoreSetup X K L T Y n) :
    Nat.card L ∣ Nat.card (↥K ⧸ center ↥K) := by
  let f : ↥L →* (↥K ⧸ Subgroup.center ↥K) :=
    (QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion h.le)
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxZ : (x : X) ∈ (Subgroup.center ↥K).map K.subtype := by
      refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion h.le x, ?_, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hxbot : (x : X) ∈ (L ⊓ (Subgroup.center ↥K).map K.subtype) := ⟨x.2, hxZ⟩
    rw [h.inf_center_eq_bot] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : x * y⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hker] at h1
    exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h1)
  exact Subgroup.card_dvd_of_injective f hf

theorem card_bar2_dvd_card_quotient_center (h : CoreSetup X K L T Y n) :
    Nat.card (Bar2 L) ∣ Nat.card (↥K ⧸ center ↥K) :=
  (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L)).trans
    h.card_dvd_card_quotient_center

theorem pRank_K_le (h : CoreSetup X K L T Y n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 3 := by
  have hp1 : 1 < p := hp.one_lt
  exact (CFSG.SectionRank.pRank_top_le_of_injective (G := ↥K) (G' := X) hp1 K.subtype
    K.subtype_injective).trans (h.pRank_le p hp hp2)

end CoreSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
