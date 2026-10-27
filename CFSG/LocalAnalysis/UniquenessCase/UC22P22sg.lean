module

import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.EvenBN.GMSK.CatAltBender
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Alt
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAlt
import CFSG.Holt.PointHullTwoGroupBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22s
public import CFSG.Quasithin.Background.GoldschmidtE23Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin (autI IntMod)
open scoped commutatorElement

section NotAlt

variable {Y : Type} [Group Y] [Finite Y]

theorem uc22p22sg_not_alt {n : ℕ} (hn : 3 ≤ n) (hshape : IsSz Y n ∨ IsL2 Y n ∨ IsSU3 Y n ∨ IsSL3 Y n ∨ IsSp4 Y n)
    {m : ℕ} (hm : 5 ≤ m) (ψ : Y →* alternatingGroup (Fin m)) (hψ : Function.Surjective ψ) : False := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hA : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
  have hdvd : Nat.card (alternatingGroup (Fin m)) ∣ Nat.card Y := Subgroup.card_dvd_of_surjective (f := ψ) hψ
  have hAnt : Nontrivial (alternatingGroup (Fin m)) := by
    haveI : IsSimpleGroup (alternatingGroup (Fin m)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
    infer_instance
  have hiso : IsSimpleGroup Y → Nat.card Y = m.factorial / 2 := by
    intro hs
    have hker : ψ.ker = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
      · exact h
      · exfalso
        obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin m))
        obtain ⟨y, rfl⟩ := hψ a
        exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top y))
    rw [← hA]
    exact Nat.card_congr (MulEquiv.ofBijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).1 hker, hψ⟩).toEquiv
  have hcen : CFSG.Open.IsQuasisimple Y → Nat.card (Y ⧸ Subgroup.center Y) = m.factorial / 2 := by
    intro hq
    have hkc : ψ.ker ≤ Subgroup.center Y := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups
          (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq) (N := ψ.ker) inferInstance with h | h
      · exfalso
        obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin m))
        obtain ⟨y, rfl⟩ := hψ a
        exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top y))
      · exact h
    have hck : Subgroup.center Y ≤ ψ.ker := by
      intro z hz
      have hzc : ψ z ∈ Subgroup.center (alternatingGroup (Fin m)) := by
        rw [Subgroup.mem_center_iff]
        intro a
        obtain ⟨y, rfl⟩ := hψ a
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz) y]
      rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega), Subgroup.mem_bot] at hzc
      exact hzc
    rw [← hA]
    exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq (le_antisymm hck hkc)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).toEquiv
  have h3 : 3 ∣ m.factorial / 2 := CFSG.LocalAnalysis.EvenBN.GMSK.AltBender.three_dvd_factorial_div_two (by omega)
  rcases hshape with h | h | h | h | h
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 h
      ((hA ▸ h3).trans hdvd)
  · have hY := hiso (CFSG.Blueprint.LieModel.isSimpleGroup_psl_two h)
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h] at hY
    have := CFSG.SeitzReduction.RankOne.eq_two_of_ordA_one_eq_factorial_div_two (f := n) (by omega) hY
    omega
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.AltBender.card_ne_factorial_div_two_of_lieModel_PSU3 h.2 hm
      (hcen h.1)
  · have hc := hcen h.1
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h.2] at hc
    rcases CFSG.SeitzReduction.LinearPilot.ordA_two_pow_eq_factorial_div_two (n := 2) le_rfl (by omega) hc with
      h' | h' <;> omega
  · have hY := hiso (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h)
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h] at hY
    exact CFSG.SeitzReduction.SymplecticPilot.ordBC_two_pow_ne_factorial_div_two (m := 2) le_rfl (by omega) hY

end NotAlt

section Image

variable {G : Type} [Group G] [Finite G] {V L : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)

namespace P22s

@[expose] noncomputable def barStar (hLN : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) : Bar2 L →* ↥(autI hV L) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥L) (CFSG.Quasithin.GE23.starHom hV hLN) fun x hx => by
    rw [CFSG.Quasithin.GE23.ker_starHom]
    exact Subgroup.mem_subgroupOf.2 ⟨x.2, hO ⟨x, hx, rfl⟩⟩

theorem barStar_surjective (hLN : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) : Function.Surjective (barStar hV hLN hO) := by
  intro y
  obtain ⟨x, rfl⟩ := CFSG.Quasithin.GE23.starHom_surjective hV hLN y
  exact ⟨QuotientGroup.mk x, QuotientGroup.lift_mk _ _ _⟩

end P22s

open P22s

theorem uc22p22sg_autI_perfect (hLN : L ≤ normalizer (V : Set G)) (hLp : ⁅L, L⁆ = L) :
    ⁅autI hV L, autI hV L⁆ = autI hV L := by
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hLp
  rw [← CFSG.Quasithin.range_convHom hV L hLN]
  exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range _)

theorem uc22p22sg_isQuasisimple_autI (hLN : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    (hne : autI hV L ≠ ⊥) : CFSG.Open.IsQuasisimple ↥(autI hV L) := by
  have hq' := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq
  have hs := barStar_surjective hV hLN hO
  have hker : (barStar hV hLN hO).ker ≤ Subgroup.center (Bar2 L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq' (N := (barStar hV hLN hO).ker) inferInstance with
      h | h
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
      have h1 : barStar hV hLN hO x = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x)
      rw [h1] at hx
      rw [Subgroup.mem_bot]
      exact (congrArg Subtype.val hx).symm
    · exact h
  exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mp
    (CFSG.LocalCores.isQuasisimple_of_surjective hq' _ hs hker)

theorem uc22p22sg_normal_of_isQuasisimple {X : Type} [Group X] {K : Subgroup X}
    (hq : CFSG.Open.IsQuasisimple ↥K) :
    ∀ N : Subgroup X, N ≤ K → K ≤ normalizer (N : Set X) → N = K ∨ K ≤ centralizer (N : Set X) := by
  intro N hNK hKN
  haveI : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)
      (N := N.subgroupOf K) inferInstance with h | h
  · left
    exact le_antisymm hNK (Subgroup.subgroupOf_eq_top.1 h)
  · right
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have := Subgroup.mem_center_iff.1 (h (show (⟨n, hNK hn⟩ : ↥K) ∈ N.subgroupOf K from hn)) ⟨k, hk⟩
    exact (congrArg Subtype.val this).symm

theorem uc22p22sg_not_alt_autI (hLN : L ≤ normalizer (V : Set G))
    (hO : pCoreOf 2 L ≤ centralizer (V : Set G)) {n : ℕ} (hn : 3 ≤ n)
    (hshape : IsSz (Bar2 L) n ∨ IsL2 (Bar2 L) n ∨ IsSU3 (Bar2 L) n ∨ IsSL3 (Bar2 L) n ∨ IsSp4 (Bar2 L) n)
    {m : ℕ} (hm : 5 ≤ m) (e : ↥(autI hV L) ≃* alternatingGroup (Fin m)) : False :=
  uc22p22sg_not_alt hn hshape hm (e.toMonoidHom.comp (barStar hV hLN hO))
    (e.surjective.comp (barStar_surjective hV hLN hO))

end Image

theorem uc22p22sg_isQuasisimple_bar2_of_shape {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hLp : ⁅L, L⁆ = L) {n : ℕ} (hshape : NParamSingle (Bar2 L) n) : CFSG.Open.IsQuasisimple (Bar2 L) := by
  have hsimple : IsSimpleGroup (Bar2 L) → CFSG.Open.IsQuasisimple (Bar2 L) := by
    intro hs
    refine CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup ?_
    haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hLp
    haveI : Group.IsPerfect (Bar2 L) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
    by_contra hcomm
    push Not at hcomm
    have hbot : commutator (Bar2 L) = ⊥ := by
      rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm a b
    have htop : commutator (Bar2 L) = ⊤ := Group.isPerfect_def.mp inferInstance
    obtain ⟨a, b, hab⟩ := exists_pair_ne (Bar2 L)
    have ha : a ∈ commutator (Bar2 L) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ commutator (Bar2 L) := htop ▸ Subgroup.mem_top b
    rw [hbot, Subgroup.mem_bot] at ha hb
    exact hab (ha.trans hb.symm)
  rcases hshape with h | h | h | h | h
  · exact hsimple (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h)
  · exact hsimple (CFSG.Blueprint.LieModel.isSimpleGroup_psl_two h)
  · exact h.1
  · exact h.1
  · exact hsimple (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h)

end CFSG.LocalAnalysis.UniquenessCase.UC22
