module

public import CFSG.Adapters.LieModelSimple
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3L4Defs
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16t_l4_card_sup_of_commute_of_inf_eq_bot {H : Type*} [Group H] {A B : Subgroup H}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hd : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype hcomm) := by
    refine (MonoidHom.noncommCoprod_injective A.subtype B.subtype hcomm).2 ?_
    refine ⟨A.subtype_injective, B.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hd
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  calc Nat.card ↥(A ⊔ B)
      = Nat.card (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range := by rw [hrange]
    _ = Nat.card (↥A × ↥B) := (Nat.card_congr (Equiv.ofInjective _ hinj)).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

private theorem s16t_l4_exists_mul_of_mem_sup_of_commute {H : Type*} [Group H] {A B : Subgroup H}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : H} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hcomm : ∀ (a : ↥A) (b : ↥B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  have hx' : x ∈ (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact hx
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, h⟩ := hx'
  exact ⟨a, ha, b, hb, h⟩

private theorem s16t_l4_perm_fin_eight_orderOf_dvd_840 (σ : Equiv.Perm (Fin 8)) :
    orderOf σ ∣ 840 := by
  rw [← Equiv.Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.2 fun n hn => ?_
  have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  have hn8 : n ≤ 8 := by
    have h1 := Equiv.Perm.le_card_support_of_mem_cycleType hn
    have h2 : σ.support.card ≤ 8 := by simpa using Finset.card_le_univ σ.support
    exact h1.trans h2
  interval_cases n <;> decide

theorem s16t_l4_lbar_le_mbar (hS : S16tL4Setting D V₀ V L hV) :
    lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
  barSub_mono V₀ V hV hS.counterex.setting.hyp151.le

theorem s16t_l4_card_lbar (hS : S16tL4Setting D V₀ V L hV) :
    Nat.card ↥(lBar V₀ V hV L) = 20160 := by
  obtain ⟨-, ⟨L₀, -, -, hLn, -⟩, -⟩ := hS.shape
  exact s16c167_card_isLn_four hLn

theorem s16t_l4_card_kbar (hS : S16tL4Setting D V₀ V L hV) :
    Nat.card ↥(kBar D.M V₀ V hV L) = 6 := by
  obtain ⟨⟨e⟩, -⟩ := hS.shape
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem s16t_l4_lbar_simple (hS : S16tL4Setting D V₀ V L hV) : IsSimpleGroup ↥(lBar V₀ V hV L) := by
  obtain ⟨-, ⟨L₀, -, -, hLn, -⟩, -⟩ := hS.shape
  exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hLn

theorem s16t_l4_mbar_direct (hS : S16tL4Setting D V₀ V L hV) :
    IsInternalDirect (kBar D.M V₀ V hV L) (lBar V₀ V hV L) (Mbar D.M V₀ V hV) := by
  obtain ⟨-, ⟨L₀, hdir, hLn₀, -, -⟩, -⟩ := hS.shape
  obtain ⟨hL₀comm, hL₀inf, hL₀sup⟩ := hdir
  have hKcent : kBar D.M V₀ V hV L ≤
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    inf_le_right
  have hKcent₀ : kBar D.M V₀ V hV L ≤
      Subgroup.centralizer (L₀ : Set (MulAut (Vtil V₀ V hV))) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hL₀comm
  have hcomm : ⁅kBar D.M V₀ V hV L, lBar V₀ V hV L⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hKcent
  have hcomm' : ∀ a ∈ kBar D.M V₀ V hV L, ∀ b ∈ lBar V₀ V hV L, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hKcent ha) b hb).symm
  have hcomm₀ : ∀ a ∈ kBar D.M V₀ V hV L, ∀ b ∈ L₀, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hKcent₀ ha) b hb).symm
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := s16t_l4_lbar_simple hS
  have hnotcomm : ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
    intro hc
    haveI : IsMulCommutative ↥(lBar V₀ V hV L) := hc
    have hp : (Nat.card ↥(lBar V₀ V hV L)).Prime :=
      (Group.is_simple_iff_prime_card).mp inferInstance
    rw [s16t_l4_card_lbar hS] at hp
    exact (by norm_num : ¬ Nat.Prime 20160) hp
  have hcenter : Subgroup.center ↥(lBar V₀ V hV L) = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnotcomm
  have hinf : kBar D.M V₀ V hV L ⊓ lBar V₀ V hV L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxcenter : (⟨x, hx.2⟩ : ↥(lBar V₀ V hV L)) ∈
        Subgroup.center ↥(lBar V₀ V hV L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKcent hx.1) y y.2)
    rw [hcenter] at hxcenter
    simpa using hxcenter
  have hle : kBar D.M V₀ V hV L ⊔ lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    sup_le inf_le_left (s16t_l4_lbar_le_mbar hS)
  have hcard : Nat.card ↥(kBar D.M V₀ V hV L ⊔ lBar V₀ V hV L) =
      Nat.card ↥(Mbar D.M V₀ V hV) := by
    rw [s16t_l4_card_sup_of_commute_of_inf_eq_bot hcomm' hinf, s16t_l4_card_kbar hS,
      s16t_l4_card_lbar hS, ← hL₀sup, s16t_l4_card_sup_of_commute_of_inf_eq_bot hcomm₀ hL₀inf,
      s16t_l4_card_kbar hS, s16c167_card_isLn_four hLn₀]
  exact ⟨hcomm, hinf, Subgroup.eq_of_le_of_card_ge hle hcard.ge⟩

theorem s16t_l4_lbar_normal (hS : S16tL4Setting D V₀ V L hV) :
    ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal := by
  obtain ⟨hcomm, -, hsup⟩ := s16t_l4_mbar_direct hS
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (s16t_l4_lbar_le_mbar hS), ← hsup]
  exact sup_le ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
    (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer

theorem s16t_l4_mbar_not_nine (hS : S16tL4Setting D V₀ V L hV) (g : ↥(Mbar D.M V₀ V hV)) :
    ¬ 9 ∣ orderOf g := by
  intro h9
  obtain ⟨-, ⟨L₀, -, -, hLnL, -⟩, -⟩ := hS.shape
  obtain ⟨hcomm, -, hsup⟩ := s16t_l4_mbar_direct hS
  have hKcent : kBar D.M V₀ V hV L ≤
      Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    inf_le_right
  have hcomm' : ∀ a ∈ kBar D.M V₀ V hV L, ∀ b ∈ lBar V₀ V hV L, a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hKcent ha) b hb).symm
  have hg : (g : MulAut (Vtil V₀ V hV)) ∈ kBar D.M V₀ V hV L ⊔ lBar V₀ V hV L := by
    rw [hsup]; exact g.2
  obtain ⟨k, hk, l, hl, hkl⟩ := s16t_l4_exists_mul_of_mem_sup_of_commute hcomm' hg
  have hcommkl : Commute k l := (commute_iff_eq k l).2 (hcomm' k hk l hl)
  have hdvd : orderOf (k * l) ∣ Nat.lcm (orderOf k) (orderOf l) :=
    hcommkl.orderOf_mul_dvd_lcm
  have hk6 : orderOf k ∣ 6 := by
    have h := Subgroup.orderOf_dvd_natCard (kBar D.M V₀ V hV L) hk
    rwa [s16t_l4_card_kbar hS] at h
  obtain ⟨e⟩ :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hLnL
  have hl840 : orderOf l ∣ 840 := by
    have h1 := s16t_l4_perm_fin_eight_orderOf_dvd_840
      ((e ⟨l, hl⟩ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8))
    rwa [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk l hl] at h1
  have hord840 : orderOf (k * l) ∣ 840 :=
    hdvd.trans (Nat.lcm_dvd (hk6.trans (by norm_num)) hl840)
  have h9' : 9 ∣ orderOf (k * l) := by
    simpa [hkl, Subgroup.orderOf_coe] using h9
  exact (by norm_num : ¬ 9 ∣ 840) (h9'.trans hord840)

theorem s16t_l4_le_stabTil (hS : S16tL4Setting D V₀ V L hV) : D.M ≤ stabTil V₀ V :=
  le_stabTil hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer
    hS.counterex.setting.hyp151.hyp125.pairFacts.le_normalizer₀

theorem s16t_l4_lbar_isAlt (hS : S16tL4Setting D V₀ V L hV) : IsAlt ↥(lBar V₀ V hV L) 8 := by
  obtain ⟨-, ⟨L₀, -, -, hLnL, -⟩, -⟩ := hS.shape
  exact CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hLnL

theorem s16t_l4_lbar_not_commutative (hS : S16tL4Setting D V₀ V L hV) :
    ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
  intro hc
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := s16t_l4_lbar_simple hS
  haveI : IsMulCommutative ↥(lBar V₀ V hV L) := hc
  have hp : (Nat.card ↥(lBar V₀ V hV L)).Prime := (Group.is_simple_iff_prime_card).mp inferInstance
  rw [s16t_l4_card_lbar hS] at hp
  exact (by norm_num : ¬ Nat.Prime 20160) hp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
