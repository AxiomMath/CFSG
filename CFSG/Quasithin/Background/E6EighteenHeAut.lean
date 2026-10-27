module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.E6EighteenHeOut

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

section BarHomOn

variable {G : Type} [Group G] {K X : Subgroup G}

@[expose] noncomputable def barHomOn (hX : X ≤ Subgroup.normalizer (K : Set G)) :
    ↥X →* MulAut (Bar.Qbar K) :=
  (Bar.barHom K).comp (Subgroup.inclusion hX)

theorem barHomOn_apply (hX : X ≤ Subgroup.normalizer (K : Set G)) (x : ↥X) :
    barHomOn hX x = Bar.barHom K ⟨x, hX x.2⟩ := rfl

theorem barHomOn_eq_one_iff (hKq : CFSG.IsQuasisimple ↥K)
    (hX : X ≤ Subgroup.normalizer (K : Set G)) (x : ↥X) :
    barHomOn hX x = 1 ↔ (x : G) ∈ Subgroup.centralizer (K : Set G) := by
  rw [barHomOn_apply, Bar.barHom_eq_one_iff hKq.1]
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (h ⟨k, hk⟩).symm
  · intro h k
    exact (Subgroup.mem_centralizer_iff.1 h k k.2).symm

theorem card_range_barHomOn (hKq : CFSG.IsQuasisimple ↥K)
    (hX : X ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (barHomOn hX).range = (X ⊓ Subgroup.centralizer (K : Set G)).relIndex X := by
  have hker : (barHomOn hX).ker = (X ⊓ Subgroup.centralizer (K : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, barHomOn_eq_one_iff hKq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [← Subgroup.index_ker, hker]
  rfl

end BarHomOn

theorem apply_eq_of_conj_comm {S : Type*} [Group S] (hZ : Subgroup.center S = ⊥)
    {σ : MulAut S} {d : S} (h : MulAut.conj d * σ = σ * MulAut.conj d) : σ d = d := by
  apply Id2519.conj_injective_of_center_bot hZ
  rw [← mulAut_mul_conj_mul_inv, ← h, mul_inv_cancel_right]

theorem relIndex_inf_inner_le_two_of_card_outer {S : Type*} [Group S]
    (hOut : Nat.card (Outer S) = 2) (H : Subgroup (MulAut S)) : (H ⊓ inner S).relIndex H ≤ 2 := by
  rw [Subgroup.inf_relIndex_left]
  have h := Subgroup.relIndex_dvd_index_of_normal (inner S) H
  have h2 : (inner S).index = 2 := by
    rw [Subgroup.index_eq_card]
    exact hOut
  rw [h2] at h
  exact Nat.le_of_dvd (by norm_num) h

theorem card_outer_qbar_of_isHeQuot
    {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} (hKq : CFSG.IsQuasisimple ↥K)
    (hHe : IsHeQuot K) : Nat.card (Outer (Bar.Qbar K)) = 2 := by
  obtain ⟨φ⟩ := nonempty_qbar_mulEquiv_he hKq hHe
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (φ.trans CFSG.Sporadic.HeldB.heEquivP)).toEquiv]
  exact CFSG.Sporadic.HeldB.ctbh_full_automorphism_permutation_model.2.2.2.2.1

theorem barHom_eq_one_of_mem_inner
    {G : Type} [Group G] [Finite G] {K L : Subgroup G} (hKq : CFSG.IsQuasisimple ↥K)
    (hHe : IsHeQuot K) (hLK : L ≤ K) (hLq : CFSG.IsQuasisimple ↥L) (hL7 : IsA7Type L)
    (u : ↥(Subgroup.normalizer (K : Set G))) (hu2 : (u : G) * u = 1)
    (huL : ∀ l ∈ L, (u : G) * l = l * u) (hin : Bar.barHom K u ∈ inner (Bar.Qbar K)) :
    Bar.barHom K u = 1 := by
  classical
  obtain ⟨φ⟩ := nonempty_qbar_mulEquiv_he hKq hHe
  have hZ : Subgroup.center (Bar.Qbar K) = ⊥ :=
    CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hKq
  set f : ↥L →* Bar.Qbar K := (QuotientGroup.mk' (Subgroup.center ↥K)).comp
    (Subgroup.inclusion hLK) with hfdef
  have hfker : f.ker ≤ Subgroup.center ↥L := by
    intro l hl
    rw [MonoidHom.mem_ker, hfdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hl
    rw [Subgroup.mem_center_iff] at hl ⊢
    intro m
    apply Subtype.ext
    have := congrArg Subtype.val (hl (Subgroup.inclusion hLK m))
    simpa using this
  have h7 : IsA7Group ↥f.range := IsA7Group.range hLq hL7 f hfker
  obtain ⟨x, hx⟩ := hin
  by_cases hx1 : x = 1
  · rw [← hx, hx1, map_one]
  exfalso
  have huu : Bar.barHom K u * Bar.barHom K u = 1 := by
    rw [← map_mul, show u * u = 1 from Subtype.ext hu2, map_one]
  have hxx : x * x = 1 := by
    apply Id2519.conj_injective_of_center_bot hZ
    rw [map_mul, hx, huu, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two, hxx]) hx1
  have hle : f.range ≤ Subgroup.centralizer ({x} : Set (Bar.Qbar K)) := by
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (u : G) * ((Subgroup.inclusion hLK l : ↥K) : G) =
        ((Subgroup.inclusion hLK l : ↥K) : G) * u := huL l l.2
    have h1 : Bar.barHom K u (f l) = f l := Bar.barHom_mk_of_comm _ _ hcomm
    rw [← hx, MulAut.conj_apply] at h1
    calc f l * x = (x * f l * x⁻¹) * x := by rw [h1]
      _ = x * f l := by group
  exact factHeInnerNoA7_holds (Bar.Qbar K) ⟨φ⟩ x hord f.range hle h7

theorem centralizer_le_normalizer_of_isHeQuot {G : Type} [Group G]
    [Finite G] {A K E : Subgroup G} (hK : IsComponentIn K (Subgroup.centralizer (A : Set G)))
    (hHe : IsHeQuot K) (hEK : E ≤ K) (hE3 : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hrank : CFSG.Open.pRank 3 (Subgroup.centralizer (A : Set G)) ≤ 2) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKq := BenderBranch.isQuasisimple_of_isComponentIn hK
  intro g hg
  have hAg : CFSG.conjugate A g = A :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.2 (Subgroup.centralizer_le_normalizer _ hg)
  have hKg : IsComponentIn (CFSG.conjugate K g) (Subgroup.centralizer (A : Set G)) := by
    have := isComponentIn_conjugate' hK g
    rwa [hAg] at this
  rcases BenderBranch.eq_or_commute_of_isComponentIn hK hKg with heq | hc
  · exact BenderBranch.conjugate_eq_iff_mem_normalizer.1 heq.symm
  exfalso
  have hc' : K ≤ Subgroup.centralizer ((CFSG.conjugate K g : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
  set Eg := CFSG.conjugate E g with hEgdef
  have hEgK : Eg ≤ CFSG.conjugate K g := BenderBranch.conjugate_mono hEK g
  have hEg3 : IsElemAbelian 3 Eg :=
    CFSG.SectionRank.isElemAbelian_map hE3 (MulAut.conj g⁻¹).toMonoidHom
  have hne : ¬ Eg ≤ E := by
    intro hle
    have hEg9 : Nat.card Eg = 9 := by rw [hEgdef, BenderBranch.card_conjugate, hE9]
    obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ Eg, x ≠ 1 := by
      by_contra hall
      push Not at hall
      have h0 : Eg = ⊥ := (Subgroup.eq_bot_iff_forall Eg).2 hall
      rw [h0, Subgroup.card_bot] at hEg9
      omega
    have hxK : x ∈ K := hEK (hle hxE)
    have hxC : x ∈ Subgroup.centralizer (K : Set G) :=
      Subgroup.le_centralizer_iff.1 hc' (hEgK hxE)
    have hz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC y y.2)
    rw [center_eq_pCore_of_isHeQuot hKq hHe] at hz
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥K)) ⟨_, hz⟩
    have h2 : x ^ 2 ^ k = 1 := by
      have := congrArg (fun w : ↥(CFSG.pCore 2 ↥K) => ((w : ↥K) : G)) hk
      simpa using this
    have h3 : x ^ 3 = 1 := hEg3.2 x hxE
    apply hx1
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rw [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).gcd_eq_one] at hd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  have h3 := three_le_pRank_of_commuting_E (p := 3) hc' hK.1 hKg.1 hEK hEgK hE3 hEg3
    (by rw [hE9]; norm_num) hne
  omega

end E6

end CFSG.Quasithin
