module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.ComponentAction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.CoprimeCentralizerTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

private theorem normal_closure_of_conj {G : Type*} [Group G] {s : Set G}
    (h : ∀ g : G, ∀ x ∈ s, g * x * g⁻¹ ∈ s) : (Subgroup.closure s).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  have key : ∀ x ∈ Subgroup.closure s, g * x * g⁻¹ ∈ Subgroup.closure s := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure s)
      ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Subgroup.subset_closure (h g y hy)
    · simp
    · intro a b ha hb ha' hb'
      have h1 : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [h1]
      exact Subgroup.mul_mem _ ha' hb'
    · intro a ha ha'
      have h1 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [h1]
      exact Subgroup.inv_mem _ ha'
  exact key n hn

private theorem normal_le_or_top_of_simple_bar2 {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L]
    (hS : IsSimpleGroup (L ⧸ CFSG.pCore 2 L)) (K : Subgroup L) [hK : K.Normal] :
    K ≤ CFSG.pCore 2 L ∨ K = ⊤ := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (K.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hS.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' (CFSG.pCore 2 L))) with h | h
  · left
    intro k hk
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 L) k ∈
        K.map (QuotientGroup.mk' (CFSG.pCore 2 L)) := Subgroup.mem_map_of_mem _ hk
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · right
    have hsurj : Function.Surjective ((QuotientGroup.mk' K).comp (CFSG.pCore 2 L).subtype) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : QuotientGroup.mk' (CFSG.pCore 2 L) g ∈
          K.map (QuotientGroup.mk' (CFSG.pCore 2 L)) := by rw [h]; trivial
      obtain ⟨k, hkK, hkg⟩ := Subgroup.mem_map.mp hg
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkg
      refine ⟨⟨k⁻¹ * g, hkg⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hK.conj_mem' k hkK g
    have : Group.IsNilpotent (CFSG.pCore 2 L) :=
      (CFSG.pCore_isPGroup (p := 2) (G := L)).isNilpotent
    have : Group.IsNilpotent (L ⧸ K) := Group.nilpotent_of_surjective _ hsurj
    rw [Subgroup.eq_top_iff']
    intro g
    by_contra hg
    have : Nontrivial (L ⧸ K) :=
      ⟨⟨QuotientGroup.mk g, 1, fun h => hg ((QuotientGroup.eq_one_iff g).1 h)⟩⟩
    exact Group.IsPerfect.not_isNilpotent (L ⧸ K) inferInstance

private theorem odd_prime_closure_eq_top {L : Subgroup X} {n : ℕ}
    (hLp : ⁅L, L⁆ = L) (hSz : IsSz (Bar2 L) n) :
    Subgroup.closure {x : ↥L | (orderOf x).Prime ∧ orderOf x ≠ 2} = ⊤ := by
  classical
  let S : Set ↥L := {x | (orderOf x).Prime ∧ orderOf x ≠ 2}
  let N : Subgroup ↥L := Subgroup.closure S
  have hSconj : ∀ g : ↥L, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
    intro g x hx
    have hxconj : IsConj x (g * x * g⁻¹) := by
      rw [isConj_iff]
      exact ⟨g, rfl⟩
    exact ⟨by rw [← hxconj.orderOf_eq]; exact hx.1,
      by rw [← hxconj.orderOf_eq]; exact hx.2⟩
  have hNnormal : N.Normal := by
    refine normal_closure_of_conj ?_
    intro g x hx
    exact hSconj g x hx
  have hSsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5dvd : 5 ∣ Nat.card (Bar2 L) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.five_dvd_card_of_isSz hSz
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Bar2 L) 5 h5dvd
  have h5not : ¬ 5 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hk]
    intro h
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five h
    have hEq : 5 = 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_two).mp h52
    norm_num at hEq
  obtain ⟨x, hxord, hxq⟩ :=
    CFSG.GroupTheory.CoprimeTransport.exists_orderOf_eq_prime_mk_eq
      (N := CFSG.pCore 2 ↥L) h5not hy
  have hxS : x ∈ S := ⟨by rw [hxord]; exact Nat.prime_five, by rw [hxord]; norm_num⟩
  have hxN : x ∈ N := Subgroup.subset_closure hxS
  have hqne : QuotientGroup.mk' (CFSG.pCore 2 ↥L) x ≠ 1 := by
    intro h
    rw [hxq] at h
    have h1 : orderOf y = 1 := by rw [h]; simp
    omega
  have hnotle : ¬ N ≤ CFSG.pCore 2 ↥L := by
    intro hle
    refine hqne ?_
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hle hxN
  have : N.Normal := hNnormal
  rcases normal_le_or_top_of_simple_bar2 hSsimple N with hle | htop
  · exact absurd hle hnotle
  · exact htop

private noncomputable def conjAct (C : Subgroup X) : ↥C →* MulAut ↥C :=
  C.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.le_normalizer))

private noncomputable def conjActOf (C L : Subgroup X) (hLC : L ≤ normalizer (C : Set X)) :
    ↥L →* MulAut ↥C :=
  C.normalizerMonoidHom.comp (Subgroup.inclusion hLC)

private noncomputable def inducerSubgroup (C L : Subgroup X) (hLC : L ≤ normalizer (C : Set X)) :
    Subgroup ↥C :=
  (conjActOf C L hLC).range.comap (conjAct C)

omit [Finite X] in
private lemma conjAct_apply (C : Subgroup X) (g x : ↥C) :
    ((conjAct C g x : ↥C) : X) = (g : X) * (x : X) * (g : X)⁻¹ := rfl

omit [Finite X] in
private lemma conjActOf_apply (C L : Subgroup X) (hLC : L ≤ normalizer (C : Set X))
    (l : ↥L) (x : ↥C) :
    ((conjActOf C L hLC l x : ↥C) : X) = (l : X) * (x : X) * (l : X)⁻¹ := rfl

omit [Finite X] in
private theorem inducer_mem_normalizer {C L : Subgroup X} {a c : X}
    (haL : a ∈ L) (ha : (orderOf a).Prime) (ha2 : orderOf a ≠ 2)
    (hcC : c ∈ C)
    (hac : ∀ x ∈ C, a * x * a⁻¹ = c * x * c⁻¹)
    (hstar : ∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set X) ≤ normalizer (L : Set X)) :
    c ∈ normalizer (L : Set X) := by
  have hcentral : c⁻¹ * a ∈ Subgroup.centralizer (C : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : a * x * a⁻¹ = c * x * c⁻¹ := hac x hx
    have h2 : (c⁻¹ * a) * x * (c⁻¹ * a)⁻¹ = x := by
      rw [show (c⁻¹ * a)⁻¹ = a⁻¹ * c by group]
      calc
        c⁻¹ * a * x * (a⁻¹ * c) = c⁻¹ * (a * x * a⁻¹) * c := by group
        _ = c⁻¹ * (c * x * c⁻¹) * c := by rw [h1]
        _ = x := by group
    have h3 : (c⁻¹ * a) * x = x * (c⁻¹ * a) := by
      have := congrArg (fun t => t * (c⁻¹ * a)) h2
      simpa [mul_assoc] using this
    exact h3.symm
  have hca : Commute (c⁻¹ * a) c :=
    (Subgroup.mem_centralizer_iff.mp hcentral c hcC).symm
  have hca_a : c * a = a * c := by
    have h := hca.eq
    have h' : c⁻¹ * a * c = a := by
      calc c⁻¹ * a * c = c * (c⁻¹ * a) := h
        _ = a := by group
    have h2 : a * c = c * a := by
      calc a * c = c * (c⁻¹ * a * c) := by group
        _ = c * a := by rw [h']
    exact h2.symm
  have hcz : c ∈ Subgroup.centralizer (Subgroup.zpowers a : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute a c from hca_a.symm).zpow_left k).eq
  have hle := hstar (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haL)
    (by rw [Nat.card_zpowers]; exact ha)
    (by rw [Nat.card_zpowers]; exact ha2)
  exact hle (Subgroup.centralizer_le_normalizer (Subgroup.zpowers a : Set X) hcz)

omit [Finite X] in
private theorem conjAct_range_le {C L : Subgroup X} (hLC : L ≤ normalizer (C : Set X))
    (hinner : ∀ l ∈ L, ∃ c ∈ C, ∀ x ∈ C, l * x * l⁻¹ = c * x * c⁻¹) :
    (conjActOf C L hLC).range ≤ (conjAct C).range := by
  rintro _ ⟨l, rfl⟩
  obtain ⟨c, hcC, hcy⟩ := hinner l l.2
  refine ⟨⟨c, hcC⟩, ?_⟩
  ext x
  exact (hcy x x.2).symm

omit [Finite X] in
private theorem center_le_inducer {C L : Subgroup X} (hLC : L ≤ normalizer (C : Set X)) :
    Subgroup.center ↥C ≤ inducerSubgroup C L hLC := by
  intro z hz
  rw [inducerSubgroup, Subgroup.mem_comap]
  refine ⟨1, ?_⟩
  ext x
  rw [conjActOf_apply, conjAct_apply]
  simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
  have hzx : (x : X) * (z : X) = (z : X) * (x : X) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz x)
  rw [← hzx]
  group


private theorem center_le_normalizer_of_inner {C L : Subgroup X} {n : ℕ}
    (hLp : ⁅L, L⁆ = L) (hSz : IsSz (Bar2 L) n)
    (hinner : ∀ l ∈ L, ∃ c ∈ C, ∀ x ∈ C, l * x * l⁻¹ = c * x * c⁻¹) :
    (Subgroup.center ↥C).map C.subtype ≤ normalizer (L : Set X) := by
  let S₀ : Set ↥L := {x | (orderOf x).Prime ∧ orderOf x ≠ 2}
  have hgen : Subgroup.closure S₀ = ⊤ := odd_prime_closure_eq_top hLp hSz
  intro z hz
  obtain ⟨z', hz'center, rfl⟩ := Subgroup.mem_map.mp hz
  have hcomm_gen : ∀ a ∈ S₀, Commute (z' : X) (a : X) := by
    intro a ha
    obtain ⟨c, hcC, hcy⟩ := hinner (a : X) a.2
    have hzc : (z' : X) * c = c * (z' : X) :=
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'center ⟨c, hcC⟩)).symm
    have haz : (a : X) * (z' : X) * (a : X)⁻¹ = (z' : X) := by
      rw [hcy (z' : X) z'.2]
      rw [← hzc]
      group
    have h1 : (a : X) * (z' : X) = (z' : X) * (a : X) := by
      have := congrArg (fun t => t * (a : X)) haz
      simpa [mul_assoc] using this
    exact h1.symm
  have hzcentral : (z' : X) ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    let l' : ↥L := ⟨l, hl⟩
    have hl' : l' ∈ Subgroup.closure S₀ := by rw [hgen]; trivial
    have hcommL : ∀ y : ↥L, y ∈ Subgroup.closure S₀ →
        (z' : X) * (y : X) = (y : X) * (z' : X) := by
      intro y hy
      refine Subgroup.closure_induction (G := ↥L)
        (p := fun y _ => (z' : X) * (y : X) = (y : X) * (z' : X)) ?_ ?_ ?_ ?_ hy
      · intro a ha
        exact (hcomm_gen a ha).eq
      · simp
      · intro a b ha hb ha' hb'
        change (z' : X) * ((a : X) * (b : X)) = ((a : X) * (b : X)) * (z' : X)
        calc (z' : X) * ((a : X) * (b : X)) = ((z' : X) * (a : X)) * (b : X) := by group
          _ = ((a : X) * (z' : X)) * (b : X) := by rw [ha']
          _ = (a : X) * ((z' : X) * (b : X)) := by group
          _ = (a : X) * ((b : X) * (z' : X)) := by rw [hb']
          _ = ((a : X) * (b : X)) * (z' : X) := by group
      · intro a ha ha'
        have hcomm : Commute (z' : X) (a : X) := ha'
        change (z' : X) * ((a : X)⁻¹) = ((a : X)⁻¹) * (z' : X)
        exact hcomm.inv_right.eq
    exact (hcommL l' hl').symm
  exact Subgroup.centralizer_le_normalizer (L : Set X) hzcentral

private theorem inducerSubgroup_le_normalizer {C L : Subgroup X} {n : ℕ}
    (hLp : ⁅L, L⁆ = L) (hSz : IsSz (Bar2 L) n)
    (hLC : L ≤ normalizer (C : Set X))
    (hinner : ∀ l ∈ L, ∃ c ∈ C, ∀ x ∈ C, l * x * l⁻¹ = c * x * c⁻¹)
    (hstar : ∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set X) ≤ normalizer (L : Set X)) :
    (inducerSubgroup C L hLC).map C.subtype ≤ normalizer (L : Set X) := by
  classical
  let S₀ : Set ↥L := {a | (orderOf a).Prime ∧ orderOf a ≠ 2}
  have hgen : Subgroup.closure S₀ = ⊤ := odd_prime_closure_eq_top hLp hSz
  let cfun : ↥L → ↥C := fun a =>
    if ha : a ∈ S₀ then
      ⟨Classical.choose (hinner (a : X) a.2),
       (Classical.choose_spec (hinner (a : X) a.2)).1⟩
    else 1
  have hcfun_spec : ∀ a ∈ S₀, cfun a =
      ⟨Classical.choose (hinner (a : X) a.2),
       (Classical.choose_spec (hinner (a : X) a.2)).1⟩ := by
    intro a ha
    simp only [cfun, dif_pos ha]
  have hc_ind : ∀ a ∈ S₀, conjAct C (cfun a) = conjActOf C L hLC a := by
    intro a ha
    rw [hcfun_spec a ha]
    ext x
    exact ((Classical.choose_spec (hinner (a : X) a.2)).2 x x.2).symm
  have hcN : ∀ a ∈ S₀, ((cfun a : ↥C) : X) ∈ normalizer (L : Set X) := by
    intro a ha
    have haX : (a : X) ∈ L := a.2
    have hmem : ((cfun a : ↥C) : X) ∈ C := (cfun a).2
    have hac : ∀ x ∈ C, (a : X) * x * (a : X)⁻¹ =
        ((cfun a : ↥C) : X) * x * ((cfun a : ↥C) : X)⁻¹ := by
      intro x hx
      have h := (Classical.choose_spec (hinner (a : X) a.2)).2 x hx
      rw [hcfun_spec a ha]
      exact h
    have haord : orderOf (a : X) = orderOf a := Subgroup.orderOf_coe a
    exact inducer_mem_normalizer haX (by rw [haord]; exact ha.1)
      (by rw [haord]; exact ha.2) hmem hac hstar
  set P₀ : Subgroup ↥C := Subgroup.closure (cfun '' S₀) with hP₀
  have hP₀N : P₀.map C.subtype ≤ normalizer (L : Set X) := by
    rw [hP₀, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact hcN a ha
  have hset : conjAct C '' (cfun '' S₀) = (conjActOf C L hLC) '' S₀ := by
    ext y
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, hb, (hc_ind b hb).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨cfun a, ⟨a, ha, rfl⟩, hc_ind a ha⟩
  have hP₀_range : P₀.map (conjAct C) = (conjActOf C L hLC).range := by
    calc
      P₀.map (conjAct C) = Subgroup.closure (conjAct C '' (cfun '' S₀)) := by
        rw [hP₀, MonoidHom.map_closure]
      _ = Subgroup.closure ((conjActOf C L hLC) '' S₀) := by rw [hset]
      _ = (Subgroup.closure S₀).map (conjActOf C L hLC) :=
        (MonoidHom.map_closure _ S₀).symm
      _ = (⊤ : Subgroup ↥L).map (conjActOf C L hLC) := by rw [hgen]
      _ = (conjActOf C L hLC).range := (MonoidHom.range_eq_map _).symm
  have hP_le : inducerSubgroup C L hLC ≤ P₀ ⊔ Subgroup.center ↥C := by
    intro p hp
    have hp' : conjAct C p ∈ (conjActOf C L hLC).range := by
      rw [inducerSubgroup, Subgroup.mem_comap] at hp
      exact hp
    rw [← hP₀_range] at hp'
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.mp hp'
    have hz : q⁻¹ * p ∈ Subgroup.center ↥C := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hψ : conjAct C (q⁻¹ * p) = 1 := by
        rw [map_mul, map_inv, hqp, inv_mul_cancel]
      have hconj : (q⁻¹ * p) * y * (q⁻¹ * p)⁻¹ = y := by
        apply Subtype.ext
        have h1 : ((conjAct C (q⁻¹ * p)) y : X) = (y : X) := by
          simpa using congrArg Subtype.val
            (congrArg (fun f : MulAut ↥C => (f y : ↥C)) hψ)
        rw [conjAct_apply] at h1
        exact h1
      have hcomm : (q⁻¹ * p) * y = y * (q⁻¹ * p) := by
        have := congrArg (fun t => t * (q⁻¹ * p)) hconj
        simpa [mul_assoc] using this
      exact hcomm.symm
    have hp_eq : p = q * (q⁻¹ * p) := by group
    rw [hp_eq]
    exact Subgroup.mul_mem_sup hq hz
  have hmap_le : (inducerSubgroup C L hLC).map C.subtype ≤
      (P₀ ⊔ Subgroup.center ↥C).map C.subtype := Subgroup.map_mono hP_le
  refine hmap_le.trans ?_
  rw [Subgroup.map_sup]
  exact sup_le hP₀N (center_le_normalizer_of_inner hLp hSz hinner)



omit [Finite X] in
private theorem conjAct_ker (C : Subgroup X) :
    (conjAct C).ker = Subgroup.center ↥C := by
  ext z
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
  constructor
  · intro hz y
    have h1 : ((conjAct C z) y : X) = (y : X) := by
      simpa using congrArg Subtype.val (congrArg (fun f : MulAut ↥C => (f y : ↥C)) hz)
    rw [conjAct_apply] at h1
    have h2 : (y : X) * (z : X) = (z : X) * (y : X) := by
      have h3 : (z : X) * (y : X) = (y : X) * (z : X) := by
        have := congrArg (fun t => t * (z : X)) h1
        simpa [mul_assoc] using this
      exact h3.symm
    exact Subtype.ext h2
  · intro hz
    ext y
    rw [conjAct_apply]
    simp only [MulAut.one_apply]
    have h := congrArg Subtype.val (hz y)
    have h2 : (y : X) * (z : X) = (z : X) * (y : X) := h
    have h3 : (z : X) * (y : X) * (z : X)⁻¹ = (y : X) := by
      rw [← h2]
      group
    exact h3



omit [Finite X] in
private theorem inducer_commutator_facts {C L : Subgroup X}
    (hLp : ⁅L, L⁆ = L)
    (hLC : L ≤ normalizer (C : Set X))
    (hinner : ∀ l ∈ L, ∃ c ∈ C, ∀ x ∈ C, l * x * l⁻¹ = c * x * c⁻¹) :
    (inducerSubgroup C L hLC =
        ⁅inducerSubgroup C L hLC, inducerSubgroup C L hLC⁆ ⊔ Subgroup.center ↥C) ∧
      (⁅inducerSubgroup C L hLC, inducerSubgroup C L hLC⁆ =
        ⁅⁅inducerSubgroup C L hLC, inducerSubgroup C L hLC⁆,
          ⁅inducerSubgroup C L hLC, inducerSubgroup C L hLC⁆⁆) := by
  let P := inducerSubgroup C L hLC
  let Z := Subgroup.center ↥C
  let S := ⁅P, P⁆
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hP_range : P.map (conjAct C) = (conjActOf C L hLC).range := by
    rw [show P = (conjActOf C L hLC).range.comap (conjAct C) from rfl,
      Subgroup.map_comap_eq]
    exact inf_eq_right.mpr (conjAct_range_le hLC hinner)
  have hZP : Z ≤ P := center_le_inducer hLC
  let π : ↥C →* (↥C ⧸ Z) := QuotientGroup.mk' Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  let ψP : P →* MulAut ↥C := (conjAct C).comp P.subtype
  have hψP_ker : ψP.ker = Z.subgroupOf P := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ψP x = 1 ↔ (x : ↥C) ∈ Subgroup.center ↥C
    rw [← conjAct_ker C, MonoidHom.mem_ker]
    exact Iff.rfl
  have hψP_range : ψP.range = (conjActOf C L hLC).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hP_range
  have hφrange_perf : Group.IsPerfect ↥(conjActOf C L hLC).range :=
    Group.IsPerfect.range (conjActOf C L hLC)
  have hPZ_perf : Group.IsPerfect (P ⧸ Z.subgroupOf P) := by
    have e : P ⧸ Z.subgroupOf P ≃* ↥(conjActOf C L hLC).range :=
      (QuotientGroup.quotientMulEquivOfEq hψP_ker).symm.trans
        ((QuotientGroup.quotientKerEquivRange ψP).trans
          (MulEquiv.subgroupCongr hψP_range))
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) (fun y => e.symm.surjective y)
  let πP : P →* (↥C ⧸ Z) := π.comp P.subtype
  have hπP_ker : πP.ker = Z.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  have hπP_range : πP.range = P.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hPπ_perf : Group.IsPerfect ↥(P.map π) := by
    have : Group.IsPerfect (P ⧸ Z.subgroupOf P) := hPZ_perf
    have e : P ⧸ Z.subgroupOf P ≃* ↥(P.map π) :=
      (QuotientGroup.quotientMulEquivOfEq hπP_ker).symm.trans
        ((QuotientGroup.quotientKerEquivRange πP).trans
          (MulEquiv.subgroupCongr hπP_range))
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) (fun y => e.surjective y)
  have hSmap : S.map π = P.map π := by
    have : Group.IsPerfect ↥(P.map π) := hPπ_perf
    calc
      S.map π = ⁅P,P⁆.map π := rfl
      _ = ⁅P.map π, P.map π⁆ := Subgroup.map_commutator P P π
      _ = P.map π := Subgroup.commutator_eq_self
  have hP_eq : P = S ⊔ Z := by
    have h1 : Subgroup.comap π (S.map π) = S ⊔ Z := by
      rw [Subgroup.comap_map_eq, hπker]
    have h2 : Subgroup.comap π (P.map π) = P := by
      rw [Subgroup.comap_map_eq, hπker]
      exact sup_eq_left.mpr hZP
    rw [← h1, hSmap, h2]
  have hSS : S = ⁅S,S⁆ := by
    have hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, Commute z z' := by
      intro z hz z' hz'
      exact (Subgroup.mem_center_iff.mp hz z').symm
    have hZS : ∀ z ∈ Z, ∀ s ∈ S, Commute z s := by
      intro z hz s hs
      exact (Subgroup.mem_center_iff.mp hz s).symm
    have hle : S ≤ ⁅S,S⁆ := by
      have hcomm := CFSG.commutator_sup_le_commutator_right (A := Z) (B := S) hZZ hZS
      have hP' : Z ⊔ S = P := by rw [sup_comm, hP_eq]
      rw [hP'] at hcomm
      rwa [← show S = ⁅P,P⁆ from rfl] at hcomm
    exact le_antisymm hle (Subgroup.commutator_le_self S)
  exact ⟨hP_eq, hSS⟩

theorem le_of_inner {C L : Subgroup X} {n : ℕ}
    (hLp : ⁅L, L⁆ = L) (hSz : IsSz (Bar2 L) n)
    (hLC : L ≤ normalizer (C : Set X))
    (hinner : ∀ l ∈ L, ∃ c ∈ C, ∀ x ∈ C, l * x * l⁻¹ = c * x * c⁻¹)
    (hnc : ¬ L ≤ centralizer (C : Set X))
    (hstar : ∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set X) ≤ normalizer (L : Set X)) :
    L ≤ C := by
  classical
  set P : Subgroup ↥C := inducerSubgroup C L hLC with hP
  set Z : Subgroup ↥C := Subgroup.center ↥C with hZ
  set S : Subgroup ↥C := ⁅P, P⁆ with hS
  have hPN : P.map C.subtype ≤ normalizer (L : Set X) := by
    rw [hP]
    exact inducerSubgroup_le_normalizer hLp hSz hLC hinner hstar
  obtain ⟨hP_eq0, hSS0⟩ := inducer_commutator_facts hLp hLC hinner
  have hP_eq : P = S ⊔ Z := by
    rw [hP, hZ, hS]
    exact hP_eq0
  have hSS : S = ⁅S, S⁆ := by
    rw [hS, hP]
    exact hSS0
  set SX : Subgroup X := S.map C.subtype with hSX
  have hSX_perf : ⁅SX, SX⁆ = SX := by
    change ⁅S.map C.subtype, S.map C.subtype⁆ = S.map C.subtype
    rw [← Subgroup.map_commutator, ← hSS]
  have hSX_N : SX ≤ normalizer (L : Set X) :=
    (Subgroup.map_mono (Subgroup.commutator_le_self P)).trans hPN
  have hcomm_le : ⁅SX, SX⁆ ≤ ⁅SX, L⁆ := by
    rw [Subgroup.commutator_le]
    intro s1 hs1 s2 hs2
    obtain ⟨t1, ht1, rfl⟩ := Subgroup.mem_map.mp hs1
    obtain ⟨t2, ht2, rfl⟩ := Subgroup.mem_map.mp hs2
    have ht2P : t2 ∈ P := Subgroup.commutator_le_self P ht2
    obtain ⟨l2, hl2ψ⟩ := MonoidHom.mem_range.mp (Subgroup.mem_comap.mp ht2P)
    have hl2L : (l2 : X) ∈ L := l2.2
    have hval : l2 * (t1 : X) * l2⁻¹ = (t2 : X) * (t1 : X) * (t2 : X)⁻¹ := by
      have h := congrArg (fun f : MulAut ↥C => (f t1 : ↥C)) hl2ψ
      exact congrArg Subtype.val h
    have hinv : l2 * (t1 : X)⁻¹ * l2⁻¹ =
        (t2 : X) * (t1 : X)⁻¹ * (t2 : X)⁻¹ := by
      have h := congrArg (fun x : X => x⁻¹) hval
      simpa [mul_assoc] using h
    have hcomm_eq : ⁅(t1 : X), (t2 : X)⁆ = ⁅(t1 : X), (l2 : X)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have h1 : (t2 : X) * (t1 : X)⁻¹ * (t2 : X)⁻¹ =
          (l2 : X) * (t1 : X)⁻¹ * (l2 : X)⁻¹ := by
        simpa using hinv.symm
      calc
        (t1 : X) * (t2 : X) * (t1 : X)⁻¹ * (t2 : X)⁻¹
            = (t1 : X) * ((t2 : X) * (t1 : X)⁻¹ * (t2 : X)⁻¹) := by group
        _ = (t1 : X) * ((l2 : X) * (t1 : X)⁻¹ * (l2 : X)⁻¹) := by rw [h1]
        _ = (t1 : X) * (l2 : X) * (t1 : X)⁻¹ * (l2 : X)⁻¹ := by group
    change ⁅(t1 : X), (t2 : X)⁆ ∈ ⁅SX, L⁆
    rw [hcomm_eq]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_map_of_mem C.subtype ht1) hl2L
  have hSL_le_L : ⁅SX, L⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro s hs l hl
    have hsN : s ∈ normalizer (L : Set X) := hSX_N hs
    have hsl : s * l * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsN l).mp hl
    exact L.mul_mem hsl (L.inv_mem hl)
  have hSX_le_L : SX ≤ L := by
    calc SX = ⁅SX, SX⁆ := hSX_perf.symm
      _ ≤ ⁅SX, L⁆ := hcomm_le
      _ ≤ L := hSL_le_L
  have hSX_ne_bot : SX ≠ ⊥ := by
    intro hbot
    have hSbot : S = ⊥ := by
      have hmapbot : S.map C.subtype = ⊥ := hbot
      rw [Subgroup.map_eq_bot_iff] at hmapbot
      have hle : S ≤ ⊥ := by simpa using hmapbot
      exact le_bot_iff.mp hle
    have hPZ : P = Z := by
      rw [hP_eq, hSbot, bot_sup_eq]
    have hLcentral : L ≤ centralizer (C : Set X) := by
      intro l hl
      obtain ⟨c, hcC, hcy⟩ := hinner l hl
      have hcP : (⟨c, hcC⟩ : ↥C) ∈ P := by
        change (⟨c, hcC⟩ : ↥C) ∈ (conjActOf C L hLC).range.comap (conjAct C)
        rw [Subgroup.mem_comap]
        refine MonoidHom.mem_range.mpr ⟨⟨l, hl⟩, ?_⟩
        ext x
        exact hcy x x.2
      have hcZ : (⟨c, hcC⟩ : ↥C) ∈ Z := hPZ ▸ hcP
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hcx : (⟨c, hcC⟩ : ↥C) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨c, hcC⟩ :=
        (Subgroup.mem_center_iff.mp hcZ ⟨x, hx⟩).symm
      have hcx' : c * x = x * c := congrArg Subtype.val hcx
      have h1 : l * x * l⁻¹ = x := by
        rw [hcy x hx, hcx']
        group
      have h2 : l * x = x * l := by
        have := congrArg (fun t => t * l) h1
        simpa [mul_assoc] using this
      exact h2.symm
    exact hnc hLcentral
  have hSX_normal : (SX.subgroupOf L).Normal := by
    refine Subgroup.Normal.mk ?_
    intro s hs l
    have hsSX : (s : X) ∈ SX := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨t, htS, hts⟩ := Subgroup.mem_map.mp hsSX
    obtain ⟨p, hpC, hlp⟩ := hinner (l : X) l.2
    have hpP : (⟨p, hpC⟩ : ↥C) ∈ P := by
      change (⟨p, hpC⟩ : ↥C) ∈ (conjActOf C L hLC).range.comap (conjAct C)
      rw [Subgroup.mem_comap]
      refine MonoidHom.mem_range.mpr ⟨l, ?_⟩
      ext x
      exact hlp x x.2
    have hp_normS : (⟨p, hpC⟩ : ↥C) ∈ Subgroup.normalizer (S : Set ↥C) := by
      rw [hS]
      exact Subgroup.normalizer_commutator_ge_left P P hpP
    have hpt : (⟨p, hpC⟩ : ↥C) * t * (⟨p, hpC⟩ : ↥C)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp hp_normS t).mp htS
    rw [Subgroup.mem_subgroupOf]
    change (l : X) * (s : X) * (l : X)⁻¹ ∈ SX
    rw [← hts]
    change (l : X) * (t : X) * (l : X)⁻¹ ∈ SX
    rw [hlp (t : X) t.2]
    exact Subgroup.mem_map.mpr ⟨_, hpt, rfl⟩
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hSsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz
  have : (SX.subgroupOf L).Normal := hSX_normal
  rcases normal_le_or_top_of_simple_bar2 hSsimple (SX.subgroupOf L) with hle | htop
  · exfalso
    have hKne : SX.subgroupOf L ≠ ⊥ := by
      intro hbot
      apply hSX_ne_bot
      apply le_antisymm _ bot_le
      intro x hx
      have hxK : (⟨x, hSX_le_L hx⟩ : ↥L) ∈ SX.subgroupOf L :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot] at hxK
      exact Subgroup.mem_bot.mpr (by
        simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hxK))
    have hKp : IsPGroup 2 (SX.subgroupOf L) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).to_le hle
    have : Nontrivial ↥(SX.subgroupOf L) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hKne
    have hKperf : Group.IsPerfect ↥(SX.subgroupOf L) := by
      have e : ↥(SX.subgroupOf L) ≃* ↥SX := Subgroup.subgroupOfEquivOfLe hSX_le_L
      have : Group.IsPerfect ↥SX := Subgroup.isPerfect_iff.mpr hSX_perf
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
        (fun y => e.symm.surjective y)
    have : Group.IsPerfect ↥(SX.subgroupOf L) := hKperf
    exact Group.IsPerfect.not_isNilpotent ↥(SX.subgroupOf L) hKp.isNilpotent
  · have hSX_eq_L : SX = L := by
      apply le_antisymm hSX_le_L
      intro x hx
      have : (⟨x, hx⟩ : ↥L) ∈ SX.subgroupOf L := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    intro l hl
    have hlSX : l ∈ SX := by rw [hSX_eq_L]; exact hl
    exact Subgroup.map_subtype_le S hlSX

theorem exists_component_le (hKSch : UCK.KSch) (hK : CFSG.Open.IsKGroup X)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (hO2 : CFSG.pCore 2 X = ⊥) {L : Subgroup X} {n : ℕ} (hLp : ⁅L, L⁆ = L)
    (hSz : IsSz (Bar2 L) n) (hLO : ⁅L, CFSG.oddCore X⁆ = ⊥)
    (hstar : ∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set X) ≤ normalizer (L : Set X)) :
    ∃ K : Subgroup X, CFSG.Open.IsQuasisimple ↥K ∧ CFSG.Open.IsSubnormal K ⊤ ∧ L ≤ K := by
  obtain ⟨C, hCq, hCs, hLC, hinner, hnc⟩ := exists_component_inner hKSch hK hp hO2 hLp hSz hLO
  exact ⟨C, hCq, hCs, le_of_inner hLp hSz hLC hinner hnc hstar⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
