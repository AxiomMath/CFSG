module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Members
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3M23
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2bH
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.Quasithin.EmptyFaithful.S1421QA25Orb
public import CFSG.Quasithin.EmptyFaithful.S1421QA25Rows
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151ZC
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch1EightFourChar2

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

namespace QA25

section General

variable {Y : Type} [Group Y]

theorem isSubnormal_eq_bot_or_eq_of_simple {K : Subgroup Y} (hK : IsSimpleGroup ↥K) {L : Subgroup Y}
    (h : IsSubnormal L K) : L = ⊥ ∨ L = K :=
  h.eq_bot_or_eq_of_isSimpleGroup hK

theorem mem_cComp_self_of_simple {K : Subgroup Y} (hK : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) : K ∈ cComp K := by
  obtain ⟨a, b, hab⟩ := hnab
  have hbot : K ≠ ⊥ := by
    intro h
    apply hab
    have ha : (a : Y) = 1 := (Subgroup.mem_bot.mp (h ▸ a.2))
    exact Subtype.ext (by simp [ha])
  have hperf : ⁅K, K⁆ = K := by
    have h1 : commutator ↥K = ⊤ := by
      rcases (inferInstance : (commutator ↥K).Normal).eq_bot_or_eq_top with h | h
      · exfalso
        apply hab
        have : ⁅a, b⁆ ∈ commutator ↥K :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot] at this
        exact commutatorElement_eq_one_iff_mul_comm.mp this
      · exact h
    exact Subgroup.isPerfect_iff.mp ⟨h1⟩
  refine ⟨hbot, hperf, IsSubnormal.refl K, ?_⟩
  intro K' hlt hne hperf' hsub
  rcases isSubnormal_eq_bot_or_eq_of_simple hK hsub with h | h
  · exact hne h
  · exact hlt.ne h

theorem card_sup_mul_card_inf [Finite Y] {S A : Subgroup Y}
    (h : S ≤ Subgroup.normalizer (A : Set Y)) :
    Nat.card ↥(S ⊔ A) * Nat.card ↥(A ⊓ S) = Nat.card ↥A * Nat.card ↥S := by
  have hn1 : (A.subgroupOf S).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
  have hn2 : (A.subgroupOf (S ⊔ A)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have hr : A.relIndex (S ⊔ A) = A.relIndex S :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient S A h).toEquiv.symm
  have e1 := Subgroup.relIndex_mul_card A (S ⊔ A)
  have e2 := Subgroup.relIndex_mul_card A S
  rw [inf_eq_left.mpr le_sup_right] at e1
  calc Nat.card ↥(S ⊔ A) * Nat.card ↥(A ⊓ S)
      = (A.relIndex (S ⊔ A) * Nat.card ↥A) * Nat.card ↥(A ⊓ S) := by rw [e1]
    _ = Nat.card ↥A * (A.relIndex S * Nat.card ↥(A ⊓ S)) := by rw [hr]; ring
    _ = Nat.card ↥A * Nat.card ↥S := by rw [e2]

theorem isSylowTwoOf_inf_of_le_normalizer [Finite Y] {S A : Subgroup Y} (hS : IsSylowTwoOf S ⊤)
    (h : S ≤ Subgroup.normalizer (A : Set Y)) : IsSylowTwoOf (S ⊓ A) A := by
  have hH : IsSylowTwoOf S (A ⊔ S) := by
    refine ⟨le_sup_right, hS.2.1, fun hd => hS.2.2 ?_⟩
    have h2 : S.relIndex (A ⊔ S) ∣ S.index := Subgroup.relIndex_dvd_index_of_le le_sup_right
    have h3 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
    rw [h3]
    exact hd.trans h2
  have hsub : IsSubnormal A (A ⊔ S) :=
    A3.subnormal_of_normal le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer h))
  exact L246C127.isSylowTwoOf_inf_of_isSubnormal' hsub hH

end General

section PairStab

open scoped Pointwise

variable {G Ω : Type} [Group G] [MulAction G Ω] [DecidableEq Ω]

theorem mem_stabilizer_pair_iff {p q : Ω} {g : G} :
    g ∈ MulAction.stabilizer G ({p, q} : Finset Ω) ↔
      (g • p = p ∨ g • p = q) ∧ (g • q = p ∨ g • q = q) := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h1 : g • p ∈ g • ({p, q} : Finset Ω) := Finset.smul_mem_smul_finset (by simp)
    have h2 : g • q ∈ g • ({p, q} : Finset Ω) := Finset.smul_mem_smul_finset (by simp)
    rw [h] at h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl <;> assumption
    · rw [Finset.card_smul_finset]

theorem le_fixingSubgroup_pair_of_simple [Finite G] {p q : Ω} (hpq : p ≠ q) {A : Subgroup G}
    (hA : IsSimpleGroup ↥A) (hcard : 2 < Nat.card ↥A)
    (hle : A ≤ MulAction.stabilizer G ({p, q} : Finset Ω)) :
    A ≤ fixingSubgroup G ({p, q} : Set Ω) := by
  have hmem : ∀ a : ↥A, (a : G) • p = p ∨ (a : G) • p = q := fun a =>
    (mem_stabilizer_pair_iff.mp (hle a.2)).1
  have hmem' : ∀ a : ↥A, (a : G) • q = p ∨ (a : G) • q = q := fun a =>
    (mem_stabilizer_pair_iff.mp (hle a.2)).2
  have hfp : ∀ a : ↥A, (a : G) • p = p := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a₀, ha₀⟩ := hcon
    have ha₀q : (a₀ : G) • p = q := (hmem a₀).resolve_left ha₀
    have horb : MulAction.orbit ↥A p = {p, q} := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact hmem a
      · intro hy
        rcases hy with rfl | hy
        · exact MulAction.mem_orbit_self _
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact ⟨a₀, ha₀q⟩
    have hidx : (MulAction.stabilizer ↥A p).index = 2 := by
      rw [MulAction.index_stabilizer, horb, Set.ncard_pair hpq]
    have hnorm := Subgroup.normal_of_index_eq_two hidx
    have := hA
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.stabilizer ↥A p) with h | h
    · rw [h, Subgroup.index_bot] at hidx
      omega
    · rw [h, Subgroup.index_top] at hidx
      omega
  have hfq : ∀ a : ↥A, (a : G) • q = q := by
    intro a
    rcases hmem' a with h | h
    · exact absurd (MulAction.injective (a : G) (h.trans (hfp a).symm)) hpq.symm
    · exact h
  intro g hg
  exact mem_fixingSubgroup_pair.mpr ⟨hfp ⟨g, hg⟩, hfq ⟨g, hg⟩⟩

end PairStab

section M23

open CFSG.QuasithinUnique.A5.G3.M23 CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312M23
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H.MathieuLat
open scoped Pointwise

abbrev Gm : Type := ↥CFSG.Blueprint.NativeSporadic.M23

theorem img_wordTabA {tabs : Array (Array ℕ)} {n : ℕ} {w : List ℕ} {p : ℕ} (hp : p < n) :
    img (wordTabA tabs n w) p = wordImg tabs w p := by
  simp [img, wordTabA, Array.getD_eq_getD_getElem?, hp]

theorem letters_pair :
    ∀ t ∈ m23Letters 2, (img t 15 = 15 ∨ img t 15 = 18) ∧ (img t 18 = 15 ∨ img t 18 = 18) := by
  intro t ht
  have hW : m23Letters 2 =
      m23STabs ++ [wordTabA #[m23ta.toArray, m23tb.toArray] 23 [0, 1, 1, 0]] := by
    unfold m23Letters
    have : m23MwLit[2]! = [[0, 1, 1, 0]] := by decide +kernel
    rw [this]
    rfl
  rw [hW, List.mem_append] at ht
  rcases ht with ht | ht
  · have hS : ∀ t ∈ m23STabs,
        (img t 15 = 15 ∨ img t 15 = 18) ∧ (img t 18 = 15 ∨ img t 18 = 18) := by
      decide +kernel
    exact hS t ht
  · rw [List.mem_singleton] at ht
    subst ht
    rw [img_wordTabA (by norm_num), img_wordTabA (by norm_num)]
    constructor <;> decide +kernel


theorem gen_maps_pair {x : Gm} (hx : x ∈ m23Ctx.sg ++ m23Ctx.gens 2) :
    (x • (15 : Fin 23) = 15 ∨ x • (15 : Fin 23) = 18) ∧
      (x • (18 : Fin 23) = 15 ∨ x • (18 : Fin 23) = 18) := by
  have h1 : genTabs 23 (m23Ctx.sg ++ m23Ctx.gens 2) = m23Letters 2 :=
    (m23Ctx.Y_letters (j := 2) (by rw [m23_J]; norm_num)).trans
      (m23_letters (j := 2) (by norm_num))
  have ht : (tab 23 x).toArray ∈ m23Letters 2 := by
    rw [← h1]
    simp only [genTabs, List.mem_map]
    exact ⟨x, hx, rfl⟩
  have hp := letters_pair _ ht
  rw [img_tab, img_tab] at hp
  have e15 : act 23 x 15 = (x • (15 : Fin 23)).val := act_eq x ⟨15, by norm_num⟩
  have e18 : act 23 x 18 = (x • (18 : Fin 23)).val := act_eq x ⟨18, by norm_num⟩
  rw [e15, e18] at hp
  refine ⟨?_, ?_⟩
  · rcases hp.1 with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  · rcases hp.2 with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)

theorem Y2_le_stab : m23Ctx.Y 2 ≤ MulAction.stabilizer Gm ({15, 18} : Finset (Fin 23)) := by
  unfold LatCtx.Y
  rw [Subgroup.closure_le]
  intro x hx
  exact mem_stabilizer_pair_iff.mpr (gen_maps_pair hx)

theorem card_isE2_four {V : Type} [Group V] (h : IsE2 4 V) : Nat.card V = 16 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin 4 → ZMod 2) = 16
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem fixing_eq_of_lattice
    {A : Subgroup Gm} (hA : IsPSL 3 2 2 ↥A)
    (hSN : m23Ctx.S ≤ Subgroup.normalizer (A : Set Gm)) :
    A = fixingSubgroup Gm ({15, 18} : Set (Fin 23)) := by
  have hAcard : Nat.card ↥A = 20160 := Ch1Four.card_of_isPSL_three_four hA
  have hAsimple : IsSimpleGroup ↥A := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2 hA).2
  have hnab : ∃ a b : ↥A, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative ↥A := ⟨⟨fun a b => hcon a b⟩⟩
    have hp := IsSimpleGroup.prime_card (α := ↥A)
    rw [hAcard] at hp
    norm_num at hp
  have hAc : A ∈ cComp A := mem_cComp_self_of_simple hAsimple hnab
  have hAfam' : A ∈ cComp (A ⊔ m23Ctx.S) :=
    F146Field.Case2b.mem_cComp_sup_of_normalizes hAc hSN
  have hAfam : A ∈ lFamily m23Ctx.S := hAfam'
  have hSsyl := m23_S_sylow
  have hU : Nat.card ↥(m23Ctx.S ⊓ A) = 64 :=
    card_eq_sixty_four_of_isSylowTwoOf (isSylowTwoOf_inf_of_le_normalizer hSsyl hSN) hAcard
  have hScard : Nat.card ↥m23Ctx.S = 128 := by
    have h := m23_member_card 0 (by norm_num)
    rw [m23Ctx.Y_zero] at h
    simpa using h
  have hcardH : Nat.card ↥(A ⊔ m23Ctx.S) = 40320 := by
    have h := card_sup_mul_card_inf hSN
    rw [sup_comm, inf_comm] at h
    rw [hU, hAcard, hScard] at h
    refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 64) ?_
    rw [h]
  obtain ⟨j, hj, hjeq⟩ := m23_complete (A ⊔ m23Ctx.S) le_sup_right
  have hY2 : A ⊔ m23Ctx.S = m23Ctx.Y 2 := by
    by_cases hj16 : j < 16
    · have hmem : memberOrTop 16 m23Ctx.Y j = m23Ctx.Y j := by simp [memberOrTop, hj16]
      rw [hmem] at hjeq
      have hc := m23_member_card j hj16
      rw [← hjeq, hcardH] at hc
      have hj25 : j = 2 ∨ j = 5 := by
        interval_cases j <;> first | omega | simp at hc
      rcases hj25 with rfl | rfl
      · exact hjeq
      · exfalso
        obtain ⟨V, hVn, hV, hY⟩ := m23_shape_y5 hSsyl.2.1 hAfam hjeq
        have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
        rw [Ch1Four.card_alt7 hY, card_isE2_four hV, hAcard] at h1
        omega
    · exfalso
      have hj16' : j = 16 := by omega
      subst hj16'
      have hmem : memberOrTop 16 m23Ctx.Y 16 = ⊤ := by simp [memberOrTop]
      rw [hmem] at hjeq
      rw [hjeq, Subgroup.card_top, card_Mg] at hcardH
      omega
  have hAY : A ≤ m23Ctx.Y 2 := by
    rw [← hY2]
    exact le_sup_left
  have hle : A ≤ MulAction.stabilizer Gm ({15, 18} : Finset (Fin 23)) := hAY.trans Y2_le_stab
  have hle' : A ≤ fixingSubgroup Gm ({15, 18} : Set (Fin 23)) :=
    le_fixingSubgroup_pair_of_simple (by decide) hAsimple (by omega) hle
  refine Subgroup.eq_of_le_of_card_ge hle' ?_
  rw [card_fix_pair four_pretrans (by simp) card_Mg (by decide : (15 : Fin 23) ≠ 18), hAcard]

theorem stableMax_lattice
    {A : Subgroup Gm} (hA : IsPSL 3 2 2 ↥A)
    (hSN : m23Ctx.S ≤ Subgroup.normalizer (A : Set Gm)) : StableMax m23Ctx.S A := by
  have hAeq := fixing_eq_of_lattice hA hSN
  have hSyl := isSylowTwoOf_inf_of_le_normalizer m23_S_sylow hSN
  subst hAeq
  exact stableMax_of_pair four_pretrans (by simp) card_Mg (by decide : (15 : Fin 23) ≠ 18)
    m23_S_sylow.2.1 hSN hSyl

end M23

end QA25

end CFSG.Quasithin
