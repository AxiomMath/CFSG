module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporGen
public import CFSG.Sporadic.ThSchreier.NodeFullAutomorphism
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Sporadic.Th.Recog.AltNine
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Rank
import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF
import CFSG.Quasithin.Vol2.Ch8Sec2L829LN1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

namespace SporTh

open Equiv Equiv.Perm

@[expose] def omega8 : Finset (Fin 9) := Finset.univ.erase 8

@[expose] def altEight : Subgroup (alternatingGroup (Fin 9)) :=
  CFSG.Sporadic.Th.Recog.fixingSubgroup omega8

noncomputable def altEightEquiv : ↥altEight ≃* alternatingGroup ↥omega8 :=
  (MulEquiv.subgroupCongr (CFSG.Sporadic.Th.Recog.fixingSubgroup_eq_map omega8)).trans
    (((⊤ : Subgroup (alternatingGroup ↥omega8)).equivMapOfInjective _
      (CFSG.Sporadic.Th.Recog.altEmbed_injective omega8)).symm.trans Subgroup.topEquiv)

instance : Nontrivial ↥omega8 :=
  ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩⟩

theorem natCard_omega8 : Nat.card ↥omega8 = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

theorem isSimpleGroup_altEight : IsSimpleGroup ↥altEight := by
  haveI : IsSimpleGroup (alternatingGroup ↥omega8) :=
    alternatingGroup.isSimpleGroup (by rw [natCard_omega8]; norm_num)
  exact altEightEquiv.isSimpleGroup

theorem card_altEight : Nat.card ↥altEight = 20160 := by
  rw [Nat.card_congr altEightEquiv.toEquiv, nat_card_alternatingGroup, natCard_omega8]
  decide

@[expose] def cyc1 : alternatingGroup (Fin 9) :=
  ⟨swap 0 1 * swap 1 2, by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide⟩

@[expose] def cyc2 : alternatingGroup (Fin 9) :=
  ⟨swap 3 4 * swap 4 5, by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap (by decide), sign_swap (by decide)]
    decide⟩

theorem orderOf_cyc1 : orderOf cyc1 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext (by decide)) fun h => ?_
  have := congrArg Subtype.val h
  revert this
  decide

theorem orderOf_cyc2 : orderOf cyc2 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (Subtype.ext (by decide)) fun h => ?_
  have := congrArg Subtype.val h
  revert this
  decide

theorem cyc2_not_mem_zpowers : cyc2 ∉ Subgroup.zpowers cyc1 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_cyc1]
  intro h
  simp only [Finset.mem_image, Finset.mem_range] at h
  obtain ⟨k, hk, hkc⟩ := h
  have hv := congrArg Subtype.val hkc
  interval_cases k <;> revert hv <;> decide

theorem two_le_pRank_altEight : 2 ≤ CFSG.Open.pRank 3 altEight := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmem : ∀ c : alternatingGroup (Fin 9), (c : Perm (Fin 9)) 8 = 8 → c ∈ altEight :=
    fun c hc x hx => by
      have : x = 8 := by simpa [omega8] using hx
      exact this ▸ hc
  exact CFSG.GroupTheory.two_le_pRank_of_commute (hmem cyc1 (by decide)) (hmem cyc2 (by decide))
    orderOf_cyc1 orderOf_cyc2 (Subtype.ext (by decide)) cyc2_not_mem_zpowers

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3


noncomputable def kap : ↥M →* alternatingGroup (Fin 9) := kappa.toMonoidHom.comp AltQuot.proj

theorem kap_surjective : Function.Surjective kap :=
  kappa.surjective.comp AltQuot.proj_surjective

theorem kap_eq_one_iff {m : ↥M} : kap m = 1 ↔ (m : J) ∈ Q := by
  rw [← AltQuot.proj_eq_one_iff]
  exact kappa.map_eq_one_iff

noncomputable def xM : Subgroup ↥M := altEight.comap kap

noncomputable def kapX : ↥xM →* ↥altEight :=
  (kap.comp xM.subtype).codRestrict altEight fun x => x.2

theorem kapX_surjective : Function.Surjective kapX := by
  rintro ⟨a, ha⟩
  obtain ⟨m, rfl⟩ := kap_surjective a
  exact ⟨⟨m, ha⟩, rfl⟩

theorem ker_kapX : kapX.ker = (Q.subgroupOf M).subgroupOf xM := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← kap_eq_one_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem subgroupOf_Q_le_xM : Q.subgroupOf M ≤ xM := fun m hm => by
  change kap m ∈ altEight
  rw [kap_eq_one_iff.2 (Subgroup.mem_subgroupOf.1 hm)]
  exact one_mem _

theorem card_ker_kapX : Nat.card kapX.ker = 512 := by
  rw [ker_kapX, Nat.card_congr (Subgroup.subgroupOfEquivOfLe subgroupOf_Q_le_xM).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q_le_M).toEquiv, card_Q]

theorem card_xM : Nat.card xM = 512 * 20160 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup kapX.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective kapX kapX_surjective).toEquiv,
    card_altEight, card_ker_kapX, mul_comm]

theorem not_hasCompFactor_xM (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    ¬ HasCompFactor xM IsCalL0 := by
  rintro ⟨L, _, hL, hcal⟩
  rcases isCompositionFactor_of_normal kapX.ker hL with h1 | h2
  · exact not_isCalL0_of_isCompositionFactor_of_dvd hO (k := 9) (N := 512) (by decide +kernel)
      (by rw [card_ker_kapX]) h1 hcal
  · have h3 := (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      (QuotientGroup.quotientKerEquivOfSurjective kapX kapX_surjective)).1 h2
    haveI := isSimpleGroup_altEight
    exact not_isCalL0_of_isCompositionFactor_of_isSimpleGroup hO (k := 6)
      (by rw [card_altEight]; decide +kernel) h3 hcal

theorem two_le_pRank_xM : 2 ≤ CFSG.Open.pRank 3 xM :=
  two_le_pRank_of_le_map kap Nat.prime_three (by decide)
    (Subgroup.map_comap_eq_self_of_surjective kap_surjective altEight).ge two_le_pRank_altEight

noncomputable def xJ : Subgroup J := xM.map M.subtype

theorem card_xJ : Nat.card xJ = 512 * 20160 := by
  rw [xJ, Subgroup.card_map_of_injective M.subtype_injective, card_xM]

theorem exists_isSylowIn_le_xJ :
    ∃ S : Subgroup J, S ≤ xJ ∧ IsSylowIn 2 S ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 15) (G := ↥xJ)
    (by rw [card_xJ]; norm_num)
  refine ⟨K.map xJ.subtype, Subgroup.map_subtype_le K, le_top, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 15)
      (by rw [Subgroup.card_map_of_injective xJ.subtype_injective, hK])
  · rw [Subgroup.relIndex_top_right]
    have h := (K.map xJ.subtype).index_mul_card
    rw [Subgroup.card_map_of_injective xJ.subtype_injective, hK,
      CFSG.Sporadic.Bridge.Th.card_J] at h
    omega

theorem card_xJ_lt :
    Nat.card xJ < Nat.card J := by
  rw [card_xJ, CFSG.Sporadic.Bridge.Th.card_J]
  norm_num

theorem x_mul_y_ne : x * y ≠ y * x := by
  intro h
  apply CFSG.Sporadic.ThSchreier.aPerm_mul_bPerm_ne
  have h' : (⟨x, x_mem_M⟩ : ↥M) * ⟨y, y_mem_M⟩ = ⟨y, y_mem_M⟩ * ⟨x, x_mem_M⟩ := Subtype.ext h
  have h2 := congrArg (fun m : ↥M =>
    ((kappa (QuotientGroup.mk m : ↥M ⧸ Q.subgroupOf M) : alternatingGroup (Fin 9)) :
      Perm (Fin 9))) h'
  simp only [QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul, kappa_mk_x, kappa_mk_y] at h2
  exact h2

abbrev GrpEquiv (G H : Type*) [Group G] [Group H] : Type _ := G ≃* H

theorem four_le_pRank_J :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup J) := by
  obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Th_elementary_three_rank_four
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Blueprint.NativeSporadic.Th) :=
    CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hE hcard
  have f : GrpEquiv Blueprint.NativeSporadic.Th J := thEquivJ
  rwa [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt f] at h4

theorem card_outer_J :
    Nat.card (Outer J) = 1 := by
  change (inner J).index = 1
  rw [CFSG.Sporadic.ThSchreier.inner_J, Subgroup.index_top]

theorem nonempty_grpEquiv_J
    (Y : Type) [Group Y]
    (hY : CFSG.Models.IsSporadic Y .Th) : Nonempty (GrpEquiv Y J) := by
  letI : Mul TauCeti.SporadicName.Th.Group := Monoid.toMul
  obtain ⟨e₁⟩ := hY
  obtain ⟨e₂⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  exact ⟨(e₁.trans e₂.symm).trans thEquivJ⟩

end SporTh

theorem asch54SporThGen_of_model {C : Type} [hCg : Group C] [hCf : Finite C]
    (hsC : ∀ (Y : Type) [Group Y], CFSG.Models.IsSporadic Y .Th → Nonempty (Y ≃* C))
    (hOut : Nat.card (Outer C) = 1) (hsimp : IsSimpleGroup C) (hnab : ∃ a b : C, a * b ≠ b * a)
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup C)) {X₀ : Subgroup C}
    (hX₀ : Nat.card X₀ < Nat.card C) (hS : ∃ S : Subgroup C, S ≤ X₀ ∧ IsSylowIn 2 S ⊤)
    (hX₀L : ¬ HasCompFactor X₀ IsCalL0) (hX₀3 : 2 ≤ CFSG.Open.pRank 3 X₀) :
    Asch54SporThGen := by
  intro Q _ _ L T hLn hL hC hT
  obtain ⟨φ⟩ := hsC ↥L hL
  have hOutL : Nat.card (Outer ↥L) = 1 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv,
      hOut]
  have hLt : L = ⊤ := Subgroup.index_eq_one.1 (le_antisymm
    ((index_le_card_outer L hC).trans hOutL.le)
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite))
  let e : Q ≃* C := (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLt.symm)).trans φ
  have hcardQ : Nat.card Q = Nat.card C := Nat.card_congr e.toEquiv
  refine ⟨?_, ?_⟩
  ·
    haveI := hsimp
    haveI : IsSimpleGroup Q := e.isSimpleGroup
    have hperf : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = (⊤ : Subgroup Q) := by
      rcases (Subgroup.commutator_normal (⊤ : Subgroup Q) ⊤).eq_bot_or_eq_top with hb | ht
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        apply hab
        have hm : ⁅e.symm a, e.symm b⁆ ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [hb, Subgroup.mem_bot] at hm
        have h := commutatorElement_eq_one_iff_mul_comm.1 hm
        rw [← map_mul, ← map_mul] at h
        exact e.symm.injective h
      · exact ht
    have hle : (⊤ : Subgroup Q) ≤ perfectCore ⊤ := le_perfectCore_of_perfect le_rfl hperf
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e] at h4
    exact lt_of_lt_of_le h4 (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hle)
  ·
    obtain ⟨S, hSX, hS⟩ := hS
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_map_conj_eq_of_isSylowIn hS (isSylowIn_top_map_mulEquiv hT e)
    set X : Subgroup Q := (X₀.map (MulAut.conj g).toMonoidHom).map e.symm.toMonoidHom with hXdef
    have hTX : T ≤ X := fun t ht => by
      refine ⟨e t, ?_, e.symm_apply_apply t⟩
      have : e t ∈ T.map e.toMonoidHom := ⟨t, ht, rfl⟩
      rw [← hg] at this
      exact Subgroup.map_mono hSX this
    have hXcard : Nat.card X = Nat.card X₀ := by
      rw [hXdef, Subgroup.card_map_of_injective e.symm.injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hXlt : X < ⊤ := by
      refine lt_top_iff_ne_top.2 fun htop => ?_
      have h1 := hX₀
      rw [← hXcard, htop, Subgroup.card_top, hcardQ] at h1
      exact lt_irrefl _ h1
    have hX0 : ¬ HasCompFactor X IsCalL0 := by
      rw [hXdef, hasCompFactor_map_of_injective _ e.symm.injective,
        hasCompFactor_map_of_injective _ (MulAut.conj g).injective]
      exact hX₀L
    have hX3 : 2 ≤ CFSG.Open.pRank 3 X := by
      refine hX₀3.trans ?_
      refine (CFSG.SectionRank.pRank_le_map Nat.prime_three.one_lt
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective X₀).trans ?_
      exact CFSG.SectionRank.pRank_le_map Nat.prime_three.one_lt e.symm.toMonoidHom
        e.symm.injective _
    have hXl : X ≤ lGen IsCalL0 ⊤ T :=
      le_iSup₂_of_le (f := fun X (_ : X ∈ calLT IsCalL0 ⊤ T) => X) X ⟨hTX, hXlt, hX0⟩ le_rfl
    exact lt_of_lt_of_le (by omega) (hX3.trans (CFSG.SectionRank.pRank_mono
      Nat.prime_three.one_lt hXl))

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 SporTh

theorem SporTh.not_hasCompFactor_xJ :
    ¬ HasCompFactor xJ IsCalL0 := by
  rw [xJ, hasCompFactor_map_of_injective _ M.subtype_injective]
  exact not_hasCompFactor_xM CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

theorem SporTh.two_le_pRank_xJ :
    2 ≤ CFSG.Open.pRank 3 xJ :=
  two_le_pRank_xM.trans (CFSG.SectionRank.pRank_le_map Nat.prime_three.one_lt M.subtype
    M.subtype_injective xM)


theorem asch54SporThGen_holds : Asch54SporThGen :=
  asch54SporThGen_of_model (C := J) (hCg := J.toGroup) (hCf := inferInstance)
    nonempty_grpEquiv_J card_outer_J
    (CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts)
    ⟨x, y, x_mul_y_ne⟩ four_le_pRank_J
    card_xJ_lt exists_isSylowIn_le_xJ not_hasCompFactor_xJ two_le_pRank_xJ

end CFSG.LocalAnalysis.WeakClosure81

end
