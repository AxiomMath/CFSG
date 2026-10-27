module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Defs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Fi22
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzFuse
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.SuzOddCore.Outer
public import CFSG.Mathlib.GroupTheory.FiniteCentralizerImage
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.CoprimeAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
public import Mathlib.GroupTheory.PGroup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.Sporadic.Co1Block.TwoBTri
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds

public section

namespace CFSG.StandardType.TwE6MaxEleven

open CFSG.Blueprint

private theorem orderOf_ne_thirtythree {G : Type*} [Group G]
    (h : ∀ x : G, orderOf x = 3 →
      ¬ 11 ∣ Nat.card (Subgroup.centralizer ({x} : Set G))) :
    ∀ g : G, orderOf g ≠ 33 := by
  intro g hg
  have hx : orderOf (g ^ 11) = 3 := by
    rw [orderOf_pow' g (n := 11) (by norm_num), hg]
    norm_num
  have hu : orderOf (g ^ 3) = 11 := by
    rw [orderOf_pow' g (n := 3) (by norm_num), hg]
    norm_num
  have hcomm : Commute (g ^ 3) (g ^ 11) := Commute.pow_pow_self g 3 11
  have hle : Subgroup.zpowers (g ^ 3) ≤ Subgroup.centralizer ({g ^ 11} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (hcomm.zpow_left k).eq
  have hdvd : 11 ∣ Nat.card (Subgroup.centralizer ({g ^ 11} : Set G)) := by
    have h1 : 11 ∣ Nat.card (Subgroup.zpowers (g ^ 3)) := by rw [Nat.card_zpowers, hu]
    exact h1.trans (Subgroup.card_dvd_of_le hle)
  exact h (g ^ 11) hx hdvd

private noncomputable def frattiniAutLocal (A : Type*) [Group A] :
    MulAut A →* MulAut (A ⧸ frattini A) where
  toFun σ := QuotientGroup.congr (frattini A) (frattini A) σ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' σ τ := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

@[simp]
private theorem frattiniAutLocal_mk {A : Type*} [Group A] (σ : MulAut A) (x : A) :
    frattiniAutLocal A σ (x : A ⧸ frattini A) = (σ x : A ⧸ frattini A) := rfl

private theorem actsTrivially_of_frattini_three {G A : Type*} [Group G] [Finite G] [Group A]
    [Finite A] [MulDistribMulAction A G] (hG : IsPGroup 3 G)
    (hcop : Nat.Coprime (Nat.card A) (Nat.card G))
    (h : ∀ (a : A) (x : G), x⁻¹ * (a • x) ∈ frattini G) : ∀ (a : A) (x : G), a • x = x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 G) := ⟨hG⟩
  have hsolv : Group.IsSolvable G := by
    have := hG.isNilpotent
    infer_instance
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := G) (A := A) hsolv hcop
  have hle : CFSG.commutatorAction A G ≤ frattini G := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, x, -, rfl⟩
    exact h a x
  have htop : CFSG.fixedPointSubgroup A G ⊔ frattini G = ⊤ :=
    eq_top_iff.mpr (hsup.symm.le.trans (sup_le_sup_left hle _))
  have hfix := CFSG.lemma_1_7_a (R := G) (p := 3) (CFSG.fixedPointSubgroup A G) htop
  intro a x
  have hx : x ∈ CFSG.fixedPointSubgroup A G := by rw [hfix]; exact Subgroup.mem_top x
  exact (FixedPoints.mem_subgroup A G x).mp hx a

private theorem eq_one_of_frattiniAutLocal_eq_one_three {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 3 G) {τ : MulAut G} (hcop : Nat.Coprime 3 (orderOf τ))
    (h : frattiniAutLocal G τ = 1) : τ = 1 := by
  have hcard : Nat.Coprime (Nat.card (Subgroup.zpowers τ)) (Nat.card G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
    rw [Nat.card_zpowers, hn]
    exact (Nat.Coprime.pow_left n hcop).symm
  have htriv := actsTrivially_of_frattini_three (A := Subgroup.zpowers τ) hG hcard (by
    rintro ⟨_, z, rfl⟩ x
    have hz : frattiniAutLocal G (τ ^ z) = 1 := by rw [map_zpow, h, one_zpow]
    rw [← QuotientGroup.eq]
    have := congrArg (fun σ : MulAut (G ⧸ frattini G) => σ (x : G ⧸ frattini G)) hz
    simp only [frattiniAutLocal_mk, MulAut.one_apply] at this
    exact this.symm)
  ext x
  exact htriv ⟨τ, Subgroup.mem_zpowers τ⟩ x

private theorem mulAut_eq_one_of_order_dvd_eleven {V : Type*} [Group V] [Finite V]
    [IsElementaryAbelian 3 V] (hcard : Nat.card V ≤ 3 ^ 4) {σ : MulAut V}
    (hσ : orderOf σ ∣ 11) : σ = 1 := by
  by_contra hne
  haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  have hodd : orderOf σ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have h11 : orderOf σ = 11 := by
    rcases (Nat.dvd_prime Nat.prime_eleven).mp hσ with h | h
    · exact absurd h hodd
    · exact h
  let H := Subgroup.zpowers σ
  have hH : IsPGroup 11 H := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h11, pow_one])
  have hmod := hH.card_modEq_card_fixedPoints V
  have hfixcard : Nat.card (MulAction.fixedPoints H V) =
      Nat.card ↥(CFSG.fixedPointSubgroup H V) := rfl
  rw [hfixcard] at hmod
  have hV : Nat.card V = 3 ^ generatorRank V :=
    CFSG.elementaryAbelian_card_eq_pow_generatorRank V
  have hWle : Nat.card ↥(CFSG.fixedPointSubgroup H V) ∣ Nat.card V :=
    Subgroup.card_subgroup_dvd_card _
  obtain ⟨d, hd, hdeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (hV ▸ hWle)
  have hWne : Nat.card ↥(CFSG.fixedPointSubgroup H V) ≠ Nat.card V := by
    intro heq
    have htop : CFSG.fixedPointSubgroup H V = ⊤ :=
      (Subgroup.card_eq_iff_eq_top (H := CFSG.fixedPointSubgroup H V)).mp heq
    have hfix : ∀ v : V, σ v = v := by
      intro v
      have hv : v ∈ CFSG.fixedPointSubgroup H V := by rw [htop]; exact Subgroup.mem_top v
      exact (FixedPoints.mem_subgroup H V v).mp hv ⟨σ, Subgroup.mem_zpowers σ⟩
    exact hne (MulEquiv.ext hfix)
  have hdlt : d < generatorRank V := by
    by_contra h
    push Not at h
    have hle : Nat.card V ≤ Nat.card ↥(CFSG.fixedPointSubgroup H V) := by
      rw [hV, hdeq]
      exact Nat.pow_le_pow_right (by norm_num) h
    have hle' : Nat.card ↥(CFSG.fixedPointSubgroup H V) ≤ Nat.card V :=
      Nat.le_of_dvd Nat.card_pos hWle
    exact hWne (le_antisymm hle' hle)
  have hdvd : 11 ∣ 3 ^ generatorRank V - 3 ^ d := by
    rw [hV, hdeq] at hmod
    exact (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hdlt.le)).mp hmod.symm
  have hle4 : generatorRank V ≤ 4 := by
    rw [hV] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcard
  have hpos : 0 < generatorRank V - d := by omega
  have hk : generatorRank V - d ≤ 4 := by omega
  have hdvd2 : 11 ∣ 3 ^ (generatorRank V - d) - 1 := by
    have h1 : 3 ^ generatorRank V = 3 ^ d * 3 ^ (generatorRank V - d) := by
      rw [← pow_add, Nat.add_sub_of_le hdlt.le]
    have hfac : 3 ^ generatorRank V - 3 ^ d =
        3 ^ d * (3 ^ (generatorRank V - d) - 1) := by
      calc 3 ^ generatorRank V - 3 ^ d
          = 3 ^ d * 3 ^ (generatorRank V - d) - 3 ^ d * 1 := by rw [h1, mul_one]
        _ = 3 ^ d * (3 ^ (generatorRank V - d) - 1) := by
            rw [← Nat.mul_sub_left_distrib]
    rw [hfac] at hdvd
    have hnot : ¬ 11 ∣ 3 ^ d := by
      intro h
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_eleven h
      norm_num at this
    exact (Nat.Prime.dvd_mul Nat.prime_eleven).mp hdvd |>.resolve_left hnot
  interval_cases h : (generatorRank V - d)
  all_goals norm_num at hdvd2

private theorem not_eleven_dvd_card_centralizer_Fi22 (t : CFSG.Sporadic.Fi22.J)
    (ht : orderOf t = 3) :
    ¬ 11 ∣ Nat.card (Subgroup.centralizer ({t} : Set CFSG.Sporadic.Fi22.J)) := by
  obtain ⟨k, hk, hkf, hcard⟩ :=
    CFSG.HardMathSupport.Dickson.I271.TabFi23.classify_card (t := t) ht
  interval_cases k
  · have hf : CFSG.HardMathSupport.Solomon.Coordinator.YS08.Fi22Copy.fixN
        (CFSG.Sporadic.Fi23.pi22 t) = 0 := by
      rcases hkf with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      all_goals omega
    have hdvd := CFSG.HardMathSupport.Dickson.I271.TabFi23.card_cent_dvd_of_fixN ht (Or.inl hf)
    refine fun h11 => ?_
    have := h11.trans hdvd
    norm_num at this
  · have hf : CFSG.HardMathSupport.Solomon.Coordinator.YS08.Fi22Copy.fixN
        (CFSG.Sporadic.Fi23.pi22 t) = 27 := by
      rcases hkf with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · omega
      · exact h
      all_goals omega
    have hdvd := CFSG.HardMathSupport.Dickson.I271.TabFi23.card_cent_dvd_of_fixN ht
      (Or.inr (Or.inl hf))
    refine fun h11 => ?_
    have := h11.trans hdvd
    norm_num at this
  · have hf : CFSG.HardMathSupport.Solomon.Coordinator.YS08.Fi22Copy.fixN
        (CFSG.Sporadic.Fi23.pi22 t) = 36 := by
      rcases hkf with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · omega
      · exact h
      · omega
    have hdvd := CFSG.HardMathSupport.Dickson.I271.TabFi23.card_cent_dvd_of_fixN ht
      (Or.inr (Or.inr hf))
    refine fun h11 => ?_
    have := h11.trans hdvd
    norm_num at this
  · have hf : CFSG.HardMathSupport.Solomon.Coordinator.YS08.Fi22Copy.fixN
        (CFSG.Sporadic.Fi23.pi22 t) = 126 := by
      rcases hkf with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · omega
      · omega
      · exact h
    rw [CFSG.HardMathSupport.Dickson.I271.TabFi23.card_cent_eq_of_fixN ht hf]
    norm_num

private theorem noOrder33_Fi22_native :
    ∀ g : CFSG.Blueprint.NativeSporadic.Fi22, orderOf g ≠ 33 := by
  have hJ : ∀ y : CFSG.Sporadic.Fi22.J, orderOf y ≠ 33 :=
    orderOf_ne_thirtythree (fun t ht => not_eleven_dvd_card_centralizer_Fi22 t ht)
  intro g hg
  exact hJ (CFSG.Sporadic.Fi22.fi22EquivJ g) (by rw [MulEquiv.orderOf_eq]; exact hg)

private theorem noOrder33_Fi22 :
    ∀ g : CFSG.Blueprint.NativeSporadic.Carrier .Fi22, orderOf g ≠ 33 := by
  change ∀ g : CFSG.Blueprint.NativeSporadic.Fi22, orderOf g ≠ 33
  exact noOrder33_Fi22_native

private theorem group_rank_closure_permsA_le (n : ℕ) (gs : Array (Array ℕ))
    (hsize : gs.size = 4) :
    Group.rank (Subgroup.closure (CFSG.RankThree.Native.permsA n gs)) ≤ 4 := by
  let A := Subgroup.closure (CFSG.RankThree.Native.permsA n gs)
  let gen : Fin 4 → A := fun k =>
    ⟨CFSG.Monster.B.Co2.permOfArr n gs[k.val]!, by
      show CFSG.Monster.B.Co2.permOfArr n gs[k.val]! ∈
        Subgroup.closure (CFSG.RankThree.Native.permsA n gs)
      rw [CFSG.RankThree.Native.permsA]
      exact Subgroup.subset_closure
        (Set.mem_image_of_mem (fun k => CFSG.Monster.B.Co2.permOfArr n gs[k]!)
          (x := k.val) (a := {k | k < gs.size}) (by rw [hsize]; exact k.2))⟩
  have himg : A.subtype '' Set.range gen = CFSG.RankThree.Native.permsA n gs := by
    ext x
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨k.val, by rw [hsize]; exact k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨gen ⟨k, by rwa [hsize] at hk⟩, ⟨⟨k, by rwa [hsize] at hk⟩, rfl⟩, rfl⟩
  have hmap : (Subgroup.closure (Set.range gen)).map A.subtype = A := by
    rw [MonoidHom.map_closure, himg]
  have htop : Subgroup.closure (Set.range gen) = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype]
  have hle := Group.rank_le (S := Finset.univ.image gen) (by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact htop)
  calc Group.rank A ≤ (Finset.univ.image gen).card := hle
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

private theorem map_centralizer_singleton_subtype {G : Type*} [Group G] (P : Subgroup G) (x : ↥P) :
    (Subgroup.centralizer ({x} : Set ↥P)).map P.subtype =
      P ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨z.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    exact congrArg Subtype.val hz
  · intro hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hyP, hyC⟩ := hy
    refine ⟨⟨y, hyP⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
    exact Subtype.ext hyC

private theorem centralizer_pow_eq_local {P : Type*} [Group P] {c : P} (hc : c ^ 3 = 1)
    {e : ℕ} (he : e = 1 ∨ e = 2) :
    Subgroup.centralizer ({c ^ e} : Set P) = Subgroup.centralizer ({c} : Set P) := by
  rcases he with rfl | rfl
  · rw [pow_one]
  · have hc2 : c ^ 2 = c⁻¹ := by
      rw [pow_two]
      exact eq_inv_of_mul_eq_one_left (by
        simpa [pow_succ, pow_two, mul_assoc] using hc)
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hc2]
    exact Iff.intro (fun hx => Commute.inv_right_iff.mp hx)
      (fun hx => Commute.inv_right_iff.mpr hx)

open CFSG.Sporadic.SuzOddCore
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.HardMathSupport.Dickson.I271

private theorem card_centralizer_fuseXA :
    Nat.card (Subgroup.centralizer
      ({⟨CFSG.HardMathSupport.Dickson.I271.fuseXA,
        CFSG.HardMathSupport.Dickson.I271.fuseXA_mem⟩} : Set ↥suzM)) = 9797760 := by
  rw [← Subgroup.card_map_of_injective suzM.subtype_injective,
    map_centralizer_singleton_subtype (P := suzM)
      (x := ⟨CFSG.HardMathSupport.Dickson.I271.fuseXA,
        CFSG.HardMathSupport.Dickson.I271.fuseXA_mem⟩)]
  rw [inf_comm, ← CFSG.HardMathSupport.Dickson.I271.aSub_eq,
    CFSG.HardMathSupport.Dickson.I271.card_aSub]

private theorem card_centralizer_yPerm :
    Nat.card (Subgroup.centralizer
      ({⟨CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm_mem⟩} : Set ↥suzM)) = 3240 := by
  rw [← Subgroup.card_map_of_injective suzM.subtype_injective,
    map_centralizer_singleton_subtype (P := suzM)
      (x := ⟨CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm_mem⟩)]
  rw [inf_comm, ← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.Cy_eq.1,
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.Cy_eq.2]

private theorem not_eleven_dvd_centralizer_xB_ambient :
    ¬ 11 ∣ Nat.card (↥(Subgroup.centralizer
      ({CFSG.HardMathSupport.Dickson.I271.xBPerm} :
        Set (Equiv.Perm (Fin 1782))) ⊓ suzM)) := by
  intro h11
  set A : Subgroup (Equiv.Perm (Fin 1782)) :=
    Subgroup.closure (CFSG.RankThree.Native.permsA 1782
      (CFSG.HardMathSupport.Dickson.I271.TabSuzB.aGens ())) with hA
  set C : Subgroup (Equiv.Perm (Fin 1782)) :=
    Subgroup.centralizer ({CFSG.HardMathSupport.Dickson.I271.xBPerm} :
      Set (Equiv.Perm (Fin 1782))) ⊓ suzM with hC
  obtain ⟨hAcard, hxBmem, hAle, hnorm, hcent⟩ :=
    CFSG.HardMathSupport.Dickson.I271.TabSuzB.caseB_spec
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 6) (by rw [hAcard]; norm_num)
  have hsize : (CFSG.HardMathSupport.Dickson.I271.TabSuzB.aGens ()).size = 4 := by
    simp [CFSG.HardMathSupport.Dickson.I271.TabSuzB.aGens,
      CFSG.HardMathSupport.Dickson.I271.TabSuzB.aTuples]
  have hrankA : Group.rank A ≤ 4 := by
    simpa [A] using group_rank_closure_permsA_le 1782
      (CFSG.HardMathSupport.Dickson.I271.TabSuzB.aGens ()) hsize
  have hAleC : A ≤ C := by simpa [A, C] using hAle
  have hnormC : ∀ g ∈ C, ∀ a ∈ A, g * a * g⁻¹ ∈ A := by simpa [A, C] using hnorm
  have hcentC : C ⊓ Subgroup.centralizer (A : Set (Equiv.Perm (Fin 1782))) ≤ A := by
    simpa [A, C, inf_assoc, inf_comm, inf_left_comm] using hcent
  haveI : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' (G := C) 11 (by simpa [C] using h11)
  have hC_le_norm : C ≤ Subgroup.normalizer (A : Set (Equiv.Perm (Fin 1782))) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hnormC g hg a ha
    · intro ha
      have := hnormC g⁻¹ (C.inv_mem hg) (g * a * g⁻¹) ha
      simpa [mul_assoc] using this
  let ψ : C →* MulAut A :=
    (Subgroup.normalizerMonoidHom (H := A)).comp (Subgroup.inclusion hC_le_norm)
  let σ : MulAut A := ψ u
  have hu11 : u ^ 11 = 1 := by
    rw [← huord]
    exact pow_orderOf_eq_one u
  have hσ11 : σ ^ 11 = 1 := by
    rw [← map_pow, hu11, map_one]
  have hσne : σ ≠ 1 := by
    intro hσ
    have hker : u ∈ ψ.ker := by rw [MonoidHom.mem_ker]; exact hσ
    have hmem : (Subgroup.inclusion hC_le_norm u : Subgroup.normalizer
        (A : Set (Equiv.Perm (Fin 1782)))) ∈
        (Subgroup.normalizerMonoidHom (H := A)).ker := by
      rw [MonoidHom.mem_ker] at hker ⊢
      exact hker
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    have hcentA : (u : Equiv.Perm (Fin 1782)) ∈
        Subgroup.centralizer (A : Set (Equiv.Perm (Fin 1782))) := by
      simpa using hmem
    have huA : (u : Equiv.Perm (Fin 1782)) ∈ A :=
      hcentC (Subgroup.mem_inf.mpr ⟨u.2, hcentA⟩)
    have huord' : orderOf (u : Equiv.Perm (Fin 1782)) = 11 := by
      rw [Subgroup.orderOf_coe u]
      exact huord
    have hdvd : orderOf (⟨(u : Equiv.Perm (Fin 1782)), huA⟩ : A) ∣ Nat.card A :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, huord', hAcard] at hdvd
    norm_num at hdvd
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (IsPGroup 3 ↥A) := ⟨hA3⟩
  letI : Finite ↥A := inferInstance
  haveI : IsElementaryAbelian 3 (↥A ⧸ frattini ↥A) :=
    @CFSG.isElementaryAbelian_quotient_frattini ↥A (inferInstance) (inferInstance) 3
      (inferInstance) (inferInstance)
  have hrankV : Group.rank (↥A ⧸ frattini ↥A) ≤ 4 :=
    (Group.rank_le_of_surjective (QuotientGroup.mk' (frattini ↥A))
      (QuotientGroup.mk'_surjective _)).trans hrankA
  have hcardV : Nat.card (↥A ⧸ frattini ↥A) ≤ 3 ^ 4 := by
    have hVcard : Nat.card (↥A ⧸ frattini ↥A) =
        3 ^ generatorRank (↥A ⧸ frattini ↥A) :=
      CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := 3)
        (G := ↥A ⧸ frattini ↥A)
    have hgen : generatorRank (↥A ⧸ frattini ↥A) =
        Group.rank (↥A ⧸ frattini ↥A) :=
      CFSG.generatorRank_eq_group_rank (↥A ⧸ frattini ↥A)
    rw [hVcard, hgen]
    exact Nat.pow_le_pow_right (by norm_num) hrankV
  have hσbar : frattiniAutLocal A σ = 1 := by
    refine mulAut_eq_one_of_order_dvd_eleven hcardV ?_
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hσ11, map_one])
  have hcop : Nat.Coprime 3 (orderOf σ) := by
    have hdvd : orderOf σ ∣ 11 := orderOf_dvd_of_pow_eq_one hσ11
    have hσord : orderOf σ = 11 := by
      rcases (Nat.dvd_prime Nat.prime_eleven).mp hdvd with h | h
      · exact absurd h (by simpa [orderOf_eq_one_iff] using hσne)
      · exact h
    rw [hσord]
    norm_num
  exact hσne (eq_one_of_frattiniAutLocal_eq_one_three hA3 hcop hσbar)

private theorem not_eleven_dvd_centralizer_xB :
    ¬ 11 ∣ Nat.card (Subgroup.centralizer
      ({⟨CFSG.HardMathSupport.Dickson.I271.fuseXB,
        CFSG.HardMathSupport.Dickson.I271.fuseXB_mem⟩} : Set ↥suzM)) := by
  intro h11
  rw [← Subgroup.card_map_of_injective suzM.subtype_injective,
    map_centralizer_singleton_subtype (P := suzM)
      (x := ⟨CFSG.HardMathSupport.Dickson.I271.fuseXB,
        CFSG.HardMathSupport.Dickson.I271.fuseXB_mem⟩)] at h11
  exact not_eleven_dvd_centralizer_xB_ambient (by
    rwa [inf_comm] at h11)

private theorem not_eleven_dvd_card_centralizer_suzM (x : ↥suzM) (hx : orderOf x = 3) :
    ¬ 11 ∣ Nat.card (Subgroup.centralizer ({x} : Set ↥suzM)) := by
  have hx3 : orderOf (x : Equiv.Perm (Fin 1782)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hx
  obtain ⟨k, hk, c, hc, e, he, hcon⟩ :=
    CFSG.HardMathSupport.Dickson.I271.suz_exists_conj_classes x.2 hx3
  let K : ↥suzM := ⟨k, hk⟩
  have hc' : ∃ c' : ↥suzM, (c' : Equiv.Perm (Fin 1782)) = c := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨⟨CFSG.HardMathSupport.Dickson.I271.fuseXA,
        CFSG.HardMathSupport.Dickson.I271.fuseXA_mem⟩, rfl⟩
    · exact ⟨⟨CFSG.HardMathSupport.Dickson.I271.fuseXB,
        CFSG.HardMathSupport.Dickson.I271.fuseXB_mem⟩, rfl⟩
    · exact ⟨⟨CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm_mem⟩, rfl⟩
  obtain ⟨c', hc'val⟩ := hc'
  have hc3 : c' ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hc'val]
    rcases hc with rfl | rfl | rfl
    · simpa using CFSG.HardMathSupport.Dickson.I271.fuseXA_pow
    · simpa using CFSG.HardMathSupport.Dickson.I271.fuseXB_pow
    · simpa using CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm_pow
  have hxeq : x = K * c' ^ e * K⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
    rw [hc'val]
    exact hcon.symm
  have hcard : Nat.card (Subgroup.centralizer ({x} : Set ↥suzM)) =
      Nat.card (Subgroup.centralizer ({c' ^ e} : Set ↥suzM)) := by
    rw [hxeq]
    exact CFSG.HardMathSupport.Dickson.I271.TabFi23.card_centralizer_conj K (c' ^ e)
  rw [hcard, centralizer_pow_eq_local hc3 he]
  rcases hc with rfl | rfl | rfl
  · have hc'eq : c' = ⟨CFSG.HardMathSupport.Dickson.I271.fuseXA,
        CFSG.HardMathSupport.Dickson.I271.fuseXA_mem⟩ := Subtype.ext hc'val
    rw [hc'eq, card_centralizer_fuseXA]
    norm_num
  · have hc'eq : c' = ⟨CFSG.HardMathSupport.Dickson.I271.fuseXB,
        CFSG.HardMathSupport.Dickson.I271.fuseXB_mem⟩ := Subtype.ext hc'val
    rw [hc'eq]
    exact not_eleven_dvd_centralizer_xB
  · have hc'eq : c' = ⟨CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm,
        CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT.yPerm_mem⟩ := Subtype.ext hc'val
    rw [hc'eq, card_centralizer_yPerm]
    norm_num

private theorem noOrder33_suzM : ∀ g : ↥suzM, orderOf g ≠ 33 :=
  orderOf_ne_thirtythree (fun x hx => not_eleven_dvd_card_centralizer_suzM x hx)

private theorem noOrder33_Suz :
    ∀ g : CFSG.Blueprint.NativeSporadic.Carrier .Suz, orderOf g ≠ 33 := by
  change ∀ g : CFSG.Blueprint.NativeSporadic.Suz, orderOf g ≠ 33
  intro g hg
  exact noOrder33_suzM (CFSG.Sporadic.SuzOddCore.suzEquivM g) (by
    rw [MulEquiv.orderOf_eq]
    exact hg)

private theorem isInnerAut_suz (σ : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .Suz))
    (hσ : σ ^ 3 = 1) : ∃ n, ∀ x, σ x = n * x * n⁻¹ := by
  let G := CFSG.Blueprint.NativeSporadic.Carrier .Suz
  let N := CFSG.ComponentClassification.OuterAutomorphisms.inner G
  let q : CFSG.ComponentClassification.OuterAutomorphisms.Outer G := QuotientGroup.mk' N σ
  have hq3 : q ^ 3 = 1 := by
    rw [← map_pow, hσ, map_one]
  have hq_dvd3 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one hq3
  have hq_dvd2 : orderOf q ∣ 2 := by
    have h := orderOf_dvd_natCard q
    rwa [show Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer G) = 2 from
      CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1] at h
  have hq1 : q = 1 := by
    have h1 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) hq_dvd3 hq_dvd2
    exact orderOf_eq_one_iff.mp h1
  have hmem : σ ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    exact hq1
  change σ ∈ (MulAut.conj : G →* MulAut G).range at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, fun x => by rw [← hn, MulAut.conj_apply]⟩

theorem sporadicFacts_holds : SporadicFacts :=
  ⟨CFSG.Sporadic.Fi22.card_Fi22, noOrder33_Fi22, noOrder33_Suz, isInnerAut_suz⟩

end CFSG.StandardType.TwE6MaxEleven
