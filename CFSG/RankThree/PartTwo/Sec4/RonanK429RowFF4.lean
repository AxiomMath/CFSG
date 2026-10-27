module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFSp8
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp2
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.HardMathSupport.Dickson.Bal207 (CompShape)
open CFSG.HardMathSupport.Dickson.Bal207.FamF42 (F42CompType compShape_conj_F4_two)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 card_H6)
open scoped commutatorElement

namespace F4

variable {X : Type} [Group X]

theorem fixSubgroup_conj (x : X) :
    fixSubgroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_fixSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  · intro h
    rw [← h]
    group

theorem card_statedSp_quot {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (↥(StatedSp 3 F) ⧸ Subgroup.center ↥(StatedSp 3 F)) = 1451520 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hF, ZMod.card]
  let φ : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hc
  let e : ↥(StatedSp 3 F) ≃* H6 :=
    (MulEquiv.subgroupMap (CFSG.Adapters.RankTwoModelTransports.glCongr
      (ι := Fin 3 ⊕ Fin 3) φ) (StatedSp 3 F)).trans
      (MulEquiv.subgroupCongr (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp
        (φ := φ) 3))
  haveI : IsSimpleGroup H6 := Sp8.isSimpleGroup_H6
  have hZ : Subgroup.center H6 = ⊥ := center_eq_bot_of_simple_nonab Sp8.exists_not_comm_H6
  have hZ' : Subgroup.center ↥(StatedSp 3 F) = ⊥ := by
    have h := Subgroup.map_center_eq e.symm
    rw [hZ] at h
    simp only [Subgroup.map_bot] at h
    exact h.symm
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ').trans
    QuotientGroup.quotientBot).toEquiv, Nat.card_congr e.toEquiv, card_H6]

variable [Finite X]

theorem good429_of_compShape
    {x : X} (h : CompShape F42CompType (MulAut.conj x)) :
    Good429 (Subgroup.centralizer ({x} : Set X)) := by
  set C := Subgroup.centralizer ({x} : Set X) with hCdef
  have hfix : fixSubgroup (MulAut.conj x) = C := fixSubgroup_conj x
  intro K hKC hKp hKs hT
  haveI := hKp
  set T := K ⧸ CFSG.pCore 2 K
  haveI : Group.IsPerfect T := inferInstance
  haveI hTs : IsSimpleGroup T := isSimpleGroup_of_isType429 hT
  haveI : Nontrivial T := nontrivial_of_isType429 hT
  have hcompN : ∀ L : Subgroup X, CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) →
      ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro L hL g hg l hl
    have hcomm : MulAut.conj g * MulAut.conj x = MulAut.conj x * MulAut.conj g := by
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp hg)]
    have hmap := h.norm (MulAut.conj g) hcomm L hL
    have : (MulAut.conj g).toMonoidHom l ∈ L.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
    rw [hmap] at this
    exact this
  have hdich : ∀ L : Subgroup X, CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) →
      L ≤ K ∨ ∀ l ∈ L, ∀ k ∈ K, l * k = k * l := by
    intro L hL
    have hLC : L ≤ C := hfix ▸ hL.1
    have hLq : IsQuasisimple L := isQuasisimple_of_open hL.2.2
    set L' : Subgroup C := L.subgroupOf C
    have hL'n : L'.Normal := by
      constructor
      intro a ha g
      exact hcompN L hL g g.2 a ha
    have hL'c : IsComponent L' :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLC).symm hLq,
        hL'n.isSubnormal⟩
    rcases CFSG.LocalCores.component_subnormal_subgroup hL'c hKs with h1 | h1
    · left
      intro l hl
      have : (⟨l, hLC hl⟩ : C) ∈ K.subgroupOf C := h1 hl
      exact this
    · right
      intro l hl k hk
      have hmem : ⁅(⟨l, hLC hl⟩ : C), (⟨k, hKC hk⟩ : C)⁆ ∈ ⁅L', K.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator hl hk
      rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact congrArg Subtype.val hmem
  have hlay : K ≤ CFSG.Open.GLALayer (fixSubgroup (MulAut.conj x)) :=
    h.layer K (hfix ▸ hKC) (Subgroup.commutator_eq_self (H := K))
  obtain ⟨L, hL, hLK⟩ : ∃ L : Subgroup X,
      CFSG.Open.IsComponentOf L (fixSubgroup (MulAut.conj x)) ∧ L ≤ K := by
    by_contra hno
    push Not at hno
    have hcent : CFSG.Open.GLALayer (fixSubgroup (MulAut.conj x)) ≤
        Subgroup.centralizer (K : Set X) := by
      apply sSup_le
      rintro L hL
      rcases hdich L hL with h1 | h1
      · exact absurd h1 (hno L hL)
      · intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (h1 l hl k hk).symm
    have hab : ⁅K, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hlay.trans hcent)
    rw [Subgroup.commutator_eq_self] at hab
    haveI : Subsingleton K := by
      rw [hab]
      infer_instance
    haveI : Subsingleton T := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) |>.subsingleton
    exact not_subsingleton T inferInstance
  have hLq : IsQuasisimple L := isQuasisimple_of_open hL.2.2
  have hLC : L ≤ C := hfix ▸ hL.1
  set π : K →* T := QuotientGroup.mk' (CFSG.pCore 2 K)
  set ψ : L →* T := π.comp (Subgroup.inclusion hLK)
  have hψn : ψ.range.Normal := by
    constructor
    rintro _ ⟨l, rfl⟩ t
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) t
    refine ⟨⟨k * l * k⁻¹, hcompN L hL k (hKC k.2) l l.2⟩, ?_⟩
    show π (Subgroup.inclusion hLK _) = π k * π (Subgroup.inclusion hLK l) * (π k)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  haveI : Group.IsPerfect L := hLq.1
  haveI : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hLq
  have hψs : Function.Surjective ψ := by
    rcases hψn.eq_bot_or_eq_top with h1 | h1
    · exfalso
      have hker : ∀ l : L, ψ l = 1 := fun l => by
        have : ψ l ∈ ψ.range := ⟨l, rfl⟩
        rw [h1, Subgroup.mem_bot] at this
        exact this
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h2 : IsPGroup 2 L := by
        intro l
        have hl : (Subgroup.inclusion hLK l) ∈ CFSG.pCore 2 K := by
          rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 K)]
          exact hker l
        obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨_, hl⟩
        refine ⟨n, ?_⟩
        apply Subtype.ext
        have := congrArg (fun y : CFSG.pCore 2 K => ((y : K) : X)) hn
        simpa using this
      exact not_isPGroup_of_isPerfect h2
    · intro t
      have : t ∈ ψ.range := h1 ▸ Subgroup.mem_top t
      exact this
  have hkerZ : ψ.ker = Subgroup.center L := by
    have hZT : Subgroup.center T = ⊥ := by
      rcases (inferInstance : (Subgroup.center T).Normal).eq_bot_or_eq_top with h1 | h1
      · exact h1
      · exfalso
        have hcomm : ∀ a b : T, a * b = b * a := fun a b =>
          Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a
        have hab : ⁅(⊤ : Subgroup T), (⊤ : Subgroup T)⁆ = (⊥ : Subgroup T) := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro a _
          rw [Subgroup.mem_centralizer_iff]
          intro b _
          exact hcomm b a
        have htop : commutator T = ⊤ := Group.IsPerfect.commutator_eq_top
        rw [commutator_def, hab] at htop
        exact bot_ne_top htop
    refine le_antisymm ?_ ?_
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (MonoidHom.normal_ker ψ) with h1 | h1
      · exfalso
        have : ∀ t : T, t = 1 := by
          intro t
          obtain ⟨l, rfl⟩ := hψs t
          have : l ∈ ψ.ker := h1 ▸ Subgroup.mem_top l
          exact this
        exact not_subsingleton T ⟨fun a b => by rw [this a, this b]⟩
      · exact h1
    · intro z hz
      have hzc : ψ z ∈ Subgroup.center T := by
        rw [Subgroup.mem_center_iff]
        intro t
        obtain ⟨l, rfl⟩ := hψs t
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz l)]
      rw [hZT, Subgroup.mem_bot] at hzc
      exact hzc
  have eT : T ≃* L ⧸ Subgroup.center L :=
    ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm).trans
      (QuotientGroup.quotientMulEquivOfEq hkerZ)
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := h.type L hL
  have hcard : Nat.card T = 1451520 := by
    rw [Nat.card_congr (eT.trans f).toEquiv]
    exact card_statedSp_quot hF
  have hmem := card_mem_typeOrders (M := 1451520) (B := 114) (by norm_num) (by norm_num) hT
    hcard.dvd
  rw [hcard] at hmem
  exact absurd hmem (by decide +kernel)

end F4

section Row

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem good429_adjointF4
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) [Finite ↥(adjointGroup Tag.F4 K)]
    (x : ↥(adjointGroup Tag.F4 K)) (hx : orderOf x = 3) :
    Good429 (Subgroup.centralizer ({x} : Set ↥(adjointGroup Tag.F4 K))) :=
  F4.good429_of_compShape (compShape_conj_F4_two hK x hx)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem noCfgS429_f42
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* (TauCeti.CFSGIndex.lie CFSG.Assembly.RankThreeEven.f4TwoIndex).Group) :
    NoCfgS429 S := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := Item434F42.exists_model e
  haveI : Finite ↥(adjointGroup Tag.F4 K) := Finite.of_equiv S φ.toEquiv
  exact noCfgS429_of_model φ (center_eq_bot_of_simple_nonab hna)
    (Item434F42.not_three_dvd_card_outer e) (good429_adjointF4 hK)

theorem eight_F4 :
    RowSOf429 (TauCeti.CFSGIndex.lie CFSG.Assembly.RankThreeEven.f4TwoIndex).Group :=
  rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    exact noCfgS429_f42 hna e

end Row

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
