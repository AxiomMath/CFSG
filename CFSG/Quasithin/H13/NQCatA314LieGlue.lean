module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Rank2Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParDef

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
open CFSG.QuasithinUnique.Vol2Native.A312L Matrix
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

@[expose] def LieP (c : Prop) {G : Type} [Group G] (X : Subgroup G) : Prop :=
  IsAlt 5 (ModO2 X) → CharTwo X ∧ c

theorem LieP.of_equiv {c : Prop} {G G' : Type} [Group G] [Group G'] {X : Subgroup G}
    {X' : Subgroup G'} (e : ↥X ≃* ↥X') (h : LieP c X) : LieP c X' := by
  intro hA
  obtain ⟨φ⟩ := hA
  let e' : ModO2 X ≃* ModO2 X' := QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)
  obtain ⟨h1, h2⟩ := h ⟨e'.trans φ⟩
  exact ⟨CFSG.Quasithin.Rk2.charTwo_of_equiv e h1, h2⟩

theorem LieP.mono {c c' : Prop} {G : Type} [Group G] {X : Subgroup G} (hcc : c → c')
    (h : LieP c X) : LieP c' X := fun hA => ⟨(h hA).1, hcc (h hA).2⟩

theorem eq_two_of_card_eq_four {K : Type} {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (h : Nat.card K = 4) : f = 2 :=
  Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by rw [← hf, h])

theorem lieP_bot (c : Prop) {G : Type} [Group G] : LieP c (⊥ : Subgroup G) := by
  intro hA
  exfalso
  have h60 := A314.card_isAlt_five hA
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(⊥ : Subgroup G))
  rw [Subgroup.card_bot] at h1
  have h2 : Nat.card (ModO2 (⊥ : Subgroup G)) = 1 := Nat.eq_one_of_mul_eq_one_right h1.symm
  omega

theorem lieP_perfectCore_parabolic {c : Prop} {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S} (hP : ResidualOvergroupsAt S U P)
    (hPj : ∀ j, LieP c (perfectCore (P j))) {Pa : Subgroup S}
    (hpar : IsParabolic2 (⊤ : Subgroup S) Pa) (hne : Pa ≠ ⊤) : LieP c (perfectCore Pa) := by
  rcases CFSG.QuasithinUnique.A5.G3.perfectCore_parabolic_cases hU hP hpar hne with h | ⟨j, ⟨e⟩⟩
  · rw [h]
    exact lieP_bot c
  · exact (hPj j).of_equiv e.symm

theorem lieP_perfectCore_of_equiv {c : Prop} {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (e : X ≃* Y) {Pa : Subgroup X}
    (h : LieP c (perfectCore (Pa.map e.toMonoidHom))) : LieP c (perfectCore Pa) :=
  h.of_equiv (((perfectCore Pa).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_perfectCore e.toMonoidHom Pa))).symm

theorem lieP_perfectCore_of_subgroupOf {c : Prop} {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} (hP : IsParabolic2 L P) (hne : P ≠ L)
    (h : ∀ Pa : Subgroup ↥L, IsParabolic2 (⊤ : Subgroup ↥L) Pa → Pa ≠ ⊤ →
      LieP c (perfectCore Pa)) : LieP c (perfectCore P) := by
  have hPL : P ≤ L := hP.1
  have hmap : (P.subgroupOf L).map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  have hpar : IsParabolic2 (⊤ : Subgroup ↥L) (P.subgroupOf L) := by
    rw [A312.isParabolic2_top_iff, hmap]
    exact hP
  have hne' : P.subgroupOf L ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map L.subtype) htop
    rw [hmap, Subgroup.map_top, Subgroup.range_subtype] at this
    exact this
  have hcore : (perfectCore (P.subgroupOf L)).map L.subtype = perfectCore P := by
    rw [map_perfectCore, hmap]
  exact (h _ hpar hne').of_equiv (((perfectCore (P.subgroupOf L)).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hcore))

theorem lieP_perfectCore_subgroupOf_of {c : Prop} {G : Type} [Group G] [Finite G]
    {C P : Subgroup G} (hPC : P ≤ C) (h : LieP c (perfectCore P)) :
    LieP c (perfectCore (P.subgroupOf C)) := by
  have hcore : (perfectCore (P.subgroupOf C)).map C.subtype = perfectCore P := by
    rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hPC]
  exact h.of_equiv (((perfectCore (P.subgroupOf C)).equivMapOfInjective C.subtype
    C.subtype_injective).trans (MulEquiv.subgroupCongr hcore)).symm

theorem lieP_of_hom {c : Prop} {G : Type} [Group G] {X : Subgroup G} {M : Type} [Group M]
    [Finite M] [IsSimpleGroup M] (hnab : ∃ a b : M, a * b ≠ b * a) (g : ↥X →* M)
    (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker)
    (h60 : IsAlt 5 (ModO2 X) → Nat.card M = 60 → CharTwo X ∧ c) : LieP c X := by
  intro hA
  apply h60 hA
  have hpc : CFSG.pCore 2 ↥X = g.ker := pCore_two_eq_ker hnab g hg hker
  let e : ModO2 X ≃* M :=
    (QuotientGroup.quotientMulEquivOfEq hpc).trans (QuotientGroup.quotientKerEquivOfSurjective g hg)
  rw [← Nat.card_congr e.toEquiv]
  exact A314.card_isAlt_five hA

theorem card_field_eq_four_of_card_sl2 {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F)
    (h : Nat.card (SpecialLinearGroup (Fin 2) F) = 60) : Nat.card F = 4 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h
  by_contra hne
  have h5 : 5 ≤ Nat.card F := by omega
  have h24 : 24 ≤ Nat.card F ^ 2 - 1 := by
    have : 25 ≤ Nat.card F ^ 2 := by nlinarith
    omega
  have : 5 * 24 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h5 h24
  omega

theorem lieP_of_sl2 {c : Prop} {G : Type} [Group G] {X : Subgroup G} {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) (g : ↥X →* SpecialLinearGroup (Fin 2) F)
    (hg : Function.Surjective g) (hker : IsPGroup 2 g.ker)
    (h4 : IsAlt 5 (ModO2 X) → Nat.card F = 4 → CharTwo X ∧ c) : LieP c X := by
  have hK4 : ∃ s : Finset F, s.card = 4 := exists_finset_card_four hF4
  have := sl2_isSimple hK4
  exact lieP_of_hom (sl2_nonabelian hK4) g hg hker fun hA h60 =>
    h4 hA (card_field_eq_four_of_card_sl2 hF4 h60)

theorem charTwo_of_parabolicFacts {G : Type} [Group G] [Finite G] {P Q : Subgroup G}
    (hF : CFSG.QuasithinUnique.Vol2Native.L239.Lie.ParabolicFacts P Q)
    (hA : IsAlt 5 (ModO2 (perfectCore P))) : CharTwo (perfectCore P) := by
  have hnorm : P ≤ Subgroup.normalizer (perfectCore P : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hn := perfectCore_normal P
    constructor
    · intro hy
      have h1 := hn.conj_mem ⟨y, perfectCore_le P hy⟩ (Subgroup.mem_subgroupOf.mpr hy) ⟨x, hx⟩
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hy
      have h1 := hn.conj_mem ⟨x * y * x⁻¹, perfectCore_le P hy⟩ (Subgroup.mem_subgroupOf.mpr hy)
        ⟨x⁻¹, P.inv_mem hx⟩
      have h2 := Subgroup.mem_subgroupOf.mp h1
      simpa [mul_assoc] using h2
  rcases hF.levi with hle | ⟨hQ, -⟩
  · exfalso
    have hp : IsPGroup 2 ↥(perfectCore P) :=
      hF.pGroup.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hs : Group.IsSolvable ↥(perfectCore P) := by
      have := hp.isNilpotent
      infer_instance
    have hbot : perfectCore (perfectCore P) = ⊥ :=
      (isSolvable_iff_perfectCore_eq_bot (perfectCore P)).mp hs
    rw [perfectCore_eq_self_of_perfect (perfectCore_perfect P)] at hbot
    have := lieP_bot False (G := G)
    rw [← hbot] at this
    exact (this hA).2
  · have hQP : Q ≤ perfectCore P := by
      refine hQ.trans ?_
      rw [Subgroup.commutator_le]
      intro q hq x hx
      have hxq : q * x * q⁻¹ ∈ perfectCore P :=
        (Subgroup.mem_normalizer_iff.mp (hnorm (hF.le hq)) x).mp hx
      have : q * x * q⁻¹ * x⁻¹ ∈ perfectCore P := mul_mem hxq (inv_mem hx)
      simpa [commutatorElement_def] using this
    have hQc : Q ≤ pCoreOf 2 (perfectCore P) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQP
        ((perfectCore_le P).trans hF.normalizes) hF.pGroup
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hQc) hx.2
    exact hQc (hF.selfCentralizing ⟨perfectCore_le P hx.1, hxC⟩)

theorem generalizedFitting_eq_of_charTwo {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (h : CharTwo X) : CFSG.generalizedFitting ↥X = CFSG.pCore 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [charTwo_iff_internal] at h
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥X 2).mp h

end CFSG.Quasithin.H13.NQCat.A314D
