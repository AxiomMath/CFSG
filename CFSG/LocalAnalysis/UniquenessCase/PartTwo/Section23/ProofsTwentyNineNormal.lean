module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineDecomp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyNineInner
public import CFSG.GroupTheory.PerfectNormalConjugate

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

@[expose] noncomputable def calLJoin (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    Subgroup G :=
  ⨆ K ∈ calLOf D.T D.M (Subgroup.normalizer (c.L : Set G)), K

theorem L_le_calLJoin (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    c.L ≤ calLJoin D Ch c := by
  have hsub : CFSG.Open.IsSubnormal c.L (Subgroup.normalizer (c.L : Set G)) :=
    CFSG.Open.IsSubnormal.step (Subgroup.le_normalizer) Subgroup.normal_in_normalizer
      (CFSG.Open.IsSubnormal.refl _)
  exact le_iSup_of_le c.L (le_iSup_of_le ⟨c.hL.1, hsub⟩ le_rfl)

theorem calLJoin_le_normalizer_L (D : Data G) (Ch : Choice2011 G) (c : Ctx23L D Ch) :
    calLJoin D Ch c ≤ Subgroup.normalizer (c.L : Set G) :=
  iSup_le fun K => iSup_le fun hK => hK.2.le

theorem normalizer_calLJoin_eq_N (D : Data G) (Ch : Choice2011 G) (h208 : S20_8 D)
    (h1930 : H1930 D) (c : Ctx23L D Ch) :
    Subgroup.normalizer ((calLJoin D Ch c : Subgroup G) : Set G) = c.N := by
  have h1 := h208 h1930 c.L c.hL
  have hset : ({Subgroup.normalizer ((calLJoin D Ch c : Subgroup G) : Set G)} : Set (Subgroup G)) =
      {c.N} := h1.symm.trans c.hN
  exact Set.singleton_eq_singleton_iff.mp hset

theorem map_conj_calLJoin_eq (D : Data G) (Ch : Choice2011 G) (h208 : S20_8 D)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {g : G} (hg : g ∈ c.N) :
    (calLJoin D Ch c).map (MulAut.conj g).toMonoidHom = calLJoin D Ch c := by
  have hgX : g ∈ Subgroup.normalizer ((calLJoin D Ch c : Subgroup G) : Set G) := by
    rw [normalizer_calLJoin_eq_N D Ch h208 h1930 c]
    exact hg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgX

theorem conj_L_le (D : Data G) (Ch : Choice2011 G) (h208 : S20_8 D)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {g : G} (hg : g ∈ c.N) :
    c.L.map (MulAut.conj g).toMonoidHom ≤ c.N ∧
      c.L.map (MulAut.conj g).toMonoidHom ≤ calLJoin D Ch c ∧
      calLJoin D Ch c ≤
        Subgroup.normalizer ((c.L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hX := map_conj_calLJoin_eq D Ch h208 h1930 c hg
  refine ⟨?_, (Subgroup.map_mono (L_le_calLJoin D Ch c)).trans hX.le, ?_⟩
  · rintro x ⟨l, hl, rfl⟩
    exact c.N.mul_mem (c.N.mul_mem hg (sup_le_N D Ch c (Subgroup.mem_sup_left hl)))
      (c.N.inv_mem hg)
  · calc calLJoin D Ch c = (calLJoin D Ch c).map (MulAut.conj g).toMonoidHom := hX.symm
      _ ≤ (Subgroup.normalizer (c.L : Set G)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono (calLJoin_le_normalizer_L D Ch c)
      _ = Subgroup.normalizer ((c.L.map (MulAut.conj g).toMonoidHom) : Set G) :=
          Subgroup.map_equiv_normalizer_eq c.L (MulAut.conj g)

private theorem le_of_not_inf_le_pCoreOf (D : Data G) (Ch : Choice2011 G)
    (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {Lg : Subgroup G} (hLgX : Lg ≤ calLJoin D Ch c)
    (hXleNLg : calLJoin D Ch c ≤ Subgroup.normalizer (Lg : Set G))
    (hne : Lg ≠ c.L) (hcard : Nat.card Lg = Nat.card c.L)
    (hnot : ¬ c.L ⊓ Lg ≤ CFSG.Open.pCoreOf 2 c.L) : False := by
  classical
  let K : Subgroup G := c.L ⊓ Lg
  have hKleL : K ≤ c.L := inf_le_left
  have hKnormal : (K.subgroupOf c.L).Normal := by
    refine Subgroup.Normal.mk fun x hx l => ?_
    have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact c.L.mul_mem (c.L.mul_mem l.2 hxK.1) (c.L.inv_mem l.2)
    · exact (Subgroup.mem_normalizer_iff.mp (hXleNLg (L_le_calLJoin D Ch c l.2)) (x : G)).mp hxK.2
  obtain ⟨-, hL2, -⟩ := h23 h1930 c
  haveI : IsSimpleGroup (Bar2 c.L) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  have hsimple : IsSimpleGroup (↥c.L ⧸ CFSG.pCore 2 ↥c.L) := inferInstance
  haveI : (K.subgroupOf c.L).Normal := hKnormal
  rcases CFSG.GroupTheory.le_or_sup_eq_top_of_normal_of_isSimpleGroup_quotient
    (H := ↥c.L) (N := CFSG.pCore 2 ↥c.L) (K := K.subgroupOf c.L) hsimple with hle | hsup
  · exact hnot fun x hx => by
      have hxK : (⟨x, hx.1⟩ : ↥c.L) ∈ K.subgroupOf c.L := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hle hxK, rfl⟩
  · exfalso
    have hO2 : IsPGroup 2 (CFSG.pCore 2 ↥c.L) := CFSG.pCore_isPGroup
    let π : ↥c.L →* (↥c.L ⧸ K.subgroupOf c.L) := QuotientGroup.mk' (K.subgroupOf c.L)
    have hmap_top : (CFSG.pCore 2 ↥c.L).map π = ⊤ := by
      have h := congrArg (Subgroup.map π) hsup
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective π
        (QuotientGroup.mk'_surjective (K.subgroupOf c.L))] at h
      have hKbot : (K.subgroupOf c.L).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [hKbot, bot_sup_eq] at h
      exact h
    have hquotP : IsPGroup 2 (↥c.L ⧸ K.subgroupOf c.L) := by
      have hmapP : IsPGroup 2 ((CFSG.pCore 2 ↥c.L).map π) := hO2.map π
      rw [hmap_top] at hmapP
      letI : IsPGroup 2 ↥(⊤ : Subgroup (↥c.L ⧸ K.subgroupOf c.L)) := hmapP
      exact IsPGroup.of_injective hmapP
        (Subgroup.topEquiv (G := ↥c.L ⧸ K.subgroupOf c.L)).symm.toMonoidHom
        (Subgroup.topEquiv (G := ↥c.L ⧸ K.subgroupOf c.L)).symm.injective
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hquotP
    have hidx : K.relIndex c.L = 2 ^ m := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card, hm]
    have hnorm : c.L ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKleL).mp hKnormal
    have hLleK : c.L ≤ K :=
      Subgroup.le_of_commutator_eq_self_of_relIndex_eq_prime_pow (D := K) (C := c.L)
        (H := c.L) (p := 2) (k := m) Nat.prime_two hKleL hnorm hidx le_rfl c.hL.1.2.1
    have hLe : c.L ≤ Lg := fun x hx => (Subgroup.mem_inf.mp (hLleK hx)).2
    exact hne (Subgroup.eq_of_le_of_card_ge hLe (le_of_eq hcard)).symm

private theorem inf_le_pCoreOf_of_ne (D : Data G) (Ch : Choice2011 G)
    (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D) (c : Ctx23L D Ch) {g : G}
    (hg : g ∈ c.N) (hne : c.L.map (MulAut.conj g).toMonoidHom ≠ c.L) :
    c.L ⊓ c.L.map (MulAut.conj g).toMonoidHom ≤ CFSG.Open.pCoreOf 2 c.L := by
  classical
  let Lg : Subgroup G := c.L.map (MulAut.conj g).toMonoidHom
  obtain ⟨-, hLgX, hXleNLg⟩ := conj_L_le D Ch h208 h1930 c hg
  have hcard : Nat.card Lg = Nat.card c.L :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  by_contra hnot
  exact le_of_not_inf_le_pCoreOf D Ch h23 h1930 c hLgX hXleNLg
    (by simpa [Lg] using hne) hcard hnot

theorem commutator_le_inf (D : Data G) (Ch : Choice2011 G) (h208 : S20_8 D)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {g : G} (hg : g ∈ c.N) :
    ⁅c.L, c.L.map (MulAut.conj g).toMonoidHom⁆ ≤
      c.L ⊓ c.L.map (MulAut.conj g).toMonoidHom := by
  classical
  let Lg : Subgroup G := c.L.map (MulAut.conj g).toMonoidHom
  have hLleX : c.L ≤ calLJoin D Ch c := L_le_calLJoin D Ch c
  have hXleNL : calLJoin D Ch c ≤ Subgroup.normalizer (c.L : Set G) :=
    calLJoin_le_normalizer_L D Ch c
  obtain ⟨-, hLgX, hXleNLg⟩ := conj_L_le D Ch h208 h1930 c hg
  refine (Subgroup.commutator_le (H₁ := c.L) (H₂ := Lg)
    (H₃ := c.L ⊓ Lg)).mpr fun l hl y hy => ?_
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hyX : y ∈ calLJoin D Ch c := hLgX hy
    have hyconj : y * l⁻¹ * y⁻¹ ∈ c.L :=
      (Subgroup.mem_normalizer_iff.mp (hXleNL hyX) l⁻¹).mp (c.L.inv_mem hl)
    rw [commutatorElement_def,
      show l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) from by group]
    exact c.L.mul_mem hl hyconj
  · have hlX : l ∈ calLJoin D Ch c := hLleX hl
    have hconj : l * y * l⁻¹ ∈ Lg :=
      (Subgroup.mem_normalizer_iff.mp (hXleNLg hlX) y).mp hy
    rw [commutatorElement_def,
      show l * y * l⁻¹ * y⁻¹ = (l * y * l⁻¹) * y⁻¹ from by group]
    exact Lg.mul_mem hconj (Lg.inv_mem hy)

private theorem alpha_conj_eq {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {y l : G} (hyL : y ∈ Subgroup.normalizer (c.L : Set G))
    (hl : l ∈ c.L) (hcomm : ⁅l, y⁆ ∈ Subgroup.centralizer (c.V : Set G)) :
    B.κ.α ⟨y * l * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyL l).mp hl⟩ =
      B.κ.α ⟨l, hl⟩ := by
  have hyLconj : y * l * y⁻¹ ∈ c.L := (Subgroup.mem_normalizer_iff.mp hyL l).mp hl
  have hcommL : ⁅y, l⁆ ∈ c.L := by
    rw [commutatorElement_def]
    exact c.L.mul_mem hyLconj (c.L.inv_mem hl)
  have hcommC : ⁅y, l⁆ ∈ Subgroup.centralizer (c.V : Set G) := by
    rw [← commutatorElement_inv (g₁ := l) (g₂ := y)]
    exact (Subgroup.centralizer (c.V : Set G)).inv_mem hcomm
  have hker : B.κ.α ⟨⁅y, l⁆, hcommL⟩ = 1 := by
    rw [← MonoidHom.mem_ker, B.hker_eq, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨hcommL, hcommC⟩
  have hdecomp : y * l * y⁻¹ = ⁅y, l⁆ * l := by
    rw [commutatorElement_def]
    group
  have hsub : (⟨y * l * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyL l).mp hl⟩ : ↥c.L) =
      ⟨⁅y, l⁆, hcommL⟩ * ⟨l, hl⟩ := Subtype.ext hdecomp
  rw [hsub, map_mul, hker, one_mul]

private theorem phiAdd_comm_alpha {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {y l : G} (hyN : y ∈ c.N)
    (hyNL : y ∈ Subgroup.normalizer (c.L : Set G)) (hl : l ∈ c.L)
    (hcomm : ⁅l, y⁆ ∈ Subgroup.centralizer (c.V : Set G)) (v : Fin 2 → B.κ.K) :
    B2Data.phiAdd B y hyN
        ((B.κ.α ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) B.κ.K) *ᵥ v) =
      (B.κ.α ⟨l, hl⟩ : Matrix (Fin 2) (Fin 2) B.κ.K) *ᵥ
        B2Data.phiAdd B y hyN v := by
  rw [B2Data.phiAdd_mulVec B y hyN hyNL ⟨l, hl⟩ v]
  rw [alpha_conj_eq B hyNL hl hcomm]

private theorem exists_scalar_phiAdd {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {Lg : Subgroup G} (hLgN : Lg ≤ c.N)
    (hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G))
    (hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G)) {y : G} (hy : y ∈ Lg) :
    ∃ lam : B.κ.K, ∀ v, B2Data.phiAdd B y (hLgN hy) v = lam • v := by
  refine CFSG.Quasithin.H13.exists_eq_smul_of_commute (B2Data.phiAdd B y (hLgN hy)) ?_
  intro A v
  obtain ⟨l, rfl⟩ := B.κ.α_surj A
  exact phiAdd_comm_alpha B (hLgN hy) (hLgNL hy) l.2
    (Subgroup.commutator_le.mp hcommC (l : G) l.2 y hy) v

private noncomputable def scalarOf {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {Lg : Subgroup G} (hLgN : Lg ≤ c.N)
    (hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G))
    (hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G)) (y : ↥Lg) : B.κ.K :=
  Classical.choose (exists_scalar_phiAdd B hLgN hLgNL hcommC y.2)

private theorem scalarOf_spec {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {Lg : Subgroup G} (hLgN : Lg ≤ c.N)
    (hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G))
    (hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G)) (y : ↥Lg)
    (v : Fin 2 → B.κ.K) :
    B2Data.phiAdd B (y : G) (hLgN y.2) v = scalarOf B hLgN hLgNL hcommC y • v :=
  Classical.choose_spec (exists_scalar_phiAdd B hLgN hLgNL hcommC y.2) v

private theorem scalarOf_ne_zero {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {Lg : Subgroup G} (hLgN : Lg ≤ c.N)
    (hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G))
    (hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G)) (y : ↥Lg) :
    scalarOf B hLgN hLgNL hcommC y ≠ 0 := by
  intro h0
  have hz : B2Data.phiAdd B (y : G) (hLgN y.2) B.e = 0 := by
    rw [scalarOf_spec B hLgN hLgNL hcommC y B.e, h0, zero_smul]
  have hinj : B.e = 0 := (B2Data.phiAdd B (y : G) (hLgN y.2)).injective (by rw [hz, map_zero])
  exact B.e_ne_zero hinj

private theorem scalarOf_mul {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {Lg : Subgroup G} (hLgN : Lg ≤ c.N)
    (hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G))
    (hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G)) (y z : ↥Lg) :
    scalarOf B hLgN hLgNL hcommC (y * z) =
      scalarOf B hLgN hLgNL hcommC y * scalarOf B hLgN hLgNL hcommC z := by
  have h1 : ∀ v : Fin 2 → B.κ.K, B2Data.phiAdd B ((y * z : ↥Lg) : G) (hLgN (y * z).2) v =
      B2Data.phiAdd B (y : G) (hLgN y.2) (B2Data.phiAdd B (z : G) (hLgN z.2) v) := by
    intro v
    have hproof : hLgN (y * z).2 = c.N.mul_mem (hLgN y.2) (hLgN z.2) := Subsingleton.elim _ _
    have hmul' : B2Data.phiAdd B ((y : G) * (z : G)) (c.N.mul_mem (hLgN y.2) (hLgN z.2)) v =
        B2Data.phiAdd B (y : G) (hLgN y.2) (B2Data.phiAdd B (z : G) (hLgN z.2) v) := by
      rw [B2Data.phiAdd_mul B (y : G) (z : G) (hLgN y.2) (hLgN z.2)]
      rfl
    simpa [hproof] using hmul'
  have h2 : scalarOf B hLgN hLgNL hcommC (y * z) • B.e =
      (scalarOf B hLgN hLgNL hcommC y * scalarOf B hLgN hLgNL hcommC z) • B.e := by
    rw [← scalarOf_spec B hLgN hLgNL hcommC (y * z) B.e, h1,
      scalarOf_spec B hLgN hLgNL hcommC z B.e,
      scalarOf_spec B hLgN hLgNL hcommC y, smul_smul]
  have h3 : (scalarOf B hLgN hLgNL hcommC (y * z) -
      scalarOf B hLgN hLgNL hcommC y * scalarOf B hLgN hLgNL hcommC z) • B.e = 0 := by
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h B.e_ne_zero

private noncomputable def scalarChar {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch}
    (B : B2Data D Ch c) {Lg : Subgroup G} (hLgN : Lg ≤ c.N)
    (hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G))
    (hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G)) : ↥Lg →* B.κ.Kˣ :=
  MonoidHom.mk' (fun y => Units.mk0 (scalarOf B hLgN hLgNL hcommC y)
    (scalarOf_ne_zero B hLgN hLgNL hcommC y)) fun y z => by
    apply Units.ext
    simpa using scalarOf_mul B hLgN hLgNL hcommC y z

private theorem le_centralizer_V_of_commutator_le (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {Lg : Subgroup G} (hLgN : Lg ≤ c.N)
    (hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G))
    (hLgperf : Group.IsPerfect ↥Lg)
    (hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G)) :
    Lg ≤ Subgroup.centralizer (c.V : Set G) := by
  classical
  obtain ⟨B⟩ := nonempty_b2Data D Ch c h4 h23 h1930
  letI : Group.IsPerfect ↥Lg := hLgperf
  let χ : ↥Lg →* B.κ.Kˣ := scalarChar B hLgN hLgNL hcommC
  haveI : Group.IsPerfect ↥χ.range := Group.IsPerfect.range χ
  haveI : IsMulCommutative ↥χ.range := inferInstance
  have hsub : Subsingleton ↥χ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  intro y hy
  have hχ : χ ⟨y, hy⟩ = 1 := by
    have h1 : (⟨χ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩ : ↥χ.range) = 1 := Subsingleton.elim _ _
    exact congrArg Subtype.val h1
  have hlam : scalarOf B hLgN hLgNL hcommC ⟨y, hy⟩ = 1 := by
    have := congrArg Units.val hχ
    simpa [χ, scalarChar] using this
  have hphi : ∀ v, B2Data.phiAdd B y (hLgN hy) v = v := by
    intro v
    rw [scalarOf_spec B hLgN hLgNL hcommC ⟨y, hy⟩ v, hlam, one_smul]
  exact mem_centralizer_V_of_phiAdd_eq_one B (hLgN hy) hphi

private theorem le_centralizer_V_of_map_conj_le (D : Data G) (Ch : Choice2011 G)
    (c : Ctx23L D Ch) {g : G} (hg : g ∈ c.N)
    (hLgC : c.L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (c.V : Set G)) :
    c.L ≤ Subgroup.centralizer (c.V : Set G) := by
  intro l hl
  have hy : g * l * g⁻¹ ∈ c.L.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
  have hyC := hLgC hy
  have hgV : g ∈ Subgroup.normalizer (c.V : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.N D.Z hg
  rw [Subgroup.mem_centralizer_iff] at hyC ⊢
  intro v hv
  have hv' : g * v * g⁻¹ ∈ c.V := (Subgroup.mem_normalizer_iff.mp hgV v).mp hv
  have hcomm := hyC (g * v * g⁻¹) hv'
  have hl_decomp : l = g⁻¹ * (g * l * g⁻¹) * g := by group
  have hv_decomp : v = g⁻¹ * (g * v * g⁻¹) * g := by group
  calc v * l = g⁻¹ * ((g * v * g⁻¹) * (g * l * g⁻¹)) * g := by
        rw [hl_decomp, hv_decomp]
        group
    _ = g⁻¹ * ((g * l * g⁻¹) * (g * v * g⁻¹)) * g := by rw [hcomm]
    _ = l * v := by
        rw [hl_decomp, hv_decomp]
        group

private theorem false_of_le_centralizer_V (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    (hLC : c.L ≤ Subgroup.centralizer (c.V : Set G)) : False := by
  classical
  obtain ⟨B⟩ := nonempty_b2Data D Ch c h4 h23 h1930
  have hker_top : B.κ.α.ker = ⊤ := by
    rw [B.hker_eq, show c.L ⊓ Subgroup.centralizer (c.V : Set G) = c.L from inf_eq_left.mpr hLC]
    simp
  have hα1 : B.κ.α = 1 := MonoidHom.ker_eq_top_iff.mp hker_top
  have hXne : CFSG.Quasithin.H13.sl2X (1 : B.κ.K) ≠ 1 := by
    intro h
    have := congrFun (congrFun (congrArg Subtype.val h) 0) 1
    simp [CFSG.Quasithin.H13.sl2X] at this
  obtain ⟨l, hl⟩ := B.κ.α_surj (CFSG.Quasithin.H13.sl2X (1 : B.κ.K))
  exact hXne (by rw [← hl, hα1]; rfl)

private theorem map_conj_eq_self_of_mem_N (D : Data G) (Ch : Choice2011 G)
    (h4 : S23_4 D Ch) (h23 : S23_23 D Ch) (h208 : S20_8 D) (h1930 : H1930 D)
    (c : Ctx23L D Ch) {g : G} (hg : g ∈ c.N) :
    c.L.map (MulAut.conj g).toMonoidHom = c.L := by
  classical
  let Lg : Subgroup G := c.L.map (MulAut.conj g).toMonoidHom
  by_contra hne
  obtain ⟨hLgN, hLgX, -⟩ := conj_L_le D Ch h208 h1930 c hg
  have hLgNL : Lg ≤ Subgroup.normalizer (c.L : Set G) :=
    hLgX.trans (calLJoin_le_normalizer_L D Ch c)
  have hLgperf : Group.IsPerfect ↥Lg := by
    rw [show Lg = c.L.map (MulAut.conj g).toMonoidHom from rfl]
    haveI : Group.IsPerfect ↥c.L := Subgroup.isPerfect_iff.mpr c.hL.1.2.1
    exact Group.IsPerfect.map (MulAut.conj g).toMonoidHom
  have hne' : c.L.map (MulAut.conj g).toMonoidHom ≠ c.L := by simpa [Lg] using hne
  have hK_le_O : c.L ⊓ c.L.map (MulAut.conj g).toMonoidHom ≤
      CFSG.Open.pCoreOf 2 c.L := inf_le_pCoreOf_of_ne D Ch h23 h208 h1930 c hg hne'
  have hcomm_inf : ⁅c.L, c.L.map (MulAut.conj g).toMonoidHom⁆ ≤
      c.L ⊓ c.L.map (MulAut.conj g).toMonoidHom := commutator_le_inf D Ch h208 h1930 c hg
  obtain ⟨B⟩ := nonempty_b2Data D Ch c h4 h23 h1930
  have hOcentral : CFSG.Open.pCoreOf 2 c.L ≤ Subgroup.centralizer (c.V : Set G) := by
    rw [Ctx23L.pCoreOf_L_eq D Ch h4 h23 h1930 c B.hV B.hLV B.κ]
    exact inf_le_right
  have hcommC : ⁅c.L, Lg⁆ ≤ Subgroup.centralizer (c.V : Set G) := by
    have hmap : ⁅c.L, c.L.map (MulAut.conj g).toMonoidHom⁆ ≤
        Subgroup.centralizer (c.V : Set G) := hcomm_inf.trans (hK_le_O.trans hOcentral)
    simpa [Lg] using hmap
  have hLgC : Lg ≤ Subgroup.centralizer (c.V : Set G) :=
    le_centralizer_V_of_commutator_le D Ch h4 h23 h1930 c hLgN hLgNL hLgperf hcommC
  have hLC : c.L ≤ Subgroup.centralizer (c.V : Set G) :=
    le_centralizer_V_of_map_conj_le D Ch c hg (by simpa [Lg] using hLgC)
  exact false_of_le_centralizer_V D Ch h4 h23 h1930 c hLC

theorem normal_L_N (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h23 : S23_23 D Ch)
    (h208 : S20_8 D) (h1930 : H1930 D) (c : Ctx23L D Ch) :
    (c.L.subgroupOf c.N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer
    (le_sup_left.trans (sup_le_N D Ch c))]
  intro g hg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_conj_eq_self_of_mem_N D Ch h4 h23 h208 h1930 c hg)

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
