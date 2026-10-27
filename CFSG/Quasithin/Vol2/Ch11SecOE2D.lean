module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.EmptyFaithful.LRed3FourB
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.Quasithin.H13.VolIAltCoverG2Field
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj
public import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE2

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem card_zornO0 (K : Type) [Field K] [Finite K] : Nat.card ↥(zornO0 K) = Nat.card K ^ 7 := by
  have e : ↥(zornO0 K) ≃ K × (Fin 3 → K) × (Fin 3 → K) :=
    { toFun := fun x => ((Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1,
        (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.1,
        (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).2.2.1)
      invFun := fun y => ⟨Multiplicative.ofAdd (y.1, y.2.1, y.2.2, -y.1),
        show y.1 + -y.1 = 0 from add_neg_cancel y.1⟩
      left_inv := fun x => by
        obtain ⟨x, hx⟩ := x
        have hx' : (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2.2.2 = 0 := hx
        apply Subtype.ext
        show Multiplicative.ofAdd ((Multiplicative.toAdd x).1, (Multiplicative.toAdd x).2.1,
          (Multiplicative.toAdd x).2.2.1, -(Multiplicative.toAdd x).1) = x
        rw [neg_eq_of_add_eq_zero_right hx']
        rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin]
  ring

theorem card_zornR (K : Type) [Field K] : Nat.card ↥(zornR K) = Nat.card K := by
  have e : K ≃ ↥(zornR K) :=
    { toFun := fun c => ⟨Multiplicative.ofAdd (c, 0, 0, c), ⟨c, rfl⟩⟩
      invFun := fun x => (Multiplicative.toAdd (x : Multiplicative (quasithinZorn K))).1
      left_inv := fun _ => rfl
      right_inv := fun x => by
        obtain ⟨y, c, hc⟩ := x
        apply Subtype.ext
        show Multiplicative.ofAdd ((Multiplicative.toAdd y).1, 0, 0, (Multiplicative.toAdd y).1) = y
        rw [hc]
        exact Multiplicative.toAdd.injective hc.symm }
  exact (Nat.card_congr e).symm

theorem zornR_le_zornO0 (K : Type) [Field K] [CharP K 2] : zornR K ≤ zornO0 K := by
  rintro x ⟨c, hc⟩
  show (Multiplicative.toAdd x).1 + (Multiplicative.toAdd x).2.2.2 = 0
  rw [hc]
  exact CharTwo.add_self_eq_zero c

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem index_eq_of_g2NaturalDerived {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {Z : Subgroup V} (h : G2NaturalDerived H ⊤ Z 1) : Z.index = 2 ^ 6 := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have := charP_two_of_card hK
  let β₀ : V →* ↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K) :=
    β.comp Subgroup.topEquiv.symm.toMonoidHom
  have hβ₀s : Function.Surjective β₀ := fun y => by
    obtain ⟨u, hu⟩ := hβs y
    exact ⟨u, hu⟩
  have hker : β₀.ker = Z := by
    ext u
    exact hβk (Subgroup.topEquiv.symm u)
  have h1 : Z.index = Nat.card (↥(zornO0 K) ⧸ (zornR K).subgroupOf (zornO0 K)) := by
    rw [← hker, Subgroup.index]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β₀ hβ₀s).toEquiv
  have h2 := Subgroup.card_mul_index ((zornR K).subgroupOf (zornO0 K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zornR_le_zornO0 K)).toEquiv, card_zornR,
    card_zornO0, hK2, Subgroup.index] at h2
  rw [h1]
  omega

theorem isG2Block_of_partial {G : Type} [Group G] {L : Subgroup G} (h : H13.IsG2Block L) :
    CFSG.Quasithin.IsG2BlockPartial L := by
  obtain ⟨hshort, ⟨K, _, _, hK, ⟨e⟩⟩, hcomm, hN⟩ := h
  have hidx := index_eq_of_g2NaturalDerived hN
  refine ⟨hshort, ?_, hidx⟩
  obtain ⟨eP⟩ := lred3_equiv_g2derived_psu33 hK
  have hK9 : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hne : ((3 : ℕ), 3 ^ 1) ≠ (3, 2) := fun h => absurd (congrArg Prod.snd h) (by norm_num)
  exact ⟨⟨Nat.prime_three, le_rfl, le_rfl, hne⟩, GaloisField 3 (2 * 1), inferInstance,
    inferInstance, hK9, ⟨e.trans eP.symm⟩⟩

private theorem oe2_g2Derived_two_le :
    ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ ≤ quasithinG2 (ZMod 2) :=
  (CFSG.Quasithin.H13.VolI.g2Derived_le (ZMod 2)).trans
    (CFSG.Quasithin.G11.P3G2.quasithinG2_eq_cayleyGroup (K := ZMod 2)).symm.le

private theorem realizes_zmod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 1)
    {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {Z : Subgroup V}
    (h : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes H ⊤ Z) :
    (FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆).Realizes H ⊤ Z := by
  obtain ⟨π, hπ⟩ := h
  have hcp : CharP K 2 := charP_two_of_card hK
  letI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  let τ : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ :=
    CFSG.Quasithin.H13.VolI.g2DerivedFieldEquiv ε
  obtain ⟨hπs, hZU, -, hUi, hZi, hsec, -, β₀, hβs, hβk, hβe⟩ := hπ
  unfold FFModel.Realizes
  refine ⟨π.comp τ.symm.toMonoidHom, ?_⟩
  unfold FFModel.RealizesVia
  refine ⟨hπs.comp τ.symm.surjective, hZU, ?_, hUi, hZi, ?_, ?_, ?_⟩
  · exact CFSG.Quasithin.zornR_le_zornO0
  · intro γ m hm
    exact CFSG.Quasithin.zornAct_mem_O0 _ oe2_g2Derived_two_le γ hm
  · intro γ m hm
    exact CFSG.Quasithin.zornAct_mem_R _ oe2_g2Derived_two_le γ hm
  refine ⟨(CFSG.Quasithin.H13.VolI.zornQSecEquiv ε).toMonoidHom.comp β₀, ?_, ?_, ?_⟩
  · exact (CFSG.Quasithin.H13.VolI.zornQSecEquiv ε).surjective.comp hβs
  · intro u
    show CFSG.Quasithin.H13.VolI.zornQSecEquiv ε (β₀ u) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact hβk u
  · intro γ' u m hu hm hβm
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β₀ u)
    have hm0 : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act (τ.symm γ') m₀.1 ∈
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec :=
      hsec (τ.symm γ') m₀.1 m₀.2
    have h1 := hβe (τ.symm γ') u m₀ (Subgroup.mem_top _) hm0 hm₀.symm
    have h2 : CFSG.Quasithin.H13.VolI.zornQSecEquiv ε (QuotientGroup.mk m₀) =
        QuotientGroup.mk m := by
      rw [hm₀]
      exact hβm
    have h3 := CFSG.Quasithin.H13.VolI.zornQSecEquiv_act ε (τ.symm γ') γ'
      (τ.apply_symm_apply γ') m₀ m h2 hm0 hm
    exact (congrArg (CFSG.Quasithin.H13.VolI.zornQSecEquiv ε) h1).trans h3

private theorem le_normalizer_blockU_any {G : Type} [Group G] (L : Subgroup G) :
    L ≤ Subgroup.normalizer (CFSG.QuasithinUnique.blockU L : Set G) := by
  intro g hg
  rw [← CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer, CFSG.QuasithinUnique.blockU,
    CFSG.QuasithinUnique.C5.conjSubgroup_commutator,
    CFSG.QuasithinUnique.C5.conjSubgroup_eq_self
      (show g ∈ Subgroup.normalizer (CFSG.QuasithinUnique.blockQ L : Set G) from
        CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L hg),
    CFSG.QuasithinUnique.C5.conjSubgroup_eq_self (Subgroup.le_normalizer hg)]

private theorem isSimpleGroup_of_isPSU33 {X : Type} [Group X]
    (h : CFSG.Quasithin.IsPSU 3 3 1 X) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSU) (n := 3) (p := 3)
    (f := 1) (by decide) (Or.inl ⟨by decide, h⟩)

private theorem isG2BlockNatural_of_realizes {G : Type} [Group G] {L : Subgroup G}
    (hshort : CFSG.QuasithinUnique.IsShort2 L)
    (hsimp : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    [IsMulCommutative ↥(CFSG.QuasithinUnique.blockU L)]
    (hreal : (FFModel.zornQ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆).Realizes
      (autOn L (CFSG.QuasithinUnique.blockU L)) ⊤
      ((CFSG.QuasithinUnique.blockZ L).subgroupOf (CFSG.QuasithinUnique.blockU L))) :
    CFSG.Quasithin.IsG2BlockNatural L := by
  have hLN : L ≤ Subgroup.normalizer (CFSG.QuasithinUnique.blockU L : Set G) :=
    le_normalizer_blockU_any L
  obtain ⟨π, hπ⟩ := hreal
  have hinj : Function.Injective π :=
    CFSG.Quasithin.FFC.injective_of_faithful_sec
      (CFSG.Quasithin.FFC.zornQ_faithful _ oe2_g2Derived_two_le) hπ
  obtain ⟨hπs, -, -, -, -, hsec, -, β₀, hβs, hβk, hβe⟩ := hπ
  let c : ↥L →* ↥(autOn L (CFSG.QuasithinUnique.blockU L)) :=
    ((CFSG.Quasithin.conjAct (CFSG.QuasithinUnique.blockU L)).comp
      (Subgroup.inclusion hLN)).codRestrict _
      (fun ℓ => ⟨⟨ℓ, hLN ℓ.2⟩, Subgroup.mem_subgroupOf.mpr ℓ.2, rfl⟩)
  have c_apply : ∀ (ℓ : ↥L) (u : ↥(CFSG.QuasithinUnique.blockU L)),
      ((((c ℓ : ↥(autOn L (CFSG.QuasithinUnique.blockU L))) :
        MulAut ↥(CFSG.QuasithinUnique.blockU L)) u : ↥(CFSG.QuasithinUnique.blockU L)) : G) =
        (ℓ : G) * (u : G) * (ℓ : G)⁻¹ := fun _ _ => rfl
  have hcsurj : Function.Surjective c := by
    rintro ⟨φ, hφ⟩
    obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.mp hφ
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxφ⟩
  have hc_one : ∀ ℓ : ↥L, c ℓ = 1 ↔
      ∀ u : ↥(CFSG.QuasithinUnique.blockU L), (ℓ : G) * (u : G) * (ℓ : G)⁻¹ = (u : G) := by
    intro ℓ
    constructor
    · intro h u
      have h1 := congrArg (fun φ : ↥(autOn L (CFSG.QuasithinUnique.blockU L)) =>
        ((φ : MulAut ↥(CFSG.QuasithinUnique.blockU L)) u : G)) h
      simpa [c_apply] using h1
    · intro h
      apply Subtype.ext
      rw [Subgroup.coe_one]
      apply MulEquiv.ext
      intro u
      rw [MulAut.one_apply]
      apply Subtype.ext
      rw [c_apply]
      exact h u
  have hQN : CFSG.pCore 2 ↥L ≤ c.ker := by
    intro q hq
    rw [MonoidHom.mem_ker, hc_one]
    intro u
    have hqQ : (q : G) ∈ CFSG.QuasithinUnique.blockQ L := Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_iff.mp (hshort.2.2.1.1 u.2).2 (q : G) hqQ)
  have hkerle : c.ker ≤ CFSG.pCore 2 ↥L := by
    have hnorm : (c.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
    rcases hsimp.eq_bot_or_eq_top_of_normal
        (c.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with hb | ht
    · intro ℓ hℓ
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ℓ ∈
          c.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
        Subgroup.mem_map_of_mem _ hℓ
      rw [hb, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff ℓ).mp h1
    · exfalso
      have hall : ∀ ℓ : ↥L, ℓ ∈ c.ker := by
        intro ℓ
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ℓ ∈
            c.ker.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
          rw [ht]
          exact Subgroup.mem_top _
        obtain ⟨n, hn, hqn⟩ := Subgroup.mem_map.mp h1
        have h2 : n⁻¹ * ℓ ∈ CFSG.pCore 2 ↥L := QuotientGroup.eq.mp hqn
        have h4 := c.ker.mul_mem hn (hQN h2)
        simpa using h4
      have hUZ : CFSG.QuasithinUnique.blockU L ≤ CFSG.QuasithinUnique.blockZ L := by
        intro u hu
        refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro ℓ hℓ
        have h1 := (hc_one ⟨ℓ, hℓ⟩).mp (MonoidHom.mem_ker.mp (hall ⟨ℓ, hℓ⟩))
        exact mul_inv_eq_iff_eq_mul.mp (h1 ⟨u, hu⟩)
      exact lt_irrefl _ (lt_of_lt_of_le hshort.2.2.2.2.1 hUZ)
  have hker : c.ker = CFSG.pCore 2 ↥L := le_antisymm hkerle hQN
  let e : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ ≃*
      ↥(autOn L (CFSG.QuasithinUnique.blockU L)) :=
    MulEquiv.ofBijective π ⟨hinj, hπs⟩
  let α : ↥L →* ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := e.symm.toMonoidHom.comp c
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    rw [← hker]
    ext ℓ
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact e.symm.map_eq_one_iff
  have hαsurj : Function.Surjective α := by
    intro x
    obtain ⟨ℓ, hℓ⟩ := hcsurj (e x)
    exact ⟨ℓ, by
      show e.symm (c ℓ) = x
      rw [hℓ, MulEquiv.symm_apply_apply]⟩
  let β := β₀.comp
    (Subgroup.topEquiv.symm : ↥(CFSG.QuasithinUnique.blockU L) ≃*
      ↥(⊤ : Subgroup ↥(CFSG.QuasithinUnique.blockU L))).toMonoidHom
  have hβsurj : Function.Surjective β := hβs.comp (MulEquiv.surjective _)
  have hβker : β.ker =
      (CFSG.QuasithinUnique.blockZ L).subgroupOf (CFSG.QuasithinUnique.blockU L) := by
    ext u
    rw [MonoidHom.mem_ker]
    exact hβk (Subgroup.topEquiv.symm u)
  refine ⟨α, hαsurj, hαker, β, hβsurj, hβker, ?_⟩
  intro ℓ u v rep hv hu
  have hm := hsec (α ℓ) rep.1 rep.2
  have hγ : π (α ℓ) = c ℓ := e.apply_symm_apply (c ℓ)
  have hvu : ((π (α ℓ) : ↥(autOn L (CFSG.QuasithinUnique.blockU L))) :
      MulAut ↥(CFSG.QuasithinUnique.blockU L)) u = v := by
    rw [hγ]
    apply Subtype.ext
    rw [c_apply]
    exact hv.symm
  have key := hβe (α ℓ) ⟨u, Subgroup.mem_top u⟩ rep (Subgroup.mem_top _) hm hu
  refine ⟨⟨_, hm⟩, rfl, ?_⟩
  show β₀ (Subgroup.topEquiv.symm v) = _
  have hv' : (Subgroup.topEquiv.symm v : ↥(⊤ : Subgroup ↥(CFSG.QuasithinUnique.blockU L))) =
      ⟨((π (α ℓ) : ↥(autOn L (CFSG.QuasithinUnique.blockU L))) :
        MulAut ↥(CFSG.QuasithinUnique.blockU L)) u, Subgroup.mem_top _⟩ :=
    Subtype.ext hvu.symm
  rw [hv']
  exact key

theorem isG2Block_of {G : Type} [Group G] {L : Subgroup G} (h : H13.IsG2Block L) :
    CFSG.Quasithin.IsG2Block L := by
  obtain ⟨hshort, hquotient, hindex⟩ := isG2Block_of_partial h
  refine ⟨hshort, hquotient, hindex, ?_⟩
  obtain ⟨-, -, ⟨hcomm, hN⟩⟩ := h
  obtain ⟨K, hKf, hKfin, hK, hreal⟩ := hN
  exact isG2BlockNatural_of_realizes hshort (isSimpleGroup_of_isPSU33 hquotient)
    (realizes_zmod_two hK hreal)

theorem exists_sl2_of_lieModel {X : Type} [Group X] {n : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSL 2 2 n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hc
    have := charP_two_of_card hcard
    exact ⟨K, hK, hKf, hcard, ⟨e.trans (Setup.Family.statedProjSL_two_equiv K)⟩⟩
  all_goals exact absurd ht (by decide)

theorem nonempty_sl_of_lieModel {X : Type} [Group X] {d : ℕ}
    (h : CFSG.Blueprint.LieModel X .PSL d 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) := by
  rcases h with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := hc
    exact ⟨e.trans (Setup.Family.statedProjSL_equiv_of_card_two d K (by rw [hcard]; norm_num))⟩
  all_goals exact absurd ht (by decide)

end CFSG.Quasithin.Vol2.Ch11.OE2
