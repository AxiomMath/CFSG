module

public import CFSG.GroupTheory.TwoElementSquare
public import CFSG.Quasithin.Vol2.Ch12Sec6L12TwoLeviNotL52
public import CFSG.Quasithin.Background.C35InspLeviAll
public import CFSG.GH74.GLS.Stage4.LocalSE
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Sec
public import CFSG.GroupTheory.SurjectiveRangeFactor

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint Subgroup
open scoped commutatorElement

theorem char2LeviFamily_tits {t : StatedLieTag} {n f : ℕ} (h : Char2LeviFamily t n f)
    (ht : t = StatedLieTag.Tits) : n = 0 ∧ f = 1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hn, hf⟩
  · exact absurd (h.symm.trans ht) (by decide)
  · exact absurd (h.symm.trans ht) (by decide)
  · exact absurd (h.symm.trans ht) (by decide)
  · exact absurd (h.symm.trans ht) (by decide)
  · exact absurd (h.symm.trans ht) (by decide)
  · exact absurd (h.symm.trans ht) (by decide)
  · exact ⟨hn, hf⟩

theorem false_of_solvable_of_surjective {H G : Type*} [Group H] [Group G] [IsSimpleGroup G]
    [Group.IsSolvable H] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (φ : H →* G) (hφ : Function.Surjective φ) : False := by
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr (Group.isSolvable_of_surjective hφ) a b)

theorem false_of_le_solvable_of_surjective {X H : Type*} [Group X] [Group H]
    [IsSimpleGroup H] (hnonab : ∃ a b : H, a * b ≠ b * a) {P Y : Subgroup X}
    (hYP : Y ≤ P) (hP : Group.IsSolvable ↥P) (φ : ↥Y →* H)
    (hφ : Function.Surjective φ) : False := by
  haveI : Group.IsSolvable ↥P := hP
  have hY : Group.IsSolvable ↥Y :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYP)
      (Subgroup.inclusion_injective hYP)
  haveI : Group.IsSolvable ↥Y := hY
  exact false_of_solvable_of_surjective hnonab φ hφ

theorem exists_quotient_modO2 {X H : Type} [Group X] [Finite X] [Group H] [IsSimpleGroup H]
    (hnonab : ∃ a b : H, a * b ≠ b * a) {P Y : Subgroup X}
    [((perfectCore P).subgroupOf P).Normal]
    (hYP : Y ≤ P) (φ : ↥Y →* H) (hφ : Function.Surjective φ)
    (hsolv : Group.IsSolvable (↥P ⧸ ((perfectCore P).subgroupOf P))) :
    ∃ Q : Subgroup (ModO2 (perfectCore P)),
      ∃ ψ : ↥Q →* H, Function.Surjective ψ := by
  haveI : Finite H := Finite.of_surjective φ hφ
  let g : ↥Y →* ↥P ⧸ ((perfectCore P).subgroupOf P) :=
    (QuotientGroup.mk' ((perfectCore P).subgroupOf P)).comp (Subgroup.inclusion hYP)
  have hgker : g.ker = (perfectCore P).subgroupOf Y := by
    ext y
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, g, MonoidHom.comp_apply,
      Subgroup.coe_inclusion, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff (Subgroup.inclusion hYP y)
  haveI : Group.IsSolvable (↥P ⧸ ((perfectCore P).subgroupOf P)) := hsolv
  have htop : ((perfectCore P).subgroupOf Y).map φ = ⊤ := by
    have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613.map_ker_eq_top_of_solvable
      (S := H) (fun hcomm => by
        obtain ⟨a, b, hab⟩ := hnonab
        exact hab (hcomm a b)) φ hφ g
    rwa [hgker] at h
  obtain ⟨ψ, hψ⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L613.exists_surjective_inf_of_map_eq_top φ htop
  let q : ↥(Y ⊓ perfectCore P) →* ModO2 (perfectCore P) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(perfectCore P))).comp
      (Subgroup.inclusion (inf_le_right : Y ⊓ perfectCore P ≤ perfectCore P))
  have hqker : q.ker = ((Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P)).subgroupOf
      (Y ⊓ perfectCore P) := by
    ext m
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥(perfectCore P))
        (⟨m.1, m.2.2⟩ : ↥(perfectCore P)) = 1) ↔
      m ∈ ((Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P)).subgroupOf (Y ⊓ perfectCore P)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf]
    constructor
    · intro hm
      refine ⟨m.2, ?_⟩
      exact Subgroup.mem_map.mpr ⟨⟨m.1, m.2.2⟩, hm, rfl⟩
    · intro hm
      obtain ⟨-, hmO⟩ := hm
      obtain ⟨o, ho, hoeq⟩ := Subgroup.mem_map.mp hmO
      have : (⟨m.1, m.2.2⟩ : ↥(perfectCore P)) = o := Subtype.ext hoeq.symm
      rwa [this]
  have hker_le : q.ker ≤ ψ.ker := by
    rw [hqker]
    have hO2 : IsPGroup 2 (pCoreOf 2 (perfectCore P)) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥(perfectCore P))).map (perfectCore P).subtype
    have hInf2 : IsPGroup 2 ↥((Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P)) :=
      hO2.to_inf_right
    have hX0normO : perfectCore P ≤
        Subgroup.normalizer (pCoreOf 2 (perfectCore P) : Set X) := by
      rw [← Subgroup.normal_subgroupOf_iff_le_normalizer
        (show pCoreOf 2 (perfectCore P) ≤ perfectCore P from Subgroup.map_subtype_le _)]
      rw [show (pCoreOf 2 (perfectCore P)).subgroupOf (perfectCore P) =
          CFSG.pCore 2 ↥(perfectCore P) by
        rw [pCoreOf, Subgroup.subgroupOf_map_subtype_eq_self]]
      exact CFSG.pCore_normal
    have hnormal : (((Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P)).subgroupOf
        (Y ⊓ perfectCore P)).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      intro m hm
      exact Subgroup.inf_normalizer_le_normalizer_inf
        (H := Y ⊓ perfectCore P) (K := pCoreOf 2 (perfectCore P))
        ⟨Subgroup.le_normalizer hm, hX0normO hm.2⟩
    haveI := hnormal
    have hmapN : ((((Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P)).subgroupOf
        (Y ⊓ perfectCore P)).map ψ).Normal :=
      Subgroup.Normal.map inferInstance ψ hψ
    have hmapP : IsPGroup 2 ((((Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P)).subgroupOf
        (Y ⊓ perfectCore P)).map ψ) :=
      hInf2.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        (Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P) ≤ Y ⊓ perfectCore P)).symm |>.map ψ
    haveI := hmapN
    have hbot := eq_bot_of_normal_isPGroup_of_isSimpleGroup hnonab hmapP
    intro m hm
    have hmψ : ψ m ∈ (((Y ⊓ perfectCore P) ⊓ pCoreOf 2 (perfectCore P)).subgroupOf
        (Y ⊓ perfectCore P)).map ψ := Subgroup.mem_map_of_mem ψ hm
    rw [hbot, Subgroup.mem_bot] at hmψ
    exact hmψ
  obtain ⟨ρ, hρ⟩ := CFSG.exists_surjective_range_of_ker_le q ψ hψ hker_le
  exact ⟨q.range, ρ, hρ⟩

theorem sq_eq_one_of_isPSL_two_two {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (hL : IsPSL 2 2 m X) : ∀ g : X, (∃ k : ℕ, g ^ 2 ^ k = 1) → g ^ 2 = 1 := by
  have hLie : LieModel X .PSL 2 2 m := Or.inl ⟨by decide, hL⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even hm hLie
  have hexp : ∀ S : Sylow 2 X, ∀ x ∈ (S : Subgroup X), x ^ 2 = 1 := by
    intro S x hx
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
    haveI : Finite (CFSG.Theory.Comparator.PSL2Model m) := Finite.of_equiv X e.toEquiv
    let S' : Sylow 2 (CFSG.Theory.Comparator.PSL2Model m) :=
      S.mapSurjective (f := e.toMonoidHom) e.surjective
    obtain ⟨f⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF S'
    have hchar : CharP (GaloisField 2 m) 2 :=
      CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hF
    haveI : CharP (GaloisField 2 m) 2 := hchar
    have hexp' : ∀ z : Multiplicative (GaloisField 2 m), z ^ 2 = 1 := by
      intro z
      obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective z
      rw [pow_two, ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero]
    have hx' : e x ∈ (S' : Subgroup (CFSG.Theory.Comparator.PSL2Model m)) := by
      simpa [S'] using Subgroup.mem_map_of_mem e.toMonoidHom hx
    have h1 : (⟨e x, hx'⟩ : ↥S') ^ 2 = 1 := by
      apply Subtype.ext
      have hz2 : (f (f.symm ⟨e x, hx'⟩)) ^ 2 = 1 := by
        rw [← map_pow, hexp', map_one]
      simpa using hz2
    apply e.injective
    simpa [map_pow] using congrArg Subtype.val h1
  intro g hg
  obtain ⟨k, hk⟩ := hg
  have hdvd : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hcard : Nat.card (Subgroup.zpowers g) = 2 ^ c := by
    rw [Nat.card_zpowers, hc]
  have hg2 : IsPGroup 2 (Subgroup.zpowers g) := IsPGroup.of_card (n := c) hcard
  obtain ⟨S, hle⟩ := IsPGroup.exists_le_sylow hg2
  exact hexp S g (hle (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))

theorem false_of_L2_of_surjective {X : Type} {H : Type*} [Group X] [Finite X] [Group H]
    (hH2 : ∃ g : H, (∃ k : ℕ, g ^ 2 ^ k = 1) ∧ g ^ 2 ≠ 1) {m : ℕ} (hm : 2 ≤ m)
    (hL : IsPSL 2 2 m X) {Q : Subgroup X}
    (ψ : ↥Q →* H) (hψ : Function.Surjective ψ) : False := by
  have hsqX : ∀ x : X, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ^ 2 = 1 :=
    sq_eq_one_of_isPSL_two_two hm hL
  obtain ⟨g, hg, hgne⟩ := hH2
  have hsqQ : ∀ y : ↥Q, (∃ k : ℕ, y ^ 2 ^ k = 1) → y ^ 2 ∈ ψ.ker := by
    intro y hy
    have hyX : ((y : X) ^ 2) = 1 := by
      obtain ⟨k, hk⟩ := hy
      exact hsqX (y : X) ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hyQ : y ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hyX
    rw [MonoidHom.mem_ker]
    simpa using congrArg ψ hyQ
  exact hgne (CFSG.sq_eq_one_of_surjective_of_sq_mem_ker ψ hψ hsqQ hg)

theorem false_of_sz_of_surjective {X : Type} {H : Type*} [Group X] [Finite X] [Group H]
    (hH3 : 3 ∣ Nat.card H) {m : ℕ} (h : IsSz m X)
    {Q : Subgroup X} (ψ : ↥Q →* H) (hψ : Function.Surjective ψ) : False := by
  obtain ⟨-, a, -, K, _, _, hfa, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hK
  have hcard : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK']
  have h3X : 3 ∣ Nat.card X :=
    hH3.trans ((Subgroup.card_dvd_of_surjective hψ).trans (Subgroup.card_subgroup_dvd_card Q))
  rw [hcard] at h3X
  exact CFSG.GH74.GLS.Stage4.not_three_dvd_suzuki_order a h3X

theorem false_of_L3_of_surjective {X : Type} {H : Type*} [Group X] [Finite X] [Group H]
    (hH168 : ¬ Nat.card H ∣ 168) (hL : IsPSL 3 2 1 X) {Q : Subgroup X}
    (ψ : ↥Q →* H) (hψ : Function.Surjective ψ) : False := by
  have hcard : Nat.card X = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hL
  have hdiv : Nat.card H ∣ Nat.card X :=
    (Subgroup.card_dvd_of_surjective hψ).trans (Subgroup.card_subgroup_dvd_card Q)
  rw [hcard] at hdiv
  exact hH168 hdiv

theorem false_of_char2LeviFamily_of_surjective
    {H : Type} [Group H] [IsSimpleGroup H] (hHc : ∃ a b : H, a * b ≠ b * a)
    (hH2 : ∃ g : H, (∃ k : ℕ, g ^ 2 ^ k = 1) ∧ g ^ 2 ≠ 1)
    (hH3 : 3 ∣ Nat.card H) (hH168 : ¬ Nat.card H ∣ 168)
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ} (hfam : Char2LeviFamily t n f)
    (hmodel : LieModel X t n 2 f) (S : Sylow 2 X) {P : Subgroup X} (hP : P ≠ ⊤)
    (hNS : t ≠ StatedLieTag.Tits → Subgroup.normalizer (S : Set X) ≤ P)
    (hTits : t = StatedLieTag.Tits → (S : Subgroup X) ≤ P)
    {Y : Subgroup X} (hYP : Y ≤ P) (φ : ↥Y →* H) (hφ : Function.Surjective φ) : False := by
  by_cases ht : t = StatedLieTag.Tits
  ·
    have hmodelTits : LieModel X .Tits n 2 f := ht ▸ hmodel
    obtain ⟨-, hTitsModel⟩ := hmodelTits.reeTitsModel
      (t := StatedLieTag.Tits) (by decide)
    obtain ⟨-, hf1⟩ := char2LeviFamily_tits hfam ht
    have hTitsX : IsTits X := by
      rw [IsTits, ← hf1]
      exact hTitsModel
    have hS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup X) ⊤ :=
      CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
    have hsolvP : Group.IsSolvable ↥P :=
      CFSG.Quasithin.C35Pf.solvOver_of_isTits hTitsX (S : Subgroup X) P hS (hTits ht) hP
    exact false_of_le_solvable_of_surjective hHc hYP hsolvP φ hφ
  ·
    have hsimple : IsSimpleGroup X := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hmodel
    haveI : IsSimpleGroup X := hsimple
    have hnoncomm : ∃ a b : X, a * b ≠ b * a := by
      by_contra h
      have hcomm : ∀ a b : X, a * b = b * a := by
        intro a b
        by_contra hab
        exact h ⟨a, b, hab⟩
      clear h
      have hnorm : Subgroup.normalizer (S : Set X) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        apply Subgroup.mem_normalizer_iff.mpr
        intro s
        constructor
        · intro hs
          rw [hcomm g s, mul_assoc, mul_inv_cancel, mul_one]
          exact hs
        · intro hs
          have hconj : g * s * g⁻¹ = s := by
            rw [hcomm g s, mul_assoc, mul_inv_cancel, mul_one]
          rwa [hconj] at hs
      have htop : P = ⊤ := le_antisymm le_top (hnorm ▸ hNS ht)
      exact hP htop
    have hcenter : Subgroup.center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnoncomm
        have hba : a * b = b * a := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
        exact hab hba
    have hcenterOf : centerOf (⊤ : Subgroup X) = Subgroup.center X := by
      rw [centerOf, top_inf_eq, Subgroup.coe_top, Subgroup.centralizer_univ]
    have hZ : IsPGroup 2 ↥(centerOf (⊤ : Subgroup X)) := by
      rw [hcenterOf, hcenter]
      exact IsPGroup.iff_card.2 ⟨0, by simp⟩
    have hcommX : _root_.commutator X = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator X) with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnoncomm
        have hmem : ⁅a, b⁆ ∈ _root_.commutator X := by
          rw [_root_.commutator_def]
          exact commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
        exact hab hmem
      · exact h
    have hcommTop : _root_.commutator ↥(⊤ : Subgroup X) = ⊤ := by
      let e : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [show _root_.commutator ↥(⊤ : Subgroup X) =
        ⁅(⊤ : Subgroup ↥(⊤ : Subgroup X)), ⊤⁆ from _root_.commutator_def _]
      rw [Subgroup.map_commutator (f := e.toMonoidHom)]
      rw [Subgroup.map_top_of_surjective (f := e.toMonoidHom) e.surjective]
      rw [← _root_.commutator_def]
      exact hcommX
    haveI : IsSimpleGroup ↥(⊤ : Subgroup X) := Subgroup.topEquiv.isSimpleGroup
    have hcentTop : Subgroup.center ↥(⊤ : Subgroup X) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.center ↥(⊤ : Subgroup X)) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnoncomm
        have hba : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup X)) *
            ⟨b, Subgroup.mem_top b⟩ =
            ⟨b, Subgroup.mem_top b⟩ * ⟨a, Subgroup.mem_top a⟩ :=
          Subgroup.mem_center_iff.mp
            (h ▸ Subgroup.mem_top (⟨b, Subgroup.mem_top b⟩ : ↥(⊤ : Subgroup X)))
            ⟨a, Subgroup.mem_top a⟩
        exact hab (by
          have := congrArg (fun z : ↥(⊤ : Subgroup X) => (z : X)) hba
          simpa using this)
    let eK : ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hcentTop).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
    haveI : IsSimpleGroup ((↥(⊤ : Subgroup X)) ⧸
        Subgroup.center ↥(⊤ : Subgroup X)) := eK.isSimpleGroup
    have hq : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup X) := ⟨hcommTop, inferInstance⟩
    have hpar : IsParabolic2 (⊤ : Subgroup X) P := by
      refine ⟨le_top, (S : Subgroup X), CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S, ?_⟩
      simpa using hNS ht
    have hne : P ≠ (⊤ : Subgroup X) := hP
    have hfamLevi :
        (IsAlt 5 ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ∨
          IsAlt 6 ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ∨
          IsAlt 8 ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X)) ∨
          ((∃ f : ℕ,
              (2 ≤ f ∧ IsPSL 2 2 f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
              (1 ≤ f ∧ IsPSL 3 2 f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
              (2 ≤ f ∧ IsPSU 3 2 f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
              (2 ≤ f ∧ IsPSp4 2 f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
              (2 ≤ f ∧ IsG2 2 f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
              (1 ≤ f ∧ Is3D4 2 f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
              (Odd f ∧ 3 ≤ f ∧ Is2F4 f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
              (Odd f ∧ 3 ≤ f ∧ IsSz f
                ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X)))) ∨
            IsTits ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) ∨
          ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1
            ((↥(⊤ : Subgroup X)) ⧸ Subgroup.center ↥(⊤ : Subgroup X))) := by
      rcases hfam with ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ |
        ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hf⟩ | ⟨rfl, rfl, hodd, hf⟩ | ⟨rfl, rfl, rfl⟩
      · refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩))))
        exact Or.inr (Or.inl ⟨hf, IsPSL.of_mulEquiv eK.symm
          (hmodel.statedClassicalModel (by decide))⟩)
      · refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩))))
        exact Or.inr (Or.inr (Or.inl ⟨hf, IsPSU.of_mulEquiv eK.symm
          (hmodel.statedClassicalModel (by decide))⟩))
      · refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩))))
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, IsPSp4.of_mulEquiv eK.symm
          (hmodel.statedClassicalModel (by decide))⟩)))
      · refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩))))
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf, IsG2.of_mulEquiv eK.symm
          (hmodel.chevalleyExceptionalModel (by decide))⟩))))
      · refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩))))
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hf,
          Is3D4.of_mulEquiv eK.symm (hmodel.chevalleyExceptionalModel (by decide))⟩)))))
      · obtain ⟨-, hF4⟩ := hmodel.reeTitsModel
          (by decide : StatedLieTag.twistedF4 ∈ reeTitsTags)
        refine Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨f, ?_⟩))))
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hodd, hf, Is2F4.of_mulEquiv eK.symm hF4⟩))))))
      · exact absurd rfl ht
    by_cases hsolvP : Group.IsSolvable ↥P
    · exact false_of_le_solvable_of_surjective hHc hYP hsolvP φ hφ
    · haveI : ((perfectCore P).subgroupOf P).Normal := perfectCore_normal P
      have hX0 : perfectCore P ≠ ⊥ := by
        intro h
        exact hsolvP ((isSolvable_iff_perfectCore_eq_bot P).mpr h)
      obtain ⟨-, hsmall, hL4⟩ :=
        CFSG.Quasithin.C35Levi.levi_holds X (⊤ : Subgroup X) P hq hZ hfamLevi hpar hne hX0
      have hsolvQuot : Group.IsSolvable (↥P ⧸ ((perfectCore P).subgroupOf P)) := by
        refine (CFSG.isSolvable_quotient_iff_exists_derivedSeries_le
          ((perfectCore P).subgroupOf P)).2 ?_
        obtain ⟨r, hr⟩ := CFSG.Quasithin.exists_perfectCore_eq P
        refine ⟨r, ?_⟩
        have hle : CFSG.Quasithin.derivedSeriesOf P r ≤ perfectCore P := by
          rw [hr r le_rfl]
        rw [CFSG.Quasithin.derivedSeriesOf_eq_map_derivedSeries] at hle
        exact (Subgroup.map_le_iff_le_comap).mp hle
      haveI : Finite H := Finite.of_surjective φ hφ
      obtain ⟨Q, ψ, hψ⟩ := exists_quotient_modO2 hHc hYP φ hφ hsolvQuot
      rcases hsmall with ⟨m, hm, hL2⟩ | ⟨m, -, -, hSz⟩ | hL3 | hL4small
      · exact false_of_L2_of_surjective hH2 hm hL2 ψ hψ
      · exact false_of_sz_of_surjective hH3 hSz ψ hψ
      · exact false_of_L3_of_surjective hH168 hL3 ψ hψ
      · exact not_isPSL52_of_char2LeviFamily hfam ht hmodel
          (IsPSL.of_mulEquiv eK (hL4 hL4small).1)

end CFSG.Quasithin.H13.K1262Two
