module

public import CFSG.Quasithin.Vol2.Ch9Sec3FactsLie
public import CFSG.Quasithin.Vol2.Ch9Sec3Sp4Red
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk2
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped MatrixGroups commutatorElement

theorem commutator_le_commutator_of_perfect {G : Type} [Group G] {X Q W L : Subgroup G}
    (hQX : Q ≤ X) (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hWX : W ≤ X) (hLX : L ≤ X)
    (hperf : ⁅L, L⁆ = L) (hWL : ⁅W, L⁆ ≤ Q) : ⁅W, L⁆ ≤ ⁅Q, X⁆ := by
  set Q' := Q.subgroupOf X with hQ'
  set W' := W.subgroupOf X with hW'
  set L' := L.subgroupOf X with hL'
  have : Q'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hXQ
  set U' := ⁅Q', (⊤ : Subgroup ↥X)⁆ with hU'
  have : U'.Normal := Subgroup.commutator_normal Q' ⊤
  set π := QuotientGroup.mk' U' with hπ
  have hmapX : ∀ H : Subgroup G, H ≤ X → (H.subgroupOf X).map X.subtype = H := fun H hH => by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hH]
  have hL'perf : ⁅L', L'⁆ = L' := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, hmapX L hLX, hperf]
  have hWL' : ⁅W', L'⁆ ≤ Q' := by
    rw [← Subgroup.map_le_map_iff_of_injective X.subtype_injective, Subgroup.map_commutator,
      hmapX W hWX, hmapX L hLX, hmapX Q hQX]
    exact hWL
  have hWLL : ⁅⁅W', L'⁆, L'⁆ ≤ U' := Subgroup.commutator_mono hWL' le_top
  have h1 : ⁅⁅W'.map π, L'.map π⁆, L'.map π⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hWLL hx
  have h2 : ⁅⁅L'.map π, W'.map π⁆, L'.map π⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (L'.map π)]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L'.map π) (H₂ := L'.map π)
    (H₃ := W'.map π) h2 h1
  rw [← Subgroup.map_commutator, hL'perf] at h3
  have h4 : ⁅L', W'⁆ ≤ U' := by
    intro x hx
    have hx' : π x ∈ (⁅L', W'⁆).map π := ⟨x, hx, rfl⟩
    rw [Subgroup.map_commutator, h3, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx'
    exact hx'
  have h5 := Subgroup.map_mono (f := X.subtype) h4
  rw [Subgroup.map_commutator, Subgroup.map_commutator, hmapX L hLX, hmapX W hWX, hmapX Q hQX,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.commutator_comm L W] at h5
  exact h5

theorem sp4BlockParabolicFact_holds : Sp4BlockParabolicFact := by
  intro G _ _ X S L W hb _ hLX _ hperf hA5 hWX hW2 hLW hcard
  obtain ⟨hsh, F, _, _, hF4, α, hαs, hαk, -⟩ := hb
  set φ : ↥X →* GL (Fin 2 ⊕ Fin 2) F :=
    (CFSG.Assembly.LowTwoRank.StatedSp 2 F).subtype.comp α with hφ
  have hmemker : ∀ x : ↥X, x ∈ φ.ker ↔ x ∈ CFSG.pCore 2 ↥X := by
    intro x
    rw [MonoidHom.mem_ker, ← hαk, MonoidHom.mem_ker, hφ, MonoidHom.comp_apply,
      Subgroup.coe_subtype, OneMemClass.coe_eq_one]
  have hker2 : IsPGroup 2 φ.ker := by
    have h := CFSG.pCore_isPGroup (p := 2) (G := ↥X)
    have heq : φ.ker = CFSG.pCore 2 ↥X := Subgroup.ext hmemker
    rw [heq]
    exact h
  set θL : ↥L →* GL (Fin 2 ⊕ Fin 2) F := φ.comp (Subgroup.inclusion hLX) with hθL
  set θW : ↥W →* GL (Fin 2 ⊕ Fin 2) F := φ.comp (Subgroup.inclusion hWX) with hθW
  have hθLr : θL.range = (L.subgroupOf X).map φ := by
    rw [hθL, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hθWr : θW.range = (W.subgroupOf X).map φ := by
    rw [hθW, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hrangeS : ∀ {H : Type} [Group H] (f : H →* ↥X),
      (φ.comp f).range ≤ CFSG.Assembly.LowTwoRank.StatedSp 2 F := by
    rintro H _ f _ ⟨h, rfl⟩
    exact (α (f h)).2
  have hcfg : Sp4B.Cfg θL.range θW.range := by
    refine ⟨hrangeS _, hrangeS _, ?_, ?_, hW2.of_surjective θW.rangeRestrict
      θW.rangeRestrict_surjective, ?_, ?_⟩
    ·
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        Sp4B.commutator_eq_top_of_perfect hperf]
    ·
      intro N hN hnorm hN2
      set M := N.comap θL with hM
      have hMn : M.Normal := by
        refine ⟨fun m hm l => ?_⟩
        rw [hM, Subgroup.mem_comap, map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp (hnorm ⟨l, rfl⟩) (θL m)).mp hm
      have hkerL : IsPGroup 2 θL.ker := by
        rw [hθL, ← MonoidHom.comap_ker]
        exact hker2.comap_of_injective _ (Subgroup.inclusion_injective hLX)
      have hM2 : IsPGroup 2 M := hN2.comap_of_ker_isPGroup θL hkerL
      have hMO : M ≤ CFSG.pCore 2 ↥L :=
        CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hMn hM2
      have hidx : N.relIndex θL.range = M.index := by
        rw [Subgroup.relIndex,
          ← Subgroup.index_comap_of_surjective _ θL.rangeRestrict_surjective]
        congr 1
      have hO : (CFSG.pCore 2 ↥L).index = 60 := by
        obtain ⟨e⟩ := hA5
        rw [Subgroup.index, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      rw [hidx, ← hO]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
        (Subgroup.index_dvd_of_le hMO)
    ·
      have hk : (θW.ker).map W.subtype = W ⊓ pCoreOf 2 X := by
        ext x
        constructor
        · rintro ⟨w, hw, rfl⟩
          refine ⟨w.2, ?_⟩
          have : Subgroup.inclusion hWX w ∈ CFSG.pCore 2 ↥X := (hmemker _).mp hw
          exact (CFSG.QuasithinUnique.Lin2.mem_pCoreOf_iff_mem_pCore _).mpr this
        · rintro ⟨hxW, hxQ⟩
          refine ⟨⟨x, hxW⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, hθW, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
            hmemker]
          exact (CFSG.QuasithinUnique.Lin2.mem_pCoreOf_iff_mem_pCore
            (Subgroup.inclusion hWX ⟨x, hxW⟩)).mp hxQ
      have hkc : Nat.card θW.ker = Nat.card ↥(W ⊓ pCoreOf 2 X) := by
        rw [← hk, Subgroup.card_map_of_injective W.subtype_injective]
      have hUQ : W ⊓ blockU X ≤ W ⊓ pCoreOf 2 X := inf_le_inf_left _ (hsh.2.2.1.1.trans inf_le_left)
      have h1 := Subgroup.card_ker_mul_card_range θW
      have h2 := Subgroup.card_le_of_le hUQ
      have hpos : 0 < Nat.card ↥(W ⊓ pCoreOf 2 X) := Nat.card_pos
      rw [hkc] at h1
      have h3 : Nat.card θW.range * Nat.card ↥(W ⊓ pCoreOf 2 X) ≤
          16 * Nat.card ↥(W ⊓ pCoreOf 2 X) := by
        rw [mul_comm, h1]
        exact hcard.trans (Nat.mul_le_mul_left _ h2)
      exact Nat.le_of_mul_le_mul_right h3 hpos
    ·
      rw [hθLr, hθWr]
      refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map φ)
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hLW hl) y
  have hcomm := Sp4B.commute_of_cfg hF4 hcfg
  have hWLQ : ⁅W, L⁆ ≤ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    set w₀ := Subgroup.inclusion hWX ⟨w, hw⟩ with hw₀
    set l₀ := Subgroup.inclusion hLX ⟨l, hl⟩ with hl₀
    have hc := hcomm (φ w₀) ⟨⟨w, hw⟩, rfl⟩ (φ l₀) ⟨⟨l, hl⟩, rfl⟩
    have hker : ⁅w₀, l₀⁆ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hc
    exact (CFSG.QuasithinUnique.Lin2.mem_pCoreOf_iff_mem_pCore ⁅w₀, l₀⁆).mpr
      ((hmemker _).mp hker)
  change ⁅W, L⁆ ≤ ⁅pCoreOf 2 X, X⁆
  exact commutator_le_commutator_of_perfect (Subgroup.map_subtype_le _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) hWX hLX hperf hWLQ

end CFSG.Quasithin.H13.Ch9
