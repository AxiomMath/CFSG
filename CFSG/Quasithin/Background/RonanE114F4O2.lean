module

public import CFSG.Quasithin.Background.RonanE114O2
public import CFSG.Quasithin.Background.RonanE114F4
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizersCentral
public import CFSG.LieType.ChevTwo.OppositeFixedExcReeStd
public import CFSG.LieType.Ree.FixedBruhatDecomposition
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.CGT.Timmesfeld75.L2Defs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951
public import Certificates.Certificate18000
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeNormalForm

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.CGT
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

section Ree


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem exists_unit_pow (hK : Nat.card K = 2 ^ (2 * a + 1)) {c : K} (hc : c ≠ 0) :
    ∃ u : Kˣ, (u : K) ^ 2 ^ a = c := by
  have hu : c ^ (2 * 2 ^ a) ≠ 0 := pow_ne_zero _ hc
  refine ⟨Units.mk0 (c ^ (2 * 2 ^ a)) hu, ?_⟩
  have h1 : (2 * 2 ^ a) * 2 ^ a = Nat.card K := by rw [hK]; ring
  have := Fintype.ofFinite K
  simp only [Units.val_mk0]
  rw [← pow_mul, h1, Nat.card_eq_fintype_card, FiniteField.pow_card]

@[expose] noncomputable def reeCenter (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ) :
    Subgroup (ModGL F4.tag K) :=
  (Subgroup.center ↥(F4.reeFixedPosUnipotent K a)).map (F4.reeFixedPosUnipotent K a).subtype

theorem mem_reeCenter_iff (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : ModGL F4.tag K} : x ∈ reeCenter K a ↔ ∃ c : K, centralZ K a c = x := by
  have h := coe_center_eq_range_centralZ ha hK
  have hx : x ∈ ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
      (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) ↔
        x ∈ Set.range (centralZ K a) := by rw [h]
  exact hx

theorem reeCenter_le_posUnipotent : reeCenter K a ≤ F4.reeFixedPosUnipotent K a :=
  Subgroup.map_subtype_le _

theorem reeCenter_conj (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {b : ModGL F4.tag K}
    (hb : b ∈ F4.reeFixedBorel K a) {x : ModGL F4.tag K} (hx : x ∈ reeCenter K a) :
    b * x * b⁻¹ ∈ reeCenter K a := by
  obtain ⟨c, rfl⟩ := (mem_reeCenter_iff ha hK).mp hx
  obtain ⟨u, hu⟩ := exists_conj_centralZ ha hK hb c
  rw [hu]
  exact (mem_reeCenter_iff ha hK).mpr ⟨_, rfl⟩

theorem reeCenter_torus_dichotomy (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {O : Subgroup (ModGL F4.tag K)}
    (hO : ∀ h ∈ F4.reeFixedTorus K a, ∀ z ∈ O, h * z * h⁻¹ ∈ O) :
    reeCenter K a ⊓ O = ⊥ ∨ reeCenter K a ≤ O := by
  by_cases hbot : reeCenter K a ⊓ O = ⊥
  · exact Or.inl hbot
  refine Or.inr fun y hy => ?_
  obtain ⟨⟨x, hxR, hxO⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨c₀, rfl⟩ := (mem_reeCenter_iff ha hK).mp hxR
  obtain ⟨c, rfl⟩ := (mem_reeCenter_iff ha hK).mp hy
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    exact hx1 (Subtype.ext centralZ_zero)
  by_cases hc : c = 0
  · rw [hc, centralZ_zero]
    exact O.one_mem
  obtain ⟨u, hu⟩ := exists_unit_pow hK (div_ne_zero hc hc₀)
  have hT := rankOne_torusPair_mem_reeFixedTorus hK u 1
  have hconj := torusPair_conj_centralZ (a := a) hK u 1 c₀
  have hmem := hO _ hT _ hxO
  rw [hconj, hu, div_mul_cancel₀ _ hc₀] at hmem
  exact hmem

end Ree


section Main


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem reeCenter_le_reeGamma : reeCenter K a ≤ F4.reeGamma K a :=
  reeCenter_le_posUnipotent.trans
    (ReeTag.reeFixedPosUnipotent_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma)

theorem reeFixedTorus_le_reeGamma : F4.reeFixedTorus K a ≤ F4.reeGamma K a :=
  ReeTag.reeFixedTorus_le_reeFixedBorel.trans ReeTag.reeFixedBorel_le_reeGamma

theorem ree_normalTwo (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (R : Subgroup ↥(F4.reeGamma K a))
    (hR : (reeCenter K a).subgroupOf (F4.reeGamma K a) ≤ R) :
    NormalTwoDichotomy ((reeCenter K a).subgroupOf (F4.reeGamma K a)) R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBT : CFSG.LieType.BorelTits.Holds ↥(F4.reeGamma K a) 2 :=
    CFSG.LieType.ChevTwo.Semi.holds_reeGamma ReeTag.F4 K a
  have hU : IsSylowIn 2 ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ := by
    obtain ⟨S, hS⟩ := (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center a ha
      K hK).1
    rw [← hS]
    exact isSylowIn_top S
  have hBN : borelGroup F4.tag K ≤
      Subgroup.normalizer (posUnipotent F4.tag K : Set (ModGL F4.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mp
      (triangular_borel_structure.{0, 0} F4.tag K).2.2.2.2.2.2.2.2.1
  have hBU := subgroupOf_le_normalizer_of_forward (Γ := F4.reeGamma K a)
    (B := F4.reeFixedBorel K a) (Y := F4.reeFixedPosUnipotent K a) fun b hb u hu => by
      have hbΓ : b ∈ F4.reeGamma K a := ReeTag.reeFixedBorel_le_reeGamma hb
      have huΓ : u ∈ F4.reeGamma K a :=
        ReeTag.reeFixedBorel_le_reeGamma (ReeTag.reeFixedPosUnipotent_le_reeFixedBorel hu)
      refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hbΓ huΓ) (Subgroup.inv_mem _ hbΓ)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hBN hb.1) u).mp hu.1
  have hBA := subgroupOf_le_normalizer_of_forward (Γ := F4.reeGamma K a)
    (B := F4.reeFixedBorel K a) (Y := reeCenter K a) fun b hb y hy => reeCenter_conj ha hK hb hy
  have hHB : (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a) ≤
      (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a) :=
    Subgroup.subgroupOf_mono _ ReeTag.reeFixedTorus_le_reeFixedBorel
  have hbruhat : ∀ g : ↥(F4.reeGamma K a), ∃ b₁ ∈ (F4.reeFixedBorel K a).subgroupOf
      (F4.reeGamma K a), ∃ n : ↥(F4.reeGamma K a),
      (∀ h ∈ (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a),
        n * h * n⁻¹ ∈ (F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a)) ∧
      ∃ b₂ ∈ (F4.reeFixedBorel K a).subgroupOf (F4.reeGamma K a), g = b₁ * n * b₂ := by
    intro g
    have hg : (g : ModGL F4.tag K) ∈ (F4.reeGamma K a : Set (ModGL F4.tag K)) := g.2
    rw [ReeTag.reeGamma_eq_iUnion_reeFixedBruhatCell (t := ReeTag.F4) (K := K) (a := a)] at hg
    obtain ⟨⟨w, hw⟩, hmem⟩ := Set.mem_iUnion.mp hg
    obtain ⟨b₁, hb₁, b₂, hb₂, hgb⟩ := ReeTag.mem_reeFixedBruhatCell.mp hmem
    have hb₁Γ : b₁ ∈ F4.reeGamma K a := ReeTag.reeFixedBorel_le_reeGamma hb₁
    have hb₂Γ : b₂ ∈ F4.reeGamma K a := ReeTag.reeFixedBorel_le_reeGamma hb₂
    set b₁' : ↥(F4.reeGamma K a) := ⟨b₁, hb₁Γ⟩ with hb₁'
    set b₂' : ↥(F4.reeGamma K a) := ⟨b₂, hb₂Γ⟩ with hb₂'
    set n : ↥(F4.reeGamma K a) := b₁'⁻¹ * g * b₂'⁻¹ with hn
    have hnval : (n : ModGL F4.tag K) = canonicalRep (coxeterSystem F4.tag) K w := by
      rw [hn]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hb₁', hb₂']
      rw [← hgb]
      group
    refine ⟨b₁', hb₁, n, fun h hh => ?_, b₂', hb₂, by rw [hn]; group⟩
    have hhT : (h : ModGL F4.tag K) ∈ F4.reeFixedTorus K a := hh
    have hnorm := (canonical_weyl_root_transport F4.tag K).2.2 w
    rw [← hnval] at hnorm
    refine ⟨?_, (n * h * n⁻¹).2⟩
    have := (Subgroup.mem_normalizer_iff.mp hnorm (h : ModGL F4.tag K)).mp hhT.1
    simpa using this
  exact normalTwo_of_BT_bruhat hBT hU hBU hHB hBA hbruhat
    (dichotomy_subgroupOf reeFixedTorus_le_reeGamma reeCenter_le_reeGamma
      fun O hO => reeCenter_torus_dichotomy ha hK hO) R hR

end Main


section Model


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem isElemAbelian_reeCenter (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsElemAbelian 2 (reeCenter K a) := by
  have hE := (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center a ha K hK).2.2.1
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hux, ← hvy]
    simp only [Subgroup.subtype_apply]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, Subgroup.mem_center_iff.mp hu v]
  · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    haveI := hE
    set g : ↥(Subgroup.center ↥(F4.reeFixedPosUnipotent K a)) := ⟨u, hu⟩ with hg
    have h2 : g ^ 2 = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (CFSG.IsElementaryAbelian.exponent_dvd_p 2
          ↥(Subgroup.center ↥(F4.reeFixedPosUnipotent K a)))) g
    have h3 : u ^ 2 = 1 := congrArg Subtype.val h2
    simp only [Subgroup.subtype_apply]
    rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]

theorem card_reeCenter (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (reeCenter K a) = 2 ^ (2 * a + 1) := by
  rw [reeCenter, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact (CFSG.ComponentClassification.UnbalancedCatalog.large_Ree_Sylow_center a ha K hK).2.2.2

theorem isElemAbelian_subgroupOf {M : Type} [Group M] {Γ Y : Subgroup M}
    (h : IsElemAbelian 2 Y) : IsElemAbelian 2 (Y.subgroupOf Γ) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact B2F.isElemAbelian_comm h x.2 y.2
  · apply Subtype.ext
    have := h.2 (x : M) hx
    simpa using this

theorem reeBlock_le_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    rankOneGroupOne K a ≤ F4.reeGamma K a := by
  obtain ⟨⟨h0eq, -, -⟩, -⟩ := large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  rw [← h0eq]
  exact (large_Ree_local_block_Sylow_action F4 a K ⟨0, by decide⟩).1.trans inf_le_left

@[expose] noncomputable def reeBlockHom (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SL(2, K) →* ↥(F4.reeGamma K a) :=
  (Subgroup.inclusion (reeBlock_le_reeGamma ha hK)).comp (rankOneEquivSL K a hK).toMonoidHom

theorem reeBlockHom_injective (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Injective (reeBlockHom ha hK) :=
  (Subgroup.inclusion_injective (reeBlock_le_reeGamma ha hK)).comp
    (rankOneEquivSL K a hK).injective

theorem ree_nonabelian (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ x y : ↥(F4.reeGamma K a), x * y ≠ y * x := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨x, y, hxy⟩ := (Rk1.sl2 hK hK4).nonabelian
  exact ⟨reeBlockHom ha hK x, reeBlockHom ha hK y, fun h =>
    hxy (reeBlockHom_injective ha hK (by rw [map_mul, map_mul, h]))⟩

variable {G : Type} [Group G] [Finite G]

theorem le_nParam_of_is2F4 {T : Subgroup G} {n : ℕ}
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (h2F4 : CFSG.Quasithin.Is2F4 n ↥(CFSG.generalizedFitting G)) :
    (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model h2F4
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hn : n = 2 * a + 1 := hfa
  have hn2 : 2 ≤ n := by omega
  refine le_nParam_of_normalTwo_model hn2 hs hT hFT e (ree_nonabelian ha hK')
    (isElemAbelian_subgroupOf (isElemAbelian_reeCenter ha hK')) ?_
    fun R hR => ree_normalTwo ha hK' R hR
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe reeCenter_le_reeGamma).toEquiv,
    card_reeCenter ha hK', hn]

end Model

end CFSG.Quasithin.RonanE114
