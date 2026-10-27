module

public import CFSG.Milestones.ASVolI.F45.Lie
public import CFSG.GH74.GLS.SP.Model
public import CFSG.LieType.Steinberg.CentralExt.BorelIndex
public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LieType.Universal.SymplecticExtras.Torus
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section CharP

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg

theorem burnsideF45_isPGroup_range_of_charP {F G : Type*} [Ring F] {p : ℕ} [CharP F p] [Group G]
    (f : Multiplicative F →* G) : IsPGroup p f.range := by
  rintro ⟨_, c, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hc : c ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hc, map_one]

theorem burnsideF45_sp_isPGroup_rootGroup {n : ℕ} {F : Type} [Field F] {p : ℕ} [CharP F p]
    {γ : Fin (rootDatum n F).rank → ℤ} (hγ : γ ∈ (rootDatum n F).roots) :
    IsPGroup p ((rootDatum n F).rootGroup γ) := by
  obtain ⟨r, hr⟩ := SpExtras.exists_stdVec_of_mem_roots hγ
  change IsPGroup p (rootGroup n F γ)
  rw [SpExtras.rootGroup_eq_range hr]
  exact burnsideF45_isPGroup_range_of_charP _

theorem burnsideF45_sp_coprime_card_torus {n : ℕ} {F : Type} [Field F] [Finite F] {p : ℕ}
    [hp : Fact p.Prime] [CharP F p] :
    Nat.Coprime p (Nat.card (⨆ i, torus n F i : Subgroup (StatedSp n F))) := by
  rw [Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨d, hd⟩ := SpExtras.exists_diagonal_of_mem_iSup_torus g.2
  have hgp : (g : StatedSp n F) ^ p = 1 := by
    rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
  have h1 : TauCeti.GLSymplecticFin.diagonal (d ^ p) = 1 := by
    apply (equivStatedSp n F).injective
    rw [map_pow, map_pow, map_one, ← hd]
    exact hgp
  have h2 : d ^ p = 1 := TauCeti.GLSymplecticFin.diagonal_injective (by rw [h1, map_one])
  have h3 : d = 1 := by
    funext i
    have hi := congrFun h2 i
    refine Units.ext ?_
    have hpow : ((d i : Fˣ) : F) ^ p = 1 := by
      have := congrArg (fun u : Fˣ => (u : F)) hi
      simpa using this
    have hsub : ((d i : F) - 1) ^ p = 0 := by
      rw [sub_pow_char, hpow, one_pow, sub_self]
    have h0 : (d i : F) - 1 = 0 := (pow_eq_zero_iff hp.out.ne_zero).1 hsub
    simpa [sub_eq_zero] using h0
  have hg1 : g = 1 := by
    apply Subtype.ext
    rw [hd, h3, map_one, map_one]
    rfl
  rw [hg1, orderOf_one] at hg
  exact hp.out.one_lt.ne hg

theorem burnsideF45_sp_iSup_torus_eq_bot {n : ℕ} {F : Type} [Field F] (hF : Nat.card F = 2) :
    (⨆ i, torus n F i : Subgroup (StatedSp n F)) = ⊥ := by
  have h1 : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.1 h1).1
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨t, rfl⟩ := SpExtras.exists_diagonal_of_mem_iSup_torus hx
  rw [Subsingleton.elim t 1, map_one, map_one]
  exact Subgroup.one_mem _

end CharP

section Faithful

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped Pointwise

theorem burnsideF45_pre_parabolic_inf {X : Type*} [Group X] {n : ℕ} (D : PreRankTwoSystem X n) :
    parabolic D.B D.N {D.w₁} ⊓ parabolic D.B D.N {D.w₂} = D.B := by
  classical
  have hT := D.isTits
  have hP := hT.proposition302
  have hS1 : ({D.w₁} : Finset (WeylGroup D.B D.N)) ⊆ {D.w₁, D.w₂} := by simp
  have hS2 : ({D.w₂} : Finset (WeylGroup D.B D.N)) ⊆ {D.w₁, D.w₂} := by simp
  have hB1 : D.B ≤ parabolic D.B D.N {D.w₁} := by
    have := hT.le_parabolic hS1
    simpa using this
  have hB2 : D.B ≤ parabolic D.B D.N {D.w₂} := by
    have := hT.le_parabolic hS2
    simpa using this
  obtain ⟨J, hJS, hQJ⟩ := hP.exists_parabolic _ (le_inf hB1 hB2)
  have hJ1 : J ⊆ {D.w₁} := by
    refine (hP.parabolic_le_iff J {D.w₁} hJS hS1).1 ?_
    rw [← hQJ]
    simp
  have hJ2 : J ⊆ {D.w₂} := by
    refine (hP.parabolic_le_iff J {D.w₂} hJS hS2).1 ?_
    rw [← hQJ]
    simp
  have hJe : J = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have h1 := Finset.mem_singleton.1 (hJ1 hx)
    have h2 := Finset.mem_singleton.1 (hJ2 hx)
    exact D.w₁_ne_w₂ (h1.symm.trans h2)
  rw [hQJ, hJe]
  simpa using hP.parabolic_empty

theorem burnsideF45_pre_faithful_of_inf_eq_bot {X : Type*} [Group X] {n : ℕ}
    (D : PreRankTwoSystem X n) (h : D.B ⊓ D.N = ⊥) : FaithfulOnBuilding D.B D.N D.w₁ D.w₂ := by
  classical
  intro g hg
  have hinf := burnsideF45_pre_parabolic_inf D
  have hcore : ∀ x : X, x * g * x⁻¹ ∈ D.B := by
    intro x
    rw [← hinf]
    constructor
    · have hv := hg _ (Or.inl ⟨x, rfl⟩ : _ ∈ rankTwoVertices D.B D.N D.w₁ D.w₂)
      have hx : x * g ∈ ((parabolic D.B D.N {D.w₁} : Subgroup X) : Set X) * {x} * {g} :=
        Set.mem_mul.2 ⟨x, Set.mem_mul.2 ⟨1, (parabolic D.B D.N {D.w₁}).one_mem, x, rfl,
          one_mul x⟩, g, rfl, rfl⟩
      rw [hv] at hx
      obtain ⟨q, hq, y, hy, hqy⟩ := Set.mem_mul.1 hx
      rw [Set.mem_singleton_iff] at hy
      rw [hy] at hqy
      have : x * g * x⁻¹ = q := by rw [← hqy]; group
      rw [this]
      exact hq
    · have hv := hg _ (Or.inr ⟨x, rfl⟩ : _ ∈ rankTwoVertices D.B D.N D.w₁ D.w₂)
      have hx : x * g ∈ ((parabolic D.B D.N {D.w₂} : Subgroup X) : Set X) * {x} * {g} :=
        Set.mem_mul.2 ⟨x, Set.mem_mul.2 ⟨1, (parabolic D.B D.N {D.w₂}).one_mem, x, rfl,
          one_mul x⟩, g, rfl, rfl⟩
      rw [hv] at hx
      obtain ⟨q, hq, y, hy, hqy⟩ := Set.mem_mul.1 hx
      rw [Set.mem_singleton_iff] at hy
      rw [hy] at hqy
      have : x * g * x⁻¹ = q := by rw [← hqy]; group
      rw [this]
      exact hq
  have hsat := D.isSaturated
  unfold IsSaturated at hsat
  have hmem : g ∈ D.B ⊓ D.N := by
    rw [hsat, Subgroup.mem_iInf]
    intro m
    show g ∈ CFSG.GH74.BNPair.conjBy (m : X) D.B
    rw [CFSG.GH74.BNPair.mem_conjBy_iff]
    exact hcore m
  rw [h] at hmem
  exact Subgroup.mem_bot.1 hmem

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic in
theorem burnsideF45_modelPre_inf_eq_bot {F : Type} [Field F] (hF : Nat.card F = 2) :
    (modelPre F).B ⊓ (modelPre F).N = ⊥ := by
  show (spB F).map (spProj F) ⊓ (spN F).map (spProj F) = ⊥
  rw [map_inf_map_of_ker_le (spProj F) ((ker_spProj_le F).trans inf_le_left), spB_inf_spN]
  show (⨆ i, torus 2 F i : Subgroup (StatedSp 2 F)).map (spProj F) = ⊥
  rw [burnsideF45_sp_iSup_torus_eq_bot hF, Subgroup.map_bot]

open CFSG.Assembly.LowTwoRank in
theorem burnsideF45_modelPre_faithful (F : Type) [Field F] [Finite F] :
    FaithfulOnBuilding (modelPre F).B (modelPre F).N (modelPre F).w₁ (modelPre F).w₂ := by
  by_cases h2 : Nat.card F = 2
  · exact burnsideF45_pre_faithful_of_inf_eq_bot _ (burnsideF45_modelPre_inf_eq_bot h2)
  · have hlt : 1 < Nat.card F := Finite.one_lt_card
    haveI : IsSimpleGroup (StatedProj (StatedSp 2 F)) := by
      refine CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num) ?_
      by_cases h4 : 4 ≤ Nat.card F
      · exact Or.inl (Or.inr h4)
      · exact Or.inr (Or.inl ⟨by omega, le_rfl⟩)
    exact (modelPre F).faithful_of_isSimpleGroup

end Faithful

section System

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Steinberg

@[expose] noncomputable def burnsideF45_sp4System (F : Type) [Field F] [Finite F] :
    RankTwoSystem (StatedProj (StatedSp 2 F)) 4 :=
  (modelPre F).toSystem (burnsideF45_modelPre_faithful F)

theorem burnsideF45_sp4System_U (F : Type) [Field F] [Finite F] :
    (burnsideF45_sp4System F).U = (spU F).map (spProj F) :=
  rfl

theorem burnsideF45_sp4System_isSylow (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    [CharP F p] : ChF.IsSylowOf p (burnsideF45_sp4System F).U ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hX : ∀ γ ∈ (rootDatum 2 F).roots, IsPGroup p ((rootDatum 2 F).rootGroup γ) :=
    fun γ hγ => burnsideF45_sp_isPGroup_rootGroup hγ
  have hU : IsPGroup p (spU F) := isPGroup_iSup_pos (steinbergExtras 2 F) hX
  have hidx : p.Coprime (spU F).index :=
    CentralExt.BorelIndex.coprime_index_posUnipotent (D := rootDatum 2 F) (isCTGroupDatum 2 F)
      (steinbergExtras 2 F) (spBruhatExtras F) hX burnsideF45_sp_coprime_card_torus
  rw [burnsideF45_sp4System_U]
  refine ⟨le_top, hU.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hidx
    (hdvd.trans (Subgroup.index_map_dvd _ (spProj_surjective F)))

end System

section Facts

open CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.F431.BN


theorem burnsideF45_facts45L_Sp4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ GLKind.Sp4.m) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  obtain ⟨chart, -⟩ := hyp.toHypF_4_4g.lie_amalgam
  rcases chart.coordinates with
    ⟨c', hk, marking, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ |
    ⟨-, exponent, K', fK', finK', charK', scope, ⟨hk, -⟩ | ⟨hk, -⟩⟩
  · have hc : c' = .Sp4 := by
      cases c' <;> first | rfl | exact absurd hk (by decide)
    subst hc
    haveI : Fact p.Prime := ⟨hp⟩
    have hK : Nat.card marking.field = p ^ f := by simpa using marking.field_card
    haveI : CharP marking.field p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        marking.exponent_pos hK
    haveI : Finite (StatedProj (StatedSp 2 marking.field)) :=
      CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp 2 marking.field
    let θ₀ : StatedProj (StatedSp 2 marking.field) ≃* ↥Gp := marking.identification
    have hU := burnsideF45_sp4System_isSylow marking.field hp
    exact burnsideF45_facts45L_of_system hyp hp hm (burnsideF45_parabolics hyp.toHypF_4_4g) θ₀
      (burnsideF45_sp4System marking.field) rfl hU
      (fun i => burnsideF45_bn_modelBase (burnsideF45_sp4System marking.field) hp hU i)
  all_goals exact absurd hk (by decide)

end Facts

end CFSG.ASVolI
