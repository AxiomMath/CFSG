module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Red
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSCases
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.TorusSp4
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.SectionRank.Induction
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GroupTheory.PCore.PCoreOfIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Assembly.LowTwoRank
open scoped Matrix

@[expose] def K_19_19_sp4TorusRed : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n p : ℕ), Nat.card K = 2 ^ n → 3 ≤ n → Odd n →
    p.Prime → p ∣ 2 ^ n + 1 → ∀ H : Subgroup (StatedSp 2 K), ⁅H, H⁆ = H →
      torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K)) → CFSG.Open.pRank p H ≤ 1 →
      ∃ W : Submodule K (Fin 2 ⊕ Fin 2 → K), W ≠ ⊥ ∧ W ≠ ⊤ ∧
        (∀ d ∈ torus 2 K, ∀ w ∈ W,
          ((d : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ w ∈ W) ∧
        ∀ h ∈ H, ∀ w ∈ W,
          ((h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix _ _ K) *ᵥ w ∈ W

namespace TorusQS

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)
open scoped commutatorElement

section Generic

private theorem commutator_eq_top_of_commutator_eq_self' {G : Type*} [Group G] {H : Subgroup G}
    (h : ⁅H, H⁆ = H) : commutator ↥H = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    h]

private theorem commutator_range_eq_self' {G Y : Type*} [Group G] [Group Y]
    (hG : commutator G = ⊤) (f : G →* Y) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hG]

private theorem injective_of_isPGroup_ker_of_odd' {G Y : Type*} [Group G] [Group Y] [Finite G]
    (f : G →* Y) (hk : IsPGroup 2 f.ker) (hG : Odd (Nat.card G)) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk'⟩ := hk.exists_card_eq
  have hdvd : Nat.card f.ker ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
  rw [hk'] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.mpr hG) (even_iff_two_dvd.mpr ((dvd_pow_self 2 hk0).trans hdvd))
  rw [hk0, pow_zero] at hk'
  exact Subgroup.eq_bot_of_card_eq _ hk'

private theorem odd_card_of_isZModSq' {X : Type} [Group X] [Finite X] {A : Subgroup X} {n : ℕ}
    (hn : 1 ≤ n) (hA : IsZModSq A n) : Odd (Nat.card A) := by
  rw [S19.card_eq_of_isZModSq hA]
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, hm⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact ⟨m - 1, by omega⟩
  exact hodd.mul hodd

private theorem eq_bot_of_normal_isPGroup_of_mulEquiv' {G Y : Type*} [Group G] [Group Y]
    (e : G ≃* Y) (hY : ∀ P : Subgroup Y, P.Normal → IsPGroup 2 P → P = ⊥) {P : Subgroup G}
    (hP : P.Normal) (h2 : IsPGroup 2 P) : P = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp
    (hY (P.map e.toMonoidHom) (hP.map e.toMonoidHom e.surjective) (h2.map e.toMonoidHom))

theorem center_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
  · exact hc
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have ha : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem not_isPGroup_two_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsPGroup 2 G := fun h2 => by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h2.center_nontrivial
  rw [center_eq_bot_of_simple h] at this
  exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl

theorem isQuasisimple_of_simple' {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : CFSG.IsQuasisimple G :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native G).mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open G).mpr
      (isQuasisimple_of_simple (center_eq_bot_of_simple h)))

theorem exists_normalClosure_bar2_equiv {X Y : Type} [Group X] [Group Y] [IsSimpleGroup Y]
    {I J : Subgroup X} (hJI : J ≤ I) (φ : ↥I →* Y) (hφ : Function.Surjective φ)
    (hk : IsPGroup 2 φ.ker) (hJ : commutator ↥J = ⊤) (hR : (J.subgroupOf I).map φ ≠ ⊥)
    (hY : ¬ IsPGroup 2 Y) :
    ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧ Nonempty (Bar2 K ≃* Y) ∧ J ≤ K := by
  have hOY : ∀ P : Subgroup ↥(⊤ : Subgroup Y), P.Normal → IsPGroup 2 P → P = ⊥ := fun P hP h2 =>
    eq_bot_of_normal_isPGroup_of_mulEquiv' Subgroup.topEquiv
      (fun Q hQ hQ2 => eq_bot_of_normal_isPGroup_of_simple hY hQ hQ2) hP h2
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup ↥I,
      N = Subgroup.normalClosure ((J.subgroupOf I : Subgroup ↥I) : Set ↥I) := ⟨_, rfl⟩
  have hNn : N.Normal := by rw [hNdef]; exact Subgroup.normalClosure_normal
  have hJN : J.subgroupOf I ≤ N := by rw [hNdef]; exact Subgroup.le_normalClosure
  have hKI : N.map I.subtype ≤ I := Subgroup.map_subtype_le N
  have hKN : (N.map I.subtype).subgroupOf I = N :=
    Subgroup.comap_map_eq_self_of_injective I.subtype_injective N
  have hJK : J ≤ N.map I.subtype := fun x hx =>
    ⟨⟨x, hJI hx⟩, hJN (by rw [Subgroup.mem_subgroupOf]; exact hx), rfl⟩
  have hJ'J' : ⁅J.subgroupOf I, J.subgroupOf I⁆ = J.subgroupOf I := by
    rw [← Subgroup.inclusion_range hJI]; exact commutator_range_eq_self' hJ _
  have hNN : ⁅N, N⁆ = N := by
    refine le_antisymm (Subgroup.commutator_le_self N) ?_
    have h : Subgroup.normalClosure ((J.subgroupOf I : Subgroup ↥I) : Set ↥I) ≤ ⁅N, N⁆ :=
      Subgroup.normalClosure_le_normal fun x hx => by
        have hx' : x ∈ ⁅J.subgroupOf I, J.subgroupOf I⁆ := by rw [hJ'J']; exact hx
        exact Subgroup.commutator_mono hJN hJN hx'
    rwa [← hNdef] at h
  have hImK : ((N.map I.subtype).subgroupOf I).map φ = ⊤ := by
    rw [hKN, hNdef, Subgroup.map_normalClosure _ _ hφ, ← Subgroup.coe_map]
    have hnc : (Subgroup.normalClosure (((J.subgroupOf I).map φ : Subgroup Y) : Set Y)).Normal :=
      Subgroup.normalClosure_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure (((J.subgroupOf I).map φ : Subgroup Y) : Set Y)) with h | h
    · exact absurd (eq_bot_iff.mpr (Subgroup.le_normalClosure.trans h.le)) hR
    · exact h
  obtain ⟨eK⟩ := nonempty_bar2_equiv_of_map_eq φ hk hKI hImK hOY
  exact ⟨N.map I.subtype, hKI, by rw [hKN]; exact hNn, by rw [← Subgroup.map_commutator, hNN],
    ⟨eK.trans Subgroup.topEquiv⟩, hJK⟩

theorem pRank_range_eq {X G : Type} [Group X] [Finite X] [Group G] [Finite G] {J : Subgroup X}
    (ψ : ↥J →* G) (hk : IsPGroup 2 ψ.ker) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p ψ.range = CFSG.Open.pRank p (⊤ : Subgroup ↥J) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← CFSG.Quasithin.pRank_top_subtype ψ.range,
    ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (QuotientGroup.quotientKerEquivRange ψ),
    CFSG.SectionRank.pRank_quotient_two_group ψ.ker hk hp hp2]

end Generic

end TorusQS

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)
open TorusQS

theorem exists_sp4_coords {X : Type} [Group X] [Finite X] {I A : Subgroup X} {n : ℕ} (hn : 3 ≤ n)
    (hodd : Odd n) (hsp : IsSp4 (Bar2 I) n) (hAI : A ≤ I) (hA : IsZModSq A n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (φ : ↥I →* StatedSp 2 F),
      Nat.card F = 2 ^ n ∧ Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧
        (A.subgroupOf I).map φ = torus 2 F := by
  obtain ⟨F, _, _, _, hF, ⟨eI⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel hsp
  set φ₀ : ↥I →* StatedSp 2 F := eI.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥I))
  have hk₀ : IsPGroup 2 φ₀.ker := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).to_le fun x hx => by
    have h0 : eI (QuotientGroup.mk' (CFSG.pCore 2 ↥I) x) = 1 := hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I) x = 1 := (MulEquiv.map_eq_one_iff eI).mp h0
    exact (QuotientGroup.eq_one_iff x).mp h1
  have hginj : Function.Injective (restr φ₀ hAI) :=
    injective_of_isPGroup_ker_of_odd' _ (isPGroup_ker_restr φ₀ hk₀ hAI)
      (odd_card_of_isZModSq' (by omega) hA)
  have hTZ : IsZModSq ↥((A.subgroupOf I).map φ₀) n := by
    obtain ⟨e⟩ := hA
    exact ⟨(MulEquiv.subgroupCongr (range_restr φ₀ hAI)).symm.trans
      ((MonoidHom.ofInjective hginj).symm.trans e)⟩
  obtain ⟨g, hg⟩ := S19.exists_conj_eq_torus_of_isZModSq_sp4 hF hn hodd hTZ
  have hker : ((MulAut.conj g⁻¹).toMonoidHom.comp φ₀).ker = φ₀.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have hcc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (StatedSp 2 F) := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨F, inferInstance, inferInstance, inferInstance, (MulAut.conj g⁻¹).toMonoidHom.comp φ₀,
    hF, (MulAut.conj g⁻¹).surjective.comp (eI.surjective.comp (QuotientGroup.mk'_surjective _)),
    by rw [hker]; exact hk₀, ?_⟩
  rw [← Subgroup.map_map, hg, Subgroup.map_map, hcc, Subgroup.map_id]

theorem nonempty_bar2_sl2_of_coords (hS : K_19_19_sp4TorusRed) {X : Type} [Group X] [Finite X]
    {I A J : Subgroup X} {n p : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ 2 ^ n + 1) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ n)
    (φ : ↥I →* StatedSp 2 F) (hk : IsPGroup 2 φ.ker) (hAT : (A.subgroupOf I).map φ = torus 2 F)
    (hJI : J ≤ I) (hAJ : A ≤ Subgroup.normalizer (J : Set X)) (hJ : commutator ↥J = ⊤)
    (hq : CFSG.IsQuasisimple (Bar2 J)) (hpr : CFSG.Open.pRank p (⊤ : Subgroup ↥J) ≤ 1) :
    Nonempty (Bar2 J ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set ψ := restr φ hJI with hψdef
  have hkψ : IsPGroup 2 ψ.ker := isPGroup_ker_restr φ hk hJI
  have hHH : ⁅ψ.range, ψ.range⁆ = ψ.range := commutator_range_eq_self' hJ ψ
  have hTH : torus 2 F ≤ Subgroup.normalizer (ψ.range : Set (StatedSp 2 F)) := by
    rw [← hAT, hψdef, range_restr φ hJI]
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map φ)
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_normalizer_iff]
    intro j
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hAJ ha) (j : X)
  obtain ⟨eJ⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (p := 2)
    ψ.rangeRestrict ψ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hkψ)
  obtain ⟨W, hW0, hW1, hWt, hWH⟩ := hS F n p hF hn hodd hp hpd ψ.range hHH hTH
    (by rw [pRank_range_eq ψ hkψ hp hp2]; exact hpr)
  obtain ⟨e⟩ := nonempty_bar2_sl2_of_reducible h8 hHH (hq.of_mulEquiv eJ.symm) hTH hWt hWH hW0 hW1
  exact ⟨eJ.trans e⟩

theorem k_19_19_torusQS_sp4_of_red (hS : K_19_19_sp4TorusRed) : K_19_19_torusQS_sp4 := by
  intro X _ _ I A J n p hn hp hp2 hshape hAI hA hJI hAJ hO hpr _ _
  obtain ⟨hsp, hodd, hcong, hq⟩ := hshape
  right
  have hJ : commutator ↥J = ⊤ := commutator_eq_top_of_commutator_eq_self'
    (commutator_eq_self_of_oUpperTwo hO (by have := hq.1; exact Group.IsPerfect.commutator_eq_top))
  obtain ⟨F, _, _, _, φ, hF, -, hk, hAT⟩ := exists_sp4_coords hn hodd hsp hAI hA
  obtain ⟨e⟩ := nonempty_bar2_sl2_of_coords hS hn hodd hp hp2 (P2214R.dvd_of_cong hcong) hF φ hk
    hAT hJI hAJ hJ hq (by rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; exact hpr)
  refine ⟨CFSG.Blueprint.LieModel.of_mulEquiv e.symm
    (uc22p22d_isL2_of_statedSL (by omega) hF (specialLinearGroupEquivStatedSL 2 F)), ?_⟩
  obtain ⟨hsimp, hnab⟩ := uc22p22a_sp4_simple (Bar2 I) n hsp
  have hkI : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥I)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hR : (J.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) ≠ ⊥ := by
    intro hR0
    apply not_isPGroup_two_of_isQuasisimple_bar2 hq
    have hker' : (restr (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) hJI).ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : restr (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) hJI x ∈
          (restr (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) hJI).range := ⟨x, rfl⟩
      rw [range_restr, hR0, Subgroup.mem_bot] at hx
      exact hx
    have h2 := isPGroup_ker_restr (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) hkI hJI
    rw [hker'] at h2
    exact h2.of_equiv Subgroup.topEquiv
  have : Finite (Bar2 I) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I))
  obtain ⟨K, hKI, hKn, hKK, ⟨eK⟩, hJK⟩ := exists_normalClosure_bar2_equiv hJI
    (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) (QuotientGroup.mk'_surjective _) hkI hJ hR
    (not_isPGroup_two_of_simple hnab)
  exact ⟨K, hKI, hKn, hKK, (isQuasisimple_of_simple' hnab).of_mulEquiv eK, hJK,
    Or.inr (Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eK.symm hsp))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
