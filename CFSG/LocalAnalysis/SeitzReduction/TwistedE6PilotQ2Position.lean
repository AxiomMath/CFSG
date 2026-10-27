module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2LeviCentralizer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Quasithin (perfectCore perfectCore_eq_self_of_perfect)
open CFSG.ComponentClassification.OuterAutomorphisms


section Model

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_repXC_zero_eq_map [CharP K 2] {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    centralizer ({repXC hσσ 0} : Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      (centralizer ({stdRepC hσσ 0} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom := by
  rw [E6Pilot.map_conj_centralizer_singleton_q2, repXC_eq_conj hσσ 0]
  rfl

theorem commutator_centralizer_repXC_zero_two [CharP K 2] (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) :
    ⁅centralizer ({repXC (apply_apply_eq hK hσ) 0} : Set (graphFixedRootGroup TwistTag.E6 K σ)),
        centralizer ({repXC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ))⁆ =
      centralizer ({repXC (apply_apply_eq hK hσ) 0} :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) := by
  rw [centralizer_repXC_zero_eq_map, ← map_commutator,
    commutator_centralizer_stdRepC_zero_two hk hK hσ]

theorem decomp_centralizer_repXC_zero_two [CharP K 2] (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) :
    ∃ Q : Subgroup (graphFixedRootGroup TwistTag.E6 K σ),
      centralizer ({repXC (apply_apply_eq hK hσ) 0} :
          Set (graphFixedRootGroup TwistTag.E6 K σ)) =
        Q ⊔ ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom ∧
      IsPGroup 2 Q ∧
      ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom ≤
        normalizer (Q : Set (graphFixedRootGroup TwistTag.E6 K σ)) ∧
      Disjoint Q (((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom) ∧
      (∀ N : Subgroup (((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom), N.Normal → IsPGroup 2 N → N = ⊥) ∧
      (thetaRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) ≤
        ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
          (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom := by
  have hf : 1 ≤ 1 := le_rfl
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  set n := relWeylC σ relWordTX with hn
  have hd := (isCoreLeviDecomp_stdRepC_zero (k := k) hf hk hK hσ).map (MulAut.conj n)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hd
  rw [← centralizer_repXC_zero_eq_map (apply_apply_eq hK hσ)] at h1
  rw [perfectCore_eq_self_of_perfect (commutator_centralizer_repXC_zero_two hk hK hσ)] at h1
  refine ⟨_, h1, h2, h3, h4, h5, subgroupOf_le_map_conj n fun x hx => ?_⟩
  refine mem_inf.2 ⟨mem_map_conj_iff.1 (thetaRankOneGroup_le_map_relWordTX _ hx), ?_⟩
  exact mul_mem (mul_mem (inv_mem n.2) (thetaRankOneGroup_le_C0 hf hk hK hσ hx)) n.2

end Model

section LemmaB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem exists_le_centralizer_mulEquiv_of_conj_eq_mul_twistedE6_two [CharP K 2]
    (hset : StandardSetting G L) (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ (((thetaRankOneGroup (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {g z : G} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hzU : ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u)
    (hg : g⁻¹ * t * g = t * z) :
    ∃ P : Subgroup G,
      P ≤ centralizer (X : Set G) ⊓
        centralizer ({t * (e.symm (repXC (apply_apply_eq hK hσ) 0) : G)} : Set G) ∧
      Nonempty (P ≃* (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  classical
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hOut, -⟩ := outer_solvable_and_center_eq_bot_twistedE6 hK σ e
  set rep : graphFixedRootGroup TwistTag.E6 K σ := repXC (apply_apply_eq hK hσ) 0 with hrepdef
  set φ : graphFixedRootGroup TwistTag.E6 K σ →* G := L.subtype.comp e.symm.toMonoidHom
    with hφdef
  have hφ : Function.Injective φ := L.subtype_injective.comp e.symm.injective
  have hφr : φ.range = L := F4Pilot.range_subtype_comp_symm e
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hperf := commutator_centralizer_repXC_zero_two hk hK hσ
  have hrep2 : orderOf rep = 2 := by
    rw [← orderOf_injective (graphFixedRootGroup TwistTag.E6 K σ).subtype
      Subtype.val_injective rep]
    exact orderOf_repX 0
  obtain ⟨U, hU⟩ := hzU
  set zC : graphFixedRootGroup TwistTag.E6 K σ := e ⟨z, hzL⟩ with hzC
  have hφz : φ zC = z := by simp [hφdef, hzC]
  have hzC2 : orderOf zC = 2 := by
    rw [← orderOf_injective φ hφ zC, hφz]
    exact hz2
  have hUtop : (U : Subgroup L) ≤ (e.symm.toMonoidHom).range := by
    rw [MonoidHom.range_eq_top.2 e.symm.surjective]
    exact le_top
  have hinj : Function.Injective e.symm.toMonoidHom := e.symm.injective
  set UC : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ) :=
    U.comapOfInjective e.symm.toMonoidHom hinj hUtop with hUC
  have hmemUC : ∀ c, c ∈ (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) ↔
      e.symm c ∈ (U : Subgroup L) := by
    intro c
    rw [hUC, Sylow.coe_comapOfInjective, mem_comap]
    rfl
  have hzCU : ∀ c ∈ (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)), c * zC = zC * c := by
    intro c hc
    have h := hU _ ((hmemUC c).1 hc)
    apply hφ
    rw [map_mul, map_mul, hφz]
    exact h
  obtain ⟨c, hc⟩ := (conj_repX_zero_iff_twoCentral le_rfl hK hσ hzC2).2 ⟨UC, hzCU⟩
  have hc' : c * zC * c⁻¹ = rep := Subtype.ext hc
  set y : G := φ rep with hydef
  have hyL : y ∈ L := hφr ▸ ⟨rep, rfl⟩
  have hy : y = φ c * z * (φ c)⁻¹ := by
    rw [hydef, ← hc', map_mul, map_mul, map_inv, hφz]
  have hcL : φ c ∈ L := hφr ▸ ⟨c, rfl⟩
  set g₁ := g * (φ c)⁻¹ with hg₁def
  have hg₁ : g₁⁻¹ * t * g₁ = t * y := by
    have htc : φ c * t = t * φ c := mem_centralizer_singleton_iff.1 (hLt hcL)
    calc g₁⁻¹ * t * g₁ = φ c * (g⁻¹ * t * g) * (φ c)⁻¹ := by rw [hg₁def]; group
      _ = φ c * t * z * (φ c)⁻¹ := by rw [hg, mul_assoc (φ c) t z]
      _ = t * (φ c * z * (φ c)⁻¹) := by rw [htc]; group
      _ = t * y := by rw [hy]

  set Λ := (centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ with hΛdef
  have hΛeq : Λ = L ⊓ centralizer ({y} : Set G) := by
    rw [hΛdef, F4Pilot.map_centralizer_singleton hφ, hφr]
  have hΛperf : ⁅Λ, Λ⁆ = Λ := by rw [hΛdef, ← map_commutator, hperf]
  have hΛt : Λ ≤ centralizer ({t} : Set G) := hΛeq ▸ inf_le_left.trans hLt
  have hΛy : Λ ≤ centralizer ({y} : Set G) := hΛeq ▸ inf_le_right
  have hΛt' : Λ ≤ centralizer ({g₁⁻¹ * t * g₁} : Set G) := by
    rw [hg₁]
    exact fun x hx => F4Pilot.mem_centralizer_singleton_mul (hΛt hx) (hΛy hx)
  have hΛL' : Λ ≤ L ⊓ CFSG.conjugate L g₁ :=
    std_perfect_le_inf_conjugate hset hOut htC ht g₁ hΛperf hΛt hΛt'
  set φ'₀ : graphFixedRootGroup TwistTag.E6 K σ →* G :=
    (MulAut.conj g₁⁻¹).toMonoidHom.comp φ with hφ'₀def
  have hφ'₀ : Function.Injective φ'₀ := (MulAut.conj g₁⁻¹).injective.comp hφ
  have hφ'₀r : φ'₀.range = CFSG.conjugate L g₁ := by
    rw [hφ'₀def, MonoidHom.range_comp, hφr]
    rfl
  have hyΛ : y ∈ Λ := hΛeq ▸ ⟨hyL, mem_centralizer_singleton_iff.2 rfl⟩
  obtain ⟨w, hw⟩ : y ∈ φ'₀.range := hφ'₀r ▸ (hΛL' hyΛ).2
  set W₁ := (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)).map
    (MulAut.conj c).toMonoidHom with hW₁def
  have hW₁y : ∀ a ∈ W₁, a * rep = rep * a := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hzCU u hu
    rw [← hc']
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * u * c⁻¹ * (c * zC * c⁻¹) = c * (u * zC) * c⁻¹ := by group
      _ = c * (zC * u) * c⁻¹ := by rw [h]
      _ = c * zC * c⁻¹ * (c * u * c⁻¹) := by group
  set U₀ := W₁.map φ with hU₀def
  have hU₀Λ : U₀ ≤ Λ := by
    rw [hΛeq]
    rintro _ ⟨a, ha, rfl⟩
    refine mem_inf.2 ⟨hφr ▸ ⟨a, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, hydef, ← map_mul, ← map_mul, hW₁y a ha]
  have hU₀L' : U₀ ≤ φ'₀.range := hφ'₀r ▸ hU₀Λ.trans (hΛL'.trans inf_le_right)
  set W := U₀.comap φ'₀ with hWdef
  have hWcard : Nat.card W = Nat.card (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) := by
    have h1 : W.map φ'₀ = U₀ := map_comap_eq_self hU₀L'
    rw [← card_map_of_injective hφ'₀, h1, hU₀def, card_map_of_injective hφ, hW₁def,
      card_map_of_injective (MulAut.conj c).injective]
  have hWp : IsPGroup 2 W := by
    obtain ⟨k', hk'⟩ := UC.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hWcard.trans hk')
  have hWidx : ¬ 2 ∣ W.index := by
    have h1 := W.card_mul_index
    have h2 := (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)).card_mul_index
    rw [hWcard] at h1
    have hpos : 0 < Nat.card (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) := Nat.card_pos
    have h3 : W.index = (UC : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)).index :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)
    rw [h3]
    exact UC.not_dvd_index
  set WS : Sylow 2 (graphFixedRootGroup TwistTag.E6 K σ) := hWp.toSylow hWidx with hWS
  have hwW : ∀ a ∈ (WS : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)), a * w = w * a := by
    intro a ha
    have ha' : φ'₀ a ∈ U₀ := ha
    have h := mem_centralizer_singleton_iff.1 (hΛy (hU₀Λ ha'))
    apply hφ'₀
    rw [map_mul, map_mul, hw]
    exact h
  have hw2 : orderOf w = 2 := by
    rw [← orderOf_injective φ'₀ hφ'₀ w, hw, hydef, orderOf_injective φ hφ rep]
    exact hrep2
  obtain ⟨c', hcw0⟩ := (conj_repX_zero_iff_twoCentral le_rfl hK hσ hw2).2 ⟨WS, hwW⟩
  have hcw : c' * w * c'⁻¹ = rep := Subtype.ext hcw0
  set φ' : graphFixedRootGroup TwistTag.E6 K σ →* G :=
    φ'₀.comp (MulAut.conj c'⁻¹).toMonoidHom with hφ'def
  have hφ' : Function.Injective φ' := hφ'₀.comp (MulAut.conj c'⁻¹).injective
  have hφ'r : φ'.range = CFSG.conjugate L g₁ := by
    rw [hφ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c'⁻¹).surjective,
      ← MonoidHom.range_eq_map, hφ'₀r]
  have hφ'y : φ' rep = y := by
    rw [hφ'def, MonoidHom.comp_apply, ← hcw, ← hw]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hΛ' : (centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ =
      (centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ' := by
    have hR : (centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ' =
        CFSG.conjugate L g₁ ⊓ centralizer ({y} : Set G) := by
      rw [F4Pilot.map_centralizer_singleton hφ', hφ'r, hφ'y]
    rw [← hΛdef, hR]
    apply le_antisymm
    · exact le_inf (hΛL'.trans inf_le_right) hΛy
    · have hperf' : ⁅(centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ',
          (centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ'⁆ =
          (centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ' := by
        rw [← map_commutator, hperf]
      have ht' : (centralizer ({rep} : Set (graphFixedRootGroup TwistTag.E6 K σ))).map φ' ≤
          centralizer ({t} : Set G) := by
        rw [hR]
        intro x hx
        have h1 := F4Pilot.conjugate_le_centralizer htC g₁ hx.1
        rw [hg₁] at h1
        exact F4Pilot.mem_centralizer_singleton_of_mul h1 hx.2
      have hle := std_perfect_le hset hOut htC ht hperf' ht'
      rw [hR] at hle
      rw [hΛeq]
      exact fun x hx => ⟨hle hx, hx.2⟩
  obtain ⟨Q, hCQM, hQ, hMN, hQM, hO2, hJM⟩ := decomp_centralizer_repXC_zero_two hk hK hσ
  have hΛQM : (Q ⊔ ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom).map φ =
      (Q ⊔ ((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom).map φ' := by
    rw [← hCQM]
    exact hΛ'
  have hXJ' : X ≤ ((thetaRankOneGroup (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map φ := by
    rw [hφdef, ← Subgroup.map_map]
    exact hXJ
  obtain ⟨ι, -, P, hP, ⟨eP⟩⟩ := EPilot.exists_le_centralizer_mulEquiv_of_two_decompositions
    hφ hφ' hQ hQ hO2 hO2 hMN hMN hQM hQM hΛQM hJM hXJ'
    (fun h => (Nat.not_even_iff_odd.2 hXodd) (even_iff_two_dvd.2 h))
  obtain ⟨eD⟩ := factF56_leviX_two hk hK hσ 0 0 ι
  refine ⟨P, le_inf (hP.trans inf_le_right) ?_, ⟨eP.trans eD⟩⟩
  have h := (hP.trans inf_le_left).trans (hφ'r ▸ F4Pilot.conjugate_le_centralizer htC g₁)
  rwa [hg₁] at h

end LemmaB

end CFSG.SeitzReduction.TwistedE6Pilot
