module

public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Defs
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.NormRFlag
public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.NormRTransv

public section

namespace CFSG.Quasithin.H13.KG12617L52.NormR

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits Module

section Upper

variable {G : Type*} [Group G] [Finite G]

theorem card_le_of_isPGroup_le_normalizer {B : Subgroup G}
    (hiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) {x : G} (hxB : x ∈ B)
    (hx : ∀ d : G, (∃ k : ℕ, d ^ 2 ^ k = 1) → d * x = x * d → d = 1) {D : Subgroup G}
    (hD : IsPGroup 2 ↥D) (hDN : D ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥D ≤ 32 * Nat.card ↥(pCoreOf 2 B) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 ↥(pCoreOf 2 B) := pCoreOf_isPGroup 2 B
  have hBU : B ≤ Subgroup.normalizer (pCoreOf 2 B : Set G) := le_normalizer_pCoreOf 2 B
  have hcU : ∀ u ∈ pCoreOf 2 B, u * x = x * u → u = 1 := by
    intro u hu hux
    obtain ⟨k, hk⟩ := hU2 ⟨u, hu⟩
    exact hx u ⟨k, congrArg Subtype.val hk⟩ hux
  exact card_le_of_isPGroup_normalizer hiso (fun c hc2 hc =>
    mem_of_two_elt hBU hU2 hxB hcU hx hc2 hc.2.2.1 hc.2.2.2) hD hDN

end Upper

section SL5

variable {F : Type} [Field F]

local notation "SLF" => StatedSL 5 F
local notation "ρ" => natRep (StatedSL 5 F)

theorem map_theta_map_theta (X : Subgroup ↥SLF) :
    (X.map (theta (F := F)).toMonoidHom).map (theta (F := F)).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have hθ : ∀ g : ↥SLF, theta (theta g) = g := fun g => Subtype.ext (invTr_invTr g.1)
  have h : (theta (F := F)).toMonoidHom.comp (theta (F := F)).toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun g => hθ g
  rw [h, Subgroup.map_id]

theorem exists_pGroup_le_normalizer_of_finrank_theta [Finite F] (hF : Nat.card F = 2)
    {U R : Subgroup ↥SLF} (hRU : R ≤ U)
    (h : finrank F ↥(fixFlag ρ (U.map theta.toMonoidHom) 1) = 4) :
    ∃ P : Subgroup ↥SLF, IsPGroup 2 ↥P ∧ Nat.card ↥P = 2 ^ 10 ∧
      P ≤ Subgroup.normalizer (R : Set ↥SLF) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := finrank_fix_theta U
  rw [h] at hc
  have hc1 : finrank F ↥(commSp U) = 1 := by omega
  obtain ⟨v, hv0, hvspan⟩ := finrank_eq_one_iff'.1 hc1
  set v₁ : Fin 5 → F := (v : Fin 5 → F)
  have hv₁0 : v₁ ≠ 0 := fun h0 => hv0 (Subtype.ext h0)
  have hspan : ∀ w ∈ commSp U, ∃ c : F, c • v₁ = w := fun w hw => by
    obtain ⟨c, hc⟩ := hvspan ⟨w, hw⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hR : ∀ r ∈ R, ∃ φ : Module.Dual F (Fin 5 → F), ∀ x, ρ r x = x + φ x • v₁ := by
    intro r hr
    obtain ⟨l, hl, -⟩ := exists_dual_eq_one_of_notMem
      (W := (⊥ : Submodule F (Fin 5 → F))) (w := v₁) (by simpa using hv₁0)
    refine ⟨l.comp (ρ r - 1), fun x => ?_⟩
    obtain ⟨c, hc⟩ := hspan (ρ r x - x) (Submodule.subset_span ⟨r, hRU hr, x, rfl⟩)
    have hlc : l (ρ r x - x) = c := by rw [← hc, map_smul, hl, smul_eq_mul, mul_one]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [hlc, hc]
    abel
  have hAB : F ∙ v₁ ≤ tvFix ρ R v₁ := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact center_mem_tvFix hF hv₁0
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime (by rw [← hF, Nat.card_eq_fintype_card])
  obtain ⟨S, hS⟩ := exists_sylow_forall_stab 5 F 2 hAB
  refine ⟨S, S.isPGroup', card_sylow_two_statedSL_five hF S, fun g hg => ?_⟩
  obtain ⟨hA, hB⟩ := hS g hg
  have hg₁ : ρ g v₁ = v₁ := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      (hA v₁ (Submodule.mem_span_singleton_self v₁)).1
    rcases eq_zero_or_eq_one_of_card_eq_two hF c with rfl | rfl
    · rw [zero_smul] at hc
      exact absurd (rep_eq_zero hc.symm) hv₁0
    · rw [one_smul] at hc
      exact hc.symm
  exact mem_normalizer_of_stab hF (natRep_injective _) hv₁0 hR hg₁ fun w hw => hB w hw

theorem exists_pGroup_le_normalizer_of_finrank [Finite F] (hF : Nat.card F = 2)
    {U R : Subgroup ↥SLF} (hRU : R ≤ U) (h : finrank F ↥(fixFlag ρ U 1) = 4) :
    ∃ P : Subgroup ↥SLF, IsPGroup 2 ↥P ∧ Nat.card ↥P = 2 ^ 10 ∧
      P ≤ Subgroup.normalizer (R : Set ↥SLF) := by
  obtain ⟨P, hP2, hPc, hPN⟩ := exists_pGroup_le_normalizer_of_finrank_theta hF
    (U := U.map theta.toMonoidHom) (R := R.map theta.toMonoidHom) (Subgroup.map_mono hRU)
    (by rwa [map_theta_map_theta])
  refine ⟨P.map theta.toMonoidHom, hP2.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective theta.injective]
    exact hPc
  · have h' := Subgroup.map_mono (f := theta.toMonoidHom) hPN
    rwa [← Subgroup.map_equiv_normalizer_eq, map_theta_map_theta] at h'

end SL5

end CFSG.Quasithin.H13.KG12617L52.NormR

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LieType.BorelTits Module

theorem leafNormR_of (h2 : LeafFive) (h3 : LeafTwoElt) (_h4 : LeafCardPCore) : LeafNormR := by
  intro F _ _ hF B R _hperf hiso hU16 _hR hRU hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxB, hx5⟩ := h2 ↥(StatedSL 5 F) B hiso
  have hU2 : IsPGroup 2 ↥(pCoreOf 2 B) := pCoreOf_isPGroup 2 B
  have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 B : Set ↥(StatedSL 5 F)) :=
    le_normalizer_pCoreOf 2 B hxB
  have hU4 : 4 ≤ Nat.card ↥(pCoreOf 2 B) := by rw [hU16]; norm_num
  obtain ⟨P, hP2, hPc, hPR⟩ : ∃ P : Subgroup ↥(StatedSL 5 F), IsPGroup 2 ↥P ∧
      Nat.card ↥P = 2 ^ 10 ∧ P ≤ Subgroup.normalizer (R : Set ↥(StatedSL 5 F)) := by
    rcases finrank_fix_cases_theta hF hx5 hU2 hxN hU4 with ⟨-, h⟩ | ⟨h, -⟩
    · exact NormR.exists_pGroup_le_normalizer_of_finrank_theta hF hRU h
    · exact NormR.exists_pGroup_le_normalizer_of_finrank hF hRU h
  have hle := NormR.card_le_of_isPGroup_le_normalizer hiso hxB
    (fun d hd hdx => h3 F hF x d hx5 hd hdx.symm) hP2 (hPR.trans hN)
  rw [hPc, hU16] at hle
  omega

end CFSG.Quasithin.H13.KG12617L52
