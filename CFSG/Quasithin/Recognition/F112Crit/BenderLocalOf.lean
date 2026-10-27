module

public import CFSG.Quasithin.Recognition.F112Crit.Theorem723
public import CFSG.Quasithin.Recognition.F112Crit.BenderQuot
public import CFSG.Quasithin.MS93.ASGroup
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)
open scoped Pointwise

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

namespace BenderLocalOf

section Lift

variable [Finite G] {X T : Subgroup G} {q i : ℕ}

theorem pCore_le_subgroupOf (hT : IsSylowTwoOf T X) : pCore 2 ↥X ≤ T.subgroupOf X := by
  rw [← CFSG.openPCoreOf_subgroupOf 2 X]
  exact Subgroup.comap_mono (F7.isSylowTwoOf_pCoreOf_le hT)

theorem exists_sylow_oTwoQuot (hT : IsSylowTwoOf T X) :
    ∃ P : Sylow 2 (oTwoQuot ↥X), (P : Subgroup (oTwoQuot ↥X)) =
      (T.subgroupOf X).map (QuotientGroup.mk' (pCore 2 ↥X)) := by
  obtain ⟨S', hS'⟩ := F7.isSylowTwoOf_exists_sylow hT
  exact ⟨S'.mapSurjective (QuotientGroup.mk'_surjective _), by
    rw [Sylow.coe_mapSurjective, hS']⟩

theorem comap_normalizer_oTwoQuot (hT : IsSylowTwoOf T X) {P : Subgroup (oTwoQuot ↥X)}
    (hP : P = (T.subgroupOf X).map (QuotientGroup.mk' (pCore 2 ↥X))) :
    (Subgroup.normalizer (P : Set (oTwoQuot ↥X))).comap (QuotientGroup.mk' (pCore 2 ↥X)) =
      (Subgroup.normalizer (T : Set G)).subgroupOf X := by
  rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _), hP,
    Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left (pCore_le_subgroupOf hT),
    Subgroup.subgroupOf_normalizer_eq hT.1]

variable (hK : IsBenderQuot (oTwoQuot ↥X) q i) (hT : IsSylowTwoOf T X)
include hK hT

theorem lift_trans {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (hxN : x ∉ Subgroup.normalizer (T : Set G)) (hyN : y ∉ Subgroup.normalizer (T : Set G)) :
    ∃ u ∈ T, y⁻¹ * u * x ∈ Subgroup.normalizer (T : Set G) := by
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  have hmem : ∀ z : ↥X, QuotientGroup.mk' (pCore 2 ↥X) z ∈
      Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥X)) : Set (oTwoQuot ↥X)) ↔
        (z : G) ∈ Subgroup.normalizer (T : Set G) := fun z => by
    rw [← Subgroup.mem_comap, comap_normalizer_oTwoQuot hT hP, Subgroup.mem_subgroupOf]
  obtain ⟨ū, hū, hu⟩ := hK.trans P (QuotientGroup.mk' _ ⟨x, hx⟩) (QuotientGroup.mk' _ ⟨y, hy⟩)
    (fun h => hxN ((hmem _).mp h)) (fun h => hyN ((hmem _).mp h))
  rw [hP] at hū
  obtain ⟨u', hu', rfl⟩ := hū
  refine ⟨u', hu', ?_⟩
  have := (hmem (⟨y, hy⟩⁻¹ * u' * ⟨x, hx⟩)).mp (by simpa [map_mul, map_inv] using hu)
  simpa using this

theorem lift_reg {u x : G} (hu : u ∈ T) (hx : x ∈ X)
    (hxN : x ∉ Subgroup.normalizer (T : Set G))
    (hux : x⁻¹ * u * x ∈ Subgroup.normalizer (T : Set G)) : u ∈ pCoreOf 2 X := by
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  have hmem : ∀ z : ↥X, QuotientGroup.mk' (pCore 2 ↥X) z ∈
      Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥X)) : Set (oTwoQuot ↥X)) ↔
        (z : G) ∈ Subgroup.normalizer (T : Set G) := fun z => by
    rw [← Subgroup.mem_comap, comap_normalizer_oTwoQuot hT hP, Subgroup.mem_subgroupOf]
  have huP : QuotientGroup.mk' (pCore 2 ↥X) ⟨u, hT.1 hu⟩ ∈ (P : Subgroup (oTwoQuot ↥X)) := by
    rw [hP]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
  have hconj : QuotientGroup.mk' (pCore 2 ↥X) (⟨x, hx⟩⁻¹ * ⟨u, hT.1 hu⟩ * ⟨x, hx⟩) ∈
      Subgroup.normalizer ((P : Subgroup (oTwoQuot ↥X)) : Set (oTwoQuot ↥X)) :=
    (hmem _).mpr (by simpa using hux)
  have h1 := hK.reg P _ huP (QuotientGroup.mk' _ ⟨x, hx⟩) (fun h => hxN ((hmem _).mp h))
    (by simpa [map_mul, map_inv] using hconj)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact (F1.mem_pCore_iff_coe _).mp h1

theorem lift_relIndex : (Subgroup.normalizer (T : Set G)).relIndex X = q ^ i + 1 := by
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot hT
  rw [Subgroup.relIndex, ← comap_normalizer_oTwoQuot hT hP,
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 ↥X))]
  exact hK.index_eq P

omit hT in
theorem le_oddGen_sup_pCoreOf : X ≤ oddGen X ⊔ pCoreOf 2 X := by
  set π : ↥X →* oTwoQuot ↥X := QuotientGroup.mk' (pCore 2 ↥X) with hπ
  set M : Subgroup ↥X := (oddGen X ⊔ pCoreOf 2 X).subgroupOf X with hM
  have hker : π.ker ≤ M := by
    rw [hπ, QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 X]
    exact Subgroup.comap_mono le_sup_right
  have hodd : ∀ k : oTwoQuot ↥X, Odd (orderOf k) → k ∈ M.map π := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥X) k
    obtain ⟨a, ha⟩ := MS93.exists_pow_mem_oddGen x.2
    have hcop : (2 ^ a).Coprime (orderOf (π x)) :=
      Nat.Coprime.pow_left a hk.coprime_two_left
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    refine Subgroup.pow_mem (M.map π) (Subgroup.mem_map.mpr ⟨x ^ 2 ^ a, ?_, by simp [hπ]⟩) m
    exact Subgroup.mem_sup_left ha
  have htop : M.map π = ⊤ := eq_top_iff.mpr (by
    rw [← hK.oddGen, Subgroup.closure_le]
    exact hodd)
  have hM' : M = ⊤ := by
    have h := Subgroup.comap_map_eq π M
    rw [htop, Subgroup.comap_top, sup_of_le_left hker] at h
    exact h.symm
  intro x hx
  have : (⟨x, hx⟩ : ↥X) ∈ M := hM' ▸ Subgroup.mem_top _
  exact this

end Lift

theorem le_normalizer_oddGen_of_le_normalizer {X Y : Subgroup G}
    (h : Y ≤ Subgroup.normalizer (X : Set G)) : Y ≤ Subgroup.normalizer (oddGen X : Set G) := by
  refine F7.le_normalizer_closure _ fun g hg s hs => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (h hg) s).mp hs.1
  · have := MulEquiv.orderOf_eq (MulAut.conj g) s
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hs.2

def UnipotentAt {G₀ G₁ G₂ : Subgroup G} (μ δ : CosetGeom G₀ G₁ G₂) (L : Subgroup G) : Prop :=
  ∃ U : Subgroup G, U ≤ L ∧ IsPGroup 2 U ∧ U ≤ stab δ ∧
    (∀ ε ∈ nbrs μ, ∀ ε' ∈ nbrs μ, ε ≠ δ → ε' ≠ δ → ∃ g : ↥G₀, (g : G) ∈ U ∧ g • ε = ε') ∧
    (∀ g : ↥G₀, (g : G) ∈ U → ∀ ε ∈ nbrs μ, ε ≠ δ → g • ε = ε → (g : G) ∈ ballStab 1 μ) ∧
    stab μ ⊓ stab δ ≤ Subgroup.normalizer ((U ⊔ ballStab 1 μ : Subgroup G) : Set G)

theorem UnipotentAt.smul {G₀ G₁ G₂ : Subgroup G} {μ δ : CosetGeom G₀ G₁ G₂} {L : Subgroup G}
    (h : UnipotentAt μ δ L) (g : ↥G₀) : UnipotentAt (g • μ) (g • δ) (conjSub (g : G) L) := by
  obtain ⟨U, hUL, hU2, hUδ, hUtr, hUreg, hUn⟩ := h
  refine ⟨conjSub (g : G) U, conjSub_mono _ hUL, F7.isPGroup_conjSub hU2, ?_, ?_, ?_, ?_⟩
  · rw [CosetGeom.stab_smul]
    exact conjSub_mono _ hUδ
  · intro ε hε ε' hε' hne hne'
    obtain ⟨e, rfl⟩ : ∃ e, ε = g • e := ⟨g⁻¹ • ε, by simp⟩
    obtain ⟨e', rfl⟩ : ∃ e', ε' = g • e' := ⟨g⁻¹ • ε', by simp⟩
    have he : e ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε
    have he' : e' ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε'
    obtain ⟨k, hkU, hk⟩ :=
      hUtr e he e' he' (fun h => hne (by rw [h])) (fun h => hne' (by rw [h]))
    refine ⟨g * k * g⁻¹, ?_, ?_⟩
    · show (g : G) * (k : G) * (g : G)⁻¹ ∈ conjSub (g : G) U
      exact mul_mem_conjSub hkU
    · rw [mul_smul, mul_smul, inv_smul_smul, hk]
  · intro k hk ε hε hne hfix
    obtain ⟨e, rfl⟩ : ∃ e, ε = g • e := ⟨g⁻¹ • ε, by simp⟩
    have he : e ∈ nbrs μ := (CosetGeom.smul_adj g).mp hε
    rw [CosetGeom.ballStab_smul, mem_conjSub]
    have hk' : ((g⁻¹ * k * g : ↥G₀) : G) ∈ U := mem_conjSub.mp hk
    refine hUreg (g⁻¹ * k * g) hk' e he (fun h => hne (by rw [h])) ?_
    have h1 : k • g • e = g • e := hfix
    calc (g⁻¹ * k * g) • e = g⁻¹ • (k • (g • e)) := by simp [mul_smul]
      _ = g⁻¹ • (g • e) := by rw [h1]
      _ = e := inv_smul_smul g e
  · rw [CosetGeom.stab_smul, CosetGeom.stab_smul, ← conjSub_inf, CosetGeom.ballStab_smul,
      ← conjSub_sup]
    exact conjSub_le_normalizer hUn

theorem smul_eq_of_mem_ballStab_one {G₀ G₁ G₂ : Subgroup G} {μ ε : CosetGeom G₀ G₁ G₂}
    (hε : ε ∈ nbrs μ) {g : ↥G₀} (hg : (g : G) ∈ ballStab 1 μ) : g • ε = ε :=
  CosetGeom.smul_eq_of_mem_stab
    (CosetGeom.mem_ballStab.mp hg ε (CosetGeom.dist_eq_one_iff_adj.mpr hε).le)

theorem smul_eq_smul_iff_mem_stab {G₀ G₁ G₂ : Subgroup G} {γ : CosetGeom G₀ G₁ G₂}
    {g h : ↥G₀} : g • γ = h • γ ↔ (g : G)⁻¹ * (h : G) ∈ stab γ := by
  rw [eq_comm, ← inv_smul_eq_iff, ← mul_smul]
  exact ⟨fun hh => CosetGeom.mem_stab_of_smul_eq hh, fun hh => CosetGeom.smul_eq_of_mem_stab hh⟩

section Base

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "𝒱" => CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem stab_γ₀_eq (hs : Setting L₁ L₂ S Z) : stab ν₀ = P₂ L₁ L₂ S :=
  hs.toCritAmalgam.stab_γ₀_eq

theorem stab_γ₁_eq (hs : Setting L₁ L₂ S Z) : stab ν₁ = P₁ L₁ L₂ S :=
  hs.toCritAmalgam.stab_γ₁_eq

theorem bigB_le_normalizer (hs : Setting L₁ L₂ S Z) :
    bigB L₁ L₂ S ≤ Subgroup.normalizer (L₂ : Set G) :=
  (F1.bigB_le_normalizer_left hs.hyp).2

theorem bigB_le_normalizer_inf (hs : Setting L₁ L₂ S Z) :
    bigB L₁ L₂ S ≤ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) :=
  (F1.bigB_le_normalizer_sylow hs.hyp).2

theorem P₂_le_normalizer (hs : Setting L₁ L₂ S Z) :
    P₂ L₁ L₂ S ≤ Subgroup.normalizer (L₂ : Set G) :=
  sup_le Subgroup.le_normalizer (bigB_le_normalizer hs)

theorem isSylowTwoOf_inf (hs : Setting L₁ L₂ S Z) : IsSylowTwoOf (S ⊓ L₂) L₂ :=
  hs.hyp.hyp.h2.sylow

theorem pCoreOf_le_inf (hs : Setting L₁ L₂ S Z) : pCoreOf 2 L₂ ≤ S ⊓ L₂ :=
  F7.isSylowTwoOf_pCoreOf_le (isSylowTwoOf_inf hs)

theorem S_le_bigB : S ≤ bigB L₁ L₂ S := le_sup_right

theorem borelOf_le_bigB : borelOf L₂ S ≤ bigB L₁ L₂ S := le_sup_right.trans le_sup_left

theorem bigB_le_P₁ : bigB L₁ L₂ S ≤ P₁ L₁ L₂ S := le_sup_right

theorem bigB_le_P₂ : bigB L₁ L₂ S ≤ P₂ L₁ L₂ S := le_sup_right

theorem pCoreOf_le_bigB (hs : Setting L₁ L₂ S Z) : pCoreOf 2 L₂ ≤ bigB L₁ L₂ S :=
  (pCoreOf_le_inf hs).trans (inf_le_left.trans S_le_bigB)

theorem mem_P₁_iff (hs : Setting L₁ L₂ S Z) {x : G} (hx : x ∈ L₂) :
    x ∈ P₁ L₁ L₂ S ↔ x ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := by
  constructor
  · intro h
    have hB : x ∈ bigB L₁ L₂ S := by
      rw [← F112W.inf_alpha_beta hs.hyp]
      exact ⟨Subgroup.mem_sup_left hx, h⟩
    exact bigB_le_normalizer_inf hs hB
  · intro h
    have hB : x ∈ borelOf L₂ S := ⟨hx, h⟩
    exact bigB_le_P₁ (borelOf_le_bigB hB)

theorem pCoreOf_le_ballStab (hs : Setting L₁ L₂ S Z) : pCoreOf 2 L₂ ≤ ballStab 1 ν₀ := by
  refine (CosetGeom.ballStab_one_γ₀ hs.toCritAmalgam.amalgam.gen).2.2 ⟨?_, ?_⟩
  · rw [F112W.inf_alpha_beta hs.hyp]
    exact pCoreOf_le_bigB hs
  · exact F7.le_normalizer_pCoreOf_of_le_normalizer (P₂_le_normalizer hs)

theorem smul_γ₁_eq_iff (hs : Setting L₁ L₂ S Z) {x : ↥(L₁ ⊔ L₂ ⊔ S)} (hx : (x : G) ∈ L₂) :
    x • ν₁ = ν₁ ↔ (x : G) ∈ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := by
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ (mem_P₁_iff hs hx)
  · have := CosetGeom.mem_stab_of_smul_eq h
    rwa [stab_γ₁_eq hs] at this
  · exact CosetGeom.smul_eq_of_mem_stab (by rwa [stab_γ₁_eq hs])

theorem le_normalizer_inf_sup_ballStab (hs : Setting L₁ L₂ S Z) :
    bigB L₁ L₂ S ≤
      Subgroup.normalizer (((S ⊓ L₂) ⊔ ballStab 1 ν₀ : Subgroup G) : Set G) := by
  have h := CosetGeom.le_normalizer_ballStab 1 ν₀
  rw [stab_γ₀_eq hs] at h
  exact F1.le_normalizer_sup (bigB_le_normalizer_inf hs) (bigB_le_P₂.trans h)

section Quot

variable {q i : ℕ} (hK : IsBenderQuot (oTwoQuot ↥L₂) q i)
include hK

theorem exists_mul_of_mem_P₂ (hs : Setting L₁ L₂ S Z) {p : G} (hp : p ∈ P₂ L₁ L₂ S) :
    ∃ l ∈ oddGen L₂, ∃ b ∈ bigB L₁ L₂ S, p = l * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes (bigB_le_normalizer hs)).mp hp
  obtain ⟨l, hl, o, ho, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
    ((MS93.oddGen_le L₂).trans (le_normalizer_pCoreOf 2 L₂))).mp
      (le_oddGen_sup_pCoreOf hK ha)
  exact ⟨l, hl, o * b, (bigB L₁ L₂ S).mul_mem (pCoreOf_le_bigB hs ho) hb, by rw [mul_assoc]⟩

theorem exists_mul_inf_oddGen (hs : Setting L₁ L₂ S Z) {u : G} (hu : u ∈ S ⊓ L₂) :
    ∃ u₀ ∈ S ⊓ oddGen L₂, ∃ o ∈ pCoreOf 2 L₂, u = u₀ * o := by
  obtain ⟨l, hl, o, ho, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_le_normalizer
    ((MS93.oddGen_le L₂).trans (le_normalizer_pCoreOf 2 L₂))).mp
      (le_oddGen_sup_pCoreOf hK hu.2)
  refine ⟨l, ⟨?_, hl⟩, o, ho, rfl⟩
  have h : l = (l * o) * o⁻¹ := by group
  rw [h]
  exact S.mul_mem hu.1 (S.inv_mem (pCoreOf_le_inf hs ho).1)

theorem exists_smul_γ₁_eq (hs : Setting L₁ L₂ S Z) {δ : 𝒱} (hδ : δ ∈ nbrs ν₀) :
    ∃ g : ↥(L₁ ⊔ L₂ ⊔ S), (g : G) ∈ oddGen L₂ ∧ g • ν₁ = δ := by
  have hA := hs.toCritAmalgam.amalgam
  obtain ⟨g, hg, hgδ⟩ := CosetGeom.stab_transitive_on_nbrs
    (show ν₁ ∈ nbrs ν₀ from CosetGeom.adj_γ₀_γ₁) hδ
  rw [stab_γ₀_eq hs] at hg
  obtain ⟨l, hl, b, hb, hgb⟩ := exists_mul_of_mem_P₂ hK hs hg
  have hlΛ : l ∈ L₁ ⊔ L₂ ⊔ S :=
    hA.le₁ (Subgroup.mem_sup_left (MS93.oddGen_le L₂ hl))
  have hbP₁ : b ∈ P₁ L₁ L₂ S := bigB_le_P₁ hb
  refine ⟨⟨l, hlΛ⟩, hl, ?_⟩
  rw [← hgδ]
  have hg' : g = ⟨l, hlΛ⟩ * ⟨b, hA.le₂ hbP₁⟩ := Subtype.ext hgb
  rw [hg', mul_smul, CosetGeom.smul_γ₁_of_mem hA.le₂ hbP₁]

theorem inf_oddGen_trans (hs : Setting L₁ L₂ S Z) {ε ε' : 𝒱} (hε : ε ∈ nbrs ν₀)
    (hε' : ε' ∈ nbrs ν₀) (hne : ε ≠ ν₁) (hne' : ε' ≠ ν₁) :
    ∃ g : ↥(L₁ ⊔ L₂ ⊔ S), (g : G) ∈ S ⊓ oddGen L₂ ∧ g • ε = ε' := by
  obtain ⟨x, hxL, rfl⟩ := exists_smul_γ₁_eq hK hs hε
  obtain ⟨y, hyL, rfl⟩ := exists_smul_γ₁_eq hK hs hε'
  have hx₂ : (x : G) ∈ L₂ := MS93.oddGen_le L₂ hxL
  have hy₂ : (y : G) ∈ L₂ := MS93.oddGen_le L₂ hyL
  have hxN : (x : G) ∉ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := fun h =>
    hne ((smul_γ₁_eq_iff hs hx₂).mpr h)
  have hyN : (y : G) ∉ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := fun h =>
    hne' ((smul_γ₁_eq_iff hs hy₂).mpr h)
  obtain ⟨u, hu, huN⟩ := lift_trans hK (isSylowTwoOf_inf hs) hx₂ hy₂ hxN hyN
  obtain ⟨u₀, hu₀, o, ho, rfl⟩ := exists_mul_inf_oddGen hK hs hu
  have hu₀Λ : u₀ ∈ L₁ ⊔ L₂ ⊔ S := Subgroup.mem_sup_right hu₀.1
  have hoΛ : o ∈ L₁ ⊔ L₂ ⊔ S :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (pCoreOf_le 2 L₂ ho))
  refine ⟨⟨u₀, hu₀Λ⟩, hu₀, ?_⟩
  have h1 : (⟨u₀, hu₀Λ⟩ * ⟨o, hoΛ⟩ * x : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁ = y • ν₁ := by
    rw [smul_eq_smul_iff_mem_stab, stab_γ₁_eq hs]
    have h2 : ((y : G)⁻¹ * (u₀ * o) * x)⁻¹ ∈ P₁ L₁ L₂ S := by
      refine (P₁ L₁ L₂ S).inv_mem ((mem_P₁_iff hs ?_).mpr huN)
      exact L₂.mul_mem (L₂.mul_mem (L₂.inv_mem hy₂) hu.2) hx₂
    simpa [mul_assoc] using h2
  have h3 : (⟨o, hoΛ⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • (x • ν₁) = x • ν₁ :=
    smul_eq_of_mem_ballStab_one hε (pCoreOf_le_ballStab hs ho)
  rw [← h1, mul_smul, mul_smul, h3]

theorem inf_oddGen_reg (hs : Setting L₁ L₂ S Z) {g : ↥(L₁ ⊔ L₂ ⊔ S)}
    (hg : (g : G) ∈ S ⊓ oddGen L₂) {ε : 𝒱} (hε : ε ∈ nbrs ν₀) (hne : ε ≠ ν₁)
    (hfix : g • ε = ε) : (g : G) ∈ ballStab 1 ν₀ := by
  obtain ⟨x, hxL, rfl⟩ := exists_smul_γ₁_eq hK hs hε
  have hx₂ : (x : G) ∈ L₂ := MS93.oddGen_le L₂ hxL
  have hxN : (x : G) ∉ Subgroup.normalizer ((S ⊓ L₂ : Subgroup G) : Set G) := fun h =>
    hne ((smul_γ₁_eq_iff hs hx₂).mpr h)
  have hg₂ : (g : G) ∈ L₂ := MS93.oddGen_le L₂ hg.2
  have h1 : (x : G)⁻¹ * g * x ∈ P₁ L₁ L₂ S := by
    have h := smul_eq_smul_iff_mem_stab.mp (show (1 : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁ =
      (x⁻¹ * g * x : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁ by
        rw [one_smul, mul_smul, mul_smul, hfix, inv_smul_smul])
    rw [stab_γ₁_eq hs] at h
    simpa using h
  have h2 : (x : G)⁻¹ * g * x ∈ L₂ := L₂.mul_mem (L₂.mul_mem (L₂.inv_mem hx₂) hg₂) hx₂
  exact pCoreOf_le_ballStab hs (lift_reg hK (isSylowTwoOf_inf hs) (u := g) ⟨hg.1, hg₂⟩ hx₂
    hxN ((mem_P₁_iff hs h2).mp h1))

theorem inf_oddGen_sup_ballStab (hs : Setting L₁ L₂ S Z) :
    (S ⊓ oddGen L₂) ⊔ ballStab 1 ν₀ = (S ⊓ L₂) ⊔ ballStab 1 ν₀ := by
  refine le_antisymm (sup_le_sup_right (inf_le_inf_left S (MS93.oddGen_le L₂)) _)
    (sup_le (fun u hu => ?_) le_sup_right)
  obtain ⟨u₀, hu₀, o, ho, rfl⟩ := exists_mul_inf_oddGen hK hs hu
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₀)
    (Subgroup.mem_sup_right (pCoreOf_le_ballStab hs ho))

theorem unipotentAt_γ₁ (hs : Setting L₁ L₂ S Z) : UnipotentAt ν₀ ν₁ (oddGen L₂) := by
  refine ⟨S ⊓ oddGen L₂, inf_le_right, hs.hyp.hyp.h2.pgroup.to_le inf_le_left, ?_,
    fun ε hε ε' hε' hne hne' => inf_oddGen_trans hK hs hε hε' hne hne',
    fun g hg ε hε hne hfix => inf_oddGen_reg hK hs hg hε hne hfix, ?_⟩
  · rw [stab_γ₁_eq hs]
    exact inf_le_left.trans (S_le_bigB.trans bigB_le_P₁)
  · rw [stab_γ₀_eq hs, stab_γ₁_eq hs, F112W.inf_alpha_beta hs.hyp, inf_oddGen_sup_ballStab hK hs]
    exact le_normalizer_inf_sup_ballStab hs

end Quot

end Base

end BenderLocalOf

namespace Setting

variable {L₁ L₂ S Z : Subgroup G} [Finite G]

theorem benderLocal (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) :
    BenderLocal (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) (oddGen L₂) := by
  refine { le_stab := ?_, normal := ?_, odd_gen := ?_, trans := ?_, unipotent := ?_ }
  · rw [BenderLocalOf.stab_γ₀_eq hs]
    exact (MS93.oddGen_le L₂).trans le_sup_left
  · rw [BenderLocalOf.stab_γ₀_eq hs]
    exact sup_le (MS93.le_normalizer_oddGen L₂) (BenderLocalOf.le_normalizer_oddGen_of_le_normalizer
      (BenderLocalOf.bigB_le_normalizer hs))
  · exact Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩
  · intro δ hδ δ' hδ'
    obtain ⟨g, hg, rfl⟩ := BenderLocalOf.exists_smul_γ₁_eq hK hs hδ
    obtain ⟨g', hg', rfl⟩ := BenderLocalOf.exists_smul_γ₁_eq hK hs hδ'
    refine ⟨g' * g⁻¹, ?_, by rw [mul_smul, inv_smul_smul]⟩
    exact (oddGen L₂).mul_mem hg' ((oddGen L₂).inv_mem hg)
  · intro δ hδ
    obtain ⟨g, hg, rfl⟩ := BenderLocalOf.exists_smul_γ₁_eq hK hs hδ
    have h := (BenderLocalOf.unipotentAt_γ₁ hK hs).smul g
    have h0 : g • γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) =
        γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) := by
      refine CosetGeom.smul_eq_of_mem_stab ?_
      rw [BenderLocalOf.stab_γ₀_eq hs]
      exact Subgroup.mem_sup_left (MS93.oddGen_le L₂ hg)
    have hL : conjSub (g : G) (oddGen L₂) = oddGen L₂ :=
      F1.conjSub_eq_of_mem_normalizer (MS93.le_normalizer_oddGen L₂ (MS93.oddGen_le L₂ hg))
    rw [h0, hL] at h
    exact h

theorem card_nbrs_γ₀ (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) :
    Nat.card (nbrs (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S))) = q ^ i + 1 := by
  have hB : L₂ ⊓ bigB L₁ L₂ S = borelOf L₂ S := by
    have := F1.inf_bigB_eq_borelOf hs.hyp.symm
    rwa [bigB_comm] at this
  rw [CosetGeom.card_nbrs_eq_relIndex_geom (show γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) ∈
      nbrs (γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)) from CosetGeom.adj_γ₀_γ₁),
    BenderLocalOf.stab_γ₀_eq hs, BenderLocalOf.stab_γ₁_eq hs, F112W.inf_alpha_beta hs.hyp,
    F112W.relIndex_sup_eq_relIndex_inf (BenderLocalOf.bigB_le_normalizer hs), hB, borelOf,
    inf_comm, Subgroup.inf_relIndex_right]
  exact BenderLocalOf.lift_relIndex hK (BenderLocalOf.isSylowTwoOf_inf hs)

end Setting

end CFSG.Quasithin.F112Crit

end
