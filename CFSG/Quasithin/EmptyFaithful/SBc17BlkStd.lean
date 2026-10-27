module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.EmptyFaithful.SBc17SL2Defs
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace SBc17

@[expose] def SylowConjStatement : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2], 4 ≤ Fintype.card F →
    ∀ P : Subgroup (SL2 F), IsPGroup 2 P → ¬ 2 ∣ P.index →
      ∃ g : SL2 F, ∀ x : SL2 F, x ∈ P ↔ g⁻¹ * x * g ∈ upperSub F

@[expose] def NormalizerUpperStatement : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2], 4 ≤ Fintype.card F →
    Subgroup.normalizer (upperSub F : Set (SL2 F)) = borelSub F

namespace BlkStd

theorem uElt_injective {F : Type} [Field F] : Function.Injective (uElt : F → SL2 F) := by
  intro x y h
  have h01 := congrArg (fun g : SL2 F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [uElt] using h01

theorem four_le_natCard {F : Type} [Field F] [Fintype F] (hq : 4 ≤ Fintype.card F) :
    4 ≤ Nat.card (SL2 F) := by
  calc 4 ≤ Fintype.card F := hq
    _ = Nat.card F := (Nat.card_eq_fintype_card).symm
    _ ≤ Nat.card (SL2 F) := Nat.card_le_card_of_injective _ uElt_injective

theorem mem_normalizer_iff_conj {H : Type*} [Group H] {P U : Subgroup H} {c : H}
    (hP : ∀ x : H, x ∈ P ↔ c⁻¹ * x * c ∈ U) (z : H) :
    z ∈ Subgroup.normalizer (P : Set H) ↔ c⁻¹ * z * c ∈ Subgroup.normalizer (U : Set H) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h u
    have h1 := h (c * u * c⁻¹)
    rw [hP, hP] at h1
    have e1 : c⁻¹ * (c * u * c⁻¹) * c = u := by group
    have e2 : c⁻¹ * (z * (c * u * c⁻¹) * z⁻¹) * c = (c⁻¹ * z * c) * u * (c⁻¹ * z * c)⁻¹ := by
      group
    rwa [e1, e2] at h1
  · intro h x
    have h1 := h (c⁻¹ * x * c)
    rw [hP, hP]
    have e2 : (c⁻¹ * z * c) * (c⁻¹ * x * c) * (c⁻¹ * z * c)⁻¹ = c⁻¹ * (z * x * z⁻¹) * c := by
      group
    rwa [e2] at h1

theorem mem_pCore_iff_coe {G : Type*} [Group G] {L : Subgroup G} (x : ↥L) :
    x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ pCoreOf 2 L := (CFSG.mem_openPCoreOf_iff x).symm

end BlkStd

variable {G : Type*} [Group G]

theorem exists_std_position (hS : SylowConjStatement) (hN : NormalizerUpperStatement) [Finite G]
    {L B : Subgroup G} {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    (hq : 4 ≤ Fintype.card F) (α : ↥L →* SL2 F) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) (hB : IsBorelOfBlock L B) :
    ∃ g₀ : G, g₀ ∈ L ∧ (∀ x : G, x ∈ conjSub g₀⁻¹ B → x ∈ L) ∧
      ∀ g : SL2 F, g ∈ borelSub F ↔ ∃ (x : G) (hx : x ∈ L), x ∈ conjSub g₀⁻¹ B ∧ α ⟨x, hx⟩ = g := by
  have h3 : ¬ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3 := by
    rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv]
    have := BlkStd.four_le_natCard hq
    omega
  simp only [IsBorelOfBlock, h3, ↓reduceIte] at hB
  obtain ⟨S, hSsyl, hBS⟩ := hB
  have hSL : S ≤ L := hSsyl.1
  have hQS : pCoreOf 2 L ≤ S := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSsyl
  have hQL : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hBL : B ≤ L := le_sup_left.trans (hBS.le.trans inf_le_left)
  have hKS : α.ker ≤ S.subgroupOf L := by
    intro x hx
    rw [hker] at hx
    rw [Subgroup.mem_subgroupOf]
    exact hQS ((BlkStd.mem_pCore_iff_coe x).1 hx)
  set P : Subgroup (SL2 F) := (S.subgroupOf L).map α with hPdef
  have hPS : P.comap α = S.subgroupOf L := by
    rw [hPdef, Subgroup.comap_map_eq, sup_eq_left.2 hKS]
  have hPp : IsPGroup 2 P :=
    (hSsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm).map α
  have hPi : ¬ 2 ∣ P.index := by
    rw [← Subgroup.index_comap_of_surjective P hα, hPS]
    exact hSsyl.2.2
  obtain ⟨c, hc⟩ := hS F hq P hPp hPi
  have hNP : ∀ z : SL2 F, z ∈ Subgroup.normalizer (P : Set (SL2 F)) ↔ c⁻¹ * z * c ∈ borelSub F := by
    intro z
    rw [BlkStd.mem_normalizer_iff_conj hc z, hN F hq]
  have hNimg : Subgroup.normalizer (P : Set (SL2 F)) =
      ((Subgroup.normalizer (S : Set G)).subgroupOf L).map α := by
    have h1 : (Subgroup.normalizer (S : Set G)).subgroupOf L =
        (Subgroup.normalizer (P : Set (SL2 F))).comap α := by
      rw [Subgroup.subgroupOf_normalizer_eq hSL, Subgroup.comap_normalizer_eq_of_surjective P hα,
        hPS]
    rw [h1, Subgroup.map_comap_eq_self_of_surjective hα]
  have hBimg : (B.subgroupOf L).map α = Subgroup.normalizer (P : Set (SL2 F)) := by
    rw [hNimg]
    have h1 : (Subgroup.normalizer (S : Set G)).subgroupOf L =
        B.subgroupOf L ⊔ (pCoreOf 2 L).subgroupOf L := by
      rw [← Subgroup.subgroupOf_sup hBL hQL, hBS, Subgroup.inf_subgroupOf_left]
    have h2 : ((pCoreOf 2 L).subgroupOf L).map α = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro x hx
      rw [hker]
      exact (BlkStd.mem_pCore_iff_coe x).2 (Subgroup.mem_subgroupOf.1 hx)
    rw [h1, Subgroup.map_sup, h2, sup_bot_eq]
  obtain ⟨g₀, hg₀⟩ := hα c
  refine ⟨(g₀ : G), g₀.2, ?_, ?_⟩
  · intro x hx
    rw [mem_conjSub] at hx
    have hxB : (g₀ : G) * x * (g₀ : G)⁻¹ ∈ B := by simpa using hx
    have e : (g₀ : G)⁻¹ * ((g₀ : G) * x * (g₀ : G)⁻¹) * g₀ = x := by group
    rw [← e]
    exact L.mul_mem (L.mul_mem (L.inv_mem g₀.2) (hBL hxB)) g₀.2
  · intro g
    constructor
    · intro hg
      have hz : c * g * c⁻¹ ∈ Subgroup.normalizer (P : Set (SL2 F)) := by
        have e : c⁻¹ * (c * g * c⁻¹) * c = g := by group
        rw [hNP, e]
        exact hg
      rw [← hBimg] at hz
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨(g₀ : G)⁻¹ * (b : G) * g₀,
        L.mul_mem (L.mul_mem (L.inv_mem g₀.2) b.2) g₀.2, ?_, ?_⟩
      · rw [mem_conjSub]
        have e : ((g₀ : G)⁻¹)⁻¹ * ((g₀ : G)⁻¹ * (b : G) * g₀) * (g₀ : G)⁻¹ = (b : G) := by group
        rw [e]
        exact Subgroup.mem_subgroupOf.1 hb
      · have e : (⟨(g₀ : G)⁻¹ * (b : G) * g₀,
            L.mul_mem (L.mul_mem (L.inv_mem g₀.2) b.2) g₀.2⟩ : ↥L) = g₀⁻¹ * b * g₀ :=
          Subtype.ext rfl
        rw [e, map_mul, map_mul, map_inv, hg₀]
        have hbz' : α b = c * g * c⁻¹ := hbz
        rw [hbz']
        group
    · rintro ⟨x, hx, hxB, rfl⟩
      rw [mem_conjSub] at hxB
      have hxB' : (g₀ : G) * x * (g₀ : G)⁻¹ ∈ B := by simpa using hxB
      have hb : (g₀ * ⟨x, hx⟩ * g₀⁻¹ : ↥L) ∈ B.subgroupOf L := hxB'
      have hz : α (g₀ * ⟨x, hx⟩ * g₀⁻¹) ∈ Subgroup.normalizer (P : Set (SL2 F)) := by
        rw [← hBimg]
        exact ⟨_, hb, rfl⟩
      rw [hNP, map_mul, map_mul, map_inv, hg₀] at hz
      have e : c⁻¹ * (c * α ⟨x, hx⟩ * c⁻¹) * c = α ⟨x, hx⟩ := by group
      rwa [e] at hz

end SBc17

end CFSG.Quasithin
