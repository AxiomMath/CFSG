module

public import CFSG.Quasithin.Vol2.Ch8Sec2L8210B
public import CFSG.Quasithin.Background.KGSchurMult2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

section L8210C

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] noncomputable def actHom82 {V : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G)) :
    ↥L →* ↥(autOn L V) :=
  ((conjAct V).comp (Subgroup.inclusion hLN)).codRestrict (autOn L V) fun l =>
    ⟨Subgroup.inclusion hLN l, l.2, rfl⟩

theorem actHom82_surjective {V : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G)) :
    Function.Surjective (actHom82 hLN) := by
  rintro ⟨_, ⟨g, hg, rfl⟩⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem mem_ker_actHom82 {V : Subgroup G} (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (l : ↥L) : l ∈ (actHom82 hLN).ker ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (conjAct_eq_one_iff_82 (Subgroup.inclusion hLN l)).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((conjAct_eq_one_iff_82 (Subgroup.inclusion hLN l)).mpr h)

variable [Finite G]

theorem quot_structure_of_82 (hsimp : HSimple82) {V W : Subgroup G} [hc : IsMulCommutative ↥V]
    (hmod : IsModel82 (V := ↥V) (autOn L V)) (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hperf : ⁅L, L⁆ = L) (hVW : V ≤ W) (hWQ : W ≤ pCoreOf 2 L)
    (hQL : ⁅pCoreOf 2 L, L⁆ ≤ V)
    (hCQ : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L)
    [hWn : (W.subgroupOf L).Normal] :
    CFSG.Open.IsQuasisimple (↥L ⧸ W.subgroupOf L) ∧
      Subgroup.center (↥L ⧸ W.subgroupOf L) =
        ((pCoreOf 2 L).subgroupOf L).map (QuotientGroup.mk' (W.subgroupOf L)) ∧
      Nonempty ((↥L ⧸ W.subgroupOf L) ⧸ Subgroup.center (↥L ⧸ W.subgroupOf L) ≃*
        ↥(autOn L V)) := by
  obtain ⟨hS, a₀, b₀, hab⟩ := hsimp ↥V (autOn L V) hmod
  set φ := actHom82 hLN with hφ
  have hker : φ.ker = (pCoreOf 2 L).subgroupOf L := by
    ext l
    rw [mem_ker_actHom82, Subgroup.mem_subgroupOf, ← hCQ]
    exact ⟨fun h => ⟨l.2, h⟩, fun h => h.2⟩
  have hWker : W.subgroupOf L ≤ φ.ker := by
    rw [hker]
    exact fun x hx => hWQ hx
  set ψ := QuotientGroup.lift (W.subgroupOf L) φ hWker with hψ
  have hψs : Function.Surjective ψ := by
    intro h
    obtain ⟨l, rfl⟩ := actHom82_surjective hLN h
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hψker : ψ.ker = ((pCoreOf 2 L).subgroupOf L).map (QuotientGroup.mk' (W.subgroupOf L)) := by
    rw [hψ, QuotientGroup.ker_lift, hker]
  have hZH : Subgroup.center ↥(autOn L V) = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(autOn L V)) with hc0 | hc0
    · exact hc0
    · exact absurd (Subgroup.mem_center_iff.mp (hc0 ▸ Subgroup.mem_top b₀) a₀) hab
  have hcen : Subgroup.center (↥L ⧸ W.subgroupOf L) = ψ.ker := by
    apply le_antisymm
    · intro c hc
      have h1 : ψ c ∈ Subgroup.center ↥(autOn L V) := by
        rw [Subgroup.mem_center_iff]
        intro h
        obtain ⟨k, rfl⟩ := hψs h
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc k]
      rw [hZH, Subgroup.mem_bot] at h1
      exact h1
    · rw [hψker]
      rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro k
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have hqQ : (q : G) ∈ pCoreOf 2 L := Subgroup.mem_subgroupOf.mp hq
      have h1 : ⁅(q : G)⁻¹, (l : G)⁻¹⁆ ∈ V :=
        hQL (Subgroup.commutator_mem_commutator ((pCoreOf 2 L).inv_mem hqQ) (L.inv_mem l.2))
      have h2 : (((l * q)⁻¹ * (q * l) : ↥L) : G) = ⁅(q : G)⁻¹, (l : G)⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [h2]
      exact hVW h1
  set e := (QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs) with he
  refine ⟨⟨?_, e.isSimpleGroup⟩, hcen.trans hψker, ⟨e⟩⟩
  have hLt : commutator ↥L = ⊤ := by
    have h1 : (commutator ↥L).map L.subtype = L := by
      change Subgroup.map L.subtype ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = L
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
    rw [eq_top_iff]
    intro x _
    have hx : (x : G) ∈ (commutator ↥L).map L.subtype := by
      rw [h1]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [Subgroup.subtype_injective _ hyx] at hy
  change ⁅(⊤ : Subgroup (↥L ⧸ W.subgroupOf L)), (⊤ : Subgroup (↥L ⧸ W.subgroupOf L))⁆ = ⊤
  rw [eq_top_iff]
  intro k _
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective k
  have hl : l ∈ ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ := by
    change l ∈ commutator ↥L
    rw [hLt]
    exact Subgroup.mem_top l
  have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (W.subgroupOf L)) hl
  rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    at h2
  exact h2

theorem pCoreOf_eq_of_m24_82 (hsimp : HSimple82) (hm24 : SchurMult2M24) {V : Subgroup G}
    [hc : IsMulCommutative ↥V] (hmod : IsModel82 (V := ↥V) (autOn L V))
    (hiso : IsSporadic .M24 ↥(autOn L V)) (hLN : L ≤ Subgroup.normalizer (V : Set G))
    (hperf : ⁅L, L⁆ = L) (hVQ : V ≤ pCoreOf 2 L) (hQL : ⁅pCoreOf 2 L, L⁆ ≤ V)
    (hCQ : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L) : pCoreOf 2 L = V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVn : (V.subgroupOf L).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLN
  obtain ⟨hq, hZ, ⟨e⟩⟩ := quot_structure_of_82 hsimp hmod hLN hperf le_rfl hVQ hQL hCQ
  have hQL' : pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hZp : IsPGroup 2 ↥(Subgroup.center (↥L ⧸ V.subgroupOf L)) := by
    rw [hZ]
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQL').symm).map _
  have hiso' : IsSporadic .M24 ((↥L ⧸ V.subgroupOf L) ⧸ Subgroup.center (↥L ⧸ V.subgroupOf L)) := by
    obtain ⟨f⟩ := hiso
    exact ⟨e.trans f⟩
  have h1 := hm24 (↥L ⧸ V.subgroupOf L) hq hZp hiso'
  rw [hZ] at h1
  refine le_antisymm (fun q hq' => ?_) hVQ
  have hqL : q ∈ L := hQL' hq'
  have h2 : QuotientGroup.mk' (V.subgroupOf L) ⟨q, hqL⟩ ∈
      ((pCoreOf 2 L).subgroupOf L).map (QuotientGroup.mk' (V.subgroupOf L)) :=
    ⟨⟨q, hqL⟩, hq', rfl⟩
  rw [h1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact h2

end L8210C

end CFSG.Quasithin.H13
