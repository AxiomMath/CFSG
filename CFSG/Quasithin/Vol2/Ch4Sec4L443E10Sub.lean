module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443E7Le

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem isPGroup_subgroupOf {p : ℕ} {A : Subgroup G} (hA : IsPGroup p A) (K : Subgroup G) :
    IsPGroup p (A.subgroupOf K) :=
  hA.comap_subtype

theorem subgroupOf_ne_bot {A K : Subgroup G} (hAK : A ≤ K) (hA : A ≠ ⊥) : A.subgroupOf K ≠ ⊥ :=
  fun h => hA (by rw [← Subgroup.map_subgroupOf_eq_of_le hAK, h, Subgroup.map_bot])

theorem mem_normalizer_subgroupOf {A K : Subgroup G} {x : ↥K}
    (hx : (x : G) ∈ Subgroup.normalizer (A : Set G)) :
    x ∈ Subgroup.normalizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact hx y

theorem le_normalizer_subgroupOf {A B : Subgroup G} (K : Subgroup G)
    (h : B ≤ Subgroup.normalizer (A : Set G)) :
    B.subgroupOf K ≤ Subgroup.normalizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K) :=
  fun _ hx => mem_normalizer_subgroupOf (h hx)

theorem coe_mem_normalizer_map {K : Subgroup G} {P : Subgroup ↥K} {x : ↥K}
    (hx : x ∈ Subgroup.normalizer (P : Set ↥K)) :
    (x : G) ∈ Subgroup.normalizer ((P.map K.subtype : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype hx)

theorem coe_mem_centralizer {A K : Subgroup G} (hAK : A ≤ K) {x : ↥K}
    (hx : x ∈ Subgroup.centralizer ((A.subgroupOf K : Subgroup ↥K) : Set ↥K)) :
    (x : G) ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro a ha
  exact congrArg Subtype.val (hx ⟨a, hAK ha⟩ ha)

variable [Finite G]

theorem subgroupOf_pCoreOf_le (p : ℕ) [Fact p.Prime] (A K : Subgroup G) :
    (pCoreOf p A).subgroupOf K ≤ pCoreOf p (A.subgroupOf K) :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer p (fun _ hx => pCoreOf_le p A hx)
    (le_normalizer_subgroupOf K (le_normalizer_pCoreOf p A))
    (isPGroup_subgroupOf (pCoreOf_isPGroup p A) K)

theorem pCoreOf_top_eq_bot {K : Subgroup G} (h : pCoreOf 2 K = ⊥) :
    pCoreOf 2 (⊤ : Subgroup ↥K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (pCoreOf 2 (⊤ : Subgroup ↥K)).map K.subtype ≤ pCoreOf 2 K :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _)
      (fun x hx => coe_mem_normalizer_map (x := ⟨x, hx⟩)
        (le_normalizer_pCoreOf 2 (⊤ : Subgroup ↥K) (Subgroup.mem_top _)))
      ((pCoreOf_isPGroup 2 _).map K.subtype)
  rwa [h, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h1

theorem pCoreOf_inf_le (A K : Subgroup G) : pCoreOf 2 A ⊓ K ≤ pCoreOf 2 (A ⊓ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_inf_right K (pCoreOf_le 2 A))
    (fun x hx => ?_)
    ((pCoreOf_isPGroup 2 A).to_le inf_le_left)
  exact (mem_normalizer_inf_sup (le_normalizer_pCoreOf 2 A hx.1)
    (Subgroup.le_normalizer hx.2)).1

end CFSG.Quasithin.H13.Ch4.E443
