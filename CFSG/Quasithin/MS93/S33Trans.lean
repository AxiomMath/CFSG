module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.MS93.PUBase
public import CFSG.Quasithin.MS93.Sec2Basic

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem exists_conj_of_isCritical (h : Hyp20 X) (hb : 0 < critDist X) {γ γ' : Vtx X}
    (hc : IsCritical X γ γ') :
    ∃ k : X.Universal, k • baseA X = γ' ∧ k • baseB X = geo X γ' γ 1 ∧
      IsCritical X (k⁻¹ • γ) (baseA X) ∧ geo X (baseA X) (k⁻¹ • γ) 1 = baseB X := by
  have hγ' : IsMVtx X γ' := hc.isMVtx_right X h
  have hd : 0 < X.treeGraph.dist γ' γ := by
    rw [SimpleGraph.dist_comm, hc.2.1]
    exact hb
  have hadj : X.treeGraph.Adj γ' (geo X γ' γ 1) := by
    have := adj_geo X (u := γ') (w := γ) (i := 0) hd
    rwa [geo_zero] at this
  obtain ⟨k, hkα, hkβ⟩ := exists_smul_edge_of_isMVtx X (isMVtx_baseA X) (adj_baseA_baseB X)
    hγ' hadj
  refine ⟨k, hkα, hkβ, ?_, ?_⟩
  · have := (isCritical_smul X k⁻¹ γ γ').mpr hc
    rwa [← hkα, inv_smul_smul] at this
  · have := geo_smul X k⁻¹ γ' γ 1
    rw [← hkα, inv_smul_smul, hkα, ← hkβ, inv_smul_smul] at this
    exact this

end General

section Base

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

theorem imM_self : imM hTM M = (puAmalgam hTM).ofA.range := by
  rw [imM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]

theorem ofA_mem_imM_iff {K : Subgroup G} (m : ↥M) :
    (puAmalgam hTM).ofA m ∈ imM hTM K ↔ (m : G) ∈ K := by
  rw [imM, Subgroup.mem_map_iff_mem (puAmalgam hTM).ofA_injective, Subgroup.mem_subgroupOf]

theorem card_imM {K : Subgroup G} (hK : K ≤ M) : Nat.card ↥(imM hTM K) = Nat.card ↥K := by
  rw [imM, Subgroup.card_map_of_injective (puAmalgam hTM).ofA_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem relIndex_imM {H K : Subgroup G} (hK : K ≤ M) :
    (imM hTM H).relIndex (imM hTM K) = H.relIndex K := by
  rw [imM, imM, Subgroup.relIndex_map_map_of_injective _ _ (puAmalgam hTM).ofA_injective,
    Subgroup.relIndex_subgroupOf hK]

theorem imM_sup {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM hTM (K ⊔ K') = imM hTM K ⊔ imM hTM K' := by
  rw [imM, imM, imM, ← Subgroup.map_sup, Subgroup.subgroupOf_sup hK hK']

@[expose] def pre (S : Subgroup (puAmalgam hTM).Universal) : Subgroup G :=
  (S.comap (puAmalgam hTM).ofA).map M.subtype

theorem pre_le (S : Subgroup (puAmalgam hTM).Universal) : pre hTM S ≤ M :=
  Subgroup.map_subtype_le _

theorem imM_pre {S : Subgroup (puAmalgam hTM).Universal} (hS : S ≤ imM hTM M) :
    imM hTM (pre hTM S) = S := by
  rw [imM, pre, PU.map_subtype_subgroupOf]
  rw [imM_self] at hS
  exact Subgroup.map_comap_eq_self hS

theorem mem_pre_iff {S : Subgroup (puAmalgam hTM).Universal} (m : ↥M) :
    (m : G) ∈ pre hTM S ↔ (puAmalgam hTM).ofA m ∈ S := by
  rw [pre]
  constructor
  · rintro ⟨m', hm', he⟩
    have : m' = m := Subtype.ext he
    rw [← this]
    exact hm'
  · intro hm
    exact ⟨m, hm, rfl⟩

theorem imM_pre_eq_inf (S : Subgroup (puAmalgam hTM).Universal) :
    imM hTM (pre hTM S) = S ⊓ (puAmalgam hTM).ofA.range := by
  rw [imM, pre, PU.map_subtype_subgroupOf, Subgroup.map_comap_eq, inf_comm]

theorem mem_pre_iff' {S : Subgroup (puAmalgam hTM).Universal} {x : G} :
    x ∈ pre hTM S ↔ ∃ m : ↥M, (puAmalgam hTM).ofA m ∈ S ∧ (m : G) = x := by
  rw [pre, Subgroup.mem_map]
  rfl

theorem relIndex_pre (S : Subgroup (puAmalgam hTM).Universal) {K : Subgroup G} (hK : K ≤ M) :
    (pre hTM S).relIndex K = S.relIndex (imM hTM K) := by
  have hKr : imM hTM K ≤ (puAmalgam hTM).ofA.range := by
    rw [← imM_self]
    exact imM_mono hTM hK
  rw [← relIndex_imM hTM hK, imM_pre_eq_inf, ← Subgroup.inf_relIndex_right,
    inf_assoc, inf_eq_right.2 hKr, Subgroup.inf_relIndex_right]

theorem imM_commutator {H K : Subgroup G} (hH : H ≤ M) (hK : K ≤ M) :
    imM hTM ⁅H, K⁆ = ⁅imM hTM H, imM hTM K⁆ := by
  have hH' : H = (H.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hH).symm
  have hK' : K = (K.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hK).symm
  rw [hH', hK', ← Subgroup.map_commutator, imM_map_subtype, imM_map_subtype, imM_map_subtype,
    Subgroup.map_commutator]

theorem pre_comm {S : Subgroup (puAmalgam hTM).Universal}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : ∀ x ∈ pre hTM S, ∀ y ∈ pre hTM S, x * y = y * x := by
  intro x hx y hy
  obtain ⟨x', hx', rfl⟩ := (mem_pre_iff' hTM).1 hx
  obtain ⟨y', hy', rfl⟩ := (mem_pre_iff' hTM).1 hy
  have := hS _ hx' _ hy'
  rw [← map_mul, ← map_mul] at this
  exact congrArg Subtype.val ((puAmalgam hTM).ofA_injective this)

theorem pre_sq {S : Subgroup (puAmalgam hTM).Universal} (hS : ∀ x ∈ S, x ^ 2 = 1) :
    ∀ x ∈ pre hTM S, x ^ 2 = 1 := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (mem_pre_iff' hTM).1 hx
  have := hS _ hx'
  rw [← map_pow] at this
  have h1 := (puAmalgam hTM).ofA_injective (this.trans (map_one _).symm)
  exact congrArg Subtype.val h1

theorem pre_le_centralizer {S : Subgroup (puAmalgam hTM).Universal} {R : Subgroup G}
    (hR : R ≤ M) (hS : S ≤ Subgroup.centralizer (imM hTM R : Set (puAmalgam hTM).Universal)) :
    pre hTM S ≤ Subgroup.centralizer (R : Set G) := by
  intro x hx
  obtain ⟨x', hx', rfl⟩ := (mem_pre_iff' hTM).1 hx
  refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
  have h1 := Subgroup.mem_centralizer_iff.mp (hS hx') ((puAmalgam hTM).ofA ⟨r, hR hr⟩)
    ((ofA_mem_imM_iff hTM _).2 hr)
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val ((puAmalgam hTM).ofA_injective h1)

end Base

end CFSG.Quasithin.MS93.S33
