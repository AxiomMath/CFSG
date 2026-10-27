module

public import CFSG.Quasithin.Recognition.St84.Gold26
public import CFSG.Quasithin.Recognition.St84.L2Facts
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise MatrixGroups commutatorElement

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem pCoreOf_isPGroup' {G : Type*} [Group G] (H : Subgroup G) :
    IsPGroup 2 (pCoreOf 2 H) :=
  (CFSG.pCore_isPGroup (G := H) (p := 2)).map H.subtype

theorem finite_of_le_stabilizer (h : Hyp30 Γ G) {α : V} {H : Subgroup G}
    (hH : H ≤ MulAction.stabilizer G α) : Finite H := by
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  exact Finite.of_injective
    (fun x : H => (⟨(x : G), hH x.2⟩ : MulAction.stabilizer G α))
    (fun a b hab => Subtype.ext (congrArg (fun z : MulAction.stabilizer G α => (z : G)) hab))

theorem subgroupOf_map_subtype_eq {N : Subgroup G} {A : Subgroup N} :
    (A.map N.subtype).subgroupOf N = A := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := Subtype.ext hyx
    simpa [this] using hy
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_of_mem N.subtype hx

theorem isSylowTwoOf_map_of_sylow {N : Subgroup G} [Finite N] (S : Sylow 2 N) :
    IsSylowTwoOf ((S : Subgroup N).map N.subtype) N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_subtype_le _)
    (S.isPGroup'.map N.subtype) ?_
  rw [Subgroup.relIndex, subgroupOf_map_subtype_eq]
  exact S.not_dvd_index

@[expose] def kernelOnNeighbors (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V]
    (α : V) : Subgroup G :=
  MulAction.stabilizer G α ⊓ CFSG.Quasithin.Fan86.fixSet G (Γ.neighborSet α)

theorem mem_kernelOnNeighbors {α : V} {g : G} :
    g ∈ kernelOnNeighbors Γ G α ↔
      g ∈ MulAction.stabilizer G α ∧ ∀ a : V, Γ.Adj α a → g • a = a := by
  rw [kernelOnNeighbors, Subgroup.mem_inf, CFSG.Quasithin.Fan86.mem_fixSet]
  constructor
  · rintro ⟨hα, hfix⟩
    refine ⟨hα, fun a ha => ?_⟩
    exact hfix a (by simpa [SimpleGraph.mem_neighborSet] using ha)
  · rintro ⟨hα, hfix⟩
    refine ⟨hα, fun a ha => ?_⟩
    exact hfix a (by simpa [SimpleGraph.mem_neighborSet] using ha)

theorem kernelOnNeighbors_le (α : V) : kernelOnNeighbors Γ G α ≤ MulAction.stabilizer G α := by
  change MulAction.stabilizer G α ⊓
    CFSG.Quasithin.Fan86.fixSet G (Γ.neighborSet α) ≤ MulAction.stabilizer G α
  exact inf_le_left

theorem kernelOnNeighbors_normal (h : Hyp30 Γ G) (α : V) :
    ((kernelOnNeighbors Γ G α).subgroupOf (MulAction.stabilizer G α)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (kernelOnNeighbors_le α)]
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub g (kernelOnNeighbors Γ G α) = kernelOnNeighbors Γ G α
  have hgα : g • α = α := MulAction.mem_stabilizer_iff.mp hg
  have hset : g • (Γ.neighborSet α) = Γ.neighborSet α := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : Γ.Adj α b := by simpa [hgα] using hb
      simpa [hgα] using (h.adj_smul g α b).2 hb'
    · intro ha
      refine ⟨g⁻¹ • a, ?_, by simp⟩
      have ha' : Γ.Adj α (g⁻¹ • a) := by
        have h1 := (h.adj_smul g α (g⁻¹ • a)).1 ?_
        · simpa using h1
        · simpa [hgα] using ha
      exact ha'
  rw [kernelOnNeighbors, conjSub_inf, conjSub_eq_of_mem hg, conjSub_fixSet, hset]

theorem inf_kernelOnNeighbors_eq_pCoreOf (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) :
    N ⊓ kernelOnNeighbors Γ G α = pCoreOf 2 (MulAction.stabilizer G α) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxC : ∀ a : V, Γ.Adj α a → x • a = a := (mem_kernelOnNeighbors.mp hx.2).2
    exact hN.N_fixes_neighbors_mem_Q h.adj_smul (h.finite_stab α) (h.valency α).2
      (h.valency α).1 (x := ⟨x, hx.1⟩) hxC
  · intro x hx
    rw [Subgroup.mem_inf]
    refine ⟨hN.oTwo_le hx, ?_⟩
    rw [mem_kernelOnNeighbors]
    refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 (MulAction.stabilizer G α) hx, ?_⟩
    intro a ha
    exact hN.Q_fixes_neighbors h.adj_smul (h.finite_stab α) (h.valency α).2
      (h.valency α).1 a ha x hx

@[expose] noncomputable def localSubgroup (h : Hyp30 Γ G) (v : V) : Subgroup G :=
  Classical.choose (h.locL2 v)

theorem localSubgroup_spec (h : Hyp30 Γ G) (v : V) :
    IsLocL2 Γ G v (nOf Γ v) (localSubgroup h v) :=
  Classical.choose_spec (h.locL2 v)

@[expose] noncomputable def edgeLocal (h : Hyp30 Γ G) (α β : V) : Subgroup G :=
  localSubgroup h α ⊓ MulAction.stabilizer G β

@[expose] noncomputable def edgeSylow (h : Hyp30 Γ G) (α β : V) : Subgroup G :=
  pCoreOf 2 (edgeLocal h α β)

@[expose] noncomputable def vertexSylowMap (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) (β : V) : Subgroup G :=
  ((hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β :
    Sylow 2 N) : Subgroup N).map N.subtype

theorem vertexSylowMap_le {h : Hyp30 Γ G} {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) (β : V) :
    vertexSylowMap h hN β ≤ N := Subgroup.map_subtype_le _

theorem pCoreOf_le_vertexSylowMap (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) (β : V) :
    pCoreOf 2 (MulAction.stabilizer G α) ≤ vertexSylowMap h hN β := by
  classical
  let S' : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
  have hQN : (pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf N ≤ (S' : Subgroup N) :=
    hN.pCoreOf_subgroupOf_le_sylow S'
  intro x hx
  have hxN : x ∈ N := hN.oTwo_le hx
  have hxQN : (⟨x, hxN⟩ : N) ∈ (pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf N := by
    simpa [Subgroup.mem_subgroupOf] using hx
  exact Subgroup.mem_map_of_mem N.subtype (hQN hxQN)

theorem relIndex_pCoreOf_vertexSylowMap (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) (β : V) :
    (pCoreOf 2 (MulAction.stabilizer G α)).relIndex (vertexSylowMap h hN β) =
      2 ^ nOf Γ α := by
  classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite ↥N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  let S' : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
  let L := PSL(2, GaloisField 2 (nOf Γ α))
  let f : (S' : Subgroup N) →* L := hN.phi.comp (S' : Subgroup N).subtype
  have hQN : (pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf N ≤ (S' : Subgroup N) :=
    hN.pCoreOf_subgroupOf_le_sylow S'
  have hrel : (pCoreOf 2 (MulAction.stabilizer G α)).relIndex (vertexSylowMap h hN β) =
      ((pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf N).relIndex (S' : Subgroup N) := by
    have h := Subgroup.relIndex_map_map_of_injective (f := N.subtype)
      ((pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf N) (S' : Subgroup N)
      N.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hN.oTwo_le] at h
    exact h
  have hker : f.ker = ((pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf N).subgroupOf
      (S' : Subgroup N) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hN.phi_ker x
  have hrange : f.range = ((S' : Subgroup N).map hN.phi) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map_of_mem hN.phi x.2
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcardRange : Nat.card f.range = 2 ^ nOf Γ α := by
    rw [hrange]
    exact psl2_sylow_two_card (h.valency α).1 (S'.mapSurjective hN.phi_surjective)
  rw [hrel, Subgroup.relIndex]
  rw [← hker, Subgroup.index_ker]
  exact hcardRange


theorem vertexSylowMap_fixes {h : Hyp30 Γ G} {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    vertexSylowMap h hN β ≤ MulAction.stabilizer G β := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have hy'' : y ∈ (hN.pointSylow h.adj_smul (h.finite_stab α) (h.valency α).2
      (h.valency α).1 β).comap hN.phi := by
    change y ∈ ↑(hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2
      (h.valency α).1 β) at hy
    exact hy
  have hy' : y ∈ hN.pointSubgroup β := by
    rw [hN.pointSubgroup_eq_comap_pointBorel h.adj_smul (h.finite_stab α)
      (h.valency α).2 (h.valency α).1 hαβ]
    exact Subgroup.comap_mono
      (hN.pointSylow_spec h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 hαβ).1 hy''
  exact Subgroup.mem_subgroupOf.mp (show y ∈ (N ⊓ MulAction.stabilizer G β).subgroupOf N from hy') |>.2

theorem isSylowTwoOf_vertexSylowMap_edge {h : Hyp30 Γ G} {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    IsSylowTwoOf (vertexSylowMap h hN β) (N ⊓ MulAction.stabilizer G β) := by classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  classical
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  have hS : IsSylowTwoOf (vertexSylowMap h hN β) N :=
    isSylowTwoOf_map_of_sylow
      (hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β)
  exact F7.isSylowTwoOf_mono_right hS
    (le_inf (vertexSylowMap_le hN β) (vertexSylowMap_fixes hN hαβ)) inf_le_left

theorem edgeLocal_le_normalizer_vertexSylow (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    N ⊓ MulAction.stabilizer G β ≤
      Subgroup.normalizer (vertexSylowMap h hN β : Set G) := by
  have hEq := hN.inf_stabilizer_eq_inf_normalizer_pointSylowN h.adj_smul
    (h.finite_stab α) (h.valency α).2 (h.valency α).1 hαβ
  change N ⊓ MulAction.stabilizer G β ≤
    Subgroup.normalizer
      (((((hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2
        (h.valency α).1 β : Sylow 2 N) : Subgroup N).map N.subtype) : Subgroup G) : Set G)
  rw [hEq]
  exact inf_le_right

theorem edgeSylow_eq_vertexSylowMap (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    pCoreOf 2 (N ⊓ MulAction.stabilizer G β) = vertexSylowMap h hN β := by classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  classical
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  have hSylow := isSylowTwoOf_vertexSylowMap_edge (h := h) hN hαβ
  haveI : Finite ↥(N ⊓ MulAction.stabilizer G β) :=
    finite_of_le_stabilizer (h := h) (α := α) (H := N ⊓ MulAction.stabilizer G β)
      (inf_le_left.trans hN.le)
  have hnorm := edgeLocal_le_normalizer_vertexSylow h hN hαβ
  have hp : IsPGroup 2 (vertexSylowMap h hN β) := hSylow.2.1
  refine le_antisymm (pCoreOf_le_of_isSylowTwoOf hSylow) ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hSylow.1
    (Subgroup.normal_subgroupOf_of_le_normalizer hnorm) hp

theorem isSylowTwoOf_vertexSylowMap (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    IsSylowTwoOf (vertexSylowMap h hN β) N := by
  classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  exact isSylowTwoOf_map_of_sylow
    (hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β)

theorem edgeSylow_fixes_unique (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    ∃! a : V, Γ.Adj α a ∧ ∀ x : G, x ∈ vertexSylowMap h hN β → x • a = a := by
  classical
  let S0 : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
  obtain ⟨a0, ha0, huniq⟩ :=
    hN.sylow_fixes_unique h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 S0
  have hβ : Γ.Adj α β ∧ ∀ x : G,
      x ∈ vertexSylowMap h hN β → x • β = β :=
    ⟨hαβ, fun x hx => vertexSylowMap_fixes hN hαβ hx⟩
  refine ⟨a0, ⟨ha0.1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact ha0.2 y hy
  · intro b hb
    have hbS : ∀ y : N, y ∈ (S0 : Subgroup N) → (y : G) • b = b := by
      intro y hy
      exact hb.2 (y : G) (Subgroup.mem_map_of_mem N.subtype hy)
    exact (huniq b ⟨hb.1, hbS⟩).trans (huniq a0 ⟨ha0.1, ha0.2⟩).symm

theorem edgeSylow_fixes_unique_of_not_pcore (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {x : G} (hxS : x ∈ vertexSylowMap h hN β)
    (hxQ : x ∉ pCoreOf 2 (MulAction.stabilizer G α)) :
    ∃! a : V, Γ.Adj α a ∧ x • a = a := by
  classical
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hxS
  exact hN.fixes_unique_of_mem_sylow_not_pcore h.adj_smul (h.finite_stab α)
    (h.valency α).2 (h.valency α).1
    (hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β) hy hxQ


@[expose] def neighborActionOf (h : Hyp30 Γ G) {α : V} (S : Subgroup G)
    (hS : S ≤ MulAction.stabilizer G α) : SubMulAction S V where
  carrier := Γ.neighborSet α
  smul_mem' := by
    intro s a ha
    rw [SimpleGraph.mem_neighborSet] at ha ⊢
    have hs : (s : G) • α = α := MulAction.mem_stabilizer_iff.mp (hS s.2)
    have h1 : Γ.Adj ((s : G) • α) ((s : G) • a) := (h.adj_smul (s : G) α a).2 ha
    simpa [MulAction.subgroup_smul_def, hs] using h1

theorem stabilizer_vertexSylow_neighbor (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {a : V} (ha : Γ.Adj α a) (haβ : a ≠ β) :
    let Sg := vertexSylowMap h hN β
    let hSg : Sg ≤ MulAction.stabilizer G α := (vertexSylowMap_le hN β).trans hN.le
    let Δ := neighborActionOf h Sg hSg
    let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
    MulAction.stabilizer Sg aΔ = (pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf Sg := by
  classical
  dsimp only
  let Sg := vertexSylowMap h hN β
  let hSg : Sg ≤ MulAction.stabilizer G α := (vertexSylowMap_le hN β).trans hN.le
  let Δ := neighborActionOf h Sg hSg
  let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
  ext s
  constructor
  · intro hs
    rw [Subgroup.mem_subgroupOf]
    by_contra hsQ
    have hsa : (s : G) • a = a := by
      have hval := congrArg (fun z : Δ => (z : V)) hs
      rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at hval
      simpa [aΔ] using hval
    have hsS : (s : G) ∈ Sg := s.2
    obtain ⟨z, hz, huniq⟩ :=
      edgeSylow_fixes_unique_of_not_pcore h hN hαβ (x := (s : G)) hsS hsQ
    have hβfix : (s : G) • β = β := vertexSylowMap_fixes hN hαβ hsS
    have hza : a = z := huniq a ⟨ha, hsa⟩
    have hzβ : β = z := huniq β ⟨hαβ, hβfix⟩
    exact haβ (hza.trans hzβ.symm)
  · intro hs
    apply Subtype.ext
    have hsQ : (s : G) ∈ pCoreOf 2 (MulAction.stabilizer G α) :=
      Subgroup.mem_subgroupOf.mp hs
    have hfix : (s : G) • a = a :=
      hN.Q_fixes_neighbors h.adj_smul (h.finite_stab α) (h.valency α).2
        (h.valency α).1 a ha (s : G) hsQ
    rw [SubMulAction.val_smul, MulAction.subgroup_smul_def]
    exact hfix


theorem ncard_neighborSet_diff (h : Hyp30 Γ G) {α β : V} (hαβ : Γ.Adj α β) :
    (Γ.neighborSet α \ {β}).ncard = 2 ^ nOf Γ α := by
  have hfin : (Γ.neighborSet α).Finite := h.finite_neighborSet α
  have hβ : β ∈ Γ.neighborSet α := by
    rw [SimpleGraph.mem_neighborSet]
    exact hαβ
  haveI : Finite (Γ.neighborSet α) := hfin
  haveI : Fintype (Γ.neighborSet α) := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // (a : V) = β} := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // (a : V) ≠ β} := Fintype.ofFinite _
  have hone : Fintype.card {a : Γ.neighborSet α // (a : V) = β} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨β, hβ⟩, rfl⟩, ?_⟩
    rintro ⟨⟨x, hx⟩, hxβ⟩
    exact Subtype.ext (Subtype.ext hxβ)
  have hcard' : Nat.card {a : Γ.neighborSet α // (a : V) ≠ β} = 2 ^ nOf Γ α := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun a : Γ.neighborSet α => (a : V) = β)]
    have hcardn : Fintype.card (Γ.neighborSet α) = 2 ^ nOf Γ α + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact (h.valency α).2
    rw [hone, hcardn, Nat.add_sub_cancel]
  let e : {a : Γ.neighborSet α // (a : V) ≠ β} ≃
      ↥((Γ.neighborSet α) \ ({β} : Set V)) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, by simpa using x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, by simpa using y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have heq : Nat.card {a : Γ.neighborSet α // (a : V) ≠ β} =
      Nat.card ↥((Γ.neighborSet α) \ ({β} : Set V)) := Nat.card_congr e
  rw [← Nat.card_coe_set_eq, ← heq]
  exact hcard'


theorem orbit_vertexSylow_neighbor_ncard (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {a : V} (ha : Γ.Adj α a) (haβ : a ≠ β) :
    let Sg := vertexSylowMap h hN β
    let hSg : Sg ≤ MulAction.stabilizer G α := (vertexSylowMap_le hN β).trans hN.le
    let Δ := neighborActionOf h Sg hSg
    let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
    (MulAction.orbit Sg aΔ).ncard = 2 ^ nOf Γ α := by
  dsimp only
  let Sg := vertexSylowMap h hN β
  let hSg : Sg ≤ MulAction.stabilizer G α := (vertexSylowMap_le hN β).trans hN.le
  let Δ := neighborActionOf h Sg hSg
  let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
  have hstab := stabilizer_vertexSylow_neighbor h hN hαβ ha haβ
  dsimp only at hstab
  calc
    (MulAction.orbit Sg aΔ).ncard = (MulAction.stabilizer Sg aΔ).index :=
      (MulAction.index_stabilizer Sg aΔ).symm
    _ = ((pCoreOf 2 (MulAction.stabilizer G α)).subgroupOf Sg).index := by rw [hstab]
    _ = (pCoreOf 2 (MulAction.stabilizer G α)).relIndex Sg := rfl
    _ = 2 ^ nOf Γ α := relIndex_pCoreOf_vertexSylowMap h hN β

theorem orbit_vertexSylow_neighbor_image_eq (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {a : V} (ha : Γ.Adj α a) (haβ : a ≠ β) :
    let Sg := vertexSylowMap h hN β
    let hSg : Sg ≤ MulAction.stabilizer G α := (vertexSylowMap_le hN β).trans hN.le
    let Δ := neighborActionOf h Sg hSg
    let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
    (Subtype.val '' (MulAction.orbit Sg aΔ)) = (Γ.neighborSet α \ {β}) := by
  dsimp only
  let Sg := vertexSylowMap h hN β
  let hSg : Sg ≤ MulAction.stabilizer G α := (vertexSylowMap_le hN β).trans hN.le
  let Δ := neighborActionOf h Sg hSg
  let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
  have hSgβ : Sg ≤ MulAction.stabilizer G β := vertexSylowMap_fixes hN hαβ
  have hsubset : (Subtype.val '' (MulAction.orbit Sg aΔ)) ⊆
      (Γ.neighborSet α \ {β}) := by
    rintro v ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rintro hvβ
    obtain ⟨s, hs⟩ := hx
    have hval : (s : G) • a = (x : V) := by
      have := congrArg (fun z : Δ => (z : V)) hs
      rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at this
      simpa [aΔ] using this
    have haeq : a = β := by
      have h1 : (s⁻¹ : G) • ((s : G) • a) = (s⁻¹ : G) • β := by rw [hval, hvβ]
      rw [← mul_smul] at h1
      simpa using h1.trans (MulAction.mem_stabilizer_iff.mp (hSgβ (s⁻¹).2))
    exact haβ haeq
  refine Set.eq_of_subset_of_ncard_le hsubset ?_
    ((h.finite_neighborSet α).sdiff (t := ({β} : Set V)))
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,
    orbit_vertexSylow_neighbor_ncard h hN hαβ ha haβ,
    ncard_neighborSet_diff h hαβ]

theorem edgeSylow_transitive (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {a b : V} (ha : Γ.Adj α a) (hb : Γ.Adj α b) (haβ : a ≠ β) (hbβ : b ≠ β) :
    ∃ s ∈ vertexSylowMap h hN β, s • a = b := by
  classical
  let Sg := vertexSylowMap h hN β
  let hSg : Sg ≤ MulAction.stabilizer G α := (vertexSylowMap_le hN β).trans hN.le
  let Δ := neighborActionOf h Sg hSg
  let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
  have heq := orbit_vertexSylow_neighbor_image_eq h hN hαβ ha haβ
  dsimp only at heq
  have hbneighbor : b ∈ Γ.neighborSet α := by
    rw [SimpleGraph.mem_neighborSet]
    exact hb
  have hbimg : b ∈ (Subtype.val '' (MulAction.orbit Sg aΔ)) := by
    rw [heq]
    exact ⟨hbneighbor, hbβ⟩
  obtain ⟨x, hx, hxb⟩ := hbimg
  obtain ⟨s, hs⟩ := hx
  refine ⟨s, s.2, ?_⟩
  have hval : (s : G) • a = (x : V) := by
    have := congrArg (fun z : Δ => (z : V)) hs
    rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at this
    simpa [aΔ] using this
  rw [hval, hxb]

theorem edgeLocal_normal (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} :
    ((N ⊓ MulAction.stabilizer G β).subgroupOf
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)).Normal := by
  have hBle : N ⊓ MulAction.stabilizer G β ≤
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
    le_inf (inf_le_left.trans hN.le) inf_le_right
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hBle).mpr ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change conjSub g (N ⊓ MulAction.stabilizer G β) = N ⊓ MulAction.stabilizer G β
  rw [conjSub_inf]
  have hgN : g ∈ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN.le).mp hN.normal hg.1
  have hNconj : conjSub g N = N := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hgN
  have hGconj : conjSub g (MulAction.stabilizer G β) = MulAction.stabilizer G β :=
    conjSub_eq_of_mem hg.2
  rw [hNconj, hGconj]

theorem edgeLocal_normal_swap (h : Hyp30 Γ G) {α β : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G β (nOf Γ β) N) :
    ((N ⊓ MulAction.stabilizer G α).subgroupOf
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)).Normal := by
  have h' := edgeLocal_normal h hN (α := β) (β := α)
  rw [show MulAction.stabilizer G β ⊓ MulAction.stabilizer G α =
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β from
      inf_comm (MulAction.stabilizer G β) (MulAction.stabilizer G α)] at h'
  exact h'

theorem edgeSylow_normal (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} :
    ((pCoreOf 2 (N ⊓ MulAction.stabilizer G β)).subgroupOf
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)).Normal := by
  have hB := edgeLocal_normal h hN (β := β)
  have hBle : N ⊓ MulAction.stabilizer G β ≤
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
    le_inf (inf_le_left.trans hN.le) inf_le_right
  have hnorm : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ≤
      Subgroup.normalizer ((N ⊓ MulAction.stabilizer G β) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBle).mp hB
  exact Subgroup.normal_subgroupOf_of_le_normalizer
    (hnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2
      (N ⊓ MulAction.stabilizer G β)))

theorem le_edgeSylow_of_isPGroup (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPB : P ≤ N ⊓ MulAction.stabilizer G β) :
    P ≤ pCoreOf 2 (N ⊓ MulAction.stabilizer G β) := by
  classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  let B := N ⊓ MulAction.stabilizer G β
  haveI : Finite ↥B := finite_of_le_stabilizer (h := h) (α := α) (H := N ⊓ MulAction.stabilizer G β)
      (inf_le_left.trans hN.le)
  have hSylow : IsSylowTwoOf (vertexSylowMap h hN β) B :=
    isSylowTwoOf_vertexSylowMap_edge (h := h) hN hαβ
  have hnorm : B ≤ Subgroup.normalizer (vertexSylowMap h hN β : Set G) :=
    edgeLocal_le_normalizer_vertexSylow h hN hαβ
  have hSnormal : ((vertexSylowMap h hN β).subgroupOf B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  obtain ⟨S, hS⟩ := F7.isSylowTwoOf_exists_sylow hSylow
  have hSnormal' : S.Normal := hS ▸ hSnormal
  haveI : S.Normal := hSnormal'
  have hPB' : IsPGroup 2 (P.subgroupOf B) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPB).symm
  obtain ⟨Q, hQ⟩ := hPB'.exists_le_sylow
  have hQS : Q = S := by
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (M := B) S Q
    rw [← hx, Sylow.smul_eq_of_normal]
  have heq := edgeSylow_eq_vertexSylowMap (h := h) hN hαβ
  rw [heq]
  intro x hx
  have hx' : (⟨x, hPB hx⟩ : B) ∈ P.subgroupOf B := by
    simpa [Subgroup.mem_subgroupOf] using hx
  have hxS : (⟨x, hPB hx⟩ : B) ∈ (S : Subgroup B) := by
    rw [← hQS]
    exact hQ hx'
  rw [hS] at hxS
  simpa [Subgroup.mem_subgroupOf] using hxS

theorem edgeSylow_normal_swap (h : Hyp30 Γ G) {α β : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G β (nOf Γ β) N) :
    ((pCoreOf 2 (N ⊓ MulAction.stabilizer G α)).subgroupOf
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)).Normal := by
  have h' := edgeSylow_normal h hN (α := β) (β := α)
  rw [show MulAction.stabilizer G β ⊓ MulAction.stabilizer G α =
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β from
      inf_comm (MulAction.stabilizer G β) (MulAction.stabilizer G α)] at h'
  exact h' 

theorem isPGroup_sup_edgeSylow (h : Hyp30 Γ G) {α β : V} {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ)
    (hαβ : Γ.Adj α β) :
    IsPGroup 2 ↥((pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) : Subgroup G) ⊔
      (pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) : Subgroup G)) := by
  classical
  let Gαβ := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let S := pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)
  let T := pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α)
  have hSle : S ≤ Gαβ :=
    le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans
      (inf_le_left.trans hNα.le))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans inf_le_right)
  have hTle : T ≤ Gαβ :=
    le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_right)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans (inf_le_left.trans hNβ.le))
  have hTn : (T.subgroupOf Gαβ).Normal := edgeSylow_normal_swap h hNβ
  have hGnormT : Gαβ ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTle).mp hTn
  exact IsPGroup.to_sup_of_normal_right'
    (pCoreOf_isPGroup' (Nα ⊓ MulAction.stabilizer G β))
    (pCoreOf_isPGroup' (Nβ ⊓ MulAction.stabilizer G α))
    (hSle.trans hGnormT)

theorem sup_edgeSylow_normal (h : Hyp30 Γ G) {α β : V} {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ)
    (hαβ : Γ.Adj α β) :
    ((pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) ⊔
      pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α)).subgroupOf
        (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)).Normal := by
  classical
  let Gαβ := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let S := pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)
  let T := pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α)
  have hSle : S ≤ Gαβ :=
    le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans
      (inf_le_left.trans hNα.le))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans inf_le_right)
  have hTle : T ≤ Gαβ :=
    le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_right)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans (inf_le_left.trans hNβ.le))
  have hSn : (S.subgroupOf Gαβ).Normal := edgeSylow_normal h hNα (β := β)
  have hTn : (T.subgroupOf Gαβ).Normal := edgeSylow_normal_swap h hNβ
  have hGnormS : Gαβ ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mp hSn
  have hGnormT : Gαβ ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTle).mp hTn
  have hsup : (S ⊔ T).subgroupOf Gαβ =
      (S.subgroupOf Gαβ) ⊔ (T.subgroupOf Gαβ) := Subgroup.subgroupOf_sup hSle hTle
  rw [hsup]
  exact Subgroup.sup_normal _ _

theorem frattini_edgeLocal (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ⊔ N = MulAction.stabilizer G α := by
  classical
  obtain ⟨M, hM⟩ := h.locL2 β
  have hsup := stabilizer_eq_sup_left h hαβ hN.le hM.le hN.normal hM.normal hN.trans hM.trans
  have hle : MulAction.stabilizer G α ≤
      N ⊔ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
    calc MulAction.stabilizer G α
        = N ⊔ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ⊓ M) := hsup
      _ ≤ N ⊔ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) :=
          sup_le_sup_left (show MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ⊓ M ≤
            MulAction.stabilizer G α ⊓ MulAction.stabilizer G β from inf_le_left) N
  apply le_antisymm
  · exact sup_le inf_le_left hN.le
  · calc MulAction.stabilizer G α ≤
        N ⊔ (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := hle
      _ = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ⊔ N := sup_comm _ _


theorem exists_edgeTorus (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    ∃ K : Subgroup G, K ≤ N ∧ K ≤ MulAction.stabilizer G β ∧
      K ⊓ vertexSylowMap h hN β = ⊥ ∧
      K ⊔ vertexSylowMap h hN β = N ⊓ MulAction.stabilizer G β := by
  classical
  let B := N ⊓ MulAction.stabilizer G β
  let S := vertexSylowMap h hN β
  have hSB : S ≤ B := le_inf (vertexSylowMap_le hN β) (vertexSylowMap_fixes hN hαβ)
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite ↥B := finite_of_le_stabilizer (h := h) (α := α) (H := B)
    (inf_le_left.trans hN.le)
  let Ssub : Subgroup B := S.subgroupOf B
  have hSnormal : Ssub.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (edgeLocal_le_normalizer_vertexSylow h hN hαβ)
  haveI : Ssub.Normal := hSnormal
  have hSylow : IsSylowTwoOf S B := isSylowTwoOf_vertexSylowMap_edge hN hαβ
  have hSp : IsPGroup 2 Ssub :=
    hSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSB).symm
  have hSodd : ¬ 2 ∣ Ssub.index := hSylow.2.2
  have hcop : Nat.Coprime (Nat.card Ssub) Ssub.index := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSp
    rw [hk]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSodd |>.pow_left k
  obtain ⟨K', hK'⟩ := Subgroup.exists_right_complement'_of_coprime (N := Ssub) hcop
  let K : Subgroup G := K'.map B.subtype
  have hKleN : K ≤ N := by
    refine (Subgroup.map_subtype_le _).trans ?_
    exact inf_le_left
  have hKleβ : K ≤ MulAction.stabilizer G β := by
    refine (Subgroup.map_subtype_le _).trans ?_
    exact inf_le_right
  have hKinf : K ⊓ S = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨b₁, hb₁, hb₁x⟩ := Subgroup.mem_map.mp hx.1
    obtain ⟨b₂, hb₂, hb₂x⟩ := Subgroup.mem_map.mp hx.2
    have hbS : b₁ ∈ Ssub := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.mpr ⟨b₂, hb₂, hb₂x.trans hb₁x.symm⟩
    have hbot : b₁ ∈ (⊥ : Subgroup B) := by
      have hdisj : K' ⊓ Ssub = ⊥ := by
        rw [inf_comm]
        exact hK'.disjoint.eq_bot
      have : b₁ ∈ K' ⊓ Ssub := ⟨hb₁, hbS⟩
      rwa [hdisj] at this
    rw [Subgroup.mem_bot] at hbot
    rw [← hb₁x, hbot]
    rfl
  have hKsup : K ⊔ S = B := by
    have hmap := congrArg (Subgroup.map B.subtype) hK'.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top, B.range_subtype] at hmap
    rw [Subgroup.map_subgroupOf_eq_of_le hSB] at hmap
    rw [sup_comm]
    exact hmap
  exact ⟨K, hKleN, hKleβ, hKinf, hKsup⟩



@[expose] noncomputable def edgeTorus (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) : Subgroup G :=
  Classical.choose (exists_edgeTorus h hN hαβ)

theorem edgeTorus_spec (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    edgeTorus h hN hαβ ≤ N ∧
      edgeTorus h hN hαβ ≤ MulAction.stabilizer G β ∧
      edgeTorus h hN hαβ ⊓ vertexSylowMap h hN β = ⊥ ∧
      edgeTorus h hN hαβ ⊔ vertexSylowMap h hN β = N ⊓ MulAction.stabilizer G β :=
  Classical.choose_spec (exists_edgeTorus h hN hαβ)

theorem edgeTorus_le (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    edgeTorus h hN hαβ ≤ N := (edgeTorus_spec h hN hαβ).1

theorem edgeTorus_fixes (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    edgeTorus h hN hαβ ≤ MulAction.stabilizer G β := (edgeTorus_spec h hN hαβ).2.1

theorem edgeTorus_inf (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    edgeTorus h hN hαβ ⊓ vertexSylowMap h hN β = ⊥ := (edgeTorus_spec h hN hαβ).2.2.1

theorem edgeTorus_sup (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    edgeTorus h hN hαβ ⊔ vertexSylowMap h hN β =
      N ⊓ MulAction.stabilizer G β := (edgeTorus_spec h hN hαβ).2.2.2

theorem edgeTorus_cyclic (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    IsCyclic (edgeTorus h hN hαβ) ∧ Nat.card (edgeTorus h hN hαβ) = 2 ^ nOf Γ α - 1 := by
  classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite ↥N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  let S' : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
  let Sg : Subgroup G := vertexSylowMap h hN β
  let B : Subgroup G := N ⊓ MulAction.stabilizer G β
  let K : Subgroup G := edgeTorus h hN hαβ
  let KN : Subgroup N := K.subgroupOf N
  have hKle : K ≤ N := edgeTorus_le h hN hαβ
  have hSgle : Sg ≤ N := vertexSylowMap_le hN β
  have hKmap : KN.map N.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKle
  have hSmap : (S' : Subgroup N).map N.subtype = Sg := rfl
  have hSgsub : Sg.subgroupOf N = (S' : Subgroup N) := subgroupOf_map_subtype_eq
  have hnormN : (Subgroup.normalizer (S' : Subgroup N)).map N.subtype =
      N ⊓ Subgroup.normalizer (Sg : Set G) := by
    have h1 : (Subgroup.normalizer (Sg : Set G)).subgroupOf N =
        Subgroup.normalizer (S' : Subgroup N) := by
      rw [Subgroup.subgroupOf_normalizer_eq hSgle, hSgsub]
    rw [← h1, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hBnorm : B = (Subgroup.normalizer (S' : Subgroup N)).map N.subtype := by
    change N ⊓ MulAction.stabilizer G β =
      (Subgroup.normalizer (S' : Subgroup N)).map N.subtype
    rw [hnormN]
    exact hN.inf_stabilizer_eq_inf_normalizer_pointSylowN h.adj_smul
      (h.finite_stab α) (h.valency α).2 (h.valency α).1 hαβ
  have hKSinf : KN ⊓ (S' : Subgroup N) = ⊥ := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.map_inf _ _ _ N.subtype_injective, hKmap, hSmap,
      edgeTorus_inf h hN hαβ, Subgroup.map_bot]
  have hKSsup : KN ⊔ (S' : Subgroup N) = Subgroup.normalizer (S' : Subgroup N) := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.map_sup, hKmap, hSmap, edgeTorus_sup]
    change N ⊓ MulAction.stabilizer G β =
      (Subgroup.normalizer (S' : Subgroup N)).map N.subtype
    exact hBnorm
  have hcyc := hN.torus_cyclic h.adj_smul (h.finite_stab α) (h.valency α).2
    (h.valency α).1 S' KN hKSinf hKSsup
  have hcard : Nat.card K = Nat.card KN :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle)).symm
  refine ⟨?_, hcard.trans hcyc.2⟩
  change IsCyclic ↥K
  haveI : IsCyclic ↥KN := hcyc.1
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hKle)
    (Subgroup.subgroupOfEquivOfLe hKle).surjective



theorem edgeTorus_N_facts (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    let S' : Sylow 2 N :=
      hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
    let KN : Subgroup N := (edgeTorus h hN hαβ).subgroupOf N
    KN ⊓ (S' : Subgroup N) = ⊥ ∧
      KN ⊔ (S' : Subgroup N) = Subgroup.normalizer (S' : Subgroup N) ∧
      IsCyclic KN ∧ Nat.card KN = 2 ^ nOf Γ α - 1 := by
  classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite ↥N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  dsimp only
  let S' : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
  let Sg : Subgroup G := vertexSylowMap h hN β
  let B : Subgroup G := N ⊓ MulAction.stabilizer G β
  let K : Subgroup G := edgeTorus h hN hαβ
  let KN : Subgroup N := K.subgroupOf N
  have hKle : K ≤ N := edgeTorus_le h hN hαβ
  have hSgle : Sg ≤ N := vertexSylowMap_le hN β
  have hKmap : KN.map N.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKle
  have hSmap : (S' : Subgroup N).map N.subtype = Sg := rfl
  have hSgsub : Sg.subgroupOf N = (S' : Subgroup N) := subgroupOf_map_subtype_eq
  have hnormN : (Subgroup.normalizer (S' : Subgroup N)).map N.subtype =
      N ⊓ Subgroup.normalizer (Sg : Set G) := by
    have h1 : (Subgroup.normalizer (Sg : Set G)).subgroupOf N =
        Subgroup.normalizer (S' : Subgroup N) := by
      rw [Subgroup.subgroupOf_normalizer_eq hSgle, hSgsub]
    rw [← h1, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hBnorm : B = (Subgroup.normalizer (S' : Subgroup N)).map N.subtype := by
    change N ⊓ MulAction.stabilizer G β =
      (Subgroup.normalizer (S' : Subgroup N)).map N.subtype
    rw [hnormN]
    exact hN.inf_stabilizer_eq_inf_normalizer_pointSylowN h.adj_smul
      (h.finite_stab α) (h.valency α).2 (h.valency α).1 hαβ
  have hKSinf : KN ⊓ (S' : Subgroup N) = ⊥ := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.map_inf _ _ _ N.subtype_injective, hKmap, hSmap,
      edgeTorus_inf h hN hαβ, Subgroup.map_bot]
  have hKSsup : KN ⊔ (S' : Subgroup N) = Subgroup.normalizer (S' : Subgroup N) := by
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.map_sup, hKmap, hSmap, edgeTorus_sup]
    change N ⊓ MulAction.stabilizer G β =
      (Subgroup.normalizer (S' : Subgroup N)).map N.subtype
    exact hBnorm
  have hcyc := hN.torus_cyclic h.adj_smul (h.finite_stab α) (h.valency α).2
    (h.valency α).1 S' KN hKSinf hKSsup
  exact ⟨hKSinf, hKSsup, hcyc.1, hcyc.2⟩



theorem exists_edgeGamma (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    ∃ γ : V, Γ.Adj α γ ∧ γ ≠ β ∧
      edgeTorus h hN hαβ ≤ MulAction.stabilizer G γ := by
  classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite ↥N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  let K := edgeTorus h hN hαβ
  by_cases hn1 : nOf Γ α = 1
  · have hcardK : Nat.card K = 1 := by
      have hc := (edgeTorus_cyclic h hN hαβ).2
      rw [hn1] at hc
      simpa [K] using hc
    have hKbot : K = ⊥ := Subgroup.eq_bot_of_card_eq K hcardK
    obtain ⟨γ, hαγ, hγβ⟩ := h.exists_adj_ne α β
    refine ⟨γ, hαγ, hγβ, ?_⟩
    change K ≤ MulAction.stabilizer G γ
    rw [hKbot]
    exact bot_le
  · have hn2 : 2 ≤ nOf Γ α := by
      have := (h.valency α).1
      omega
    let S' : Sylow 2 N :=
      hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
    let KN : Subgroup N := K.subgroupOf N
    have hfacts := edgeTorus_N_facts h hN hαβ
    dsimp only at hfacts
    obtain ⟨hKSinf, hKSsup, hcyc, hcardKN⟩ := hfacts
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := KN)
    have hgne : g ≠ 1 := by
      intro hg1
      have hKNbot : KN = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hzbot : Subgroup.zpowers g = ⊥ := (Subgroup.zpowers_eq_bot).mpr hg1
        have hxgen : (⟨x, hx⟩ : KN) ∈ Subgroup.zpowers g := hg ⟨x, hx⟩
        rw [hzbot] at hxgen
        have hx1 : (⟨x, hx⟩ : KN) = 1 := Subgroup.mem_bot.mp hxgen
        have : x = 1 := congrArg (fun y : KN => (y : N)) hx1
        simpa using this
      have hcard1 : Nat.card KN = 1 := by rw [hKNbot, Subgroup.card_bot]
      rw [hcardKN] at hcard1
      have h2n : 4 ≤ 2 ^ nOf Γ α := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ nOf Γ α := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    have hfix := hN.torus_fixes_two h.adj_smul (h.finite_stab α) (h.valency α).2
      (h.valency α).1 S' KN hKSinf hKSsup g hgne
    let Fix : Set V := {a : V | Γ.Adj α a ∧ (((g : KN) : N) : G) • a = a}
    have hβFix : β ∈ Fix := by
      refine ⟨hαβ, ?_⟩
      have hgK : (((g : KN) : N) : G) ∈ K := Subgroup.mem_subgroupOf.mp g.2
      exact MulAction.mem_stabilizer_iff.mp (edgeTorus_fixes h hN hαβ hgK)
    have hFixcard : Fix.ncard = 2 := by simpa [Fix] using hfix
    have hlt : 1 < Fix.ncard := by rw [hFixcard]; norm_num
    obtain ⟨γ, hγFix, hγβ⟩ := Set.exists_ne_of_one_lt_ncard hlt β
    refine ⟨γ, hγFix.1, hγβ, ?_⟩
    intro k hk
    have hkmap : k ∈ KN.map N.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le (edgeTorus_le h hN hαβ)]
      exact hk
    obtain ⟨x, hxKN, hxk⟩ := Subgroup.mem_map.mp hkmap
    let xKN : KN := ⟨x, hxKN⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg xKN)
    have hxpow : ((xKN : KN) : N) = ((g ^ m : KN) : N) := by
      exact congrArg (fun y : KN => (y : N)) hm.symm
    have hgenmem : (((g : KN) : N) : G) ∈ MulAction.stabilizer G γ := hγFix.2
    have hpowmem : ((((g : KN) : N) : G) ^ m) ∈ MulAction.stabilizer G γ :=
      (MulAction.stabilizer G γ).zpow_mem hgenmem m
    have hpowfix : (((((g : KN) : N) : G) ^ m) • γ = γ) :=
      MulAction.mem_stabilizer_iff.mp hpowmem
    have hxG : ((x : N) : G) = ((((g : KN) : N) : G) ^ m) := by
      have := congrArg (fun y : N => (y : G)) hxpow
      simpa using this
    have hxfix : ((x : N) : G) • γ = γ := by
      rw [hxG]
      exact hpowfix
    rw [← hxk]
    exact hxfix


@[expose] noncomputable def edgeGamma (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) : V :=
  Classical.choose (exists_edgeGamma h hN hαβ)

theorem edgeGamma_spec (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β) :
    Γ.Adj α (edgeGamma h hN hαβ) ∧ edgeGamma h hN hαβ ≠ β ∧
      edgeTorus h hN hαβ ≤ MulAction.stabilizer G (edgeGamma h hN hαβ) :=
  Classical.choose_spec (exists_edgeGamma h hN hαβ)

theorem ncard_neighborSet_diff_two (h : Hyp30 Γ G) {α β γ : V}
    (hαβ : Γ.Adj α β) (hαγ : Γ.Adj α γ) (hβγ : β ≠ γ) :
    (Γ.neighborSet α \ {β, γ}).ncard = 2 ^ nOf Γ α - 1 := by
  classical
  have hfin : (Γ.neighborSet α).Finite := h.finite_neighborSet α
  have hβ : β ∈ Γ.neighborSet α := by rw [SimpleGraph.mem_neighborSet]; exact hαβ
  have hγ : γ ∈ Γ.neighborSet α := by rw [SimpleGraph.mem_neighborSet]; exact hαγ
  haveI : Finite (Γ.neighborSet α) := hfin
  haveI : Fintype (Γ.neighborSet α) := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // (a : V) = β} := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // ¬(a : V) = β} := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // (a : V) = γ} := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // ¬(a : V) = γ} := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // (a : V) = β ∨ (a : V) = γ} := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // ¬((a : V) = β ∨ (a : V) = γ)} := Fintype.ofFinite _
  haveI : Fintype {a : Γ.neighborSet α // (a : V) ≠ β ∧ (a : V) ≠ γ} := Fintype.ofFinite _
  have honeβ : Fintype.card {a : Γ.neighborSet α // (a : V) = β} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨β, hβ⟩, rfl⟩, ?_⟩
    rintro ⟨⟨x, hx⟩, hxβ⟩
    exact Subtype.ext (Subtype.ext hxβ)
  have honeγ : Fintype.card {a : Γ.neighborSet α // (a : V) = γ} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨γ, hγ⟩, rfl⟩, ?_⟩
    rintro ⟨⟨x, hx⟩, hxγ⟩
    exact Subtype.ext (Subtype.ext hxγ)
  have hor : Fintype.card {a : Γ.neighborSet α // (a : V) = β ∨ (a : V) = γ} = 2 := by
    have hne : (⟨β, hβ⟩ : Γ.neighborSet α) ≠ ⟨γ, hγ⟩ := by
      intro h
      exact hβγ (congrArg Subtype.val h)
    simpa [Subtype.ext_iff] using Fintype.card_subtype_eq_or_eq_of_ne (a := (⟨β, hβ⟩ : Γ.neighborSet α))
      (b := ⟨γ, hγ⟩) hne
  have hcard' : Nat.card {a : Γ.neighborSet α //
      ¬((a : V) = β ∨ (a : V) = γ)} = 2 ^ nOf Γ α - 1 := by
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (p := fun a : Γ.neighborSet α =>
        (a : V) = β ∨ (a : V) = γ)]
    have hcardn : Fintype.card (Γ.neighborSet α) = 2 ^ nOf Γ α + 1 := by
      rw [← Nat.card_eq_fintype_card]
      exact (h.valency α).2
    rw [hor, hcardn]
    have hpos : 2 ≤ 2 ^ nOf Γ α := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ nOf Γ α := Nat.pow_le_pow_right (by norm_num) (h.valency α).1
    omega
  let e : {a : Γ.neighborSet α // ¬((a : V) = β ∨ (a : V) = γ)} ≃
      ↥((Γ.neighborSet α) \ ({β, γ} : Set V)) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact not_or.mp x.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
        have hy : (y : V) ≠ β ∧ (y : V) ≠ γ := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using y.2.2
        exact not_or.mpr hy⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  have heq : Nat.card {a : Γ.neighborSet α // ¬((a : V) = β ∨ (a : V) = γ)} =
      Nat.card ↥((Γ.neighborSet α) \ ({β, γ} : Set V)) := Nat.card_congr e
  rw [← Nat.card_coe_set_eq, ← heq]
  exact hcard'



theorem stabilizer_edgeTorus_neighbor (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {δ : V} (hδ : Γ.Adj α δ) (hδβ : δ ≠ β) (hδγ : δ ≠ edgeGamma h hN hαβ) :
    let K := edgeTorus h hN hαβ
    let hK : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
    let Δ := neighborActionOf h K hK
    let δΔ : Δ := ⟨δ, by change δ ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact hδ⟩
    MulAction.stabilizer K δΔ = ⊥ := by
  classical
  haveI : Finite (MulAction.stabilizer G α) := h.finite_stab α
  haveI : Finite ↥N :=
    Finite.of_injective
      (fun x : N => (⟨(x : G), hN.le x.2⟩ : MulAction.stabilizer G α))
      (fun a b h => Subtype.ext
        (congrArg (fun z : MulAction.stabilizer G α => (z : G)) h))
  dsimp only
  let K := edgeTorus h hN hαβ
  let hK : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
  let Δ := neighborActionOf h K hK
  let δΔ : Δ := ⟨δ, by change δ ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact hδ⟩
  let S' : Sylow 2 N :=
    hN.pointSylowN h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1 β
  let KN : Subgroup N := K.subgroupOf N
  have hfacts := edgeTorus_N_facts h hN hαβ
  dsimp only at hfacts
  obtain ⟨hKSinf, hKSsup, hcyc, hcardKN⟩ := hfacts
  let γ := edgeGamma h hN hαβ
  have hγspec := edgeGamma_spec h hN hαβ
  have hβγ : β ≠ γ := fun hb => hγspec.2.1 hb.symm
  have hKβ : K ≤ MulAction.stabilizer G β := edgeTorus_fixes h hN hαβ
  have hKγ : K ≤ MulAction.stabilizer G γ := hγspec.2.2
  ext k
  constructor
  · intro hk
    rw [Subgroup.mem_bot]
    by_contra hk1
    have hkmap : ((k : K) : G) ∈ KN.map N.subtype := by
      rw [Subgroup.map_subgroupOf_eq_of_le (edgeTorus_le h hN hαβ)]
      exact k.2
    obtain ⟨x, hxKN, hxk⟩ := Subgroup.mem_map.mp hkmap
    let xKN : KN := ⟨x, hxKN⟩
    have hxne : xKN ≠ 1 := by
      intro hx1
      have hxG : (x : N) = 1 := by
        simpa [xKN] using congrArg (fun y : KN => (y : N)) hx1
      have hxG' : ((x : N) : G) = 1 := by
        simpa using congrArg (fun y : N => (y : G)) hxG
      apply hk1
      apply Subtype.ext
      rw [← hxk]
      exact hxG'
    have hfix := hN.torus_fixes_two h.adj_smul (h.finite_stab α) (h.valency α).2
      (h.valency α).1 S' KN hKSinf hKSsup xKN hxne
    let Fix : Set V := {a : V | Γ.Adj α a ∧ (((xKN : KN) : N) : G) • a = a}
    have hδfix : δ ∈ Fix := by
      refine ⟨hδ, ?_⟩
      have hkδ : ((k : K) : G) • δ = δ := by
        have hval := congrArg (fun z : Δ => (z : V)) hk
        rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at hval
        simpa [δΔ] using hval
      have hkx : (((xKN : KN) : N) : G) = ((k : K) : G) := by simpa [xKN] using hxk
      rw [hkx]
      exact hkδ
    have hβfix : β ∈ Fix := by
      refine ⟨hαβ, ?_⟩
      have hkx : (((xKN : KN) : N) : G) = ((k : K) : G) := by simpa [xKN] using hxk
      rw [hkx]
      exact MulAction.mem_stabilizer_iff.mp (hKβ k.2)
    have hγfix : γ ∈ Fix := by
      refine ⟨hγspec.1, ?_⟩
      have hkx : (((xKN : KN) : N) : G) = ((k : K) : G) := by simpa [xKN] using hxk
      rw [hkx]
      exact MulAction.mem_stabilizer_iff.mp (hKγ k.2)
    have hsub : ({β, γ, δ} : Set V) ⊆ Fix := by
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact hβfix
      · exact hγfix
      · exact hδfix
    have h3 : ({β, γ, δ} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hβγ, Ne.symm hδβ]),
        Set.ncard_insert_of_notMem (by simpa using hδγ.symm), Set.ncard_singleton]
    have hFixcard : Fix.ncard = 2 := by simpa [Fix] using hfix
    have hFixfin : Fix.Finite := (h.finite_neighborSet α).subset (by
      intro a ha
      exact ha.1)
    have hle := Set.ncard_le_ncard hsub hFixfin
    rw [h3, hFixcard] at hle
    omega
  · intro hk
    rw [Subgroup.mem_bot] at hk
    subst hk
    exact Subgroup.one_mem _



theorem orbit_edgeTorus_neighbor_ncard (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {δ : V} (hδ : Γ.Adj α δ) (hδβ : δ ≠ β) (hδγ : δ ≠ edgeGamma h hN hαβ) :
    let K := edgeTorus h hN hαβ
    let hK : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
    let Δ := neighborActionOf h K hK
    let δΔ : Δ := ⟨δ, by change δ ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact hδ⟩
    (MulAction.orbit K δΔ).ncard = 2 ^ nOf Γ α - 1 := by
  dsimp only
  let K := edgeTorus h hN hαβ
  let hK : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
  let Δ := neighborActionOf h K hK
  let δΔ : Δ := ⟨δ, by change δ ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact hδ⟩
  have hstab := stabilizer_edgeTorus_neighbor h hN hαβ hδ hδβ hδγ
  dsimp only at hstab
  calc
    (MulAction.orbit K δΔ).ncard = (MulAction.stabilizer K δΔ).index :=
      (MulAction.index_stabilizer K δΔ).symm
    _ = (⊥ : Subgroup K).index := by rw [hstab]
    _ = Nat.card K := Subgroup.index_bot
    _ = 2 ^ nOf Γ α - 1 := (edgeTorus_cyclic h hN hαβ).2

theorem orbit_edgeTorus_neighbor_image_eq (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {δ : V} (hδ : Γ.Adj α δ) (hδβ : δ ≠ β) (hδγ : δ ≠ edgeGamma h hN hαβ) :
    let K := edgeTorus h hN hαβ
    let hK : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
    let Δ := neighborActionOf h K hK
    let δΔ : Δ := ⟨δ, by change δ ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact hδ⟩
    (Subtype.val '' (MulAction.orbit K δΔ)) =
      (Γ.neighborSet α \ {β, edgeGamma h hN hαβ}) := by
  dsimp only
  let K := edgeTorus h hN hαβ
  let hK : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
  let Δ := neighborActionOf h K hK
  let δΔ : Δ := ⟨δ, by change δ ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact hδ⟩
  let γ := edgeGamma h hN hαβ
  have hγspec := edgeGamma_spec h hN hαβ
  have hKβ : K ≤ MulAction.stabilizer G β := edgeTorus_fixes h hN hαβ
  have hKγ : K ≤ MulAction.stabilizer G γ := hγspec.2.2
  have hsubset : (Subtype.val '' (MulAction.orbit K δΔ)) ⊆
      (Γ.neighborSet α \ {β, γ}) := by
    rintro v ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hvβ
      obtain ⟨s, hs⟩ := hx
      have hval : ((s : K) : G) • δ = (x : V) := by
        have := congrArg (fun z : Δ => (z : V)) hs
        rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at this
        simpa [δΔ] using this
      have hδeq : δ = β := by
        have h1 : ((s⁻¹ : K) : G) • (((s : K) : G) • δ) = ((s⁻¹ : K) : G) • β := by
          rw [hval, hvβ]
        rw [← mul_smul] at h1
        simpa using h1.trans (MulAction.mem_stabilizer_iff.mp (hKβ (s⁻¹).2))
      exact hδβ hδeq
    · intro hvγ
      obtain ⟨s, hs⟩ := hx
      have hval : ((s : K) : G) • δ = (x : V) := by
        have := congrArg (fun z : Δ => (z : V)) hs
        rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at this
        simpa [δΔ] using this
      have hδeq : δ = γ := by
        have h1 : ((s⁻¹ : K) : G) • (((s : K) : G) • δ) = ((s⁻¹ : K) : G) • γ := by
          rw [hval, hvγ]
        rw [← mul_smul] at h1
        simpa using h1.trans (MulAction.mem_stabilizer_iff.mp (hKγ (s⁻¹).2))
      exact hδγ hδeq
  refine Set.eq_of_subset_of_ncard_le hsubset ?_
    ((h.finite_neighborSet α).sdiff (t := ({β, γ} : Set V)))
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,
    orbit_edgeTorus_neighbor_ncard h hN hαβ hδ hδβ hδγ,
    ncard_neighborSet_diff_two h hαβ hγspec.1 (by
      intro hb
      exact hγspec.2.1 hb.symm)]

theorem edgeTorus_transitive (h : Hyp30 Γ G) {α : V} {N : Subgroup G}
    (hN : IsLocL2 Γ G α (nOf Γ α) N) {β : V} (hαβ : Γ.Adj α β)
    {a b : V} (ha : Γ.Adj α a) (hb : Γ.Adj α b)
    (haβ : a ≠ β) (haγ : a ≠ edgeGamma h hN hαβ)
    (hbβ : b ≠ β) (hbγ : b ≠ edgeGamma h hN hαβ) :
    ∃ k ∈ edgeTorus h hN hαβ, k • a = b := by
  classical
  let K := edgeTorus h hN hαβ
  let hK : K ≤ MulAction.stabilizer G α := (edgeTorus_le h hN hαβ).trans hN.le
  let Δ := neighborActionOf h K hK
  let aΔ : Δ := ⟨a, by change a ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact ha⟩
  have heq := orbit_edgeTorus_neighbor_image_eq h hN hαβ ha haβ haγ
  dsimp only at heq
  have hbneighbor : b ∈ Γ.neighborSet α := by
    rw [SimpleGraph.mem_neighborSet]
    exact hb
  have hbimg : b ∈ (Subtype.val '' (MulAction.orbit K aΔ)) := by
    rw [heq]
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hbneighbor, hbβ, hbγ⟩
  obtain ⟨x, hx, hxb⟩ := hbimg
  obtain ⟨s, hs⟩ := hx
  refine ⟨s, s.2, ?_⟩
  have hval : ((s : K) : G) • a = (x : V) := by
    have := congrArg (fun z : Δ => (z : V)) hs
    rw [SubMulAction.val_smul, MulAction.subgroup_smul_def] at this
    simpa [aΔ] using this
  rw [hval, hxb]



theorem commutator_mem_kernel (h : Hyp30 Γ G) {α β : V} {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ)
    (hαβ : Γ.Adj α β) {t k : G}
    (ht : t ∈ pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β))
    (hk : k ∈ edgeTorus h hNα hαβ)
    (hγt : t • edgeGamma h hNα hαβ = edgeGamma h hNα hαβ) :
    ⁅t, k⁆ ∈ kernelOnNeighbors Γ G α := by
  classical
  have hPnorm : ((pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)).subgroupOf
        (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)).Normal :=
    (by
      have h := sup_edgeSylow_normal (h := h) (α := α) (β := β) (Nα := Nα) (Nβ := Nβ)
        hNα hNβ hαβ
      rw [sup_comm] at h
      exact h)
  have hPle : pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) ≤
        MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    refine sup_le ?_ ?_
    · exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2
        (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_right)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2
          (Nβ ⊓ MulAction.stabilizer G α)).trans (inf_le_left.trans hNβ.le))
    · exact le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2
        (Nα ⊓ MulAction.stabilizer G β)).trans (inf_le_left.trans hNα.le))
        ((CFSG.LieType.BorelTits.pCoreOf_le 2
          (Nα ⊓ MulAction.stabilizer G β)).trans inf_le_right)
  have hBnorm : ((Nα ⊓ MulAction.stabilizer G β).subgroupOf
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)).Normal :=
    edgeLocal_normal h hNα (β := β)
  have hBle : Nα ⊓ MulAction.stabilizer G β ≤
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
    le_inf (inf_le_left.trans hNα.le) inf_le_right
  have hKG : edgeTorus h hNα hαβ ≤
      MulAction.stabilizer G α ⊓ MulAction.stabilizer G β :=
    le_inf ((edgeTorus_le h hNα hαβ).trans hNα.le) (edgeTorus_fixes h hNα hαβ)
  have htG : t ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := hPle ht
  have hkG : k ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := hKG hk
  have hcommP : ⁅t, k⁆ ∈ pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) := by
    have htinv : t⁻¹ ∈ pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
        pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) :=
      (pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
        pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)).inv_mem ht
    have hconj : k * t⁻¹ * k⁻¹ ∈
        pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
          pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) := by
      have hsub := hPnorm.conj_mem ⟨t⁻¹, hPle htinv⟩
        (by simpa [Subgroup.mem_subgroupOf] using htinv) ⟨k, hkG⟩
      have := Subgroup.mem_subgroupOf.mp hsub
      simpa [mul_assoc] using this
    have hform : ⁅t, k⁆ = t * (k * t⁻¹ * k⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [hform]
    exact Subgroup.mul_mem _ ht hconj
  have hcommB : ⁅t, k⁆ ∈ Nα ⊓ MulAction.stabilizer G β := by
    have hkB : k ∈ Nα ⊓ MulAction.stabilizer G β :=
      ⟨edgeTorus_le h hNα hαβ hk, edgeTorus_fixes h hNα hαβ hk⟩
    have hconj : t * k * t⁻¹ ∈ Nα ⊓ MulAction.stabilizer G β := by
      have hsub := hBnorm.conj_mem ⟨k, hBle hkB⟩
        (by simpa [Subgroup.mem_subgroupOf] using hkB) ⟨t, htG⟩
      have := Subgroup.mem_subgroupOf.mp hsub
      simpa [mul_assoc] using this
    have hform : ⁅t, k⁆ = (t * k * t⁻¹) * k⁻¹ := by
      simp [commutatorElement_def, mul_assoc]
    rw [hform]
    exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hkB)
  have hcommS : ⁅t, k⁆ ∈ pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) := by
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) ⊔
        pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α)) :=
      isPGroup_sup_edgeSylow h hNα hNβ hαβ
    have hP2' : IsPGroup 2 ↥(pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
        pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)) := by
      rw [sup_comm]
      exact hP2
    have hPinf : IsPGroup 2 ↥((pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
        pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)) ⊓
          (Nα ⊓ MulAction.stabilizer G β)) :=
      hP2'.to_le inf_le_left
    exact le_edgeSylow_of_isPGroup h hNα hαβ hPinf inf_le_right ⟨hcommP, hcommB⟩
  have hcommQ : ⁅t, k⁆ ∈ pCoreOf 2 (MulAction.stabilizer G α) := by
    by_contra hQ
    have hcommS' : ⁅t, k⁆ ∈ vertexSylowMap h hNα β := by
      rw [← edgeSylow_eq_vertexSylowMap h hNα hαβ]
      exact hcommS
    have hβfix : ⁅t, k⁆ • β = β :=
      MulAction.mem_stabilizer_iff.mp (vertexSylowMap_fixes hNα hαβ hcommS')
    have hγk : k • edgeGamma h hNα hαβ = edgeGamma h hNα hαβ :=
      MulAction.mem_stabilizer_iff.mp ((edgeGamma_spec h hNα hαβ).2.2 hk)
    have hγti : t⁻¹ • edgeGamma h hNα hαβ = edgeGamma h hNα hαβ := by
      rw [inv_smul_eq_iff]
      exact hγt.symm
    have hγki : k⁻¹ • edgeGamma h hNα hαβ = edgeGamma h hNα hαβ := by
      rw [inv_smul_eq_iff]
      exact hγk.symm
    have hγfix : ⁅t, k⁆ • edgeGamma h hNα hαβ = edgeGamma h hNα hαβ := by
      simp [commutatorElement_def, mul_smul, hγt, hγk, hγti, hγki]
    obtain ⟨z, hz, huniq⟩ :=
      edgeSylow_fixes_unique_of_not_pcore h hNα hαβ hcommS' hQ
    have hzβ : β = z := huniq β ⟨hαβ, hβfix⟩
    have hzγ : edgeGamma h hNα hαβ = z :=
      huniq _ ⟨(edgeGamma_spec h hNα hαβ).1, hγfix⟩
    exact (edgeGamma_spec h hNα hαβ).2.1 (hzβ.trans hzγ.symm).symm
  have hC : pCoreOf 2 (MulAction.stabilizer G α) ≤ kernelOnNeighbors Γ G α := by
    rw [← inf_kernelOnNeighbors_eq_pCoreOf h hNα]
    exact inf_le_right
  exact hC hcommQ

theorem commute_on_neighbors (h : Hyp30 Γ G) {α β : V} {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ)
    (hαβ : Γ.Adj α β) {t k : G}
    (ht : t ∈ pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β))
    (hk : k ∈ edgeTorus h hNα hαβ)
    (hγt : t • edgeGamma h hNα hαβ = edgeGamma h hNα hαβ) :
    ∀ a : V, Γ.Adj α a → t • (k • a) = k • (t • a) := by
  intro a ha
  have hcom := commutator_mem_kernel h hNα hNβ hαβ ht hk hγt
  have hfixall := (mem_kernelOnNeighbors.mp hcom).2
  have htα : t ∈ MulAction.stabilizer G α :=
    (sup_le
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_right)
      (((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans
        inf_le_left).trans hNα.le)) ht
  have hkα : k ∈ MulAction.stabilizer G α := hNα.le (edgeTorus_le h hNα hαβ hk)
  have hta : Γ.Adj α (t • a) := by
    have h1 := (h.adj_smul t α a).2 ha
    simpa [MulAction.mem_stabilizer_iff.mp htα] using h1
  have hkta : Γ.Adj α (k • (t • a)) := by
    have h1 := (h.adj_smul k α (t • a)).2 hta
    simpa [MulAction.mem_stabilizer_iff.mp hkα] using h1
  have h1 := hfixall (k • (t • a)) hkta
  simpa [commutatorElement_def, mul_smul, inv_smul_smul] using h1

theorem kernelOnNeighbors_of_fixes_edgeGamma (h : Hyp30 Γ G) {α β : V} {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ)
    (hαβ : Γ.Adj α β) {t : G}
    (ht : t ∈ pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ⊔
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β))
    (hγt : t • edgeGamma h hNα hαβ = edgeGamma h hNα hαβ) :
    t ∈ kernelOnNeighbors Γ G α := by
  classical
  let T := pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α)
  let S := pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)
  let K := edgeTorus h hNα hαβ
  let γ := edgeGamma h hNα hαβ
  have hγ := edgeGamma_spec h hNα hαβ
  have hTleα : T ≤ MulAction.stabilizer G α :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_right
  have hSleα : S ≤ MulAction.stabilizer G α :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans inf_le_left).trans
      hNα.le
  have hTleβ : T ≤ MulAction.stabilizer G β :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_left).trans
      hNβ.le
  have hSleβ : S ≤ MulAction.stabilizer G β :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans inf_le_right
  have htα : t ∈ MulAction.stabilizer G α := (sup_le hTleα hSleα) ht
  have htβ : t • β = β := MulAction.mem_stabilizer_iff.mp ((sup_le hTleβ hSleβ) ht)
  have htinvβ : t⁻¹ • β = β := by
    have h := congrArg (fun z : V => t⁻¹ • z) htβ
    simpa using h.symm
  have htinvγ : t⁻¹ • γ = γ := by
    have h := congrArg (fun z : V => t⁻¹ • z) hγt
    simpa using h.symm
  have hβγ : β ≠ γ := fun hb => hγ.2.1 hb.symm
  have hfin : (Γ.neighborSet α \ {β, γ}).Finite := (h.finite_neighborSet α).sdiff
  have hstep : ∀ a : V, a ∈ Γ.neighborSet α \ {β, γ} →
      t • a ∈ Γ.neighborSet α \ {β, γ} := by
    intro a ha
    rw [Set.mem_sdiff] at ha
    obtain ⟨haneigh, hane⟩ := ha
    have haadj : Γ.Adj α a := (SimpleGraph.mem_neighborSet (G := Γ) α a).mp haneigh
    have haβ : a ≠ β := by intro h1; exact hane (by simp [h1])
    have haγ : a ≠ γ := by intro h1; exact hane (by simp [h1])
    have htaadj : Γ.Adj α (t • a) := by
      have h1 := (h.adj_smul t α a).2 haadj
      simpa [MulAction.mem_stabilizer_iff.mp htα] using h1
    have htaβ : t • a ≠ β := by
      intro h1
      have h2 : t⁻¹ • (t • a) = t⁻¹ • β := by rw [h1]
      rw [inv_smul_smul, htinvβ] at h2
      exact haβ h2
    have htaγ : t • a ≠ γ := by
      intro h1
      have h2 : t⁻¹ • (t • a) = t⁻¹ • γ := by rw [h1]
      rw [inv_smul_smul, htinvγ] at h2
      exact haγ h2
    rw [Set.mem_sdiff]
    exact ⟨(SimpleGraph.mem_neighborSet (G := Γ) α (t • a)).mpr htaadj, by simp [htaβ, htaγ]⟩
  have hfix : ∀ a : V, Γ.Adj α a → t • a = a := by
    intro a ha
    by_cases hn1 : nOf Γ α = 1
    · have hcard : (Γ.neighborSet α \ {β, γ}).ncard = 1 := by
        rw [ncard_neighborSet_diff_two h hαβ hγ.1 hβγ, hn1]
        norm_num
      have hone : ∀ {x y : V}, x ∈ Γ.neighborSet α \ {β, γ} →
          y ∈ Γ.neighborSet α \ {β, γ} → x = y :=
        (Set.ncard_le_one_iff (s := Γ.neighborSet α \ {β, γ}) (hs := hfin)).mp
          (le_of_eq hcard)
      by_cases haβ : a = β
      · rw [haβ]; exact htβ
      by_cases haγ : a = γ
      · rw [haγ]; exact hγt
      have hmem : a ∈ Γ.neighborSet α \ {β, γ} := by
        rw [Set.mem_sdiff]
        exact ⟨(SimpleGraph.mem_neighborSet (G := Γ) α a).mpr ha, by simp [haβ, haγ]⟩
      exact (hone hmem (hstep a hmem)).symm
    · have hn2 : 2 ≤ nOf Γ α := by
        have := (h.valency α).1
        omega
      have hcard : (Γ.neighborSet α \ {β, γ}).ncard = 2 ^ nOf Γ α - 1 :=
        ncard_neighborSet_diff_two h hαβ hγ.1 hβγ
      have hpos : 0 < (Γ.neighborSet α \ {β, γ}).ncard := by
        rw [hcard]
        have h4 : 4 ≤ 2 ^ nOf Γ α := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ nOf Γ α := Nat.pow_le_pow_right (by norm_num) hn2
        omega
      obtain ⟨δ₀, hδ₀⟩ := (Set.ncard_pos (hs := hfin)).mp hpos
      rw [Set.mem_sdiff] at hδ₀
      obtain ⟨hδ₀neigh, hδ₀ne⟩ := hδ₀
      have hδ₀adj : Γ.Adj α δ₀ := (SimpleGraph.mem_neighborSet (G := Γ) α δ₀).mp hδ₀neigh
      have hδ₀β : δ₀ ≠ β := by intro h1; exact hδ₀ne (by simp [h1])
      have hδ₀γ : δ₀ ≠ γ := by intro h1; exact hδ₀ne (by simp [h1])
      have htδ₀ := hstep δ₀ (by rw [Set.mem_sdiff]; exact ⟨hδ₀neigh, hδ₀ne⟩)
      rw [Set.mem_sdiff] at htδ₀
      obtain ⟨htδ₀neigh, htδ₀ne⟩ := htδ₀
      have htδ₀adj : Γ.Adj α (t • δ₀) := (SimpleGraph.mem_neighborSet (G := Γ) α (t • δ₀)).mp htδ₀neigh
      have htδ₀β : t • δ₀ ≠ β := by intro h1; exact htδ₀ne (by simp [h1])
      have htδ₀γ : t • δ₀ ≠ γ := by intro h1; exact htδ₀ne (by simp [h1])
      obtain ⟨k₁, hk₁K, hk₁⟩ :=
        edgeTorus_transitive h hNα hαβ hδ₀adj htδ₀adj hδ₀β hδ₀γ htδ₀β htδ₀γ
      have hact : ∀ b : V, Γ.Adj α b → t • b = k₁ • b := by
        intro b hb
        by_cases hbβ : b = β
        · rw [hbβ, htβ, MulAction.mem_stabilizer_iff.mp (edgeTorus_fixes h hNα hαβ hk₁K)]
        by_cases hbγ : b = γ
        · rw [hbγ, hγt, MulAction.mem_stabilizer_iff.mp (hγ.2.2 hk₁K)]
        · obtain ⟨k, hkK, hk⟩ :=
            edgeTorus_transitive h hNα hαβ hδ₀adj hb hδ₀β hδ₀γ hbβ hbγ
          have hc := commute_on_neighbors h hNα hNβ hαβ ht hkK hγt δ₀ hδ₀adj
          haveI : IsMulCommutative ↥K := (edgeTorus_cyclic h hNα hαβ).1.isMulCommutative
          have hcommK : k * k₁ = k₁ * k := by
            have h' : (⟨k, hkK⟩ : K) * ⟨k₁, hk₁K⟩ = ⟨k₁, hk₁K⟩ * ⟨k, hkK⟩ :=
              mul_comm' _ _
            exact congrArg (fun x : K => (x : G)) h'
          calc t • b = t • (k • δ₀) := by rw [hk]
            _ = k • (t • δ₀) := hc
            _ = k • (k₁ • δ₀) := by rw [hk₁]
            _ = (k * k₁) • δ₀ := (mul_smul k k₁ δ₀).symm
            _ = (k₁ * k) • δ₀ := by rw [hcommK]
            _ = k₁ • (k • δ₀) := mul_smul k₁ k δ₀
            _ = k₁ • b := by rw [hk]
      let Gαs := MulAction.stabilizer G α
      let Δ := neighborActionOf h Gαs le_rfl
      let ρ : Gαs →* Equiv.Perm Δ := MulAction.toPermHom Gαs Δ
      let tα : Gαs := ⟨t, htα⟩
      let k₁α : Gαs := ⟨k₁, hNα.le (edgeTorus_le h hNα hαβ hk₁K)⟩
      have hρ : ρ tα = ρ k₁α := by
        ext aΔ
        have haΔ : Γ.Adj α (aΔ : V) := (SimpleGraph.mem_neighborSet (G := Γ) α (aΔ : V)).mp aΔ.2
        have h1 : (((ρ tα) aΔ : Δ) : V) = t • (aΔ : V) := by
          rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, SubMulAction.val_smul,
            MulAction.subgroup_smul_def]
        have h2 : (((ρ k₁α) aΔ : Δ) : V) = k₁ • (aΔ : V) := by
          rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, SubMulAction.val_smul,
            MulAction.subgroup_smul_def]
        rw [h1, h2]
        exact hact (aΔ : V) haΔ
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hR2 : IsPGroup 2 ↥(T ⊔ S) := by
        have h' := isPGroup_sup_edgeSylow (h := h) (α := α) (β := β)
          (Nα := Nα) (Nβ := Nβ) hNα hNβ hαβ
        rw [sup_comm] at h'
        exact h'
      haveI : Finite ↥(T ⊔ S) := finite_of_le_stabilizer h (α := α) (H := T ⊔ S)
        (sup_le hTleα hSleα)
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR2
      have htorder : orderOf tα ∣ 2 ^ m := by
        have h1 : orderOf t ∣ Nat.card ↥(T ⊔ S) := Subgroup.orderOf_dvd_natCard (T ⊔ S) ht
        have h2 : orderOf t = orderOf tα := Subgroup.orderOf_coe tα
        rw [h2, hm] at h1
        exact h1
      have hkorder : orderOf k₁α ∣ 2 ^ nOf Γ α - 1 := by
        have h1 : orderOf k₁ ∣ Nat.card ↥K := Subgroup.orderOf_dvd_natCard K hk₁K
        have h2 : orderOf k₁ = orderOf k₁α := Subgroup.orderOf_coe k₁α
        rw [h2, (edgeTorus_cyclic h hNα hαβ).2] at h1
        exact h1
      have hodd : Odd (2 ^ nOf Γ α - 1) := by
        have h2 : Even (2 ^ nOf Γ α) :=
          even_two.pow_of_ne_zero (by have := (h.valency α).1; omega)
        exact Nat.Even.sub_odd Nat.one_le_two_pow h2 odd_one
      have hcop : Nat.Coprime (2 ^ m) (2 ^ nOf Γ α - 1) := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · subst hm0
          simp
        · rw [Nat.coprime_pow_left_iff hmpos]
          exact Nat.coprime_two_left.mpr hodd
      have hρ1 : ρ tα = 1 := by
        refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop ?_ ?_)
        · exact (orderOf_map_dvd ρ tα).trans htorder
        · rw [hρ]
          exact (orderOf_map_dvd ρ k₁α).trans hkorder
      have hfixK : ∀ b : V, Γ.Adj α b → t • b = b := by
        intro b hb
        let bΔ : Δ := ⟨b, by change b ∈ Γ.neighborSet α; rw [SimpleGraph.mem_neighborSet]; exact hb⟩
        have h3 : (ρ tα) bΔ = bΔ := by rw [hρ1]; rfl
        have h2 : (((ρ tα) bΔ : Δ) : V) = t • b := by
          rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, SubMulAction.val_smul,
            MulAction.subgroup_smul_def]
        rw [h3] at h2
        exact h2.symm
      exact hfixK a ha
  exact mem_kernelOnNeighbors.mpr ⟨htα, hfix⟩

theorem pCoreOf_inf_le (h : Hyp30 Γ G) {α β : V}
    (hαβ : Γ.Adj α β) {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ) :
    pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) ≤
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) := by
  classical
  let T := pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α)
  let S := pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β)
  let Gαs := MulAction.stabilizer G α
  let Gβs := MulAction.stabilizer G β
  let H := Gαs ⊓ Gβs
  let γ := edgeGamma h hNα hαβ
  have hγ := edgeGamma_spec h hNα hαβ
  have hTleα : T ≤ Gαs :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_right
  have hTleNβ : T ≤ Nβ :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (Nβ ⊓ MulAction.stabilizer G α)).trans inf_le_left
  have hTleβ : T ≤ Gβs := hTleNβ.trans hNβ.le
  have hSleα : S ≤ Gαs :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans inf_le_left).trans
      hNα.le
  have hSleβ : S ≤ Gβs :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (Nα ⊓ MulAction.stabilizer G β)).trans inf_le_right
  have hRleα : T ⊔ S ≤ Gαs := sup_le hTleα hSleα
  have hRleβ : T ⊔ S ≤ Gβs := sup_le hTleβ hSleβ
  have hRleH : T ⊔ S ≤ H := le_inf hRleα hRleβ
  have hQS : pCoreOf 2 Gαs ≤ S := by
    refine le_edgeSylow_of_isPGroup h hNα hαβ (pCoreOf_isPGroup' Gαs) ?_
    refine le_inf hNα.oTwo_le ?_
    intro q hq
    exact MulAction.mem_stabilizer_iff.mpr
      (hNα.Q_fixes_neighbors h.adj_smul (h.finite_stab α) (h.valency α).2 (h.valency α).1
        β hαβ q hq)
  have hQC : pCoreOf 2 Gαs ≤ kernelOnNeighbors Γ G α := by
    rw [← inf_kernelOnNeighbors_eq_pCoreOf h hNα]
    exact inf_le_right
  have hPleGα : (T ⊔ S) ⊓ kernelOnNeighbors Γ G α ≤ Gαs := inf_le_left.trans hRleα
  have hHnormR : H ≤ Subgroup.normalizer ((T ⊔ S : Subgroup G) : Set G) := by
    have h' := sup_edgeSylow_normal (h := h) (α := α) (β := β)
      (Nα := Nα) (Nβ := Nβ) hNα hNβ hαβ
    rw [sup_comm] at h'
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRleH).mp h'
  have hCnormG : Gαs ≤ Subgroup.normalizer (kernelOnNeighbors Γ G α : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (kernelOnNeighbors_le α)).mp
      (kernelOnNeighbors_normal h α)
  have hHnormC : H ≤ Subgroup.normalizer (kernelOnNeighbors Γ G α : Set G) :=
    inf_le_left.trans hCnormG
  have hHnorm : H ≤ Subgroup.normalizer
      (((T ⊔ S) ⊓ kernelOnNeighbors Γ G α : Subgroup G) : Set G) :=
    (le_inf hHnormR hHnormC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQP : pCoreOf 2 Gαs ≤ (T ⊔ S) ⊓ kernelOnNeighbors Γ G α :=
    le_inf (hQS.trans le_sup_right) hQC
  have key : ∀ m ∈ Nα, ∀ c ∈ (T ⊔ S) ⊓ kernelOnNeighbors Γ G α,
      m * c * m⁻¹ ∈ (T ⊔ S) ⊓ kernelOnNeighbors Γ G α := by
    intro m hm c hc
    obtain ⟨hcR, hcC⟩ := hc
    have hmα : m ∈ Gαs := hNα.le hm
    have hcG : c ∈ Gαs := hPleGα ⟨hcR, hcC⟩
    have hmemN : ⁅m, c⁆ ∈ Nα := by
      have hc' : c * m⁻¹ * c⁻¹ ∈ Nα :=
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hNα.le).mp hNα.normal hcG)
          m⁻¹).mp (Nα.inv_mem hm)
      have h2 : ⁅m, c⁆ = m * (c * m⁻¹ * c⁻¹) := by
        rw [commutatorElement_def]; group
      rw [h2]
      exact Nα.mul_mem hm hc'
    have hmemC : ⁅m, c⁆ ∈ kernelOnNeighbors Γ G α := by
      have h1 : m * c * m⁻¹ ∈ kernelOnNeighbors Γ G α :=
        (Subgroup.mem_normalizer_iff.mp (hCnormG hmα) c).mp hcC
      have h2 : ⁅m, c⁆ = (m * c * m⁻¹) * c⁻¹ := by
        rw [commutatorElement_def]
      rw [h2]
      exact (kernelOnNeighbors Γ G α).mul_mem h1 ((kernelOnNeighbors Γ G α).inv_mem hcC)
    have hcommQ : ⁅m, c⁆ ∈ pCoreOf 2 Gαs := by
      rw [← inf_kernelOnNeighbors_eq_pCoreOf h hNα]
      exact ⟨hmemN, hmemC⟩
    have heq : m * c * m⁻¹ = ⁅m, c⁆ * c := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Subgroup.mul_mem _ (hQP hcommQ) ⟨hcR, hcC⟩
  have hNnorm : Nα ≤ Subgroup.normalizer (((T ⊔ S) ⊓ kernelOnNeighbors Γ G α : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact key m hm c hc
    · intro hc
      have h := key m⁻¹ (Nα.inv_mem hm) (m * c * m⁻¹) hc
      simpa [mul_assoc] using h
  have hGnorm : Gαs ≤ Subgroup.normalizer
      (((T ⊔ S) ⊓ kernelOnNeighbors Γ G α : Subgroup G) : Set G) := by
    rw [show Gαs = H ⊔ Nα from (frattini_edgeLocal h hNα hαβ).symm]
    exact sup_le hHnorm hNnorm
  have hPnorm : (((T ⊔ S) ⊓ kernelOnNeighbors Γ G α).subgroupOf Gαs).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPleGα).mpr hGnorm
  have hPQ : (T ⊔ S) ⊓ kernelOnNeighbors Γ G α ≤ pCoreOf 2 Gαs :=
    CFSG.LieType.BorelTits.le_pCoreOf (r := 2) hPleGα hPnorm
      (by
        have hR2 : IsPGroup 2 ↥(T ⊔ S) := by
          have h' := isPGroup_sup_edgeSylow (h := h) (α := α) (β := β)
            (Nα := Nα) (Nβ := Nβ) hNα hNβ hαβ
          rw [sup_comm] at h'
          exact h'
        exact hR2.to_le inf_le_left)
  intro t ht
  have htα : t ∈ Gαs := hTleα ht
  have htβ : t • β = β := MulAction.mem_stabilizer_iff.mp (hTleβ ht)
  have htγ_adj : Γ.Adj α (t • γ) := by
    have h1 := (h.adj_smul t α γ).2 hγ.1
    simpa [MulAction.mem_stabilizer_iff.mp htα] using h1
  have htinvβ : t⁻¹ • β = β := by simpa [htβ] using inv_smul_smul t β
  have htγ_neβ : t • γ ≠ β := by
    intro h1
    have h2 : t⁻¹ • (t • γ) = t⁻¹ • β := by rw [h1]
    rw [inv_smul_smul, htinvβ] at h2
    exact hγ.2.1 h2
  have hγβ : γ ≠ β := fun hb => hγ.2.1 hb
  obtain ⟨s, hsSyl, hs⟩ :=
    edgeSylow_transitive h hNα hαβ hγ.1 htγ_adj hγβ htγ_neβ
  have hsS : s ∈ S := by
    rw [show S = vertexSylowMap h hNα β from edgeSylow_eq_vertexSylowMap h hNα hαβ]
    exact hsSyl
  let x := s⁻¹ * t
  have hxR : x ∈ T ⊔ S := by
    have hs' : s⁻¹ ∈ T ⊔ S := (T ⊔ S).inv_mem (Subgroup.mem_sup_right hsS)
    exact (T ⊔ S).mul_mem hs' (Subgroup.mem_sup_left ht)
  have hxγ : x • γ = γ := by
    rw [mul_smul, ← hs, inv_smul_smul]
  have hxker : x ∈ kernelOnNeighbors Γ G α :=
    kernelOnNeighbors_of_fixes_edgeGamma h hNα hNβ hαβ hxR hxγ
  have hxQ : x ∈ pCoreOf 2 Gαs := hPQ ⟨hxR, hxker⟩
  have ht_sx : t = s * x := by
    simp [x]
  rw [ht_sx]
  exact S.mul_mem hsS (hQS hxQ)

theorem pCoreOf_inf_eq (h : Hyp30 Γ G) {α β : V}
    (hαβ : Γ.Adj α β) {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ) :
    pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) =
      pCoreOf 2 (Nβ ⊓ MulAction.stabilizer G α) := by
  refine le_antisymm ?_ (pCoreOf_inf_le h hαβ hNα hNβ)
  exact pCoreOf_inf_le h hαβ.symm hNβ hNα

theorem isSylowTwoOf_edgeSylow (h : Hyp30 Γ G) {α β : V}
    (hαβ : Γ.Adj α β) {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ) :
    IsSylowTwoOf (pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β))
      (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) := by
  classical
  let Gαβ := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let Bα := Nα ⊓ MulAction.stabilizer G β
  let Bβ := Nβ ⊓ MulAction.stabilizer G α
  let S := pCoreOf 2 Bα
  have hSeq : S = pCoreOf 2 Bβ := pCoreOf_inf_eq h hαβ hNα hNβ
  have hBαG : Bα ≤ Gαβ := le_inf (inf_le_left.trans hNα.le) inf_le_right
  have hBβG : Bβ ≤ Gαβ := le_inf inf_le_right (inf_le_left.trans hNβ.le)
  have hSBα : S ≤ Bα := CFSG.LieType.BorelTits.pCoreOf_le 2 Bα
  have hSBβ : S ≤ Bβ := hSeq ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 Bβ
  have hSleG : S ≤ Gαβ := hSBα.trans hBαG
  have hSylowBα : IsSylowTwoOf S Bα := by
    rw [show S = vertexSylowMap h hNα β from edgeSylow_eq_vertexSylowMap h hNα hαβ]
    exact isSylowTwoOf_vertexSylowMap_edge hNα hαβ
  have hSylowBβ : IsSylowTwoOf S Bβ := by
    rw [hSeq, show pCoreOf 2 Bβ = vertexSylowMap h hNβ α from
      edgeSylow_eq_vertexSylowMap h hNβ hαβ.symm]
    exact isSylowTwoOf_vertexSylowMap_edge hNβ hαβ.symm
  have h25 := inf_stabilizer_eq_sup h hαβ hNα.le hNβ.le hNα.normal hNβ.normal
    hNα.trans hNβ.trans
  have hBα_eq : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ⊓ Nα = Bα := by
    ext x
    simp only [Bα, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxα, hxβ⟩, hxN⟩
      exact ⟨hxN, hxβ⟩
    · rintro ⟨hxN, hxβ⟩
      exact ⟨⟨hNα.le hxN, hxβ⟩, hxN⟩
  have hBβ_eq : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β ⊓ Nβ = Bβ := by
    ext x
    simp only [Bβ, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hxα, hxβ⟩, hxN⟩
      exact ⟨hxN, hxα⟩
    · rintro ⟨hxN, hxα⟩
      exact ⟨⟨hxα, hNβ.le hxN⟩, hxN⟩
  have hsup : Bα ⊔ Bβ = Gαβ := by
    change Bα ⊔ Bβ = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
    rw [h25, hBα_eq, hBβ_eq]
  let Bα' := Bα.subgroupOf Gαβ
  let Bβ' := Bβ.subgroupOf Gαβ
  have hBα'_normal : Bα'.Normal := edgeLocal_normal h hNα (β := β)
  have hBβ'_normal : Bβ'.Normal := edgeLocal_normal_swap h hNβ
  have hsup' : Bα' ⊔ Bβ' = ⊤ := by
    have hsub := Subgroup.subgroupOf_sup hBαG hBβG
    rw [hsup] at hsub
    simpa [Bα', Bβ'] using hsub.symm
  haveI : Bα'.Normal := hBα'_normal
  have hrel1 : Bα'.relIndex ⊤ = Bα'.relIndex Bβ' := by
    rw [← hsup']
    exact Subgroup.relIndex_sup_left (H := Bβ') (K := Bα')
  have hrel2 : Bα'.relIndex Bβ' = (Bα ⊓ Bβ).relIndex Bβ := by
    rw [Subgroup.relIndex_subgroupOf hBβG, Subgroup.inf_relIndex_right]
  have hrel3 : Bα.relIndex Gαβ = Bα'.relIndex ⊤ := by
    have h := Subgroup.relIndex_subgroupOf (H := Bα) (K := Gαβ) (L := Gαβ) le_rfl
    simpa [Bα'] using h.symm
  have hSInt : S ≤ Bα ⊓ Bβ := le_inf hSBα hSBβ
  have hnot : ¬ 2 ∣ (Bα ⊓ Bβ).relIndex Bβ := by
    intro hd
    apply hSylowBβ.2.2
    change 2 ∣ S.relIndex Bβ
    rw [← Subgroup.relIndex_mul_relIndex S (Bα ⊓ Bβ) Bβ hSInt inf_le_right]
    exact dvd_mul_of_dvd_right hd _
  have hBα_not : ¬ 2 ∣ Bα.relIndex Gαβ := by
    rw [hrel3, hrel1, hrel2]
    exact hnot
  have hS_Bα : ¬ 2 ∣ S.relIndex Bα := hSylowBα.2.2
  refine F7.isSylowTwoOf_of_relIndex hSleG (pCoreOf_isPGroup' Bα) ?_
  change ¬ 2 ∣ S.relIndex Gαβ
  rw [← Subgroup.relIndex_mul_relIndex S Bα Gαβ hSBα hBαG]
  exact Nat.prime_two.not_dvd_mul hS_Bα hBα_not

theorem edgeSylow_eq_pCoreOf_edge (h : Hyp30 Γ G) {α β : V}
    (hαβ : Γ.Adj α β) {Nα Nβ : Subgroup G}
    (hNα : IsLocL2 Γ G α (nOf Γ α) Nα) (hNβ : IsLocL2 Γ G β (nOf Γ β) Nβ) :
    pCoreOf 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) =
      pCoreOf 2 (Nα ⊓ MulAction.stabilizer G β) := by
  classical
  let Gαβ := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let Bα := Nα ⊓ MulAction.stabilizer G β
  haveI : Finite ↥Gαβ := finite_of_le_stabilizer h (α := α) (H := Gαβ) inf_le_left
  have hSylow : IsSylowTwoOf (pCoreOf 2 Bα) Gαβ :=
    isSylowTwoOf_edgeSylow h hαβ hNα hNβ
  refine le_antisymm (pCoreOf_le_of_isSylowTwoOf hSylow) ?_
  have hBle : Bα ≤ Gαβ := le_inf (inf_le_left.trans hNα.le) inf_le_right
  have hBnorm : Gαβ ≤ Subgroup.normalizer (Bα : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBle).mp
      (edgeLocal_normal h hNα (β := β))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2)
    (N := pCoreOf 2 Bα) (H := Gαβ) ((CFSG.LieType.BorelTits.pCoreOf_le 2 Bα).trans hBle)
    (hBnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Bα))
    (pCoreOf_isPGroup' Bα)

end CFSG.Quasithin.St84
