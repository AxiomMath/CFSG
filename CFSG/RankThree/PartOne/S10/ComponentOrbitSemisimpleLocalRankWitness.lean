module

public import CFSG.RankThree.PartOne.S10.SemisimpleContract
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.GroupTheory.SteinbergBKComponentOrbitLocalRank
import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartOne.SemisimpleSection

open CFSG CFSG.LocalCores Subgroup
open CFSG.Assembly.RankThreeEven (localRank)

section Coordinates

variable {I : Type} [DecidableEq I] (S : I → Type) [∀ i, Group (S i)]

@[expose] noncomputable def coordSubgroupEquiv (i : I) : S i ≃* coordSubgroup S i :=
  MonoidHom.ofInjective (f := MonoidHom.mulSingle S i) (Pi.mulSingle_injective i)

theorem mem_coordSubgroup_iff {g : ∀ i, S i} {i : I} :
    g ∈ coordSubgroup S i ↔ ∀ j, j ≠ i → g j = 1 := by
  constructor
  · rintro ⟨s, rfl⟩ j hj
    exact Pi.mulSingle_eq_of_ne hj s
  · intro h
    refine ⟨g i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj, h j hj]

theorem normal_coordSubgroup (i : I) : (coordSubgroup S i).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_coordSubgroup_iff] at hn ⊢
  intro j hj
  simp [hn j hj]

variable {S}

theorem isComponent_coordSubgroup [∀ i, IsSimpleGroup (S i)]
    (hS : ∀ i, ∃ a b : S i, a * b ≠ b * a) (i : I) : IsComponent (coordSubgroup S i) :=
  ⟨isQuasisimple_of_mulEquiv (coordSubgroupEquiv S i) (isQuasisimple_of_isSimpleGroup (hS i)).1,
    (normal_coordSubgroup S i).isSubnormal⟩

theorem center_coordSubgroup_eq_bot [∀ i, IsSimpleGroup (S i)]
    (hS : ∀ i, ∃ a b : S i, a * b ≠ b * a) (i : I) : center (coordSubgroup S i) = ⊥ := by
  have h := Subgroup.map_center_eq (coordSubgroupEquiv S i)
  rw [(isQuasisimple_of_isSimpleGroup (hS i)).2, Subgroup.map_bot] at h
  exact h.symm

theorem natCard_coordSubgroup_quotient_center [∀ i, IsSimpleGroup (S i)]
    (hS : ∀ i, ∃ a b : S i, a * b ≠ b * a) (i : I) :
    Nat.card (coordSubgroup S i ⧸ center (coordSubgroup S i)) = Nat.card (S i) := by
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq (center_coordSubgroup_eq_bot hS i)).trans
    QuotientGroup.quotientBot).toEquiv]
  exact Nat.card_congr (coordSubgroupEquiv S i).symm.toEquiv

theorem coordSubgroup_injective (hS : ∀ i, Nontrivial (S i)) :
    Function.Injective (coordSubgroup S) := by
  intro i j h
  by_contra hij
  obtain ⟨t, ht⟩ := exists_ne (1 : S i)
  have hmem : (Pi.mulSingle i t : ∀ i, S i) ∈ coordSubgroup S i := ⟨t, rfl⟩
  rw [h, mem_coordSubgroup_iff] at hmem
  exact ht (by simpa using hmem i hij)

end Coordinates

section ComponentFamily

theorem card_sub_one_le_localRank_of_component_family {H : Type*} [Group H] [Finite H]
    {ι : Type*} [Fintype ι] [Nonempty ι] {q : ℕ} (hq : q.Prime) (L : ι → Subgroup H)
    (hL : ∀ i, IsComponent (L i)) (hinj : Function.Injective L)
    (h2q : ∀ i, 2 * q ∣ Nat.card (L i ⧸ center (L i))) :
    Fintype.card ι - 1 ≤ localRank q H := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h2L : 2 ∣ Nat.card (L i₀) :=
    (dvd_mul_right 2 q).trans ((h2q i₀).trans (Subgroup.card_quotient_dvd_card _))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := L i₀) 2 h2L
  have hex : ∀ i : {i : ι // i ≠ i₀}, ∃ z : L i, orderOf (z : L i ⧸ center (L i)) = q := by
    intro i
    have : Fact q.Prime := ⟨hq⟩
    have hqi : q ∣ Nat.card (L i ⧸ center (L i)) := (dvd_mul_left q 2).trans (h2q i)
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' q hqi
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨z, hs⟩
  choose z hz using hex
  obtain ⟨V, hVB, hVab, hVcard⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.exists_elemAbelian_of_component_family hq
      (fun i : {i : ι // i ≠ i₀} => L i) (fun i => hL i) (fun a b h => Subtype.ext (hinj h))
      (fun i => (z i : H)) (fun i => (z i).2) hz
  have hVu : V ≤ centralizer {(u : H)} := by
    refine hVB.trans ((closure_le _).mpr ?_)
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases distinct_components_commute (hL i) (hL i₀) with h | h
    · exact absurd (hinj h) i.2
    · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h (z i).2) u u.2).symm
  have hu2 : orderOf (u : H) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hcard : Fintype.card {i : ι // i ≠ i₀} = Fintype.card ι - 1 := by
    simp
  rw [hcard] at hVcard
  exact CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hq hu2 hVu hVab hVcard

theorem card_sub_one_le_localRank_pi {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    {S : I → Type} [∀ i, Group (S i)] [∀ i, Finite (S i)] [∀ i, IsSimpleGroup (S i)]
    (hS : ∀ i, ∃ a b : S i, a * b ≠ b * a) {q : ℕ} (hq : q.Prime)
    (h2q : ∀ i, 2 * q ∣ Nat.card (S i)) : Fintype.card I - 1 ≤ localRank q (∀ i, S i) :=
  card_sub_one_le_localRank_of_component_family hq (coordSubgroup S)
    (isComponent_coordSubgroup hS)
    (coordSubgroup_injective fun _ => inferInstance)
    (fun i => by rw [natCard_coordSubgroup_quotient_center hS i]; exact h2q i)

end ComponentFamily

section CentralQuotient

variable {G : Type*} [Group G]

theorem exists_mulEquiv_layerQuotient_of_eq_top (hE : layer G = ⊤) :
    ∃ e : layer G ⧸ center (layer G) ≃* G ⧸ center G,
      ∀ g : layer G, e (g : layer G ⧸ center (layer G)) = ((g : G) : G ⧸ center G) :=
  ⟨QuotientGroup.congr (center (layer G)) (center G)
    ((MulEquiv.subgroupCongr hE).trans Subgroup.topEquiv) (Subgroup.map_center_eq _),
    fun _ => rfl⟩

theorem exists_mulEquiv_quotient_center_pi_components [Finite G] (hE : layer G = ⊤) :
    ∃ φ : G ⧸ center G ≃* (∀ C : ComponentIndex G, C.1 ⧸ center C.1),
      ∀ (C : ComponentIndex G) (g : C.1),
        φ ((g : G) : G ⧸ center G) = Pi.mulSingle C (g : C.1 ⧸ center C.1) := by
  obtain ⟨e1, he1⟩ := exists_mulEquiv_layerQuotient_of_eq_top hE
  refine ⟨((layerCentralQuotientEquiv G).trans e1).symm, fun C g => ?_⟩
  rw [MulEquiv.symm_apply_eq, MulEquiv.trans_apply, layerCentralQuotientEquiv_mulSingle]
  exact (he1 ⟨g, component_le_layer C.2 g.2⟩).symm

end CentralQuotient

section CoordinateMembership

variable {G : Type} [Group G]

theorem phi_mem_coordSubgroup_iff
    (φ : G ⧸ center G ≃* (∀ C : ComponentIndex G, C.1 ⧸ center C.1))
    (hφ : ∀ (C : ComponentIndex G) (g : C.1),
      φ ((g : G) : G ⧸ center G) = Pi.mulSingle C (g : C.1 ⧸ center C.1))
    (C : ComponentIndex G) (s : G ⧸ center G) :
    φ s ∈ coordSubgroup (fun C : ComponentIndex G => C.1 ⧸ center C.1) C ↔
      s ∈ C.1.map (QuotientGroup.mk' (center G)) := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective t
    have hs : s = ((g : G) : G ⧸ center G) := φ.injective (by rw [hφ C g]; exact ht.symm)
    exact ⟨g, g.2, hs.symm⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨((⟨g, hg⟩ : C.1) : C.1 ⧸ center C.1), (hφ C ⟨g, hg⟩).symm⟩

end CoordinateMembership

section OrbitJoin

variable {H : Type*} [Group H]

theorem isComponent_subgroupOf_iSup {ι : Sort*} (A : ι → Subgroup H)
    (hA : ∀ i, IsComponent (A i)) (i : ι) :
    IsComponent ((A i).subgroupOf (⨆ j, A j)) :=
  component_overgroup (hA i) (le_iSup A i)

theorem iSup_subgroupOf_iSup {ι : Sort*} (A : ι → Subgroup H) :
    ⨆ i, (A i).subgroupOf (⨆ j, A j) = ⊤ := by
  apply Subgroup.map_injective (⨆ j, A j).subtype_injective
  have h : ∀ i, ((A i).subgroupOf (⨆ j, A j)).map (⨆ j, A j).subtype = A i := fun i => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_iSup A i)]
  rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
  simp only [h]

theorem layer_iSup_eq_top {ι : Sort*} [Finite H] (A : ι → Subgroup H)
    (hA : ∀ i, IsComponent (A i)) : layer ↥(⨆ j, A j) = ⊤ :=
  eq_top_iff.mpr ((iSup_subgroupOf_iSup A).symm.le.trans
    (iSup_le fun i => component_le_layer (isComponent_subgroupOf_iSup A hA i)))

theorem exists_eq_subgroupOf_of_isComponent_iSup {ι : Sort*} [Finite H] (A : ι → Subgroup H)
    (hA : ∀ i, IsComponent (A i)) {C : Subgroup ↥(⨆ j, A j)} (hC : IsComponent C) :
    ∃ i, C = (A i).subgroupOf (⨆ j, A j) := by
  by_contra hne
  push Not at hne
  have hcomm : ∀ i, ⁅C, (A i).subgroupOf (⨆ j, A j)⁆ = ⊥ := fun i =>
    (distinct_components_commute hC (isComponent_subgroupOf_iSup A hA i)).resolve_left (hne i)
  have hcent : C ≤ center ↥(⨆ j, A j) := by
    intro c hc
    rw [mem_center_iff]
    intro g
    have hg : g ∈ ⨆ i, (A i).subgroupOf (⨆ j, A j) := by
      rw [iSup_subgroupOf_iSup]
      exact mem_top g
    have hle : ⨆ i, (A i).subgroupOf (⨆ j, A j) ≤ centralizer {c} := by
      refine iSup_le fun i g hgi => ?_
      rw [mem_centralizer_singleton_iff]
      have hcc := commutator_eq_bot_iff_le_centralizer.mp (hcomm i) hc
      exact mem_centralizer_iff.mp hcc g hgi
    exact mem_centralizer_singleton_iff.mp (hle hg)
  have : Group.IsSolvable C := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_center_iff.mp (hcent b.2) a)
  have : Nontrivial C := isQuasisimple_nontrivial hC.1
  have : Group.IsPerfect C := hC.1.1
  exact Group.IsPerfect.not_isSolvable C inferInstance

theorem natCard_componentIndex_iSup {ι : Sort*} [Finite H] (A : ι → Subgroup H)
    (hA : ∀ i, IsComponent (A i)) :
    Nat.card (ComponentIndex ↥(⨆ j, A j)) = (Set.range A).ncard := by
  have hset : {C : Subgroup ↥(⨆ j, A j) | IsComponent C} =
      (fun M : Subgroup H => M.subgroupOf (⨆ j, A j)) '' Set.range A := by
    ext C
    constructor
    · intro hC
      obtain ⟨i, rfl⟩ := exists_eq_subgroupOf_of_isComponent_iSup A hA hC
      exact ⟨A i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact isComponent_subgroupOf_iSup A hA i
  have hinj : Set.InjOn (fun M : Subgroup H => M.subgroupOf (⨆ j, A j)) (Set.range A) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    have := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr (le_iSup A i), inf_eq_left.mpr (le_iSup A j)] at this
  rw [← hinj.ncard_image, ← hset, ← Nat.card_coe_set_eq]
  rfl

theorem nonempty_mulEquiv_quotient_center_map_conj (g : H) (L K : Subgroup H)
    (hle : L.map (MulAut.conj g).toMonoidHom ≤ K) :
    Nonempty (((L.map (MulAut.conj g).toMonoidHom).subgroupOf K) ⧸
      center ((L.map (MulAut.conj g).toMonoidHom).subgroupOf K) ≃* L ⧸ center L) := by
  let e : ((L.map (MulAut.conj g).toMonoidHom).subgroupOf K) ≃* L :=
    (Subgroup.subgroupOfEquivOfLe hle).trans
      (L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  exact ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

end OrbitJoin

end CFSG.RankThree.PartOne.SemisimpleSection

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalCores Subgroup SemisimpleSection
open CFSG.Assembly.RankThreeEven (localRank)

theorem component_orbit_semisimple_local_rank_witness :
    ∀ (H : Type) [Group H] [Finite H] (r : ℕ), r.Prime → ∀ x : H, (∃ k : ℕ, orderOf x = r ^ k) →
      ∀ L : Subgroup H, IsComponent L → L.map (MulAut.conj x).toMonoidHom ≠ L →
      ∀ q : ℕ, q.Prime → q ≠ 2 → 2 * q ∣ Nat.card (L ⧸ Subgroup.center L) →
      ∀ (d : ℕ) (K : Subgroup H), d = (conjOrbit x L).ncard → K = conjOrbitJoin x L →
        (∃ k : ℕ, 0 < k ∧ d = r ^ k) ∧ r ≤ d ∧
        Nonempty (K ⧸ Subgroup.center K ≃* (Fin d → (L ⧸ Subgroup.center L))) ∧
        Subgroup.center (K ⧸ Subgroup.center K) = ⊥ ∧ layer (K ⧸ Subgroup.center K) = ⊤ ∧
        d - 1 ≤ localRank q (K ⧸ Subgroup.center K) ∧
        ∀ b : ℕ, (∀ (U : Subgroup H) (M : Subgroup U) [M.Normal], layer (U ⧸ M) = ⊤ →
          localRank q (U ⧸ M) ≤ b) → r ≤ b + 1 := by
  intro H _ _ r hr x hx L hL hmove q hq _ hqL d K hd hK
  subst hK
  obtain ⟨⟨k, hk, hdk⟩, hrd, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBK.component_orbit_ambient_local_rank_witness hr hx hL
      hmove hq hqL hd.symm
  set A : ℤ → Subgroup H := fun n => L.map (MulAut.conj (x ^ n)).toMonoidHom with hA
  have hAcomp : ∀ n, IsComponent (A n) := fun n =>
    isComponent_map_mulEquiv (MulAut.conj (x ^ n)) hL
  have hKA : conjOrbitJoin x L = ⨆ n, A n := rfl
  have hdA : d = (Set.range A).ncard := hd
  have : IsSimpleGroup (L ⧸ center L) := hL.1.2.1
  have hnab : ∃ a b : L ⧸ center L, a * b ≠ b * a := hL.1.2.2
  rw [hKA]
  have hE : layer ↥(⨆ n, A n) = ⊤ := layer_iSup_eq_top A hAcomp
  obtain ⟨φA, -⟩ := exists_mulEquiv_quotient_center_pi_components hE
  have hcard : Nat.card (ComponentIndex ↥(⨆ n, A n)) = d :=
    (natCard_componentIndex_iSup A hAcomp).trans hdA.symm
  have hiso : ∀ C : ComponentIndex ↥(⨆ n, A n), Nonempty (C.1 ⧸ center C.1 ≃* L ⧸ center L) := by
    intro C
    obtain ⟨n, hn⟩ := exists_eq_subgroupOf_of_isComponent_iSup A hAcomp C.2
    obtain ⟨e⟩ := nonempty_mulEquiv_quotient_center_map_conj (x ^ n) L (⨆ j, A j) (le_iSup A n)
    exact ⟨(QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hn)
      (Subgroup.map_center_eq _)).trans e⟩
  let σ : ComponentIndex ↥(⨆ n, A n) ≃ Fin d := (Finite.equivFin _).trans (finCongr hcard)
  let e : ↥(⨆ n, A n) ⧸ center ↥(⨆ n, A n) ≃* (Fin d → L ⧸ center L) :=
    φA.trans ((MulEquiv.piCongrRight fun C => (hiso C).some).trans
      (MulEquiv.arrowCongr σ (MulEquiv.refl _)))
  have hlayer : layer (↥(⨆ n, A n) ⧸ center ↥(⨆ n, A n)) = ⊤ :=
    layer_eq_top_of_mulEquiv_pi (fun _ => hnab) e
  have hcenter : center (↥(⨆ n, A n) ⧸ center ↥(⨆ n, A n)) = ⊥ := by
    have h1 := Subgroup.map_center_eq e
    rw [Subgroup.center_pi] at h1
    have h2 : (Subgroup.pi Set.univ fun _ : Fin d => center (L ⧸ center L)) = ⊥ := by
      rw [(isQuasisimple_of_isSimpleGroup hnab).2]
      ext g
      simp [Subgroup.mem_pi, funext_iff]
    rw [h2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hrank : d - 1 ≤ localRank q (↥(⨆ n, A n) ⧸ center ↥(⨆ n, A n)) := by
    have : Nonempty (Fin d) := ⟨⟨0, by have := hr.two_le; omega⟩⟩
    have hW := card_sub_one_le_localRank_pi (S := fun _ : Fin d => L ⧸ center L)
      (fun _ => hnab) hq (fun _ => hqL)
    rw [Fintype.card_fin] at hW
    rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hq]
    exact hW
  refine ⟨⟨k, hk, hdk⟩, hrd, ⟨e⟩, hcenter, hlayer, hrank, fun b hb => ?_⟩
  have := hb (⨆ n, A n) (center _) hlayer
  omega

end CFSG.RankThree.PartOne
