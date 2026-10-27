module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentCentralSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: a Sylow `2`-subgroup of the maximal subgroup lies in `C_M(t)`

The second-case maximal subgroup `M` is the product of its normal component
`E` and `C_M(t)`.  From the component Sylow theorem we obtain a Sylow
`2`-subgroup of `E` inside `C_M(t)`; the normal-product index identity
`[M : C_M(t)] = [E : E ∩ C_M(t)]` then makes `[M : C_M(t)]` odd, so a Sylow
`2`-subgroup of `C_M(t)` transfers to one of `M`.  Intersecting this Sylow
subgroup with the normal subgroup `E` gives a Sylow `2`-subgroup of `E`, which
we transport back to the ambient component.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- If a normal subgroup `E` generates the whole group with a subgroup `C`,
then `C` has the same index as `E ∩ C` in `E`.  This is the cardinal part of
the second isomorphism theorem for the non-normal factor `C`. -/
private lemma index_eq_index_of_normal_sup
    {G : Type u} [Group G] [Finite G]
    (E C : Subgroup G) (hE : E.Normal) (hEC : E ⊔ C = ⊤) :
    C.index = ((E ⊓ C).subgroupOf E).index := by
  classical
  let : E.Normal := hE
  let b : G ⧸ C := QuotientGroup.mk (1 : G)
  have horbit : MulAction.orbit E b = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    have hg : g ∈ E ⊔ C := by
      rw [hEC]
      trivial
    rcases ((@Subgroup.mem_sup_of_normal_left G _ E C hE g).mp hg) with ⟨e, he, c, hc, rfl⟩
    refine ⟨⟨e, he⟩, ?_⟩
    change (e : G) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
      (QuotientGroup.mk (e * c : G) : G ⧸ C)
    have hsmul : (e : G) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
        QuotientGroup.mk (e * 1 : G) := rfl
    rw [hsmul, mul_one]
    rw [QuotientGroup.eq]
    simpa using hc
  have hstab : MulAction.stabilizer E b = C.subgroupOf E := by
    ext e
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.mem_subgroupOf]
    change (e : E) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
      (QuotientGroup.mk (1 : G) : G ⧸ C) ↔ (e : G) ∈ C
    have hsmul : (e : E) • (QuotientGroup.mk (1 : G) : G ⧸ C) =
        QuotientGroup.mk ((e : G) * 1 : G) := rfl
    rw [hsmul, mul_one]
    rw [QuotientGroup.eq]
    simp
  have hindex : (MulAction.stabilizer E b).index = C.index := by
    rw [MulAction.index_stabilizer]
    rw [horbit, Set.ncard_univ]
    rfl
  rw [← hindex]
  rw [hstab, ← Subgroup.inf_subgroupOf_right, inf_comm]

/-- The intersection of a Sylow `2`-subgroup with a normal subgroup is a
Sylow `2`-subgroup of that normal subgroup. -/
private theorem sylow_inf_normal_is_sylow
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) (hN : N.Normal) (S : Sylow 2 G) :
    ∃ Q : Sylow 2 (↥N),
      (Q : Subgroup N) = (S : Subgroup G).subgroupOf N := by
  classical
  let T : Subgroup N := (S : Subgroup G).subgroupOf N
  have hTp : IsPGroup 2 T := S.isPGroup'.comap_subtype
  let H : Subgroup G := N ⊔ S
  let E' : Subgroup (↥H) := N.subgroupOf H
  let C' : Subgroup (↥H) := S.subgroupOf H
  have hE'normal : E'.Normal := by
    simpa [E'] using (hN.subgroupOf H)
  have hsup : E' ⊔ C' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := N) (A' := S) (B := H)
      le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self H
  have hIdx : C'.index = ((E' ⊓ C').subgroupOf E').index :=
    index_eq_index_of_normal_sup E' C' hE'normal hsup
  have hIdxT : ((E' ⊓ C').subgroupOf E').index = T.index := by
    rw [inf_comm]
    rw [Subgroup.inf_subgroupOf_right]
    change (S.subgroupOf H).relIndex (N.subgroupOf H) = T.index
    rw [Subgroup.relIndex_subgroupOf (H := S) (K := N) (L := H) (hKL := le_sup_left)]
    rfl
  have hTidx : T.index = C'.index := hIdxT.symm.trans hIdx.symm
  have hTdvd : T.index ∣ (S : Subgroup G).index := by
    rw [hTidx]
    refine ⟨H.index, ?_⟩
    simpa [C', Subgroup.relIndex] using
      (Subgroup.relIndex_mul_index (h := (le_sup_right : S ≤ H))).symm
  have hTindex : ¬ 2 ∣ T.index := by
    intro h2
    exact S.not_dvd_index (dvd_trans h2 hTdvd)
  refine ⟨hTp.toSylow hTindex, ?_⟩
  simp [T]

/-- In the second case, the maximal subgroup `M` has a Sylow `2`-subgroup
centralizing `t`, and its intersection with the selected component `E` is
exactly the ambient image of a Sylow `2`-subgroup of `E`. -/
public theorem secondCase_centralizer_contains_sylow
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    ∃ SM : Sylow 2 (↥w.M),
      ((SM : Subgroup w.M).map w.M.subtype) ≤
        Subgroup.centralizer ({c.t} : Set G) ∧
      ∃ SE : Sylow 2 (↥d.E),
        (SE : Subgroup d.E).map d.E.subtype =
          ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E := by
  classical
  let E0 : Subgroup (↥w.M) := d.E.subgroupOf w.M
  let C0 : Subgroup (↥w.M) :=
    (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).subgroupOf w.M
  have hE0normal : E0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff d.E_component.1]
    intro h k hh hk
    exact d.E_normal.2 k hk h hh
  have hE0top : E0 ⊔ C0 = ⊤ := by
    have hM : w.M = d.E ⊔ (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M) :=
      secondCase_M_eq_component_sup_centralizer w d
    have hsub : (d.E ⊔ (Subgroup.centralizer ({c.t} : Set G) ⊓ w.M)).subgroupOf w.M = ⊤ := by
      rw [← hM]
      exact Subgroup.subgroupOf_self w.M
    simpa [E0, C0, Subgroup.subgroupOf_sup d.E_component.1 inf_le_right] using hsub
  obtain ⟨PE, hPE⟩ := secondCase_componentCentralizer_contains_sylow c w d
  let eE0 : (d.E.subgroupOf w.M) ≃* d.E := Subgroup.subgroupOfEquivOfLe d.E_component.1
  let PE0 : Sylow 2 E0 := PE.mapSurjective
    (f := eE0.symm.toMonoidHom) eE0.symm.surjective
  have hPE0_C0 : ∀ x : E0, x ∈ (PE0 : Subgroup E0) → (x : w.M) ∈ C0 := by
    intro x hx
    change x ∈ (PE.map eE0.symm.toMonoidHom : Subgroup E0) at hx
    rcases Subgroup.mem_map.mp hx with ⟨e, he, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_inf]
    constructor
    · have heC : (e : G) ∈ Subgroup.centralizer ({c.t} : Set G) :=
        Subgroup.mem_comap.mp (hPE he)
      simpa [eE0] using heC
    · exact (eE0.symm e : E0).1.2
  let H0 : Subgroup E0 := (E0 ⊓ C0).subgroupOf E0
  have hPE0_H0 : (PE0 : Subgroup E0) ≤ H0 := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, hPE0_C0 x hx⟩
  have hIdx0 : C0.index = H0.index :=
    index_eq_index_of_normal_sup E0 C0 hE0normal hE0top
  have hH0dvd : H0.index ∣ (PE0 : Subgroup E0).index :=
    Subgroup.index_dvd_of_le hPE0_H0
  have hC0odd : ¬ 2 ∣ C0.index := by
    intro h2
    exact PE0.not_dvd_index (dvd_trans (by rwa [hIdx0] at h2) hH0dvd)
  obtain ⟨PC0⟩ : Nonempty (Sylow 2 C0) := inferInstance
  let TC0 : Subgroup (↥w.M) := (PC0 : Subgroup C0).map C0.subtype
  have hTC0p : IsPGroup 2 TC0 := PC0.isPGroup'.map C0.subtype
  have hTC0idx : ¬ 2 ∣ TC0.index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Nat.prime_two PC0.not_dvd_index hC0odd
  let SM : Sylow 2 (↥w.M) := hTC0p.toSylow hTC0idx
  have hTC0leC0 : TC0 ≤ C0 := by
    dsimp [TC0]
    exact Subgroup.map_subtype_le (PC0 : Subgroup C0)
  have hSMleC0 : (SM : Subgroup (↥w.M)) ≤ C0 := by
    simpa [SM, TC0] using hTC0leC0
  have hSMcent : ((SM : Subgroup w.M).map w.M.subtype) ≤
      Subgroup.centralizer ({c.t} : Set G) := by
    have hmap : C0.map w.M.subtype ≤ Subgroup.centralizer ({c.t} : Set G) := by
      change ((Subgroup.centralizer ({c.t} : Set G) ⊓ w.M).subgroupOf w.M).map w.M.subtype ≤
        Subgroup.centralizer ({c.t} : Set G)
      rw [Subgroup.subgroupOf_map_subtype]
      exact le_trans inf_le_left inf_le_left
    exact (Subgroup.map_mono hSMleC0).trans hmap
  obtain ⟨QE0, hQE0⟩ := sylow_inf_normal_is_sylow E0 hE0normal SM
  let SE : Sylow 2 (↥d.E) := QE0.mapSurjective
    (f := eE0.toMonoidHom) eE0.surjective
  have hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((QE0 : Subgroup E0).map E0.subtype).map w.M.subtype := by
    have hhom : d.E.subtype.comp eE0.toMonoidHom = w.M.subtype.comp E0.subtype := by
      ext x
      rfl
    change
      ((QE0.map eE0.toMonoidHom : Subgroup d.E).map d.E.subtype) =
        ((QE0 : Subgroup E0).map E0.subtype).map w.M.subtype
    rw [Subgroup.map_map]
    rw [Subgroup.map_map]
    rw [hhom]
  have hQE0amb : ((QE0 : Subgroup E0).map E0.subtype).map w.M.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E := by
    rw [hQE0, Subgroup.subgroupOf_map_subtype]
    rw [Subgroup.map_inf_eq _ _ w.M.subtype w.M.subtype_injective]
    congr 1
    change (d.E.subgroupOf w.M).map w.M.subtype = d.E
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr d.E_component.1
  refine ⟨SM, hSMcent, SE, ?_⟩
  rw [hSEamb, hQE0amb]

end CFSG.GorensteinWalter
