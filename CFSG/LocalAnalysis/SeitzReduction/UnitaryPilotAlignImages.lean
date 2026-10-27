module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParam
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresMonomial
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImagesConj
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAlignImages

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore map_centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono blockComplProj)

theorem card_compl_le_card_compl_of_subset {n : ℕ} {I N : Finset (Fin n)} (hIN : I ⊆ N) :
    Nᶜ.card ≤ Iᶜ.card :=
  Finset.card_le_card (Finset.compl_subset_compl.2 hIN)

theorem map_compl_pair {n : ℕ} (ρ : Equiv.Perm (Fin n)) (a b : Fin n) :
    (({a, b} : Finset (Fin n))ᶜ).map ρ.toEmbedding = ({ρ a, ρ b} : Finset (Fin n))ᶜ := by
  ext x
  simp only [Finset.mem_map_equiv, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
    Equiv.symm_apply_eq]

section Images

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} {e : L ≃* unitaryPSU h n} {t : G}

namespace GraphFieldNeighbourParam

variable {X : Subgroup G} {N : Finset (Fin n)}

theorem pieceCore_eq_map_of_compl [Finite G] (P : GraphFieldNeighbourParam e t X N)
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hI2 : 2 ≤ I.card) (hN : 2 ≤ Nᶜ.card)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) :
    pieceCore e I = ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map P.Φ :=
  P.pieceCore_eq_map hIN hI2 (hN.trans (card_compl_le_card_compl_of_subset hIN)) hXI

theorem pieceCore_index_eq_range [Finite G] (P : GraphFieldNeighbourParam e t X N)
    (hN : 2 ≤ N.card) (hXN : X ≤ modelToG e (unitaryBlockTorus h N)) :
    pieceCore e N = centralizerPerfectCore X := by
  rw [pieceCore_eq_range_of_conjTorus e (commutator_blockSpecialLinear_eq_of_unitaryFieldData h hN)
    hXN P.Φ P.ker_le P.range_eq (TorusEquivariant.mono e (Finset.empty_subset N) P.N2),
    P.range_eq]

theorem nonempty_mulEquiv_pieceCore [Finite G] (P : GraphFieldNeighbourParam e t X N)
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hne : I ≠ N) (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) :
    Nonempty (SpecialLinearGroup (Fin I.card) K ≃* pieceCore e I) :=
  nonempty_mulEquiv_pieceCore_of_conjTorus e hIN hne hI2 hIc hXI P.Φ P.ker_le P.range_eq
    (TorusEquivariant.mono e (Finset.empty_subset I) P.N2)

theorem map_eq_map [Finite G] {X' : Subgroup G} {N' : Finset (Fin n)}
    (P : GraphFieldNeighbourParam e t X N) (P' : GraphFieldNeighbourParam e t X' N')
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hIN' : I ⊆ N') (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (hXI' : X' ≤ modelToG e (unitaryBlockTorus h I)) :
    ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map P.Φ =
      ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N')).map P'.Φ := by
  rw [← P.pieceCore_eq_map hIN hI2 hIc hXI, ← P'.pieceCore_eq_map hIN' hI2 hIc hXI']

theorem pieceCore_le_centralizer_of_disjoint [Finite G] (P : GraphFieldNeighbourParam e t X N)
    {I J : Finset (Fin n)} (hIN : I ⊆ N) (hJN : J ⊆ N) (hIJ : Disjoint I J) (hI2 : 2 ≤ I.card)
    (hJ2 : 2 ≤ J.card) (hN : 2 ≤ Nᶜ.card) (hXI : X ≤ modelToG e (unitaryBlockTorus h I))
    (hXJ : X ≤ modelToG e (unitaryBlockTorus h J)) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  rw [P.pieceCore_eq_map_of_compl hIN hI2 hN hXI, P.pieceCore_eq_map_of_compl hJN hJ2 hN hXJ]
  exact LinearPilot.map_subgroupOf_le_centralizer_of_disjoint hIJ P.Φ

theorem modelToG_blockSU_le_map (P : GraphFieldNeighbourParam e t X N) {I : Finset (Fin n)}
    (hIN : I ⊆ N) :
    modelToG e (blockSU h I) ≤
      ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map P.Φ := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  obtain ⟨A, hA, rfl⟩ := (mem_blockSU h).1 hx
  have hAN : A ∈ unitaryBlock h N := unitaryBlock_mono h hIN hA
  exact ⟨⟨toSL h n A, (mem_unitaryBlock_iff_toSL h).1 hAN⟩,
    mem_subgroupOf.2 ((mem_unitaryBlock_iff_toSL h).1 hA), P.N1 ⟨A, hAN⟩⟩

theorem modelToG_blockSU_le_pieceCore [Finite G] (P : GraphFieldNeighbourParam e t X N)
    {I : Finset (Fin n)} (hIN : I ⊆ N) (hI2 : 2 ≤ I.card) (hIc : 2 ≤ Iᶜ.card)
    (hXI : X ≤ modelToG e (unitaryBlockTorus h I)) :
    modelToG e (blockSU h I) ≤ pieceCore e I := by
  rw [P.pieceCore_eq_map hIN hI2 hIc hXI]
  exact P.modelToG_blockSU_le_map hIN

theorem map_eq_map_rootTorus [Finite G] {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (P : GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n)))
    (P' : GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hcd))
      ({c, d}ᶜ : Finset (Fin n)))
    {I : Finset (Fin n)} (hI : I ⊆ {a, b}ᶜ) (hI' : I ⊆ {c, d}ᶜ) (hI2 : 2 ≤ I.card) :
    ((blockSpecialLinear (K := K) I).subgroupOf
        (blockSpecialLinear ({a, b}ᶜ : Finset (Fin n)))).map P.Φ =
      ((blockSpecialLinear (K := K) I).subgroupOf
        (blockSpecialLinear ({c, d}ᶜ : Finset (Fin n)))).map P'.Φ := by
  rw [← P.pieceCore_eq_map_rootTorus hab hI hI2, ← P'.pieceCore_eq_map_rootTorus hcd hI' hI2]

theorem nonempty_mulEquiv_pieceCore_pair_rootTorus [Finite G] (hn : 5 ≤ n) {a b : Fin n}
    (hab : a ≠ b)
    (P : GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n)))
    {i j : Fin n} (hij : i ≠ j) (hI : ({i, j} : Finset (Fin n)) ⊆ {a, b}ᶜ) :
    Nonempty (SpecialLinearGroup (Fin 2) K ≃* pieceCore e ({i, j} : Finset (Fin n))) := by
  have hcard : ({i, j} : Finset (Fin n)).card = 2 := Finset.card_pair hij
  have hne : ({i, j} : Finset (Fin n)) ≠ {a, b}ᶜ := by
    intro heq
    have := card_compl_pair hab
    rw [← heq, hcard] at this
    omega
  obtain ⟨φ⟩ := P.nonempty_mulEquiv_pieceCore hI hne hcard.ge
    (two_le_card_compl_of_subset_compl_pair hab hI) (modelToG_unitaryRootTorus_le e hab hI)
  exact ⟨(LinearPilot.reindexSpecialLinear (finCongr hcard)).symm.trans φ⟩

end GraphFieldNeighbourParam

end Images

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} {e : L ≃* unitaryPSU h n} {t : G}
  {X : Subgroup G} {N : Finset (Fin n)}

theorem GraphFieldNeighbourParam.conj [Finite G] (P : GraphFieldNeighbourParam e t X N)
    (htC : t ∈ centralizer (L : Set G)) (ρ : Equiv.Perm (Fin n)) :
    Nonempty (GraphFieldNeighbourParam e t
      (X.map (MulAut.conj ((e.symm (unitaryProj h n (permSU h ρ.symm)) : L) : G)).toMonoidHom)
      (N.map ρ.toEmbedding)) := by
  set w₀ : unitarySU 2 f K n := permSU h ρ.symm with hw₀
  set g : SpecialLinearGroup (Fin n) K := toSL h n w₀ with hg
  set w : G := ((e.symm (unitaryProj h n w₀) : L) : G) with hw
  have hgP : blockComplProj (N.map ρ.toEmbedding) * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * blockComplProj N :=
    blockComplProj_mul_permSU h ρ N
  set γ := (LinearPilot.conjBlockEquiv (RingHom.id K) g hgP).symm with hγ
  have hmapid : SpecialLinearGroup.map (RingHom.id K) g = g := by
    ext i j
    simp
  have hγapp : ∀ y, ((γ y : blockSpecialLinear (K := K) N) : SpecialLinearGroup (Fin n) K) =
      g⁻¹ * y * g := fun y => by
    rw [hγ, LinearPilot.coe_conjBlockEquiv_symm_apply, hmapid]
  let Φ' : blockSpecialLinear (K := K) (N.map ρ.toEmbedding) →* G :=
    (MulAut.conj w).toMonoidHom.comp (P.Φ.comp γ.toMonoidHom)
  have hΦ' : ∀ y, Φ' y = w * P.Φ (γ y) * w⁻¹ := fun y => rfl
  have hconj : ∀ y : unitarySU 2 f K n,
      w * ((e.symm (unitaryProj h n y) : L) : G) * w⁻¹ =
        ((e.symm (unitaryProj h n (w₀ * y * w₀⁻¹)) : L) : G) := fun y => by
    simp only [hw, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨⟨Φ', ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    have hγs : (P.Φ.comp γ.toMonoidHom).range = P.Φ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective γ),
        ← MonoidHom.range_eq_map]
    rw [MonoidHom.range_comp, hγs, P.range_eq, map_centralizerPerfectCore]
  ·
    intro y hy
    have h1 : P.Φ (γ y) = 1 := (MulEquiv.map_eq_one_iff (MulAut.conj w)).1 hy
    have hz := P.ker_le h1
    rw [mem_center_iff] at hz ⊢
    intro z
    apply γ.injective
    rw [map_mul, map_mul, hz (γ z)]
  ·
    intro x
    have hx : (x : unitarySU 2 f K n) ∈ (unitaryBlock h N).map (MulAut.conj w₀).toMonoidHom := by
      rw [hw₀, map_conj_permSU_unitaryBlock h ρ N]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have hyx' : w₀ * y * w₀⁻¹ = x := hyx
    have hγx : γ ⟨toSL h n x, (mem_unitaryBlock_iff_toSL h).1 x.2⟩ =
        ⟨toSL h n y, (mem_unitaryBlock_iff_toSL h).1 hy⟩ := by
      apply Subtype.ext
      rw [hγapp]
      change g⁻¹ * toSL h n x * g = toSL h n y
      rw [← hyx', hg, map_mul, map_mul, map_inv]
      group
    rw [hΦ', hγx, P.N1 ⟨y, hy⟩, hconj, hyx']
  ·
    intro c _ y
    set c' := unitaryPermParam h ρ.symm c with hc'
    have hcc : unitaryPermParam h ρ c' = c := unitaryPermParam_unitaryPermParam_symm h ρ c
    have hd : w₀ * torusDiagSU h c' * w₀⁻¹ = torusDiagSU h c := by
      rw [hw₀, permSU_mul_torusDiagSU, hcc]
    have hd' : toSL h n (torusDiagSU h c') = g⁻¹ * toSL h n (torusDiagSU h c) * g := by
      rw [← hd, hg, map_mul, map_mul, map_inv]
      group
    have hγc : γ (conjTorus h (N.map ρ.toEmbedding) c y) = conjTorus h N c' (γ y) := by
      apply Subtype.ext
      rw [hγapp, coe_conjTorus_apply, coe_conjTorus_apply, hγapp, hd']
      group
    have hw' : w * ((e.symm (unitaryProj h n (torusDiagSU h c')) : L) : G) * w⁻¹ =
        ((e.symm (unitaryProj h n (torusDiagSU h c)) : L) : G) := by
      rw [hconj, hd]
    rw [hΦ', hΦ', hγc, P.N2 c' c'.2 (γ y), ← hw']
    group
  ·
    intro y
    have htw : t * w = w * t := (mem_centralizer_iff.1 htC w (e.symm _).2).symm
    have hτg : graphFieldSL h n g = g := graphFieldSL_toSL h w₀
    have hτγ : graphFieldBlock h N (γ y) = γ (graphFieldBlock h (N.map ρ.toEmbedding) y) := by
      apply Subtype.ext
      rw [coe_graphFieldBlock_apply, hγapp, hγapp, coe_graphFieldBlock_apply, map_mul, map_mul,
        map_inv, hτg]
    rw [hΦ', hΦ', ← hτγ, ← P.N3 (γ y)]
    calc t * (w * P.Φ (γ y) * w⁻¹) * t⁻¹ = (t * w) * P.Φ (γ y) * (t * w)⁻¹ := by group
      _ = (w * t) * P.Φ (γ y) * (w * t)⁻¹ := by rw [htw]
      _ = w * (t * P.Φ (γ y) * t⁻¹) * w⁻¹ := by group

theorem nonempty_graphFieldNeighbourParam_rootTorus_of_nonempty [Finite G]
    (htC : t ∈ centralizer (L : Set G)) {a b : Fin n} (hab : a ≠ b)
    (hP : Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n))))
    {a' b' : Fin n} (hab' : a' ≠ b') :
    Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab'))
      ({a', b'}ᶜ : Finset (Fin n))) := by
  obtain ⟨P⟩ := hP
  obtain ⟨ρ, rfl, rfl⟩ := LinearPilot.exists_perm_apply_eq_apply_eq hab hab'
  have hX : (modelToG e (unitaryRootTorus h hab)).map
      (MulAut.conj ((e.symm (unitaryProj h n (permSU h ρ.symm)) : L) : G)).toMonoidHom =
        modelToG e (unitaryRootTorus h hab') := by
    rw [← modelToG_map_conj, map_conj_unitaryRootTorus h ρ hab]
  have hP' := P.conj htC ρ
  rw [hX, map_compl_pair] at hP'
  exact hP'

end Transport

section Cover

variable {G : Type*} [Group G] {L : Subgroup G} {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {n : ℕ} {e : L ≃* unitaryPSU h n} {t : G}

@[expose] def GraphFieldNeighbourCover (e : L ≃* unitaryPSU h n) (t : G) (s : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ s → ∃ (X : Subgroup G) (N : Finset (Fin n)), S ⊆ N ∧
    2 ≤ Nᶜ.card ∧ X ≤ modelToG e (unitaryBlockTorus h S) ∧
      Nonempty (GraphFieldNeighbourParam e t X N)

theorem GraphFieldNeighbourCover.mono {s s' : ℕ} (hcov : GraphFieldNeighbourCover e t s)
    (hs : s' ≤ s) : GraphFieldNeighbourCover e t s' :=
  fun S hS => hcov S (hS.trans hs)

theorem graphFieldNeighbourCover_rootTorus
    (hparam : ∀ (a b : Fin n) (hab : a ≠ b),
      Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin n))))
    {s : ℕ} (hs : s + 2 ≤ n) : GraphFieldNeighbourCover e t s := by
  intro S hS
  obtain ⟨a, b, hab, ha, hb⟩ := LinearPilot.exists_two_index_notMem (S := S) (by omega)
  have hSab : S ⊆ ({a, b}ᶜ : Finset (Fin n)) := subset_compl_pair_iff.2 ⟨ha, hb⟩
  refine ⟨modelToG e (unitaryRootTorus h hab), {a, b}ᶜ, hSab, ?_,
    modelToG_unitaryRootTorus_le e hab hSab, hparam a b hab⟩
  rw [compl_compl, Finset.card_pair hab]

theorem graphFieldNeighbourCover_rootTorus_of_nonempty [Finite G]
    (htC : t ∈ centralizer (L : Set G)) {a b : Fin n} (hab : a ≠ b)
    (hP : Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
      ({a, b}ᶜ : Finset (Fin n))))
    {s : ℕ} (hs : s + 2 ≤ n) : GraphFieldNeighbourCover e t s :=
  graphFieldNeighbourCover_rootTorus
    (fun _ _ hab' => nonempty_graphFieldNeighbourParam_rootTorus_of_nonempty htC hab hP hab') hs

theorem pieceCore_le_centralizer_of_graphFieldNeighbourCover [Finite G] {s : ℕ}
    (hcov : GraphFieldNeighbourCover e t s) {I J : Finset (Fin n)} (hIJ : Disjoint I J)
    (hI : 2 ≤ I.card) (hJ : 2 ≤ J.card) (hs : (I ∪ J).card ≤ s) :
    pieceCore e I ≤ centralizer (pieceCore e J : Set G) := by
  obtain ⟨X, N, hSN, hN, hX, ⟨P⟩⟩ := hcov (I ∪ J) hs
  exact P.pieceCore_le_centralizer_of_disjoint (Finset.subset_union_left.trans hSN)
    (Finset.subset_union_right.trans hSN) hIJ hI hJ hN
    (hX.trans (modelToG_mono e (unitaryBlockTorus_anti h Finset.subset_union_left)))
    (hX.trans (modelToG_mono e (unitaryBlockTorus_anti h Finset.subset_union_right)))

theorem exists_pieceCore_eq_map_of_graphFieldNeighbourCover [Finite G] {s : ℕ}
    (hcov : GraphFieldNeighbourCover e t s) {I : Finset (Fin n)} (hI : 2 ≤ I.card)
    (hs : I.card ≤ s) :
    ∃ (X : Subgroup G) (N : Finset (Fin n)) (P : GraphFieldNeighbourParam e t X N), I ⊆ N ∧
      2 ≤ Nᶜ.card ∧ X ≤ modelToG e (unitaryBlockTorus h I) ∧
      pieceCore e I =
        ((blockSpecialLinear (K := K) I).subgroupOf (blockSpecialLinear N)).map P.Φ := by
  obtain ⟨X, N, hIN, hN, hX, ⟨P⟩⟩ := hcov I hs
  exact ⟨X, N, P, hIN, hN, hX, P.pieceCore_eq_map_of_compl hIN hI hN hX⟩

theorem modelToG_blockSU_le_pieceCore_of_graphFieldNeighbourCover [Finite G] {s : ℕ}
    (hcov : GraphFieldNeighbourCover e t s) {I : Finset (Fin n)} (hI : 2 ≤ I.card)
    (hs : I.card ≤ s) : modelToG e (blockSU h I) ≤ pieceCore e I := by
  obtain ⟨X, N, hIN, hN, hX, ⟨P⟩⟩ := hcov I hs
  exact P.modelToG_blockSU_le_pieceCore hIN hI
    (hN.trans (card_compl_le_card_compl_of_subset hIN)) hX

end Cover

end CFSG.SeitzReduction.UnitaryPilot
