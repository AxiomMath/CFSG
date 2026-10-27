module

public import CFSG.LocalAnalysis.StandardType.McLaughlinOddKantorConn

public section

namespace CFSG.StandardType.McLaughlinOdd

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def NcRel (S : Set (V ≃ₗ[ZMod p] V)) (t s : V ≃ₗ[ZMod p] V) : Prop :=
  t ∈ S ∧ s ∈ S ∧ ¬ Commute t s

@[expose] def trComp (S : Set (V ≃ₗ[ZMod p] V)) (t : V ≃ₗ[ZMod p] V) : Set (V ≃ₗ[ZMod p] V) :=
  {s | s ∈ S ∧ Relation.ReflTransGen (NcRel S) t s}

@[expose] def trComps (S : Set (V ≃ₗ[ZMod p] V)) : Set (Set (V ≃ₗ[ZMod p] V)) :=
  {D | ∃ t ∈ S, D = trComp S t}

variable {S : Set (V ≃ₗ[ZMod p] V)}

theorem rtg_ncRel_symm {t s : V ≃ₗ[ZMod p] V} (h : Relation.ReflTransGen (NcRel S) t s) :
    Relation.ReflTransGen (NcRel S) s t := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    obtain ⟨hb, hc, hn⟩ := hbc
    exact Relation.ReflTransGen.head ⟨hc, hb, fun h => hn h.symm⟩ ih

theorem mem_trComp_self {t : V ≃ₗ[ZMod p] V} (ht : t ∈ S) : t ∈ trComp S t :=
  ⟨ht, Relation.ReflTransGen.refl⟩

theorem trComp_subset (t : V ≃ₗ[ZMod p] V) : trComp S t ⊆ S := fun _ hs => hs.1

theorem trComp_eq_of_mem {t s : V ≃ₗ[ZMod p] V} (hs : s ∈ trComp S t) :
    trComp S s = trComp S t := by
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, hs.2.trans h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (rtg_ncRel_symm hs.2).trans h⟩

theorem commute_of_notMem_trComp {t s s' : V ≃ₗ[ZMod p] V} (hs : s ∈ trComp S t) (hs' : s' ∈ S)
    (hs'C : s' ∉ trComp S t) : Commute s s' := by
  by_contra hn
  exact hs'C ⟨hs', hs.2.tail ⟨hs.1, hs', hn⟩⟩

theorem isConnTr_trComp (t : V ≃ₗ[ZMod p] V) : IsConnTr (trComp S t) := by
  intro P hP hcomm
  by_cases hPe : P = ∅
  · exact Or.inl hPe
  right
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hPe
  refine Set.Subset.antisymm hP fun b hb => ?_
  have hab : Relation.ReflTransGen (NcRel S) a b := (rtg_ncRel_symm (hP ha).2).trans hb.2
  induction hab with
  | refl => exact ha
  | tail hac hcd ih =>
    rename_i c d
    have hd : d ∈ trComp S t := ⟨hcd.2.1, ((hP ha).2.trans hac).tail hcd⟩
    have hc : c ∈ P := ih ⟨hcd.1, ((hP ha).2.trans hac)⟩
    by_contra hdP
    exact hcd.2.2 (hcomm c hc d hd hdP)

theorem mem_trComps {t : V ≃ₗ[ZMod p] V} (ht : t ∈ S) : trComp S t ∈ trComps S := ⟨t, ht, rfl⟩

theorem nonempty_of_mem_trComps {D : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S) : D.Nonempty := by
  obtain ⟨t, ht, rfl⟩ := hD
  exact ⟨t, mem_trComp_self ht⟩

theorem subset_of_mem_trComps {D : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S) : D ⊆ S := by
  obtain ⟨t, -, rfl⟩ := hD
  exact trComp_subset t

theorem isConnTr_of_mem_trComps {D : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S) : IsConnTr D := by
  obtain ⟨t, -, rfl⟩ := hD
  exact isConnTr_trComp t

theorem exists_mem_trComps {t : V ≃ₗ[ZMod p] V} (ht : t ∈ S) : ∃ D ∈ trComps S, t ∈ D :=
  ⟨_, mem_trComps ht, mem_trComp_self ht⟩

theorem disjoint_of_mem_trComps {D D' : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S)
    (hD' : D' ∈ trComps S) (hne : D ≠ D') : Disjoint D D' := by
  obtain ⟨t, -, rfl⟩ := hD
  obtain ⟨t', -, rfl⟩ := hD'
  refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
  rw [← trComp_eq_of_mem hx, trComp_eq_of_mem hx']

theorem commute_of_mem_trComps_of_notMem {D : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S)
    {t s : V ≃ₗ[ZMod p] V} (ht : t ∈ D) (hs : s ∈ S) (hsD : s ∉ D) : Commute t s := by
  obtain ⟨u, -, rfl⟩ := hD
  exact commute_of_notMem_trComp ht hs hsD

theorem commute_of_mem_trComps {D D' : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S)
    (hD' : D' ∈ trComps S) (hne : D ≠ D') {t s : V ≃ₗ[ZMod p] V} (ht : t ∈ D) (hs : s ∈ D') :
    Commute t s := by
  exact commute_of_mem_trComps_of_notMem hD ht (subset_of_mem_trComps hD' hs)
    (Set.disjoint_right.mp (disjoint_of_mem_trComps hD hD' hne) hs)

theorem noNormalExpP_closure_of_commute {D : Set (V ≃ₗ[ZMod p] V)} (hDS : D ⊆ S)
    (hcomm : ∀ t ∈ D, ∀ s ∈ S, s ∉ D → Commute t s) (hT : NoNormalExpP (Subgroup.closure S)) :
    NoNormalExpP (Subgroup.closure D) := by
  intro N hN hnorm hexp
  have hcen : ∀ s ∈ S, s ∉ D → ∀ n ∈ Subgroup.closure D, s * n * s⁻¹ = n := by
    intro s hs hsD n hn
    have hle : Subgroup.closure D ≤ Subgroup.centralizer {s} := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (hcomm t ht s hs hsD).eq.symm
    have := Subgroup.mem_centralizer_iff.mp (hle hn) s rfl
    rw [this, mul_inv_cancel_right]
  refine hT N (hN.trans (Subgroup.closure_mono hDS)) (fun g hg n hn => ?_) hexp
  refine Subgroup.closure_induction'' (p := fun g _ => ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (fun s hs n hn => ?_) (fun s hs n hn => ?_) (fun n hn => by simpa using hn)
    (fun a b _ _ ha hb n hn => ?_) hg n hn
  · by_cases hsD : s ∈ D
    · exact hnorm s (Subgroup.subset_closure hsD) n hn
    · rw [hcen s hs hsD n (hN hn)]
      exact hn
  · by_cases hsD : s ∈ D
    · exact hnorm s⁻¹ (Subgroup.inv_mem _ (Subgroup.subset_closure hsD)) n hn
    · have h1 := hcen s hs hsD n (hN hn)
      have h2 : s⁻¹ * n * s⁻¹⁻¹ = n := by
        conv_lhs => rw [← h1]
        group
      rw [h2]
      exact hn
  · have := ha _ (hb n hn)
    rwa [show a * b * n * (a * b)⁻¹ = a * (b * n * b⁻¹) * a⁻¹ by group]

theorem cenSpan_le_fixSub_of_commute {D D' : Set (V ≃ₗ[ZMod p] V)}
    (hD : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f)
    (hcomm : ∀ t ∈ D, ∀ s ∈ D', Commute t s) : cenSpan D' ≤ fixSub (Subgroup.closure D) := by
  rw [cenSpan, Submodule.span_le]
  rintro w ⟨s, hs, g, hsw⟩
  rw [SetLike.mem_coe, mem_fixSub_closure hD]
  intro t ht v f htv
  exact (apply_eq_zero_of_commute htv hsw (hcomm t ht s hs)).1

theorem isCompl_sup_inf {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
    {A B U F : Submodule (ZMod p) M} (hAB : IsCompl A B) (hUF : IsCompl U F) (hAF : A ≤ F) :
    IsCompl (U ⊔ A) (F ⊓ B) := by
  refine ⟨Submodule.disjoint_def.mpr fun x hx hx' => ?_,
    codisjoint_iff.mpr (eq_top_iff.mpr fun y _ => ?_)⟩
  · obtain ⟨u, hu, a, ha, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨hxF, hxB⟩ := Submodule.mem_inf.mp hx'
    have huF : u ∈ F := by
      have := F.sub_mem hxF (hAF ha)
      rwa [add_sub_cancel_right] at this
    have hu0 : u = 0 := Submodule.disjoint_def.mp hUF.disjoint u hu huF
    rw [hu0, zero_add] at hxB ⊢
    exact Submodule.disjoint_def.mp hAB.disjoint a ha hxB
  · have hy : y ∈ U ⊔ F := by rw [hUF.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, f, hf, rfl⟩ := Submodule.mem_sup.mp hy
    have hf' : f ∈ A ⊔ B := by rw [hAB.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf'
    have hbF : b ∈ F := by
      have := F.sub_mem hf (hAF ha)
      rwa [add_sub_cancel_left] at this
    rw [show u + (a + b) = (u + a) + b by abel]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup hu ha) ⟨hbF, hb⟩

theorem finite_linearEquiv [Module.Finite (ZMod p) V] : Finite (V ≃ₗ[ZMod p] V) := by
  have := Module.finite_of_finite (ZMod p) (M := V)
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
    fun e e' h => LinearEquiv.ext (congrFun h)

theorem trComps_finite [Module.Finite (ZMod p) V] (S : Set (V ≃ₗ[ZMod p] V)) :
    (trComps S).Finite := by
  have := finite_linearEquiv (p := p) (V := V)
  exact Set.toFinite _

theorem tr_of_mem_trComps (hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f)
    {D : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S) : ∀ t ∈ D, ∃ v f, IsTransvectionWith t v f :=
  fun t ht => hS t (subset_of_mem_trComps hD ht)

theorem noNormalExpP_of_mem_trComps (hT : NoNormalExpP (Subgroup.closure S))
    {D : Set (V ≃ₗ[ZMod p] V)} (hD : D ∈ trComps S) : NoNormalExpP (Subgroup.closure D) :=
  noNormalExpP_closure_of_commute (subset_of_mem_trComps hD)
    (fun _ ht _ hs hsD => commute_of_mem_trComps_of_notMem hD ht hs hsD) hT

theorem isCompl_finset_trComps (hp : p ≠ 2) [Module.Finite (ZMod p) V]
    (hS : ∀ t ∈ S, ∃ v f, IsTransvectionWith t v f) (hT : NoNormalExpP (Subgroup.closure S))
    (𝒜 : Finset (Set (V ≃ₗ[ZMod p] V))) (h𝒜 : ∀ D ∈ 𝒜, D ∈ trComps S) :
    IsCompl (𝒜.sup cenSpan) (𝒜.inf fun D => fixSub (Subgroup.closure D)) := by
  classical
  induction 𝒜 using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.inf_empty]
    exact isCompl_bot_top
  | insert D 𝒜 hD ih =>
    rw [Finset.sup_insert, Finset.inf_insert]
    have hDm : D ∈ trComps S := h𝒜 D (Finset.mem_insert_self D 𝒜)
    have ih' := ih fun D' hD' => h𝒜 D' (Finset.mem_insert_of_mem hD')
    refine isCompl_sup_inf ih' (kantor_connected hp D (tr_of_mem_trComps hS hDm)
      (isConnTr_of_mem_trComps hDm) (noNormalExpP_of_mem_trComps hT hDm)).1
      (Finset.sup_le fun D' hD' => ?_)
    have hD'm := h𝒜 D' (Finset.mem_insert_of_mem hD')
    have hne : D ≠ D' := fun h => hD (h ▸ hD')
    exact cenSpan_le_fixSub_of_commute (tr_of_mem_trComps hS hDm)
      fun t ht s hs => commute_of_mem_trComps hDm hD'm hne ht hs

end CFSG.StandardType.McLaughlinOdd
