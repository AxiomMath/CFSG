module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLinearCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresDefs

public section

namespace CFSG.StandardType

namespace LayerCyc

open CFSG.Assembly

section Defs

variable {G : Type*} [Group G]

@[expose] def HasCycCore (U : Subgroup G) : Prop :=
  ∃ S : Subgroup G, S ≤ U ∧ (∀ u ∈ U, ∀ s ∈ S, u * s * u⁻¹ ∈ S) ∧
    (∃ k, LayerFacts.ggDer U k ≤ S) ∧
    (S = ⊥ ∨ (CFSG.IsQuasisimple S ∧ IsCyclic (Subgroup.center S)))

theorem hasCycCore_of_isSolvable {U : Subgroup G} (hU : Group.IsSolvable U) : HasCycCore U := by
  obtain ⟨k, hk⟩ := LayerCores.exists_ggDer_eq_bot hU
  refine ⟨⊥, bot_le, fun u _ s hs => ?_, ⟨k, hk.le⟩, Or.inl rfl⟩
  rw [Subgroup.mem_bot.mp hs, mul_one, mul_inv_cancel]
  exact Subgroup.one_mem _

@[expose] def IsCycCoreFamily (H : Subgroup G) {β : Type} (S : β → Subgroup G) : Prop :=
  (∀ c, S c ≤ H) ∧ (∀ c, ∀ u ∈ H, ∀ s ∈ S c, u * s * u⁻¹ ∈ S c) ∧
    (∀ c, CFSG.IsQuasisimple (S c)) ∧ (∃ k, LayerFacts.ggDer H k ≤ ⨆ c, S c) ∧
    ∀ c, IsCyclic (Subgroup.center (S c))

theorem isCyclic_center_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsCyclic (Subgroup.center A)) : IsCyclic (Subgroup.center B) :=
  isCyclic_of_surjective (Subgroup.centerCongr e) (Subgroup.centerCongr e).surjective

theorem IsCycCoreFamily.mono {H₀ H₁ : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsCycCoreFamily H₁ S) (h₀ : H₀ ≤ H₁) (hS : ∀ c, S c ≤ H₀) : IsCycCoreFamily H₀ S := by
  obtain ⟨-, hn, hq, ⟨k, hk⟩, hz⟩ := h
  exact ⟨hS, fun c u hu s hs => hn c u (h₀ hu) s hs, hq,
    ⟨k, (LayerFacts.ggDer_mono h₀ k).trans hk⟩, hz⟩

variable {G' : Type*} [Group G']

theorem IsCycCoreFamily.map {H : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsCycCoreFamily H S) (f : G →* G') (hf : Function.Injective f) :
    IsCycCoreFamily (H.map f) (fun c => (S c).map f) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  refine ⟨fun c => Subgroup.map_mono (hle c), fun c u hu s hs => ?_, fun c => ?_, ⟨k, ?_⟩,
    fun c => isCyclic_center_of_mulEquiv ((S c).equivMapOfInjective f hf) (hz c)⟩
  · obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨s, hs, rfl⟩ := hs
    exact ⟨u * s * u⁻¹, hn c u hu s hs, by rw [map_mul, map_mul, map_inv]⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((S c).equivMapOfInjective f hf) (hq c)
  · rw [← LayerFacts.map_ggDer, ← Subgroup.map_iSup]
    exact Subgroup.map_mono hk

theorem IsCycCoreFamily.comap {H' : Subgroup G'} {β : Type} {S : β → Subgroup G'}
    (h : IsCycCoreFamily H' S) (f : G →* G') (hf : Function.Injective f) (hH : H' ≤ f.range) :
    IsCycCoreFamily (H'.comap f) (fun c => (S c).comap f) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  have hmapS : ∀ c, ((S c).comap f).map f = S c := fun c =>
    Subgroup.map_comap_eq_self ((hle c).trans hH)
  have hmapH : (H'.comap f).map f = H' := Subgroup.map_comap_eq_self hH
  have he : ∀ c, S c ≃* ↥((S c).comap f) := fun c =>
    ((((S c).comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (hmapS c))).symm
  refine ⟨fun c => Subgroup.comap_mono (hle c), fun c u hu s hs => ?_,
    fun c => CFSG.LocalCores.isQuasisimple_of_mulEquiv (he c) (hq c), ⟨k, ?_⟩,
    fun c => isCyclic_center_of_mulEquiv (he c) (hz c)⟩
  · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hn c (f u) hu (f s) hs
  · rw [← Subgroup.map_le_map_iff_of_injective hf, LayerFacts.map_ggDer, hmapH,
      Subgroup.map_iSup]
    refine hk.trans (iSup_mono fun c => ?_)
    rw [hmapS c]

end Defs

theorem isCyclic_center_of_forall_mem_center {d : ℕ} {D : Type*} [Field D] [Finite D]
    {S : Subgroup (GL (Fin d) D)}
    (h : ∀ z ∈ S, (∀ y ∈ S, z * y = y * z) → z ∈ Subgroup.center (GL (Fin d) D)) :
    IsCyclic (Subgroup.center S) := by
  have : IsCyclic (Subgroup.center (GL (Fin d) D)) := LayerCC.isCyclic_center_GL
  have hmem : ∀ z : Subgroup.center S,
      ((z : S) : GL (Fin d) D) ∈ Subgroup.center (GL (Fin d) D) := fun z =>
    h _ (z : S).2 fun y hy => (congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)).symm
  let f : Subgroup.center S →* Subgroup.center (GL (Fin d) D) :=
    ((S.subtype.comp (Subgroup.center S).subtype).codRestrict _ hmem)
  refine isCyclic_of_injective f fun a b hab => ?_
  have h1 : ((f a : Subgroup.center (GL (Fin d) D)) : GL (Fin d) D) = f b :=
    congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h1)

theorem mem_center_of_eq_smul_one {d : ℕ} {D : Type*} [Field D] {z : GL (Fin d) D} {c : D}
    (hz : (z : Matrix (Fin d) (Fin d) D) = c • (1 : Matrix (Fin d) (Fin d) D)) :
    z ∈ Subgroup.center (GL (Fin d) D) :=
  Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    ⟨c, by rw [hz, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem isCyclic_of_isCycCoreFamily {G : Type*} [Group G] {C : Subgroup G} {β : Type}
    {S : β → Subgroup G} (hS : IsCycCoreFamily C S)
    (hcomp : IsComponentOf (LargeEvenLayer C) C) {T : Subgroup G}
    (hTE : T ≤ LargeEvenLayer C) (hTC : T ≤ Subgroup.centralizer (LargeEvenLayer C : Set G)) :
    IsCyclic T := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hcyc⟩ := hS
  set E := LargeEvenLayer C with hEdef
  have hEq : CFSG.IsQuasisimple E := (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have hSE : ∀ c, S c ≤ E := by
    intro c
    have hnormal : ((S c).subgroupOf C).Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hn c g g.2 x hx
    exact le_sSup ⟨hle c, IsSubnormal.step (hle c) hnormal (IsSubnormal.refl C),
      (TableBSymp.isQuasisimple_iff _).mpr (hq c)⟩
  have hEle : E ≤ ⨆ c, S c := by
    have hEp : ⁅E, E⁆ = E := LayerCC.commutator_largeEvenLayer C
    calc E = LayerFacts.ggDer E k := (LayerFacts.ggDer_of_perfect hEp k).symm
      _ ≤ LayerFacts.ggDer C k := LayerFacts.ggDer_mono (LayerCC.largeEvenLayer_le C) k
      _ ≤ ⨆ c, S c := hk
  obtain ⟨c⟩ : Nonempty β := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hbot : (⨆ c, S c) = ⊥ := iSup_of_empty _
    obtain ⟨x, hx1⟩ := LayerCC.exists_ne_one_of_isQuasisimple hEq
    apply hx1
    have hx : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact hEle x.2
    exact Subtype.ext (Subgroup.mem_bot.mp hx)
  have hNn : ((S c).subgroupOf E).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn c g (LayerCC.largeEvenLayer_le C g.2) x hx
  have hES : E ≤ S c := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hEq hNn with h | h
    · intro x hx
      have hx' : (⟨x, hx⟩ : E) ∈ (S c).subgroupOf E := by
        rw [h]
        exact Subgroup.mem_top _
      exact hx'
    · exfalso
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple (hq c)
      have haZ := h (show (⟨a, hSE c ha⟩ : E) ∈ (S c).subgroupOf E from ha)
      have h1 := Subgroup.mem_center_iff.mp haZ ⟨b, hSE c hb⟩
      apply hab
      apply Subtype.ext
      exact (congrArg Subtype.val h1).symm
  have hTS : T ≤ S c := hTE.trans hES
  have hcen : ∀ t : T, Subgroup.inclusion hTS t ∈ Subgroup.center (S c) := by
    intro t
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hTC t.2) g (hSE c g.2)
  have := hcyc c
  exact isCyclic_of_injective ((Subgroup.inclusion hTS).codRestrict _ hcen) fun a b hab =>
    Subgroup.inclusion_injective hTS (congrArg Subtype.val hab)

theorem ggModelLayerCyclic_of_cycCoreFamily {p : ℕ} {H : Type} [Group H] {α : MulAut H}
    (h : α ≠ 1 → α ^ p = 1 → ∃ (β : Type) (S : β → Subgroup H), IsCycCoreFamily (ggFix α) S) :
    GGModelLayerCyclic p α := by
  intro hα1 hαp hcomp T hTE hTC _
  obtain ⟨β, S, hS⟩ := h hα1 hαp
  exact isCyclic_of_isCycCoreFamily hS hcomp hTE hTC

end LayerCyc

end CFSG.StandardType

end
