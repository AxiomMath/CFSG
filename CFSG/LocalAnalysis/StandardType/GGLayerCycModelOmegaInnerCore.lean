module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaDefs

public section

namespace CFSG.StandardType

namespace LayerCyc

open CFSG.Assembly LayerCores

section Defs

variable {G : Type*} [Group G]

@[expose] def IsSubCycCoreFamily (H : Subgroup G) {β : Type} (S : β → Subgroup G) : Prop :=
  (∀ c, S c ≤ H) ∧ (∀ c, IsSubnormal (S c) H) ∧ (∀ c, CFSG.IsQuasisimple (S c)) ∧
    (∃ k, LayerFacts.ggDer H k ≤ ⨆ c, S c) ∧ ∀ c, IsCyclic (Subgroup.center (S c))

theorem IsCycCoreFamily.toSub {H : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsCycCoreFamily H S) : IsSubCycCoreFamily H S := by
  obtain ⟨hle, hn, hq, hk, hz⟩ := h
  exact ⟨hle, fun c => ggSubnormal_of_normal (hle c) (hn c), hq, hk, hz⟩

theorem isSubCycCoreFamily_of_isSolvable {H : Subgroup G} (hH : Group.IsSolvable H) :
    IsSubCycCoreFamily H (fun c : Empty => c.elim) := by
  obtain ⟨k, hk⟩ := exists_ggDer_eq_bot hH
  exact ⟨fun c => c.elim, fun c => c.elim, fun c => c.elim, ⟨k, by rw [hk]; exact bot_le⟩,
    fun c => c.elim⟩

theorem IsSubCycCoreFamily.mono {H₀ H₁ : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsSubCycCoreFamily H₁ S) (h₀ : H₀ ≤ H₁) (hS : ∀ c, S c ≤ H₀) :
    IsSubCycCoreFamily H₀ S := by
  obtain ⟨-, hn, hq, ⟨k, hk⟩, hz⟩ := h
  exact ⟨hS, fun c => ggSubnormal_mono (hn c) (hS c) h₀, hq,
    ⟨k, (LayerFacts.ggDer_mono h₀ k).trans hk⟩, hz⟩

theorem IsSubCycCoreFamily.inf_of_commutator_le {H N : Subgroup G} {β : Type}
    {S : β → Subgroup G} (h : IsSubCycCoreFamily H S) (hN : ⁅H, H⁆ ≤ N) :
    IsSubCycCoreFamily (H ⊓ N) S := by
  refine h.mono inf_le_left fun c => le_inf (h.1 c) ?_
  rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (h.2.2.1 c)]
  exact (Subgroup.commutator_mono (h.1 c) (h.1 c)).trans hN

variable {G' : Type*} [Group G']

theorem IsSubCycCoreFamily.map {H : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsSubCycCoreFamily H S) (f : G →* G') (hf : Function.Injective f) :
    IsSubCycCoreFamily (H.map f) (fun c => (S c).map f) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  refine ⟨fun c => Subgroup.map_mono (hle c), fun c => ggSubnormal_map f (hn c), fun c => ?_,
    ⟨k, ?_⟩, fun c => isCyclic_center_of_mulEquiv ((S c).equivMapOfInjective f hf) (hz c)⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((S c).equivMapOfInjective f hf) (hq c)
  · rw [← LayerFacts.map_ggDer, ← Subgroup.map_iSup]
    exact Subgroup.map_mono hk

theorem IsSubCycCoreFamily.comap {H' : Subgroup G'} {β : Type} {S : β → Subgroup G'}
    (h : IsSubCycCoreFamily H' S) (f : G →* G') (hf : Function.Injective f)
    (hH : H' ≤ f.range) : IsSubCycCoreFamily (H'.comap f) (fun c => (S c).comap f) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  have hmapS : ∀ c, ((S c).comap f).map f = S c := fun c =>
    Subgroup.map_comap_eq_self ((hle c).trans hH)
  have hmapH : (H'.comap f).map f = H' := Subgroup.map_comap_eq_self hH
  have he : ∀ c, S c ≃* ↥((S c).comap f) := fun c =>
    ((((S c).comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (hmapS c))).symm
  refine ⟨fun c => Subgroup.comap_mono (hle c), fun c => ggSubnormal_comap f (hn c),
    fun c => CFSG.LocalCores.isQuasisimple_of_mulEquiv (he c) (hq c), ⟨k, ?_⟩,
    fun c => isCyclic_center_of_mulEquiv (he c) (hz c)⟩
  rw [← Subgroup.map_le_map_iff_of_injective hf, LayerFacts.map_ggDer, hmapH,
    Subgroup.map_iSup]
  refine hk.trans (iSup_mono fun c => ?_)
  rw [hmapS c]

end Defs

section Prod

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

theorem IsSubCycCoreFamily.prod {H₁ : Subgroup G₁} {H₂ : Subgroup G₂} {β₁ β₂ : Type}
    {S₁ : β₁ → Subgroup G₁} {S₂ : β₂ → Subgroup G₂} (h₁ : IsSubCycCoreFamily H₁ S₁)
    (h₂ : IsSubCycCoreFamily H₂ S₂) : IsSubCycCoreFamily (H₁.prod H₂) (prodFamily S₁ S₂) := by
  obtain ⟨hle₁, hn₁, hq₁, ⟨k₁, hk₁⟩, hz₁⟩ := h₁
  obtain ⟨hle₂, hn₂, hq₂, ⟨k₂, hk₂⟩, hz₂⟩ := h₂
  have hinl : Function.Injective (MonoidHom.inl G₁ G₂) := fun a b h => congrArg Prod.fst h
  have hinr : Function.Injective (MonoidHom.inr G₁ G₂) := fun a b h => congrArg Prod.snd h
  have hn1 : IsSubnormal (H₁.map (MonoidHom.inl G₁ G₂)) (H₁.prod H₂) := by
    refine ggSubnormal_of_normal ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem _⟩
    · rintro u hu _ ⟨x, hx, rfl⟩
      refine ⟨u.1 * x * u.1⁻¹, H₁.mul_mem (H₁.mul_mem (Subgroup.mem_prod.mp hu).1 hx)
        (H₁.inv_mem (Subgroup.mem_prod.mp hu).1), ?_⟩
      ext <;> simp
  have hn2 : IsSubnormal (H₂.map (MonoidHom.inr G₁ G₂)) (H₁.prod H₂) := by
    refine ggSubnormal_of_normal ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hx⟩
    · rintro u hu _ ⟨x, hx, rfl⟩
      refine ⟨u.2 * x * u.2⁻¹, H₂.mul_mem (H₂.mul_mem (Subgroup.mem_prod.mp hu).2 hx)
        (H₂.inv_mem (Subgroup.mem_prod.mp hu).2), ?_⟩
      ext <;> simp
  refine ⟨?_, ?_, ?_, ⟨k₁ + k₂, ?_⟩, ?_⟩
  · rintro (c | c) <;> rintro _ ⟨x, hx, rfl⟩
    · exact Subgroup.mem_prod.mpr ⟨hle₁ c hx, Subgroup.one_mem _⟩
    · exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hle₂ c hx⟩
  · rintro (c | c)
    · exact ggSubnormal_trans (ggSubnormal_map _ (hn₁ c)) hn1
    · exact ggSubnormal_trans (ggSubnormal_map _ (hn₂ c)) hn2
  · rintro (c | c)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((S₁ c).equivMapOfInjective _ hinl) (hq₁ c)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((S₂ c).equivMapOfInjective _ hinr) (hq₂ c)
  · rw [ggDer_prod, iSup_prodFamily]
    exact Subgroup.prod_mono ((ggDer_antitone H₁ (Nat.le_add_right k₁ k₂)).trans hk₁)
      ((ggDer_antitone H₂ (Nat.le_add_left k₂ k₁)).trans hk₂)
  · rintro (c | c)
    · exact isCyclic_center_of_mulEquiv ((S₁ c).equivMapOfInjective _ hinl) (hz₁ c)
    · exact isCyclic_center_of_mulEquiv ((S₂ c).equivMapOfInjective _ hinr) (hz₂ c)

end Prod

section Model

variable {G : Type*} [Group G]

theorem le_or_commute_of_isSubnormal {S E : Subgroup G} (h : IsSubnormal S E)
    (hE : CFSG.IsQuasisimple E) : E ≤ S ∨ ∀ s ∈ S, ∀ e ∈ E, s * e = e * s := by
  revert hE
  induction h with
  | refl => exact fun _ => Or.inl le_rfl
  | @step H M K hHM hn hMK ih =>
    intro hE
    rcases ih hE with hKM | hc
    · have hMK' : M = K := le_antisymm (ggSubnormal_le hMK) hKM
      subst hMK'
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hE hn with h | h
      · left
        intro x hx
        have hx' : (⟨x, hx⟩ : M) ∈ H.subgroupOf M := by
          rw [h]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hx'
      · right
        intro s hs e he
        have hz := h (Subgroup.mem_subgroupOf.mpr hs : (⟨s, hHM hs⟩ : M) ∈ H.subgroupOf M)
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨e, he⟩)).symm
    · exact Or.inr fun s hs e he => hc s (hHM hs) e he

theorem isCyclic_of_isSubCycCoreFamily {C : Subgroup G} {β : Type} {S : β → Subgroup G}
    (hS : IsSubCycCoreFamily C S) (hcomp : IsComponentOf (LargeEvenLayer C) C)
    {T : Subgroup G} (hTE : T ≤ LargeEvenLayer C)
    (hTC : T ≤ Subgroup.centralizer (LargeEvenLayer C : Set G)) : IsCyclic T := by
  obtain ⟨hle, hsn, hq, ⟨k, hk⟩, hcyc⟩ := hS
  set E := LargeEvenLayer C with hEdef
  have hEq : CFSG.IsQuasisimple E := (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have hSE : ∀ c, S c ≤ E := fun c =>
    le_sSup ⟨hle c, hsn c, (TableBSymp.isQuasisimple_iff _).mpr (hq c)⟩
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
  have hES : E ≤ S c := by
    rcases le_or_commute_of_isSubnormal
        (ggSubnormal_mono (hsn c) (hSE c) (LayerCC.largeEvenLayer_le C)) hEq with h | h
    · exact h
    · exfalso
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple (hq c)
      exact hab (Subtype.ext (h a ha b (hSE c hb)))
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

theorem ggModelLayerCyclic_of_subCycCoreFamily {p : ℕ} {H : Type} [Group H] {α : MulAut H}
    (h : α ≠ 1 → α ^ p = 1 →
      ∃ (β : Type) (S : β → Subgroup H), IsSubCycCoreFamily (ggFix α) S) :
    GGModelLayerCyclic p α := by
  intro hα1 hαp hcomp T hTE hTC _
  obtain ⟨β, S, hS⟩ := h hα1 hαp
  exact isCyclic_of_isSubCycCoreFamily hS hcomp hTE hTC

end Model

end LayerCyc

end CFSG.StandardType

end
