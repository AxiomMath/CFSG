module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFamily
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

namespace LayerCores

open CFSG.Assembly

section Subnormal

variable {G : Type*} [Group G]

theorem ggSubnormal_le {H K : Subgroup G} (h : IsSubnormal H K) : H ≤ K :=
  h.le

theorem ggSubnormal_trans {H M K : Subgroup G} (h1 : IsSubnormal H M) (h2 : IsSubnormal M K) :
    IsSubnormal H K :=
  h1.trans h2

theorem ggSubnormal_of_normal {H K : Subgroup G} (hHK : H ≤ K)
    (hn : ∀ u ∈ K, ∀ s ∈ H, u * s * u⁻¹ ∈ H) : IsSubnormal H K :=
  IsSubnormal.step hHK ((Subgroup.normal_subgroupOf_iff hHK).mpr fun s u hs hu => hn u hu s hs)
    (IsSubnormal.refl K)

theorem ggSubnormal_inf {H K : Subgroup G} (h : IsSubnormal H K) (X : Subgroup G) :
    IsSubnormal (H ⊓ X) (K ⊓ X) :=
  h.inf X

theorem ggSubnormal_mono {H K X : Subgroup G} (h : IsSubnormal H K) (hHX : H ≤ X)
    (hXK : X ≤ K) : IsSubnormal H X := by
  have h1 := ggSubnormal_inf h X
  rwa [inf_eq_left.mpr hHX, inf_eq_right.mpr hXK] at h1

variable {G' : Type*} [Group G']

theorem ggSubnormal_map (f : G →* G') {H K : Subgroup G} (h : IsSubnormal H K) :
    IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem ggSubnormal_comap (f : G →* G') {H K : Subgroup G'} (h : IsSubnormal H K) :
    IsSubnormal (H.comap f) (K.comap f) :=
  h.comap f

end Subnormal

section Family

variable {G : Type*} [Group G]

@[expose] def IsSubCoreFamily (H : Subgroup G) {β : Type} (S : β → Subgroup G) : Prop :=
  (∀ c, S c ≤ H) ∧ (∀ c, IsSubnormal (S c) H) ∧ (∀ c, CFSG.IsQuasisimple (S c)) ∧
    (∃ k, LayerFacts.ggDer H k ≤ ⨆ c, S c) ∧
    ∀ z ∈ ⨆ c, S c, (∀ y ∈ ⨆ c, S c, z * y = y * z) → z ^ 2 = 1 → z = 1

theorem IsCoreFamily.toSub {H : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsCoreFamily H S) : IsSubCoreFamily H S := by
  obtain ⟨hle, hn, hq, hk, hz⟩ := h
  exact ⟨hle, fun c => ggSubnormal_of_normal (hle c) (hn c), hq, hk, hz⟩

theorem IsSubCoreFamily.mono {H₀ H₁ : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsSubCoreFamily H₁ S) (h₀ : H₀ ≤ H₁) (hS : ∀ c, S c ≤ H₀) : IsSubCoreFamily H₀ S := by
  obtain ⟨-, hn, hq, ⟨k, hk⟩, hz⟩ := h
  exact ⟨hS, fun c => ggSubnormal_mono (hn c) (hS c) h₀, hq,
    ⟨k, (LayerFacts.ggDer_mono h₀ k).trans hk⟩, hz⟩

theorem IsSubCoreFamily.inf_of_commutator_le {H N : Subgroup G} {β : Type}
    {S : β → Subgroup G} (h : IsSubCoreFamily H S) (hN : ⁅H, H⁆ ≤ N) :
    IsSubCoreFamily (H ⊓ N) S := by
  refine h.mono inf_le_left fun c => le_inf (h.1 c) ?_
  rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (h.2.2.1 c)]
  exact (Subgroup.commutator_mono (h.1 c) (h.1 c)).trans hN

theorem isSubCoreFamily_of_isSolvable {H : Subgroup G} (hH : Group.IsSolvable H) :
    IsSubCoreFamily H (fun c : Empty => c.elim) := by
  obtain ⟨k, hk⟩ := exists_ggDer_eq_bot hH
  refine ⟨fun c => c.elim, fun c => c.elim, fun c => c.elim, ⟨k, by rw [hk]; exact bot_le⟩,
    fun z hz _ _ => ?_⟩
  rwa [iSup_of_empty, Subgroup.mem_bot] at hz

variable {G' : Type*} [Group G']

theorem IsSubCoreFamily.map {H : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsSubCoreFamily H S) (f : G →* G') (hf : Function.Injective f) :
    IsSubCoreFamily (H.map f) (fun c => (S c).map f) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  refine ⟨fun c => Subgroup.map_mono (hle c), fun c => ggSubnormal_map f (hn c), fun c => ?_,
    ⟨k, ?_⟩, fun z hz' hzc hz2 => ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv ((S c).equivMapOfInjective f hf) (hq c)
  · rw [← LayerFacts.map_ggDer, ← Subgroup.map_iSup]
    exact Subgroup.map_mono hk
  · rw [← Subgroup.map_iSup] at hz' hzc
    obtain ⟨z, hz'', rfl⟩ := hz'
    have h1 : z = 1 := hz z hz'' (fun y hy => hf (by
      rw [map_mul, map_mul]
      exact hzc (f y) ⟨y, hy, rfl⟩)) (hf (by rw [map_pow, hz2, map_one]))
    rw [h1, map_one]

theorem IsSubCoreFamily.comap {H' : Subgroup G'} {β : Type} {S : β → Subgroup G'}
    (h : IsSubCoreFamily H' S) (f : G →* G') (hf : Function.Injective f) (hH : H' ≤ f.range) :
    IsSubCoreFamily (H'.comap f) (fun c => (S c).comap f) := by
  have hmapS : ∀ c, ((S c).comap f).map f = S c := fun c =>
    Subgroup.map_comap_eq_self ((h.1 c).trans hH)
  have hmapH : (H'.comap f).map f = H' := Subgroup.map_comap_eq_self hH
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  have hsup : (⨆ c, (S c).comap f).map f = ⨆ c, S c := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hmapS
  refine ⟨fun c => Subgroup.comap_mono (hle c), fun c => ggSubnormal_comap f (hn c),
    fun c => ?_, ⟨k, ?_⟩, fun z hz' hzc hz2 => ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((((S c).comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (hmapS c))).symm
      (hq c)
  · rw [← Subgroup.map_le_map_iff_of_injective hf, LayerFacts.map_ggDer, hmapH, hsup]
    exact hk
  · have hz'' : f z ∈ ⨆ c, S c := by
      rw [← hsup]
      exact Subgroup.mem_map_of_mem f hz'
    have h2 : f z = 1 := hz (f z) hz'' (fun y hy => by
      rw [← hsup] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      rw [← map_mul, ← map_mul, hzc y' hy']) (by rw [← map_pow, hz2, map_one])
    exact hf (h2.trans (map_one f).symm)

end Family

section Prod

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

theorem ggDer_prod (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (k : ℕ) :
    LayerFacts.ggDer (H₁.prod H₂) k = (LayerFacts.ggDer H₁ k).prod (LayerFacts.ggDer H₂ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [LayerFacts.ggDer_succ, LayerFacts.ggDer_succ, LayerFacts.ggDer_succ, ih,
      Subgroup.commutator_prod_prod]

@[expose] def prodFamily {β₁ β₂ : Type} (S₁ : β₁ → Subgroup G₁) (S₂ : β₂ → Subgroup G₂) :
    β₁ ⊕ β₂ → Subgroup (G₁ × G₂) :=
  Sum.elim (fun c => (S₁ c).map (MonoidHom.inl G₁ G₂)) (fun c => (S₂ c).map (MonoidHom.inr G₁ G₂))

theorem iSup_prodFamily {β₁ β₂ : Type} (S₁ : β₁ → Subgroup G₁) (S₂ : β₂ → Subgroup G₂) :
    (⨆ c, prodFamily S₁ S₂ c) = (⨆ c, S₁ c).prod (⨆ c, S₂ c) := by
  rw [prodFamily, iSup_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← Subgroup.map_iSup, ← Subgroup.map_iSup]
  refine le_antisymm (sup_le ?_ ?_) (Subgroup.prod_le_iff.mpr ⟨le_sup_left, le_sup_right⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem _⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hx⟩

theorem IsSubCoreFamily.prod {H₁ : Subgroup G₁} {H₂ : Subgroup G₂} {β₁ β₂ : Type}
    {S₁ : β₁ → Subgroup G₁} {S₂ : β₂ → Subgroup G₂} (h₁ : IsSubCoreFamily H₁ S₁)
    (h₂ : IsSubCoreFamily H₂ S₂) : IsSubCoreFamily (H₁.prod H₂) (prodFamily S₁ S₂) := by
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
  refine ⟨?_, ?_, ?_, ⟨k₁ + k₂, ?_⟩, fun z hz hzc hz2 => ?_⟩
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
  · rw [iSup_prodFamily] at hz hzc
    obtain ⟨hz1, hz2'⟩ := Subgroup.mem_prod.mp hz
    have e1 : z.1 = 1 := hz₁ z.1 hz1 (fun y hy => by
      have := congrArg Prod.fst (hzc (y, 1) (Subgroup.mem_prod.mpr ⟨hy, Subgroup.one_mem _⟩))
      simpa using this) (by simpa using congrArg Prod.fst hz2)
    have e2 : z.2 = 1 := hz₂ z.2 hz2' (fun y hy => by
      have := congrArg Prod.snd (hzc (1, y) (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem _, hy⟩))
      simpa using this) (by simpa using congrArg Prod.snd hz2)
    exact Prod.ext e1 e2

end Prod

end LayerCores

namespace LayerFacts

open CFSG.Assembly LayerCores

theorem ggLayer_of_subcore {L : Type*} [Group L] [Finite L] {G : Type*} [Group G] (ψ : L →* G)
    (hker : ψ.ker ≤ Subgroup.center L) {H : Subgroup G} {C₀ : Subgroup L}
    (hC₀H : C₀.map ψ ≤ H) (hnorm : ((C₀.map ψ).subgroupOf H).Normal)
    (hcomm : ⁅H, H⁆ ≤ C₀.map ψ) {β : Type} {S : β → Subgroup L} (hS : IsSubCoreFamily C₀ S) :
    LargeEvenLayer H = (⨆ b, S b).map ψ ∧ Odd (Nat.card (Subgroup.center ↥(LargeEvenLayer H))) ∧
      ∀ X : Subgroup G, X ≤ H → ⁅X, X⁆ = X → X ≤ LargeEvenLayer H := by
  obtain ⟨hSC, hSn, hSq, hder, hZ⟩ := hS
  set Ñ := ⨆ b, S b with hÑ
  have hcomp : ∀ b, IsComponentOf ((S b).map ψ) H := by
    intro b
    have hKq : CFSG.Assembly.IsQuasisimple ((S b).map ψ) := by
      refine (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_map (hSq b) ψ fun hle => ?_)
      obtain ⟨a, a', haa⟩ := exists_mul_ne_of_isQuasisimple (hSq b)
      exact haa (Subtype.ext (Subgroup.mem_center_iff.mp (hker (hle a.2)) a').symm)
    exact ⟨(Subgroup.map_mono (hSC b)).trans hC₀H,
      ggSubnormal_trans (ggSubnormal_map ψ (hSn b))
        (IsSubnormal.step hC₀H hnorm (IsSubnormal.refl H)), hKq⟩
  have hÑlayer : Ñ.map ψ ≤ LargeEvenLayer H := by
    rw [hÑ, Subgroup.map_iSup]
    exact iSup_le fun b => le_sSup (hcomp b)
  obtain ⟨k, hk⟩ := hder
  have hperf : ∀ X : Subgroup G, X ≤ H → ⁅X, X⁆ = X → X ≤ Ñ.map ψ := by
    intro X hXH hX
    calc X = ggDer X (k + 1) := (ggDer_of_perfect hX _).symm
      _ ≤ ggDer H (k + 1) := ggDer_mono hXH _
      _ = ggDer ⁅H, H⁆ k := ggDer_succ' H k
      _ ≤ ggDer (C₀.map ψ) k := ggDer_mono hcomm k
      _ = (ggDer C₀ k).map ψ := (map_ggDer ψ C₀ k).symm
      _ ≤ Ñ.map ψ := Subgroup.map_mono hk
  have hlayer : LargeEvenLayer H = Ñ.map ψ := by
    refine le_antisymm (sSup_le fun K hK => hperf K hK.1 ?_) hÑlayer
    exact ggCommutator_eq_of_isQuasisimple
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hK.2.2)
  refine ⟨hlayer, ?_, fun X hXH hX => (hperf X hXH hX).trans hlayer.ge⟩
  rw [hlayer]
  have hÑperf : ⁅Ñ, Ñ⁆ = Ñ := by
    refine le_antisymm (Subgroup.commutator_le.mpr fun _ hg _ hh =>
      Ñ.mul_mem (Ñ.mul_mem (Ñ.mul_mem hg hh) (Ñ.inv_mem hg)) (Ñ.inv_mem hh))
      (iSup_le fun b => ?_)
    rw [← ggCommutator_eq_of_isQuasisimple (hSq b)]
    exact Subgroup.commutator_mono (le_iSup S b) (le_iSup S b)
  have hZodd : Odd (Nat.card (Subgroup.center ↥Ñ)) := by
    refine odd_card_of_forall_sq_eq_one fun z hz2 => ?_
    have h1 := hZ ((z : ↥Ñ) : L) (z : ↥Ñ).2 (fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩).symm)
      (by simpa using congrArg (fun t : Subgroup.center ↥Ñ => ((t : ↥Ñ) : L)) hz2)
    exact Subtype.ext (Subtype.ext h1)
  have hsurj := ψ.subgroupMap_surjective Ñ
  have hkerN : (ψ.subgroupMap Ñ).ker ≤ Subgroup.center ↥Ñ := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx1 : ψ (x : L) = 1 := by
      simpa using congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hker (MonoidHom.mem_ker.mpr hx1)) y)
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect (ggIsPerfect_of_commutator_eq hÑperf) _
    hsurj hkerN
  have hc2 : Subgroup.center ↥(Ñ.map ψ) = (Subgroup.center ↥Ñ).map (ψ.subgroupMap Ñ) := by
    rw [← hc, Subgroup.map_comap_eq_self_of_surjective hsurj]
  rw [hc2]
  exact Odd.of_dvd_nat hZodd (Subgroup.card_map_dvd _ _)

end LayerFacts

end CFSG.StandardType
