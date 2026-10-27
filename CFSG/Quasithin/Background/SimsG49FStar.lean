module

public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.Adapters.WholeGroupLayer
import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GHLemma53OneFStar

public section

namespace CFSG.Quasithin.SimsG4

variable {Γ : Type*} [Group Γ]

namespace G49

theorem normal_subgroupOf {G N : Subgroup Γ} (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    (N.subgroupOf G).Normal :=
  ⟨fun n hn g => hN g g.2 n hn⟩

theorem eq_one_of_forall_commute {N : Subgroup Γ} (hs : IsSimpleGroup ↥N)
    (hnab : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) {z : Γ} (hz : z ∈ N)
    (hzc : ∀ n ∈ N, z * n = n * z) : z = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  have hZ : Subgroup.center ↥N = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center ↥N) with h | h
    · exact h
    · refine absurd ?_ hxy
      have hyZ : (⟨y, hy⟩ : ↥N) ∈ Subgroup.center ↥N := h ▸ Subgroup.mem_top _
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨x, hx⟩)
  have hzZ : (⟨z, hz⟩ : ↥N) ∈ Subgroup.center ↥N :=
    Subgroup.mem_center_iff.mpr fun n => Subtype.ext (hzc n n.2).symm
  rw [hZ, Subgroup.mem_bot] at hzZ
  exact congrArg Subtype.val hzZ

theorem nonabelian_subgroupOf {G N : Subgroup Γ} (hNG : N ≤ G)
    (hnab : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) :
    ∃ x y : ↥(N.subgroupOf G), x * y ≠ y * x := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  exact ⟨⟨⟨x, hNG hx⟩, hx⟩, ⟨⟨y, hNG hy⟩, hy⟩,
    fun h => hxy (congrArg (fun z : ↥(N.subgroupOf G) => ((z : ↥G) : Γ)) h)⟩

theorem centralizer_subgroupOf_eq_bot {G N : Subgroup Γ} (hNG : N ≤ G)
    (hC : ∀ g ∈ G, (∀ n ∈ N, g * n = n * g) → g = 1) :
    Subgroup.centralizer ((N.subgroupOf G : Subgroup ↥G) : Set ↥G) = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr (Subtype.ext (hC g g.2 fun n hn => ?_))
  have h := Subgroup.mem_centralizer_iff.mp hg ⟨n, hNG hn⟩ hn
  exact (congrArg Subtype.val h).symm

theorem isComponent_subgroupOf {G N M : Subgroup Γ} (hNM : N ≤ M) (hMG : M ≤ G)
    (hM : ∀ g ∈ G, ∀ m ∈ M, g * m * g⁻¹ ∈ M) (hN : ∀ g ∈ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hs : IsSimpleGroup ↥N) (hnab : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) :
    CFSG.IsComponent (N.subgroupOf G) := by
  haveI := hs
  haveI : IsSimpleGroup ↥(N.subgroupOf G) :=
    (Subgroup.subgroupOfEquivOfLe (hNM.trans hMG)).isSimpleGroup
  refine ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (nonabelian_subgroupOf (hNM.trans hMG) hnab)).1, ?_⟩
  have hle : N.subgroupOf G ≤ M.subgroupOf G := fun x hx => hNM hx
  refine Subgroup.IsSubnormal.step _ (M.subgroupOf G) hle (normal_subgroupOf hM).isSubnormal ?_
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro n k hn hk
  exact hN k hk n hn

end G49

theorem fStarOf_eq_of_simple_normal {G N : Subgroup Γ} [Finite G] (hNG : N ≤ G)
    (hN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hs : IsSimpleGroup ↥N)
    (hnab : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x)
    (hC : ∀ g ∈ G, (∀ n ∈ N, g * n = n * g) → g = 1) : fStarOf G = N := by
  haveI := hs
  haveI := G49.normal_subgroupOf hN
  haveI : IsSimpleGroup ↥(N.subgroupOf G) := (Subgroup.subgroupOfEquivOfLe hNG).isSimpleGroup
  rw [fStarOf, CFSG.Adapters.generalizedFitting_eq_of_normal_simple_of_centralizer_eq_bot _
    (G49.nonabelian_subgroupOf hNG hnab) (G49.centralizer_subgroupOf_eq_bot hNG hC),
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNG]

theorem fStarOf_eq_of_two_simple {G N₁ N₂ : Subgroup Γ} [Finite G] (hle : N₁ ⊔ N₂ ≤ G)
    (hN : ∀ g ∈ G, ∀ n ∈ N₁ ⊔ N₂, g * n * g⁻¹ ∈ N₁ ⊔ N₂)
    (hcomm : ∀ x ∈ N₁, ∀ y ∈ N₂, x * y = y * x) (hdisj : N₁ ⊓ N₂ = ⊥)
    (hs₁ : IsSimpleGroup ↥N₁) (hs₂ : IsSimpleGroup ↥N₂)
    (hnab₁ : ∃ x ∈ N₁, ∃ y ∈ N₁, x * y ≠ y * x) (hnab₂ : ∃ x ∈ N₂, ∃ y ∈ N₂, x * y ≠ y * x)
    (hC : ∀ g ∈ G, (∀ n ∈ N₁ ⊔ N₂, g * n = n * g) → g = 1) :
    fStarOf G = N₁ ⊔ N₂ ∧ Nonempty (↥(N₁ ⊔ N₂) ≃* ↥N₁ × ↥N₂) := by
  have h₁ : N₁ ≤ G := le_sup_left.trans hle
  have h₂ : N₂ ≤ G := le_sup_right.trans hle
  have hnorm₁ : ∀ g ∈ N₁ ⊔ N₂, ∀ n ∈ N₁, g * n * g⁻¹ ∈ N₁ := by
    have hle₁ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₁ : Set Γ) := by
      refine sup_le Subgroup.le_normalizer fun y hy =>
        Subgroup.centralizer_le_normalizer (N₁ : Set Γ) ?_
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => hcomm x hx y hy
    intro g hg n hn
    exact (Subgroup.mem_normalizer_iff.mp (hle₁ hg) n).mp hn
  have hnorm₂ : ∀ g ∈ N₁ ⊔ N₂, ∀ n ∈ N₂, g * n * g⁻¹ ∈ N₂ := by
    have hle₂ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₂ : Set Γ) := by
      refine sup_le (fun x hx => Subgroup.centralizer_le_normalizer (N₂ : Set Γ) ?_)
        Subgroup.le_normalizer
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm x hx y hy).symm
    intro g hg n hn
    exact (Subgroup.mem_normalizer_iff.mp (hle₂ hg) n).mp hn
  have hA := G49.isComponent_subgroupOf le_sup_left hle hN hnorm₁ hs₁ hnab₁
  have hB := G49.isComponent_subgroupOf le_sup_right hle hN hnorm₂ hs₂ hnab₂
  have hAB : N₁.subgroupOf G ⊔ N₂.subgroupOf G = (N₁ ⊔ N₂).subgroupOf G :=
    (Subgroup.subgroupOf_sup h₁ h₂).symm
  have hF := CFSG.EvenSporadicStandard.RuStd.S2.generalizedFitting_eq_sup_of_isComponent hA hB
    (hAB ▸ G49.centralizer_subgroupOf_eq_bot hle hC)
  refine ⟨?_, ?_⟩
  · rw [fStarOf, hF, hAB, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
  ·
    have hc : ∀ (x : ↥N₁) (y : ↥N₂), Commute (N₁.subtype x) (N₂.subtype y) :=
      fun x y => hcomm x x.2 y y.2
    have hinj : Function.Injective (MonoidHom.noncommCoprod N₁.subtype N₂.subtype hc) :=
      Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hdisj)
    have hrange : (MonoidHom.noncommCoprod N₁.subtype N₂.subtype hc).range = N₁ ⊔ N₂ := by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

end CFSG.Quasithin.SimsG4
