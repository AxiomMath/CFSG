module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements

public section

namespace CFSG.StandardType.GGQ2Frame.SpPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.SpBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def spRealizationCore {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hOcc : SpComponentOccursIff) (hCent : SpComponentCentEq) (hIn : SpComponentInsideEq)
    (hMk : SpComponentMarked) (hm : 4 ≤ m) (ctx : SpCtx H E hEN K m ζ) :
    RealizationCore H E (planeEntry .symplectic m) where
  coord := ctx.fr.coord
  component := ctx.fr.component
  innerDiag := ctx.innerDiag
  component_le := fun c _ => by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  marked := fun c h => hMk ctx c h.2
  occurs_iff := fun A hA X => by
    constructor
    · rintro h
      obtain ⟨c, hc, hocc, rfl⟩ := (hOcc ctx A hA X).1 h
      exact ⟨c, ⟨hm, hc⟩, hocc, rfl⟩
    · rintro ⟨c, ⟨-, hc⟩, hocc, hX⟩
      exact (hOcc ctx A hA X).2 ⟨c, hc, hocc, hX⟩
  cent_eq := fun c h => hCent ctx c h.2
  inside_eq := fun c h => hIn ctx c h.2
  root_le_cent := fun c _ => by
    intro v hv
    have h0 : v ∈ LinearMap.ker (LinearMap.id : PlaneRaw.V m →ₗ[ZMod 3] PlaneRaw.V m) := hv
    rw [LinearMap.ker_id] at h0
    have hv' : v = 0 := (Submodule.mem_bot (ZMod 3)).mp h0
    rw [hv']
    exact Submodule.zero_mem _

theorem spCtx_of_pieces (hD : SpInnerDiagData) (hF : ExistsSpFrame) (hLe : SpEleH)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel .symplectic m) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 3 ≤ Nat.card E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
      (hEN : E ≤ Subgroup.normalizer (H : Set G)), Nonempty (SpCtx H E hEN K m ζ) := by
  obtain ⟨K, _, _, _, _, hK, hHp, θ, hEN, hEI⟩ := hD hInn
  have hfaith : E ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hx3 : x ^ 3 = 1 := hEab.2 x hx.1
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    exact hC3 (hord ▸ Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (H : Set G)) hx.2)
  obtain ⟨ζ, hζ, hEc, ⟨fr⟩⟩ := hF θ hK hHp hEab hEN hEI hSC hfaith hcard
  have hm : 3 ≤ m := by
    have h : 3 ^ 3 ≤ 3 ^ m := hEc ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥H) := by
    intro h
    apply hC3
    refine h.trans ?_
    have hle : (Subgroup.center ↥H).map H.subtype ≤ Subgroup.centralizer (H : Set G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.mp hy ⟨g, hg⟩
      exact congrArg Subtype.val this
    have hcardeq : Nat.card ((Subgroup.center ↥H).map H.subtype) = Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective H)
    rw [← hcardeq]
    exact Subgroup.card_dvd_of_le hle
  have hEH : E ≤ H := hLe fr hHp hEab hC3
  refine ⟨K, inferInstance, inferInstance, inferInstance, ζ, hEN, ⟨?_⟩⟩
  exact
    { fr := fr, hK := hK, hζ := hζ, hHp := hHp, hEab := hEab, hZ3 := hZ3, hEH := hEH, hm := hm,
      innerDiag := hInn }

theorem spPlacementCore_of_pieces (hD : SpInnerDiagData) (hF : ExistsSpFrame) (hLe : SpEleH)
    (hOcc : SpComponentOccursIff) (hCent : SpComponentCentEq) (hIn : SpComponentInsideEq)
    (hMk : SpComponentMarked) {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel .symplectic m) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E) :
    Nonempty (RealizationCore H E (planeEntry .symplectic m)) := by
  have hcard3 : 3 ^ 3 ≤ Nat.card E :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ := spCtx_of_pieces hD hF hLe hInn hEab hSC hC3 hcard3
  have hEc : Nat.card E = 3 ^ m := by
    rw [← Nat.card_congr ctx.fr.τ.toEquiv, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hm : 4 ≤ m := by
    have h : 3 ^ 4 ≤ 3 ^ m := hEc ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  exact ⟨spRealizationCore hOcc hCent hIn hMk hm ctx⟩

end

end CFSG.StandardType.GGQ2Frame.SpPlacement
