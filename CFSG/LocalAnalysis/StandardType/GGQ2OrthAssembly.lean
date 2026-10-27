module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthStatements

public section

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.OrthBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose]
def orthRealizationCore {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2}
    {K : Type} [Field K] [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hOcc : OrthComponentOccursIff) (hCent : OrthComponentCentEq) (hIn : OrthComponentInsideEq)
    (hMk : OrthComponentMarked) (ctx : OrthCtx H E hEN K t δ ζ) :
    RealizationCore H E (planeEntry (.orthogonal δ) t) where
  coord := ctx.fr.coord
  component := ctx.fr.component
  innerDiag := ctx.innerDiag
  component_le := fun c _ => by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  marked := hMk ctx
  occurs_iff := fun A hA X => hOcc ctx A hA X
  cent_eq := hCent ctx
  inside_eq := hIn ctx
  root_le_cent := fun c _ => by
    intro v hv
    have h0 : v ∈ LinearMap.ker (LinearMap.id : PlaneRaw.V t →ₗ[ZMod 3] PlaneRaw.V t) := hv
    rw [LinearMap.ker_id] at h0
    have hv' : v = 0 := (Submodule.mem_bot (ZMod 3)).mp h0
    rw [hv']
    exact Submodule.zero_mem _

theorem orthCtx_of_pieces (hD : OrthInnerDiagData) (hF : ExistsOrthFrame) (hLe : OrthEleH)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.orthogonal δ) t) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E)
    (h4 : 4 ≤ t + δ.val) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
      (hEN : E ≤ Subgroup.normalizer (H : Set G)), Nonempty (OrthCtx H E hEN K t δ ζ) := by
  obtain ⟨K, _, _, _, hK, hHp, θ, hEN, hEI⟩ := hD hInn h4
  have hfaith : E ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    have hx3 : x ^ 3 = 1 := hEab.2 x hx.1
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    exact hC3 (hord ▸ Subgroup.orderOf_dvd_natCard (Subgroup.centralizer (H : Set G)) hx.2)
  have hcard3 : 3 ^ 3 ≤ Nat.card E :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard
  obtain ⟨ζ, hζ, hEc, ⟨fr⟩⟩ := hF θ hK hHp hEab h4 hEN hEI hSC hfaith hC3 hcard3
  have ht : 4 ≤ t := by
    have h : 3 ^ 4 ≤ 3 ^ t := hEc ▸ hcard
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
    have hcardeq :
        Nat.card ((Subgroup.center ↥H).map H.subtype) = Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective H)
    rw [← hcardeq]
    exact Subgroup.card_dvd_of_le hle
  have hEH : E ≤ H := hLe fr hK hHp hEab hC3
  refine ⟨K, inferInstance, inferInstance, inferInstance, ζ, hEN, ⟨?_⟩⟩
  exact
    { fr := fr, hK := hK, hζ := hζ, hHp := hHp, hEab := hEab, hZ3 := hZ3, hEH := hEH, ht := ht,
      innerDiag := hInn }

theorem orthPlacementCore_of_pieces (hD : OrthInnerDiagData) (hF : ExistsOrthFrame)
    (hLe : OrthEleH) (hOcc : OrthComponentOccursIff) (hCent : OrthComponentCentEq)
    (hIn : OrthComponentInsideEq) (hMk : OrthComponentMarked)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.orthogonal δ) t) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E)
    (h4 : 4 ≤ t + δ.val) :
    Nonempty (RealizationCore H E (planeEntry (.orthogonal δ) t)) := by
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ := orthCtx_of_pieces hD hF hLe hInn hEab hSC hC3 hcard h4
  exact ⟨orthRealizationCore hOcc hCent hIn hMk ctx⟩

end

end CFSG.StandardType.GGQ2Frame.OrthPlacement
