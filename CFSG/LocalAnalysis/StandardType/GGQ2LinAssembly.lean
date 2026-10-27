module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.LinBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def linRealizationCore {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2}
    {K : Type} [Field K] [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hOcc : LinComponentOccursIff) (hCent : LinComponentCentEq) (hIn : LinComponentInsideEq)
    (hMk : LinComponentMarked) (ht : 4 ≤ t) (ctx : LinCtx H E hEN K t ε ζ) :
    RealizationCore H E (planeEntry (.linear ε) t) where
  coord := ctx.fr.coord
  component := ctx.fr.component
  innerDiag := ctx.innerDiag
  component_le := fun c _ => by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  marked := fun c hc => hMk ctx c hc.2
  occurs_iff := fun A hA X => by
    rw [hOcc ctx A hA X]
    constructor
    · rintro ⟨c, hc, hocc, rfl⟩
      exact ⟨c, ⟨ht, hc⟩, hocc, rfl⟩
    · rintro ⟨c, ⟨-, hc⟩, hocc, rfl⟩
      exact ⟨c, hc, hocc, rfl⟩
  cent_eq := fun c hc => hCent ctx c hc.2
  inside_eq := fun c hc => hIn ctx c hc.2
  root_le_cent := fun c _ => by
    intro v hv
    have h0 : v ∈ LinearMap.ker (LinearMap.id : PlaneRaw.V t →ₗ[ZMod 3] PlaneRaw.V t) := hv
    rw [LinearMap.ker_id] at h0
    have hv' : v = 0 := (Submodule.mem_bot (ZMod 3)).mp h0
    rw [hv']
    exact Submodule.zero_mem _

theorem planeAmbientLabel_linear_eq {r t : ℕ} {ε : Fin 2} (h : 2 * t + ε.val = r + 1) :
    planeAmbientLabel (.linear ε) t = ⟨.A, r, 1⟩ := by
  simp only [planeAmbientLabel]
  rw [show 2 * t + ε.val - 1 = r by omega]

theorem linCtx_of_pieces (hD : LinInnerDiagData) (hF : ExistsLinFrame) (hLe : LinEleH)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {r t : ℕ} {ε : Fin 2}
    (hrt : 2 * t + ε.val = r + 1)
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, 1⟩) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 3 ≤ Nat.card E) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
      (hEN : E ≤ Subgroup.normalizer (H : Set G)), Nonempty (LinCtx H E hEN K t ε ζ) := by
  obtain ⟨K, _, _, _, hK, hHp, θ, hEN, hEI⟩ := hD hInn
  obtain ⟨ζ, hζ, hEc, ⟨fr⟩⟩ := hF θ hrt hK hHp hEab hEN hEI hSC hC3 hcard
  have ht : 3 ≤ t := by
    have h : 3 ^ 3 ≤ 3 ^ t := hEc ▸ hcard
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
    have hcardeq : Nat.card ((Subgroup.center ↥H).map H.subtype) =
        Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective H)
    rw [← hcardeq]
    exact Subgroup.card_dvd_of_le hle
  have hEH : E ≤ H := hLe fr hHp hEab hC3
  have hInn' : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.linear ε) t) 3 E H := by
    rw [planeAmbientLabel_linear_eq hrt]
    exact hInn
  exact ⟨K, inferInstance, inferInstance, inferInstance, ζ, hEN,
    ⟨{ fr := fr, hK := hK, hζ := hζ, hHp := hHp, hEab := hEab, hZ3 := hZ3, hEH := hEH, ht := ht,
       innerDiag := hInn' }⟩⟩

theorem linPlacementCore_of_pieces (hD : LinInnerDiagData) (hF : ExistsLinFrame)
    (hLe : LinEleH) (hOcc : LinComponentOccursIff) (hCent : LinComponentCentEq)
    (hIn : LinComponentInsideEq) (hMk : LinComponentMarked) {G : Type} [Group G] [Finite G]
    {H E : Subgroup G} {r t : ℕ} {ε : Fin 2} (hrt : 2 * t + ε.val = r + 1)
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, 1⟩) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E) :
    Nonempty (RealizationCore H E (planeEntry (.linear ε) t)) := by
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ :=
    linCtx_of_pieces hD hF hLe hrt hInn hEab hSC hC3 (le_trans (by norm_num) hcard)
  have hEc : Nat.card E = 3 ^ t := by
    rw [← Nat.card_congr ctx.fr.τ.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have ht : 4 ≤ t := by
    have h : 3 ^ 4 ≤ 3 ^ t := hEc ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  exact ⟨linRealizationCore hOcc hCent hIn hMk ht ctx⟩

end

end CFSG.StandardType.GGQ2Frame.LinPlacement
