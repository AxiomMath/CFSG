module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2LinNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2LinRealization
public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin

public section

namespace CFSG.StandardType.GGQ2Frame.LinPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.LinBlocks
open CFSG.StandardType.GGQ2Frame.SpPlacement (derived_comap_perfect)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem linNormalizerEqs_of_pieces (hCov : CoverComponents.AutomizerCoverEq)
    (hAmb : LinAmbientTorusAut) (hComp : LinComponentTorusAut) (hQ : LinIsQuasisimpleYcode)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {ε : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : LinCtx H E hEN K t ε ζ) :
    (∀ c : PlaneRaw.Code t, PlaneRaw.admissible (.linear ε) c →
        (ggAutomizer (ctx.fr.component c) E).map (ggLin (p := 3) ctx.fr.coord) =
          PlaneRaw.normalizerOf (.linear ε) t c) ∧
      (ggAutomizer H E).map (ggLin (p := 3) ctx.fr.coord) =
        PlaneRaw.ambientNormalizer (.linear ε) t := by
  classical
  have key : ∀ (X : Subgroup ↥H) (ψ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t),
      ψ ∈ (ggAutomizer (X.map H.subtype) E).map (ggLin (p := 3) ctx.fr.coord) ↔
        ψ ∈ torusAut ζ t ε (X.map ctx.fr.π) := by
    intro X ψ
    have hp : IsPGroup 3 ↥E := fun a =>
      ⟨1, Subtype.ext (by simpa using ctx.hEab.2 (a : G) a.2)⟩
    have hcov := hCov ctx.hEH ctx.fr.π ctx.fr.rho
      (fun a => ctx.fr.pi_eq_rho ctx.hK a (ctx.hEH a.2)) hp ctx.fr.ker_le
      (ctx.fr.not_three_dvd_card_ker ctx.hZ3) X
    have hmem : ∀ Y : Subgroup (GL (LinIdx t ε) K),
        ψ ∈ torusAut ζ t ε Y ↔ ∃ y ∈ Y, ∀ u, y * tau ζ t ε u * y⁻¹ = tau ζ t ε (ψ u) :=
      fun Y => Iff.rfl
    rw [hmem]
    constructor
    · intro hψ
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hψ
      obtain ⟨y, hy, hyφ⟩ := (hcov φ).1 hφ
      refine ⟨y, hy, fun u => ?_⟩
      obtain ⟨a, rfl⟩ : ∃ a : ↥E, ctx.fr.coord (Additive.ofMul a) = u :=
        ⟨Additive.toMul (ctx.fr.coord.symm u), by simp⟩
      rw [ggLin_apply_ofMul, ← LinFrame.rho_eq_tau, ← LinFrame.rho_eq_tau, hyφ a]
    · rintro ⟨y, hy, hyψ⟩
      refine Subgroup.mem_map.mpr ⟨ggLinInv ctx.fr.coord ψ, (hcov _).2 ⟨y, hy, fun a => ?_⟩,
        ggLin_ggLinInv _ _⟩
      have h1 : ctx.fr.coord (Additive.ofMul (ggLinInv ctx.fr.coord ψ a)) =
          ψ (ctx.fr.coord (Additive.ofMul a)) := by
        rw [← ggLin_apply_ofMul (p := 3) ctx.fr.coord (ggLinInv ctx.fr.coord ψ) a,
          ggLin_ggLinInv]
      rw [LinFrame.rho_eq_tau, LinFrame.rho_eq_tau, h1, ← hyψ]
  refine ⟨fun c hc => ?_, ?_⟩
  · ext ψ
    have hY : (⁅(Ycode ζ t ε c).comap ctx.fr.π, (Ycode ζ t ε c).comap ctx.fr.π⁆).map ctx.fr.π =
        Ycode ζ t ε c :=
      (derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
        (ycode_perfect hQ ctx.hK ctx.hζ hc)).1
    have hk := key (⁅(Ycode ζ t ε c).comap ctx.fr.π, (Ycode ζ t ε c).comap ctx.fr.π⁆) ψ
    rw [hY] at hk
    exact hk.trans (Set.ext_iff.mp (hComp ζ t ε ctx.hK ctx.hζ c hc) ψ)
  · ext ψ
    have hT : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hT' : (⊤ : Subgroup ↥H).map ctx.fr.π = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr ctx.fr.surj
    have hk := key ⊤ ψ
    rw [hT, hT'] at hk
    exact hk.trans (Set.ext_iff.mp (hAmb ζ t ε ctx.hK ctx.hζ) ψ)

theorem linPlacement_of_pieces (hD : LinInnerDiagData) (hF : ExistsLinFrame) (hLe : LinEleH)
    (hOcc : LinComponentOccursIff) (hCent : LinComponentCentEq) (hIn : LinComponentInsideEq)
    (hMk : LinComponentMarked) (hCov : CoverComponents.AutomizerCoverEq)
    (hAmb : LinAmbientTorusAut) (hComp : LinComponentTorusAut) (hQ : LinIsQuasisimpleYcode)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {r t : ℕ} {ε : Fin 2}
    (hrt : 2 * t + ε.val = r + 1)
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.A, r, 1⟩) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E) :
    Nonempty (Realization H E (planeEntry (.linear ε) t)) := by
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ :=
    linCtx_of_pieces hD hF hLe hrt hInn hEab hSC hC3 (le_trans (by norm_num) hcard)
  have hEc : Nat.card E = 3 ^ t := by
    rw [← Nat.card_congr ctx.fr.τ.toEquiv, Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have ht : 4 ≤ t := by
    have h : 3 ^ 4 ≤ 3 ^ t := hEc ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  obtain ⟨hN1, hN2⟩ := linNormalizerEqs_of_pieces hCov hAmb hComp hQ ctx
  exact ⟨Realization.ofCore (linRealizationCore hOcc hCent hIn hMk ht ctx)
    ⟨fun c hc => hN1 c hc.2, hN2⟩⟩

end

end CFSG.StandardType.GGQ2Frame.LinPlacement
