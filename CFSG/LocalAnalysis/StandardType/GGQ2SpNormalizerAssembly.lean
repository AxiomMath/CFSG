module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin

public section

namespace CFSG.StandardType.GGQ2Frame.SpPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.SpBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem spNormalizerEqs_of_pieces (hCov : CoverComponents.AutomizerCoverEq)
    (hAmb : SpAmbientTorusAut) (hComp : SpComponentTorusAut) (hQ : SpIsQuasisimpleYcode)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (ctx : SpCtx H E hEN K m ζ) :
    (∀ c : PlaneRaw.Code m, PlaneRaw.admissible .symplectic c →
        (ggAutomizer (ctx.fr.component c) E).map (ggLin (p := 3) ctx.fr.coord) =
          PlaneRaw.normalizerOf .symplectic m c) ∧
      (ggAutomizer H E).map (ggLin (p := 3) ctx.fr.coord) =
        PlaneRaw.ambientNormalizer .symplectic m := by
  classical
  have key : ∀ (X : Subgroup ↥H) (ψ : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m),
      ψ ∈ (ggAutomizer (X.map H.subtype) E).map (ggLin (p := 3) ctx.fr.coord) ↔
        ψ ∈ torusAut ζ m (X.map ctx.fr.π) := by
    intro X ψ
    have hp : IsPGroup 3 ↥E := fun a =>
      ⟨1, Subtype.ext (by simpa using ctx.hEab.2 (a : G) a.2)⟩
    have hcov := hCov ctx.hEH ctx.fr.π ctx.fr.rho (fun a => ctx.fr.pi_eq_rho a (ctx.hEH a.2)) hp
      ctx.fr.ker_le (ctx.fr.not_three_dvd_card_ker ctx.hZ3) X
    have hmem : ∀ (Y : Subgroup ↥(StatedSp m K)),
        ψ ∈ torusAut ζ m Y ↔ ∃ y ∈ Y, ∀ u, y * tau ζ m u * y⁻¹ = tau ζ m (ψ u) := fun Y => Iff.rfl
    rw [hmem]
    constructor
    · intro hψ
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hψ
      obtain ⟨y, hy, hyφ⟩ := (hcov φ).1 hφ
      refine ⟨y, hy, fun u => ?_⟩
      obtain ⟨a, rfl⟩ : ∃ a : ↥E, ctx.fr.coord (Additive.ofMul a) = u :=
        ⟨Additive.toMul (ctx.fr.coord.symm u), by simp⟩
      rw [ggLin_apply_ofMul, ← SpFrame.rho_eq_tau, ← SpFrame.rho_eq_tau, hyφ a]
    · rintro ⟨y, hy, hyψ⟩
      refine Subgroup.mem_map.mpr ⟨ggLinInv ctx.fr.coord ψ, (hcov _).2 ⟨y, hy, fun a => ?_⟩,
        ggLin_ggLinInv _ _⟩
      have h1 : ctx.fr.coord (Additive.ofMul (ggLinInv ctx.fr.coord ψ a)) =
          ψ (ctx.fr.coord (Additive.ofMul a)) := by
        rw [← ggLin_apply_ofMul (p := 3) ctx.fr.coord (ggLinInv ctx.fr.coord ψ) a,
          ggLin_ggLinInv]
      rw [SpFrame.rho_eq_tau, SpFrame.rho_eq_tau, h1, ← hyψ]
  refine ⟨fun c hc => ?_, ?_⟩
  · ext ψ
    have hY : (⁅(Ycode ζ m c).comap ctx.fr.π, (Ycode ζ m c).comap ctx.fr.π⁆).map ctx.fr.π =
        Ycode ζ m c :=
      (derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
        (ycode_perfect hQ ctx.hK ctx.hζ hc)).1
    have hk := key (⁅(Ycode ζ m c).comap ctx.fr.π, (Ycode ζ m c).comap ctx.fr.π⁆) ψ
    rw [hY] at hk
    exact hk.trans (Set.ext_iff.mp (hComp ζ m ctx.hK ctx.hζ c hc) ψ)
  · ext ψ
    have hT : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hT' : (⊤ : Subgroup ↥H).map ctx.fr.π = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr ctx.fr.surj
    have hk := key ⊤ ψ
    rw [hT, hT'] at hk
    exact hk.trans (Set.ext_iff.mp (hAmb ζ m ctx.hK ctx.hζ) ψ)

theorem spPlacement_of_pieces (hD : SpInnerDiagData) (hF : ExistsSpFrame) (hLe : SpEleH)
    (hOcc : SpComponentOccursIff) (hCent : SpComponentCentEq) (hIn : SpComponentInsideEq)
    (hMk : SpComponentMarked) (hCov : CoverComponents.AutomizerCoverEq)
    (hAmb : SpAmbientTorusAut) (hComp : SpComponentTorusAut) (hQ : SpIsQuasisimpleYcode)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {m : ℕ}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel .symplectic m) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E) :
    Nonempty (Realization H E (planeEntry .symplectic m)) := by
  have hcard3 : 3 ^ 3 ≤ Nat.card E :=
    le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hcard
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ := spCtx_of_pieces hD hF hLe hInn hEab hSC hC3 hcard3
  have hEc : Nat.card E = 3 ^ m := by
    rw [← Nat.card_congr ctx.fr.τ.toEquiv, Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have hm : 4 ≤ m := by
    have h : 3 ^ 4 ≤ 3 ^ m := hEc ▸ hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  obtain ⟨hN1, hN2⟩ := spNormalizerEqs_of_pieces hCov hAmb hComp hQ ctx
  exact ⟨Realization.ofCore (spRealizationCore hOcc hCent hIn hMk hm ctx)
    ⟨fun c hc => hN1 c hc.2, hN2⟩⟩

end

end CFSG.StandardType.GGQ2Frame.SpPlacement
