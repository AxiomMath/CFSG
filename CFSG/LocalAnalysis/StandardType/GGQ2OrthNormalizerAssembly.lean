module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthAssembly
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2SpNormalizerStatements
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthRealization
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTauMemOmega
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin

public section

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.OrthBlocks
open CFSG.StandardType.GGQ2Frame.SpPlacement (derived_comap_perfect)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

theorem orthNormalizerEqs_of_pieces (hCov : CoverComponents.AutomizerCoverEq)
    (hAmb : OrthAmbientTorusAut) (hComp : OrthComponentTorusAut) (hQ : OrthIsQuasisimpleYcode)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2} {K : Type} [Field K]
    [Finite K] [CharP K 2] {hEN : E ≤ Subgroup.normalizer (H : Set G)}
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (ctx : OrthCtx H E hEN K t δ ζ) :
    (∀ c : PlaneRaw.Code t, PlaneRaw.admissible (.orthogonal δ) c →
        (ggAutomizer (ctx.fr.component c) E).map (ggLin (p := 3) ctx.fr.coord) =
          PlaneRaw.normalizerOf (.orthogonal δ) t c) ∧
      (ggAutomizer H E).map (ggLin (p := 3) ctx.fr.coord) =
        PlaneRaw.ambientNormalizer (.orthogonal δ) t := by
  classical
  have key : ∀ (X : Subgroup ↥H) (ψ : PlaneRaw.V t ≃ₗ[ZMod 3] PlaneRaw.V t),
      ψ ∈ (ggAutomizer (X.map H.subtype) E).map (ggLin (p := 3) ctx.fr.coord) ↔
        ψ ∈ oTorusAut ζ t δ (X.map ctx.fr.π) := by
    intro X ψ
    have hp : IsPGroup 3 ↥E := fun a =>
      ⟨1, Subtype.ext (by simpa using ctx.hEab.2 (a : G) a.2)⟩
    have hcov := hCov ctx.hEH ctx.fr.π (ctx.fr.rho ctx.hK)
      (fun a => ctx.fr.pi_eq_rho ctx.hK ctx.ht a (ctx.hEH a.2)) hp
      ctx.fr.ker_le (ctx.fr.not_three_dvd_card_ker ctx.hZ3) X
    have hmem : ∀ (Y : Subgroup ↥(omegaQ (K := K) t δ)),
        ψ ∈ oTorusAut ζ t δ Y ↔ ∃ y ∈ Y, ∀ u,
          (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * otau ζ t δ u *
            (y : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)⁻¹ = otau ζ t δ (ψ u) :=
      fun Y => Iff.rfl
    rw [hmem]
    constructor
    · intro hψ
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hψ
      obtain ⟨y, hy, hyφ⟩ := (hcov φ).1 hφ
      refine ⟨y, hy, fun u => ?_⟩
      obtain ⟨a, rfl⟩ : ∃ a : ↥E, ctx.fr.coord (Additive.ofMul a) = u :=
        ⟨Additive.toMul (ctx.fr.coord.symm u), by simp⟩
      rw [ggLin_apply_ofMul, ← OrthFrame.coe_rho, ← OrthFrame.coe_rho]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
        (congrArg Subtype.val (hyφ a)).symm
    · rintro ⟨y, hy, hyψ⟩
      refine Subgroup.mem_map.mpr ⟨ggLinInv ctx.fr.coord ψ, (hcov _).2 ⟨y, hy, fun a => ?_⟩,
        ggLin_ggLinInv _ _⟩
      have h1 : ctx.fr.coord (Additive.ofMul (ggLinInv ctx.fr.coord ψ a)) =
          ψ (ctx.fr.coord (Additive.ofMul a)) := by
        rw [← ggLin_apply_ofMul (p := 3) ctx.fr.coord (ggLinInv ctx.fr.coord ψ) a,
          ggLin_ggLinInv]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [OrthFrame.coe_rho, OrthFrame.coe_rho, h1]
      exact (hyψ (ctx.fr.coord (Additive.ofMul a))).symm
  refine ⟨fun c hc => ?_, ?_⟩
  · ext ψ
    have hY : (⁅(oYcode ζ t δ c).comap ctx.fr.π, (oYcode ζ t δ c).comap ctx.fr.π⁆).map
        ctx.fr.π = oYcode ζ t δ c :=
      (derived_comap_perfect ctx.fr.π ctx.fr.surj ctx.fr.ker_le
        (ycode_perfect hQ ctx.hK ctx.hζ hc)).1
    have hk := key (⁅(oYcode ζ t δ c).comap ctx.fr.π,
      (oYcode ζ t δ c).comap ctx.fr.π⁆) ψ
    rw [hY] at hk
    exact hk.trans (Set.ext_iff.mp (hComp ζ t δ ctx.hK ctx.hζ ctx.ht c hc) ψ)
  · ext ψ
    have hT : (⊤ : Subgroup ↥H).map H.subtype = H := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hT' : (⊤ : Subgroup ↥H).map ctx.fr.π = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr ctx.fr.surj
    have hk := key ⊤ ψ
    rw [hT, hT'] at hk
    exact hk.trans (Set.ext_iff.mp (hAmb ζ t δ ctx.hK ctx.hζ ctx.ht) ψ)

theorem orthPlacement_of_pieces (hD : OrthInnerDiagData) (hF : ExistsOrthFrame)
    (hLe : OrthEleH) (hOcc : OrthComponentOccursIff) (hCent : OrthComponentCentEq)
    (hIn : OrthComponentInsideEq) (hMk : OrthComponentMarked)
    (hCov : CoverComponents.AutomizerCoverEq) (hAmb : OrthAmbientTorusAut)
    (hComp : OrthComponentTorusAut) (hQ : OrthIsQuasisimpleYcode)
    {G : Type} [Group G] [Finite G] {H E : Subgroup G} {t : ℕ} {δ : Fin 2}
    (hInn : GGInnerDiagOnLabel (fun _ lab => lab = planeAmbientLabel (.orthogonal δ) t) 3 E H)
    (hEab : IsElemAbelian 3 E) (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ 3 = 1 → g ∈ E)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) (hcard : 3 ^ 4 ≤ Nat.card E)
    (h4 : 4 ≤ t + δ.val) :
    Nonempty (Realization H E (planeEntry (.orthogonal δ) t)) := by
  obtain ⟨K, _, _, _, ζ, hEN, ⟨ctx⟩⟩ := orthCtx_of_pieces hD hF hLe hInn hEab hSC hC3 hcard h4
  obtain ⟨hN1, hN2⟩ := orthNormalizerEqs_of_pieces hCov hAmb hComp hQ ctx
  exact ⟨Realization.ofCore (orthRealizationCore hOcc hCent hIn hMk ctx)
    ⟨fun c hc => hN1 c hc.2, hN2⟩⟩

end

end CFSG.StandardType.GGQ2Frame.OrthPlacement
