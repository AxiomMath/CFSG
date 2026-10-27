module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec11SiegelInstance
public import CFSG.RankThree.GF2n.Stroth80.HeringSec117Module
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.exists_rho_factor_group {B : Subgroup G} (hc : Ctx M Q Z B) {T : Type} [Group T]
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)) (Θ : ↥(XbarH M Q Z B) →* T)
    (hΘ : Function.Surjective Θ) (hker : ∀ s, Θ s = 1 → φ (s : ↥(H0 M Z)) = 1) :
    ∃ ρV : T →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)),
      ∀ s, ρV (Θ s) = cmCommAct hc φ s := by
  have hk : Θ.ker ≤ (cmCommAct hc φ).ker := by
    intro s hs
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [coe_cmCommAct, hker s hs]
    rfl
  exact ⟨MonoidHom.liftOfSurjective Θ hΘ ⟨cmCommAct hc φ, hk⟩, fun s =>
    MonoidHom.liftOfRightInverse_comp_apply Θ _ _ ⟨cmCommAct hc φ, hk⟩ s⟩

variable [Finite K] [CharP K 2]

theorem Ctx.exists_cmComm_action_of_mulEquiv {B : Subgroup G} (hc : Ctx M Q Z B)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (h : ↥(H0 M Z)) (q : G), q ∈ Q → M₀.π ((h : G) * q * (h : G)⁻¹) = φ h (M₀.π q))
    (hφk : ∀ h : ↥(H0 M Z), φ h = 1 ↔ (h : G) ∈ Q)
    (hφQ : ∀ (h : ↥(H0 M Z)) e, M₀.Qf (φ h e) = M₀.Qf e) {T : Type} [Group T]
    (ψ : ↥(Xbar M Q Z B) ≃* T) :
    ∃ ρV : T →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)),
      Function.Injective ρV ∧ (∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v) ∧
      (∀ v, (∀ g, ρV g v = v) → v = 0) ∧ commutatorSpace ρV.range = ⊤ ∧
      (∀ s : ↥(XbarH M Q Z B), ((s : ↥(H0 M Z)) : G) ∈ LB M Q B →
        IsA2 Q Z ((s : ↥(H0 M Z)) : G) →
          IsLongRootElement (cmCommQf B φ) (ρV (ψ (xbarHToXbar M Q Z B s)))) ∧
      ∀ s : ↥(XbarH M Q Z B), ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s := by
  set Θ : ↥(XbarH M Q Z B) →* T := ψ.toMonoidHom.comp (xbarHToXbar M Q Z B) with hΘ
  have hΘs : Function.Surjective Θ := ψ.surjective.comp (xbarHToXbar_surjective hc)
  have hΘk : ∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q := fun s => by
    rw [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      xbarHToXbar_eq_one_iff]
  obtain ⟨ρV, hρV⟩ := hc.exists_rho_factor_group φ Θ hΘs
    (fun s hs => (hφk (s : ↥(H0 M Z))).mpr ((hΘk s).mp hs))
  obtain ⟨-, hiso, hfix, hcomm, hsieg⟩ := hc.cmComm_kantor_instance ha2 hD φ hφπ hφQ
  have hρQ : ∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v := fun g v => by
    obtain ⟨s, rfl⟩ := hΘs g
    rw [hρV s]
    exact hiso s v
  have hρinj : Function.Injective ρV := by
    refine (injective_iff_map_eq_one ρV).mpr fun g hg => ?_
    obtain ⟨s, rfl⟩ := hΘs g
    rw [hρV s] at hg
    exact (hΘk s).mpr (hc.mem_Q_of_cmCommAct_eq_one hD φ hφπ hφk hφQ hg)
  have hrange : ρV.range = (cmCommAct hc φ).range := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨s, rfl⟩ := hΘs g
      exact ⟨s, (hρV s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Θ s, hρV s⟩
  refine ⟨ρV, hρinj, hρQ, fun v hv => hfix v fun s => ?_, by rw [hrange]; exact hcomm,
    fun s hsL hsA => ?_, hρV⟩
  · rw [← hρV s]
    exact hv (Θ s)
  · have : ρV (ψ (xbarHToXbar M Q Z B s)) = cmCommAct hc φ s := hρV s
    rw [this]
    exact hsieg s hsL hsA

end CFSG.RankThree.GF2n.Stroth80
