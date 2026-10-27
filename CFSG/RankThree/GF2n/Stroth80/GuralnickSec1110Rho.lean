module

public import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110Lift
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group
public import CFSG.RankThree.GF2n.Stroth80.HeringSec11SiegelInstance
public import CFSG.RankThree.GF2n.Stroth80.GuralnickSec1110EbarSiegel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Kantor79 QuadraticMap Module
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

private theorem Ctx.exists_cmCommAct_factor (hc : Ctx M Q Z B)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) :
    ∃ ρX : ↥(Xbar M Q Z B) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
        ↥(cmComm M Q Z B K γ M₀ φ)),
      ∀ s, ρX (xbarHToXbar M Q Z B s) = cmCommAct hc φ s := by
  have hker : (xbarHToXbar M Q Z B).ker ≤ (cmCommAct hc φ).ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    have hQ : ((s : ↥(H0 M Z)) : G) ∈ Q := (xbarHToXbar_eq_one_iff s).mp hs
    have hφ1 : φ (s : ↥(H0 M Z)) = 1 := (hφk (s : ↥(H0 M Z))).mpr hQ
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    rw [coe_cmCommAct, hφ1]
    rfl
  exact ⟨MonoidHom.liftOfSurjective (xbarHToXbar M Q Z B) (xbarHToXbar_surjective hc)
      ⟨cmCommAct hc φ, hker⟩, fun s =>
    MonoidHom.liftOfRightInverse_comp_apply (xbarHToXbar M Q Z B) _ _
      ⟨cmCommAct hc φ, hker⟩ s⟩

private theorem Ctx.exists_longRoot_slAct_transvection (hc : Ctx M Q Z B)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e)
    {m : ℕ} {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)}
    {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
    (hσ₀ : ∀ g, CFSG.ComponentClassification.RankTwoClassical.modelHom e (σ₀ g) = proj m K g)
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s) :
    ∃ t₀ : SL(m, K), IsTransvection t₀ ∧ IsLongRootElement (cmCommQf B φ) (ρ t₀) ∧
      Module.finrank K ↥(movedSpace (ρ t₀)) = 2 ∧
      ∀ w ∈ movedSpace (ρ t₀), cmCommQf B φ w = 0 := by
  classical
  obtain ⟨a, ha, hA2⟩ := ha2
  let aM : ↥M := ⟨a, hc.LB_le_M ha⟩
  obtain ⟨t₀, ht₀, hσt₀⟩ := Ctx.exists_isTransvection_slHom_eq hc hσ₀ (a := aM) ha hA2
  obtain ⟨e₁, he₁class, he₁A2, he₁H0⟩ :=
    hc.exists_H0_rep_of_mem_Ebar (hc.mk_mem_Ebar ha hA2)
  have hq : (a : G)⁻¹ * (e₁ : G) ∈ Q := by
    have h := QuotientGroup.eq.mp he₁class.symm
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  have he₁LB : (e₁ : G) ∈ LB M Q B := by
    have h := (LB M Q B).mul_mem ha (show (a : G)⁻¹ * (e₁ : G) ∈ LB M Q B from
      (show Q ≤ LB M Q B from le_sup_left) hq)
    rwa [mul_inv_cancel_left] at h
  have he₁X : (QuotientGroup.mk e₁ : Mbar M Q) ∈ Xbar M Q Z B := by
    rw [he₁class]
    exact mk_mem_Xbar_of_LB M Q Z B aM ha hA2
  have he₁Pre : (e₁ : G) ∈ XbarPre M Q Z B :=
    (mem_XbarPre_iff hc he₁H0.1).mpr (by simpa using he₁X)
  let s : ↥(XbarH M Q Z B) :=
    ⟨⟨(e₁ : G), he₁H0⟩, (mem_XbarH_iff hc ⟨(e₁ : G), he₁H0⟩).mpr he₁Pre⟩
  have hxbar : xbarHToXbar M Q Z B s = σ₀ t₀ := by
    rw [hσt₀]
    apply Subtype.ext
    rw [coe_xbarHToXbar]
    exact he₁class
  have hρt₀ : ρ t₀ = cmCommAct hc φ s := hρ t₀ s hxbar
  have hKant := Ctx.cmComm_kantor_instance hc ⟨a, ha, hA2⟩ hD φ hφπ hφQ
  have hlong₀ : IsLongRootElement (cmCommQf B φ) (ρ t₀) := by
    rw [hρt₀]
    exact hKant.2.2.2.2 s he₁LB he₁A2
  have hmoved : Module.finrank K ↥(movedSpace (ρ t₀)) = 2 ∧
      ∀ w ∈ movedSpace (ρ t₀), cmCommQf B φ w = 0 := by
    rw [hρt₀]
    exact hc.cmCommAct_moved hD hD.card φ hφπ ⟨a, ha, hA2⟩ he₁LB he₁A2
  exact ⟨t₀, ht₀, hlong₀, hmoved⟩

theorem Ctx.exists_slAct_cmComm (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) {m : ℕ} (hm : 3 ≤ m)
    {e : XbarMod M Q Z B ≃* StatedProj (StatedSL m K)} {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
    (hσ₀ : ∀ g, CFSG.ComponentClassification.RankTwoClassical.modelHom e (σ₀ g) = proj m K g) :
    ∃ ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ)),
      (∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
        ρ g = cmCommAct hc φ s) ∧
      (∀ g v, cmCommQf B φ (ρ g v) = cmCommQf B φ v) ∧
      (∀ t : SL(m, K), IsTransvection t → IsLongRootElement (cmCommQf B φ) (ρ t)) ∧
      (∃ t₀ : SL(m, K), IsTransvection t₀ ∧ Module.finrank K ↥(movedSpace (ρ t₀)) = 2 ∧
        ∀ w ∈ movedSpace (ρ t₀), cmCommQf B φ w = 0) ∧
      commutatorSpace ρ.range = ⊤ := by
  classical
  obtain ⟨ρX, hρX⟩ := hc.exists_cmCommAct_factor φ hφk
  let ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K]
      ↥(cmComm M Q Z B K γ M₀ φ)) := ρX.comp σ₀
  have hcompat : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s := by
    intro g s hs
    change ρX (σ₀ g) = cmCommAct hc φ s
    rw [← hs, hρX s]
  have hisom : ∀ (g : SL(m, K)) (v : ↥(cmComm M Q Z B K γ M₀ φ)),
      cmCommQf B φ (ρ g v) = cmCommQf B φ v := by
    intro g v
    obtain ⟨s, hs⟩ := xbarHToXbar_surjective hc (σ₀ g)
    rw [hcompat g s hs]
    exact cmCommQf_cmCommAct hc φ hφQ s v
  have hKant := Ctx.cmComm_kantor_instance hc ha2 hD φ hφπ hφQ
  have hrangeρX : ρX.range = (cmCommAct hc φ).range := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨s, rfl⟩ := xbarHToXbar_surjective hc x
      exact ⟨s, (hρX s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨xbarHToXbar M Q Z B s, hρX s⟩
  have hρrange : ρ.range = (cmCommAct hc φ).range := by
    change (ρX.comp σ₀).range = (cmCommAct hc φ).range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (Ctx.slHom_Xbar_surjective hc hm hσ₀),
      Subgroup.map_top, hrangeρX]
  obtain ⟨t₀, ht₀, hlong₀, hmoved⟩ :=
    hc.exists_longRoot_slAct_transvection ha2 hD φ hφπ hφQ hσ₀ hcompat
  have hall : ∀ t : SL(m, K), IsTransvection t →
      IsLongRootElement (cmCommQf B φ) (ρ t) := by
    intro t ht
    obtain ⟨W, hW⟩ := exists_conj_of_isTransvection ht₀ ht
    have hρt : ρ t = ρ W * ρ t₀ * (ρ W)⁻¹ := by
      rw [← hW, map_mul, map_mul, map_inv]
    have hgW : ρ W ∈ TauCeti.QuadraticMap.orthogonalGroup (cmCommQf B φ) :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (hisom W)
    rw [hρt]
    exact IsLongRootElement.conj hgW hlong₀
  refine ⟨ρ, hcompat, hisom, hall, ⟨t₀, ht₀, hmoved⟩, ?_⟩
  rw [hρrange]
  exact hKant.2.2.2.1

end CFSG.RankThree.GF2n.Stroth80
