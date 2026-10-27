module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
public import CFSG.RankThree.GF2n.Stroth80.Satz5Core
import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group
import CFSG.RankThree.GF2n.Stroth80.HeringSec117Module
import CFSG.RankThree.GF2n.Stroth80.Satz5Stroth
import CFSG.RankThree.GF2n.Stroth80.Sec118RT1Form
import CFSG.RankThree.GF2n.Stroth80.Sec119OmegaOrder
import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Basic
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal QuadraticMap Module
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.action_eq_eichler_of_cmCommAct (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (s : ↥(XbarH M Q Z B)) {u w : ↥(cmComm M Q Z B K γ M₀ φ)}
    (hu : cmCommQf B φ u = 0) (huw : polar (cmCommQf B φ) u w = 0)
    (hs : cmCommAct hc φ s = eichler (cmCommQf B φ) u w) :
    φ (s : ↥(H0 M Z)) = eichler M₀.toQuadraticForm (u : M₀.E) (w : M₀.E) := by
  have hu' : M₀.toQuadraticForm (u : M₀.E) = 0 := hu
  have huw' : polar M₀.toQuadraticForm (u : M₀.E) (w : M₀.E) = 0 := by
    rw [Tim79.QuadModel.polar_toQuadraticForm, ← polar_cmCommQf]
    exact huw
  refine LinearEquiv.ext fun e => ?_
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Submodule.mem_sup.mp
    ((hc.isCompl_cmComm_orthogonal hD φ hφπ).sup_eq_top ▸ Submodule.mem_top (x := e))
  have hB : ∀ a : ↥(cmComm M Q Z B K γ M₀ φ), polar M₀.toQuadraticForm e₂ (a : M₀.E) = 0 := by
    intro a
    have h := he₂ (a : M₀.E) a.2
    rw [Tim79.QuadModel.polar_toQuadraticForm, Tim79.QuadModel.B_comm, h, neg_zero]
  have h₁ : φ (s : ↥(H0 M Z)) e₁ = eichler M₀.toQuadraticForm (u : M₀.E) (w : M₀.E) e₁ := by
    have h : φ (s : ↥(H0 M Z)) e₁ =
        ((eichler (cmCommQf B φ) u w ⟨e₁, he₁⟩ : ↥(cmComm M Q Z B K γ M₀ φ)) : M₀.E) := by
      rw [← hs]
      rfl
    rw [h, eichler_apply hu huw, eichler_apply hu' huw']
    simp [polar_cmCommQf, cmCommQf_apply, Tim79.QuadModel.polar_toQuadraticForm,
      Tim79.QuadModel.toQuadraticForm_apply]
  rw [map_add, map_add, h₁, hc.action_fixes_orthogonal_of_mem_XbarH hD φ hφπ s he₂,
    eichler_apply_of_polar_eq_zero (hB u) (hB w)]

theorem Ctx.card_xbarMod_le_card_range_cmCommAct (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) :
    Nat.card (XbarMod M Q Z B) ≤ Nat.card (cmCommAct hc φ).range := by
  have hker : (cmCommAct hc φ).ker ≤ (xbarHToXbar M Q Z B).ker := fun s hs =>
    MonoidHom.mem_ker.mpr ((xbarHToXbar_eq_one_iff s).mpr
      (hc.mem_Q_of_cmCommAct_eq_one hD φ hφπ hφk hφQ (MonoidHom.mem_ker.mp hs)))
  calc Nat.card (XbarMod M Q Z B) ≤ Nat.card (Xbar M Q Z B) :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    _ = Nat.card (xbarHToXbar M Q Z B).range := by
        rw [MonoidHom.range_eq_top.mpr (xbarHToXbar_surjective hc), Subgroup.card_top]
    _ = (xbarHToXbar M Q Z B).ker.index := (Subgroup.index_ker _).symm
    _ ≤ (cmCommAct hc φ).ker.index := Subgroup.index_antitone hker
    _ = Nat.card (cmCommAct hc φ).range := Subgroup.index_ker _

theorem Ctx.exists_induces_eichler (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hE : elementaryGroup (cmCommQf B φ) ≤ (cmCommAct hc φ).range)
    {u w : ↥(cmComm M Q Z B K γ M₀ φ)} (hu : cmCommQf B φ u = 0)
    (huw : polar (cmCommQf B φ) u w = 0) :
    ∃ a ∈ XbarPre M Q Z B,
      Satz5.Induces M₀ a (eichler M₀.toQuadraticForm (u : M₀.E) (w : M₀.E)) := by
  obtain ⟨s, hs⟩ := hE (eichler_mem_elementaryGroup _ u w)
  refine ⟨((s : ↥(H0 M Z)) : G), (mem_XbarH_iff hc _).mp s.2, fun x hx => ?_⟩
  rw [hφπ (s : ↥(H0 M Z)) x hx, hc.action_eq_eichler_of_cmCommAct hD φ hφπ s hu huw hs]

private theorem Ctx.false_of_orth_hypPairs [CharP K 2] (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hE : elementaryGroup (cmCommQf B φ) ≤ (cmCommAct hc φ).range)
    (P₁ P₂ : HypPair (cmCommQf B φ)) (hP : P₁.Orth P₂) : False := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  obtain ⟨hnorm, hcent, hfaith⟩ := hc.hyp.satz5_conditions (M₀ := M₀) hD.reg (XbarPre_le_H0 hc)
  have hK : 2 < Nat.card K := by
    rw [hD.card]
    have := hc.hyp.q4
    omega
  obtain ⟨ν, hν0, hν1⟩ := Satz5.exists_ne_zero_one hK
  have hB := fun x y : ↥(cmComm M Q Z B K γ M₀ φ) => (polar_cmCommQf B φ x y).symm
  have S : Satz5.Setting M₀ (XbarPre M Q Z B) (P₁.e : M₀.E) (P₂.e : M₀.E) (P₁.f : M₀.E)
      (P₂.f : M₀.E) :=
    ⟨hD.reg, h2, (hB _ _).trans P₁.polar_ef, (hB _ _).trans P₂.polar_ef, (hB _ _).trans hP.ef,
      (hB _ _).trans ((polar_comm _ _ _).trans hP.fe), (hB _ _).trans hP.ee,
      (hB _ _).trans hP.ff, hnorm, hcent, hfaith⟩
  refine S.false_of_rootLifts hν0 hν1 (fun l _ => ?_) (fun l _ => ?_)
  · obtain ⟨a, ha, hind⟩ := hc.exists_induces_eichler hD φ hφπ hE (u := P₂.e) (w := l • P₁.f)
      P₂.Q_e (by rw [polar_smul_right, polar_comm, hP.fe, smul_zero])
    refine ⟨a, ha, fun x hx => ?_⟩
    rw [hind x hx, S.rootA_eq_eichler P₂.Q_e P₁.Q_f l, Submodule.coe_smul]
  · obtain ⟨b, hb, hind⟩ := hc.exists_induces_eichler hD φ hφπ hE (u := P₂.e) (w := l • P₁.e)
      P₂.Q_e (by rw [polar_smul_right, polar_comm, hP.ee, smul_zero])
    refine ⟨b, hb, fun x hx => ?_⟩
    rw [hind x hx, S.rootB_eq_eichler P₂.Q_e P₁.Q_e l, Submodule.coe_smul]

theorem Ctx.false_of_card_xbarMod_ge (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hφk : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    (hφQ : ∀ (g : ↥(H0 M Z)) e, M₀.Qf (φ g e) = M₀.Qf e) {m : ℕ} (hm : 3 ≤ m)
    (hdim : finrank K ↥(cmComm M Q Z B K γ M₀ φ) = 2 * m)
    (hcard : (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) ≤
        Nat.card (XbarMod M Q Z B)) : False := by
  have : Module.Finite K M₀.E := M₀.fin
  obtain ⟨a, -, ha, -⟩ := hc.hyp.cp
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hD.card.trans ha)
  have hnd : (polarBilin (cmCommQf B φ)).Nondegenerate :=
    SiegelRT1.nondegenerate_polarBilin (hc.cmCommQf_nondegenerate hD φ hφπ)
  have hO : (cmCommAct hc φ).range ≤ TauCeti.QuadraticMap.orthogonalGroup (cmCommQf B φ) := by
    rintro _ ⟨s, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (cmCommQf_cmCommAct hc φ hφQ s)
  have hρ : (Nat.card (XbarMod M Q Z B) : ℤ) ≤ Nat.card (cmCommAct hc φ).range := by
    exact_mod_cast hc.card_xbarMod_le_card_range_cmCommAct hD φ hφπ hφk hφQ
  have hE := elementaryGroup_le_of_card_ge hnd hm hdim hO (hcard.trans hρ)
  obtain ⟨P₁, P₂, hP⟩ := exists_orth_hypPairs_of_finrank hnd hm hdim
  exact hc.false_of_orth_hypPairs hD φ hφπ hE P₁ P₂ hP

end CFSG.RankThree.GF2n.Stroth80
