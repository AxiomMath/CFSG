module

public import CFSG.RankThree.GF2n.Tim79a34BigIdentLocal
public import CFSG.RankThree.GF2n.Tim79a34BigEpsTwo

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section BigIdentQP

variable {G : Type} [Group G]

theorem bigIdent_mbar_commute {M Q : Subgroup G} (hQ : Q = inSubgroup (pCore 2) M) {x y : ↥M}
    (h : ⁅(x : G), (y : G)⁆ ∈ Q) : (x : Mbar M) * (y : Mbar M) = (y : Mbar M) * (x : Mbar M) := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem,
    Subgroup.mem_subgroupOf]
  have e : (((x * y) / (y * x) : ↥M) : G) = ⁅(x : G), (y : G)⁆ := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv,
      commutatorElement_def]
    group
  rw [e, ← hQ]
  exact h

end BigIdentQP

theorem bigIdent_exists_mul_CQ (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) (G : Type) [Group G] [Finite G]
    (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H) {B : Subgroup G}
    (hBW : B ≤ wOf V H) {g : G} (hg : g ∈ M)
    (hcomm : ∀ b ∈ B, ∀ w ∈ wOf V H, ⁅g * b * g⁻¹, w⁆ = 1) {y : G} (hy : y ∈ conjSubgroup g B) :
    ∃ w ∈ wOf V H, ∃ q ∈ Q, (∀ w' ∈ wOf V H, q * w' = w' * q) ∧ y = w * q := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f₂, Φ, ψ, -, hf₂, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ :=
    hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨hiff, -, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf₂ Φ ψ hNat a T ha hTT hTV
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hy' : g⁻¹ * y * g ∈ B := mem_conjSubgroup.mp hy
  have hbW : g⁻¹ * y * g ∈ wOf V H := hBW hy'
  have hyeq : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  have hyM : y ∈ M := by
    rw [hyeq]
    exact M.mul_mem (M.mul_mem hg (hWM hbW)) (M.inv_mem hg)
  have hycW : ∀ w ∈ wOf V H, y * w = w * y := fun w hw => by
    have := hcomm _ hy' w hw
    rw [← hyeq] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hy2 : y * y = 1 := by
    have h1 := hc.wOf_isElemAbelian.mul_self_eq_one hbW
    calc y * y = g * ((g⁻¹ * y * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hR : ((⟨y, hyM⟩ : ↥M) : Mbar M) ∈ Subgroup.centralizer (RbarM M V H : Set (Mbar M)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro rb ⟨r, hr, rfl⟩
    have hrXC := Subgroup.mem_subgroupOf.mp hr
    obtain ⟨hrX, hrC⟩ := Subgroup.mem_inf.mp hrXC
    refine bigIdent_mbar_commute hQM ?_
    have hW1 := bigIdent_comm_mem_W hZ hN G M V Q P H hH hyM hycW hrX
    have hW2 : ⁅(r : G), y⁆ ∈ wOf V H := by
      rw [← commutatorElement_inv]
      exact (wOf V H).inv_mem hW1
    have hV : ∀ v ∈ V, v * ⁅(r : G), y⁆ = ⁅(r : G), y⁆ * v := by
      intro v hv
      have hvr : v * (r : G) = (r : G) * v := Subgroup.mem_centralizer_iff.mp hrC v hv
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
        rw [hc.normalizer_eq]
        exact hyM
      have hv'' : y⁻¹ * v * y ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (V : Set G)).inv_mem hyN)
          v).mp hv
        simpa using this
      have hv''r : (y⁻¹ * v * y) * (r : G) = (r : G) * (y⁻¹ * v * y) :=
        Subgroup.mem_centralizer_iff.mp hrC _ hv''
      have hv''r' : (y⁻¹ * v * y) * (r : G)⁻¹ = (r : G)⁻¹ * (y⁻¹ * v * y) := by
        calc (y⁻¹ * v * y) * (r : G)⁻¹
            = (r : G)⁻¹ * ((r : G) * (y⁻¹ * v * y)) * (r : G)⁻¹ := by group
          _ = (r : G)⁻¹ * ((y⁻¹ * v * y) * (r : G)) * (r : G)⁻¹ := by rw [hv''r]
          _ = (r : G)⁻¹ * (y⁻¹ * v * y) := by group
      calc v * ⁅(r : G), y⁆ = (v * (r : G)) * y * (r : G)⁻¹ * y⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = ((r : G) * v) * y * (r : G)⁻¹ * y⁻¹ := by rw [hvr]
        _ = (r : G) * y * ((y⁻¹ * v * y) * (r : G)⁻¹) * y⁻¹ := by group
        _ = (r : G) * y * ((r : G)⁻¹ * (y⁻¹ * v * y)) * y⁻¹ := by rw [hv''r']
        _ = ⁅(r : G), y⁆ * v := by simp only [commutatorElement_def]; group
    obtain ⟨β, hβ⟩ := exists_psiElt ψ hW2
    have hs : CaseM.spForm a β = 0 := by
      refine bigRW_spForm_eq_zero_of_commute hc hNat ha hTT hTV (w := β) fun v hv => ?_
      have := hV v hv
      rw [← hβ] at this
      exact this
    have hPmem : psiElt ψ β ∈ P := (hiff β).mpr hs
    show ⁅(r : G), y⁆ ∈ Q
    rw [← hβ]
    exact hc.P_le_Q hPmem
  have hWbar : ((⟨y, hyM⟩ : ↥M) : Mbar M) ∈ Subgroup.centralizer (WbarM M V H : Set (Mbar M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro wb hwb
    obtain ⟨w, hw, rfl⟩ := mem_WbarM_iff.mp hwb
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hycW _ hw).symm
  have hord : ∃ k : ℕ, ((⟨y, hyM⟩ : ↥M) : Mbar M) ^ (2 ^ k) = 1 := by
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two, ← QuotientGroup.mk_mul]
    have : (⟨y, hyM⟩ * ⟨y, hyM⟩ : ↥M) = 1 := Subtype.ext hy2
    rw [this]
    rfl
  have hmem := bigEpsilonFaithfulTwoStatement_of_natural hZ hN hIW hγ G M V Q P H hH _
    (Subgroup.mem_inf.mpr ⟨hR, hWbar⟩) hord
  obtain ⟨w, hwW, hwy⟩ := mem_WbarM_iff.mp hmem
  have hq : ((w⁻¹ * ⟨y, hyM⟩ : ↥M) : G) ∈ inSubgroup (pCore 2) M := by
    have h1 := QuotientGroup.eq.mp hwy
    exact Subgroup.mem_subgroupOf.mp h1
  have hqe : ((w⁻¹ * ⟨y, hyM⟩ : ↥M) : G) = (w : G)⁻¹ * y := by simp
  rw [hqe, ← hQM] at hq
  refine ⟨(w : G), hwW, (w : G)⁻¹ * y, hq, fun w' hw' => ?_, by group⟩
  have h1 : ((w : G)⁻¹) * w' = w' * (w : G)⁻¹ := hc.wOf_comm ((wOf V H).inv_mem hwW) hw'
  calc (w : G)⁻¹ * y * w' = (w : G)⁻¹ * (y * w') := by group
    _ = (w : G)⁻¹ * (w' * y) := by rw [hycW w' hw']
    _ = ((w : G)⁻¹ * w') * y := by group
    _ = (w' * (w : G)⁻¹) * y := by rw [h1]
    _ = w' * ((w : G)⁻¹ * y) := by group

end CFSG.RankThree.GF2n.Tim79a
