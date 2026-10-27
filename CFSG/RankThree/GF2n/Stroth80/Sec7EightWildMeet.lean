module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EightWildWitness
public import CFSG.RankThree.GF2n.Stroth80.Sec7HsetCard8

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem step76EightWildMeet_of_inputs (h34 : Stroth34Statement) (h71 : Stroth71Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) :
    Step76EightWildMeetStatement := by
  intro G _ _ M Q Z B hc n t hs hno h4 Z0 hZ0 g hgM s hs1 hs2 hs3 hV y hy
  classical
  haveI := hc.normal_Q_in_M
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, -, -, -, -⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  obtain ⟨hHcard, hUcard⟩ := sec7_Hset_card8 h34 h310chi hc hs h4 M₀ ρ b hS ψ hψ hrange
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hd : g⁻¹ * y * g ∈ LB M Q B ⊓ hc.CN t := mem_conjSubgroup.mp hy
  have hyM : y ∈ M := by
    have h3 := M.mul_mem (M.mul_mem hgM (hc.LB_le_M hd.1)) (M.inv_mem hgM)
    simpa [mul_assoc] using h3
  have hc' := hc.conj_of_mem hgM
  have hyL : y ∈ LB M Q (conjSubgroup g B) := by
    rw [hc.LB_conj hgM]
    exact mem_conjSubgroup.mpr hd.1
  have hcommQB : ∀ v ∈ Vt M (LB M Q B) B Z t,
      ⁅y, v⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup g B) := by
    intro v hv
    refine ⟨sec7_D1_comm_mem h71 h310chi h52a hA hc hs hno hgM hs1 hs2 hy v hv, ?_⟩
    have hvN : v ∈ Subgroup.normalizer ((conjSubgroup g B : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun b' hb' => ?_
      have hb0 : g⁻¹ * b' * g ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht (mem_conjSubgroup.mp hb')
      have hW := sec7_pair_mem_W h71 h310chi hc hs hno hgM hs1 hs2 _ hb0
      have e : g * (g⁻¹ * b' * g) * g⁻¹ = b' := by group
      rw [e] at hW
      have h1 := Subgroup.mem_centralizer_iff.mp hW.2 v hv
      have e2 : v * b' * v⁻¹ = b' := by
        rw [h1]
        group
      rw [e2]
      exact hb'
    have h1 := Ctx.comm_mem_inf_QB_of_mem_normalizer hc' (hVQ hv) hvN hyL
    rw [← commutatorElement_inv]
    exact (QB (conjSubgroup g B)).inv_mem h1.2
  let S' : Subgroup G :=
    (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup g B)) ⊔ Z
  let ν : M₀.E ≃+ M₀.E := (ρ (QuotientGroup.mk ⟨y, hyM⟩)).toAdd
  have hrange : ∀ u : ↥(hc.VtSub hS.model t), ν (u : M₀.E) - (u : M₀.E) ∈ M₀.img S' := by
    intro u
    obtain ⟨v, hvV, hvQ, hv⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp u.2)
    have hyvQ : y * v * y⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hyM).1 v hvQ
    have h1 : M₀.π (y * v * y⁻¹) = ν (M₀.π v) := hS.conj ⟨y, hyM⟩ v hvQ
    have h2 : M₀.π ⁅y, v⁆ = ν (M₀.π v) - M₀.π v := by
      have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := rfl
      rw [e, M₀.π_mul _ hyvQ _ (Q.inv_mem hvQ), M₀.pi_inv hvQ, ← h1, sub_eq_add_neg]
    have hcQ : ⁅y, v⁆ ∈ Q := by
      have e : ⁅y, v⁆ = (y * v * y⁻¹) * v⁻¹ := rfl
      rw [e]
      exact Q.mul_mem hyvQ (Q.inv_mem hvQ)
    rw [← hv, ← h2]
    exact M₀.pi_mem_img (Subgroup.mem_sup_left (hcommQB v hvV)) hcQ
  have hS'card : Nat.card (M₀.img S') = Nat.card K ^ 7 := by
    have hS'eq : S' = conjSubgroup g ((Vt M (LB M Q B) B Z t ⊓ QB B) ⊔ Z) := by
      show (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ QB (conjSubgroup g B)) ⊔ Z = _
      rw [conjSubgroup_sup', conjSubgroup_inf, QB_conj, hc.conj_Z_eq hgM]
    rw [hS'eq, sec7_card_img_conj hc M₀ ρ b hS hgM le_sup_right]
    exact hHcard
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hnotinj : ¬ Function.Injective
      (fun u : ↥(hc.VtSub hS.model t) =>
        (⟨ν (u : M₀.E) - (u : M₀.E), hrange u⟩ : ↥(M₀.img S'))) := by
    intro hinj
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hS'card, hUcard] at h1
    have hq : 1 < Nat.card K := Finite.one_lt_card
    exact absurd h1 (not_le.mpr (Nat.pow_lt_pow_right hq (by norm_num)))
  simp only [Function.Injective, not_forall] at hnotinj
  obtain ⟨u₁, u₂, hu12, hne⟩ := hnotinj
  have hfix : ν ((u₁ : M₀.E) - (u₂ : M₀.E)) = (u₁ : M₀.E) - (u₂ : M₀.E) := by
    have h := congrArg Subtype.val hu12
    rw [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  have hu0 : (u₁ : M₀.E) - (u₂ : M₀.E) ≠ 0 := by
    intro h0
    exact hne (Subtype.ext (sub_eq_zero.mp h0))
  have hmemU : (u₁ : M₀.E) - (u₂ : M₀.E) ∈ hc.VtSub hS.model t :=
    (hc.VtSub hS.model t).sub_mem u₁.2 u₂.2
  obtain ⟨v₀, hv₀V, hv₀Q, hv₀⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hmemU)
  have hv₀Z : v₀ ∉ Z := by
    intro hz
    exact hu0 (hv₀.symm.trans ((M₀.π_ker v₀ hv₀Q).mpr hz))
  have hyv₀Q : y * v₀ * y⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hyM).1 v₀ hv₀Q
  have hcomm : ⁅y, v₀⁆ ∈ Z := by
    have h1 : M₀.π (y * v₀ * y⁻¹) = ν (M₀.π v₀) := hS.conj ⟨y, hyM⟩ v₀ hv₀Q
    have h2 : M₀.π ⁅y, v₀⁆ = 0 := by
      have e : ⁅y, v₀⁆ = (y * v₀ * y⁻¹) * v₀⁻¹ := rfl
      rw [e, M₀.π_mul _ hyv₀Q _ (Q.inv_mem hv₀Q), M₀.pi_inv hv₀Q, h1, hv₀, hfix, sub_eq_add_neg]
      exact add_neg_cancel _
    have hcQ : ⁅y, v₀⁆ ∈ Q := by
      have e : ⁅y, v₀⁆ = (y * v₀ * y⁻¹) * v₀⁻¹ := rfl
      rw [e]
      exact Q.mul_mem hyv₀Q (Q.inv_mem hv₀Q)
    exact (M₀.π_ker _ hcQ).mp h2
  intro hmeet
  have hwV : y * v₀ * y⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    have e : y * v₀ * y⁻¹ = ⁅y, v₀⁆ * v₀ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hZV hcomm) hv₀V
  have hwy : y * v₀ * y⁻¹ ∈ conjSubgroup y (Vt M (LB M Q B) B Z t) := by
    rw [mem_conjSubgroup]
    have e : y⁻¹ * (y * v₀ * y⁻¹) * y = v₀ := by group
    rw [e]
    exact hv₀V
  have hwZ : y * v₀ * y⁻¹ ∈ Z := by
    rw [← hmeet]
    exact ⟨hwV, hwy⟩
  apply hv₀Z
  have e : v₀ = ⁅y, v₀⁆⁻¹ * (y * v₀ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Z.mul_mem (Z.inv_mem hcomm) hwZ

end CFSG.RankThree.GF2n.Stroth80
