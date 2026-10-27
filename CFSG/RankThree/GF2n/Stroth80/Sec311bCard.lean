module

public import CFSG.RankThree.GF2n.Stroth80.Sec311bNatData
public import CFSG.RankThree.GF2n.Stroth80.Sec311bCalc
public import CFSG.RankThree.GF2n.Stroth80.Sec311bWt
public import CFSG.RankThree.GF2n.Stroth80.Sec311bVt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.card_T_le (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {X : Subgroup (GL ι K)} (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (T : Subgroup G)
    (hT : ∀ x, x ∈ T ↔ x ∈ LB M Q B ∧ ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ Q) :
    Nat.card T ≤ Nat.card Q * Nat.card Z := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hchi := hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB h35 ht hs.notQ hnotQB
  let D := hc.natCommData ht hchi.1 hchi.2
  have hVR := hc.Rt_normalizes_Vt ht
  have htM : t ∈ M := hc.LB_le_M ht
  set V := Vt M (LB M Q B) B Z t with hV
  have hTL : ∀ τ ∈ T, τ ∈ LB M Q B := fun τ hτ => ((hT τ).mp hτ).1
  have hTR : ∀ τ ∈ T, ∀ r ∈ Rt M (LB M Q B) t, ⁅r, τ⁆ ∈ Q := fun τ hτ => ((hT τ).mp hτ).2
  have hTN : ∀ τ ∈ T, τ ∈ hc.CN t := fun τ hτ =>
    hc.T_le_CN ht hX φ hφ hker (hTL τ hτ) (hTR τ hτ)
  have hK1 : ∀ τ ∈ T, ∀ w ∈ Wt Q V, ⁅τ, w⁆ ∈ Z := fun τ hτ w hw =>
    hc.comm_T_Wt_mem_Z h35 ht hnotQB (hTL τ hτ) (hTR τ hτ) hw
  have hK2 : ∀ τ ∈ T, ∀ y ∈ Q, ⁅y, τ⁆ ∈ V := by
    intro τ hτ y hy
    have := hc.comm_T_Q_mem_Vt ht (hTL τ hτ) (hK1 τ hτ) hy
    rw [← commutatorElement_inv]
    exact V.inv_mem this
  have hK3 : ∀ (τ : G) (hτ : τ ∈ T), ∃ κ : K, ∀ y : ↥Q,
      secVec ψ ⟨⁅(y : G), τ⁆, hK2 τ hτ y y.2⟩ = κ • kapVec D ψ y := by
    intro τ hτ
    refine exists_scalar_of_equivariant D ψ hX φ hφ hψ hVR
      (fun y => secVec ψ ⟨⁅(y : G), τ⁆, hK2 τ hτ y y.2⟩) ?_ ?_ ?_
    · intro y y'
      exact D.secVec_comm_mul ψ (hK2 τ hτ) y y'
    · intro y hy
      have hyW : (y : G) ∈ Wt Q V := by
        rw [hchi.2]
        refine (hc.mem_Q1_iff htM).mpr ⟨y.2, ?_⟩
        rw [← commutatorElement_inv]
        exact Z.inv_mem hy
      have h1 := hK1 τ hτ y hyW
      show secVec ψ _ = 0
      rw [secVec_eq_zero_iff]
      show ⁅(y : G), τ⁆ ∈ Z
      rw [← commutatorElement_inv]
      exact Z.inv_mem h1
    · intro r y
      exact D.secVec_comm_conj ψ hψ (hK2 τ hτ) (hTR τ hτ) r y
  have hTQ : Q ≤ T := fun x hx => (hT x).mpr ⟨sec39_Q_le_LB hx, fun r hr => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (hc.Rt_le_M t hr)) x).mp hx) (Q.inv_mem hx)⟩
  let δ : ↥T → ↥Q → (ι → K) := fun τ y => secVec ψ ⟨⁅(y : G), (τ : G)⁆, hK2 τ τ.2 y y.2⟩
  let Δ : ↥T →* Multiplicative (↥Q → (ι → K)) :=
    { toFun := fun τ => Multiplicative.ofAdd (δ τ)
      map_one' := by
        refine congrArg Multiplicative.ofAdd (funext fun y => ?_)
        show secVec ψ _ = 0
        rw [secVec_eq_zero_iff]
        show ⁅(y : G), ((1 : ↥T) : G)⁆ ∈ Z
        rw [show ⁅(y : G), ((1 : ↥T) : G)⁆ = 1 by simp [commutatorElement_def]]
        exact Z.one_mem
      map_mul' := fun τ τ' => by
        show Multiplicative.ofAdd (δ (τ * τ')) =
          Multiplicative.ofAdd (δ τ) * Multiplicative.ofAdd (δ τ')
        rw [← ofAdd_add]
        refine congrArg Multiplicative.ofAdd (funext fun y => ?_)
        exact D.secVec_comm_mul_right ψ (hK2 τ τ.2) (hK2 τ' τ'.2) (hK2 (τ * τ') (τ * τ').2)
          (fun v hv => (Ctx.mem_CN.mp (hTN τ τ.2)).2 v hv) y }
  have hΔ : ∀ τ : ↥T, ∀ y : ↥Q, Multiplicative.toAdd (Δ τ) y =
      secVec ψ ⟨⁅(y : G), (τ : G)⁆, hK2 τ τ.2 y y.2⟩ := fun τ y => rfl
  have hkerΔ : Δ.ker = Q.subgroupOf T := by
    ext τ
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have hz : ∀ y ∈ Q, ⁅(τ : G), y⁆ ∈ Z := by
        intro y hy
        have h2 := congrFun (congrArg Multiplicative.toAdd h1) ⟨y, hy⟩
        rw [hΔ] at h2
        have h3 : ⁅y, (τ : G)⁆ ∈ Z := (secVec_eq_zero_iff ψ _).mp h2
        rw [← commutatorElement_inv]
        exact Z.inv_mem h3
      exact hc.hyp.centralizer_Qt _ (hc.LB_le_M (hTL τ τ.2)) hz
    · intro hτQ
      refine congrArg Multiplicative.ofAdd (funext fun y => ?_)
      show secVec ψ _ = 0
      rw [secVec_eq_zero_iff]
      exact D.comm_Z y y.2 τ hτQ
  have hrange : Nat.card Δ.range ≤ Nat.card K := by
    let gAdd : K →+ (↥Q → (ι → K)) :=
      { toFun := fun κ y => κ • kapVec D ψ y
        map_zero' := by funext y; simp
        map_add' := fun a b => by funext y; simp [add_smul] }
    let g : Multiplicative K →* Multiplicative (↥Q → (ι → K)) := AddMonoidHom.toMultiplicative gAdd
    have hle : Δ.range ≤ g.range := by
      rintro _ ⟨τ, rfl⟩
      obtain ⟨κ, hκ⟩ := hK3 τ τ.2
      refine ⟨Multiplicative.ofAdd κ, ?_⟩
      refine congrArg Multiplicative.ofAdd (funext fun y => ?_)
      exact (hκ y).symm
    calc Nat.card Δ.range ≤ Nat.card g.range := Subgroup.card_le_of_le hle
      _ ≤ Nat.card (Multiplicative K) :=
        Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective g)
      _ = Nat.card K := rfl
  have hcardT : Nat.card T = Nat.card Δ.range * Nat.card Δ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Δ.ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange Δ).toEquiv
  have hkerQ : Nat.card Δ.ker = Nat.card Q := by
    rw [hkerΔ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv
  rw [hcardT, hkerQ, mul_comm]
  calc Nat.card Q * Nat.card Δ.range ≤ Nat.card Q * Nat.card K := Nat.mul_le_mul_left _ hrange
    _ = Nat.card Q * Nat.card Z := by rw [hK]


theorem stroth311bCard_of_34 (h34 : Stroth34Statement) (h310 : Stroth310Statement) :
    Stroth311bCardStatement := by
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ hR hnotSL T hT
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := fun hV =>
    hnotSL (stroth310SLBranch_of_34 h34 G M Q Z B hc n t hs hR hV)
  obtain ⟨K, fK, finK, hcp, hK, ι, fι, dι, nι, X, φ, hX, hφ, hker, hn', ψ, hψ, -⟩ :=
    hc.exists_nat_data h34 h310 hs hR hnotSL
  exact hc.card_T_le h34 hs hnotQB hK hX φ hφ hker ψ hψ T hT

end CFSG.RankThree.GF2n.Stroth80
