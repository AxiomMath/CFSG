module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Transfer
public import CFSG.Quasithin.Vol2.GoldschmidtF48RigDef

public section

namespace CFSG.Quasithin.H13.F431.F48Rig

open CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.Quasithin.H13.F431.F45 CFSG.Open

universe u w x v

variable {S : LieSetting.{u, w}} {X : Type x} [Group X] {V : Type v} [MulAction X V]
  {Φ : X →* S.ι.G0} {ΓM : SimpleGraph V} {v₁ v₂ : V}

theorem cartanFPF_of_model (D : XDatum S Φ ΓM v₁ v₂) (e : S.ι.Γ ≃ V) (he1 : e S.ι.xv = v₁)
    (heq : ∀ y a, e (Φ y • a) = y • e a)
    (hadj : ∀ a b, S.ι.graph.Adj a b ↔ ΓM.Adj (e a) (e b))
    (Q : Subgroup X) (hQ : pCoreOf S.p (MulAction.stabilizer X v₁) = Q)
    (b u₁ u₂ : V) (hb : ΓM.dist v₁ b = S.m) (h₁ : ΓM.Adj v₁ u₁) (h₂ : ΓM.Adj v₁ u₂)
    (hne : u₁ ≠ u₂) (h₀ : X) (hx : h₀ • v₁ = v₁) (hbb : h₀ • b = b) (hu₁ : h₀ • u₁ = u₁)
    (hu₂ : h₀ • u₂ = u₂) (hc : ∀ q ∈ Q, h₀ * q * h₀⁻¹ = q → q = 1) : S.CartanFPF := by
  let iso : S.ι.graph ≃g ΓM := ⟨e, fun {a b} => (hadj a b).symm⟩
  have hdist : ∀ a b, ΓM.dist (e a) (e b) = S.ι.graph.dist a b := fun a b => iso_dist iso a b
  have hQb : S.Qbar S.ι.xv = Q.map Φ :=
    D.qbar_eq S.ι.xv (MulAction.stabilizer X v₁) Q (fun y => by
      rw [MulAction.mem_stabilizer_iff, ← D.stab1 y]
      exact MulAction.mem_stabilizer_iff.symm) hQ
  have hfix : ∀ w : V, h₀ • w = w → Φ h₀ • e.symm w = e.symm w := fun w hw => by
    apply e.injective
    rw [heq, e.apply_symm_apply, hw]
  refine ⟨e.symm b, e.symm u₁, e.symm u₂, ?_, ?_, ?_, ?_, Φ h₀, (D.stab1 h₀).mpr hx,
    hfix b hbb, hfix u₁ hu₁, hfix u₂ hu₂, ?_⟩
  · rw [← hdist, e.apply_symm_apply, he1]
    exact hb
  · rw [hadj, he1, e.apply_symm_apply]
    exact h₁
  · rw [hadj, he1, e.apply_symm_apply]
    exact h₂
  · exact fun h => hne (by simpa using congrArg e h)
  · intro q hq hqc
    rw [hQb] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hcomm : h₀ * q₀ * h₀⁻¹ = q₀ := D.inj (by rw [map_mul, map_mul, map_inv]; exact hqc)
    rw [hc q₀ hq₀ hcomm, map_one]

theorem tau_e_eq (D : XDatum S Φ ΓM v₁ v₂) (e : S.ι.Γ ≃ V) (he1 : e S.ι.xv = v₁)
    (he2 : e S.ι.lv = v₂) (heq : ∀ y a, e (Φ y • a) = y • e a) (τ : V → Bool)
    (hτ : ∀ (y : X) (w : V), τ (y • w) = τ w) (a : S.ι.Γ) :
    τ (e a) = τ (cond (CosetGeom.vtype a) v₂ v₁) := by
  obtain ⟨y, hy⟩ := D.hsurj a
  have h1 := heq y (S.ι.baseVert (CosetGeom.vtype a))
  rw [hy] at h1
  rw [h1, hτ]
  cases CosetGeom.vtype a
  · exact congrArg τ he1
  · exact congrArg τ he2

theorem faithfulOnType_of_model (D : XDatum S Φ ΓM v₁ v₂) (e : S.ι.Γ ≃ V)
    (he1 : e S.ι.xv = v₁) (he2 : e S.ι.lv = v₂) (heq : ∀ y a, e (Φ y • a) = y • e a)
    (τ : V → Bool) (hτ : ∀ (y : X) (w : V), τ (y • w) = τ w) (hlab : τ v₁ ≠ τ v₂) (s : Bool)
    (hcent : ∀ k : S.ι.G0, (∀ y : X, k * Φ y = Φ y * k) → k = 1)
    (hX : ∀ y : X, (∀ w : V, τ w = τ (cond s v₂ v₁) → y • w = w) → y = 1) :
    S.FaithfulOnType s := by
  have hfaith : ∀ y : X, (∀ a : S.ι.Γ, CosetGeom.vtype a = s → Φ y • a = a) → y = 1 := by
    intro y hy
    apply hX
    intro w hw
    have hvt : CosetGeom.vtype (e.symm w) = s := by
      have h1 := tau_e_eq D e he1 he2 heq τ hτ (e.symm w)
      rw [e.apply_symm_apply, hw] at h1
      cases hs : CosetGeom.vtype (e.symm w) <;> cases s <;> rw [hs] at h1 <;>
        first
        | rfl
        | exact absurd h1.symm hlab
        | exact absurd h1 hlab
    have := hy _ hvt
    rw [← e.apply_symm_apply w, ← heq, this]
  intro k hk
  apply hcent
  intro y
  have hmem : k * Φ y * k⁻¹ ∈ S.N := by
    refine S.hN.conj_mem _ ?_ k
    rw [D.N_eq]
    exact ⟨y, rfl⟩
  rw [D.N_eq] at hmem
  obtain ⟨y', hy'⟩ := hmem
  have hy : y' = y := by
    have h1 : ∀ a : S.ι.Γ, CosetGeom.vtype a = s → Φ (y'⁻¹ * y) • a = a := by
      intro a ha
      have e1 : k⁻¹ • a = a := inv_smul_eq_iff.mpr (hk a ha).symm
      have e2 : k • (Φ y • a) = Φ y • a := hk _ (by rw [CosetGeom.vtype_smul]; exact ha)
      have e3 : Φ y' • a = Φ y • a := by
        rw [hy', mul_smul, mul_smul, e1, e2]
      rw [map_mul, map_inv, mul_smul, ← e3, inv_smul_smul]
    exact inv_mul_eq_one.mp (hfaith _ h1)
  rw [hy] at hy'
  calc k * Φ y = (k * Φ y * k⁻¹) * k := by group
    _ = Φ y * k := by rw [← hy']

end CFSG.Quasithin.H13.F431.F48Rig
