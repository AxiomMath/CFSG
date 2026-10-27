module

public import CFSG.Quasithin.Background.Harris.R1.QbetaKer
public import CFSG.Quasithin.Recognition.SzR1Prep

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

theorem pCoreK1_le_kerM [Fintype Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hodd : Odd (Fintype.card Ω)) : pCoreOf 2 K1 ≤ C.kerM := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQK : pCoreOf 2 K1 ≤ K1 := CFSG.LieType.BorelTits.pCoreOf_le 2 K1
  set Q' : Subgroup ↥K1 := (pCoreOf 2 K1).subgroupOf K1 with hQ'
  have hQ'p : IsPGroup 2 ↥Q' :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K1).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQK).symm
  have hQ'n : Q'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K1)
  let _ : MulAction ↥Q' Ω := MulAction.compHom Ω (C.D.act.comp Q'.subtype)
  have hmod := hQ'p.card_modEq_card_fixedPoints (α := Ω)
  have hfix : ∃ ω₀ : Ω, ∀ q : ↥Q', C.D.act (q : ↥K1) ω₀ = ω₀ := by
    by_contra hcon
    push Not at hcon
    have h0 : Nat.card (MulAction.fixedPoints ↥Q' Ω) = 0 := by
      rw [Nat.card_eq_zero]
      left
      constructor
      rintro ⟨ω, hω⟩
      obtain ⟨q, hq⟩ := hcon ω
      exact hq (MulAction.mem_fixedPoints.mp hω q)
    rw [h0, Nat.card_eq_fintype_card] at hmod
    obtain ⟨r, hr⟩ := hodd
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨ω₀, hω₀⟩ := hfix
  have hconj : ∀ (k : ↥K1) (ω₁ : Ω), (∀ q : ↥Q', C.D.act (q : ↥K1) ω₁ = ω₁) →
      ∀ q : ↥Q', C.D.act (q : ↥K1) (C.D.act k ω₁) = C.D.act k ω₁ := by
    intro k ω₁ h q
    have hq' : k⁻¹ * (q : ↥K1) * k ∈ Q' := by
      have := hQ'n.conj_mem (q : ↥K1) q.2 k⁻¹
      simpa using this
    have h1 := h ⟨_, hq'⟩
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h1
    have h3 := congrArg (C.D.act k) h1
    simpa [map_inv] using h3
  have hpt : ∀ q : ↥Q', C.D.act (q : ↥K1) C.D.pt = C.D.pt := by
    obtain ⟨k₁, hk₁⟩ := C.D.trans ω₀
    have h5 : C.D.act k₁⁻¹ ω₀ = C.D.pt := by
      rw [map_inv, ← hk₁]
      exact Equiv.symm_apply_apply _ _
    have := hconj k₁⁻¹ ω₀ hω₀
    rw [h5] at this
    exact this
  have hall : ∀ ω, ∀ q : ↥Q', C.D.act (q : ↥K1) ω = ω := by
    intro ω q
    obtain ⟨k, hk⟩ := C.D.trans ω
    rw [← hk]
    exact hconj k C.D.pt hpt q
  intro q hq
  have hqK : q ∈ K1 := hQK hq
  rw [C.mem_kerM]
  refine ⟨Subgroup.mem_sup_left hqK, fun ω => ?_⟩
  have h1 := C.D.conjSub_Vf C.hVn ⟨q, hqK⟩ ω
  rw [hall ω ⟨⟨q, hqK⟩, hq⟩] at h1
  exact h1

theorem pCoreK1_eq_vBeta [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hodd : Odd (Fintype.card Ω)) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hWK : vBeta K1 L2 S Zs ≤ K1)
    (hC : ∀ x ∈ pCoreOf 2 K1, x ∈ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) → x ∈ Zs) :
    pCoreOf 2 K1 = vBeta K1 L2 S Zs := by
  have hWpc : vBeta K1 L2 S Zs ≤ pCoreOf 2 K1 :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWK
      (fun k hk => le_normalizer_conjClosure (conjClosure Zs L2) (K1 ⊔ S)
        (Subgroup.mem_sup_left hk))
      (C.h.hyp.h1.pgroup.to_le C.vBeta_le_S)
  refine le_antisymm (fun q hq => ?_) hWpc
  obtain ⟨w, hw, hwc⟩ := exists_inner_of_kerM C hodd hij l₀ hl₀ hall hcen (pCoreK1_le_kerM C hodd hq)
  have hwq : w⁻¹ * q ∈ pCoreOf 2 K1 :=
    (pCoreOf 2 K1).mul_mem ((pCoreOf 2 K1).inv_mem (hWpc hw)) hq
  have hZ : w⁻¹ * q ∈ Zs := hC _ hwq hwc
  have e : q = w * (w⁻¹ * q) := by group
  rw [e]
  exact (vBeta K1 L2 S Zs).mul_mem hw (F112J2.Zs_le_vBeta K1 L2 S Zs hZ)

end CFSG.Quasithin.Background.Harris.R1
