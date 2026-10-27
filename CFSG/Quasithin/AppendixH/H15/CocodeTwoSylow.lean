module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoNorm
public import CFSG.Quasithin.AppendixH.Common.OctadCentralizer
public import CFSG.Quasithin.Background.E3Weak

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

private theorem isSylowIn_of_le_aux {G : Type*} [Group G] {T M H : Subgroup G}
    (hT : IsSylowIn 2 T H) (hTM : T ≤ M) (hMH : M ≤ H) : IsSylowIn 2 T M := by
  refine ⟨hTM, hT.isPGroup, fun hdvd => hT.not_dvd_relIndex ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex T M H hTM hMH]
  exact Dvd.dvd.mul_right hdvd _

private theorem isPGroup_zpowers_of_sq_aux {G : Type*} [Group G] {z : G} (hz : z ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers z) := fun g => ⟨1, by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
  apply Subtype.ext
  change (g : G) ^ 2 ^ 1 = 1
  rw [pow_one, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]⟩

theorem mem_of_centralizes_sylow {G : Type*} [Group G] {Q : Subgroup G} {H : Subgroup G}
    [Finite H] (hQ : IsSylowIn 2 Q H) {z : G} (hzH : z ∈ H) (hz2 : orderOf z = 2)
    (hc : ∀ q ∈ Q, q * z = z * q) : z ∈ Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := Subgroup.zpowers z
  let H' : Subgroup G := Q ⊔ N
  have hH'H : H' ≤ H := sup_le hQ.le (Subgroup.zpowers_le.2 hzH)
  have hzsq : z ^ 2 = 1 := by simpa [hz2] using pow_orderOf_eq_one z
  have hN2 : IsPGroup 2 N := isPGroup_zpowers_of_sq_aux hzsq
  have hH'cent : H' ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le ?_ ?_
    · intro q hq
      exact Subgroup.mem_centralizer_singleton_iff.2 (hc q hq)
    · exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hNormal : (N.subgroupOf H').Normal := by
    refine ⟨?_⟩
    intro n hn h
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    change (h : G) * (n : G) * (h : G)⁻¹ ∈ N
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
    rw [← hk]
    have hcomm : (h : G) * z = z * (h : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hH'cent h.2)
    have hkeq : (h : G) * z ^ k * (h : G)⁻¹ = z ^ k := by
      rw [(Commute.zpow_right hcomm k).eq]
      group
    rw [hkeq]
    exact Subgroup.zpow_mem_zpowers z k
  have hQ' : IsSylowIn 2 Q H' := isSylowIn_of_le_aux hQ le_sup_left hH'H
  exact hQ'.le_of_normal le_sup_right hNormal hN2 (Subgroup.mem_zpowers z)

theorem exists_conj_octFix (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {z : S24}
    (hzΓ : z ∈ Γ) (hz2 : orderOf z = 2) (hc : IsTwoCentralElt Γ z) :
    ∃ c : ↥Γ, (c : S24)⁻¹ * z * (c : S24) ∈ octFix O := by
  let R : Subgroup S24 := T₀ ⊓ Γ
  obtain ⟨S', hS', hS'comm⟩ := hc
  obtain ⟨h, hh, hle⟩ :=
    CFSG.Quasithin.E3.exists_le_conj_of_isSylowIn (H := Γ) (S := S') (Y := R)
      hS' inf_le_right hM.sylow.isPGroup
  have hz'2 : orderOf (h⁻¹ * z * h) = 2 := by
    have heq : h⁻¹ * z * h = (MulAut.conj h⁻¹).toMonoidHom z := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [heq, orderOf_injective (MulAut.conj h⁻¹).toMonoidHom
      (MulAut.conj h⁻¹).injective z, hz2]
  have hz'Γ : h⁻¹ * z * h ∈ Γ := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hh) hzΓ) hh
  have hcent : ∀ y ∈ R, y * (h⁻¹ * z * h) = (h⁻¹ * z * h) * y := by
    intro y hy
    have hyS : h * y * h⁻¹ ∈ S' := CFSG.Quasithin.mem_conjSubgroup_iff.1 (hle hy)
    have hyz : (h * y * h⁻¹) * z = z * (h * y * h⁻¹) := hS'comm _ hyS
    calc y * (h⁻¹ * z * h)
        = h⁻¹ * ((h * y * h⁻¹) * z) * h := by group
      _ = h⁻¹ * (z * (h * y * h⁻¹)) * h := by rw [hyz]
      _ = (h⁻¹ * z * h) * y := by group
  have hz'R : h⁻¹ * z * h ∈ R := mem_of_centralizes_sylow hM.sylow hz'Γ hz'2 hcent
  have hz'T : h⁻¹ * z * h ∈ T₀ := (Subgroup.mem_inf.1 hz'R).1
  have hz'stab : h⁻¹ * z * h ∈ octStab O :=
    mem_octStab_iff.2 ⟨hM.cfg.sylow.le hz'T, hM.cfg.stab_O _ hz'T⟩
  have hz'cent : h⁻¹ * z * h ∈ Subgroup.centralizer (octFix O : Set S24) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => hcent y (mctx_octFix_le_T hM hy)
  have hz'octFix : h⁻¹ * z * h ∈ octFix O := by
    rw [← octStab_inf_centralizer_octFix hM.cfg.octad]
    exact Subgroup.mem_inf.2 ⟨hz'stab, hz'cent⟩
  exact ⟨⟨h, hh⟩, by simpa using hz'octFix⟩

end CFSG.ASVolI.AppH

