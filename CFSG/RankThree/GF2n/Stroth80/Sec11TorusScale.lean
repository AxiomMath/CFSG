module

public import CFSG.RankThree.GF2n.Stroth80.Sec11TorusFrame
import CFSG.RankThree.GF2n.Smith81.Lin26Roots
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace LBFrame

variable (fr : LBFrame Q Z B)

private theorem conj_mem_ZB (hc : Ctx M Q Z B) {k : G} (hkZ : k ∈ Subgroup.centralizer (Z : Set G))
    (hkB : k ∈ Subgroup.normalizer (B : Set G)) {w : G} (hw : w ∈ Z ⊔ B) : k * w * k⁻¹ ∈ Z ⊔ B := by
  obtain ⟨z, hz, b, hb, rfl⟩ := (Smith81.Ctx.mem_sup_iff hc).mp hw
  have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hkZ z hz).symm
  have e : k * (z * b) * k⁻¹ = z * (k * b * k⁻¹) := by
    calc k * (z * b) * k⁻¹ = (k * z) * b * k⁻¹ := by group
      _ = (z * k) * b * k⁻¹ := by rw [hkz]
      _ = z * (k * b * k⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz)
    (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hkB b).mp hb))

private theorem exists_conj_decomp_ZB (hc : Ctx M Q Z B) {k : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G))
    (w w' : ↥(Z ⊔ B)) (hw' : (w' : G) = k * w * k⁻¹) :
    ∃ (z : G) (hz : z ∈ Z) (b : G) (hb : b ∈ B) (hb' : k * b * k⁻¹ ∈ B),
      w = ⟨z, Subgroup.mem_sup_left hz⟩ * ⟨b, Subgroup.mem_sup_right hb⟩ ∧
      w' = ⟨z, Subgroup.mem_sup_left hz⟩ * ⟨k * b * k⁻¹, Subgroup.mem_sup_right hb'⟩ := by
  obtain ⟨z, hz, b, hb, hw⟩ := (Smith81.Ctx.mem_sup_iff hc).mp w.2
  have hb' : k * b * k⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hkB b).mp hb
  have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hkZ z hz).symm
  refine ⟨z, hz, b, hb, hb', Subtype.ext hw, Subtype.ext ?_⟩
  rw [hw', hw]
  show k * (z * b) * k⁻¹ = z * (k * b * k⁻¹)
  calc k * (z * b) * k⁻¹ = (k * z) * b * k⁻¹ := by group
    _ = (z * k) * b * k⁻¹ := by rw [hkz]
    _ = z * (k * b * k⁻¹) := by group

private theorem coord_zero_conj_ZB (hc : Ctx M Q Z B) {k : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G))
    (w w' : ↥(Z ⊔ B)) (hw' : (w' : G) = k * w * k⁻¹) :
    Multiplicative.toAdd (fr.ψ w') 0 = Multiplicative.toAdd (fr.ψ w) 0 := by
  obtain ⟨z, hz, b, hb, hb', e1, e2⟩ := exists_conj_decomp_ZB hc hkZ hkB w w' hw'
  rw [e1, e2, map_mul, toAdd_mul, map_mul, toAdd_mul, Pi.add_apply, Pi.add_apply,
    (fr.mem_B_iff_coord hc ⟨b, Subgroup.mem_sup_right hb⟩).mp hb,
    (fr.mem_B_iff_coord hc ⟨_, Subgroup.mem_sup_right hb'⟩).mp hb']

private theorem scale_mul_coord_conj (hc : Ctx M Q Z B) {k : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G))
    (hkx : k * fr.lbRootU 1 * k⁻¹ ∈ Q) {τ : fr.K}
    (hτ : fr.φ ⟨k * fr.lbRootU 1 * k⁻¹, Subgroup.mem_sup_left hkx⟩ =
      Timmesfeld.RankOne.upperElt fr.K τ)
    (w w' : ↥(Z ⊔ B)) (hw : (w : G) ∈ B) (hw' : (w' : G) = k * w * k⁻¹) :
    τ * Multiplicative.toAdd (fr.ψ w') 1 = Multiplicative.toAdd (fr.ψ w) 1 := by
  have hx := fr.lbRootU_mem 1
  have hv : fr.lbRootU 1 * w * (fr.lbRootU 1)⁻¹ ∈ Z ⊔ B :=
    (Subgroup.mem_normalizer_iff.mp (Smith81.Ctx.Q_le_normalizer_ZB hc hx) w).mp w.2
  have hv' := conj_mem_ZB hc hkZ hkB hv
  have e1 := fr.compat ⟨_, Subgroup.mem_sup_left hx⟩ w ⟨_, hv⟩ rfl
  have e2 := fr.compat ⟨_, Subgroup.mem_sup_left hkx⟩ w' ⟨_, hv'⟩ (by
    show k * (fr.lbRootU 1 * w * (fr.lbRootU 1)⁻¹) * k⁻¹ =
      k * fr.lbRootU 1 * k⁻¹ * w' * (k * fr.lbRootU 1 * k⁻¹)⁻¹
    rw [hw']
    group)
  have e3 := fr.coord_zero_conj_ZB hc hkZ hkB ⟨_, hv⟩ ⟨_, hv'⟩ rfl
  rw [fr.phi_lbRootU, Timmesfeld.ARS.NaturalModule.upperElt_mulVec] at e1
  rw [hτ, Timmesfeld.ARS.NaturalModule.upperElt_mulVec] at e2
  rw [e1, e2] at e3
  have h0 := (fr.mem_B_iff_coord hc w).mp hw
  have h0' := (fr.mem_B_iff_coord hc w').mp
    (by rw [hw']; exact (Subgroup.mem_normalizer_iff.mp hkB w).mp hw)
  simpa [h0, h0'] using e3

private theorem exists_scale_B (hc : Ctx M Q Z B) {k : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G)) :
    ∃ β : fr.K, β ≠ 0 ∧ ∀ w w' : ↥(Z ⊔ B), (w : G) ∈ B → (w' : G) = k * w * k⁻¹ →
      Multiplicative.toAdd (fr.ψ w') 1 = β * Multiplicative.toAdd (fr.ψ w) 1 := by
  have hkM : k ∈ M := hc.hyp.normalizer_Z.1 ▸ Subgroup.centralizer_le_normalizer _ hkZ
  have hkx : k * fr.lbRootU 1 * k⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hkM) _).mp (fr.lbRootU_mem 1)
  obtain ⟨τ, hτ⟩ := fr.exists_phi_eq_upperElt hkx
  obtain ⟨w₁, hw₁⟩ : ∃ w : ↥(Z ⊔ B), Multiplicative.toAdd (fr.ψ w) = ![0, 1] :=
    ⟨fr.ψ.symm (Multiplicative.ofAdd ![0, 1]), by simp⟩
  have hw₁B : (w₁ : G) ∈ B := (fr.mem_B_iff_coord hc w₁).mpr (by rw [hw₁]; rfl)
  have hτ0 : τ ≠ 0 := by
    intro h0
    have h := fr.scale_mul_coord_conj hc hkZ hkB hkx hτ w₁ ⟨_, conj_mem_ZB hc hkZ hkB w₁.2⟩
      hw₁B rfl
    rw [h0, zero_mul, hw₁] at h
    simp at h
  refine ⟨τ⁻¹, inv_ne_zero hτ0, fun w w' hw hw' => ?_⟩
  rw [← fr.scale_mul_coord_conj hc hkZ hkB hkx hτ w w' hw hw', ← mul_assoc,
    inv_mul_cancel₀ hτ0, one_mul]

private theorem exists_conj_coord_ZB (hc : Ctx M Q Z B) {k : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G)) :
    ∃ β : fr.K, β ≠ 0 ∧ ∀ w w' : ↥(Z ⊔ B), (w' : G) = k * w * k⁻¹ →
      Multiplicative.toAdd (fr.ψ w') =
        ![Multiplicative.toAdd (fr.ψ w) 0, β * Multiplicative.toAdd (fr.ψ w) 1] := by
  obtain ⟨β, hβ, hB⟩ := fr.exists_scale_B hc hkZ hkB
  refine ⟨β, hβ, fun w w' hw' => ?_⟩
  obtain ⟨z, hz, b, hb, hb', e1, e2⟩ := exists_conj_decomp_ZB hc hkZ hkB w w' hw'
  have hz1 := (fr.memZ ⟨z, Subgroup.mem_sup_left hz⟩).mp hz
  have hb0 := (fr.mem_B_iff_coord hc ⟨b, Subgroup.mem_sup_right hb⟩).mp hb
  have hb0' := (fr.mem_B_iff_coord hc ⟨_, Subgroup.mem_sup_right hb'⟩).mp hb'
  have hbb := hB ⟨b, Subgroup.mem_sup_right hb⟩ ⟨_, Subgroup.mem_sup_right hb'⟩ hb rfl
  rw [e1, e2, map_mul, toAdd_mul, map_mul, toAdd_mul]
  ext i
  fin_cases i
  · simp [hb0, hb0']
  · simp [hz1, hbb]

private theorem phi_conj_upper (hc : Ctx M Q Z B) {k : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G))
    {β : fr.K} (hβ : β ≠ 0) (hk : ∀ w w' : ↥(Z ⊔ B), (w' : G) = k * w * k⁻¹ →
      Multiplicative.toAdd (fr.ψ w') =
        ![Multiplicative.toAdd (fr.ψ w) 0, β * Multiplicative.toAdd (fr.ψ w) 1])
    {x : G} (hx : x ∈ Q) {t : fr.K}
    (hxt : fr.φ ⟨x, Subgroup.mem_sup_left hx⟩ = Timmesfeld.RankOne.upperElt fr.K t)
    (h : k * x * k⁻¹ ∈ Q ⊔ QB B) :
    fr.φ ⟨k * x * k⁻¹, h⟩ = Timmesfeld.RankOne.upperElt fr.K (β⁻¹ * t) := by
  have hkM : k ∈ M := hc.hyp.normalizer_Z.1 ▸ Subgroup.centralizer_le_normalizer _ hkZ
  have hkx : k * x * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hkM) x).mp hx
  obtain ⟨t', ht'⟩ := fr.exists_phi_eq_upperElt hkx
  obtain ⟨w, hw⟩ : ∃ w : ↥(Z ⊔ B), Multiplicative.toAdd (fr.ψ w) = ![0, 1] :=
    ⟨fr.ψ.symm (Multiplicative.ofAdd ![0, 1]), by simp⟩
  have hv : x * w * x⁻¹ ∈ Z ⊔ B :=
    (Subgroup.mem_normalizer_iff.mp (Smith81.Ctx.Q_le_normalizer_ZB hc hx) w).mp w.2
  have hv' := conj_mem_ZB hc hkZ hkB hv
  have hw' := conj_mem_ZB hc hkZ hkB w.2
  have e1 := fr.compat ⟨x, Subgroup.mem_sup_left hx⟩ w ⟨_, hv⟩ rfl
  have e2 := fr.compat ⟨_, Subgroup.mem_sup_left hkx⟩ ⟨_, hw'⟩ ⟨_, hv'⟩ (by
    show k * (x * w * x⁻¹) * k⁻¹ = k * x * k⁻¹ * (k * w * k⁻¹) * (k * x * k⁻¹)⁻¹
    group)
  have e3 := hk ⟨_, hv⟩ ⟨_, hv'⟩ rfl
  rw [hxt, Timmesfeld.ARS.NaturalModule.upperElt_mulVec, hw] at e1
  rw [ht', Timmesfeld.ARS.NaturalModule.upperElt_mulVec, hk w ⟨_, hw'⟩ rfl, hw] at e2
  rw [e1, e2] at e3
  have h0 : t' * β = t := by
    have := congrFun e3 0
    simp at this
    linear_combination this
  have ht : t' = β⁻¹ * t := by
    rw [← h0, mul_comm t' β, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]
  rw [← ht]
  exact ht'

private theorem phi_conj_lower (hc : Ctx M Q Z B) {k : G}
    (hkZ : k ∈ Subgroup.centralizer (Z : Set G)) (hkB : k ∈ Subgroup.normalizer (B : Set G))
    {β : fr.K} (hk : ∀ w w' : ↥(Z ⊔ B), (w' : G) = k * w * k⁻¹ →
      Multiplicative.toAdd (fr.ψ w') =
        ![Multiplicative.toAdd (fr.ψ w) 0, β * Multiplicative.toAdd (fr.ψ w) 1])
    {u : G} (hu : u ∈ QB B) {s : fr.K}
    (hus : fr.φ ⟨u, Subgroup.mem_sup_right hu⟩ = Timmesfeld.RankOne.lowerElt fr.K s)
    (h : k * u * k⁻¹ ∈ Q ⊔ QB B) :
    fr.φ ⟨k * u * k⁻¹, h⟩ = Timmesfeld.RankOne.lowerElt fr.K (β * s) := by
  have hku : k * u * k⁻¹ ∈ QB B :=
    (Subgroup.mem_normalizer_iff.mp (hc.normalizer_B_le_normalizer_QB hkB) u).mp hu
  obtain ⟨s', hs'⟩ := fr.exists_phi_eq_lowerElt hku
  obtain ⟨w, hw⟩ : ∃ w : ↥(Z ⊔ B), Multiplicative.toAdd (fr.ψ w) = ![1, 0] :=
    ⟨fr.ψ.symm (Multiplicative.ofAdd ![1, 0]), by simp⟩
  have hv : u * w * u⁻¹ ∈ Z ⊔ B :=
    (Subgroup.mem_normalizer_iff.mp (Smith81.Ctx.QB_le_normalizer_ZB hc hu) w).mp w.2
  have hv' := conj_mem_ZB hc hkZ hkB hv
  have hw' := conj_mem_ZB hc hkZ hkB w.2
  have e1 := fr.compat ⟨u, Subgroup.mem_sup_right hu⟩ w ⟨_, hv⟩ rfl
  have e2 := fr.compat ⟨_, Subgroup.mem_sup_right hku⟩ ⟨_, hw'⟩ ⟨_, hv'⟩ (by
    show k * (u * w * u⁻¹) * k⁻¹ = k * u * k⁻¹ * (k * w * k⁻¹) * (k * u * k⁻¹)⁻¹
    group)
  have e3 := hk ⟨_, hv⟩ ⟨_, hv'⟩ rfl
  rw [hus, Timmesfeld.ARS.NaturalModule.lowerElt_mulVec, hw] at e1
  rw [hs', Timmesfeld.ARS.NaturalModule.lowerElt_mulVec, hk w ⟨_, hw'⟩ rfl, hw] at e2
  rw [e1, e2] at e3
  have h1 : s' = β * s := by
    have := congrFun e3 1
    simp at this
    linear_combination this
  rw [← h1]
  exact hs'

theorem exists_scale (hc : Ctx M Q Z B) {k : G} (hkZ : k ∈ Subgroup.centralizer (Z : Set G))
    (hkB : k ∈ Subgroup.normalizer (B : Set G)) :
    ∃ μ : fr.K, μ ≠ 0 ∧
      (∀ (x : G) (hx : x ∈ Q) (t : fr.K),
        fr.φ ⟨x, Subgroup.mem_sup_left hx⟩ = Timmesfeld.RankOne.upperElt fr.K t →
        ∀ h : k * x * k⁻¹ ∈ Q ⊔ QB B,
          fr.φ ⟨k * x * k⁻¹, h⟩ = Timmesfeld.RankOne.upperElt fr.K (μ * t)) ∧
      (∀ (u : G) (hu : u ∈ QB B) (s : fr.K),
        fr.φ ⟨u, Subgroup.mem_sup_right hu⟩ = Timmesfeld.RankOne.lowerElt fr.K s →
        ∀ h : k * u * k⁻¹ ∈ Q ⊔ QB B,
          fr.φ ⟨k * u * k⁻¹, h⟩ = Timmesfeld.RankOne.lowerElt fr.K (μ⁻¹ * s)) := by
  obtain ⟨β, hβ, hk⟩ := fr.exists_conj_coord_ZB hc hkZ hkB
  refine ⟨β⁻¹, inv_ne_zero hβ, fun x hx t hxt h => ?_, fun u hu s hus h => ?_⟩
  · exact fr.phi_conj_upper hc hkZ hkB hβ hk hx hxt h
  · rw [inv_inv]
    exact fr.phi_conj_lower hc hkZ hkB hk hu hus h

end LBFrame

end CFSG.RankThree.GF2n.Stroth80
