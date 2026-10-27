module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleDefs

import CFSG.Quasithin.Recognition.Stroth.Str86AbC8
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem t13g_not_central
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) :
    ¬ IsCentralStep (u3H L1 L2 S) ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ := by
  obtain ⟨hstep, -, -⟩ := hO.1
  intro hc
  have hcent : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ≤
      Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h := hc g hg x hx
    rw [Subgroup.mem_bot] at h
    have h2 : g * x * g⁻¹ = x := mul_inv_eq_one.mp h
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h2]
  have hle : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ≤
      Z2 L1 L2 S ⊓ Subgroup.centralizer ((u3H L1 L2 S : Subgroup G) : Set G) :=
    le_inf (F112W.commutator_le_self_of_le_normalizer (str86_z2_normal_u3H L1 L2 S)) hcent
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have h2 : VL2 L2 := ⟨m, hI.hL2⟩
  rw [str86_centralizer_u3H_z2 hI.hF hI.hSB h1 hI.hB2 h2 hI.hZI] at hle
  exact (ne_of_gt hstep.2.2.1) (le_bot_iff.mp hle)

private theorem t13g_commutator_le
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m) (hkm : k < m)
    {X : Subgroup G} (hVX : conjClosure (Z2 L1 L2 S) L1 ≤ X) (hXQ : X ≤ Q2 L1 L2 S)
    (hXN : P2 L1 L2 S ≤ Subgroup.normalizer (X : Set G)) {a : G} (haS : a ∈ S)
    (haQ : a ∉ Q2 L1 L2 S) (ha2 : a * a = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex X ≤
      2 ^ k * 2 ^ m) :
    ⁅X, oTwoUpper (u3H L1 L2 S)⁆ ≤ Z2 L1 L2 S := by
  classical
  have hm : 2 ≤ m := hI.hm
  have hL2u3 : IsL2Quot m (oTwoQuot ↥(u3H L1 L2 S)) := str86_isL2Quot_u3H hI.hF.toW hI.hL2
  obtain ⟨hstep, -, -⟩ := hO.1
  have hnc : ¬ IsCentralStep (u3H L1 L2 S) ⊥ ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ :=
    t13g_not_central hI hO
  have hWZ : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ≤ Z2 L1 L2 S :=
    F112W.commutator_le_self_of_le_normalizer (str86_z2_normal_u3H L1 L2 S)
  have hWX : ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ ≤ X :=
    hWZ.trans ((le_conjClosure (Z2 L1 L2 S) L1).trans hVX)
  have hXnorm : IsNormalIn (u3H L1 L2 S) (Q2 L1 L2 S) X :=
    ⟨hXQ, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp ((u3H_le_p2 L1 L2 S).trans hXN hg) x).mp hx⟩
  obtain ⟨c, hser⟩ := F112W.exists_isChiefSeriesBetween (H := u3H L1 L2 S)
    (U := Q2 L1 L2 S) (W := ⁅Z2 L1 L2 S, u3H L1 L2 S⁆) hstep.1 X hXnorm hWX
  have hUH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hU : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have haH : a ∈ u3H L1 L2 S := str86_s_le_u3H hI.hF.toW hI.hSB hm hI.hL2 haS
  have haO : a ∉ pCoreOf 2 (u3H L1 L2 S) := by rwa [str86_pCoreOf_u3H hI.hF.toW]
  have hasq : a * a ∈ pCoreOf 2 (u3H L1 L2 S) := by
    rw [ha2]
    exact (pCoreOf 2 (u3H L1 L2 S)).one_mem
  have hkstep : ∀ L' N' : Subgroup G, IsChiefStep (u3H L1 L2 S) (Q2 L1 L2 S) L' N' →
      ¬ IsCentralStep (u3H L1 L2 S) L' N' →
      2 ^ m ≤ (centralizerMod L' N' (Subgroup.zpowers a)).relIndex N' := by
    intro L' N' hs hnc'
    exact l2ChiefSectionRep_pow_le_relIndex_centralizerMod (H := u3H L1 L2 S)
      (U := Q2 L1 L2 S) hm hL2u3 hU hUH hs hnc' haH hasq haO
  have hfrom : IsChiefSeriesFrom (u3H L1 L2 S) (Q2 L1 L2 S)
      ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ 1 :=
    F112W.isChiefSeriesFrom_of_between_bot
      (F112W.IsChiefSeriesBetween.noncentral hstep hnc F112W.IsChiefSeriesBetween.refl)
  have hfull : IsChiefSeriesFrom (u3H L1 L2 S) (Q2 L1 L2 S) X (c + 1) :=
    F112W.IsChiefSeriesBetween.append hser hfrom
  have hpow := D15Proof.pow_le_relIndex hUH (Subgroup.zpowers_le.mpr haH) hkstep hfull
  have hfin : (2 ^ m) ^ (c + 1) ≤ 2 ^ k * 2 ^ m := hpow.trans hdisp
  have hbase : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have hlt : 2 ^ k * 2 ^ m < (2 ^ m) ^ 2 := by
    calc 2 ^ k * 2 ^ m < 2 ^ m * 2 ^ m :=
          Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) hkm)
            (Nat.two_pow_pos m)
      _ = (2 ^ m) ^ 2 := by rw [pow_two]
  have hc : c = 0 := by
    have := (Nat.pow_lt_pow_iff_right hbase).mp (hfin.trans_lt hlt)
    omega
  have hUQ : Q2 L1 L2 S ≤ pCoreOf 2 (u3H L1 L2 S) := by rw [str86_pCoreOf_u3H hI.hF.toW]
  have hser0 : F112W.IsChiefSeriesBetween (u3H L1 L2 S) (Q2 L1 L2 S)
      ⁅Z2 L1 L2 S, u3H L1 L2 S⁆ X 0 := by rw [hc] at hser; exact hser
  exact ((F112W.isChiefSeriesBetween_zero_iff (W := ⁅Z2 L1 L2 S, u3H L1 L2 S⁆) (N := X)
    hUH hUQ hstep.1 hXnorm hWX).mp hser0).trans hWZ

theorem str86_false_of_V2_displacement
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hO : Str86OddModule L1 L2 S m)
    (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) (hkm : k < m) {X : Subgroup G}
    (hVX : conjClosure (Z2 L1 L2 S) L1 ≤ X) (hXQ : X ≤ Q2 L1 L2 S)
    (hXN : P2 L1 L2 S ≤ Subgroup.normalizer (X : Set G)) {a : G} (haS : a ∈ S)
    (haQ : a ∉ Q2 L1 L2 S) (ha2 : a * a = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)).relIndex X ≤
      2 ^ k * 2 ^ m) : False :=
  str86_false_of_commutator_oTwoUpper_le hI hZQ hVX
    (t13g_commutator_le hI hO hkm hVX hXQ hXN haS haQ ha2 hdisp)

end CFSG.Quasithin.Stroth

end
