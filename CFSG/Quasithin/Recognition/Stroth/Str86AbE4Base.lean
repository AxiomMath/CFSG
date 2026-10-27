module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth

import CFSG.Quasithin.Recognition.Stroth.Str86AbC8
import CFSG.Quasithin.Recognition.Stroth.Str86Q1EqDisp
public import CFSG.Quasithin.Recognition.Stroth.Str86LinearVertexDisplacement

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str86_commutator_oTwoUpper_le_of_mem
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {X : Subgroup G}
    (hXN : u3H L1 L2 S ≤ Subgroup.normalizer (X : Set G)) {d : G} (hd : d ∈ u3H L1 L2 S)
    (hdQ : d ∉ Q2 L1 L2 S) (hdX : ∀ x ∈ X, d * x * d⁻¹ * x⁻¹ ∈ Z2 L1 L2 S) :
    ⁅X, oTwoUpper (u3H L1 L2 S)⁆ ≤ Z2 L1 L2 S := by
  have hHZ : u3H L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hHC : u3H L1 L2 S ≤
      Subgroup.normalizer (centralizerMod (Z2 L1 L2 S) (u3H L1 L2 S) X : Set G) :=
    le_normalizer_centralizerMod hHZ Subgroup.le_normalizer hXN
  have hdC : d ∈ centralizerMod (Z2 L1 L2 S) (u3H L1 L2 S) X := ⟨hd, hHZ hd, hdX⟩
  have hQH : Q2 L1 L2 S ≤ u3H L1 L2 S := q2_le_u3H L1 L2 S
  have hHQ : u3H L1 L2 S ≤ Subgroup.normalizer (Q2 L1 L2 S : Set G) :=
    (u3H_le_p2 L1 L2 S).trans (le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hCQ : centralizerMod (Z2 L1 L2 S) (u3H L1 L2 S) X ⊔ Q2 L1 L2 S = u3H L1 L2 S := by
    rcases eq_or_eq_sup_of_normal_of_isL2Quot hI.hF.toW hI.hm hI.hL2
        (sup_le (centralizerMod_le_left _ _ _) hQH) (F1.le_normalizer_sup hHC hHQ)
        le_sup_right with h | h
    · exact absurd (h ▸ Subgroup.mem_sup_left hdC) hdQ
    · exact h
  have hO : oTwoUpper (u3H L1 L2 S) ≤ centralizerMod (Z2 L1 L2 S) (u3H L1 L2 S) X := by
    refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    rw [← hCQ] at hx
    obtain ⟨c, hc, q, hq, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (hQH.trans hHC)).mp hx
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (P2 L1 L2 S) ⟨q, hq⟩
    have hqn : q ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    obtain ⟨c', hc', he⟩ := A4.exists_pow_mul_eq hc (hHC (hQH hq)) (2 ^ n)
    refine ⟨n, ?_⟩
    rw [he, hqn, mul_one]
    exact hc'
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have e : ⁅x, y⁆ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (Z2 L1 L2 S).inv_mem ((hO hy).2.2 x hx)

theorem str86_two_pow_le_of_commutator_mod_z2
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {X Y : Subgroup G}
    (hVX : conjClosure (Z2 L1 L2 S) L1 ≤ X) (hXQ : X ≤ Q2 L1 L2 S)
    (hXN : P2 L1 L2 S ≤ Subgroup.normalizer (X : Set G)) (hYX : Y ≤ X)
    (hidx : Y.relIndex X ≤ 2 ^ k) {t : G} (ht : t ∈ u3H L1 L2 S) (htQ : t ∉ Q2 L1 L2 S)
    (htt : t * t ∈ Q2 L1 L2 S) (htY : ∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ Z2 L1 L2 S) :
    2 ^ m ≤ 2 ^ k := by
  have hF := hI.hF
  have hZX : Z2 L1 L2 S ≤ X := (le_conjClosure _ _).trans hVX
  have hXH : X ≤ u3H L1 L2 S := hXQ.trans (q2_le_u3H L1 L2 S)
  have hHZ : u3H L1 L2 S ≤ Subgroup.normalizer (Z2 L1 L2 S : Set G) :=
    str86_z2_normal_u3H L1 L2 S
  have hHX : u3H L1 L2 S ≤ Subgroup.normalizer (X : Set G) := (u3H_le_p2 L1 L2 S).trans hXN
  have hpc : pCoreOf 2 (u3H L1 L2 S) = Q2 L1 L2 S := str86_pCoreOf_u3H hF.toW
  have hXO : X ≤ pCoreOf 2 (u3H L1 L2 S) := hpc ▸ hXQ
  have hW := F112W.isNormalIn_of_le_normalizer (H := u3H L1 L2 S) hZX hHZ
  have hN := F112W.isNormalIn_of_le_normalizer (H := u3H L1 L2 S) (le_refl X) hHX
  obtain ⟨c, hser⟩ := F112W.exists_isChiefSeriesBetween hW X hN hZX
  rcases Nat.eq_zero_or_pos c with rfl | hc
  ·
    exact (str86_false_of_commutator_oTwoUpper_le hI hZQ hVX
      ((F112W.isChiefSeriesBetween_zero_iff hXH hXO hW hN hZX).mp hser)).elim
  have hX2 : IsPGroup 2 X := (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le hXQ
  have htt' : t * t ∈ pCoreOf 2 (u3H L1 L2 S) := hpc ▸ htt
  have htO : t ∉ pCoreOf 2 (u3H L1 L2 S) := hpc ▸ htQ
  have hpow : (2 ^ m) ^ c ≤
      (centralizerMod (Z2 L1 L2 S) X (Subgroup.zpowers t)).relIndex X :=
    pow_le_relIndex_centralizerMod_between hXH (Subgroup.zpowers_le.mpr ht)
      (fun _ _ _ hstep hnc => l2ChiefSectionRep_pow_le_relIndex_centralizerMod hI.hm
        (str86_isL2Quot_u3H hF.toW hI.hL2) hX2 hXH hstep hnc ht htt' htO) hser
  have hYC : Y ≤ centralizerMod (Z2 L1 L2 S) X (Subgroup.zpowers t) := by
    intro y hy
    refine (mem_centralizerMod_zpowers_iff_of_normalizer (hXH.trans hHZ) (hHZ ht)
      (hYX hy)).mpr ?_
    have e : y * t * y⁻¹ * t⁻¹ = (t * y * t⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact (Z2 L1 L2 S).inv_mem (htY y hy)
  calc 2 ^ m ≤ (2 ^ m) ^ c := Nat.le_self_pow hc.ne' _
    _ ≤ (centralizerMod (Z2 L1 L2 S) X (Subgroup.zpowers t)).relIndex X := hpow
    _ ≤ Y.relIndex X := Subgroup.relIndex_le_of_le_left hYC (D15Proof.relIndex_ne_zero _ _)
    _ ≤ 2 ^ k := hidx

end CFSG.Quasithin.Stroth

end
