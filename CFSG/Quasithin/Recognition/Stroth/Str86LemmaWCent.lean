module


import CFSG.Goldschmidt.Steps.G75Basic
import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Vertex
public import CFSG.Quasithin.Recognition.Stroth.Str86AbHyp
public import CFSG.Quasithin.Recognition.Stroth.Str86ZTwoOrth

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem eq_bot_of_isPGroup_le_commutator
    {A I T W : Subgroup G} {y : G}
    (hA : IsElemAbelian 2 A) (hy : y ∈ Subgroup.normalizer (A : Set G))
    (hodd : Odd (orderOf y)) (hT : IsPGroup 2 T)
    (hTI : T ≤ Subgroup.normalizer (I : Set G))
    (hIA : I ≤ A) (hIW : I ≤ W) (hW : W = ⁅A, Subgroup.zpowers y⁆)
    (hC : A ⊓ Subgroup.centralizer (T : Set G) ≤ Subgroup.centralizer ({y} : Set G)) :
    I = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hI2 : IsPGroup 2 I :=
    (CFSG.Goldschmidt.G75.isPGroup_of_isElemAbelian hA).to_le hIA
  have hWinf : W ⊓ Subgroup.centralizer ({y} : Set G) = ⊥ := by
    rw [hW]
    exact CFSG.Goldschmidt.G75.commutator_inf_centralizer_eq_bot hA hy hodd
  by_contra hIne
  have hIntr : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).mpr hIne
  have hIcard_gt : 1 < Nat.card ↥I := Finite.one_lt_card_iff_nontrivial.mpr hIntr
  have hIcard2 : 2 ∣ Nat.card ↥I := by
    rcases hI2.card_eq_or_dvd with h1 | h2
    · omega
    · exact h2
  let ψ : ↥T →* MulAut ↥I := I.normalizerMonoidHom.comp (Subgroup.inclusion hTI)
  let _ : MulAction ↥T ↥I := MulAction.compHom _ ψ
  have hψ : ∀ (t : ↥T) (i : ↥I),
      ((t • i : ↥I) : G) = (t : G) * (i : G) * (t : G)⁻¹ := fun _ _ => rfl
  have hfix1 : (1 : ↥I) ∈ MulAction.fixedPoints ↥T ↥I := by
    rw [MulAction.mem_fixedPoints]
    intro t
    apply Subtype.ext
    change ((t • (1 : ↥I) : ↥I) : G) = ((1 : ↥I) : G)
    rw [hψ]
    simp
  obtain ⟨b, hbfix, hbne⟩ :=
    hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥I) hIcard2 hfix1
  have hbC : (b : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h := (MulAction.mem_fixedPoints.mp hbfix) ⟨t, ht⟩
    have h' := congrArg Subtype.val h
    rw [hψ] at h'
    calc
      t * (b : G) = (t * (b : G) * t⁻¹) * t := by group
      _ = (b : G) * t := by rw [h']
  have hbA : (b : G) ∈ A := hIA b.2
  have hbCy : (b : G) ∈ Subgroup.centralizer ({y} : Set G) :=
    hC (Subgroup.mem_inf.mpr ⟨hbA, hbC⟩)
  have hbW : (b : G) ∈ W := hIW b.2
  have hbBot : (b : G) ∈ (⊥ : Subgroup G) := by
    rw [← hWinf]
    exact Subgroup.mem_inf.mpr ⟨hbW, hbCy⟩
  exact hbne (Subtype.ext (Subgroup.mem_bot.mp hbBot)).symm

private theorem le_normalizer_commutator_zpowers_of_trivial_mod
    {A H Q S : Subgroup G} {w : G}
    (hA : IsElemAbelian 2 A) (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hS : S ≤ Subgroup.normalizer (A : Set G))
    (hQ : Q ≤ Subgroup.centralizer (A : Set G)) (hSH : S ≤ H)
    (htriv : ∀ x ∈ H, w * x * w⁻¹ * x⁻¹ ∈ Q) :
    S ≤ Subgroup.normalizer ((⁅A, Subgroup.zpowers w⁆ : Subgroup G) : Set G) := by
  classical
  refine CFSG.subgroup_le_normalizer_of_conj_mem ⁅A, Subgroup.zpowers w⁆ S ?_
  intro s x hx
  have hmap : (⁅A, Subgroup.zpowers w⁆ : Subgroup G).map
      (MulAut.conj (s : G)).toMonoidHom ≤ ⁅A, Subgroup.zpowers w⁆ := by
    rw [Subgroup.map_commutator]
    have hAmap : A.map (MulAut.conj (s : G)).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hS s.2)
    have hWmap : (Subgroup.zpowers w).map (MulAut.conj (s : G)).toMonoidHom =
        Subgroup.zpowers ((s : G) * w * (s : G)⁻¹) := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hAmap, hWmap]
    set w' : G := (s : G) * w * (s : G)⁻¹ with hw'def
    have hq : w * (s : G) * w⁻¹ * (s : G)⁻¹ ∈ Q := htriv (s : G) (hSH s.2)
    have hw'mem : w' ∈ Subgroup.centralizer (A : Set G) ⊔ Subgroup.zpowers w := by
      have hEq : w' = (w * (s : G) * w⁻¹ * (s : G)⁻¹)⁻¹ * w := by
        rw [hw'def]
        group
      rw [hEq]
      exact Subgroup.mul_mem_sup (hQ (Subgroup.inv_mem Q hq)) (Subgroup.mem_zpowers w)
    have hDle : Subgroup.zpowers w' ≤ Subgroup.centralizer (A : Set G) ⊔ Subgroup.zpowers w :=
      Subgroup.zpowers_le.mpr hw'mem
    have hDnormC : Subgroup.zpowers w ≤ Subgroup.normalizer
        ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.mpr hw).trans (F7.normalizer_le_normalizer_centralizer A)
    have hset : ((Subgroup.centralizer (A : Set G) ⊔ Subgroup.zpowers w : Subgroup G) : Set G) =
        (Subgroup.zpowers w : Set G) * (Subgroup.centralizer (A : Set G) : Set G) := by
      rw [sup_comm]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDnormC
    refine (Subgroup.commutator_mono le_rfl hDle).trans ?_
    rw [Subgroup.commutator_le]
    intro z hz d hd
    have hd' : d ∈ (Subgroup.zpowers w : Set G) *
        (Subgroup.centralizer (A : Set G) : Set G) := by
      change d ∈ ((Subgroup.centralizer (A : Set G) ⊔ Subgroup.zpowers w :
        Subgroup G) : Set G) at hd
      rwa [hset] at hd
    rcases hd' with ⟨b, hb, c, hc, rfl⟩
    have hzc : ⁅z, c⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp hc z hz)
    rw [commutatorElement_mul_right_eq_mul_conj, hzc]
    simpa using Subgroup.commutator_mem_commutator hz hb
  simpa using hmap ⟨x, hx, rfl⟩

theorem Str86AbHyp.mem_centralizer_z2_of_odd
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) {w : G} (hwL : w ∈ L1 ⊔ S)
    (hwB : w ∈ bigB L1 L2 S) (hw : Odd (orderOf w))
    (htriv : ∀ x ∈ u3H L1 L2 S, w * x * w⁻¹ * x⁻¹ ∈ Q2 L1 L2 S) :
    w ∈ Subgroup.centralizer (Z2 L1 L2 S : Set G) := by
  classical
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have h2 : VL2 L2 := ⟨m, hI.hL2⟩
  obtain ⟨hZ1eq, -, -, -, hZ2CS⟩ :=
    str86_caseI_basics hI.hF hI.hSB h1 hI.hB2 h2 hI.hZI
  have hL1C1 : L1 ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (le_sup_left : L1 ≤ L1 ⊔ Q1 L1 L2 S).trans hI.hZI
  have hSC1 : S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
    rw [hZ1eq, Subgroup.le_centralizer_iff]
    exact (A4.omegaOneCenterOf_le_centerOf S).trans (A4.centerOf_le_centralizer S)
  have hwC1 : w ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
    (sup_le hL1C1 hSC1) hwL
  set Z : Subgroup G := Z2 L1 L2 S with hZdef
  have hSleH : S ≤ u3H L1 L2 S := str86_s_le_u3H hI.hF.toW hI.hSB hI.hm hI.hL2
  have hwNZ : w ∈ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef]
    exact bigB_le_normalizer_z2 L1 L2 S hwB
  have hSNZ : S ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef]
    exact hSleH.trans (str86_z2_normal_u3H L1 L2 S)
  have hZea : IsElemAbelian 2 Z := by
    rw [hZdef]
    exact CFSG.Quasithin.SmithC27.isElemAbelian_omegaOneCenterOf (Q2 L1 L2 S)
  have hQ2C : Q2 L1 L2 S ≤ Subgroup.centralizer (Z : Set G) := by
    rw [hZdef]
    exact CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf (P2 L1 L2 S)
  set W : Subgroup G := ⁅Z, Subgroup.zpowers w⁆ with hWdef
  have hSNW : S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hWdef]
    exact le_normalizer_commutator_zpowers_of_trivial_mod hZea hwNZ hSNZ hQ2C hSleH htriv
  have hZCS : Z ⊓ Subgroup.centralizer (S : Set G) = Z1 L1 L2 S := by
    rw [hZdef]
    exact hZ2CS
  have hC : Z ⊓ Subgroup.centralizer (S : Set G) ≤
      Subgroup.centralizer ({w} : Set G) := by
    rw [hZCS]
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hwC1 z hz
  have hWleZ : W ≤ Z := by
    rw [hWdef]
    exact CFSG.Goldschmidt.G75.commutator_zpowers_le_self hwNZ
  have hWbot : W = ⊥ :=
    eq_bot_of_isPGroup_le_commutator (A := Z) (I := W) (T := S) (W := W) (y := w)
      hZea hwNZ hw hI.hF.1.h1.pgroup hSNW hWleZ le_rfl hWdef hC
  have hZle : Z ≤ Subgroup.centralizer (Subgroup.zpowers w : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hWdef ▸ hWbot)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzC : z ∈ Subgroup.centralizer (Subgroup.zpowers w : Set G) := hZle hz
  exact (Subgroup.mem_centralizer_iff.mp hzC w (Subgroup.mem_zpowers w)).symm

end CFSG.Quasithin.Stroth

end
