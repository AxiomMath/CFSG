module

public import CFSG.Quasithin.Background.H11Defs
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusRep
public import CFSG.Quasithin.Background.HSU3Borel

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.SU3 CFSG.Quasithin.SteinbergCB
  CFSG.Quasithin.G11.Harris.L2 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def barR (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : K →+* K :=
  (bar n : K ≃+* K).toRingHom

theorem barR_apply (x : K) : barR n K x = bar n x := rfl

theorem barR_inv (hK : Nat.card K = (2 ^ n) ^ 2) (x : K) :
    barR n K (barR n K x) = x := bar_bar hK x

abbrev Fq (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Type :=
  ↥(frobFixed (barR n K))

@[expose] def e4 : QIdx ≃ Fin 4 where
  toFun
    | .inl _ => 0
    | .inr (.inl _) => 1
    | .inr (.inr j) => if j = 0 then 2 else 3
  invFun i := match i with
    | 0 => .inl 0
    | 1 => .inr (.inl 0)
    | 2 => .inr (.inr 0)
    | 3 => .inr (.inr 1)
  left_inv i := by
    rcases i with i | i | i
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rfl
    · obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rfl
    · fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

@[expose] noncomputable def theta (hK : Nat.card K = (2 ^ n) ^ 2) {ω : K}
    (hω : barR n K ω ≠ ω) :
    (Fin 4 → Fq n K) ≃ₗ[Fq n K] twistedForm (barR n K) :=
  (LinearEquiv.funCongrLeft (Fq n K) (Fq n K) e4).trans
    (twistCoords (barR_inv hK) hω).symm

theorem theta_apply (hK : Nat.card K = (2 ^ n) ^ 2) {ω : K} (hω : barR n K ω ≠ ω)
    (x : Fin 4 → Fq n K) :
    theta hK hω x = coordInv (barR_inv hK) ω (fun i => x (e4 i)) := rfl

theorem twistedDet_theta (hK : Nat.card K = (2 ^ n) ^ 2) {ω : K} (hω : barR n K ω ≠ ω)
    (hb : coordB (barR_inv hK) ω = 1) (x : Fin 4 → Fq n K) :
    twistedDet (barR n K) (theta hK hω x) =
      CFSG.Quasithin.H11Proof.orthMinus (Fq n K) (coordC (barR_inv hK) ω) x := by
  rw [theta_apply, twistedDet_coordInv (barR_inv hK) ω CharTwo.two_eq_zero, statedQuadMinus_two, hb]
  simp [CFSG.Quasithin.H11Proof.orthMinus, e4]

theorem exists_trace_one (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ ω : K, ω + bar n ω = 1 := by
  obtain ⟨z, hz⟩ := exists_bar_ne hn hK
  have ht : z + bar n z ≠ 0 := by
    intro h
    apply hz
    have : bar n z = -z := eq_neg_of_add_eq_zero_right h
    rw [this, CharTwo.neg_eq]
  have htbar : bar n (z + bar n z) = z + bar n z := by
    rw [map_add, bar_bar hK, add_comm]
  refine ⟨z / (z + bar n z), ?_⟩
  rw [map_div₀, htbar, ← add_div, div_self ht]

theorem card_Fq (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) : Nat.card (Fq n K) = 2 ^ n := by
  rw [← card_fixed hn hK]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [mem_frobFixed]; rfl)

theorem barR_ne_of_trace (hK : Nat.card K = (2 ^ n) ^ 2) {ω : K} (hω : ω + bar n ω = 1) :
    barR n K ω ≠ ω := by
  intro h
  have h1 : bar n ω = ω := h
  rw [h1] at hω
  have : (2 : K) * ω = 1 := by rw [two_mul]; exact hω
  rw [CharTwo.two_eq_zero, zero_mul] at this
  exact zero_ne_one this

@[expose] def conjLin {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) : (V ≃ₗ[R] V) ≃* (W ≃ₗ[R] W) where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by
    ext v
    simp
  right_inv h := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp

theorem conjLin_apply {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (e : V ≃ₗ[R] W) (g : V ≃ₗ[R] V) (w : W) :
    conjLin e g w = e (g (e.symm w)) := rfl

theorem map_isometryGroup_theta (hK : Nat.card K = (2 ^ n) ^ 2) {ω : K}
    (hω : barR n K ω ≠ ω) (hb : coordB (barR_inv hK) ω = 1) :
    (CFSG.Quasithin.H11Proof.isometryGroup (Fq n K)
        (CFSG.Quasithin.H11Proof.orthMinus (Fq n K) (coordC (barR_inv hK) ω))).map
      (conjLin (theta hK hω)).toMonoidHom =
    isometryGroup (twistedDet (barR n K)) := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩ y
    obtain ⟨x, rfl⟩ := (theta hK hω).surjective y
    rw [MulEquiv.coe_toMonoidHom, conjLin_apply, LinearEquiv.symm_apply_apply,
      twistedDet_theta hK hω hb, twistedDet_theta hK hω hb]
    exact hg x
  · intro hh
    refine ⟨(conjLin (theta hK hω)).symm h, ?_, by simp⟩
    intro x
    have h1 := hh (theta hK hω x)
    have e1 : (conjLin (theta hK hω)).symm h x =
        (theta hK hω).symm (h (theta hK hω x)) := rfl
    rw [e1]
    have h2 := twistedDet_theta hK hω hb ((theta hK hω).symm (h (theta hK hω x)))
    rw [LinearEquiv.apply_symm_apply] at h2
    have h3 := twistedDet_theta hK hω hb x
    rw [h1] at h2
    rw [← h3, ← h2]

theorem herm_omega (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {ω : K}
    (hω : barR n K ω ≠ ω) (hb : coordB (barR_inv hK) ω = 1) :
    (∀ A : SL(2, K), ∃ φ ∈ CFSG.Quasithin.H11Proof.omegaFour (Fq n K)
        (CFSG.Quasithin.H11Proof.orthMinus (Fq n K) (coordC (barR_inv hK) ω)),
      ∀ x : Fin 4 → Fq n K, (theta hK hω).symm (twistRep (barR_inv hK) A (theta hK hω x)) =
        Multiplicative.toAdd (φ (Multiplicative.ofAdd x))) ∧
    (∀ φ ∈ CFSG.Quasithin.H11Proof.omegaFour (Fq n K)
        (CFSG.Quasithin.H11Proof.orthMinus (Fq n K) (coordC (barR_inv hK) ω)),
      ∃ A : SL(2, K), ∀ x : Fin 4 → Fq n K,
        (theta hK hω).symm (twistRep (barR_inv hK) A (theta hK hω x)) =
          Multiplicative.toAdd (φ (Multiplicative.ofAdd x))) := by
  have hrange := twistRep_range_eq (F := K) (a := n) (σ := barR n K) hn hK
    (fun x => bar_apply x)
  have hcomm : ⁅isometryGroup (twistedDet (barR n K)), isometryGroup (twistedDet (barR n K))⁆ =
      (⁅CFSG.Quasithin.H11Proof.isometryGroup (Fq n K)
          (CFSG.Quasithin.H11Proof.orthMinus (Fq n K) (coordC (barR_inv hK) ω)),
        CFSG.Quasithin.H11Proof.isometryGroup (Fq n K)
          (CFSG.Quasithin.H11Proof.orthMinus (Fq n K) (coordC (barR_inv hK) ω))⁆).map
        (conjLin (theta hK hω)).toMonoidHom := by
    rw [Subgroup.map_commutator, map_isometryGroup_theta hK hω hb]
  have key : ∀ (g : (Fin 4 → Fq n K) ≃ₗ[Fq n K] (Fin 4 → Fq n K)) (x : Fin 4 → Fq n K),
      (theta hK hω).symm (conjLin (theta hK hω) g (theta hK hω x)) = g x := by
    intro g x
    rw [conjLin_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  refine ⟨fun A => ?_, fun φ hφ => ?_⟩
  · have hA : twistRep (barR_inv hK) A ∈ (twistRep (barR_inv hK)).range := ⟨A, rfl⟩
    rw [hrange, hcomm] at hA
    obtain ⟨g, hg, hgA⟩ := hA
    refine ⟨CFSG.Quasithin.H11Proof.linToMulAut (Fq n K) (Fin 4 → Fq n K) g, ⟨g, hg, rfl⟩, ?_⟩
    intro x
    have hx : twistRep (barR_inv hK) A = conjLin (theta hK hω) g := hgA.symm
    rw [hx, key]
    rfl
  · obtain ⟨g, hg, rfl⟩ := hφ
    have hg' : conjLin (theta hK hω) g ∈ (twistRep (barR_inv hK)).range := by
      rw [hrange, hcomm]
      exact ⟨g, hg, rfl⟩
    obtain ⟨A, hA⟩ := hg'
    refine ⟨A, fun x => ?_⟩
    rw [hA, key]
    rfl

noncomputable abbrev scalF (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Fq n K →+* K :=
  (frobFixed (barR n K)).subtype

theorem scalF_apply (c : Fq n K) : scalF n K c = (c : K) := rfl

theorem bar_scalF (c : Fq n K) : bar n (scalF n K c) = scalF n K c :=
  CFSG.Quasithin.SteinbergCB.mem_frobFixed.1 c.2

end CFSG.Quasithin.RonanH44
