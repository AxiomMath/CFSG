module

public import CFSG.RankThree.PartOne.SLB4A.Sign
public import CFSG.LieType.Chevalley.PerfectSimpleRoot

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Exc

variable {τ : Tag} {K : Type} [Field K]

theorem dElt_mul_comm' (i j : Fin τ.rank) (t u : Kˣ) :
    dElt i t * dElt j u = dElt j u * dElt i t :=
  Subtype.ext (torusElt_mul_comm i j t u)

theorem dElt_neg_one_sq (i : Fin τ.rank) : dElt i (-1 : Kˣ) * dElt i (-1) = (1 : adjointGroup τ K) := by
  refine Subtype.ext ?_
  show torusElt τ K i (-1) * torusElt τ K i (-1) = 1
  rw [← torusElt_mul, show (-1 : Kˣ) * (-1) = 1 by simp, torusElt_one]

theorem dElt_pow_conj (i j : Fin τ.rank) (t : Kˣ) (n : ℕ) (c : K) :
    dElt i t ^ n * xElt j c * (dElt i t ^ n)⁻¹ =
      xElt j ((((t ^ τ.cartan i j : Kˣ) : K) ^ n) * c) := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    have h1 : dElt i t ^ (n + 1) * xElt j c * (dElt i t ^ (n + 1))⁻¹ =
        dElt i t ^ n * (dElt i t * xElt j c * (dElt i t)⁻¹) * (dElt i t ^ n)⁻¹ := by
      rw [pow_succ, _root_.mul_inv_rev]
      group
    rw [h1, dElt_mul_xElt_mul_inv, ih, pow_succ]
    congr 1
    ring

theorem xElt_injective (i : Fin τ.rank) : Function.Injective (xElt (τ := τ) (K := K) i) := by
  intro c c' h
  have h1 : (xUnit τ K i c : Module.End K (RootModule τ K)) = xUnit τ K i c' :=
    congrArg (fun g : adjointGroup τ K => ((g : ModGL τ K) : Module.End K (RootModule τ K))) h
  exact xOp_injective i h1

def Mult (j : Fin τ.rank) (Q : adjointGroup τ K) (m : K) : Prop :=
  ∀ c : K, Q * xElt j c * Q⁻¹ = xElt j (m * c)

theorem Mult_one (j : Fin τ.rank) : Mult (τ := τ) (K := K) j 1 1 := fun c => by simp

theorem Mult_mul {j : Fin τ.rank} {Q R : adjointGroup τ K} {m r : K} (hQ : Mult j Q m)
    (hR : Mult j R r) : Mult j (Q * R) (m * r) := fun c => by
  have : Q * R * xElt j c * (Q * R)⁻¹ = Q * (R * xElt j c * R⁻¹) * Q⁻¹ := by
    rw [_root_.mul_inv_rev]
    group
  rw [this, hR, hQ, mul_assoc]

theorem Mult_dElt_pow (i j : Fin τ.rank) (t : Kˣ) (n : ℕ) :
    Mult j (dElt i t ^ n) ((((t ^ τ.cartan i j : Kˣ) : K)) ^ n) := fun c =>
  dElt_pow_conj i j t n c

theorem eq_of_Mult_one {j : Fin τ.rank} {m : K} (h : Mult j (1 : adjointGroup τ K) m) : m = 1 := by
  have := h 1
  rw [one_mul, mul_one, inv_one, mul_one] at this
  exact (xElt_injective j this).symm

@[expose] def sgp (τ : Tag) (a : Fin 5 → Fin τ.rank) (k : Fin 5) (j : Fin τ.rank) : C2 :=
  if τ.cartan (a k) j % 2 = 0 then 1 else c2gen

theorem neg_one_zpow_eq_eps (m : ℤ) :
    (((-1 : Kˣ) ^ m : Kˣ) : K) = eps K (if m % 2 = 0 then 1 else c2gen) := by
  rcases Int.even_or_odd m with h | h
  · have h0 : m % 2 = 0 := Int.even_iff.1 h
    simp only [h0, reduceIte, eps_one, h.neg_one_zpow, Units.val_one]
  · have h0 : ¬ m % 2 = 0 := by
      have := Int.odd_iff.1 h
      omega
    simp only [h0, reduceIte, eps_gen, h.neg_one_zpow, Units.val_neg, Units.val_one]

theorem eps_pow (x : C2) (n : ℕ) : eps K x ^ n = eps K (x ^ n) := by
  induction n with
  | zero => simp [eps_one]
  | succ n ih => rw [pow_succ, ih, pow_succ, eps_mul]

theorem exists_two_pow_five_adjoint_odd (a : Fin 5 → Fin τ.rank) (hneg : (-1 : K) ≠ 1)
    (hcomb : ∀ v : V2 5, (∀ j : Fin τ.rank, sgp τ a 0 j ^ ex (v 0) * sgp τ a 1 j ^ ex (v 1) *
      sgp τ a 2 j ^ ex (v 2) * sgp τ a 3 j ^ ex (v 3) * sgp τ a 4 j ^ ex (v 4) = 1) → v = 1) :
    ∃ U : Subgroup (adjointGroup τ K), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  refine exists_two_pow_five_of_commInvol (fun k => dElt (a k) (-1 : Kˣ))
    (fun i j => dElt_mul_comm' _ _ _ _) (fun k => dElt_neg_one_sq _) ?_
  intro v hv
  refine hcomb v fun j => ?_
  have hM := Mult_mul (Mult_mul (Mult_mul (Mult_mul (Mult_dElt_pow (a 0) j (-1 : Kˣ) (ex (v 0)))
    (Mult_dElt_pow (a 1) j (-1 : Kˣ) (ex (v 1)))) (Mult_dElt_pow (a 2) j (-1 : Kˣ) (ex (v 2))))
    (Mult_dElt_pow (a 3) j (-1 : Kˣ) (ex (v 3)))) (Mult_dElt_pow (a 4) j (-1 : Kˣ) (ex (v 4)))
  rw [hv] at hM
  have h1 := eq_of_Mult_one hM
  simp only [neg_one_zpow_eq_eps, eps_pow, ← eps_mul] at h1
  exact eps_inj hneg (h1.trans (eps_one K).symm)

end Exc

end CFSG.RankThree.PartOne.SLB4A
