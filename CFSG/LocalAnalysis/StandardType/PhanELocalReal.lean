module

public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

variable {K : Type} [Field K] [Finite K] (f : ℕ) [CharP K 2] {n : ℕ}

theorem exists_theta (hK : Nat.card K = (2 ^ f) ^ 2) : ∃ θ : K, θ + sg K f θ = 1 := by
  obtain ⟨θ, hθ⟩ := exists_sg_trace (K := K) (f := f) hK (a := 1) (by simp)
  exact ⟨θ, hθ⟩

private theorem plh_fun_add_eq_zero {a b : Fin n → K} : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    funext i
    exact CharTwo.add_eq_zero.mp (by simpa using congrFun h i)
  · intro h
    rw [h]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero (b i)

private theorem plh_sgv_mem {S : Submodule K (Fin n → K)} (hS : sgS K f n S = S) (s : ↥S) :
    sgv K f n (s : Fin n → K) ∈ S :=
  mem_sgS.mp (by rw [hS]; exact s.2)

private noncomputable def plh_trace {S : Submodule K (Fin n → K)} (hS : sgS K f n S = S) :
    ↥S →+ ↥S where
  toFun s := ⟨(s : Fin n → K) + sgv K f n (s : Fin n → K),
    S.add_mem s.2 (plh_sgv_mem (S := S) f hS s)⟩
  map_zero' := by
    apply Subtype.ext
    funext i
    simp
  map_add' s t := by
    apply Subtype.ext
    funext i
    simp only [Submodule.coe_add, Pi.add_apply, map_add]
    abel

private theorem plh_trace_apply {S : Submodule K (Fin n → K)} (hS : sgS K f n S = S) (s : ↥S) :
    ((plh_trace (S := S) f hS s : ↥S) : Fin n → K) =
      (s : Fin n → K) + sgv K f n (s : Fin n → K) := rfl

private noncomputable def plh_kerEquiv {S : Submodule K (Fin n → K)} (hS : sgS K f n S = S) :
    (plh_trace (S := S) f hS).ker ≃ {v : Fin n → K // v ∈ S ∧ sgv K f n v = v} where
  toFun s := ⟨(s.1 : Fin n → K), s.1.2, by
    have h : plh_trace (S := S) f hS s.1 = 0 := (AddMonoidHom.mem_ker).mp s.2
    have hc : (s.1 : Fin n → K) + sgv K f n (s.1 : Fin n → K) = 0 := by
      have h0 := congrArg (fun w : ↥S => (w : Fin n → K)) h
      rwa [plh_trace_apply f hS s.1] at h0
    exact (plh_fun_add_eq_zero.mp hc).symm⟩
  invFun v := ⟨⟨v.1, v.2.1⟩, (AddMonoidHom.mem_ker).mpr (by
    apply Subtype.ext
    show (v.1 : Fin n → K) + sgv K f n (v.1 : Fin n → K) = 0
    rw [v.2.2]
    exact plh_fun_add_eq_zero.mpr rfl)⟩
  left_inv s := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

private noncomputable def plh_rangeEquiv {S : Submodule K (Fin n → K)}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hS : sgS K f n S = S) :
    (plh_trace (S := S) f hS).range ≃ {v : Fin n → K // v ∈ S ∧ sgv K f n v = v} where
  toFun w := ⟨(w.1 : Fin n → K), w.1.2, by
    obtain ⟨s, hs⟩ := (AddMonoidHom.mem_range).mp w.2
    have hs' : (s : Fin n → K) + sgv K f n (s : Fin n → K) = (w.1 : Fin n → K) := by
      have h0 := congrArg (fun u : ↥S => (u : Fin n → K)) hs
      rwa [plh_trace_apply f hS s] at h0
    rw [← hs', map_add, sgv_sgv hK]
    abel⟩
  invFun v := ⟨⟨v.1, v.2.1⟩, (AddMonoidHom.mem_range).mpr (by
    obtain ⟨θ, hθ⟩ := exists_theta (K := K) f hK
    refine ⟨⟨θ • v.1, S.smul_mem θ v.2.1⟩, ?_⟩
    apply Subtype.ext
    show θ • (v.1 : Fin n → K) + sgv K f n (θ • v.1) = (v.1 : Fin n → K)
    rw [(sgv K f n).map_smulₛₗ θ v.1, v.2.2]
    change θ • (v.1 : Fin n → K) + sg K f θ • (v.1 : Fin n → K) = (v.1 : Fin n → K)
    rw [← add_smul, hθ, one_smul])⟩
  left_inv w := Subtype.ext rfl
  right_inv v := Subtype.ext rfl

theorem card_real_eq (hK : Nat.card K = (2 ^ f) ^ 2) (S : Submodule K (Fin n → K))
    (hS : sgS K f n S = S) :
    Nat.card {v : Fin n → K // v ∈ S ∧ sgv K f n v = v} = (2 ^ f) ^ finrank K S := by
  have hker : Nat.card (plh_trace (S := S) f hS).ker =
      Nat.card {v : Fin n → K // v ∈ S ∧ sgv K f n v = v} :=
    Nat.card_congr (plh_kerEquiv (S := S) f hS)
  have hrange : Nat.card (plh_trace (S := S) f hS).range =
      Nat.card {v : Fin n → K // v ∈ S ∧ sgv K f n v = v} :=
    Nat.card_congr (plh_rangeEquiv (S := S) f hK hS)
  have hprod : Nat.card (plh_trace (S := S) f hS).ker *
      Nat.card (plh_trace (S := S) f hS).range = Nat.card ↥S :=
    AddSubgroup.card_ker_mul_card_range (plh_trace (S := S) f hS)
  rw [hker, hrange] at hprod
  have hcardS : Nat.card ↥S = ((2 ^ f) ^ finrank K S) * ((2 ^ f) ^ finrank K S) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := S), hK]
    rw [← pow_mul, two_mul, pow_add]
  rw [hcardS] at hprod
  exact Nat.mul_self_inj.mp hprod

theorem card_real_le (hK : Nat.card K = (2 ^ f) ^ 2) (S : Submodule K (Fin n → K)) :
    Nat.card {v : Fin n → K // v ∈ S ∧ sgv K f n v = v} ≤
      (2 ^ f) ^ finrank K ↥(S ⊓ sgS K f n S) := by
  have hT : sgS K f n (S ⊓ sgS K f n S) = S ⊓ sgS K f n S := by
    rw [sgS_inf, sgS_sgS hK, inf_comm]
  have heq : Nat.card {v : Fin n → K // v ∈ S ∧ sgv K f n v = v} =
      Nat.card {v : Fin n → K // v ∈ S ⊓ sgS K f n S ∧ sgv K f n v = v} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun v => ?_))
    constructor
    · rintro ⟨hvS, hvσ⟩
      exact ⟨⟨hvS, mem_sgS.mpr (by rw [hvσ]; exact hvS)⟩, hvσ⟩
    · rintro ⟨⟨hvS, _⟩, hvσ⟩
      exact ⟨hvS, hvσ⟩
  rw [heq]
  exact le_of_eq (card_real_eq (K := K) f hK (S ⊓ sgS K f n S) hT)

end CFSG.ClassicalInvolution.Phan.PhanE

end
