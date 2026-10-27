module

public import CFSG.Sporadic.HNSchreier.ArchData
public import CFSG.Sporadic.HNSchreier.StrongSpec
public import Certificates.Certificate2095
public import Certificates.Certificate2102

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem arch_eq_parts (i : ℕ) (hi : i < 1140000) :
    le32 archBytes (12 + 8 * i) = ap alphaT i ∧ le32 archBytes (12 + 8 * i + 4) = ap betaT i := by
  have h := arch_eq_cert
  unfold archEqChecks at h
  rw [← archBytes_eq] at h
  have := (allIn_eq_true.1 h) i (Nat.zero_le _) hi
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem qArch_zero
    (i : X) : ((qArch 0 i : X) : ℕ) = f0 i := by
  have hi : (i : ℕ) < 1140000 := i.isLt
  rw [f0_eq hi, ← (arch_eq_parts i hi).1]
  simp [qArch, qRaw]

theorem qArch_one
    (i : X) : ((qArch 1 i : X) : ℕ) = f1 i := by
  have hi : (i : ℕ) < 1140000 := i.isLt
  rw [f1_eq hi, ← (arch_eq_parts i hi).2]
  simp [qArch, qRaw]

theorem qArch_zero_eq :
    qArch 0 = a0 :=
  funext fun i => Fin.ext ((qArch_zero i).trans (a0_apply i).symm)

theorem qArch_one_eq : qArch 1 = a1 :=
  funext fun i => Fin.ext ((qArch_one i).trans (a1_apply i).symm)

theorem ctuc_hn_archived_arrays_equal_certified_action :
    (∀ i : X, ((qArch 0 i : X) : ℕ) = f0 i ∧ ((qArch 1 i : X) : ℕ) = f1 i) ∧
    (∃ σ₀ σ₁ : Equiv.Perm X, ⇑σ₀ = qArch 0 ∧ ⇑σ₁ = qArch 1) ∧
    (∀ i : X, qArch 0 i = aJ • i ∧ qArch 1 i = bJ • i) ∧ FaithfulSMul JH X ∧
    ∀ w : List (Fin 2 × Bool), ∀ i : X,
      Quiver.SchreierGraph.evalWord ![aJ, bJ] w • i =
        Quiver.SchreierGraph.evalWord ![a0, a1] w i := by
  refine ⟨fun i => ⟨qArch_zero i, qArch_one i⟩, ⟨a0, a1, qArch_zero_eq.symm, qArch_one_eq.symm⟩,
    fun i => ⟨by rw [qArch_zero_eq]; rfl, by rw [qArch_one_eq]; rfl⟩, hns_faithful, fun w i => ?_⟩
  have e := map_evalWord' permHom ![aJ, bJ] w
  have e2 : (permHom ∘ ![aJ, bJ]) = ![a0, a1] := by
    funext s
    fin_cases s <;> rfl
  rw [e2] at e
  rw [← e]
  rfl

end CFSG.Sporadic.HNSchreier
