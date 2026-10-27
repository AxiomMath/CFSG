module

public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def IsTv (σ : K ≃+* K) (t : SUid σ n) (a : Fin n → K) (c : K) : Prop :=
  ∀ v, t • v = v + (c * herm σ a v) • a

theorem IsTv.conj {t : SUid σ n} {a : Fin n → K} {c : K} (h : IsTv σ t a c) (g : SUid σ n) :
    IsTv σ (g * t * g⁻¹) (g • a) c := fun v => conj_smul_of_tv g t h v

theorem exists_isTv (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) : ∃ t : SUid σ n, IsTv σ t a c :=
  ⟨tv hσ ha hc, tv_smul hσ ha hc⟩

theorem IsTv.unique {t t' : SUid σ n} {a : Fin n → K} {c : K} (h : IsTv σ t a c)
    (h' : IsTv σ t' a c) : t = t' :=
  ext_smul σ fun v => by rw [h v, h' v]

theorem isTv_smul_vec {t : SUid σ n} {a : Fin n → K} {c lam : K} :
    IsTv σ t (lam • a) c ↔ IsTv σ t a (c * (σ lam * lam)) := by
  unfold IsTv
  refine forall_congr' fun v => ?_
  rw [herm_smul_left, smul_smul]
  have : c * (σ lam * herm σ a v) * lam = c * (σ lam * lam) * herm σ a v := by ring
  rw [this]

theorem IsTv.one {a : Fin n → K} : IsTv σ (1 : SUid σ n) a 0 := by
  intro v
  rw [one_smul, zero_mul, zero_smul, add_zero]

end CFSG.RankThree.PartOne.SEITZ2
