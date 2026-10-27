module

public import CFSG.Monster.B.Dyadic.Elim
public import Certificates.Certificate3102

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native

theorem dim_eq : dim = 4371 := rfl

@[expose] def Bvec (t : ℕ) : Fin 4371 → ℤ := byteVec 4371 basisRowsK[t]!

@[expose] def rowLat : Submodule ℤ (Fin 4371 → ℤ) :=
  Submodule.span ℤ (Set.range fun t : Fin 4371 => Bvec t)

theorem Bvec_mem {t : ℕ} (ht : t < 4371) : Bvec t ∈ rowLat :=
  Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩

structure BasisFacts : Prop where
  pexp_le : ∀ i < 4371, diagExpK[i]! ≤ 7
  diag : ∀ i < 4371, (basisRowsK[i]!.get! i).toNat = 2 ^ diagExpK[i]!
  lower : ∀ i < 4371, ∀ k < i, basisRowsK[i]!.get! k = 0
  upper : ∀ i < 4371, ∀ k < 4371, i < k → (basisRowsK[i]!.get! k).toNat < 128

theorem basis_facts : BasisFacts := by
  obtain ⟨h1, h2, h3, h4, -⟩ := Certificates.certificate3102
  refine ⟨fun i hi => h1 ⟨i, hi⟩, fun i hi => ?_, fun i hi k hk => ?_, fun i hi k hk hik => ?_⟩
  · have := h2 ⟨i, hi⟩
    rw [Bz] at this
    exact_mod_cast this
  · have := h3 ⟨i, hi⟩ ⟨k, by omega⟩ hk
    rw [Bz] at this
    have e : (basisRowsK[i]!.get! k).toNat = 0 := by exact_mod_cast this
    exact UInt8.toNat_inj.1 (e.trans UInt8.toNat_zero.symm)
  · have := h4 ⟨i, hi⟩ ⟨k, hk⟩ hik
    rw [Bz] at this
    exact_mod_cast this

theorem sing_mem_rowLat : ∀ i < 4371, sing 4371 128 i ∈ rowLat := by
  intro i hi
  obtain ⟨c, hc⟩ := Certificates.certificate3102.2.2.2.2 ⟨i, hi⟩
  have e : sing 4371 128 i = ∑ t : Fin 4371, c t • Bvec t := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have := hc k
    change (if (k : ℕ) = i then (128 : ℤ) else 0) = ∑ t : Fin 4371, c t * Bz t k
    rw [this]
    by_cases h : (k : ℕ) = i
    · rw [ite_eq_left h, ite_eq_left (Fin.ext h)]
    · rw [ite_eq_right h, ite_eq_right (fun e => h (congrArg Fin.val e))]
  rw [e]
  exact rowLat.sum_mem fun t _ => rowLat.smul_mem _ (Bvec_mem t.2)

theorem getBytes_ofFn {m : ℕ} (f : Fin m → UInt8) {k : ℕ} (hk : k < m) :
    (ByteArray.mk (Array.ofFn f)).get! k = f ⟨k, hk⟩ := by
  simp only [ByteArray.get!]
  rw [getElem!_pos (Array.ofFn f) k (by simpa using hk), Array.getElem_ofFn]

theorem smul128_mem_rowLat (v : Fin 4371 → ℤ) :
    (128 : ℤ) • v ∈ rowLat :=
  smul_mem_of_sing sing_mem_rowLat v

end CFSG.Monster.B.Dyadic

end
