module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7

public section

namespace CFSG.Quasithin.H13.FiveNorm

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L

theorem fiveInner_alt7 : FiveInner (alternatingGroup (Fin 7)) := by
  intro α hα
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (n := 7) (Or.inr le_rfl) α
  have hpow : ∀ k : ℕ, ∀ g : alternatingGroup (Fin 7),
      (((α ^ k) g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = σ ^ k * g * (σ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, hσ, ih, pow_succ']
      group
  have hsign : Equiv.Perm.sign (σ ^ 6) = 1 := by
    rw [map_pow, show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Int.units_sq, one_pow]
  have h6 : α ^ 6 = α := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hα, one_mul]
  refine ⟨⟨σ ^ 6, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, MulEquiv.ext fun g => ?_⟩
  apply Subtype.ext
  calc ((α g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))
      = (((α ^ 6) g : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by rw [h6]
    _ = σ ^ 6 * g * (σ ^ 6)⁻¹ := hpow 6 g
    _ = _ := rfl

theorem noFiveOver_alt7 :
    NoFiveOver (alternatingGroup (Fin 7)) := by
  intro S H hS hSH hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS8 : Nat.card S = 2 ^ 3 :=
    card_eq_of_isSylowTwoOf_top hS (m := 315) (by rw [Seven.card_A7s]; norm_num) (by decide)
  obtain ⟨h1, h2⟩ := isSylowTwoOf_top_index hS
  obtain ⟨h3, h4⟩ := isSylowTwoOf_top_index Seven.isSylowTwoOf_T7
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (h1.toSylow h2)
    (h3.toSylow h4)
  have hTM : Seven.T7 ≤ H.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    have hx' : x ∈ ((g • h1.toSylow h2 : Sylow 2 (alternatingGroup (Fin 7))) :
        Subgroup (alternatingGroup (Fin 7))) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨y, hSH hy, rfl⟩
  have hM : Nat.card (H.map (MulAut.conj g).toMonoidHom) = 40 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, hS8]
    norm_num
  obtain ⟨i, hi, hiZ⟩ := Seven.overgroup_Z hTM
  have h5 := Seven.card_Z hi
  rw [← hiZ, Seven.card_map_subtype, hM] at h5
  interval_cases i <;> simp at h5

theorem fiveRigid_alt7 :
    FiveRigid (alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨center_eq_bot_of_card_not_prime (by rw [Seven.card_A7s]; norm_num), fiveInner_alt7,
    noFiveOver_alt7⟩

end CFSG.Quasithin.H13.FiveNorm
