module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFusPar
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutKAux

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.QuasithinUnique CFSG.GH74.GLS.Stage4.Hex

section Fusion


variable {K : Type} [Field K] [Finite K] [CharP K 2] {A : LieAmalgamExt (C K)}

theorem fusion_of_gen {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {N N' : Subgroup ↥A.K}
    (hN : ∀ x : ↥A.K, x ∈ N ↔ ∃ g ∈ Pmin K ⟨1, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ)
    (hN' : ∀ x : ↥A.K, x ∈ N' ↔ ∃ g ∈ Pmin K ⟨0, by decide⟩, ∃ σ ∈ Fz A,
      (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ) :
    ∀ x ∈ outS (h.inn_le_K hn hK), orderOf x = 2 → ∃ i ∈ outI (h.inn_le_K hn hK),
      (∃ m ∈ N, m * x * m⁻¹ = i) ∨ (∃ m ∈ N', m * x * m⁻¹ = i) := by
  have hgen := h.inn_le_K hn hK
  have hinj : Function.Injective (iK A hgen) := iK_injective A hgen center_C_eq_bot'
  intro x hx hord
  obtain ⟨u, hu, hxu⟩ := (mem_outS_iff hgen x).1 hx
  have hx' : x = iK A hgen u := Subtype.ext hxu
  have hord' : orderOf u = 2 := by
    rw [← orderOf_injective (iK A hgen) hinj u, ← hx']
    exact hord
  have hsq : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hord', pow_two] at this
  have hne : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord'
    exact absurd hord' (by norm_num)
  obtain ⟨i, hi, hmn⟩ := fusion_U u hu hsq hne
  refine ⟨iK A hgen i, ?_, ?_⟩
  · rw [mem_outI_iff]
    exact ⟨i, by simpa using hi, rfl⟩
  · rcases hmn with ⟨m, hm, hmu⟩ | ⟨m, hm, hmu⟩
    · refine Or.inl ⟨iK A hgen m, (hN _).2 ⟨m, hm, 1, Subgroup.one_mem _, ?_⟩, ?_⟩
      · rw [iK_coe, map_one, mul_one]
      · rw [hx', ← map_mul, ← map_inv, ← map_mul, hmu]
    · refine Or.inr ⟨iK A hgen m, (hN' _).2 ⟨m, hm, 1, Subgroup.one_mem _, ?_⟩, ?_⟩
      · rw [iK_coe, map_one, mul_one]
      · rw [hx', ← map_mul, ← map_inv, ← map_mul, hmu]

end Fusion

end CFSG.Quasithin.H13.F431.G2.OutK
