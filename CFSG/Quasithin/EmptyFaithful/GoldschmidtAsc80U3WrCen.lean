module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3WrCom

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.B6 CFSG.QuasithinUnique

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] {hF : Nat.card F = p ^ 2}

theorem val_inv_eq_neg_u {u : ↥(muU hF)} (hi : ((u : Fˣ) : F) ^ 2 = -1) :
    (((u⁻¹ : ↥(muU hF)) : Fˣ) : F) = -((u : Fˣ) : F) := by
  have h : ((u⁻¹ : ↥(muU hF)) : Fˣ) = (u : Fˣ)⁻¹ := rfl
  rw [h, Units.val_inv_eq_inv_val]
  exact inv_eq_of_mul_eq_one_right (by linear_combination -hi)

theorem mem_diagU_of_commute_xOU (hp2 : p ≠ 2) [Finite F] {u : ↥(muU hF)}
    (hi : ((u : Fˣ) : F) ^ 2 = -1) {g : SU3F p F}
    (h : piU p F g * piU p F (xOU hF u) = piU p F (xOU hF u) * piU p F g) : g ∈ diagU hF := by
  obtain ⟨q, hqdef⟩ : ∃ q : SU3F p F, q = g * xOU hF u * g⁻¹ * (xOU hF u)⁻¹ := ⟨_, rfl⟩
  have h1 : piU p F q = 1 := by
    rw [hqdef]
    simp only [map_mul, map_inv]
    rw [h]
    group
  obtain ⟨r, hr3, hr⟩ := exists_scalar_of_mem_ker hF (show q ∈ (piU p F).ker from h1)
  have hq : q * xOU hF u * g = g * xOU hF u := by
    rw [hqdef]
    group
  have hm := congrArg matU hq
  simp only [matU_mul] at hm
  rw [hr, matU_xOU, val_inv_eq_neg_u hi] at hm
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ :=
    offdiag_zero_of_scalar_commute (two_ne_zero_u hp2 hF) hi hr3 hm
  exact ⟨h01, h02, h10, h12, h20, h21⟩

theorem flipU_mul_self (hF : Nat.card F = p ^ 2) : flipU hF * flipU hF = 1 := by
  apply ext_matU
  rw [matU_mul, matU_flipU, matU_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [flipMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem flipU_inv (hF : Nat.card F = p ^ 2) : (flipU hF)⁻¹ = flipU hF :=
  inv_eq_of_mul_eq_one_right (flipU_mul_self hF)

theorem flipU_conj_mem {d : SU3F p F} (hd : d ∈ diagU hF) : flipU hF * d * flipU hF ∈ diagU hF := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [matU_mul]
     simp only [Matrix.mul_apply, Fin.sum_univ_three]
     simp [matU_flipU, flipMat, d1, d2, d3, d4, d5, d6])

theorem flipU_mem_normalizer (hF : Nat.card F = p ^ 2) :
    flipU hF ∈ Subgroup.normalizer (diagU hF : Set (SU3F p F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [flipU_inv]
  refine ⟨fun hh => flipU_conj_mem hh, fun hh => ?_⟩
  have hc := flipU_conj_mem hh
  have e : flipU hF * (flipU hF * h * flipU hF) * flipU hF = h := by
    calc flipU hF * (flipU hF * h * flipU hF) * flipU hF
        = (flipU hF * flipU hF) * h * (flipU hF * flipU hF) := by group
      _ = h := by rw [flipU_mul_self]; simp
  rwa [e] at hc

theorem piU_flipU_mem_normalizer (hF : Nat.card F = p ^ 2) :
    piU p F (flipU hF) ∈ Subgroup.normalizer (diagCU hF : Set (PSU3F p F)) :=
  Subgroup.le_normalizer_map (piU p F) ⟨flipU hF, flipU_mem_normalizer hF, rfl⟩

theorem comap_piU_leviCU_wr (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    (leviCU hF).comap (piU p F) = leviU hF :=
  Subgroup.comap_map_eq_self (ker_piU_le_leviU hp2 hF)

theorem piU_flipU_not_mem_leviCU (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) :
    piU p F (flipU hF) ∉ leviCU hF := fun h => by
  have hc : flipU hF ∈ (leviCU hF).comap (piU p F) := h
  rw [comap_piU_leviCU_wr hp2 hF] at hc
  exact flipU_not_mem_leviU hp2 hF hc

theorem centralizer_commutator_eq_diagCU (hp2 : p ≠ 2) [Finite F] {u : ↥(muU hF)}
    (hi : ((u : Fˣ) : F) ^ 2 = -1) (hu4 : u ^ 4 = 1) {U : Subgroup (PSU3F p F)}
    (hE : evenCU hF ≤ U) (hUm : U ≤ monoCU hF) (hUD : ¬ U ≤ diagCU hF) :
    Subgroup.centralizer ((⁅U, U⁆ : Subgroup (PSU3F p F)) : Set (PSU3F p F)) = diagCU hF := by
  apply le_antisymm
  · intro g hg
    obtain ⟨g, rfl⟩ := piU_surjective g
    have h := Subgroup.mem_centralizer_iff.mp hg _ (piU_xOU_mem_commutator hu4 hE hUm hUD)
    exact ⟨g, mem_diagU_of_commute_xOU hp2 hi h.symm, rfl⟩
  · intro g hg
    exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
      diagCU_comm (commutator_le_diagCU hUm hh) hg

end CFSG.Quasithin.E2P.Asc80
