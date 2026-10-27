module

public import CFSG.Quasithin.AppendixH.H9.H92.RadHom

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_radDiffSpace {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (A' : Subgroup (GL (Fin n) (ZMod 2))) (hA' : A' ≤ RadMat n D) :
    ∃ 𝒜 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ N, N ∈ 𝒜 ↔ ∃ B ∈ A', (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 = N) ∧
      𝒜 ≤ radNil n D ∧ Nat.card 𝒜 = Nat.card A' := by
  let S : Set (Matrix (Fin n) (Fin n) (ZMod 2)) :=
    {N | ∃ B ∈ A', (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 = N}
  let 𝒜 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)) :=
    { carrier := S,
      add_mem' := (by
        rintro N N' ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
        have hBB' : ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *
            ((B' : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) = 0 :=
          radNil_mul_radNil ((mem_radMat_iff_sub_mem_radNil B).1 (hA' hB))
            ((mem_radMat_iff_sub_mem_radNil B').1 (hA' hB'))
        refine ⟨B * B', A'.mul_mem hB hB', ?_⟩
        rw [Units.val_mul]
        have e : (B : Matrix (Fin n) (Fin n) (ZMod 2)) *
              (B' : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 =
            ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *
                ((B' : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) +
              ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) +
                ((B' : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) := by
          noncomm_ring
        rw [e, hBB', zero_add]),
      zero_mem' := ⟨1, A'.one_mem, by rw [Units.val_one, sub_self]⟩,
      smul_mem' := (by
        rintro c N ⟨B, hB, rfl⟩
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · exact ⟨1, A'.one_mem, by rw [zero_smul, Units.val_one, sub_self]⟩
        · exact ⟨B, hB, by rw [one_smul]⟩) }
  refine ⟨𝒜, ?_, ?_, ?_⟩
  · intro N; exact Iff.rfl
  · intro N hN
    obtain ⟨B, hB, rfl⟩ := hN
    exact (mem_radMat_iff_sub_mem_radNil B).1 (hA' hB)
  · let φ : A' → 𝒜 := fun B =>
      ⟨((B : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1,
        ⟨(B : GL (Fin n) (ZMod 2)), B.2, rfl⟩⟩
    have hinj : Function.Injective φ := by
      intro B B' h
      apply Subtype.ext
      apply Units.ext
      have hval : (((B : A') : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 =
          (((B' : A') : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 :=
        congrArg Subtype.val h
      have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) (ZMod 2) => M + 1) hval
      simpa using h2
    have hsurj : Function.Surjective φ := by
      intro N
      obtain ⟨B, hB, hBN⟩ := N.2
      exact ⟨⟨B, hB⟩, Subtype.ext hBN⟩
    exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm

private theorem five_le_finrank_of_le_card_aux {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (h : 32 ≤ Nat.card V) : 5 ≤ Module.finrank (ZMod 2) V := by
  by_contra hlt
  rw [not_le] at hlt
  have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcard] at h
  have h2 : 2 ^ Module.finrank (ZMod 2) V ≤ 16 := by
    calc 2 ^ Module.finrank (ZMod 2) V ≤ 2 ^ 4 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num
  omega

theorem five_le_finrank_of_le_card {n : ℕ}
    (𝒜 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2))) (h : 32 ≤ Nat.card 𝒜) :
    5 ≤ Module.finrank (ZMod 2) 𝒜 :=
  five_le_finrank_of_le_card_aux h

theorem comap_pairActN_le_radMat {n : ℕ} {U : Subgroup (PairN n)}
    {A : Subgroup (MulAut (PairN n))} (hA : A ≤ RadV1 n U) :
    A.comap (pairActN n) ≤ RadMat n (v1Space n U) := by
  intro B hB
  rw [Subgroup.mem_comap] at hB
  have hmem : pairActN n B ∈ RadV1 n U := hA hB
  rw [RadV1, Subgroup.mem_map] at hmem
  obtain ⟨B₀, hB₀, hEq⟩ := hmem
  have hBB₀ : B = B₀ := (pairActN_injective hEq).symm
  rwa [hBB₀]

theorem card_comap_pairActN {n : ℕ} {A : Subgroup (MulAut (PairN n))} (hA : A ≤ Lg n) :
    Nat.card (A.comap (pairActN n)) = Nat.card A := by
  calc Nat.card (A.comap (pairActN n))
      = Nat.card ((A.comap (pairActN n)).map (pairActN n)) :=
        (Subgroup.card_map_of_injective (pairActN_injective (n := n))).symm
    _ = Nat.card A := by
        rw [Subgroup.map_comap_eq_self (show A ≤ (pairActN n).range from hA)]

theorem mem_iff_exists_comap_pairActN {n : ℕ} {A : Subgroup (MulAut (PairN n))} (hA : A ≤ Lg n)
    (g : MulAut (PairN n)) :
    g ∈ A ↔ ∃ B ∈ A.comap (pairActN n), pairActN n B = g := by
  constructor
  · intro hg
    obtain ⟨B, rfl⟩ : ∃ B, pairActN n B = g := by
      rw [← mem_Lg_iff]
      exact hA hg
    exact ⟨B, Subgroup.mem_comap.mpr hg, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact Subgroup.mem_comap.mp hB

end CFSG.ASVolI.ChH
