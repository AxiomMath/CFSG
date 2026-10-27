module

public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

namespace ThreeOne

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {α : Ω}

private theorem factorial_factorization_two_eq_pred (n : ℕ) (h : Odd n) :
    (n.factorial).factorization 2 = ((n - 1).factorial).factorization 2 := by
  have hn : n ≠ 0 := fun h0 => Nat.not_odd_zero (h0 ▸ h)
  have h2n : ¬2 ∣ n := h.not_two_dvd_nat
  calc
    (n.factorial).factorization 2
        = (n * (n - 1).factorial).factorization 2 := by
          rw [Nat.mul_factorial_pred hn]
    _ = (n.factorization + ((n - 1).factorial).factorization) 2 := by
          rw [Nat.factorization_mul hn (Nat.factorial_ne_zero _)]
    _ = ((n - 1).factorial).factorization 2 := by
          simp [Nat.factorization_eq_zero_of_not_dvd h2n]

theorem card_subtype_ne : Fintype.card {x // x ≠ α} = Fintype.card Ω - 1 := by
  rw [Fintype.card_subtype_compl (· = α), Fintype.card_subtype_eq]

theorem range_ofSubtype_eq_stabilizer :
    (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω).range = MulAction.stabilizer (Perm Ω) α := by
  ext g
  rw [CFSG.ComponentClassification.SymmetricLocal.mem_range_ofSubtype_iff]
  simp only [not_not]
  constructor
  · intro hg
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
    exact hg α rfl
  · intro hg x hx
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hg
    rw [hx]
    exact hg

theorem map_comap_ofSubtype_eq {K : Subgroup (Perm Ω)}
    (hK : K ≤ MulAction.stabilizer (Perm Ω) α) :
    (K.comap (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω)).map Perm.ofSubtype = K := by
  rw [Subgroup.map_comap_eq, range_ofSubtype_eq_stabilizer, inf_eq_right.mpr hK]

theorem map_comap_ofSubtype_eq_inf (H : Subgroup (Perm Ω)) :
    (H.comap (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω)).map Perm.ofSubtype =
      H ⊓ MulAction.stabilizer (Perm Ω) α := by
  rw [Subgroup.map_comap_eq, range_ofSubtype_eq_stabilizer, inf_comm]

theorem alternatingGroup_le_comap_ofSubtype {H : Subgroup (Perm Ω)}
    (hA : alternatingGroup Ω ≤ H) :
    alternatingGroup {x // x ≠ α} ≤ H.comap (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω) := by
  intro f hf
  apply hA
  rw [Perm.mem_alternatingGroup] at hf ⊢
  rwa [Perm.sign_ofSubtype]

theorem eq_alternatingGroup_of_comap_ofSubtype_eq (h3 : 3 ≤ Fintype.card Ω)
    {H : Subgroup (Perm Ω)} (hA : alternatingGroup Ω ≤ H)
    (h : H.comap (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω) =
      alternatingGroup {x // x ≠ α}) :
    H = alternatingGroup Ω := by
  rcases CFSG.ComponentClassification.SymmetricLocal.eq_alternatingGroup_or_eq_top hA with hH | hH
  · exact hH
  · exfalso
    have htop : alternatingGroup {x // x ≠ α} = ⊤ := by
      rw [← h, hH, Subgroup.comap_top]
    have hcard : 1 < Fintype.card {x // x ≠ α} := by
      rw [card_subtype_ne]
      exact lt_of_lt_of_le (by norm_num) (Nat.le_sub_one_of_lt (Nat.lt_of_succ_le h3))
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hcard
    exact CFSG.ComponentClassification.SymmetricLocal.alternatingGroup_ne_top hab htop

theorem exists_ofSubtype_eq {σ : Perm Ω} (hα : σ α = α) :
    ∃ σ' : Perm {x // x ≠ α}, Perm.ofSubtype σ' = σ := by
  have h : ∀ x, (σ x ≠ α) ↔ (x ≠ α) := by
    intro x
    constructor
    · intro hx hxα
      exact hx (by rw [hxα, hα])
    · intro hx hσ
      exact hx (σ.injective (hσ.trans hα.symm))
  exact ⟨σ.subtypePerm h,
    Perm.ofSubtype_subtypePerm h (fun x hx hxα => hx (by rw [hxα, hα]))⟩

theorem comap_centralizer_ofSubtype (σ' : Perm {x // x ≠ α}) :
    (Subgroup.centralizer {Perm.ofSubtype σ'}).comap
        (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω) =
      Subgroup.centralizer {σ'} := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← map_mul, ← map_mul] at h
    exact Perm.ofSubtype_injective h
  · intro h
    rw [← map_mul, ← map_mul, h]

theorem isSylowIn_comap_ofSubtype {T : Subgroup (Perm Ω)} (hT : IsSylowIn 2 T ⊤)
    (hTα : T ≤ MulAction.stabilizer (Perm Ω) α) (hodd : Odd (Fintype.card Ω)) :
    IsSylowIn 2 (T.comap (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω)) ⊤ := by
  refine isSylowIn_of_card_eq le_top ?_
  have hN : Nat.card (Perm Ω) = Nat.factorial (Fintype.card Ω) := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card]
  have hM : Nat.card (Perm {x // x ≠ α}) = Nat.factorial (Fintype.card Ω - 1) := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, card_subtype_ne]
  have hcardT : Nat.card T = 2 ^ (Nat.card (Perm Ω)).factorization 2 := by
    have h := hT.card_eq
    rwa [Subgroup.card_top] at h
  have hcardP : Nat.card (T.comap (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω)) =
      Nat.card T := by
    have h := Subgroup.card_map_of_injective
      (K := T.comap (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω))
      (f := (Perm.ofSubtype : Perm {x // x ≠ α} →* Perm Ω)) Perm.ofSubtype_injective
    rw [map_comap_ofSubtype_eq hTα] at h
    exact h.symm
  rw [Subgroup.card_top, hM, ← factorial_factorization_two_eq_pred _ hodd, ← hN, ← hcardT]
  exact hcardP

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
