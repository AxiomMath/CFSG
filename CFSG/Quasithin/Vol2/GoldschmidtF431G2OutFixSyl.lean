module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.QuasithinUnique

section Syl

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_of_top {T N : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ N) :
    IsSylowTwoOf T N := by
  refine isSylowTwoOf_of_card_eq hTN hT.isPGroup ?_
  refine le_antisymm (card_le_twoPart hTN hT.isPGroup) ?_
  rw [hT.card_eq]
  exact twoPart_mono le_top

theorem card_mul_le_card_mul_inf {Y S T : Subgroup G} (hYT : Y ≤ T) (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) :
    Nat.card Y * Nat.card S ≤ Nat.card T * Nat.card ↥(Y ⊓ S) := by
  have h := Lin2.card_sup_mul_card_inf (A := Y) (B := S) (hYT.trans hTS)
  have hsup : Nat.card ↥(Y ⊔ S) ≤ Nat.card T := Subgroup.card_le_of_le (sup_le hYT hST)
  calc Nat.card Y * Nat.card S = Nat.card ↥(Y ⊔ S) * Nat.card ↥(Y ⊓ S) := h.symm
    _ ≤ Nat.card T * Nat.card ↥(Y ⊓ S) := Nat.mul_le_mul_right _ hsup

theorem isSylowTwoOf_centralizer_inf {T N R : Subgroup G} {f : G} (hR : R.Normal)
    (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ N) (hfT : f ∈ T) (hf2 : f ^ 2 = 1) (hfR : f ∉ R)
    (hinv : ∀ f' ∈ T, f' ∉ R → f' ^ 2 = 1 →
      Nat.card ↥(T ⊓ Subgroup.centralizer ({f'} : Set G)) ≤
        Nat.card ↥(T ⊓ Subgroup.centralizer ({f} : Set G))) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({f} : Set G))
      (Subgroup.centralizer ({f} : Set G) ⊓ N) := by
  have hTfM : T ⊓ Subgroup.centralizer ({f} : Set G) ≤ Subgroup.centralizer ({f} : Set G) ⊓ N :=
    fun x hx => ⟨hx.2, hTN hx.1⟩
  have hTf2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({f} : Set G)) :=
    hT.isPGroup.to_le inf_le_left
  obtain ⟨P, hTfP, hP⟩ := exists_isSylowTwoOf_of_le hTfM hTf2
  have hPN : P ≤ N := hP.le.trans inf_le_right
  have hPC : P ≤ Subgroup.centralizer ({f} : Set G) := hP.le.trans inf_le_left
  obtain ⟨S', hPS', hS'⟩ := exists_isSylowTwoOf_of_le hPN hP.isPGroup
  obtain ⟨h, -, hS'eq⟩ := (isSylowTwoOf_of_top hT hTN).exists_conj hS'
  have hconj : ∀ p ∈ P, h⁻¹ * p * h ∈ T := by
    intro p hp
    have hp' := hPS' hp
    rw [hS'eq] at hp'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hp'
    simpa [MulAut.conj_apply, mul_assoc] using ht
  have hfC : f ∈ Subgroup.centralizer ({f} : Set G) := Subgroup.mem_centralizer_iff.2
    (fun g hg => by rw [Set.mem_singleton_iff.1 hg])
  have hfP : f ∈ P := hTfP ⟨hfT, hfC⟩
  have hf'T : h⁻¹ * f * h ∈ T := hconj f hfP
  have hf'2 : (h⁻¹ * f * h) ^ 2 = 1 := by
    have : (h⁻¹ * f * h) ^ 2 = h⁻¹ * f ^ 2 * h := by
      rw [pow_two, pow_two]
      group
    rw [this, hf2]
    group
  have hf'R : h⁻¹ * f * h ∉ R := by
    intro hmem
    apply hfR
    have := hR.conj_mem _ hmem h
    simpa [mul_assoc] using this
  have hmem : ∀ p : P, h⁻¹ * p.1 * h ∈ T ⊓ Subgroup.centralizer ({h⁻¹ * f * h} : Set G) := by
    intro p
    refine ⟨hconj p.1 p.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.1 hg]
    have hpf := Subgroup.mem_centralizer_iff.1 (hPC p.2) f rfl
    calc h⁻¹ * f * h * (h⁻¹ * p.1 * h) = h⁻¹ * (f * p.1) * h := by group
      _ = h⁻¹ * (p.1 * f) * h := by rw [hpf]
      _ = h⁻¹ * p.1 * h * (h⁻¹ * f * h) := by group
  have hcard : Nat.card P ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({f} : Set G)) := by
    calc Nat.card P ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({h⁻¹ * f * h} : Set G)) := by
          refine Nat.card_le_card_of_injective (fun p => ⟨h⁻¹ * p.1 * h, hmem p⟩) ?_
          intro p q hpq
          have := congrArg Subtype.val hpq
          simp only [mul_left_inj, mul_right_inj] at this
          exact Subtype.ext this
      _ ≤ _ := hinv _ hf'T hf'R hf'2
  have hPeq : P = T ⊓ Subgroup.centralizer ({f} : Set G) :=
    (Subgroup.eq_of_le_of_card_ge hTfP hcard).symm
  rw [← hPeq]
  exact hP

end Syl

end CFSG.Quasithin.H13.F431.G2
