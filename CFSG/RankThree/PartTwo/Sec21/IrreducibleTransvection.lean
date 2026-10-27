module

public import CFSG.RankThree.PartTwo.Sec21.Notation
public import CFSG.RankThree.PartTwo.Sec12.Coordinates
public import CFSG.RankThree.PartTwo.Sec3.ThreeSpaceTransvections

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

variable {G : Type*} [Group G]

theorem exists_generator_of_isTransvectionOn {A : Subgroup G} (hA : IsMulCommutative A)
    {φ : MulAut A} (hφ : IsTransvectionOn φ) :
    ∃ c : A, c ≠ 1 ∧ Subgroup.zpowers c = commOf φ ∧ φ ∈ Sec12.transvectionGroup A c ∧
      φ ≠ 1 := by
  have hcard := hφ.1
  have hne : commOf φ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨c, hc⟩, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hc1 : c ≠ 1 := fun h => hc1' (Subtype.ext h)
  have hfin : Finite (commOf φ) := Nat.finite_of_card_ne_zero (by omega)
  have hzle : Subgroup.zpowers c ≤ commOf φ := (Subgroup.zpowers_le).mpr hc
  have hzeq : Subgroup.zpowers c = commOf φ := by
    apply Subgroup.eq_of_le_of_card_ge hzle
    rw [hcard, Nat.card_zpowers]
    have hdvd : orderOf c ∣ 3 := by
      rw [← hcard, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hzle
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · omega
  have hφ1 : φ ≠ 1 := by
    intro h
    rw [(commOf_eq_bot_iff φ).mpr h] at hne
    exact hne rfl
  refine ⟨c, hc1, hzeq, ⟨hφ.2 hc, fun a => ?_⟩, hφ1⟩
  rw [hzeq]
  have h := mem_commOf φ a
  rwa [hA.is_comm.comm a⁻¹ (φ a)] at h

theorem exists_isTransvectionWith_coordHom {A : Subgroup G} (hA : IsMulCommutative A)
    {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] (f : Multiplicative V ≃* A)
    {φ : MulAut A} (hφ : IsTransvectionOn φ) :
    ∃ v ψ, CFSG.RankThree.Classical.IsTransvectionWith (Sec12.coordHom f φ) v ψ := by
  obtain ⟨c, hc1, -, hφT, hφ1⟩ := exists_generator_of_isTransvectionOn hA hφ
  exact (Sec12.coordHom_isTransvection f hc1 hφT hφ1).1

@[expose] def coordSubgroup {A : Subgroup G} {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Multiplicative V ≃* A) (W : Submodule (ZMod 3) V) : Subgroup A :=
  (AddSubgroup.toSubgroup W.toAddSubgroup).map f.toMonoidHom

theorem rank3II_21_11_core {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hcard : Nat.card A = 27) {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Multiplicative V ≃* A) (S : Subgroup (MulAut A)) (hirr : IsIrreducibleOn S)
    {φ : MulAut A} (hφS : φ ∈ S) (hφ : IsTransvectionOn φ) :
    ∀ σ : MulAut A, LinearMap.det (Sec12.coordHom f σ : V →ₗ[ZMod 3] V) = 1 → σ ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hVcard : Nat.card V = 27 := by
    rw [← hcard]
    exact Nat.card_congr (Multiplicative.ofAdd.trans f.toEquiv)
  have hVfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have : FiniteDimensional (ZMod 3) V := inferInstance
  have hrank : Module.finrank (ZMod 3) V = 3 := by
    have h := FiniteField.pow_finrank_eq_natCard 3 V
    rw [hVcard, show (27 : ℕ) = 3 ^ 3 by norm_num] at h
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  set T : Subgroup (V ≃ₗ[ZMod 3] V) := S.map (Sec12.coordHom f)
  have hTirr : ∀ W : Submodule (ZMod 3) V, (∀ g ∈ T, ∀ x ∈ W, g x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hB : ∀ σ ∈ S, (coordSubgroup f W).map σ.toMonoidHom = coordSubgroup f W := by
      intro σ hσ
      have hle : (coordSubgroup f W).map σ.toMonoidHom ≤ coordSubgroup f W := by
        rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        have hgw := hW (Sec12.coordHom f σ) ⟨σ, hσ, rfl⟩ (Multiplicative.toAdd w) hw
        refine ⟨Multiplicative.ofAdd (Sec12.coordHom f σ (Multiplicative.toAdd w)), hgw, ?_⟩
        simp [Sec12.coordHom_apply]
      have hfinA : Finite (coordSubgroup f W) := Subtype.finite
      exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (Subgroup.card_map_of_injective
        σ.injective).symm)
    rcases hirr (coordSubgroup f W) hB with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hmem : f (Multiplicative.ofAdd x) ∈ coordSubgroup f W := ⟨_, hx, rfl⟩
      rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
      simpa using congrArg Multiplicative.toAdd hmem
    · right
      rw [eq_top_iff]
      intro x _
      have hmem : f (Multiplicative.ofAdd x) ∈ coordSubgroup f W := h ▸ Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := hmem
      have : y = Multiplicative.ofAdd x := f.injective hyx
      rw [this] at hy
      exact hy
  obtain ⟨v, ψ, hr⟩ := exists_isTransvectionWith_coordHom hA.1 f hφ
  have hmain := Sec3.det_eq_one_mem_of_irreducible hrank T hTirr ⟨φ, hφS, rfl⟩ hr
  intro σ hσ
  obtain ⟨σ', hσ'S, hσ'eq⟩ := hmain (Sec12.coordHom f σ) hσ
  rw [Sec12.coordHom_injective f hσ'eq] at hσ'S
  exact hσ'S

end CFSG.RankThree.PartTwo.Sec21
