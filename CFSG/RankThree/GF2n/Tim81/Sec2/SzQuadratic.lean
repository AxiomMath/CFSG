module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzCor23
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzThreeGen
public import CFSG.RankThree.GF2n.Tim81.Sec2.InvolutionModule
public import CFSG.RepresentationTheory.PerfectWeightStabilizerModule

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open scoped Matrix

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.B45Sz CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7b CFSG.QuasithinUnique.Setup.SL2Modules

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem isSzNatural_of_commSub_le_fixedSub
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) (x : ↥(suzukiGroup a K))
    (hquad : commSub ρ (CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K)) ≤
      fixedSub ρ (CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K))) :
    IsSzNatural ρ := by
  classical
  let A : Subgroup ↥(suzukiGroup a K) :=
    CFSG.CGT.Timmesfeld75.conjSubgroup x (szZ a K)
  change commSub ρ A ≤ fixedSub ρ A at hquad
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hAcard : Nat.card A = 2 ^ (2 * a + 1) := by
    change Nat.card ((szZ a K).map (MulAut.conj x).toMonoidHom) = 2 ^ (2 * a + 1)
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, card_szZ hK]
  have hA2 : 2 ≤ Nat.card A := by
    rw [hAcard]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAnt : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨t, htne⟩ := exists_ne (1 : A)
  have ht_mem : (t : ↥(suzukiGroup a K)) ∈ A := t.2
  have ht1 : (t : ↥(suzukiGroup a K)) ≠ 1 := by
    intro h
    exact htne (Subtype.ext h)
  have ht2 : (t : ↥(suzukiGroup a K)) * (t : ↥(suzukiGroup a K)) = 1 := by
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp ht_mem
    rw [← hst, ← map_mul, szZ_mul_self hK hs, map_one]
  obtain ⟨g₁, g₂, hgen⟩ := exists_closure_three_conj_eq_top hK ha
    (t : ↥(suzukiGroup a K)) ht2 ht1
  let T₁ : ↥(suzukiGroup a K) := g₁ * (t : ↥(suzukiGroup a K)) * g₁⁻¹
  let T₂ : ↥(suzukiGroup a K) := g₂ * (t : ↥(suzukiGroup a K)) * g₂⁻¹
  let C₁ : Submodule (ZMod 2) W := fixedSub ρ (Subgroup.zpowers (t : ↥(suzukiGroup a K)))
  let C₂ : Submodule (ZMod 2) W := fixedSub ρ (Subgroup.zpowers T₁)
  let C₃ : Submodule (ZMod 2) W := fixedSub ρ (Subgroup.zpowers T₂)
  have hcomm_le : commSub ρ A ≤ C₁ := by
    refine hquad.trans ?_
    intro w hw
    exact mem_fixedSub.mpr fun z hz =>
      mem_fixedSub.mp hw z (Subgroup.zpowers_le.mpr ht_mem hz)
  have hWnt : Nontrivial W := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨g, hg⟩ := hnt
    exact hg (by ext w; exact Subsingleton.elim _ _)
  set l : ℕ := Module.finrank (ZMod 2) W with hl
  set k : ℕ := Module.finrank (ZMod 2) C₁ with hk
  set u : ℕ := Module.finrank (ZMod 2) (commSub ρ A) with hu
  have hlpos : 0 < l := by rw [hl]; exact Module.finrank_pos
  have hu_le_k : u ≤ k := by
    rw [hu, hk]
    exact Submodule.finrank_mono hcomm_le
  have htop : fixedSub ρ (⊤ : Subgroup ↥(suzukiGroup a K)) = ⊥ := by
    obtain ⟨-, hirr⟩ :=
      (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp
        (Fact.out : ρ.IsIrreducible)
    rcases hirr (fixedSub ρ ⊤) (fun g v hv => by
      rw [mem_fixedSub.mp hv g (Subgroup.mem_top g)]
      exact hv) with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg⟩ := hnt
      apply hg
      ext v
      have hv : v ∈ fixedSub ρ ⊤ := by rw [h]; exact Submodule.mem_top
      have h2 : ρ g v = v := mem_fixedSub.mp hv g (Subgroup.mem_top g)
      simpa using h2
  have hC : C₁ ⊓ C₂ ⊓ C₃ = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwt : ρ (t : ↥(suzukiGroup a K)) w = w :=
      (mem_fixedSub_zpowers ρ (t : ↥(suzukiGroup a K)) w).mp hw.1.1
    have hwt1 : ρ T₁ w = w := (mem_fixedSub_zpowers ρ T₁ w).mp hw.1.2
    have hwt2 : ρ T₂ w = w := (mem_fixedSub_zpowers ρ T₂ w).mp hw.2
    have hmem : w ∈ fixedSub ρ (Subgroup.closure
        ({(t : ↥(suzukiGroup a K)), T₁, T₂} : Set ↥(suzukiGroup a K))) := by
      refine mem_fixedSub.mpr fun h hh => ?_
      refine Subgroup.closure_induction (p := fun h _ => ρ h w = w) ?_ ?_ ?_ ?_ hh
      · intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl | rfl
        · exact hwt
        · exact hwt1
        · exact hwt2
      · simp
      · intro p q _ _ hp hq
        rw [map_mul, Module.End.mul_apply, hq, hp]
      · intro p _ hp
        have h1 : ρ p⁻¹ (ρ p w) = ρ p⁻¹ w := by rw [hp]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] at h1
        exact h1.symm
    have htopw : w ∈ fixedSub ρ (⊤ : Subgroup ↥(suzukiGroup a K)) := by
      rw [← hgen]
      exact hmem
    rwa [htop] at htopw
  have hk₂' : Module.finrank (ZMod 2) C₂ = Module.finrank (ZMod 2) C₁ := by
    change Module.finrank (ZMod 2)
      (fixedSub ρ (Subgroup.zpowers (g₁ * (t : ↥(suzukiGroup a K)) * g₁⁻¹))) =
        Module.finrank (ZMod 2) C₁
    rw [fixedSub_zpowers_conj ρ g₁ (t : ↥(suzukiGroup a K))]
    exact (Submodule.equivMapOfInjective (ρ g₁)
      (CFSG.RepresentationTheory.representation_injective ρ g₁)
      (fixedSub ρ (Subgroup.zpowers (t : ↥(suzukiGroup a K))))).finrank_eq.symm
  have hk₂ : Module.finrank (ZMod 2) C₂ = k := by rw [hk]; exact hk₂'
  have hk₃' : Module.finrank (ZMod 2) C₃ = Module.finrank (ZMod 2) C₁ := by
    change Module.finrank (ZMod 2)
      (fixedSub ρ (Subgroup.zpowers (g₂ * (t : ↥(suzukiGroup a K)) * g₂⁻¹))) =
        Module.finrank (ZMod 2) C₁
    rw [fixedSub_zpowers_conj ρ g₂ (t : ↥(suzukiGroup a K))]
    exact (Submodule.equivMapOfInjective (ρ g₂)
      (CFSG.RepresentationTheory.representation_injective ρ g₂)
      (fixedSub ρ (Subgroup.zpowers (t : ↥(suzukiGroup a K))))).finrank_eq.symm
  have hk₃ : Module.finrank (ZMod 2) C₃ = k := by rw [hk]; exact hk₃'
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq C₁ C₂
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (C₁ ⊓ C₂) C₃
  have hsup₁ : Module.finrank (ZMod 2) ↥(C₁ ⊔ C₂) ≤ l := by
    rw [hl]
    exact Submodule.finrank_le (C₁ ⊔ C₂)
  have hsup₂ : Module.finrank (ZMod 2) ↥((C₁ ⊓ C₂) ⊔ C₃) ≤ l := by
    rw [hl]
    exact Submodule.finrank_le ((C₁ ⊓ C₂) ⊔ C₃)
  have hk₁ : Module.finrank (ZMod 2) C₁ = k := hk.symm
  rw [hC, finrank_bot, add_zero] at h2
  have h3k : 3 * k ≤ 2 * l := by omega
  have h4u3l : 4 * u < 3 * l := by omega
  have hWcard : Nat.card W = 2 ^ l := by
    rw [hl]
    exact natCard_eq_two_pow_finrank W
  have hcommcard : Nat.card (commSub ρ A) = 2 ^ u := by
    rw [hu]
    exact natCard_eq_two_pow_finrank (commSub ρ A)
  have hcomm_lt : Nat.card (commSub ρ A) ^ 4 < Nat.card W ^ 3 := by
    rw [hcommcard, hWcard, ← pow_mul, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hWpos : 0 < Nat.card W := by
    have := Finite.one_lt_card_iff_nontrivial.mpr hWnt
    omega
  have hmain : Nat.card W * Nat.card (commSub ρ A) ^ 4 < Nat.card W ^ 4 := by
    calc Nat.card W * Nat.card (commSub ρ A) ^ 4
        < Nat.card W * Nat.card W ^ 3 :=
          Nat.mul_lt_mul_of_pos_left hcomm_lt hWpos
      _ = Nat.card W ^ 4 := by ring
  exact isSzNatural_of_commSub_card_lt (ρ := ρ) hK hnt x (by simpa [A] using hmain)

end CFSG.RankThree.GF2n.Tim81.Sec2

end
