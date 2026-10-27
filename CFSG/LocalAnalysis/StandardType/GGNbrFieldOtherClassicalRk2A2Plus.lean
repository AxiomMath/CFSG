module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixRows
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag NbrInnerNine TableB

theorem ggTorusNoLineTwo_of_card_lt_sq {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 2) :
    GGTorusNoLineTwo p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h2 _
  exfalso
  obtain ⟨Ind, hInd⟩ := ggInducedHom_exists ψ hψ A (fun a ha => by
    obtain ⟨φ, -, h⟩ := hAI a ha
    exact ⟨φ, h⟩)
  have hinj : Function.Injective Ind := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext (ggAut_eq_one_of_induced_one ψ hker hperf a fun l => ?_)
    rw [← hInd a l, ha, MulAut.one_apply]
  have hXI : (Ind.range : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨φ, hφ, hφa⟩ := hAI a a.2
    rw [ggInduced_unique hψ (hInd a) hφa]
    exact hφ
  have hXab : IsElemAbelian p Ind.range := ggIsElemAbelian_range le_rfl hA Ind
  have hcard : Nat.card Ind.range = Nat.card A :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have := h Ind.range hXI hXab
  rw [hcard] at this
  omega

namespace TypeA

variable {K : Type} [Field K] [Finite K]

theorem card_lt_sq_pgl3_of_not_dvd [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K - 1) {X : Subgroup (MulAut (projectiveSL 3 K))}
    (hX : IsElemAbelian p X)
    (hXI : (X : Set (MulAut (projectiveSL 3 K))) ⊆ Set.range (conjAut 3 K)) :
    Nat.card X < p ^ 2 := by
  have := Fact.mk hp
  obtain ⟨E, hE, hcard, -⟩ := exists_lift_of_not_dvd hp hpK (by norm_num) hX hXI
  have h := card_pow_le_of_gl (e := 2) hp
    (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo hp hp2)
    (fun j hj hje => by
      have hj1 : j = 1 := by omega
      subst hj1
      rwa [pow_one]) E (fun g hg h hh => TableB.IsElemAbelian.comm hE hg hh)
    (fun g hg => hE.2 g hg)
  rw [Fintype.card_fin] at h
  rw [← hcard]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hE)
  rw [hk, ← pow_mul] at h
  rw [hk]
  have hkd : k * 2 ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  exact Nat.pow_lt_pow_right hp.one_lt (by omega)

end TypeA

theorem largeEvenLabelAll_card_lt_sq_a2Plus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : lab.tag = .A ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 2 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn⟩ := h
  dsimp only at ht hl hpn ⊢
  subst ht hl
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : ¬ p ∣ Nat.card K - 1 := by
    rw [hK]
    intro h1
    have h1' : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpn h1
    have h3 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rw [h3] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  refine ⟨K, inferInstance, inferInstance, hK, hQ', fun X hXI hX => ?_⟩
  exact StdSubRestThree.card_lt_of_congr (TypeA.recipeEquiv 3 K)
    (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (fun _ hX'I hX' => TypeA.card_lt_sq_pgl3_of_not_dvd hp hp2 hpK hX' hX'I) hXI hX

theorem largeEvenLabelAll_rowPlainTwo_a2Plus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (h : lab.tag = .A ∧ lab.rank = 2 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  have hlt := largeEvenLabelAll_card_lt_sq_a2Plus hp hp2 h
  have hrest : LargeEvenLabelAll lab fun R _ I _ =>
      (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift p 0 R := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨ht, hl, -⟩ := h
    dsimp only at ht hl ⊢
    subst ht hl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    refine ⟨K, inferInstance, inferInstance, hK, hQ', fun g => ?_, ?_⟩
    · have := RecipeFieldLinear.conj_mem_recI (d := 2 + 1) (K := K) g
      rwa [← SetLike.mem_coe, RecipeFieldLinear.coe_recI] at this
    · exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv 3 K)
        (TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num)))
  exact (largeEvenLabelAll_and hrest hlt).mono fun _ _ _ _ ⟨⟨hi, hl⟩, hX⟩ =>
    ⟨hi, hl, fun _ _ => ggTorusNoLineTwo_of_card_lt_sq hX⟩

end CFSG.StandardType

end
