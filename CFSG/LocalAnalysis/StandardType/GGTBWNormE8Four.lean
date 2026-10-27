module

public import CFSG.LieType.SeitzGeneration.ExcTorusPowerMap
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four
public import CFSG.LocalAnalysis.StandardType.GGTBWNormInnerPowerMap
public import CFSG.LocalAnalysis.StandardType.GGTBWNormCartanScalar
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE

namespace E8FourWNorm

theorem natCast_sq_eq_neg_one_of_dvd {p q : ℕ} (h : p ∣ q ^ 2 + 1) :
    ((q : ℕ) : ZMod p) ^ 2 = -1 := by
  have h0 : ((q ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 h
  push_cast at h0
  exact eq_neg_of_add_eq_zero_left h0

theorem orderOf_eq_four_of_dvd_sq_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ q ^ 2 + 1) : orderOf ((q : ℕ) : ZMod p) = 4 := by
  have hq2 := natCast_sq_eq_neg_one_of_dvd h
  have hne : ((q : ZMod p)) ^ 2 ^ 1 ≠ 1 := by
    rw [pow_one, hq2]
    intro h1
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      have e : ((2 : ℕ) : ZMod p) = 1 - (-1) := by push_cast; ring
      rw [e, h1, sub_self]
    have := (ZMod.natCast_eq_zero_iff 2 p).1 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have h4 : ((q : ZMod p)) ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hq2, neg_one_sq]
  simpa using orderOf_eq_prime_pow hne h4

theorem not_dvd_degree_quotient_E8_four {p : ℕ} (hp7 : 7 ≤ p) :
    ∀ d ∈ degreesE .E8, 4 ∣ d → ¬ p ∣ d / 4 := by
  have key : ∀ d ∈ degreesE .E8, 4 ∣ d → 0 < d / 4 ∧ d / 4 ≤ 6 := by decide
  intro d hd h4 hpd
  obtain ⟨h0, h6⟩ := key d hd h4
  have := Nat.le_of_dvd h0 hpd
  omega

end E8FourWNorm


namespace E8FourWNorm

theorem sylowTorus_powerMap_E8_four (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) (hpq : p ∣ Nat.card K ^ 2 + 1) :
    SylowTorus (adjointGroup .E8 K) p 4 ∧
      ∃ E : Subgroup (adjointGroup .E8 K), IsElemAbelian p E ∧ Nat.card E = p ^ 4 ∧
        ∃ y : adjointGroup .E8 K, ∀ x ∈ E, y * x * y⁻¹ = x ^ Nat.card K := by
  have he := orderOf_eq_four_of_dvd_sq_add_one hp (by omega) hpq
  have h := sylowTorus_powerMap_of_blocks 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E8 e8FourWord) [4, 4, 4, 4] e8Four_charpoly e8Four_pow he
    (by norm_num) (fun d hd hne => absurd (by simpa using hd) hne)
    (not_dvd_degree_quotient_E8_four hp7) (by decide)
  simpa using h

section Row

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

open TableBExc in
theorem ggTorusWNormSC_recipe_E8_four {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hq : p ∣ Nat.card K ^ 2 + 1) : GGTorusWNormSC p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Λ _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen
  exfalso
  have hIp : GGOutdiagPrime p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
    intro φ hφ _
    obtain ⟨x, rfl⟩ := idImage_subset_inn_E8 K hφ
    exact ⟨x, rfl⟩
  obtain ⟨hS, E₀, hE₀, hE₀c, y, hy⟩ := sylowTorus_powerMap_E8_four K hp hp7 hq
  obtain ⟨u, hu, hupow⟩ := exists_pow_mem_ggAutomizer_of_innerModel hp
    (center_recipeGroup_eq_bot .E8 K) hIp (ExcSplitL.ggCenterPrime_recipe_E8 hp (by omega)) ψ hψ
    hker hperf hA hAI hsc (k := Nat.card K) fun E hE _ hEsc => by
      let ε := recipeEquiv .E8 K
      have hE' : IsElemAbelian p (E.map ε.toMonoidHom) := TableB.isElemAbelian_map hE _
      have hE'sc : ∀ g, (∀ e ∈ E.map ε.toMonoidHom, g * e = e * g) → g ^ p = 1 →
          g ∈ E.map ε.toMonoidHom := by
        intro g hg hgp
        have hg' : ε.symm g ∈ E := by
          apply hEsc
          · intro e he
            apply ε.injective
            rw [map_mul, map_mul, ε.apply_symm_apply]
            exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
          · rw [← map_pow, hgp, map_one]
        exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
      obtain ⟨-, z, hz⟩ := hS.exists_powerMap_of_selfCent hp hE₀ hE₀c hy hE' hE'sc
      refine ⟨ε.symm z, fun x hx => ε.injective ?_⟩
      rw [map_mul, map_mul, map_inv, ε.apply_symm_apply, map_pow]
      exact hz (ε x) ⟨x, hx, rfl⟩
  rw [hgen] at hu
  have hs : ggLin (p := p) ι u ∈
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ i)) := by
    have h1 := Subgroup.mem_map_of_mem (ggLin (p := p) ι) hu
    rw [MonoidHom.map_closure] at h1
    convert h1 using 2
    ext x
    simp
  have hsq := scalar_sq_eq_one_of_cartan_reflection_datum (by omega) M hM C hC h α hpair
    (fun i => ggLin (p := p) ι (φ i)) hlin (ggLin (p := p) ι u) hs (Nat.card K : ZMod p)
    (ggLin_apply_of_forall_pow ι hupow)
  have h1 : (-1 : ZMod p) = 1 := (natCast_sq_eq_neg_one_of_dvd hq).symm.trans hsq
  exact (@ZMod.neg_one_ne_one p ⟨by omega⟩) h1

end Row

end E8FourWNorm

open E8FourWNorm in
theorem largeEvenLabelAll_wnorm_E8_four
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) {lab : LargeEvenLabel}
    (htag : lab.tag = .E8) (hpq : p ∣ (2 ^ lab.n) ^ 2 + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  rcases lab with ⟨tag, r, n⟩
  dsimp only at htag hpq ⊢
  subst htag
  intro Q hQ
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ, ?_⟩
  have : CharP K 2 := charP_two_of_card hK
  exact ggTorusWNormSC_recipe_E8_four hp hp7 (by rw [hK]; exact hpq)

end CFSG.StandardType

end
