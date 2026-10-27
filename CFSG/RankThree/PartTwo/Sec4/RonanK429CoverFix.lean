module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeQuasisimpleSL
public import CFSG.RankThree.PartTwo.Sec4.Item47Inputs
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank

variable {L : Type} [Group L] [Finite L] {π : Bool} {p f f₀ : ℕ} {F : Type} [Field F]

theorem autFix_eq_of_frob (hK : PiField π p f F) (hq : ModThree π (p ^ f)) (hf : f = 3 * f₀)
    {φ : F ≃+* F} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {g : GL (Fin 3) F} (hg : g ∈ glPi π 3 (p ^ f) F) (e : L ≃* slPi π 3 (p ^ f) F)
    {α : MulAut L} (hα3 : α ^ 3 = 1)
    (hform : ∀ l, (e (α l) : GL (Fin 3) F) = g * frobGL φ (e l) * g⁻¹)
    {K : Subgroup L} (hKfix : K ≤ autFix α) (hKq : IsQuasisimple K)
    (hKsn : (K.subgroupOf (autFix α)).IsSubnormal) : K = autFix α := by
  set σ : GL (Fin 3) F →* GL (Fin 3) F := (MulAut.conj g).toMonoidHom.comp (frobGL φ) with hσdef
  have hσapp : ∀ A, σ A = g * frobGL φ A * g⁻¹ := fun A => rfl
  have hσ : ∀ A : GL (Fin 3) F, (σ A : Matrix (Fin 3) (Fin 3) F) =
      g * (A : Matrix (Fin 3) (Fin 3) F).map (· ^ piCard π (p ^ f₀)) * (g⁻¹ : GL (Fin 3) F) := by
    intro A
    rw [hσapp, Units.val_mul, Units.val_mul, coe_frobGL]
    congr 2
    ext i k
    exact hφ _
  have hσe : ∀ l, σ (e l) = e (α l) := fun l => (hform l).symm
  have hα3' : ∀ l, α (α (α l)) = l := by
    intro l
    have h := congrArg (fun β : MulAut L => β l) hα3
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
  have hσ3 : ∀ A ∈ slPi π 3 (p ^ f) F, σ (σ (σ A)) = A := by
    intro A hA
    obtain ⟨l, hl⟩ := e.surjective ⟨A, hA⟩
    have hA' : A = (e l : GL (Fin 3) F) := by rw [hl]
    rw [hA', hσe, hσe, hσe, hα3']
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  obtain ⟨S₀, -, hS₀card⟩ := exists_fixedField hK hf hφ3
  have hK₀ : PiField π p f₀ S₀ := ⟨hK.prime, hf₀, hS₀card⟩
  obtain ⟨-, -, ⟨eX⟩⟩ := rank3II_4_10_four hK hq hf hg σ hσ hσ3 S₀ hK₀
  have hmap : (autFix α).map ((slPi π 3 (p ^ f) F).subtype.comp e.toMonoidHom) =
      fixedIn (slPi π 3 (p ^ f) F) σ := by
    ext A
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨(e l).2, ?_⟩
      change σ (e l) = (e l : GL (Fin 3) F)
      have hl' : α l = l := hl
      rw [hσe, hl']
    · rintro ⟨hA, hσA⟩
      change σ A = A at hσA
      obtain ⟨l, hl⟩ := e.surjective ⟨A, hA⟩
      refine ⟨l, ?_, by simp [hl]⟩
      change α l = l
      apply e.injective
      apply Subtype.ext
      rw [← hσe, hl]
      exact hσA
  have hinj : Function.Injective ((slPi π 3 (p ^ f) F).subtype.comp e.toMonoidHom) :=
    (Subgroup.subtype_injective _).comp e.injective
  have eF : autFix α ≃* slPi π 3 (p ^ f₀) S₀ :=
    ((Subgroup.equivMapOfInjective _ _ hinj).trans (MulEquiv.subgroupCongr hmap)).trans eX
  have hKnt : Nontrivial K := LocalCores.isQuasisimple_nontrivial hKq
  by_cases h2 : 2 < p ^ f₀
  ·
    have hq0 : IsQuasisimple (slPi π 3 (p ^ f₀) S₀) :=
      Item462AltProof.KSLThree.isQuasisimple_slPi hK₀ h2
    have hqfix : IsQuasisimple (autFix α) := LocalCores.isQuasisimple_of_mulEquiv eF.symm hq0
    exact Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hKfix hqfix hKq.1 hKnt hKsn
  ·
    exfalso
    have hp := hK.prime
    have hq₀2 : p ^ f₀ = 2 := by
      have : p ≤ p ^ f₀ := Nat.le_self_pow (by omega) p
      have := hp.two_le
      omega
    obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp hq₀2
    subst hf
    cases π
    · have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 S₀ := hK₀.unitary
      have hcard : Nat.card (autFix α) = 216 := by
        rw [Nat.card_congr eF.toEquiv]
        exact CFSG.RankThree.CentralLiftU.card_statedSU_three_two hU rfl
      have := Fintype.ofFinite (autFix α)
      have hsolv : Group.IsSolvable (autFix α) :=
        CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := 3) (b := 3)
          Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
      have hsolK : Group.IsSolvable K :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKfix)
          (Subgroup.inclusion_injective hKfix)
      have : Group.IsPerfect K := hKq.1
      exact Group.IsPerfect.not_isSolvable K hsolK
    · norm_num [ModThree] at hq

theorem autFix_eq_of_frobPow (hK : PiField π p f F) (hq : ModThree π (p ^ f)) (hf : f = 3 * f₀)
    {φ : F ≃+* F} (hφ : ∀ c, φ c = c ^ piCard π (p ^ f₀)) (hφ3 : orderOf φ = 3)
    {ρ : F ≃+* F} (hρ : ρ = φ ∨ ρ = φ ^ 2)
    {g : GL (Fin 3) F} (hg : g ∈ glPi π 3 (p ^ f) F) (e : L ≃* slPi π 3 (p ^ f) F)
    {α : MulAut L} (hα3 : α ^ 3 = 1)
    (hform : ∀ l, (e (α l) : GL (Fin 3) F) = g * frobGL ρ (e l) * g⁻¹)
    {K : Subgroup L} (hKfix : K ≤ autFix α) (hKq : IsQuasisimple K)
    (hKsn : (K.subgroupOf (autFix α)).IsSubnormal) : K = autFix α := by
  rcases hρ with rfl | rfl
  · exact autFix_eq_of_frob hK hq hf hφ hφ3 hg e hα3 hform hKfix hKq hKsn
  · have hα3' : ∀ l, α (α (α l)) = l := by
      intro l
      have h := congrArg (fun β : MulAut L => β l) hα3
      simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h
    have hsq : ∀ l, (α ^ 2) l = α (α l) := fun l => by rw [pow_two, MulAut.mul_apply]
    have hfix2 : autFix (α ^ 2) = autFix α := by
      ext l
      rw [mem_autFix, mem_autFix, hsq]
      constructor
      · intro h
        calc α l = α (α (α l)) := by rw [h]
          _ = l := hα3' l
      · intro h
        rw [h, h]
    have hα23 : (α ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hα3, one_pow]
    have hg₂ : g * frobGL (φ ^ 2) g ∈ glPi π 3 (p ^ f) F :=
      mul_mem hg (frobGL_mem_glPi hK _ hg)
    have hφ4 : ∀ A, frobGL (φ ^ 2) (frobGL (φ ^ 2) A) = frobGL φ A := by
      intro A
      rw [frobGL_pow_two, frobGL_pow_two, frobGL_three hφ3]
    have hform2 : ∀ l, (e ((α ^ 2) l) : GL (Fin 3) F) =
        (g * frobGL (φ ^ 2) g) * frobGL φ (e l) * (g * frobGL (φ ^ 2) g)⁻¹ := by
      intro l
      rw [hsq, hform, hform, map_mul, map_mul, map_inv, hφ4]
      group
    rw [← hfix2] at hKfix hKsn ⊢
    exact autFix_eq_of_frob hK hq hf hφ hφ3 hg₂ e hα23 hform2 hKfix hKq hKsn

end CFSG.RankThree.PartTwo.Sec4.RonanK429
