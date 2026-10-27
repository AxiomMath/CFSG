module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartA
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A129Native
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Vol2.Ch11SecANat2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA SecS SecS.C11P9A
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.Assembly.LowTwoRank (specialLinearGroupEquivStatedSL)
open CFSG.QuasithinUnique.Vol2Native (A312L.sl2_isSimple A312L.sl2_nonabelian
  A312L.pCore_two_eq_ker)
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem isNaturalSection_of_levi {A V₃ V₁ : Subgroup G} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) (hA : A ≤ Subgroup.normalizer (V₃ : Set G))
    (ρ : ↥A →* SpecialLinearGroup (Fin 2) K) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 2 ρ.ker) (β : ↥V₃ →* Multiplicative (Fin 2 → K))
    (hβ : Function.Surjective β) (hβk : β.ker = V₁.subgroupOf V₃)
    (heq : ∀ (a : ↥A) (u v : ↥V₃), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) =
        ((ρ a : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
          Multiplicative.toAdd (β u)) :
    IsNaturalSection A V₃ V₁ (CFSG.pCore 2 ↥A) (Assembly.LowTwoRank.StatedSL 2 K) := by
  have := A312L.sl2_isSimple hK4
  have hρk := A312L.pCore_two_eq_ker (A312L.sl2_nonabelian hK4) ρ hρ hker
  refine ⟨hA, (specialLinearGroupEquivStatedSL 2 K).toMonoidHom.comp ρ,
    (specialLinearGroupEquivStatedSL 2 K).surjective.comp hρ, ?_, β, hβ, hβk,
    fun a u v h => heq a u v h⟩
  rw [hρk]
  ext a
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.map_eq_one_iff]

theorem exists_levi_of_autOn {Γ : Type*} [Group Γ] {A V : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G))) {N : Subgroup Γ}
    {ψ : Γ →* MulAut ↥V} (hψ : Function.Injective ψ) (hAN : autOn A V = N.map ψ) :
    ∃ θ : ↥A →* ↥N, Function.Surjective θ ∧ IsPGroup 2 θ.ker ∧
      ∀ a : ↥A, ψ (θ a) = conjV V a (hA a.2) := by
  set c := conjHomL V A hA
  have hc : ∀ a, c a ∈ N.map ψ := fun a => by
    rw [← hAN, ← range_conjHomL V A hA]
    exact ⟨a, rfl⟩
  set c' := c.codRestrict (N.map ψ) hc
  set e := N.equivMapOfInjective ψ hψ
  refine ⟨e.symm.toMonoidHom.comp c', fun x => ?_, fun k => ?_, fun a => ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, c a = (e x : MulAut ↥V) := by
      rw [← MonoidHom.mem_range, range_conjHomL, hAN]
      exact (e x).2
    refine ⟨a, ?_⟩
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_eq]
    exact Subtype.ext ha
  · have hk : ((k : ↥A) : G) ∈ A ⊓ Subgroup.centralizer (V : Set G) := by
      have h1 : (k : ↥A) ∈ c.ker := by
        rw [MonoidHom.mem_ker]
        have h2 := MonoidHom.mem_ker.mp k.2
        simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
          MulEquiv.map_eq_one_iff] at h2
        exact congrArg Subtype.val h2
      rw [ker_conjHomL, Subgroup.mem_subgroupOf] at h1
      exact h1
    obtain ⟨j, hj⟩ := hC ⟨_, hk⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    exact this
  · have h1 : ψ ((e.symm (c' a) : ↥N) : Γ) = (e (e.symm (c' a)) : MulAut ↥V) :=
      (Subgroup.coe_equivMapOfInjective_apply N ψ hψ _).symm
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1

section SL3

variable {K : Type} [Field K]

theorem tail_mulVec_of_mem_stabE0 {B : SpecialLinearGroup (Fin 3) K} (hB : B ∈ stabE0 K)
    (y : Fin 3 → K) :
    (fun i : Fin 2 => ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ y) i.succ) =
      lev (B : Matrix (Fin 3) (Fin 3) K) *ᵥ fun i : Fin 2 => y i.succ := by
  obtain ⟨-, h10, h20⟩ := stabE0_entries hB
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, lev_apply, h10, h20]

end SL3

end CFSG.Quasithin.Vol2.Ch11.SecO1
