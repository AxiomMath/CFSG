module

public import CFSG.GroupTheory.WeirSylow.GL

public section

namespace CFSG.RankThree.PartOne.K159R5

open CFSG.GroupTheory.WeirSylow Module

theorem sigmaModel_mul_comm {p a N : ℕ} (hN : N < p) (x y : sigmaModel p 1 a N) : x * y = y * x := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · funext i
    exfalso
    have h0 : (Nat.digits p (0 / 1)).length = 0 := by simp
    have := i.2
    omega
  · have hdig : Nat.digits p (N / 1) = [N] := by
      rw [Nat.div_one]
      exact Nat.digits_of_lt p N (Nat.pos_iff_ne_zero.1 hN0) hN
    have hlen : (Nat.digits p (N / 1)).length = 1 := by rw [hdig]; rfl
    funext i
    funext j
    obtain ⟨iv, hiv⟩ := i
    have hi0 : iv = 0 := by
      have := hiv
      rw [hlen] at this
      omega
    subst hi0
    exact mul_comm (G := Multiplicative (ZMod (p ^ a))) _ _

theorem abelian_of_pGroup_GL {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) {K : Type} [Field K] [Fintype K]
    (hpK : ¬ p ∣ Fintype.card K) (hK1 : Fintype.card K ≡ 1 [MOD p]) {d : ℕ} (hd : d < p)
    (T : Subgroup (GL (Fin d) K)) (hT : IsPGroup p ↥T) : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  obtain ⟨e⟩ := sylow_GL hp1 K hpK d S
  have he : orderOf (Fintype.card K : ZMod p) = 1 := by
    have : (Fintype.card K : ZMod p) = 1 := by
      have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hK1
      simpa using this
    rw [this]
    exact orderOf_one
  rw [he] at e
  intro x hx y hy
  have hxy : (⟨x, hS hx⟩ : S) * ⟨y, hS hy⟩ = ⟨y, hS hy⟩ * ⟨x, hS hx⟩ := by
    apply e.injective
    rw [map_mul, map_mul]
    exact sigmaModel_mul_comm hd _ _
  exact congrArg Subtype.val hxy

theorem exists_injective_hom_GL_of_restrict {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (M : Subgroup (LinearMap.GeneralLinearGroup K V)) (W : Submodule K V) [FiniteDimensional K W]
    {d : ℕ} (hd : Module.finrank K W = d)
    (hpres : ∀ g ∈ M, ∀ v ∈ W, ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ W)
    (hinj : ∀ g ∈ M, (∀ v ∈ W, ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v) → g = 1) :
    ∃ f : ↥M →* GL (Fin d) K, Function.Injective f := by
  classical
  let b : Basis (Fin d) K W := Module.finBasisOfFinrankEq K W hd
  let r : ↥M →* Module.End K W :=
    { toFun := fun g => LinearMap.restrict ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
        (fun v hv => hpres g g.2 v hv)
      map_one' := by
        ext v
        rfl
      map_mul' := fun g g' => by
        ext v
        rfl }
  let m : Module.End K W →* Matrix (Fin d) (Fin d) K := (LinearMap.toMatrixAlgEquiv b).toMonoidHom
  refine ⟨(m.comp r).toHomUnits, ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : m (r g) = 1 := by
    have := congrArg Units.val hg
    simpa using this
  have h2 : r g = 1 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_one]
    exact h1
  have h3 : ∀ v ∈ W, ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = v := by
    intro v hv
    have h4 : ((r g ⟨v, hv⟩ : W) : V) = v := by
      rw [h2]
      rfl
    exact h4
  exact Subtype.ext (hinj g g.2 h3)

end CFSG.RankThree.PartOne.K159R5
