module

public import CFSG.RankThree.SubgroupLists.QuasisimpleLayer
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped commutatorElement

theorem exists_gens_of_heisAct {X : Type} [Group X] [Finite X] {P : Subgroup (MulAut X)}
    {F : Type} [Field F] {M : Subgroup (ProjGenLinGroup (Fin 3) F)} {φ : X ≃* M}
    {y₁ y₂ : GL (Fin 3) F} (hy₁3 : y₁ ^ 3 ∈ StatedScalars (Fin 3) F)
    (hy₂3 : y₂ ^ 3 ∈ StatedScalars (Fin 3) F)
    (hact : ∀ σ ∈ P, ∃ i j : ℤ, ∀ z : X,
      ((φ (σ z) : M) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk (y₁ ^ i * y₂ ^ j) * (φ z : ProjGenLinGroup (Fin 3) F) *
          (ProjGenLinGroup.mk (y₁ ^ i * y₂ ^ j))⁻¹)
    (hP9 : Nat.card P = 9) :
    (∃ σ ∈ P, ∀ z : X, ((φ (σ z) : M) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk y₁ * (φ z : ProjGenLinGroup (Fin 3) F) *
          (ProjGenLinGroup.mk y₁)⁻¹) ∧
      ∃ σ ∈ P, ∀ z : X, ((φ (σ z) : M) : ProjGenLinGroup (Fin 3) F) =
        ProjGenLinGroup.mk y₂ * (φ z : ProjGenLinGroup (Fin 3) F) *
          (ProjGenLinGroup.mk y₂)⁻¹ := by
  classical
  set m₁ := ProjGenLinGroup.mk y₁
  set m₂ := ProjGenLinGroup.mk y₂
  have hm₁ : m₁ ^ 3 = 1 := by
    rw [← map_pow]
    exact Sec4.mk_eq_one_iff_mem_statedScalars.mpr hy₁3
  have hm₂ : m₂ ^ 3 = 1 := by
    rw [← map_pow]
    exact Sec4.mk_eq_one_iff_mem_statedScalars.mpr hy₂3
  choose i j hij using hact
  have hact' : ∀ (σ : P) (z : X), ((φ ((σ : MulAut X) z) : M) : ProjGenLinGroup (Fin 3) F) =
      (m₁ ^ (i σ σ.2 % 3) * m₂ ^ (j σ σ.2 % 3)) * (φ z : ProjGenLinGroup (Fin 3) F) *
        (m₁ ^ (i σ σ.2 % 3) * m₂ ^ (j σ σ.2 % 3))⁻¹ := by
    intro σ z
    rw [hij σ σ.2 z, map_mul, map_zpow, map_zpow, ← Sec4.zpow_emod_three hm₁,
      ← Sec4.zpow_emod_three hm₂]
  let ι : P → ZMod 3 × ZMod 3 := fun σ => ((i σ σ.2 : ZMod 3), (j σ σ.2 : ZMod 3))
  have hι : Function.Injective ι := by
    intro σ τ hστ
    simp only [ι, Prod.mk.injEq] at hστ
    obtain ⟨h1, h2⟩ := hστ
    have e1 : i σ σ.2 % 3 = i τ τ.2 % 3 := by
      have := (ZMod.intCast_eq_intCast_iff' (i σ σ.2) (i τ τ.2) 3).mp h1
      exact_mod_cast this
    have e2 : j σ σ.2 % 3 = j τ τ.2 % 3 := by
      have := (ZMod.intCast_eq_intCast_iff' (j σ σ.2) (j τ τ.2) 3).mp h2
      exact_mod_cast this
    apply Subtype.ext
    ext z
    apply φ.injective
    apply Subtype.ext
    rw [hact' σ z, hact' τ z, e1, e2]
  have hcard : Nat.card (ZMod 3 × ZMod 3) ≤ Nat.card P := by
    rw [hP9, Nat.card_prod, Nat.card_zmod]
  have hbij := hι.bijective_of_nat_card_le hcard
  have hval : ∀ σ : P, ∀ a b : ℤ, ι σ = ((a : ZMod 3), (b : ZMod 3)) →
      ∀ z : X, ((φ ((σ : MulAut X) z) : M) : ProjGenLinGroup (Fin 3) F) =
        (m₁ ^ (a % 3) * m₂ ^ (b % 3)) * (φ z : ProjGenLinGroup (Fin 3) F) *
          (m₁ ^ (a % 3) * m₂ ^ (b % 3))⁻¹ := by
    intro σ a b hσ z
    simp only [ι, Prod.mk.injEq] at hσ
    have e1 : i σ σ.2 % 3 = a % 3 := by
      have := (ZMod.intCast_eq_intCast_iff' (i σ σ.2) a 3).mp hσ.1
      exact_mod_cast this
    have e2 : j σ σ.2 % 3 = b % 3 := by
      have := (ZMod.intCast_eq_intCast_iff' (j σ σ.2) b 3).mp hσ.2
      exact_mod_cast this
    rw [hact' σ z, e1, e2]
  obtain ⟨σ₁, hσ₁⟩ := hbij.2 ((1 : ℤ), (0 : ℤ))
  obtain ⟨σ₂, hσ₂⟩ := hbij.2 ((0 : ℤ), (1 : ℤ))
  refine ⟨⟨σ₁, σ₁.2, fun z => ?_⟩, ⟨σ₂, σ₂.2, fun z => ?_⟩⟩
  · rw [hval σ₁ 1 0 (by simpa using hσ₁) z]
    norm_num
  · rw [hval σ₂ 0 1 (by simpa using hσ₂) z]
    norm_num

theorem commutator_perfect_of_ker_le_center {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : f.ker ≤ Subgroup.center G) (S : Subgroup G) (hS : ⁅S.map f, S.map f⁆ = S.map f) :
    ⁅⁅S, S⁆, ⁅S, S⁆⁆ = ⁅S, S⁆ ∧ (⁅S, S⁆ : Subgroup G).map f = S.map f := by
  have hmap : (⁅S, S⁆ : Subgroup G).map f = S.map f := by
    rw [Subgroup.map_commutator, hS]
  refine ⟨le_antisymm (Subgroup.commutator_le_self _) ?_, hmap⟩
  have hsplit : ∀ s ∈ S, ∃ d ∈ (⁅S, S⁆ : Subgroup G), ∃ z ∈ Subgroup.center G, s = d * z := by
    intro s hs
    have h1 : f s ∈ (⁅S, S⁆ : Subgroup G).map f := hmap ▸ ⟨s, hs, rfl⟩
    obtain ⟨d, hd, hds⟩ := h1
    refine ⟨d, hd, d⁻¹ * s, hf ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hds, inv_mul_cancel]
  rw [Subgroup.commutator_le]
  intro s₁ hs₁ s₂ hs₂
  obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := hsplit s₁ hs₁
  obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := hsplit s₂ hs₂
  have hc : ⁅d₁ * z₁, d₂ * z₂⁆ = ⁅d₁, d₂⁆ := by
    have c1 := Subgroup.mem_center_iff.mp hz₁
    have c2 := Subgroup.mem_center_iff.mp hz₂
    have e1 : z₁ * (d₂ * z₂) * z₁⁻¹ = d₂ * z₂ := by
      rw [← c1 (d₂ * z₂), mul_inv_cancel_right]
    have e2 : z₂ * d₁⁻¹ = d₁⁻¹ * z₂ := (c2 d₁⁻¹).symm
    calc ⁅d₁ * z₁, d₂ * z₂⁆ = d₁ * (z₁ * (d₂ * z₂) * z₁⁻¹) * d₁⁻¹ * (d₂ * z₂)⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = d₁ * d₂ * (z₂ * d₁⁻¹) * z₂⁻¹ * d₂⁻¹ := by
          rw [e1]
          group
      _ = ⁅d₁, d₂⁆ := by
          rw [e2, commutatorElement_def]
          group
  rw [hc]
  exact Subgroup.commutator_mem_commutator hd₁ hd₂

theorem commute_of_comm_scalar_of_pow {F : Type} [Field F] {a b : GL (Fin 3) F}
    (hab : a * b * a⁻¹ * b⁻¹ ∈ StatedScalars (Fin 3) F) {r : ℕ} (hr : Nat.Coprime r 3)
    (har : a ^ r ∈ StatedScalars (Fin 3) F) : a * b = b * a := by
  obtain ⟨c, hc⟩ := hab
  obtain ⟨μ, hμ⟩ := har
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hinj : ∀ u v : Fˣ, GeneralLinearGroup.scalar (Fin 3) u =
      GeneralLinearGroup.scalar (Fin 3) v → u = v := by
    intro u v h
    have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp [GeneralLinearGroup.coe_scalar] at h1
    exact Units.ext h1
  have h1 : a * b * a⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * b := by
    rw [hc]
    group
  have hn : ∀ n : ℕ, a ^ n * b * (a ^ n)⁻¹ = GeneralLinearGroup.scalar (Fin 3) (c ^ n) * b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by group
        _ = a * (GeneralLinearGroup.scalar (Fin 3) (c ^ n) * b) * a⁻¹ := by rw [ih]
        _ = (a * GeneralLinearGroup.scalar (Fin 3) (c ^ n)) * b * a⁻¹ := by group
        _ = (GeneralLinearGroup.scalar (Fin 3) (c ^ n) * a) * b * a⁻¹ := by rw [hsc]
        _ = GeneralLinearGroup.scalar (Fin 3) (c ^ n) * (a * b * a⁻¹) := by group
        _ = GeneralLinearGroup.scalar (Fin 3) (c ^ (n + 1)) * b := by
          rw [h1, ← mul_assoc, ← map_mul, pow_succ]
  have hcr : c ^ r = 1 := by
    have h2 := hn r
    have h3 : a ^ r * b * (a ^ r)⁻¹ = b := by
      rw [← hμ, ← hsc μ b, mul_inv_cancel_right]
    rw [h3] at h2
    apply hinj
    rw [map_one]
    have h4 : GeneralLinearGroup.scalar (Fin 3) (c ^ r) * b = 1 * b := by rw [← h2, one_mul]
    exact mul_right_cancel h4
  have hc3 : c ^ 3 = 1 := by
    have h2 := congrArg (fun g : GL (Fin 3) F => Matrix.GeneralLinearGroup.det g) hc
    simp only [map_mul, map_inv] at h2
    have h3 : Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) c) = c ^ 3 := by
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar,
        Matrix.det_diagonal, Fin.prod_univ_three, pow_succ]
    rw [h3, mul_right_comm, mul_inv_cancel_right, mul_inv_cancel] at h2
    exact h2
  have hc1 : c = 1 := by
    have h := (pow_gcd_eq_one (a := c)).mpr ⟨hcr, hc3⟩
    rwa [hr.gcd_eq_one, pow_one] at h
  rw [hc1, map_one] at hc
  have h5 : a * b * a⁻¹ * b⁻¹ * (b * a) = b * a := by rw [← hc, one_mul]
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := h5

theorem zeta_pow_three_of_heis {F : Type} [Field F] {y₁ y₂ : GL (Fin 3) F} {ζ : Fˣ}
    (hy₁3 : y₁ ^ 3 ∈ StatedScalars (Fin 3) F)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) : ζ ^ 3 = 1 := by
  obtain ⟨μ, hμ⟩ := hy₁3
  have hsc : ∀ (u : Fˣ) (A : GL (Fin 3) F),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have hn : ∀ n : ℕ, y₁ ^ n * y₂ * (y₁ ^ n)⁻¹ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ n) * y₂ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc y₁ ^ (n + 1) * y₂ * (y₁ ^ (n + 1))⁻¹ = y₁ * (y₁ ^ n * y₂ * (y₁ ^ n)⁻¹) * y₁⁻¹ := by
            group
        _ = (y₁ * GeneralLinearGroup.scalar (Fin 3) (ζ ^ n)) * y₂ * y₁⁻¹ := by rw [ih]; group
        _ = (GeneralLinearGroup.scalar (Fin 3) (ζ ^ n) * y₁) * y₂ * y₁⁻¹ := by rw [hsc]
        _ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ n) * (y₁ * y₂ * y₁⁻¹) := by group
        _ = GeneralLinearGroup.scalar (Fin 3) (ζ ^ (n + 1)) * y₂ := by
          rw [hζ, ← mul_assoc, ← map_mul, pow_succ]
  have h2 := hn 3
  rw [← hμ, ← hsc μ y₂, mul_inv_cancel_right] at h2
  have h3 : GeneralLinearGroup.scalar (Fin 3) (ζ ^ 3) * y₂ = 1 * y₂ := by rw [← h2, one_mul]
  have h4 := mul_right_cancel h3
  have hinj1 : ∀ u : Fˣ, GeneralLinearGroup.scalar (Fin 3) u = 1 → u = 1 := by
    intro u h
    have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp [GeneralLinearGroup.coe_scalar] at h1
    exact h1
  exact hinj1 _ h4

theorem commute_of_cyclic_normal {G : Type*} [Group G] [Group.IsPerfect G] {H : Subgroup G}
    [H.Normal] [IsCyclic H] (g : G) {h : G} (hh : h ∈ H) : g * h = h * g := by
  let ψ : G →* (ZMod (Nat.card H))ˣ :=
    (IsCyclic.mulAutMulEquiv (G := H)).toMonoidHom.comp (MulAut.conjNormal (H := H))
  have hker : ψ.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G)]
    exact Abelianization.commutator_subset_ker ψ
  have h1 : ψ g = 1 := (MonoidHom.mem_ker).mp (hker ▸ Subgroup.mem_top g)
  have h2 : MulAut.conjNormal (H := H) g = 1 := by
    apply (IsCyclic.mulAutMulEquiv (G := H)).injective
    rw [map_one]
    exact h1
  have h3 := congrArg (fun α : MulAut H => ((α ⟨h, hh⟩ : H) : G)) h2
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc g * h = g * h * g⁻¹ * g := by group
    _ = h * g := by rw [h3]

theorem scalar_of_abelian_normal_of_perfect {F : Type} [Field F] [Finite F]
    {D : Subgroup (GL (Fin 3) F)} [Group.IsPerfect D] (hD : SubgroupLists.IsIrreducibleOn D)
    {B : Subgroup (GL (Fin 3) F)} (hBD : B ≤ D) (hBn : ∀ g ∈ D, ∀ x ∈ B, g * x * g⁻¹ ∈ B)
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) :
    ∀ x ∈ B, ∃ c : F, (x : Matrix (Fin 3) (Fin 3) F) = Matrix.scalar (Fin 3) c := by
  have hG := SubgroupLists.isIrreducibleOn_iff.mp hD
  rcases SubgroupLists.irreducible_prime_degree_reduction Nat.prime_three hG with
      ⟨H, hHD, hHn, hHirr, hHcyc, -, -⟩ | hmono | ⟨-, -, habel⟩
  · exfalso
    set H' : Subgroup D := H.subgroupOf D with hH'
    haveI : H'.Normal := ⟨fun x hx g => by
      rw [hH', Subgroup.mem_subgroupOf] at hx ⊢
      exact hHn g g.2 x hx⟩
    haveI : IsCyclic H' := isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHD).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHD).symm.surjective
    have hcomm : ∀ g ∈ D, ∀ h ∈ H, g * h = h * g := by
      intro g hg h hh
      have hh' : (⟨h, hHD hh⟩ : D) ∈ H' := by
        rw [hH', Subgroup.mem_subgroupOf]
        exact hh
      have := commute_of_cyclic_normal (H := H') ⟨g, hg⟩ hh'
      exact congrArg Subtype.val this
    rcases SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hG with hsc | ⟨hcyc, -, -⟩
    · refine SubgroupLists.not_irreducible_of_forall_scalar (by norm_num) (fun h hh => ?_) hHirr
      exact hsc _ fun g hg => by rw [← Units.val_mul, ← Units.val_mul, hcomm g hg h hh]
    ·
      haveI : IsCyclic D := hcyc
      have hD1 : ∀ g : D, g = 1 := by
        intro g
        have hc : commutator D = ⊥ := by
          rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro x _ y _
          exact (IsCyclic.commutative.is_comm.comm x y).symm
        have hg : g ∈ commutator D := by
          rw [Group.IsPerfect.commutator_eq_top]
          exact Subgroup.mem_top g
        rw [hc] at hg
        exact Subgroup.mem_bot.mp hg
      refine SubgroupLists.not_irreducible_of_forall_scalar (by norm_num) (fun h hh => ?_) hHirr
      have : (⟨h, hHD hh⟩ : D) = 1 := hD1 _
      have h1 : h = 1 := congrArg Subtype.val this
      exact ⟨1, by rw [h1]; simp⟩
  · exact absurd hmono SubgroupLists.not_isTransitiveMonomial_of_perfect
  · exact habel B hBD hBn hBc

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
