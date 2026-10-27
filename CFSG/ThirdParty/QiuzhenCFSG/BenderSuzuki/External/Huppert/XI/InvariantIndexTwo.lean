module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Residual
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.Semidirect
import Mathlib.GroupTheory.IndexNormal
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.BenderSuzuki.External

universe u

/--
Huppert III.8.8, in the exact invariant-index-two form used by XI.2.5.
An involution on a nontrivial finite `2`-group fixes a maximal subgroup.
-/
public theorem huppert_III_8_8_exists_invariant_index_two_of_involutive_aut
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hPne : Nontrivial P)
    (φ : MulAut P) (hφ : Function.Involutive φ) :
    ∃ M : Subgroup P,
      M.Normal ∧ M.index = 2 ∧ ∀ x : P, x ∈ M ↔ φ x ∈ M := by
  classical
  letI : Nontrivial P := hPne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 P) := ⟨hP⟩
  letI : (frattini P).Characteristic := frattini_characteristic
  have hΦne : frattini P ≠ ⊤ := by
    intro hΦtop
    have hbotTop : (⊥ : Subgroup P) = ⊤ :=
      frattini_nongenerating (K := (⊥ : Subgroup P)) (by simp [hΦtop])
    exact bot_ne_top hbotTop
  letI : Nontrivial (P ⧸ frattini P) :=
    QuotientGroup.nontrivial_iff.mpr hΦne
  have hΦinv : ∀ x : P, x ∈ frattini P ↔ φ x ∈ frattini P :=
    fun x => hkt_characteristic_subgroup_invariant φ (frattini P) x
  let φQ : MulAut (P ⧸ frattini P) :=
    invariantQuotientAut φ (frattini P) hΦinv
  have hφQ : Function.Involutive φQ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) q
    simp only [φQ, invariantQuotientAut_mk']
    rw [hφ x]
  have hQelem : IsElementaryAbelian 2 (P ⧸ frattini P) :=
    isElementaryAbelian_quotient_frattini
  letI : IsElementaryAbelian 2 (P ⧸ frattini P) := hQelem
  letI : CommGroup (P ⧸ frattini P) := IsMulCommutative.instCommGroup
  let V := Additive (P ⧸ frattini P)
  letI : AddCommGroup V := Additive.addCommGroup
  letI : Module (ZMod 2) V := inferInstance
  letI : Finite V := inferInstance
  letI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  letI : Nontrivial V := inferInstance
  let eAdd : V ≃+ V := MulEquiv.toAdditive φQ
  let eLin : V ≃ₗ[ZMod 2] V :=
    eAdd.toLinearEquiv (fun c x => by
      simpa using (ZMod.map_smul eAdd.toAddMonoidHom c x))
  have heLin : Function.Involutive eLin := by
    intro x
    change Additive.ofMul (φQ (φQ (Additive.toMul x))) = x
    simpa using congrArg Additive.ofMul (hφQ (Additive.toMul x))
  let D := Module.Dual (ZMod 2) V
  let dLin : D ≃ₗ[ZMod 2] D := eLin.dualMap
  have hdLin : Function.Involutive dLin := by
    intro g
    apply LinearMap.ext
    intro x
    change g (eLin (eLin x)) = g x
    rw [heLin x]
  have hDnontrivial : Nontrivial D := by
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hx
    apply nontrivial_of_ne g 0
    intro hzero
    apply hg
    rw [hzero]
    simp
  letI : Nontrivial D := hDnontrivial
  letI : Finite D := Finite.of_injective
    (fun f : D => (f : V → ZMod 2)) (by
      intro f g hfg
      apply LinearMap.ext
      intro x
      exact congrFun hfg x)
  letI : Fintype D := Fintype.ofFinite D
  have hfinrankDpos : 0 < Module.finrank (ZMod 2) D := Module.finrank_pos
  have hcardD : Nat.card D = 2 ^ Module.finrank (ZMod 2) D := by
    simpa [D, Nat.card_eq_fintype_card, ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D))
  have hDcardEven : 2 ∣ Fintype.card D := by
    rw [← Nat.card_eq_fintype_card, hcardD]
    exact even_iff_two_dvd.mp
      (Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hfinrankDpos⟩)
  let σ : Equiv.Perm D := dLin.toEquiv
  have hσsq : σ ^ 2 ^ 1 = 1 := by
    simp only [pow_one, pow_two]
    apply Equiv.Perm.ext
    intro g
    exact hdLin g
  obtain ⟨g, hgfix, hgne⟩ :=
    Equiv.Perm.exists_fixed_point_of_prime'
      (p := 2) (n := 1) hDcardEven hσsq
      (a := (0 : D)) (by simp [σ, dLin])
  have hgsurj : Function.Surjective g :=
    LinearMap.surjective_iff_ne_zero.mpr hgne
  let χ : (P ⧸ frattini P) →* Multiplicative (ZMod 2) :=
    AddMonoidHom.toMultiplicativeRight g.toAddMonoidHom
  have hχsurj : Function.Surjective χ := by
    intro y
    obtain ⟨x, hx⟩ := hgsurj (Multiplicative.toAdd y)
    refine ⟨Additive.toMul x, ?_⟩
    simpa [χ] using congrArg Multiplicative.ofAdd hx
  have hg_invariant (q : P ⧸ frattini P) :
      g (Additive.ofMul (φQ q)) = g (Additive.ofMul q) := by
    have h := congrArg (fun f : D => f (Additive.ofMul q)) hgfix
    change g (Additive.ofMul (φQ q)) = g (Additive.ofMul q) at h
    exact h
  have hχ_invariant (q : P ⧸ frattini P) : χ (φQ q) = χ q := by
    simpa [χ] using congrArg Multiplicative.ofAdd (hg_invariant q)
  let ψ : P →* Multiplicative (ZMod 2) :=
    χ.comp (QuotientGroup.mk' (frattini P))
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨q, hq⟩ := hχsurj y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) q
    exact ⟨x, hq⟩
  have hψrange : ψ.range = ⊤ := MonoidHom.range_eq_top.mpr hψsurj
  have hψindex : ψ.ker.index = 2 := by
    rw [Subgroup.index_ker, hψrange]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  refine ⟨ψ.ker, Subgroup.normal_of_index_eq_two hψindex, hψindex, ?_⟩
  intro x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  have hψφ : ψ (φ x) = ψ x := by
    calc
      ψ (φ x) = χ (QuotientGroup.mk' (frattini P) (φ x)) := rfl
      _ = χ (φQ (QuotientGroup.mk' (frattini P) x)) := by
        rw [invariantQuotientAut_mk']
      _ = χ (QuotientGroup.mk' (frattini P) x) := hχ_invariant _
      _ = ψ x := rfl
  rw [hψφ]

/--
Huppert XI.2.5(a), residual-quotient step. If the 2-residual is proper, an
involutive automorphism fixes a normal subgroup of index two.
-/
public theorem huppert_XI_2_5_invariantIndexTwo_of_pResidual_ne_top
    {G : Type u} [Group G] [Finite G]
    (φ : MulAut G) (hφ : Function.Involutive φ)
    (hres : hktPResidual 2 G ≠ ⊤) :
    ∃ M : Subgroup G,
      M.Normal ∧ M.index = 2 ∧ ∀ x : G, x ∈ M ↔ φ x ∈ M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup G := hktPResidual 2 G
  have hRnormal : R.Normal := by
    simpa [R] using hktPResidual_normal (Q := G) (q := 2)
  letI : R.Normal := hRnormal
  have hRinv : ∀ x : G, x ∈ R ↔ φ x ∈ R := by
    simpa [R] using hktPResidual_invariant (p := 2) φ
  let φQ : MulAut (G ⧸ R) := invariantQuotientAut φ R hRinv
  have hφQ : Function.Involutive φQ := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R q
    simp only [φQ, invariantQuotientAut_mk']
    rw [hφ x]
  have hQp : IsPGroup 2 (G ⧸ R) := by
    simpa [R] using hktPResidual_quotient_isPGroup (Q := G) (q := 2)
  have hQne : Nontrivial (G ⧸ R) := by
    apply QuotientGroup.nontrivial_iff.mpr
    simpa [R] using hres
  obtain ⟨Mbar, hMbarNormal, hMbarIndex, hMbarInv⟩ :=
    huppert_III_8_8_exists_invariant_index_two_of_involutive_aut
      hQp hQne φQ hφQ
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  let M : Subgroup G := Mbar.comap π
  have hMnormal : M.Normal := by
    simpa [M] using hMbarNormal.comap π
  have hMindex : M.index = 2 := by
    calc
      M.index = Mbar.index := by
        simpa [M, π] using
          (Subgroup.index_comap_of_surjective
            (H := Mbar) (f := π) (QuotientGroup.mk'_surjective R))
      _ = 2 := hMbarIndex
  refine ⟨M, hMnormal, hMindex, ?_⟩
  intro x
  change π x ∈ Mbar ↔ π (φ x) ∈ Mbar
  have hφπ : φQ (π x) = π (φ x) := by
    exact invariantQuotientAut_mk' φ R hRinv x
  rw [← hφπ]
  exact hMbarInv (π x)
end CFSG.BenderSuzuki.External
