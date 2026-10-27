module

public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.Vol2.Ch11
open scoped commutatorElement

theorem sigmaFacts_of_fixed_perfect_model
    {G X : Type} [Group G] [Group X] {L : Subgroup G} [L.Normal]
    (e : ↥L ≃* X) {b : G} {N : Subgroup X}
    (hNsimple : IsSimpleGroup N)
    (hNperfect : Group.IsPerfect N)
    (hfixed : ∀ n ∈ N, MulAut.congr e (MulAut.conjNormal b) n = n)
    (hcomm : ∀ x y : X, MulAut.congr e (MulAut.conjNormal b) x = x →
      MulAut.congr e (MulAut.conjNormal b) y = y → ⁅x, y⁆ ∈ N)
    (hcentralizer : Subgroup.centralizer (N : Set X) = ⊥) :
    SecU1.SigmaFacts L b := by
  classical
  let σ : MulAut ↥L := MulAut.conjNormal b
  let β : MulAut X := MulAut.congr e σ
  let j : X →* G := L.subtype.comp e.symm.toMonoidHom
  have hj_inj : Function.Injective j := L.subtype_injective.comp e.symm.injective
  have hj_range : j.range = L := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (e.symm x).2
    · intro g hg
      exact ⟨e ⟨g, hg⟩, by simp [j]⟩
  let C : Subgroup G := L ⊓ Subgroup.centralizer ({b} : Set G)
  let CX : Subgroup X := C.comap j
  have hCX_map : CX.map j = C := by
    refine Subgroup.map_comap_eq_self ?_
    rw [hj_range]
    exact inf_le_left
  have hCX_iff : ∀ x : X, x ∈ CX ↔ β x = x := by
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_comap] at hx
      have hcomm' : ((e.symm x : ↥L) : G) * b = b * ((e.symm x : ↥L) : G) := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hx.2
        simpa [j] using h
      have hfix : σ (e.symm x) = e.symm x := by
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        calc b * ((e.symm x : ↥L) : G) * b⁻¹ =
            ((e.symm x : ↥L) : G) * b * b⁻¹ := by rw [← hcomm']
          _ = ((e.symm x : ↥L) : G) := by group
      have h2 : e (σ (e.symm x)) = x := by
        rw [hfix, MulEquiv.apply_symm_apply]
      simpa [β, MulAut.congr_apply] using h2
    · intro hx
      rw [Subgroup.mem_comap]
      change j x ∈ L ⊓ Subgroup.centralizer ({b} : Set G)
      refine ⟨(e.symm x).2, ?_⟩
      change j x ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change ((e.symm x : ↥L) : G) * b = b * ((e.symm x : ↥L) : G)
      have h2 : e (σ (e.symm x)) = x := by
        simpa [β, MulAut.congr_apply] using hx
      have hfix : σ (e.symm x) = e.symm x := by
        apply e.injective
        simpa [MulEquiv.apply_symm_apply] using h2
      have hfix' : b * ((e.symm x : ↥L) : G) * b⁻¹ = ((e.symm x : ↥L) : G) := by
        have h1 := congrArg (fun k : ↥L => (k : G)) hfix
        simpa [σ, MulAut.conjNormal_apply, Subtype.coe_mk] using h1
      calc ((e.symm x : ↥L) : G) * b =
          (b * ((e.symm x : ↥L) : G) * b⁻¹) * b := by rw [hfix']
        _ = b * ((e.symm x : ↥L) : G) := by group
  have hN_le_CX : N ≤ CX := fun n hn => (hCX_iff n).2 (hfixed n hn)
  have hN_eq_comm : N = ⁅CX, CX⁆ := by
    apply le_antisymm
    · calc N = ⁅N, N⁆ := (Subgroup.isPerfect_iff.mp hNperfect).symm
        _ ≤ ⁅CX, CX⁆ := Subgroup.commutator_mono hN_le_CX hN_le_CX
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      exact hcomm x y ((hCX_iff x).1 hx) ((hCX_iff y).1 hy)
  let NG : Subgroup G := N.map j
  have hNG_eq_comm : NG = ⁅C, C⁆ := by
    change N.map j = ⁅C, C⁆
    rw [hN_eq_comm, Subgroup.map_commutator, hCX_map]
  have hLnorm : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top (h := ‹L.Normal›)]
    exact le_top
  have hCnorm : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    (le_inf hLnorm Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcommnorm : Subgroup.centralizer ({b} : Set G) ≤
      Subgroup.normalizer ((⁅C, C⁆ : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _
      C C hCnorm hCnorm
  have hNGnorm : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (NG : Set G) := by
    rw [hNG_eq_comm]
    exact hcommnorm
  have hCL_NG : L ⊓ Subgroup.centralizer (NG : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgL, hgC⟩
    rw [Subgroup.mem_bot]
    let x : X := e ⟨g, hgL⟩
    have hgx : j x = g := by simp [j, x]
    have hxcent : x ∈ Subgroup.centralizer (N : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      apply hj_inj
      simpa [map_mul, hgx] using
        Subgroup.mem_centralizer_iff.mp hgC (j n) (Subgroup.mem_map_of_mem j hn)
    rw [hcentralizer, Subgroup.mem_bot] at hxcent
    calc g = j x := hgx.symm
      _ = 1 := by rw [hxcent]; simp
  haveI : IsSimpleGroup ↥N := hNsimple
  haveI : Group.IsPerfect ↥N := hNperfect
  let eN : ↥N ≃* ↥NG := Subgroup.equivMapOfInjective N j hj_inj
  haveI : IsSimpleGroup ↥NG := eN.symm.isSimpleGroup
  haveI : Group.IsPerfect ↥NG :=
    Group.IsPerfect.ofSurjective (f := eN.toMonoidHom) eN.surjective
  have hnc : ¬ IsMulCommutative ↥NG := Group.IsPerfect.not_isMulCommutative ↥NG
  have hnonab : ∃ x y : ↥NG, x * y ≠ y * x := by
    by_contra h
    exact hnc (isMulCommutative_iff.mpr fun x y => by
      by_contra hxy
      exact h ⟨x, y, hxy⟩)
  have hNG_le_C : NG ≤ C := by
    rw [hNG_eq_comm]
    exact Subgroup.commutator_le_self C
  refine ⟨NG, ?_, eN.symm.isSimpleGroup, hnonab, hNGnorm, hCL_NG⟩
  exact le_inf (hNG_le_C.trans inf_le_left) (hNG_le_C.trans inf_le_right)

theorem sigmaFacts_of_fixed_commutator
    {G : Type} [Group G] {L : Subgroup G} [L.Normal] {b : G} {N : Subgroup ↥L}
    (hfixed : ∀ n ∈ N, MulAut.conjNormal b n = n)
    (hsimple : IsSimpleGroup ↥N)
    (hperfect : Group.IsPerfect ↥N)
    (hcomm : ∀ x y : ↥L, MulAut.conjNormal b x = x → MulAut.conjNormal b y = y →
      ⁅x, y⁆ ∈ N)
    (hcent : Subgroup.centralizer (N : Set ↥L) = ⊥) :
    SecU1.SigmaFacts L b := by
  have hcongr : MulAut.congr (MulEquiv.refl ↥L) (MulAut.conjNormal b) = MulAut.conjNormal b := by
    ext x
    rfl
  refine sigmaFacts_of_fixed_perfect_model (MulEquiv.refl ↥L) hsimple hperfect ?_ ?_ hcent
  · intro n hn
    rw [hcongr]
    exact hfixed n hn
  · intro x y hx hy
    rw [hcongr] at hx hy
    exact hcomm x y hx hy

end CFSG.LocalAnalysis.WeakClosure81

end
