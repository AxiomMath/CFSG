module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel
public import CFSG.LocalAnalysis.StandardType.GGWPlusPerm
public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAutPerm
public import CFSG.LocalAnalysis.StandardType.GGWPlusUnitAutModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.StandardType.LineU CFSG.StandardType.UnitAct

private noncomputable def ggPermConjSU {n d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (hK : UnitaryFieldData 2 n K) (φ : ↥(unitarySU 2 n K d) →* L') :
    Equiv.Perm (Fin d) →* MulAut L' where
  toFun σ := MulAut.conj (φ (permSU hK σ))
  map_one' := by rw [permSU_one, map_one, map_one]
  map_mul' σ τ := by rw [permSU_mul, map_mul, map_mul]

private theorem ggPermConjSU_apply {n d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    (hK : UnitaryFieldData 2 n K) (φ : ↥(unitarySU 2 n K d) →* L')
    (σ : Equiv.Perm (Fin d)) :
    ggPermConjSU hK φ σ = MulAut.conj (φ (permSU hK σ)) := rfl

private noncomputable def ggAutActU {G : Type} [Group G] (H B : Subgroup G) :
    ↥(H ⊓ Subgroup.normalizer (B : Set G)) →* MulAut ↥B where
  toFun x := ggConjAut B (Subgroup.mem_inf.mp x.2).2
  map_one' := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.one_apply]
    simp only [Subgroup.coe_one]
    group
  map_mul' x y := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group

private theorem ggAutActU_apply {G : Type} [Group G] (H B : Subgroup G)
    (x : ↥(H ⊓ Subgroup.normalizer (B : Set G))) :
    ggAutActU H B x = ggConjAut B (Subgroup.mem_inf.mp x.2).2 := rfl

private theorem ggConjAut_eq_one_iffU {G : Type} [Group G] (B : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) :
    ggConjAut B hg = 1 ↔ g ∈ Subgroup.centralizer (B : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have h1 := congrArg (fun f : MulAut ↥B => ((f ⟨b, hb⟩ : ↥B) : G)) h
    simp only [ggConjAut_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro hx
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.one_apply]
    have hb := (Subgroup.mem_centralizer_iff.mp hx) b b.2
    rw [← hb, mul_assoc, mul_inv_cancel, mul_one]

private noncomputable def ggPermAutU {d : ℕ} {R : Type} [Group R]
    (Eb : Subgroup (MulAut R)) (g : Equiv.Perm (Fin d) →* MulAut R)
    (hN : ∀ σ, g σ ∈ Subgroup.normalizer (Eb : Set (MulAut R))) :
    Equiv.Perm (Fin d) →* MulAut ↥Eb where
  toFun σ := ggConjAut Eb (hN σ)
  map_one' := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.one_apply, map_one, one_mul, inv_one, mul_one]
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [ggConjAut_apply, MulAut.mul_apply, ggConjAut_apply, ggConjAut_apply, map_mul]
    group

private theorem ggPermAutU_apply {d : ℕ} {R : Type} [Group R]
    (Eb : Subgroup (MulAut R)) (g : Equiv.Perm (Fin d) →* MulAut R)
    (hN : ∀ σ, g σ ∈ Subgroup.normalizer (Eb : Set (MulAut R)))
    (σ : Equiv.Perm (Fin d)) : ggPermAutU Eb g hN σ = ggConjAut Eb (hN σ) := rfl

private theorem conj_mul_inv_eq_of_fixed {G : Type} [Group G] (a : MulAut G) {z : G}
    (hz : a z = z) : MulAut.conj z * a * (MulAut.conj z)⁻¹ = a := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv, hz]
  group

theorem exists_automizer_hom_PSU
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    (hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤)
    {Eb : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hA : IsElemAbelian p Eb)
    (hI : (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (hr : p ^ (d - 2) ≤ Nat.card Eb) (hsc : GGTorusSelfCent p Eb) :
    ∃ ρ : ↥((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).range ⊓ Subgroup.normalizer (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))) →* Equiv.Perm (Fin d),
      Function.Surjective ρ ∧
        ρ.ker ≤ (Subgroup.centralizer (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))).subgroupOf ((MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))).range ⊓ Subgroup.normalizer (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))))) := by
  classical
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hAp : ∀ a ∈ Eb, a ^ p = 1 := hA.2
  obtain ⟨φ, hM, hdiag⟩ :=
    exists_diagModel_PSU hK hn hd hp hpq hpd hperf hA hI hr
  let R := LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))
  let permConjU : Equiv.Perm (Fin d) →* MulAut R := ggPermConjSU hM.field φ
  have permConjU_apply : ∀ σ : Equiv.Perm (Fin d),
      permConjU σ = MulAut.conj (φ (permSU hM.field σ)) :=
    fun σ => ggPermConjSU_apply hM.field φ σ
  have hN : ∀ σ : Equiv.Perm (Fin d),
      permConjU σ ∈ Subgroup.normalizer (Eb : Set (MulAut R)) := by
    intro σ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [permConjU_apply σ]
      exact UnitTv.conj_perm_mem hM (by omega : 3 ≤ d) hAp hsc hdiag σ hh
    · intro hh
      have h2 := UnitTv.conj_perm_mem hM (by omega : 3 ≤ d) hAp hsc hdiag (σ⁻¹) hh
      have hinv : permConjU σ⁻¹ = (permConjU σ)⁻¹ := map_inv permConjU σ
      rw [← permConjU_apply (σ⁻¹), hinv] at h2
      have heq : (permConjU σ)⁻¹ * (permConjU σ * h * (permConjU σ)⁻¹) *
          ((permConjU σ)⁻¹)⁻¹ = h := by group
      rwa [heq] at h2
  have hInj : Function.Injective (ggPermAutU Eb permConjU hN) := by
    refine (injective_iff_map_eq_one (ggPermAutU Eb permConjU hN)).mpr fun σ hσ => ?_
    have hcomm : ∀ b ∈ Eb, permConjU σ * b * (permConjU σ)⁻¹ = b := by
      intro b hb
      have h := congrArg (fun f : MulAut ↥Eb => ((f ⟨b, hb⟩ : ↥Eb) : MulAut R)) hσ
      rw [ggPermAutU_apply, ggConjAut_apply, MulAut.one_apply] at h
      simpa using h
    exact UnitTB.permSU_eq_one_of_conj_comm hM hp hp2 hpq (by omega) hsc hdiag (fun b hb => by
      have h := hcomm b hb
      rwa [permConjU_apply σ] at h)
  have hAut : ggAutomizer (MulAut.conj : R →* MulAut R).range Eb =
      (ggPermAutU Eb permConjU hN).range := by
    refine le_antisymm ?_ ?_
    · intro ψ hψ
      obtain ⟨g, ⟨w, rfl⟩, hgN, hψg⟩ := mem_ggAutomizer_iff.mp hψ
      obtain ⟨w', hw'mem, hfix⟩ :=
        UnitAct.exists_weyl_fix hM hK hp hp2 hpq (by omega) hA hsc hdiag (w := w) hgN
      obtain ⟨σ, hσw⟩ := hw'mem
      refine MonoidHom.mem_range.mpr ⟨σ, ?_⟩
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [ggPermAutU_apply, ggConjAut_apply, permConjU_apply, hψg, ← hσw]
      set c : MulAut R := MulAut.conj w' * (b : MulAut R) * (MulAut.conj w')⁻¹ with hcdef
      have hc_mem : c ∈ Eb := by
        rw [hcdef, hσw, ← permConjU_apply σ]
        exact (Subgroup.mem_normalizer_iff.mp (hN σ) b).mp b.2
      have hfixz : c (w * w'⁻¹) = w * w'⁻¹ := hfix c hc_mem
      have hcz : MulAut.conj (w * w'⁻¹) * c * (MulAut.conj (w * w'⁻¹))⁻¹ = c :=
        conj_mul_inv_eq_of_fixed c hfixz
      have hw_eq : MulAut.conj (w * w'⁻¹) * MulAut.conj w' = MulAut.conj w := by
        rw [← map_mul, show (w * w'⁻¹) * w' = w by group]
      calc c = MulAut.conj (w * w'⁻¹) * c * (MulAut.conj (w * w'⁻¹))⁻¹ := hcz.symm
        _ = MulAut.conj w * (b : MulAut R) * (MulAut.conj w)⁻¹ := by
              rw [hcdef, ← hw_eq]
              group
    · rintro _ ⟨σ, rfl⟩
      rw [ggPermAutU_apply]
      exact ggConjAut_mem_ggAutomizer
        (H := (MulAut.conj : R →* MulAut R).range) (Bs := Eb) (g := permConjU σ)
        (MonoidHom.mem_range.mpr ⟨φ (permSU hM.field σ), (permConjU_apply σ).symm⟩) (hN σ)
  set Inn : Subgroup (MulAut R) := (MulAut.conj : R →* MulAut R).range with hInn
  set X : Subgroup (MulAut R) := Inn ⊓ Subgroup.normalizer (Eb : Set (MulAut R)) with hX
  set C : Subgroup (MulAut R) := Subgroup.centralizer (Eb : Set (MulAut R)) with hC
  let act : ↥X →* MulAut ↥Eb := ggAutActU Inn Eb
  have hact_apply : ∀ x : ↥X, act x = ggConjAut Eb ((Subgroup.mem_inf.mp x.2).2) :=
    fun x => ggAutActU_apply Inn Eb x
  have hact_one : ∀ x : ↥X, act x = 1 ↔ (x : MulAut R) ∈ C := by
    intro x
    rw [hact_apply x]
    exact ggConjAut_eq_one_iffU Eb (Subgroup.mem_inf.mp x.2).2
  let e : Equiv.Perm (Fin d) ≃* (ggPermAutU Eb permConjU hN).range :=
    MonoidHom.ofInjective hInj
  let actR : ↥X →* (ggPermAutU Eb permConjU hN).range :=
    act.codRestrict (ggPermAutU Eb permConjU hN).range (fun x => by
      rw [hact_apply x, ← hAut]
      exact ggConjAut_mem_ggAutomizer (Subgroup.mem_inf.mp x.2).1 (Subgroup.mem_inf.mp x.2).2)
  let ρ : ↥X →* Equiv.Perm (Fin d) := e.symm.toMonoidHom.comp actR
  have hρ : Function.Surjective ρ := by
    intro σ
    have hmem : ggPermAutU Eb permConjU hN σ ∈ ggAutomizer Inn Eb := by
      rw [hAut]
      exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩
    obtain ⟨g, hgInn, hgNorm, hgform⟩ := mem_ggAutomizer_iff.mp hmem
    let x0 : ↥X := ⟨g, Subgroup.mem_inf.mpr ⟨hgInn, hgNorm⟩⟩
    refine ⟨x0, ?_⟩
    have hact_eq : act x0 = ggPermAutU Eb permConjU hN σ := by
      apply MulEquiv.ext
      intro b
      apply Subtype.ext
      rw [hact_apply x0, ggConjAut_apply]
      exact (hgform b).symm
    have hactR : actR x0 = e σ := by
      apply Subtype.ext
      change act x0 = ggPermAutU Eb permConjU hN σ
      exact hact_eq
    show ρ x0 = σ
    rw [show ρ x0 = e.symm (actR x0) from rfl, hactR, MulEquiv.symm_apply_apply]
  have hker : ρ.ker ≤ C.subgroupOf X := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    rw [← hact_one x]
    have h2 : actR x = 1 := by
      have h3 : e (ρ x) = e 1 := congrArg e hx
      rw [show ρ x = e.symm (actR x) from rfl] at h3
      simpa using h3
    have h4 := congrArg (fun y : (ggPermAutU Eb permConjU hN).range =>
      (y : MulAut ↥Eb)) h2
    exact h4
  exact ⟨ρ, hρ, hker⟩

end CFSG.StandardType
