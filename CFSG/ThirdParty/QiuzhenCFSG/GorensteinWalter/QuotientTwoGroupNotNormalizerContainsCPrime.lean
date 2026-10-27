module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
import Mathlib.GroupTheory.GroupAction.SubMulAction

namespace CFSG
end CFSG
open CFSG

/-!
# Klein-four normalizers when the odd-core quotient is a two-group

If `G/O₂'(G)` is a two-group, its conjugation action on the image of a
Klein four subgroup has two-power order.  Acting on the three nonidentity
elements therefore fixes one of them, so every normalizer element has square
centralizing the subgroup.  Thus `N_G(Z)` cannot strictly contain `C'_G(Z)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- If the quotient by the odd core is a two-group, no Klein four subgroup
has strict `N_G(Z) ⊃ C'_G(Z)`. -/
public theorem quotientTwoGroup_not_normalizerContainsCPrime
    {G : Type u} [Group G] [Finite G]
    (hQ : IsPGroup 2 (G ⧸ pPrimeCore 2 G))
    (Z : Subgroup G) (hZ : IsKleinFour Z) :
    ¬ NormalizerContainsCPrime Z := by
  classical
  let : IsKleinFour Z := hZ
  let q : G →* G ⧸ pPrimeCore 2 G := QuotientGroup.mk' (pPrimeCore 2 G)
  have hZp : IsPGroup 2 Z := by
    apply IsPGroup.of_card (n := 2)
    simp [IsKleinFour.card_four]
  have hqZ : Function.Injective (q.comp Z.subtype) :=
    quotient_pPrimeCore_subgroupMap_injective Z hZp
  let Zbar : Subgroup (G ⧸ pPrimeCore 2 G) := Z.map q
  let qZ : Z →* Zbar :=
    (q.comp Z.subtype).codRestrict Zbar (fun z =>
      Subgroup.mem_map.mpr ⟨z, z.property, rfl⟩)
  have hqZsurj : Function.Surjective qZ := by
    intro y
    rcases Subgroup.mem_map.mp y.property with ⟨z, hz, hzy⟩
    exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
  have hqZinj : Function.Injective qZ := by
    intro a b hab
    exact hqZ (congrArg Subtype.val hab)
  let eZ : Z ≃* Zbar := MulEquiv.ofBijective qZ ⟨hqZinj, hqZsurj⟩
  let : IsKleinFour Zbar := {
    card_four := (Nat.card_congr eZ.toEquiv).symm.trans hZ.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eZ.symm).trans hZ.exponent_two
  }
  rintro ⟨_hsub, hnotsub⟩
  apply hnotsub
  intro n hn
  refine ⟨hn, ?_⟩
  let xn : Subgroup.normalizer (Z : Set G) := ⟨n, hn⟩
  let φ : MulAut Z := Z.normalizerMonoidHom xn
  have hqn : q n ∈ Subgroup.normalizer (Zbar : Set (G ⧸ pPrimeCore 2 G)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hnmap :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := Z) (g := n)).mp hn
    have h := congrArg (Subgroup.map q) hnmap
    have hcomp : q.comp (MulAut.conj n).toMonoidHom =
        (MulAut.conj (q n)).toMonoidHom.comp q := by
      ext x
      simp [q]
    rw [Subgroup.map_map] at h
    change Subgroup.map (q.comp (MulAut.conj n).toMonoidHom) Z =
      Subgroup.map q Z at h
    rw [hcomp, ← Subgroup.map_map] at h
    simpa [Zbar] using h
  let C : Subgroup (G ⧸ pPrimeCore 2 G) := Subgroup.zpowers (q n)
  have hCnorm : C ≤ Subgroup.normalizer (Zbar : Set (G ⧸ pPrimeCore 2 G)) :=
    Subgroup.zpowers_le.mpr hqn
  let ι : C →* Subgroup.normalizer (Zbar : Set (G ⧸ pPrimeCore 2 G)) :=
    C.subtype.codRestrict _ (fun c => hCnorm c.property)
  let ρ : C →* MulAut Zbar := Zbar.normalizerMonoidHom.comp ι
  let : MulDistribMulAction C Zbar := MulDistribMulAction.compHom Zbar ρ
  let A : SubMulAction C Zbar := {
    carrier := {z | z ≠ 1}
    smul_mem' := by
      intro c z hz
      change ρ c z ≠ 1
      intro hcz
      apply hz
      apply (ρ c).injective
      simpa using hcz
  }
  have hAcard : Nat.card A = 3 := by
    let : Fintype Zbar := Fintype.ofFinite Zbar
    let : Fintype A := Fintype.ofFinite A
    let eA : A ≃ {z : Zbar // z ≠ 1} := {
      toFun := fun a => ⟨a, a.property⟩
      invFun := fun a => ⟨a, a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }
    rw [Nat.card_congr eA, Nat.card_eq_fintype_card]
    set_option linter.unnecessarySimpa false in
      simpa using (Set.card_ne_eq (1 : Zbar))
  have hCp : IsPGroup 2 C := hQ.to_subgroup C
  have h2ndvdA : ¬ 2 ∣ Nat.card A := by
    rw [hAcard]
    norm_num
  rcases hCp.nonempty_fixed_point_of_prime_not_dvd_card A h2ndvdA with
    ⟨a, ha⟩
  let c0 : C := ⟨q n, Subgroup.mem_zpowers (q n)⟩
  have hfixA : c0 • a = a := MulAction.mem_fixedPoints.mp ha c0
  have hfixBar := congrArg Subtype.val hfixA
  change ρ c0 (a : Zbar) = (a : Zbar) at hfixBar
  let t : Z := eZ.symm (a : Zbar)
  have ht : t ≠ 1 := by
    intro ht1
    apply a.property
    have hea : eZ t = (a : Zbar) := eZ.apply_symm_apply (a : Zbar)
    rw [ht1] at hea
    simpa using hea.symm
  have hφfix : φ t = t := by
    apply hqZ
    change q ((φ t : Z) : G) = q (t : G)
    have hea : eZ t = (a : Zbar) := eZ.apply_symm_apply (a : Zbar)
    have hfixBar' : ρ c0 (eZ t) = eZ t := by
      simpa [hea] using hfixBar
    exact congrArg Subtype.val hfixBar'
  have hφ2 : φ ^ 2 = 1 :=
    mulAut_sq_eq_one_of_fixed_ne_one φ ht hφfix
  have hmap : Z.normalizerMonoidHom (xn ^ 2) = 1 := by
    rw [map_pow]
    exact hφ2
  have hker : xn ^ 2 ∈ Z.normalizerMonoidHom.ker := hmap
  rw [Subgroup.normalizerMonoidHom_ker] at hker
  exact hker

end CFSG.GorensteinWalter
