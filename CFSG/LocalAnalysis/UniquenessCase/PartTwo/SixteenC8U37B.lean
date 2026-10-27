module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8U37A
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (IsSL2Cover)

theorem u37_exists_outer_of_centralizer_structure
    (h : ∀ (X : Type) (_ : Group X) (_ : Finite X), LieModel X .PSU 3 7 1 →
      ∀ z : X, orderOf z = 2 →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 49 ∧
          Nonempty (↥(centralizer ({z} : Set X)) ≃* ↥(CFSG.Quasithin.StatedGU 2 7 F)))
    (A : Type) [Group A] [Finite A] (X : Subgroup A) (hX : LieModel ↥X .PSU 3 7 1)
    (E : Subgroup A) (hE : E ≤ X) (hEsl : IsSL2Cover ↥E 7 1)
    (D₃ : Subgroup A) (hD₃E : D₃ ≤ E) (hD₃ : Nat.card D₃ = 3) :
    ∃ g ∈ X, g ∈ normalizer (E : Set A) ∧ g ∈ normalizer (D₃ : Set A) ∧
      ¬ ∃ e ∈ E, ∀ x ∈ E, g * x * g⁻¹ = e * x * e⁻¹ := by
  have hcenter2 : Nat.card (center ↥E) = 2 := hEsl.2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (G := center ↥E) (by rw [hcenter2])
  let zX : ↥X := ⟨((z : ↥E) : A), hE (z : ↥E).2⟩
  have hzX : orderOf zX = 2 := by
    rw [← Subgroup.orderOf_coe zX]
    change orderOf (((z : ↥E) : A)) = 2
    rw [Subgroup.orderOf_coe (z : ↥E), Subgroup.orderOf_coe z, hz]
  obtain ⟨F, hFfield, hFfin, hFcard, ⟨θ⟩⟩ :=
    h ↥X (inferInstance : Group ↥X) (inferInstance : Finite ↥X) hX zX hzX
  let ι : ↥E →* ↥(centralizer ({zX} : Set ↥X)) :=
    { toFun := fun x => ⟨⟨(x : A), hE x.2⟩, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.coe_injective
          (congrArg (Subtype.val : ↥E → A) (Subgroup.mem_center_iff.mp z.2 x))⟩
      map_one' := by ext <;> rfl
      map_mul' := by intro a b; ext <;> rfl }
  have hιinj : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    simpa [ι] using congrArg
      (fun t : ↥(centralizer ({zX} : Set ↥X)) => ((t : ↥X) : A)) hab
  let E₀ : Subgroup ↥(CFSG.Quasithin.StatedGU 2 7 F) := (θ.toMonoidHom.comp ι).range
  have hcompinj : Function.Injective (θ.toMonoidHom.comp ι) := θ.injective.comp hιinj
  have hcardE : Nat.card ↥E = 336 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥E)
    have hclass : StatedClassicalModel (↥E ⧸ center ↥E) .PSL 2 7 1 :=
      LieModel.statedClassicalModel hEsl.2.2 (by decide)
    have h168 : Nat.card (↥E ⧸ center ↥E) = 168 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hclass
    rw [h, h168, hcenter2]
  have hcardE₀ : Nat.card ↥E₀ = 336 := by
    have h := Nat.card_range_of_injective hcompinj
    rw [← hcardE]
    convert h using 1
    rfl
  haveI hperfE : Group.IsPerfect ↥E := hEsl.1.1
  have hperfE₀ : Group.IsPerfect ↥E₀ := by
    have := Group.IsPerfect.range (θ.toMonoidHom.comp ι)
    simpa [E₀] using this
  obtain ⟨hE₀norm, h₀, houter₀⟩ := u37_outer_in_gu2 hFcard E₀ hperfE₀ hcardE₀
  let hc : ↥(centralizer ({zX} : Set ↥X)) := θ.symm h₀
  let hXelt : ↥X := hc.1
  let hA : A := hXelt.1
  have hEnorm : ∀ x ∈ E, hA * x * hA⁻¹ ∈ E := by
    intro x hx
    let xc : ↥(centralizer ({zX} : Set ↥X)) := ι ⟨x, hx⟩
    have hθin : θ (hc * xc * hc⁻¹) ∈ E₀ := by
      have hθeq : θ (hc * xc * hc⁻¹) = h₀ * θ xc * h₀⁻¹ := by
        rw [map_mul, map_mul, map_inv, show θ hc = h₀ from θ.apply_symm_apply h₀]
      rw [hθeq]
      exact hE₀norm.conj_mem (θ xc) (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩) h₀
    obtain ⟨y, hy⟩ := hθin
    have hy' : ι y = hc * xc * hc⁻¹ := θ.injective hy
    have hcoeeq : ((hc * xc * hc⁻¹ : ↥(centralizer ({zX} : Set ↥X))) : ↥X) = (ι y : ↥X) :=
      congrArg Subtype.val hy'.symm
    have hcoe : hA * x * hA⁻¹ = (y : A) := by
      simpa [hA, hXelt, hc, xc, ι] using congrArg Subtype.val hcoeeq
    rw [hcoe]
    exact y.2
  have hEmap : E.map (MulAut.conj hA).toMonoidHom = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply] using hEnorm x hx
    · rw [Subgroup.card_map_of_injective (MulAut.conj hA).injective]
  have hnormE : hA ∈ normalizer (E : Set A) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEmap
  have hD₃map_le : D₃.map (MulAut.conj hA).toMonoidHom ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hEnorm x (hD₃E hx)
  have hcardD₃map : Nat.card (D₃.map (MulAut.conj hA).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj hA).injective, hD₃]
  obtain ⟨e, heE, heconj⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.exists_conj_subgroup_of_le (p := 3) (k := 1) (m := 112)
      E hcardE (by norm_num) hD₃map_le hD₃E (by rw [hcardD₃map]; norm_num) hD₃
  have hconjcomp : (MulAut.conj e).toMonoidHom.comp (MulAut.conj hA).toMonoidHom =
      (MulAut.conj (e * hA)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hD₃map : D₃.map (MulAut.conj (e * hA)).toMonoidHom = D₃ := by
    have h := heconj
    rw [Subgroup.map_map] at h
    rwa [hconjcomp] at h
  have hnormD₃ : e * hA ∈ normalizer (D₃ : Set A) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hD₃map
  have hmapE_e : E.map (MulAut.conj e).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := E) heE)
  have hnormE_g : e * hA ∈ normalizer (E : Set A) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change E.map (MulAut.conj (e * hA)).toMonoidHom = E
    rw [← hconjcomp, ← Subgroup.map_map, hEmap, hmapE_e]
  have houterE : ∀ e' ∈ E, ∃ x ∈ E, hA * x * hA⁻¹ ≠ e' * x * e'⁻¹ := by
    intro e' he'
    let e₀ : ↥(CFSG.Quasithin.StatedGU 2 7 F) := θ (ι ⟨e', he'⟩)
    have he₀ : e₀ ∈ E₀ := ⟨⟨e', he'⟩, rfl⟩
    obtain ⟨x₀, hx₀, hne⟩ := houter₀ e₀ he₀
    obtain ⟨x, hx⟩ := hx₀
    refine ⟨x, x.2, ?_⟩
    intro heq
    apply hne
    have h1 : hc * ι x * hc⁻¹ = ι ⟨e', he'⟩ * ι x * (ι ⟨e', he'⟩)⁻¹ := by
      apply Subtype.ext
      apply Subtype.ext
      simpa [hA, hXelt, hc, ι] using heq
    have h2 := congrArg θ h1
    have hx' : θ (ι x) = x₀ := hx
    have hL : θ (hc * ι x * hc⁻¹) = h₀ * x₀ * h₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, show θ hc = h₀ from θ.apply_symm_apply h₀, hx']
    have hR : θ (ι ⟨e', he'⟩ * ι x * (ι ⟨e', he'⟩)⁻¹) = e₀ * x₀ * e₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, hx']
    rw [hL, hR] at h2
    exact h2
  refine ⟨e * hA, X.mul_mem (hE heE) hXelt.2, hnormE_g, hnormD₃, ?_⟩
  rintro ⟨e', he', hall⟩
  obtain ⟨x, hxE, hne⟩ := houterE (e⁻¹ * e') (E.mul_mem (E.inv_mem heE) he')
  apply hne
  have hconj : e⁻¹ * e' * x * (e⁻¹ * e')⁻¹ = hA * x * hA⁻¹ := by
    calc e⁻¹ * e' * x * (e⁻¹ * e')⁻¹
        = e⁻¹ * (e' * x * e'⁻¹) * e := by group
      _ = e⁻¹ * ((e * hA) * x * (e * hA)⁻¹) * e := by rw [hall x hxE]
      _ = hA * x * hA⁻¹ := by group
  exact hconj.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
