module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearAlignedSecondChain
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transport of the aligned equation-(11) chains

The product-family regions are obtained by conjugating an aligned line in the
fixed plane `A` by an element of `E`.  This module records the elementary
transport step: the aligned first/second chains for a line `X₀ = P^g ≤ A`
give the corresponding chains for `X₀^a`, with `a ∈ E`, in the transported
plane `A^a` and region `X₀^a ⊔ E^(a g)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private lemma conjugate_conjugate_transport
    {G : Type u} [Group G] {H : Subgroup G} (a g : G) :
    conjugateSubgroup (conjugateSubgroup H g) a =
      conjugateSubgroup H (a * g) := by
  change (H.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj a).toMonoidHom =
    H.map (MulAut.conj (a * g)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private lemma conjugate_inf_transport
    {G : Type u} [Group G] (H K : Subgroup G) (g : G) :
    conjugateSubgroup (H ⊓ K) g =
      conjugateSubgroup H g ⊓ conjugateSubgroup K g := by
  change (H ⊓ K).map (MulAut.conj g).toMonoidHom =
    H.map (MulAut.conj g).toMonoidHom ⊓
      K.map (MulAut.conj g).toMonoidHom
  exact Subgroup.map_inf H K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective

private lemma conjugate_sup_transport
    {G : Type u} [Group G] (H K : Subgroup G) (g : G) :
    conjugateSubgroup (H ⊔ K) g =
      conjugateSubgroup H g ⊔ conjugateSubgroup K g := by
  change (H ⊔ K).map (MulAut.conj g).toMonoidHom =
    H.map (MulAut.conj g).toMonoidHom ⊔
      K.map (MulAut.conj g).toMonoidHom
  exact Subgroup.map_sup H K (MulAut.conj g).toMonoidHom

private lemma conjugate_normalizer_transport
    {G : Type u} [Group G] {H : Subgroup G} (g : G) :
    Subgroup.normalizer (conjugateSubgroup H g : Set G) =
      conjugateSubgroup (Subgroup.normalizer (H : Set G)) g := by
  change Subgroup.normalizer
      ((H.map (MulAut.conj g).toMonoidHom) : Set G) =
    (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom
  exact (Subgroup.map_normalizer_eq_of_bijective H
    (MulAut.conj g).bijective).symm

private lemma conjugate_centralizer_transport
    {G : Type u} [Group G] {H : Subgroup G} (g : G) :
    Subgroup.centralizer ((conjugateSubgroup H g : Subgroup G) : Set G) =
      conjugateSubgroup (Subgroup.centralizer (H : Set G)) g := by
  apply le_antisymm
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · apply Subgroup.mem_centralizer_iff.mpr
      intro h hh
      have hgh : g * h * g⁻¹ ∈ conjugateSubgroup H g := by
        exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
      have hcomm : (g * h * g⁻¹) * x = x * (g * h * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hx) _ hgh
      calc
        h * (g⁻¹ * x * g) = g⁻¹ * ((g * h * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * h * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * x * g) * h := by group
    · simp [MulAut.conj_apply, mul_assoc]
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨h, hh, heq⟩
    have hz' : g⁻¹ * z * g = h := by
      apply (MulAut.conj g).injective
      simpa [MulAut.conj_apply, mul_assoc] using heq.symm
    have hcomm : h * y = y * h :=
      (Subgroup.mem_centralizer_iff.mp hy) h hh
    change z * (g * y * g⁻¹) = (g * y * g⁻¹) * z
    have hz'' : z = g * h * g⁻¹ := by
      calc
        z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = g * h * g⁻¹ := by rw [hz']
    rw [hz'']
    calc
      (g * h * g⁻¹) * (g * y * g⁻¹) =
          g * (h * y) * g⁻¹ := by group
      _ = g * (y * h) * g⁻¹ := by rw [hcomm]
      _ = (g * y * g⁻¹) * (g * h * g⁻¹) := by group

private lemma conjugate_self_of_mem
    {G : Type u} [Group G] {H : Subgroup G} {a : G} (ha : a ∈ H) :
    conjugateSubgroup H a = H := by
  apply le_antisymm
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact H.mul_mem (H.mul_mem ha hy) (H.inv_mem ha)
  · intro x hx
    apply Subgroup.mem_map.mpr
    refine ⟨a⁻¹ * x * a, H.mul_mem (H.mul_mem (H.inv_mem ha) hx) ha, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private lemma conjugate_fix_of_centralizes
    {G : Type u} [Group G] {P E : Subgroup G}
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    {a : G} (ha : a ∈ E) : conjugateSubgroup P a = P := by
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hcomm : p * a = a * p :=
      (Subgroup.mem_centralizer_iff.mp (hEcentP ha)) p hp
    change a * p * a⁻¹ ∈ P
    have hpa : a * p * a⁻¹ = p := by rw [← hcomm]; simp
    rw [hpa]
    exact hp
  · intro hx
    apply Subgroup.mem_map.mpr
    refine ⟨x, hx, ?_⟩
    have hcomm : x * a = a * x :=
      (Subgroup.mem_centralizer_iff.mp (hEcentP ha)) x hx
    change a * x * a⁻¹ = x
    rw [← hcomm]
    simp

/-- Transport the aligned chains by an element of the component. -/
public theorem secondCase_linear_outer_region_transport
    {G : Type u} [Group G] [Finite G]
    {P E M A C X₀ : Subgroup G} (g a : G)
    (hEcentP : E ≤ Subgroup.centralizer (P : Set G))
    (haE : a ∈ E) (haM : a ∈ M)
    (hX₀ : X₀ = conjugateSubgroup P g)
    (hfirst : conjugateSubgroup M g ⊓ (P ⊔ E) =
        (P ⊔ E) ⊓ Subgroup.normalizer (X₀ : Set G))
    (hfirstN : (P ⊔ E) ⊓ Subgroup.normalizer (X₀ : Set G) =
        P ⊔ C)
    (hfirstC : P ⊔ C = (P ⊔ E) ⊓
        Subgroup.centralizer (A : Set G))
    (hsecond : M ⊓ (X₀ ⊔ conjugateSubgroup E g) =
        X₀ ⊔ conjugateSubgroup C g)
    (hsecondC : X₀ ⊔ conjugateSubgroup C g =
        (X₀ ⊔ conjugateSubgroup E g) ⊓
          Subgroup.centralizer (A : Set G)) :
    let X := conjugateSubgroup X₀ a
    let h := a * g
    let A' := conjugateSubgroup A a
    (X = conjugateSubgroup P h) ∧
      (conjugateSubgroup M h ⊓ (P ⊔ E) =
        (P ⊔ E) ⊓ Subgroup.normalizer (X : Set G)) ∧
      ((P ⊔ E) ⊓ Subgroup.normalizer (X : Set G) =
        P ⊔ conjugateSubgroup C a) ∧
      (P ⊔ conjugateSubgroup C a = (P ⊔ E) ⊓
        Subgroup.centralizer (conjugateSubgroup A a : Set G)) ∧
      (M ⊓ (X ⊔ conjugateSubgroup E h) =
        X ⊔ conjugateSubgroup C h) ∧
      (X ⊔ conjugateSubgroup C h =
        (X ⊔ conjugateSubgroup E h) ⊓
          Subgroup.centralizer (A' : Set G)) := by
  dsimp
  have hPE : conjugateSubgroup (P ⊔ E) a = P ⊔ E := by
    rw [conjugate_sup_transport, conjugate_fix_of_centralizes hEcentP haE,
      conjugate_self_of_mem haE]
  have hM : conjugateSubgroup M a = M := conjugate_self_of_mem haM
  have hX : conjugateSubgroup X₀ a = conjugateSubgroup P (a * g) := by
    rw [hX₀, conjugate_conjugate_transport]
  have hN : Subgroup.normalizer (conjugateSubgroup X₀ a : Set G) =
      conjugateSubgroup (Subgroup.normalizer (X₀ : Set G)) a :=
    conjugate_normalizer_transport a
  have hCA : Subgroup.centralizer
      (conjugateSubgroup A a : Set G) =
      conjugateSubgroup (Subgroup.centralizer (A : Set G)) a :=
    conjugate_centralizer_transport a
  have hP : conjugateSubgroup P a = P :=
    conjugate_fix_of_centralizes hEcentP haE
  have hfirsta := congrArg (fun H : Subgroup G => conjugateSubgroup H a) hfirst
  have hfirstNa := congrArg (fun H : Subgroup G => conjugateSubgroup H a) hfirstN
  have hfirstCa := congrArg (fun H : Subgroup G => conjugateSubgroup H a) hfirstC
  have hseconda := congrArg (fun H : Subgroup G => conjugateSubgroup H a) hsecond
  have hsecondCa := congrArg (fun H : Subgroup G => conjugateSubgroup H a) hsecondC
  refine ⟨hX, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]
    simpa [conjugate_inf_transport, conjugate_conjugate_transport,
      hPE, hM, hX] using hfirsta
  · rw [hN]
    simpa [conjugate_inf_transport, conjugate_conjugate_transport,
      hPE, hX, hP, conjugate_sup_transport] using hfirstNa
  · simpa [conjugate_sup_transport, conjugate_inf_transport,
      conjugate_conjugate_transport, hPE, hCA, hP] using hfirstCa
  · simpa [conjugate_inf_transport, conjugate_sup_transport,
      conjugate_conjugate_transport, hM, hX] using hseconda
  · simpa [conjugate_sup_transport, conjugate_inf_transport,
      conjugate_conjugate_transport, hCA, hX] using hsecondCa

end CFSG.GorensteinWalter
