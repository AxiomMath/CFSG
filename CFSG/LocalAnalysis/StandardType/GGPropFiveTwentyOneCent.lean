module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneTypeA
public import Mathlib.GroupTheory.Perm.ClosureSwap

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits SpecialLinear

variable {m : ℕ}

theorem typeARealizes_inv {w : (coxeterMatrix (isFiniteType_A m)).Group}
    {π : Equiv.Perm (Fin (m + 1))} (hπ : TypeARealizes m w π) : TypeARealizes m w⁻¹ π⁻¹ :=
  fun γ => by
    have := hπ (weylAction (isFiniteType_A m) w⁻¹ γ)
    rw [weylAction_apply_inv_apply] at this
    funext x
    have h2 := congrFun this (π x)
    simp only [Equiv.symm_apply_apply] at h2
    rw [← h2]
    rfl

theorem mem_closure_swap_of_fix {a b : Fin (m + 1)} {π : Equiv.Perm (Fin (m + 1))}
    (ha : π a = a) (hb : π b = b) :
    π ∈ Subgroup.closure {σ : Equiv.Perm (Fin (m + 1)) | ∃ c d, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧
      d ≠ a ∧ d ≠ b ∧ σ = Equiv.swap c d} := by
  have hS : ∀ σ ∈ {σ : Equiv.Perm (Fin (m + 1)) | ∃ c d, c ≠ d ∧ c ≠ a ∧ c ≠ b ∧
      d ≠ a ∧ d ≠ b ∧ σ = Equiv.swap c d}, σ.IsSwap := by
    rintro σ ⟨c, d, hcd, -, -, -, -, rfl⟩
    exact ⟨c, d, hcd, rfl⟩
  rw [mem_closure_isSwap hS]
  refine ⟨Set.toFinite _, fun x => ?_⟩
  by_cases hx : π x = x
  · rw [hx]
    exact MulAction.mem_orbit_self x
  · have hxa : x ≠ a := fun h => hx (h ▸ ha)
    have hxb : x ≠ b := fun h => hx (h ▸ hb)
    have hpa : π x ≠ a := fun h => hxa (π.injective (h.trans ha.symm))
    have hpb : π x ≠ b := fun h => hxb (π.injective (h.trans hb.symm))
    exact ⟨⟨Equiv.swap x (π x), Subgroup.subset_closure
      ⟨x, π x, Ne.symm hx, hxa, hxb, hpa, hpb, rfl⟩⟩, Equiv.swap_apply_left x (π x)⟩

variable {F : Type} [Field F] {X : Type*} [Group X]

theorem typeALevi_hcent_of_swaps (h2 : (2 : F) = 0) {k : ℕ}
    (φ : ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)) →* X)
    (ρ : (coxeterMatrix (isFiniteType_A m)).Group →* X)
    (hspecial : ∀ j ∈ typeALeviJ m k, ggExt φ (weylRep m F j) =
      ρ ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j))
    (hswap : ∀ (w : (coxeterMatrix (isFiniteType_A m)).Group) (c d : Fin (m + 1)),
      TypeARealizes m w (Equiv.swap c d) → c ≠ d → k ≤ d.val →
      ∀ α ∈ ggSupp (rootDatum m F) (typeALeviJ m k), weylAction (isFiniteType_A m) w α = α →
        ∀ z ∈ rootGroup m F α, ρ w * ggExt φ z * (ρ w)⁻¹ = ggExt φ z) :
    ∀ (w : (coxeterMatrix (isFiniteType_A m)).Group),
      ∀ α ∈ ggSupp (rootDatum m F) (typeALeviJ m k), weylAction (isFiniteType_A m) w α = α →
        ∀ z ∈ rootGroup m F α, ρ w * ggExt φ z * (ρ w)⁻¹ = ggExt φ z := by
  intro w α hα hfix
  obtain ⟨a, b, hab, -, -, hαab⟩ := typeALevi_root_of_mem m F hα
  let Z : Subgroup X := Subgroup.centralizer (ggExt φ '' (rootGroup m F α : Set _))
  have hZiff : ∀ g : X, g ∈ Z ↔ ∀ z ∈ rootGroup m F α, g * ggExt φ z * g⁻¹ = ggExt φ z := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h z hz
      rw [← h _ ⟨z, hz, rfl⟩]
      group
    · rintro h _ ⟨z, hz, rfl⟩
      have e := h z hz
      calc ggExt φ z * g = (g * ggExt φ z * g⁻¹) * g := by rw [e]
        _ = g * ggExt φ z := by group
  have hν := slWeylLift_spec m h2
  have hT : ∀ t ∈ (coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
      (typeALeviJ m k : Set (Fin m)),
      slWeylLift m h2 t ∈ ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)) := by
    rintro _ ⟨j, hj, rfl⟩
    exact sup_le (rootGroup_le_ggSub (single_mem_ggSupp hj))
      (rootGroup_le_ggSub (neg_single_mem_ggSupp hj)) (hν.simple_mem j)
  have hWk : ∀ v ∈ typeALeviW m k, slWeylLift m h2 v ∈
      ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)) :=
    fun v hv => ggWeylLift_mem_of_closure hT hv
  have hρk : ∀ v ∈ typeALeviW m k, ggExt φ (slWeylLift m h2 v) = ρ v := by
    intro v hv
    have hv' : v ∈ Subgroup.closure ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple ''
        (typeALeviJ m k : Set (Fin m))) := hv
    induction hv' using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨j, hj, rfl⟩ := ht
      rw [slWeylLift_simple]
      exact hspecial j hj
    | one => rw [map_one, map_one, ggExt_one]
    | mul x y hx hy ihx ihy =>
      rw [map_mul, map_mul, ggExt_mul φ (hWk x hx) (hWk y hy), ihx hx, ihy hy]
    | inv x hx ihx => rw [map_inv, map_inv, ggExt_inv φ (hWk x hx), ihx hx]
  obtain ⟨π, hπ⟩ := exists_typeARealizes m w
  have hπfix : ∀ x, (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) (π.symm x) =
      (Pi.single a 1 - Pi.single b 1 : Fin (m + 1) → ℤ) x := by
    intro x
    have e := congrFun (hπ α) x
    rw [hfix, hαab] at e
    exact e.symm
  have hπa : π a = a := by
    by_contra h
    have e := hπfix (π a)
    rw [Equiv.symm_apply_apply] at e
    simp only [Pi.sub_apply, Pi.single_apply, h, hab] at e
    split_ifs at e <;> omega
  have hπb : π b = b := by
    by_contra h
    have e := hπfix (π b)
    rw [Equiv.symm_apply_apply] at e
    simp only [Pi.sub_apply, Pi.single_apply, h, Ne.symm hab] at e
    split_ifs at e <;> omega
  have key : ∀ σ ∈ Subgroup.closure {σ : Equiv.Perm (Fin (m + 1)) | ∃ c d, c ≠ d ∧ c ≠ a ∧
      c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ σ = Equiv.swap c d},
      ∀ v, TypeARealizes m v σ → ρ v ∈ Z := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem σ hσ =>
      obtain ⟨c, d, hcd, hca, hcb, hda, hdb, rfl⟩ := hσ
      intro v hv
      have hσa : Equiv.swap c d a = a := Equiv.swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hda)
      have hσb : Equiv.swap c d b = b := Equiv.swap_apply_of_ne_of_ne (Ne.symm hcb) (Ne.symm hdb)
      have hvα : weylAction (isFiniteType_A m) v α = α := by
        apply toStd_injective m
        rw [hv α, hαab]
        funext x
        have e1 : (Equiv.swap c d).symm x = a ↔ x = a := by rw [Equiv.symm_apply_eq, hσa]
        have e2 : (Equiv.swap c d).symm x = b ↔ x = b := by rw [Equiv.symm_apply_eq, hσb]
        simp only [Pi.sub_apply, Pi.single_apply, e1, e2]
      by_cases hd : k ≤ d.val
      · exact (hZiff _).mpr (hswap v c d hv hcd hd α hα hvα)
      by_cases hc : k ≤ c.val
      · exact (hZiff _).mpr (hswap v d c (by rwa [Equiv.swap_comm]) (Ne.symm hcd) hc α hα hvα)
      obtain ⟨v', hv'W, hv'⟩ := exists_typeALeviW_swap m (k := k) c d (by omega) (by omega)
      obtain rfl : v = v' := typeARealizes_inj m hv hv'
      refine (hZiff _).mpr fun z hz => ?_
      have hmem1 := hWk v hv'W
      have hmem2 : z ∈ ggSub (rootDatum m F) (ggSupp (rootDatum m F) (typeALeviJ m k)) :=
        rootGroup_le_ggSub hα hz
      rw [← hρk v hv'W, ← ggExt_inv φ hmem1, ← ggExt_mul φ hmem1 hmem2,
        ← ggExt_mul φ (mul_mem hmem1 hmem2) (inv_mem hmem1),
        slWeylLift_fix m h2 v hα.1 hvα hz]
    | one =>
      intro v hv
      obtain rfl : v = 1 := typeARealizes_inj m hv (typeARealizes_one m)
      rw [map_one]
      exact one_mem Z
    | mul σ₁ σ₂ _ _ ih₁ ih₂ =>
      intro v hv
      obtain ⟨v₁, hv₁⟩ := exists_weyl_toStd m σ₁
      obtain ⟨v₂, hv₂⟩ := exists_weyl_toStd m σ₂
      obtain rfl : v = v₁ * v₂ := typeARealizes_inj m hv (typeARealizes_mul m hv₁ hv₂)
      rw [map_mul]
      exact mul_mem (ih₁ v₁ hv₁) (ih₂ v₂ hv₂)
    | inv σ _ ih =>
      intro v hv
      have h1 : TypeARealizes m v⁻¹ σ := by
        have := typeARealizes_inv hv
        rwa [inv_inv] at this
      have h3 := inv_mem (ih v⁻¹ h1)
      rwa [map_inv, inv_inv] at h3
  exact (hZiff (ρ w)).mp (key π (mem_closure_swap_of_fix hπa hπb) w hπ)

theorem ggSecFiveTypeA_of_swaps {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G}
    {L D J : Subgroup G} {m k f : ℕ} (hf : 1 ≤ f)
    (φ : ggSub (rootDatum m (GaloisField 2 f)) (ggSupp (rootDatum m (GaloisField 2 f))
      (typeALeviJ m k)) →* G) (ρ : (coxeterMatrix (isFiniteType_A m)).Group →* G)
    (hρ : Function.Injective ρ)
    (hspecial : ∀ j ∈ typeALeviJ m k, ggExt φ (weylRep m (GaloisField 2 f) j) =
      ρ ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple j))
    (hswap : ∀ (w : (coxeterMatrix (isFiniteType_A m)).Group) (c d : Fin (m + 1)),
      TypeARealizes m w (Equiv.swap c d) → c ≠ d → k ≤ d.val →
      ∀ α ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
        weylAction (isFiniteType_A m) w α = α → ∀ z ∈ rootGroup m (GaloisField 2 f) α,
          ρ w * ggExt φ z * (ρ w)⁻¹ = ggExt φ z)
    (hnt : ∃ γ ∈ ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k),
      ∃ z ∈ rootGroup m (GaloisField 2 f) γ, ggExt φ z ≠ 1)
    (hφG : φ.range ≤ ggG0 p B x L D J) (hρG : ρ.range ≤ ggG0 p B x L D J)
    (hL : L ≤ ggClosure (rootDatum m (GaloisField 2 f))
      (fun _ : Unit => ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)) (fun _ => φ)
        ρ.range)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ ggClosure (rootDatum m (GaloisField 2 f))
        (fun _ : Unit => ggSupp (rootDatum m (GaloisField 2 f)) (typeALeviJ m k)) (fun _ => φ)
          ρ.range) :
    GGSecFiveTypeA p B x L D J m k f :=
  ⟨φ, ρ, hρ, hspecial, typeALevi_hcent_of_swaps
    (two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf) φ ρ hspecial hswap, hnt, hφG,
    hρG, hL, hK⟩

end CFSG.StandardType
