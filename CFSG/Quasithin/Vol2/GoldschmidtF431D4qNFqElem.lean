module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqIso
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqSpec

public section

namespace CFSG.Quasithin.H13.F431.D4q.NFq

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
def imageV (E : Subgroup (ModGL TwistTag.D4.tag K)) : AddSubgroup (Vc σ) where
  carrier := {x | ∃ f : d4k K σ, vmk σ x f ∈ E}
  zero_mem' := ⟨0, by rw [vmk_zero]; exact E.one_mem⟩
  add_mem' := by
    rintro x y ⟨f, hf⟩ ⟨f', hf'⟩
    exact ⟨beta σ hσ x y + f + f', by rw [← vmk_mul σ hσ]; exact E.mul_mem hf hf'⟩
  neg_mem' := by
    rintro x ⟨f, hf⟩
    exact ⟨f, by rw [neg_eq_of_add_eq_zero_right (vc_add_self σ x)]; exact hf⟩

include hσ in
theorem isoForm_eq_zero_of_commute {x y : Vc σ} {f f' : d4k K σ}
    (h : vmk σ x f * vmk σ y f' = vmk σ y f' * vmk σ x f) : isoForm σ x y = 0 := by
  rw [vmk_mul σ hσ, vmk_mul σ hσ] at h
  obtain ⟨-, h2⟩ := vmk_inj σ h
  have h3 : beta σ hσ x y = beta σ hσ y x := by
    have h4 : beta σ hσ x y + (f + f') = beta σ hσ y x + (f + f') := by
      rw [← add_assoc, h2, add_assoc, add_comm f' f]
    exact add_right_cancel h4
  have h5 : isoForm σ x y =
      ((beta σ hσ x y : d4k K σ) : K) + ((beta σ hσ y x : d4k K σ) : K) := by
    simp only [isoForm, beta]
    ring
  rw [h5, h3]
  exact CharTwo.add_self_eq_zero _

include hσ in
theorem card_le_of_abelian {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 3)
    (hk : Nat.card (d4k K σ) = 2 ^ f) {E : Subgroup (ModGL TwistTag.D4.tag K)}
    (hEQ : E ≤ d4Vr K σ) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ (2 ^ f) ^ 5 := by
  have hiso : ∀ x ∈ imageV σ hσ E, ∀ y ∈ imageV σ hσ E, isoForm σ x y = 0 := by
    rintro x ⟨f₁, hx⟩ y ⟨f₂, hy⟩
    exact isoForm_eq_zero_of_commute σ hσ (hEab _ hx _ hy)
  have h1 := card_le_of_isotropic σ hσ hK hk (imageV σ hσ E) hiso
  let S := {p : Vc σ × d4k K σ // vmk σ p.1 p.2 ∈ E}
  have hinj : Function.Injective (fun p : S => (⟨vmk σ p.1.1 p.1.2, p.2⟩ : E)) := by
    intro p p' h
    have h2 := congrArg Subtype.val h
    simp only at h2
    exact Subtype.ext (Prod.ext (vmk_inj σ h2).1 (vmk_inj σ h2).2)
  have hsurj : Function.Surjective (fun p : S => (⟨vmk σ p.1.1 p.1.2, p.2⟩ : E)) := by
    rintro ⟨g, hg⟩
    obtain ⟨x, f₁, rfl⟩ := exists_vmk σ hσ (hEQ hg)
    exact ⟨⟨(x, f₁), hg⟩, rfl⟩
  have h3 : Nat.card S = Nat.card E := Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  let φ : S → imageV σ hσ E × d4k K σ := fun p => (⟨p.1.1, p.1.2, p.2⟩, p.1.2)
  have hφ : Function.Injective φ := by
    intro p p' h
    have h1' := congrArg (fun z => (z.1 : Vc σ)) h
    have h2' := congrArg Prod.snd h
    exact Subtype.ext (Prod.ext h1' h2')
  have h4 : Nat.card S ≤ Nat.card (imageV σ hσ E × d4k K σ) := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, hk] at h4
  calc Nat.card E = Nat.card S := h3.symm
    _ ≤ Nat.card (imageV σ hσ E) * 2 ^ f := h4
    _ ≤ (2 ^ f) ^ 4 * 2 ^ f := Nat.mul_le_mul_right _ h1
    _ = (2 ^ f) ^ 5 := by ring

end CFSG.Quasithin.H13.F431.D4q.NFq
