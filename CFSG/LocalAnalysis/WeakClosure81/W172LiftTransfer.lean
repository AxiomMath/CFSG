module

public import CFSG.Open.LocalVocabulary
import CFSG.GH74.GLS.Stage1.Thm6.Lift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem w172_exists_lift_elemAbelian {Q : Subgroup Γ} [Q.Normal] (hQ : IsPGroup 2 ↥Q) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {B : Subgroup (Γ ⧸ Q)} (hB : IsElemAbelian p B) :
    ∃ B₁ : Subgroup Γ, B₁.map (QuotientGroup.mk' Q) = B ∧ IsElemAbelian p B₁ ∧
      Nat.card B₁ = Nat.card B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hBp : IsPGroup p B := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hB.2 _ x.2)⟩
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  have hpQ : ¬ p ∣ Nat.card Q := by
    rw [ha]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  obtain ⟨A, -, hAmap, hAbot⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.exists_lift_pSubgroup Q hpQ B hBp
  have hAB : ∀ x ∈ A, QuotientGroup.mk' Q x ∈ B := fun x hx => hAmap ▸ mem_map_of_mem _ hx
  have hinj : ∀ x ∈ A, ∀ y ∈ A, QuotientGroup.mk' Q x = QuotientGroup.mk' Q y → x = y := by
    intro x hx y hy hxy
    have h1 : y⁻¹ * x ∈ Q := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxy
      have := Q.inv_mem hxy
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : y⁻¹ * x ∈ A ⊓ Q := ⟨A.mul_mem (A.inv_mem hy) hx, h1⟩
    rw [hAbot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  let φ : A →* B := ((QuotientGroup.mk' Q).comp A.subtype).codRestrict B fun x => hAB x x.2
  have hφinj : Function.Injective φ := fun x y hxy =>
    Subtype.ext (hinj x x.2 y y.2 (congrArg Subtype.val hxy))
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hAmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨A, hAmap, ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩,
    Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)⟩
  · refine hinj ((x : Γ) * (y : Γ)) (A.mul_mem x.2 y.2) ((y : Γ) * (x : Γ))
      (A.mul_mem y.2 x.2) ?_
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hB.1.is_comm.comm (⟨_, hAB x x.2⟩ : B) ⟨_, hAB y y.2⟩)
  · refine hinj _ (A.pow_mem hx p) 1 A.one_mem ?_
    rw [map_pow, map_one]
    exact hB.2 _ (hAB x hx)

end CFSG.LocalAnalysis.WeakClosure81

end
