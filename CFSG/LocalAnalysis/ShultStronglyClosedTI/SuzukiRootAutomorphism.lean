module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiRootAutomorphismSemilinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiRootAutomorphismUnipotent
public import CFSG.LocalAnalysis.ComponentInitial.TwistedProductRigidity

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism

open CFSG.Blueprint CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial

section Coordinates

variable (a : ℕ) (K : Type) [Field K] (P : Type*) [Group P]

@[expose] def rootCenter : Subgroup (suzukiU a K × P) :=
  ((suzukiZ0 a K).subgroupOf (suzukiU a K)).prod ⊥

@[expose] def rootCenterPoint (b : K) : rootCenter a K P :=
  ⟨(unipotentElt a K 0 b, 1), Subgroup.mem_prod.2
    ⟨Subgroup.mem_subgroupOf.2 (unipotentElt_zero_mem_suzukiZ0 b), Subgroup.one_mem _⟩⟩

variable {a K P}

theorem coe_rootCenterPoint (b : K) :
    (rootCenterPoint a K P b : suzukiU a K × P) = (unipotentElt a K 0 b, 1) :=
  rfl

theorem rootCenterPoint_injective :
    Function.Injective (rootCenterPoint a K P) := fun b b' h => by
  simpa [coe_rootCenterPoint] using
    congrArg (fun z : rootCenter a K P => unipotentSnd (z : suzukiU a K × P).1) h

variable [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
include hK

theorem rootCenterPoint_add (b b' : K) :
    rootCenterPoint a K P (b + b') = rootCenterPoint a K P b * rootCenterPoint a K P b' := by
  refine Subtype.ext (Prod.ext ?_ (mul_one 1).symm)
  change unipotentElt a K 0 (b + b') = unipotentElt a K 0 b * unipotentElt a K 0 b'
  simp [unipotentElt_mul hK]

theorem rootCenterPoint_surjective :
    Function.Surjective (rootCenterPoint a K P) := by
  rintro ⟨⟨x, p⟩, hz⟩
  obtain ⟨hx, hp⟩ := Subgroup.mem_prod.1 hz
  obtain ⟨b, hb⟩ := (mem_suzukiZ0_iff hK).1 (Subgroup.mem_subgroupOf.1 hx)
  exact ⟨b, Subtype.ext (Prod.ext (Subtype.ext hb) (Subgroup.mem_bot.1 hp).symm)⟩

theorem exists_rootCenter_equiv :
    ∃ e : Multiplicative K ≃* rootCenter a K P, ∀ b : K,
      e (.ofAdd b) = rootCenterPoint a K P b :=
  ⟨MulEquiv.ofBijective (⟨fun b => rootCenterPoint a K P (Multiplicative.toAdd b),
      fun _ _ => rootCenterPoint_add hK _ _⟩ : Multiplicative K →ₙ* rootCenter a K P)
    ⟨fun _ _ h => Multiplicative.toAdd.injective (rootCenterPoint_injective (K := K) h), fun z =>
      let ⟨b, hb⟩ := rootCenterPoint_surjective hK z; ⟨Multiplicative.ofAdd b, hb⟩⟩,
    fun _ => rfl⟩

end Coordinates

variable {a : ℕ} {K : Type} [Field K] [Finite K] {P : Type*} [Group P]

theorem exists_semilinear_of_mem_autStabilizer
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {γ : MulAut (suzukiU a K × P)} (hγ : γ ∈ autStabilizer (rootCenter a K P)) :
    ∃ (c : Kˣ) (σ : K ≃+* K), ∀ b : K,
      γ (rootCenterPoint a K P b) = rootCenterPoint a K P (c * σ b) := by
  have hchar : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  have hpt : ∀ b : K, ∃ b' : K,
      (rootCenterPoint a K P b' : suzukiU a K × P) = γ (rootCenterPoint a K P b) := fun b =>
    (rootCenterPoint_surjective hK ⟨_, apply_mem_of_mem_autStabilizer hγ
      (rootCenterPoint a K P b).2⟩).imp fun _ h => congrArg Subtype.val h
  choose g hg using hpt
  have hptinj : Function.Injective fun b : K => (rootCenterPoint a K P b : suzukiU a K × P) :=
    Subtype.val_injective.comp rootCenterPoint_injective
  have hptadd : ∀ b b' : K, (rootCenterPoint a K P (b + b') : suzukiU a K × P) =
      rootCenterPoint a K P b * rootCenterPoint a K P b' := fun b b' => by
    rw [rootCenterPoint_add hK, Subgroup.coe_mul]
  have hgadd : ∀ b b' : K, g (b + b') = g b + g b' := fun b b' => hptinj (by
    simp only [hptadd, hg, map_mul])
  set E : K → suzukiU a K × P := fun u => (unipotentElt a K u 0, 1) with hE
  set f : K → K := fun u => unipotentFst (γ (E u)).1 with hf
  have hπmul : ∀ z w : suzukiU a K × P, unipotentFst (z * w).1 = unipotentFst z.1 +
      unipotentFst w.1 := fun z w => unipotentFst_mul hK z.1 w.1
  have hEmul : ∀ u u' : K, E u * E u' =
      E (u + u') * rootCenterPoint a K P (u ^ 2 ^ (a + 1) * u') := fun u u' => by
    refine Prod.ext ?_ rfl
    simp [hE, coe_rootCenterPoint, unipotentElt_mul hK]
  have hfadd : ∀ u u' : K, f (u + u') = f u + f u' := fun u u' => by
    have h := congrArg (fun z => unipotentFst (γ z).1) (hEmul u u')
    simp only [map_mul, hπmul, ← hg] at h
    simp only [coe_rootCenterPoint, unipotentFst_unipotentElt, add_zero] at h
    exact h.symm
  have hsq : ∀ u : K, g (u ^ (2 ^ (a + 1) + 1)) = f u ^ (2 ^ (a + 1) + 1) := fun u => by
    have h1 : E u ^ 2 = rootCenterPoint a K P (u ^ (2 ^ (a + 1) + 1)) :=
      Prod.ext (unipotentElt_sq hK u 0) (one_pow 2)
    have h2 := congrArg (fun z => (γ z).1) h1
    simp only [map_pow, Prod.pow_fst, ← hg] at h2
    simp only [unipotent_sq hK, coe_rootCenterPoint, unipotentElt_inj, true_and] at h2
    exact h2.symm
  let fA : K →+ K := AddMonoidHom.mk' f hfadd
  let gA : K →+ K := AddMonoidHom.mk' g hgadd
  have hf0 : fA ≠ 0 := by
    intro h0
    have h1 : g 1 = 0 := by
      simpa [fA, show f 1 = 0 from DFunLike.congr_fun h0 1] using hsq 1
    have h2 : (rootCenterPoint a K P 1 : suzukiU a K × P) = rootCenterPoint a K P 0 := by
      apply γ.injective
      rw [← hg, ← hg, h1, show g 0 = 0 from map_zero gA]
    exact one_ne_zero (hptinj h2)
  have hrel : ∀ x : K, gA (x * x ^ 2 ^ (a + 1)) = fA x * fA x ^ 2 ^ (a + 1) := fun x => by
    change g (x * x ^ 2 ^ (a + 1)) = f x * f x ^ 2 ^ (a + 1)
    rw [← pow_succ', ← pow_succ']
    exact hsq x
  have h4s : ¬ 2 * a + 1 ∣ 4 * (a + 1) := by
    intro h
    rw [show 4 * (a + 1) = 2 * (2 * a + 1) + 2 by ring] at h
    have := Nat.le_of_dvd two_pos ((Nat.dvd_add_right (dvd_mul_left _ _)).1 h)
    omega
  obtain ⟨⟨l, i⟩, ⟨-, hgl⟩, -⟩ := (twisted_product_quadratic_similarity_rigidity (by omega) hK
    (by omega) h4s).1 fA gA hf0 hrel
  refine ⟨l * l ^ 2 ^ (a + 1), RingEquiv.ofBijective (iterateFrobenius K 2 i)
    (iterateFrobenius K 2 i).injective.bijective_of_finite, fun b => ?_⟩
  rw [← hg]
  congr 2
  have := hgl b
  simp only [gA, AddMonoidHom.mk'_apply] at this
  rw [this, RingEquiv.ofBijective_apply, iterateFrobenius_def, Units.val_mul,
    Units.val_pow_eq_pow_val]

theorem suzuki_direct_product_root_center_automorphism_two_part
    (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ γ ∈ autStabilizer (rootCenter a K P), ∃ (c : Kˣ) (σ : K ≃+* K), ∀ b : K,
      γ (rootCenterPoint a K P b) = rootCenterPoint a K P (c * σ b)) ∧
    (∀ ψ ∈ (autStabilizerRestrict (rootCenter a K P)).range, ∃ (c : Kˣ) (σ : K ≃+* K),
      ∀ b : K, ψ (rootCenterPoint a K P b) = rootCenterPoint a K P (c * σ b)) ∧
    Odd (Nat.card (autStabilizerRestrict (rootCenter a K P)).range) ∧
    Nat.card (autStabilizerRestrict (rootCenter a K P)).range ∣
      (2 ^ (2 * a + 1) - 1) * (2 * a + 1) := by
  have h1 : ∀ γ ∈ autStabilizer (rootCenter a K P), ∃ (c : Kˣ) (σ : K ≃+* K), ∀ b : K,
      γ (rootCenterPoint a K P b) = rootCenterPoint a K P (c * σ b) := fun γ hγ =>
    exists_semilinear_of_mem_autStabilizer ha hK hγ
  have h2 : ∀ ψ ∈ (autStabilizerRestrict (rootCenter a K P)).range, ∃ (c : Kˣ) (σ : K ≃+* K),
      ∀ b : K, ψ (rootCenterPoint a K P b) = rootCenterPoint a K P (c * σ b) := by
    rintro _ ⟨γ, rfl⟩
    obtain ⟨c, σ, h⟩ := h1 γ γ.2
    exact ⟨c, σ, fun b => Subtype.ext (h b)⟩
  obtain ⟨e, he⟩ := exists_rootCenter_equiv (P := P) hK
  have hdvd := card_dvd_of_forall_coordSemilinear e fun ψ hψ => by
    obtain ⟨c, σ, h⟩ := h2 ψ hψ
    exact ⟨c, σ, fun b => by rw [he, he, h]⟩
  obtain ⟨-, -, -, -, hAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality (F := K) Nat.prime_two (by omega) hK
  rw [Nat.card_units, hK, hAut] at hdvd
  have hodd : Odd ((2 ^ (2 * a + 1) - 1) * (2 * a + 1)) := by
    refine Nat.odd_mul.2 ⟨⟨2 ^ (2 * a) - 1, ?_⟩, odd_two_mul_add_one a⟩
    have : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  exact ⟨h1, h2, hodd.of_dvd_nat hdvd, hdvd⟩

end CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism
