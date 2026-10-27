module

public import CFSG.Quasithin.Background.F7TwoInvU3TwoBlock
public import CFSG.ClassicalInvolution.Phan.Parabolic.Generation
public import CFSG.ClassicalInvolution.Phan.Center
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismModel

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

@[expose] noncomputable def suToGram (h : UnitaryFieldData 2 f K) :
    Su K 2 f 3 →* gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  Subgroup.inclusion (le_of_eq
    ((SUid_eq_statedSU h.card_eq_sq 3).trans (unitarySU_eq_gramSU h 3)))

@[expose] noncomputable def suToPrime (h : UnitaryFieldData 2 f K) :
    Su K 2 f 3 →* primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
  (QuotientGroup.mk' _).comp (suToGram h)

theorem suToPrime_surjective (h : UnitaryFieldData 2 f K) :
    Function.Surjective (suToPrime h) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hg : (g : GL (Fin 3) K) ∈ SUid (unitaryInvolution K 2 f) 3 := by
    rw [(SUid_eq_statedSU h.card_eq_sq 3).trans (unitarySU_eq_gramSU h 3)]
    exact g.2
  exact ⟨⟨g, hg⟩, rfl⟩

theorem suToPrime_ker_le_center (h : UnitaryFieldData 2 f K) :
    (suToPrime h).ker ≤ Subgroup.center (Su K 2 f 3) := by
  intro x hx
  obtain ⟨c, -, -, hc⟩ := (QuotientGroup.eq_one_iff _).mp hx
  have hx' : (x : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := hc
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hx']
  exact (commute_scalar c _).eq

theorem primeFormFieldAut_suToPrime (h : UnitaryFieldData 2 f K) (x : Su K 2 f 3) :
    primeFormFieldAut h isPrimeFormGram_one (unitaryInvolution K 2 f) (suToPrime h x) =
      suToPrime h (fieldAutSU 2 f (unitaryInvolution K 2 f) 3 x) := by
  change primeFormFieldAut h isPrimeFormGram_one (unitaryInvolution K 2 f)
      ((suToGram h x : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
    ((suToGram h (fieldAutSU 2 f (unitaryInvolution K 2 f) 3 x) :
      gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
        primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
  rw [primeFormFieldAut_mk]
  congr 1

theorem range_suToPrime_embSUid_le (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {α : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))}
    (hα : ∀ x, α (suToPrime h x) = suToPrime h (fieldAutSU 2 f (unitaryInvolution K 2 f) 3 x))
    (c : Fin 3) :
    ((suToPrime h).comp (embSUid (unitaryInvolution K 2 f) c)).range ≤
      Subgroup.closure (invXiAut α) := by
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  refine range_le_closure_invXiAut _ (comp_embSUid_injective hK (suToPrime_ker_le_center h) c)
    (φ := MulAut.conj (suSwap f)) (fun A => ?_) (invAutGen_suTwo_conj_suSwap f hf hK)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hα, fieldAutSU_embSUid,
    fieldAutSU_two_eq_conj_suSwap]
  rfl

theorem invAutGen_of_suToPrime_intertwine (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {α : MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))}
    (hα : ∀ x, α (suToPrime h x) = suToPrime h (fieldAutSU 2 f (unitaryInvolution K 2 f) 3 x)) :
    InvAutGen (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) α := by
  have hq : 2 ^ f ≠ 2 := by
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hgen : B12 K 2 f ⊔ B23 K 2 f = ⊤ := B12_sup_B23_eq_top h.card_eq_sq hq
  have h1 : (B12 K 2 f).map (suToPrime h) ≤ Subgroup.closure (invXiAut α) := by
    rw [B12, ← MonoidHom.range_comp]
    exact range_suToPrime_embSUid_le h hf hα 2
  have h2 : (B23 K 2 f).map (suToPrime h) ≤ Subgroup.closure (invXiAut α) := by
    rw [B23, ← MonoidHom.range_comp]
    exact range_suToPrime_embSUid_le h hf hα 0
  rw [invAutGen_iff_closure_invXiAut]
  refine top_le_iff.mp ?_
  rw [← MonoidHom.range_eq_top.mpr (suToPrime_surjective h), MonoidHom.range_eq_map, ← hgen,
    Subgroup.map_sup]
  exact sup_le h1 h2

theorem invAutGen_primeFormFieldAut_bar (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    InvAutGen (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (primeFormFieldAut h isPrimeFormGram_one (fieldDataHermitianForm h).conj) := by
  have hφ : (fieldDataHermitianForm h).conj = unitaryInvolution K 2 f := RingEquiv.ext fun x => by
    rw [fieldDataHermitianForm_conj, h.bar_apply, unitaryInvolution_apply]
  rw [hφ]
  exact invAutGen_of_suToPrime_intertwine h hf (primeFormFieldAut_suToPrime h)

end CFSG.Quasithin.F7Two
