module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.Monster.B.TwoA

section DirProd

variable {K G₁ G₂ : Type*} [Group K] [Group G₁] [Group G₂] {C : Subgroup K} [C.Normal]

theorem map_conjNormal_ker (B : C →* G₂) (hR : B.ker.Characteristic) (k : K) :
    B.ker.map (MulAut.conjNormal k : C ≃* C).toMonoidHom = B.ker :=
  (Subgroup.characteristic_iff_map_eq.1 hR) _

@[expose] noncomputable def sectionAut (B : C →* G₂) (hB : Function.Surjective B)
    (hR : B.ker.Characteristic) (k : K) : MulAut G₂ :=
  (QuotientGroup.quotientKerEquivOfSurjective B hB).symm.trans
    ((QuotientGroup.congr B.ker B.ker (MulAut.conjNormal k) (map_conjNormal_ker B hR k)).trans
      (QuotientGroup.quotientKerEquivOfSurjective B hB))

theorem sectionAut_apply (B : C →* G₂) (hB : Function.Surjective B)
    (hR : B.ker.Characteristic) (k : K) (c : C) :
    sectionAut B hB hR k (B c) = B (MulAut.conjNormal k c) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective B hB).symm (B c) =
      (QuotientGroup.mk c : C ⧸ B.ker) :=
    (MulEquiv.symm_apply_eq _).2 rfl
  change (QuotientGroup.quotientKerEquivOfSurjective B hB)
    ((QuotientGroup.congr B.ker B.ker (MulAut.conjNormal k) (map_conjNormal_ker B hR k))
      ((QuotientGroup.quotientKerEquivOfSurjective B hB).symm (B c))) = _
  rw [h1]
  rfl

@[expose] noncomputable def sectionAutHom (B : C →* G₂) (hB : Function.Surjective B)
    (hR : B.ker.Characteristic) : K →* MulAut G₂ where
  toFun := sectionAut B hB hR
  map_one' := MulEquiv.ext fun x => by
    obtain ⟨c, rfl⟩ := hB x
    rw [sectionAut_apply, map_one, MulAut.one_apply, MulAut.one_apply]
  map_mul' k k' := MulEquiv.ext fun x => by
    obtain ⟨c, rfl⟩ := hB x
    rw [MulAut.mul_apply, sectionAut_apply, sectionAut_apply, sectionAut_apply, map_mul,
      MulAut.mul_apply]

theorem sectionAutHom_coe (B : C →* G₂) (hB : Function.Surjective B)
    (hR : B.ker.Characteristic) (c : C) :
    sectionAutHom B hB hR (c : K) = MulAut.conj (B c) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨c', rfl⟩ := hB x
  change sectionAut B hB hR (c : K) (B c') = _
  rw [sectionAut_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1

@[expose] noncomputable def sigmaSec (B : C →* G₂) (hB : Function.Surjective B)
    (hR : B.ker.Characteristic)
    (hconj : Function.Bijective (MulAut.conj : G₂ →* MulAut G₂)) : K →* G₂ :=
  (MulEquiv.ofBijective _ hconj).symm.toMonoidHom.comp (sectionAutHom B hB hR)

theorem sigmaSec_coe (B : C →* G₂) (hB : Function.Surjective B) (hR : B.ker.Characteristic)
    (hconj : Function.Bijective (MulAut.conj : G₂ →* MulAut G₂)) (c : C) :
    sigmaSec B hB hR hconj (c : K) = B c := by
  change (MulEquiv.ofBijective _ hconj).symm (sectionAutHom B hB hR (c : K)) = B c
  rw [sectionAutHom_coe]
  exact (MulEquiv.ofBijective _ hconj).symm_apply_apply (B c)

@[expose] def secKer (B : C →* G₂) : Subgroup K := B.ker.map C.subtype

theorem secKer_normal (B : C →* G₂) (hR : B.ker.Characteristic) : (secKer B).Normal where
  conj_mem n hn k := by
    obtain ⟨c, hc, rfl⟩ := hn
    have h := map_conjNormal_ker B hR k
    have hc' : (MulAut.conjNormal k : C ≃* C) c ∈ B.ker := by
      rw [← h]
      exact ⟨c, hc, rfl⟩
    refine ⟨_, hc', ?_⟩
    rw [Subgroup.coe_subtype, MulAut.conjNormal_apply]

theorem exists_quotProdEquiv [Finite K] (A : K →* G₁) (hA : Function.Surjective A)
    (hAC : A.ker = C) (B : C →* G₂) (hB : Function.Surjective B) (hR : B.ker.Characteristic)
    (hconj : Function.Bijective (MulAut.conj : G₂ →* MulAut G₂)) [(secKer B).Normal] :
    ∃ e : K ⧸ secKer B ≃* G₁ × G₂, ∀ k : K,
      e (k : K ⧸ secKer B) = (A k, sigmaSec B hB hR hconj k) := by
  have : Finite G₁ := Finite.of_surjective A hA
  have : Finite G₂ := Finite.of_surjective B hB
  set σ := sigmaSec B hB hR hconj
  have hle : secKer B ≤ (A.prod σ).ker := by
    rintro _ ⟨c, hc, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one]
    refine ⟨?_, ?_⟩
    · have : (c : K) ∈ A.ker := by rw [hAC]; exact c.2
      exact this
    · rw [Subgroup.coe_subtype, sigmaSec_coe]
      exact hc
  let f : K ⧸ secKer B →* G₁ × G₂ := QuotientGroup.lift _ (A.prod σ) hle
  have hf : ∀ k : K, f (k : K ⧸ secKer B) = (A k, σ k) := fun _ => rfl
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hf, Prod.mk_eq_one] at hq
    have hkC : k ∈ C := by rw [← hAC]; exact hq.1
    have hB1 : B ⟨k, hkC⟩ = 1 := by
      rw [← sigmaSec_coe B hB hR hconj ⟨k, hkC⟩]
      exact hq.2
    exact (QuotientGroup.eq_one_iff k).2 ⟨⟨k, hkC⟩, hB1, rfl⟩
  have hcard : Nat.card (G₁ × G₂) ≤ Nat.card (K ⧸ secKer B) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (secKer B)
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup A.ker
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup B.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective A hA).toEquiv] at h2
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective B hB).toEquiv] at h3
    have h4 : Nat.card (secKer B) = Nat.card B.ker :=
      (Nat.card_congr (B.ker.equivMapOfInjective C.subtype Subtype.coe_injective).toEquiv).symm
    have h5 : Nat.card A.ker = Nat.card C := by rw [hAC]
    rw [Nat.card_prod]
    have hR0 : 0 < Nat.card B.ker := Nat.card_pos
    have hK : Nat.card (K ⧸ secKer B) * Nat.card B.ker = Nat.card G₁ * Nat.card G₂ *
        Nat.card B.ker := by
      rw [← h4, ← h1, h2, h5, h3, mul_assoc, h4]
    exact (Nat.eq_of_mul_eq_mul_right hR0 hK).ge
  exact ⟨MulEquiv.ofBijective f (hinj.bijective_of_nat_card_le hcard), hf⟩

end DirProd

end CFSG.Monster.B.TwoA
