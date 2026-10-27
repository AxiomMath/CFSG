module

public import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Sporadic.HNSchreier.IntrinsicCheck
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2104
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate16041
public import Certificates.Certificate2107
public import CFSG.Permutation.AlternatingAutomorphism

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.Blueprint.NativeSporadic CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open Equiv

theorem intrinsic_parts : IntrinsicData.wCycles = #[2, 4] ∧
    ∀ c < 2, (IntrinsicData.wRoot[c]!).all (fun l => l == 1 || l == 2) = true ∧
      plettersOK 17 IntrinsicData.wHWord[c]! = true ∧
      Data.baseList.all (fun b => seedWordInvIdx (pinvs hnsData.n #[a0Arr, a1Arr])[0]!
        (pinvs hnsData.n #[a0Arr, a1Arr])[1]! IntrinsicData.wRoot[c]!
        ((pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr) FAData.sWords[0]!)[
          seedWordIdx a0Arr a1Arr IntrinsicData.wRoot[c]! b]!) ==
        (pword hnsData.n hStrongArr (pinvs hnsData.n hStrongArr)
          IntrinsicData.wHWord[c]!)[b]!) = true ∧
      peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) IntrinsicData.wHWord[c]!)
        (natArr IntrinsicData.wNat[c]!) = true ∧
      pisInv 12 (natArr IntrinsicData.rho[c]!) (pinvCand 12 (natArr IntrinsicData.rho[c]!)) =
        true ∧
      peq 12 (pcomp 12 (pcomp 12 (natArr IntrinsicData.rho[c]!)
        (tripleArr IntrinsicData.wCycles[c]!)) (pinvCand 12 (natArr IntrinsicData.rho[c]!)))
        (natArr IntrinsicData.wNat[c]!) = true := by
  have h := intrinsic_cert
  unfold intrinsicChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← hRegs_eq, ← hStrongArr_eq, ← natStrongArr_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h8⟩, h9⟩ := h
  refine ⟨h8, fun c hc => ?_⟩
  have := allBelowN_spec h9 hc
  simp only [Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := this
  exact ⟨a1, a2, a3, a4, a5, a6⟩

theorem s1_conj
    {c : ℕ} (hc : c < 2) :
    (seedWordJ IntrinsicData.wRoot[c]!)⁻¹ * sJ 0 * seedWordJ IntrinsicData.wRoot[c]! =
      hWordJ IntrinsicData.wHWord[c]! := by
  obtain ⟨-, hw⟩ := intrinsic_parts
  obtain ⟨hroot, hlet, hbase, -⟩ := hw c hc
  have hroot' : ∀ l ∈ IntrinsicData.wRoot[c]!, l = 1 ∨ l = 2 := by
    intro l hl
    have := List.all_eq_true.1 hroot l hl
    simpa using this
  apply eq_of_base
  intro k
  apply Fin.ext
  have := List.all_eq_true.1 hbase _ (baseX_mem k)
  rw [beq_iff_eq, seedWordIdx_val _ hroot' (baseX k),
    prep_apply (sJ_rep (k := 0) (by norm_num)) (seedWordJ IntrinsicData.wRoot[c]! • baseX k),
    permJ_apply,
    seedWordInvIdx_val _ hroot' (sJ 0 • seedWordJ IntrinsicData.wRoot[c]! • baseX k),
    prep_apply (prep_hWord hlet) (baseX k), permJ_apply] at this
  rw [mul_smul, mul_smul]
  exact this

theorem hWord_conj_sJ
    {hw : List ℤ} {k : ℕ} {ρa νa : List ℕ} (hk1 : 1 ≤ k) (hk4 : k ≤ 4)
    (hlet : plettersOK 17 hw = true)
    (h1 : peq 12 (pword 12 natStrongArr (pinvs 12 natStrongArr) hw) (natArr νa) = true)
    (h2 : pisInv 12 (natArr ρa) (pinvCand 12 (natArr ρa)) = true)
    (h3 : peq 12 (pcomp 12 (pcomp 12 (natArr ρa) (tripleArr k)) (pinvCand 12 (natArr ρa)))
      (natArr νa) = true) :
    ∃ g ∈ HJ, g * sJ (k - 1) * g⁻¹ = hWordJ hw := by
  have hθ := (thetaJ_hWord hw).trans (natWord_witness hk1 hk4 hlet h1 h2 h3)
  obtain ⟨σ, hσ⟩ := exists_even_conj_tripleNat hk1 hk4 (permOfArr 12 (natArr ρa))
  have hs := thetaJ_sJ (k := k - 1) (by omega)
  rw [Nat.sub_add_cancel hk1] at hs
  have he : thetaJ (hWordH hw) = σ * thetaJ ⟨sJ (k - 1), sJ_mem _⟩ * σ⁻¹ := by
    apply Subtype.ext
    rw [hθ, ← hσ]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs]
  refine ⟨iotaA σ, iotaA_mem σ, ?_⟩
  have := congrArg iotaA he
  rw [map_mul, map_mul, map_inv, iotaA_theta, iotaA_theta] at this
  exact this.symm

theorem isConj_s1_witness
    {c : ℕ} (hc : c < 2) :
    IsConj (sJ 0) (sJ (IntrinsicData.wCycles[c]! - 1)) := by
  obtain ⟨hcyc, hw⟩ := intrinsic_parts
  obtain ⟨-, hlet, -, h1, h2, h3⟩ := hw c hc
  have hk : IntrinsicData.wCycles[c]! = 2 ∨ IntrinsicData.wCycles[c]! = 4 := by
    rw [hcyc]
    interval_cases c <;> decide
  obtain ⟨g, -, hg⟩ := hWord_conj_sJ (by omega) (by omega) hlet h1 h2 h3
  have e := s1_conj hc
  have hs : sJ (IntrinsicData.wCycles[c]! - 1) = g⁻¹ * hWordJ IntrinsicData.wHWord[c]! * g := by
    rw [← hg]; group
  refine isConj_iff.2 ⟨(seedWordJ IntrinsicData.wRoot[c]! * g)⁻¹, ?_⟩
  rw [hs, ← e]
  group

theorem isConj_s1_s2 :
    IsConj (sJ 0) (sJ 1) := by
  have h := isConj_s1_witness (c := 0) (by norm_num)
  rwa [show IntrinsicData.wCycles[0]! - 1 = 1 by decide] at h

theorem isConj_s1_s4 :
    IsConj (sJ 0) (sJ 3) := by
  have h := isConj_s1_witness (c := 1) (by norm_num)
  rwa [show IntrinsicData.wCycles[1]! - 1 = 3 by decide] at h

@[expose] def autHom (β : MulAut JH) : JH →* JH := MonoidHom.mk' β (map_mul β)

theorem autHom_apply (β : MulAut JH) (x : JH) : autHom β x = β x := rfl

theorem autHom_injective (β : MulAut JH) : Function.Injective (autHom β) := β.injective

theorem map_CJ_of_bijective (f : JH →* JH) (hf : Function.Bijective f) (x : JH) :
    (CJ x).map f = CJ (f x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := mem_CJ.1 hz
    refine mem_CJ.2 ?_
    rw [← map_mul, ← map_mul, hz']
  · intro hy
    obtain ⟨z, rfl⟩ := hf.2 y
    refine ⟨z, mem_CJ.2 (hf.1 ?_), rfl⟩
    rw [map_mul, map_mul]
    exact mem_CJ.1 hy

theorem map_CJ (β : MulAut JH) (x : JH) : (CJ x).map (autHom β) = CJ (β x) :=
  map_CJ_of_bijective _ β.bijective x

theorem card_CJ_aut (β : MulAut JH) (x : JH) : Nat.card (CJ (β x)) = Nat.card (CJ x) := by
  rw [← map_CJ, Subgroup.card_map_of_injective (autHom_injective β)]

theorem card_CJ_of_isConj {x y : JH} (h : IsConj x y) : Nat.card (CJ y) = Nat.card (CJ x) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  rw [← MulAut.conj_apply, card_CJ_aut]

theorem not_isConj_s1_s3 :
    ¬ IsConj (sJ 0) (sJ 2) := fun h => by
  have := card_CJ_of_isConj h
  rw [card_CJ_s1, card_CJ_s3] at this
  norm_num at this

theorem orderOf_of_isConj {x y : JH} (h : IsConj x y) : orderOf y = orderOf x := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact orderOf_conj_JH g x

theorem order_three_classes
    (x : JH) : orderOf x = 3 ↔ IsConj (sJ 0) x ∨ IsConj (sJ 2) x := by
  constructor
  · intro hx
    obtain ⟨k, hk, hc⟩ := order_three_isConj hx
    interval_cases k
    · exact Or.inl hc
    · exact Or.inl (isConj_s1_s2.trans hc)
    · exact Or.inr hc
    · exact Or.inl (isConj_s1_s4.trans hc)
  · rintro (h | h)
    · rw [orderOf_of_isConj h, orderOf_sJ (by norm_num)]
    · rw [orderOf_of_isConj h, orderOf_sJ (by norm_num)]

theorem isConj_s1_aut
    (α : MulAut JH) {x : JH} (hx : IsConj (sJ 0) x) : IsConj (sJ 0) (α x) := by
  have h3 : orderOf (α x) = 3 := by
    rw [MulEquiv.orderOf_eq, orderOf_of_isConj hx, orderOf_sJ (by norm_num)]
  rcases (order_three_classes _).1 h3 with h | h
  · exact h
  · exfalso
    have e1 := card_CJ_of_isConj h
    rw [card_CJ_aut, card_CJ_of_isConj hx, card_CJ_s1, card_CJ_s3] at e1
    norm_num at e1

theorem CJ_inv (x : JH) : CJ x⁻¹ = CJ x := by
  ext y
  rw [mem_CJ, mem_CJ]
  constructor
  · intro h
    calc x * y = x * (y * x⁻¹) * x := by group
      _ = x * (x⁻¹ * y) * x := by rw [h]
      _ = y * x := by group
  · intro h
    calc x⁻¹ * y = x⁻¹ * (y * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * y) * x⁻¹ := by rw [h]
      _ = y * x⁻¹ := by group

abbrev DJ (x : JH) : Subgroup JH := ⁅CJ x, CJ x⁆

theorem map_DJ_of_bijective (f : JH →* JH) (hf : Function.Bijective f) (x : JH) :
    (DJ x).map f = DJ (f x) := by
  rw [DJ, Subgroup.map_commutator, map_CJ_of_bijective f hf]

theorem map_DJ (β : MulAut JH) (x : JH) : (DJ x).map (autHom β) = DJ (β x) :=
  map_DJ_of_bijective _ β.bijective x

theorem DJ_inv (x : JH) : DJ x⁻¹ = DJ x := by rw [DJ, DJ, CJ_inv]

abbrev kappa :
    alternatingGroup (Fin 9) →* JH := iotaA.comp (alt3.subtype.comp alt9Hom)

theorem kappa_injective :
    Function.Injective kappa :=
  iotaA_injective.comp (Subtype.val_injective.comp alt9Hom_injective)

theorem mem_L1J_iff
    {y : JH} : y ∈ L1J ↔ ∃ τ, kappa τ = y := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨τ, hτ⟩ := alt9Hom_surjective ⟨σ, hσ⟩
    refine ⟨τ, ?_⟩
    show iotaA ((alt9Hom τ : alt3) : alternatingGroup (Fin 12)) = iotaA σ
    rw [hτ]
  · rintro ⟨τ, rfl⟩
    exact ⟨_, (alt9Hom τ).2, rfl⟩

@[expose] def restrA9
    (β : MulAut JH) (hβ : ∀ τ, ∃ σ, kappa σ = β (kappa τ)) :
    alternatingGroup (Fin 9) →* alternatingGroup (Fin 9) where
  toFun τ := (hβ τ).choose
  map_one' := kappa_injective (by rw [(hβ 1).choose_spec]; simp only [map_one])
  map_mul' a b := kappa_injective (by
    rw [(hβ (a * b)).choose_spec]
    simp only [map_mul, (hβ a).choose_spec, (hβ b).choose_spec])

theorem restrA9_spec
    (β : MulAut JH) (hβ : ∀ τ, ∃ σ, kappa σ = β (kappa τ))
    (τ : alternatingGroup (Fin 9)) : kappa (restrA9 β hβ τ) = β (kappa τ) :=
  (hβ τ).choose_spec

theorem restrA9_injective
    (β : MulAut JH) (hβ : ∀ τ, ∃ σ, kappa σ = β (kappa τ)) :
    Function.Injective (restrA9 β hβ) := fun a b h =>
  kappa_injective (β.injective (by rw [← restrA9_spec β hβ a, ← restrA9_spec β hβ b, h]))

theorem exists_adjust
    (α₁ : MulAut JH) (hfix : α₁ (sJ 0) = sJ 0) :
    ∃ ℓ ∈ L1J, ∃ U : Perm (Fin 12), (U = 1 ∨ U = swap 3 4) ∧
      (MulAut.conj ℓ * α₁) (sJ 0) = sJ 0 ∧ ∀ σ : alternatingGroup (Fin 12), σ ∈ alt3 →
        ∃ σ' : alternatingGroup (Fin 12), (σ' : Perm (Fin 12)) = U * σ * U⁻¹ ∧
          (MulAut.conj ℓ * α₁) (iotaA σ) = iotaA σ' := by
  have hL : L1J.map (autHom α₁) = L1J := by
    rw [← commutator_CJ_s1, Subgroup.map_commutator, map_CJ, hfix]
  have hβ : ∀ τ, ∃ σ, kappa σ = α₁ (kappa τ) := by
    intro τ
    have : α₁ (kappa τ) ∈ L1J := by
      rw [← hL]
      exact Subgroup.mem_map_of_mem _ (mem_L1J_iff.2 ⟨τ, rfl⟩)
    exact mem_L1J_iff.1 this
  have hF := restrA9_injective α₁ hβ
  obtain ⟨π, hπ⟩ := CFSG.Milestones.alternating_automorphism_permutation (n := 9)
    (Or.inr (by norm_num))
    (MulEquiv.ofBijective (restrA9 α₁ hβ) ⟨hF, Finite.injective_iff_surjective.1 hF⟩)
  have hact : ∀ σ : alternatingGroup (Fin 12), σ ∈ alt3 → ∃ σ₁ : alternatingGroup (Fin 12),
      (σ₁ : Perm (Fin 12)) = ext3 π * σ * (ext3 π)⁻¹ ∧ α₁ (iotaA σ) = iotaA σ₁ := by
    intro σ hσ
    obtain ⟨τ, hτ⟩ := alt9Hom_surjective ⟨σ, hσ⟩
    have hk : kappa τ = iotaA σ := by
      show iotaA ((alt9Hom τ : alt3) : alternatingGroup (Fin 12)) = iotaA σ
      rw [hτ]
    have hστ : ext3 (τ : Perm (Fin 9)) = σ :=
      congrArg (fun x : alt3 => ((x : alternatingGroup (Fin 12)) : Perm (Fin 12))) hτ
    refine ⟨((alt9Hom (restrA9 α₁ hβ τ) : alt3) : alternatingGroup (Fin 12)), ?_, ?_⟩
    · have e : ((restrA9 α₁ hβ τ : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
          π * τ * π⁻¹ := hπ τ
      show ext3 ((restrA9 α₁ hβ τ : alternatingGroup (Fin 9)) : Perm (Fin 9)) =
        ext3 π * σ * (ext3 π)⁻¹
      rw [e, map_mul, map_mul, map_inv, hστ]
    · rw [← hk, ← restrA9_spec α₁ hβ τ]
      rfl
  have hPfix : ∀ j : Fin 12, j.val < 3 → ext3 π j = j := fun j hj => ext3_fix π hj
  have hPinvfix : ∀ j : Fin 12, j.val < 3 → (ext3 π)⁻¹ j = j := fun j hj => by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (hPfix j hj).symm
  obtain ⟨lam, hlam, U, hU, hlamU⟩ : ∃ lam : alternatingGroup (Fin 12), lam ∈ alt3 ∧
      ∃ U : Perm (Fin 12), (U = 1 ∨ U = swap 3 4) ∧ (lam : Perm (Fin 12)) * ext3 π = U := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (ext3 π)) with h | h
    · exact ⟨⟨(ext3 π)⁻¹, by rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_inv, h]⟩,
        (mem_alt3 _).2 hPinvfix, 1, Or.inl rfl, inv_mul_cancel _⟩
    · refine ⟨⟨swap 3 4 * (ext3 π)⁻¹, ?_⟩, (mem_alt3 _).2 fun j hj => ?_, swap 3 4, Or.inr rfl,
        by show swap 3 4 * (ext3 π)⁻¹ * ext3 π = swap 3 4; rw [inv_mul_cancel_right]⟩
      · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, h,
          Equiv.Perm.sign_swap (by decide)]
        decide
      · show (swap (3 : Fin 12) 4 * (ext3 π)⁻¹ : Perm (Fin 12)) j = j
        rw [Equiv.Perm.mul_apply, hPinvfix j hj]
        exact Equiv.swap_apply_of_ne_of_ne (fun h' => by rw [h'] at hj; exact absurd hj (by decide))
          (fun h' => by rw [h'] at hj; exact absurd hj (by decide))
  have hℓ : iotaA lam ∈ L1J := ⟨lam, hlam, rfl⟩
  refine ⟨iotaA lam, hℓ, U, hU, ?_, fun σ hσ => ?_⟩
  · rw [MulAut.mul_apply, hfix, MulAut.conj_apply, CJ_s1_structure.2.2 _ hℓ, mul_assoc,
      mul_inv_cancel, mul_one]
  · obtain ⟨σ₁, hσ₁, he⟩ := hact σ hσ
    refine ⟨lam * σ₁ * lam⁻¹, ?_, ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, hσ₁]
      rw [← hlamU, mul_inv_rev]
      group
    · rw [MulAut.mul_apply, he, MulAut.conj_apply, map_mul, map_mul, map_inv]

@[expose] def blockRho : Fin 4 → Perm (Fin 12)
  | 0 => 1
  | 1 => swap 0 3 * swap 1 4 * swap 2 5 * swap 6 7
  | 2 => swap 0 6 * swap 1 7 * swap 2 8 * swap 3 4
  | 3 => swap 0 9 * swap 1 10 * swap 2 11 * swap 3 4

theorem blockRho_sign (i : Fin 4) : Equiv.Perm.sign (blockRho i) = 1 := by
  fin_cases i <;> decide

theorem blockRho_block (i : Fin 4) : ∀ j : Fin 12, j.val < 3 → (blockRho i j).val / 3 = i.val := by
  fin_cases i <;> decide

@[expose] def rhoA (i : Fin 4) : alternatingGroup (Fin 12) :=
  ⟨blockRho i, Equiv.Perm.mem_alternatingGroup.2 (blockRho_sign i)⟩

abbrev blockAlt (i : Fin 4) : Subgroup (alternatingGroup (Fin 12)) :=
  alt3.map (MulAut.conj (rhoA i)).toMonoidHom

theorem mem_blockAlt {i : Fin 4} {σ : alternatingGroup (Fin 12)}
    (h : ∀ j : Fin 12, j.val / 3 = i.val → (σ : Perm (Fin 12)) j = j) : σ ∈ blockAlt i := by
  rw [blockAlt, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_alt3]
  intro j hj
  have := h _ (blockRho_block i j hj)
  show (blockRho i)⁻¹ ((σ : Perm (Fin 12)) (blockRho i j)) = j
  rw [this]
  exact Equiv.symm_apply_apply _ _

theorem exists_block_fixed {σ : Perm (Fin 12)} (hσ : σ.IsThreeCycle) :
    ∃ i : Fin 4, ∀ j : Fin 12, j.val / 3 = i.val → σ j = j := by
  by_contra hne
  have hall : ∀ i : Fin 4, ∃ j : Fin 12, j.val / 3 = i.val ∧ σ j ≠ j := by
    intro i
    by_contra h'
    exact hne ⟨i, fun j hj => by
      by_contra hj'
      exact h' ⟨j, hj, hj'⟩⟩
  choose f hf hfj using hall
  have hinj : Function.Injective f := fun a b hab => Fin.ext (by rw [← hf a, ← hf b, hab])
  have hsub : Finset.univ.map ⟨f, hinj⟩ ⊆ σ.support := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Equiv.Perm.mem_support.2 (hfj i)
  have := Finset.card_le_card hsub
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin, hσ.card_support] at this
  omega

theorem top_le_blockAlt : (⊤ : Subgroup (alternatingGroup (Fin 12))) ≤
    blockAlt 0 ⊔ blockAlt 1 ⊔ blockAlt 2 ⊔ blockAlt 3 := by
  have h3 : Subgroup.closure {σ : Perm (Fin 12) | σ.IsThreeCycle} ≤
      (blockAlt 0 ⊔ blockAlt 1 ⊔ blockAlt 2 ⊔ blockAlt 3).map
        (alternatingGroup (Fin 12)).subtype := by
    rw [Subgroup.closure_le]
    intro c hc
    obtain ⟨i, hi⟩ := exists_block_fixed hc
    refine ⟨⟨c, hc.mem_alternatingGroup⟩, ?_, rfl⟩
    have hmem := mem_blockAlt (σ := ⟨c, hc.mem_alternatingGroup⟩) hi
    fin_cases i
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hmem))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem)
    · exact Subgroup.mem_sup_right hmem
  have hS := Equiv.Perm.closure_three_cycles_eq_alternating.ge.trans h3
  intro σ _
  obtain ⟨σ', hσ', he⟩ := hS σ.2
  rw [← Subtype.val_injective he]
  exact hσ'

theorem iotaA_range :
    (⊤ : Subgroup (alternatingGroup (Fin 12))).map iotaA = HJ := by
  ext y
  constructor
  · rintro ⟨σ, -, rfl⟩
    exact iotaA_mem σ
  · intro hy
    exact ⟨thetaJ ⟨y, hy⟩, trivial, iotaA_theta _⟩

abbrev yJ
    (i : Fin 4) : JH := iotaA (rhoA i) * sJ 0 * (iotaA (rhoA i))⁻¹

theorem conjHom_bijective (r : JH) : Function.Bijective (MulAut.conj r).toMonoidHom := by
  constructor
  · intro a b h
    have h' : r * a * r⁻¹ = r * b * r⁻¹ := h
    simpa using h'
  · intro y
    exact ⟨r⁻¹ * y * r, by show r * (r⁻¹ * y * r) * r⁻¹ = y; group⟩

theorem DJ_yJ
    (i : Fin 4) : DJ (yJ i) = (blockAlt i).map iotaA := by
  have e : DJ (yJ i) = (DJ (sJ 0)).map (MulAut.conj (iotaA (rhoA i))).toMonoidHom := by
    rw [map_DJ_of_bijective (MulAut.conj (iotaA (rhoA i))).toMonoidHom (conjHom_bijective _)]
    rfl
  rw [e, DJ, commutator_CJ_s1]
  ext y
  constructor
  · rintro ⟨z, ⟨σ, hσ, rfl⟩, rfl⟩
    refine ⟨MulAut.conj (rhoA i) σ, ⟨σ, hσ, rfl⟩, ?_⟩
    show iotaA (rhoA i * σ * (rhoA i)⁻¹) = iotaA (rhoA i) * iotaA σ * (iotaA (rhoA i))⁻¹
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨z, ⟨σ, hσ, rfl⟩, rfl⟩
    refine ⟨iotaA σ, ⟨σ, hσ, rfl⟩, ?_⟩
    show iotaA (rhoA i) * iotaA σ * (iotaA (rhoA i))⁻¹ = iotaA (rhoA i * σ * (rhoA i)⁻¹)
    rw [map_mul, map_mul, map_inv]

theorem HJ_eq_sup :
    HJ = DJ (yJ 0) ⊔ DJ (yJ 1) ⊔ DJ (yJ 2) ⊔ DJ (yJ 3) := by
  rw [DJ_yJ, DJ_yJ, DJ_yJ, DJ_yJ, ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup,
    eq_top_iff.2 top_le_blockAlt, iotaA_range]

theorem map_HJ_of_DJ
    (β : MulAut JH) (h0 : DJ (β (yJ 0)) = DJ (yJ 0))
    (h1 : DJ (β (yJ 1)) = DJ (yJ 1)) (h2 : DJ (β (yJ 2)) = DJ (yJ 2))
    (h3 : DJ (β (yJ 3)) = DJ (yJ 3)) : HJ.map (autHom β) = HJ := by
  rw [HJ_eq_sup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, map_DJ, map_DJ, map_DJ,
    map_DJ, h0, h1, h2, h3]

theorem yJ_eq
    (i : Fin 4) : yJ i = iotaA (rhoA i * tri012A * (rhoA i)⁻¹) := by
  rw [map_mul, map_mul, map_inv, iotaA_tri012]

theorem yJ_zero :
    yJ 0 = sJ 0 := by
  rw [yJ_eq, show rhoA 0 = 1 from Subtype.ext rfl, one_mul, inv_one, mul_one, iotaA_tri012]

theorem blockTri_fix (i : Fin 4) (hi : i ≠ 0) :
    ∀ j : Fin 12, j.val < 3 → (blockRho i * tri 0 1 2 * (blockRho i)⁻¹) j = j := by
  fin_cases i
  · exact absurd rfl hi
  all_goals unfold blockRho tri; decide

theorem blockTri_swap (i : Fin 4) (hi : i ≠ 0) :
    swap 3 4 * (blockRho i * tri 0 1 2 * (blockRho i)⁻¹) * (swap 3 4)⁻¹ =
        blockRho i * tri 0 1 2 * (blockRho i)⁻¹ ∨
      swap 3 4 * (blockRho i * tri 0 1 2 * (blockRho i)⁻¹) * (swap 3 4)⁻¹ =
        (blockRho i * tri 0 1 2 * (blockRho i)⁻¹)⁻¹ := by
  fin_cases i
  · exact absurd rfl hi
  · right; unfold blockRho tri; decide
  · left; unfold blockRho tri; decide
  · left; unfold blockRho tri; decide

theorem DJ_aut_yJ
    (β : MulAut JH) (U : Perm (Fin 12)) (hU : U = 1 ∨ U = swap 3 4)
    (hβ : ∀ σ : alternatingGroup (Fin 12), σ ∈ alt3 → ∃ σ' : alternatingGroup (Fin 12),
      (σ' : Perm (Fin 12)) = U * σ * U⁻¹ ∧ β (iotaA σ) = iotaA σ')
    (i : Fin 4) (hi : i ≠ 0) : DJ (β (yJ i)) = DJ (yJ i) := by
  have hmem : rhoA i * tri012A * (rhoA i)⁻¹ ∈ alt3 := (mem_alt3 _).2 (blockTri_fix i hi)
  obtain ⟨σ', hσ', he⟩ := hβ _ hmem
  rw [yJ_eq, he]
  have hc : (σ' : Perm (Fin 12)) = blockRho i * tri 0 1 2 * (blockRho i)⁻¹ ∨
      (σ' : Perm (Fin 12)) = (blockRho i * tri 0 1 2 * (blockRho i)⁻¹)⁻¹ := by
    rw [hσ']
    rcases hU with rfl | rfl
    · left
      simp only [one_mul, inv_one, mul_one]
      rfl
    · exact blockTri_swap i hi
  rcases hc with h | h
  · rw [show σ' = rhoA i * tri012A * (rhoA i)⁻¹ from Subtype.ext h]
  · rw [show σ' = (rhoA i * tri012A * (rhoA i)⁻¹)⁻¹ from Subtype.ext h, map_inv, DJ_inv]

theorem aut_factor
    (α : MulAut JH) :
    ∃ g : JH, ∃ β : MulAut JH, α = MulAut.conj g * β ∧ ∀ h : JH, h ∈ HJ ↔ β h ∈ HJ := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_s1_aut α (IsConj.refl (sJ 0)))
  have hfix : ((MulAut.conj g)⁻¹ * α) (sJ 0) = sJ 0 := by
    rw [MulAut.mul_apply, ← hg, MulAut.conj_inv_apply]
    group
  obtain ⟨ℓ, -, U, hU, h0, hact⟩ := exists_adjust _ hfix
  have hH := map_HJ_of_DJ (MulAut.conj ℓ * ((MulAut.conj g)⁻¹ * α)) (by rw [yJ_zero, h0])
    (DJ_aut_yJ _ U hU hact 1 (by decide)) (DJ_aut_yJ _ U hU hact 2 (by decide))
    (DJ_aut_yJ _ U hU hact 3 (by decide))
  refine ⟨g * ℓ⁻¹, MulAut.conj ℓ * ((MulAut.conj g)⁻¹ * α), ?_, fun h =>
    ⟨fun hh => ?_, fun hh => ?_⟩⟩
  · rw [map_mul, map_inv]
    group
  · rw [← hH]
    exact ⟨h, hh, rfl⟩
  · rw [← hH] at hh
    obtain ⟨z, hz, hzh⟩ := hh
    rw [autHom_apply] at hzh
    rw [← (MulAut.conj ℓ * ((MulAut.conj g)⁻¹ * α)).injective hzh]
    exact hz

theorem ctuc_hn_intrinsic_three_class_and_alternating_localization :
    (∀ x : JH, orderOf x = 3 ↔ IsConj (sJ 0) x ∨ IsConj (sJ 2) x) ∧ ¬ IsConj (sJ 0) (sJ 2) ∧
    IsConj (sJ 0) (sJ 1) ∧ IsConj (sJ 0) (sJ 3) ∧
    (∀ x : JH, IsConj (sJ 0) x → Nat.card (Subgroup.centralizer {x}) = 544320) ∧
    (∀ x : JH, IsConj (sJ 2) x → Nat.card (Subgroup.centralizer {x}) = 29160) ∧
    (∀ (α : MulAut JH) (x : JH), IsConj (sJ 0) x → IsConj (sJ 0) (α x)) ∧
    ∀ α : MulAut JH, ∃ g : JH, ∃ β : MulAut JH,
      α = MulAut.conj g * β ∧ ∀ h : JH, h ∈ HJ ↔ β h ∈ HJ :=
  ⟨order_three_classes, not_isConj_s1_s3, isConj_s1_s2, isConj_s1_s4,
    fun _ hx => (card_CJ_of_isConj hx).trans card_CJ_s1,
    fun _ hx => (card_CJ_of_isConj hx).trans card_CJ_s3,
    fun α _ hx => isConj_s1_aut α hx, aut_factor⟩

end CFSG.Sporadic.HNSchreier
