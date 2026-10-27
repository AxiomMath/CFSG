module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Generate
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.U3Fixed
public import CFSG.LocalAnalysis.UniquenessCase.UC22L3U3Torus
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Chevalley (fixSubfield)
open Subgroup

@[expose] def GoodU3 (J : Type) [Group J] : Prop :=
  Finite J ∧ 3 ∣ Nat.card J ∧ ¬ 9 ∣ Nat.card J ∧ ¬ 7 ∣ Nat.card J ∧
    ∃ (p f : ℕ) (K : Type) (_ : Field K) (h : UnitaryFieldData p f K), p ^ f % 3 = 1 ∧
      Nonempty (J ≃* U3 h)

theorem goodU3_of_mulEquiv (J J' : Type) [Group J] [Group J'] (e : J ≃* J') (h : GoodU3 J) :
    GoodU3 J' := by
  obtain ⟨hfin, h3, h9, h7, p, f, K, hK, hU, hq, ⟨eJ⟩⟩ := h
  haveI : Finite J := hfin
  have hcard : Nat.card J = Nat.card J' := Nat.card_congr e.toEquiv
  refine ⟨Finite.of_equiv J e.toEquiv, ?_, ?_, ?_, p, f, K, hK, hU, hq, ⟨e.symm.trans eJ⟩⟩
  · rw [← hcard]; exact h3
  · rw [← hcard]; exact h9
  · rw [← hcard]; exact h7

section Helpers

open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

variable {p f : ℕ} {K : Type} [Field K]

private theorem ksu3s_pow_mod_eq_of_seven (p f f₀ : ℕ) (hf : f = 7 * f₀)
    (h : p ^ f % 3 = 1) : p ^ f₀ % 3 = 1 := by
  have hx : p ^ f = (p ^ f₀) ^ 7 := by rw [hf, pow_mul']
  rw [hx, Nat.pow_mod] at h
  have h3 : p ^ f₀ % 3 = 0 ∨ p ^ f₀ % 3 = 1 ∨ p ^ f₀ % 3 = 2 := by
    have := Nat.mod_lt (p ^ f₀) (show 0 < 3 by norm_num)
    omega
  rcases h3 with h0 | h1 | h2
  · rw [h0] at h; norm_num at h
  · exact h1
  · rw [h2] at h; norm_num at h

private theorem ksu3s_pow_eight_lt_pow_fourteen_sub_one (q : ℕ) (hq : 2 ≤ q) :
    q ^ 8 < q ^ 14 - 1 := by
  have h6 : 64 ≤ q ^ 6 := by
    have := Nat.pow_le_pow_left hq 6; norm_num at this ⊢; omega
  have h8 : 256 ≤ q ^ 8 := by
    have := Nat.pow_le_pow_left hq 8; norm_num at this ⊢; omega
  have h : q ^ 8 + 1 < q ^ 14 := by nlinarith
  omega

private theorem ksu3s_prod_lt_pow_eight (q : ℕ) (hq : 2 ≤ q) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 8 := by
  have h1 : (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 5 := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith),
      pow_pos (by omega : 0 < q) 3]
  have h2 : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) < q ^ 3 * q ^ 5 :=
    Nat.mul_lt_mul_of_pos_left h1 (pow_pos (by omega) 3)
  calc q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)
      = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by ring
    _ < q ^ 3 * q ^ 5 := h2
    _ = q ^ 8 := by ring

private theorem ksu3s_card_gramSU_three (h : UnitaryFieldData p f K) :
    Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  haveI := h.finite
  have hsymm : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp [Matrix.map_one])
  have hsep : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hsymm hsep
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]
    ring
  rw [hprod] at hSU
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq2]
  rw [hSU]
  norm_num
  ring

private theorem ksu3s_card_U3_le_gramSU (h : UnitaryFieldData p f K) :
    Nat.card (U3 h) ≤ Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  haveI := h.finite
  let S : Subgroup (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup S
  have hpos : 0 < Nat.card S := by
    haveI : Nonempty S := ⟨1⟩
    exact Nat.card_pos
  calc Nat.card (U3 h)
      = Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ⧸ S) := rfl
    _ ≤ Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ⧸ S) *
          Nat.card S := Nat.le_mul_of_pos_right _ hpos
    _ = Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := hc.symm

private theorem ksu3s_card_U3_lt (h : UnitaryFieldData p f K) :
    Nat.card (U3 h) < (p ^ f) ^ 8 := by
  have hle := ksu3s_card_U3_le_gramSU h
  rw [ksu3s_card_gramSU_three h] at hle
  have hq2 : 2 ≤ p ^ f :=
    le_trans h.prime.two_le (le_self_pow (a := p) (n := f) h.prime.one_le
      (Nat.one_le_iff_ne_zero.mp h.one_le))
  exact lt_of_le_of_lt hle (ksu3s_prod_lt_pow_eight (p ^ f) hq2)

private theorem ksu3s_center_eq_bot (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) :
    Subgroup.center (U3 h) = ⊥ := by
  haveI := h.finite
  have hnq : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    rw [h2] at hq
    norm_num at hq
  have hnc : ¬∀ x y : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      x * y = y * x :=
    CFSG.RankThree.Classical.not_commute_primeFormP_one (n := 3) h (by norm_num) hnq
  haveI : IsSimpleGroup (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one (n := 3) h (by norm_num) hnq
  change Subgroup.center (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = ⊥
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) with
    h0 | h1
  · exact h0
  · exfalso
    exact hnc (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h1))

private theorem ksu3s_orderOf_u3Field (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1)
    (σ : K ≃+* K) (hσ : orderOf σ = 7) : orderOf (u3Field h σ) = 7 := by
  haveI := h.finite
  have hnq : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    rw [h2] at hq
    norm_num at hq
  rw [show u3Field h σ = primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ from rfl,
    orderOf_injective _ (CFSG.RankThree.Classical.primeFormFieldHom_injective (n := 3) h
      (by norm_num) hnq) σ, hσ]

private theorem ksu3s_lieModel (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) :
    CFSG.Blueprint.LieModel (U3 h) .PSU 3 p f := by
  haveI := h.finite
  refine Or.inl ⟨by decide, ?_⟩
  refine ⟨⟨h.prime, h.one_le, le_rfl, ?_⟩, K, inferInstance, inferInstance, ?_, ?_⟩
  · intro hh
    have h2 : p ^ f = 2 := ((Prod.mk.injEq 3 (p ^ f) 3 2).mp hh).2
    rw [h2] at hq
    norm_num at hq
  · rw [h.card, pow_mul']
  · exact ⟨(psuPrimeFormEquiv h).symm.trans (unitaryPSUEquiv h (by norm_num))⟩

private theorem ksu3s_isPerfect_of_simple_nonabelian {J : Type} [Group J] (F : Subgroup J)
    (hsimple : IsSimpleGroup ↥F) (hnab : ∃ a b : ↥F, a * b ≠ b * a) :
    Group.IsPerfect ↥F := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥F) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (isMulCommutative_iff.mp ((commutator_eq_bot_iff ↥F).mp h) a b)
  · exact h

private theorem ksu3s_commutator_eq_self {J : Type} [Group J] (F : Subgroup J)
    (hperf : Group.IsPerfect ↥F) : ⁅F, F⁆ = F := by
  rw [← Subgroup.map_subtype_commutator F, Group.isPerfect_def.mp hperf, Subgroup.map_top,
    Subgroup.range_subtype]

end Helpers

theorem u3_stepConcl_zpowers {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (h9 : ¬ 9 ∣ Nat.card (U3 h))
    (h7 : ¬ 7 ∣ Nat.card (U3 h)) (σ : K ≃+* K) (hσ : orderOf σ = 7) (Z : Subgroup (U3 h))
    (hZ3 : Nat.card Z = 3) (hZ : ∀ w ∈ Subgroup.zpowers (u3Field h σ), ∀ z ∈ Z, w z = z) :
    StepConcl GoodU3 (Subgroup.zpowers (u3Field h σ)) Z := by
  haveI := h.finite
  obtain ⟨f₀, h₀, hf7, ⟨eF⟩, hsimple, hnab⟩ := u3_fixedBy_zpowers_equiv h hq σ hσ
  let W₀ : Subgroup (MulAut (U3 h)) := Subgroup.zpowers (u3Field h σ)
  let F : Subgroup (U3 h) := fixedBy W₀
  have hZF : Z ≤ F := fun z hz => mem_fixedBy.mpr fun w hw => hZ w hw z hz
  have hW₀ : IsPGroup 7 W₀ := by
    refine IsPGroup.of_card (n := 1) ?_
    show Nat.card (Subgroup.zpowers (u3Field h σ)) = 7 ^ 1
    rw [Nat.card_zpowers, ksu3s_orderOf_u3Field h hq σ hσ, pow_one]
  have hrig : ∀ α : MulAut (U3 h), (∀ x ∈ fixedBy W₀, α x = x) → α ∈ W₀ :=
    fun α hα => u3_mem_zpowers_of_fixes h hq σ hσ α (fun x hx => hα x hx)
  have hLM : CFSG.Blueprint.LieModel (U3 h) .PSU 3 p f := ksu3s_lieModel h hq
  obtain ⟨C, hCcen, -, hCcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.exists_cyclic_le_centralizer_of_card_three
      (S := U3 h) (Or.inr ⟨hq, hLM⟩) (D := Z) hZ3
  have hle : (p ^ f) ^ 2 - 1 ≤ Nat.card (normalizer (Z : Set (U3 h))) := by
    rw [← hCcard]
    exact Subgroup.card_le_of_le
      (le_trans hCcen (Subgroup.centralizer_le_normalizer (Z : Set (U3 h))))
  have hFcard : Nat.card F = Nat.card (U3 h₀) := Nat.card_congr eF.toEquiv
  have hFlt : Nat.card F < (p ^ f₀) ^ 8 := by
    rw [hFcard]
    exact ksu3s_card_U3_lt h₀
  have hpows : (p ^ f₀) ^ 8 < (p ^ f) ^ 2 - 1 := by
    have hq₀ : 2 ≤ p ^ f₀ :=
      le_trans h₀.prime.two_le (le_self_pow (a := p) (n := f₀) h₀.prime.one_le
        (Nat.one_le_iff_ne_zero.mp h₀.one_le))
    have hx : p ^ f = (p ^ f₀) ^ 7 := by rw [hf7, pow_mul']
    rw [hx]
    have h14 : ((p ^ f₀) ^ 7) ^ 2 = (p ^ f₀) ^ 14 := by rw [← pow_mul]
    rw [h14]
    exact ksu3s_pow_eight_lt_pow_fourteen_sub_one (p ^ f₀) hq₀
  have hcard : Nat.card F < Nat.card (normalizer (Z : Set (U3 h))) :=
    lt_of_lt_of_le (lt_trans hFlt hpows) hle
  have hpair : ∀ n : U3 h, (fixedBy W₀).map (MulAut.conj n).toMonoidHom ≠ fixedBy W₀ →
      fixedBy W₀ ⊔ (fixedBy W₀).map (MulAut.conj n).toMonoidHom = ⊤ :=
    fun x hne => u3_fixedBy_sup_conj_eq_top h hq σ hσ x hne
  have hgen : normalizer (Z : Set (U3 h)) ⊔ fixedBy W₀ = ⊤ :=
    normalizer_sup_fixedBy_eq_top (J := U3 h) (ksu3s_center_eq_bot h hq) h7 W₀ hW₀ hrig Z
      hcard hpair
  have hperf : Group.IsPerfect ↥F := ksu3s_isPerfect_of_simple_nonabelian F hsimple hnab
  have hcommF : ⁅F, F⁆ = F := ksu3s_commutator_eq_self F hperf
  have hGoodF : GoodU3 ↥F := by
    obtain ⟨h3F, h9F, h7F⟩ := card_facts_of_le (J := U3 h) (F := F) (Z := Z) hZF hZ3 h9 h7
    exact ⟨inferInstance, h3F, h9F, h7F, p, f₀, ↥(fixSubfield σ), inferInstance, h₀,
      ksu3s_pow_mod_eq_of_seven p f f₀ hf7 hq, ⟨eF⟩⟩
  have hGoodComm : GoodU3 ↥⁅F, F⁆ :=
    goodU3_of_mulEquiv ↥F ↥⁅F, F⁆ (MulEquiv.subgroupCongr hcommF.symm) hGoodF
  have hZcomm : Z ≤ ⁅F, F⁆ := by rw [hcommF]; exact hZF
  have hsup : normalizer (Z : Set (U3 h)) ⊔ ⁅F, F⁆ = ⊤ := by rw [hcommF]; exact hgen
  unfold StepConcl
  change GoodU3 ↥⁅F, F⁆ ∧ Z ≤ ⁅F, F⁆ ∧
    normalizer (Z : Set (U3 h)) ⊔ ⁅F, F⁆ = ⊤
  exact ⟨hGoodComm, hZcomm, hsup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
