module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityMixing

public section

namespace CFSG.RankThree.PartOne.KCUnitaryLines

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.RankThree.PartOne.KCUnitaryMixing

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {Ahat : Subgroup (gramSU h (idGram K n))}

structure NonsplitFacts (h : UnitaryFieldData ℓ f K) (n p : ℕ)
    (Ahat : Subgroup (gramSU h (idGram K n))) : Prop where
  decomp : PlaneKernelDecomposition h n p Ahat
  e_gt : 1 < ordNegQ ℓ f p
  e_two : ordNegQ ℓ f p = 2 → p ∣ ℓ ^ f - 1 ∧ 3 < ℓ ^ f
  q_two : ℓ ^ f = 2 → 4 ≤ ordNegQ ℓ f p
  q_three : ℓ ^ f = 3 → 3 ≤ ordNegQ ℓ f p

theorem NonsplitFacts.not_dvd (F : NonsplitFacts h n p Ahat) (hp : p.Prime) :
    ¬ p ∣ ℓ ^ f + 1 := fun hd => by
  have := (ordNegQ_eq_one_iff hp).mpr hd
  have := F.e_gt
  omega

theorem NonsplitFacts.e_le_finrank (F : NonsplitFacts h n p Ahat) {L : Subgroup ↥Ahat}
    (hL : Nat.card L = p) (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥) :
    ordNegQ ℓ f p ≤ Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L) := by
  have hpos : 0 < Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hVL)
  exact Nat.le_of_dvd hpos (F.decomp.dvd_finrank L hL)

theorem NonsplitFacts.two_le_finrank (F : NonsplitFacts h n p Ahat) {L : Subgroup ↥Ahat}
    (hL : Nat.card L = p) (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥) :
    2 ≤ Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L) :=
  (F.e_gt).trans_le (F.e_le_finrank hL hVL)

theorem primaryComponent_X_sub_one_eq (F : NonsplitFacts h n p Ahat) {L : Subgroup ↥Ahat}
    (hL : Nat.card L = p) {t : ↥Ahat} (htL : t ∈ L) (ht1 : t ≠ 1) :
    primaryComponent (xlin h n t.1) (X - C 1) =
      fixedSpace (planeRep h n Ahat) ⊤ ⊔ lineSpace (planeRep h n Ahat) (idForm h n) L := by
  rw [primaryComponent_X_sub_C_one]
  exact F.decomp.ker_eq L hL t htL ht1

theorem finrank_X_sub_one_not_exceptional (F : NonsplitFacts h n p Ahat) {L : Subgroup ↥Ahat}
    (hL : Nat.card L = p) (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥)
    {t : ↥Ahat} (htL : t ∈ L) (ht1 : t ≠ 1) :
    (Module.finrank K (primaryComponent (xlin h n t.1) (X - C 1)), ℓ ^ f) ∉
      ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
  have hW := primaryComponent_X_sub_one_eq F hL htL ht1
  have hd := F.e_le_finrank hL hVL
  have hle : Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L) ≤
      Module.finrank K (primaryComponent (xlin h n t.1) (X - C 1)) := by
    rw [hW]
    exact Submodule.finrank_mono le_sup_right
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or]
  have hq2 := F.q_two
  have hq3 := F.q_three
  refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨hm', hq'⟩
  · have := hq2 hq'
    omega
  · have := hq3 hq'
    omega
  · have := hq2 hq'
    omega

theorem isGoodBlock_X_sub_one (F : NonsplitFacts h n p Ahat) {L : Subgroup ↥Ahat}
    (hL : Nat.card L = p) (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥)
    {t : ↥Ahat} (htL : t ∈ L) (ht1 : t ≠ 1) :
    ∃ hmem : (X - C 1 : K[X]) ∈ primaryFactors (xlin h n t.1),
      IsGoodBlock h (toLinU h n (liftUnitary t.1)) ⟨X - C 1, hmem⟩ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVL
  have hfix : xlin h n t.1 v = (1 : K) • v := by
    rw [one_smul]
    exact hv.1 t htL
  have hev : Module.End.HasEigenvalue (xlin h n t.1) 1 :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hfix, hv0⟩
  have hmem := X_sub_C_mem_primaryFactors hev
  refine ⟨hmem, ?_⟩
  have hW := primaryComponent_X_sub_one_eq F hL htL ht1
  have hd := F.e_le_finrank hL hVL
  have hle : Module.finrank K (lineSpace (planeRep h n Ahat) (idForm h n) L) ≤
      Module.finrank K (primaryComponent (xlin h n t.1) (X - C 1)) := by
    rw [hW]
    exact Submodule.finrank_mono le_sup_right
  have h2 := F.e_gt
  have hm : 2 ≤ Module.finrank K (primaryComponent (xlin h n t.1) (X - C 1)) := by omega
  exact isGoodBlock_X_sub_C (hK := h) hmem hm (finrank_X_sub_one_not_exceptional F hL hVL htL ht1)

theorem exists_scalar_on_sup (F : NonsplitFacts h n p Ahat) (S : PlaneSetup h n p Ahat)
    {L : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hVL : lineSpace (planeRep h n Ahat) (idForm h n) L ≠ ⊥)
    (M : primeFormUnitary h (idGram K n))
    (hMx : ∀ x ∈ Ahat, M * liftUnitary x = liftUnitary x * M)
    (hMb : ∀ x ∈ Ahat, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ g ∈ idSpecialBlock h x (i.1 : K[X]),
      M * g = g * M) :
    ∃ c : K, ∀ v ∈ fixedSpace (planeRep h n Ahat) ⊤ ⊔ lineSpace (planeRep h n Ahat) (idForm h n) L,
      ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v := by
  have hex : ∃ t : ↥Ahat, t ∈ L ∧ t ≠ 1 := by
    have h1 : Nontrivial ↥L := by
      have := h.finite
      have : Finite ↥Ahat := inferInstance
      exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hL]; exact S.prime.one_lt)
    obtain ⟨t, ht⟩ := exists_ne (1 : ↥L)
    exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
  obtain ⟨t, htL, ht1⟩ := hex
  obtain ⟨hmem, hgood⟩ := isGoodBlock_X_sub_one F hL hVL htL ht1
  have hx1 : t.1 ≠ 1 := fun h' => ht1 (Subtype.ext h')
  obtain ⟨c, hc⟩ := exists_scalar_of_commute_block_X_sub_C S t.2 hmem hgood M (hMx t.1 t.2)
    (fun g hg => hMb t.1 t.2 hx1 ⟨⟨X - C 1, hmem⟩, hgood⟩ g hg)
  refine ⟨c, fun v hv => hc v ?_⟩
  have : v ∈ primaryComponent (xlin h n t.1) (X - C 1) := by
    rw [primaryComponent_X_sub_one_eq F hL htL ht1]
    exact hv
  rw [one_smul]
  have h2 := mem_primaryComponent_X_sub_C.mp this
  rw [one_smul] at h2
  exact h2

theorem exists_orthonormal_family {W : Submodule K (Fin n → K)}
    (hsep : ((idForm h n).domRestrict₁₂ W W).SeparatingLeft) {m : ℕ}
    (hdim : m ≤ Module.finrank K W) :
    ∃ b : Fin m → Fin n → K, (∀ i, b i ∈ W) ∧ KCUnitaryFrame.IsOrthonormalFamily h b := by
  have := h.finite
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (M := ↥W)
    (B := (idForm h n).domRestrict₁₂ W W) ((idForm_isSymm h n).domRestrict W) hsep
  refine ⟨fun i => (e (Fin.castLE hdim i) : Fin n → K), fun i => (e _).2, fun i j => ?_⟩
  have h1 := he (Fin.castLE hdim i) (Fin.castLE hdim j)
  simp only [LinearMap.domRestrict₁₂_apply] at h1
  rw [h1]
  simp [Fin.castLE_inj]

theorem exists_orthonormal_triple {W : Submodule K (Fin n → K)}
    (hsep : ((idForm h n).domRestrict₁₂ W W).SeparatingLeft) (hdim : 3 ≤ Module.finrank K W) :
    ∃ b : Fin 3 → Fin n → K, (∀ i, b i ∈ W) ∧ KCUnitaryFrame.IsOrthonormalFamily h b :=
  exists_orthonormal_family hsep hdim

end CFSG.RankThree.PartOne.KCUnitaryLines
