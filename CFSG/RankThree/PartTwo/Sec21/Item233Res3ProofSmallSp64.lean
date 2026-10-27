module

public import CFSG.RankThree.PartTwo.Sec21.Item233Res3ProofSmallL44
public import CFSG.RankThree.PartTwo.Sec21.Item233TablesSp64
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofZRoot

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

open Matrix CFSG.RankThree.PartTwo.KFacts.KS21 CFSG.RankThree.PartTwo.KFacts.KS21.Sp64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover (embedSp embedSp_injective)
open CFSG.RankThree.PartTwo.Sec21.Tables CFSG.RankThree.PartTwo.Sec21.TablesSp64
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSp)
open CFSG.Assembly.LowTwoRank

@[expose] def planeU₁ : Fin 3 → (Fin 3 → ZMod 3) := ![![1, 0, 0], ![1, 1, 0], ![1, 2, 0]]

@[expose] def planeU₂ : Fin 3 → (Fin 3 → ZMod 3) := ![![0, 1, 0], ![0, 0, 1], ![0, 1, 2]]

theorem exists_plane_std : ∀ x y : Fin 3 → ZMod 3, x ≠ 0 → y ≠ 0 → y ≠ x → y ≠ x + x →
    ∃ σ : Equiv.Perm (Fin 3), ∃ s : Fin 3 → Bool, ∃ i : Fin 3,
      (∃ a b : Fin 3, flipVec s (((a : ℕ) • x + (b : ℕ) • y) ∘ σ) = planeU₁ i) ∧
      (∃ c d : Fin 3, flipVec s (((c : ℕ) • x + (d : ℕ) • y) ∘ σ) = planeU₂ i) := by
  decide +kernel

@[expose] noncomputable def matS : Sp →* Mat6 := (Units.coeHom Mat6).comp (StatedSp 3 F4).subtype

theorem isIdOutside_of_isolated {v₁ v₂ : Fin 3 → ZMod 3} {P : Subgroup Sp}
    (hP : Group.IsPerfect P)
    (h₁ : P ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v₁)} : Set Sp))
    (h₂ : P ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd v₂)} : Set Sp))
    (c : Set (Fin 3 ⊕ Fin 3))
    (hc : ∀ k, k ∉ c → ∀ l, l ≠ k → ext v₁ k ≠ ext v₁ l ∨ ext v₂ k ≠ ext v₂ l) :
    ∀ g ∈ P, IsIdOutside c (mat g) := by
  have hz : ∀ g ∈ P, ∀ k l, (ext v₁ k ≠ ext v₁ l ∨ ext v₂ k ≠ ext v₂ l) → mat g k l = 0 := by
    intro g hg k l h
    rcases h with h | h
    · exact isBlockDiag_of_mem_centralizer (h₁ hg) k l h
    · exact isBlockDiag_of_mem_centralizer (h₂ hg) k l h
  have hdiag : ∀ k, k ∉ c → ∀ g ∈ P, mat g k k = 1 := fun k hk =>
    entry_eq_one_of_isPerfect matS hP k fun g hg l hl => hz g hg k l (hc k hk l hl)
  intro g hg i j hij
  by_cases hij' : i = j
  · subst hij'
    rw [Matrix.one_apply_eq]
    rcases hij with hi | hi <;> exact hdiag i hi g hg
  · rw [Matrix.one_apply_ne hij']
    rcases hij with hi | hj
    · exact hz g hg i j (hc i hi j (Ne.symm hij'))
    · refine hz g hg i j ?_
      rcases hc j hj i hij' with h | h
      · exact Or.inl (Ne.symm h)
      · exact Or.inr (Ne.symm h)

theorem card_SL_two_F4 : Nat.card (SpecialLinearGroup (Fin 2) F4) = 60 :=
  CFSG.RankThree.PartTwo.KFacts.KS21.L44.card_SL2

theorem card_le_sixty_std (i : Fin 3) {P : Subgroup Sp} (hP : Group.IsPerfect P)
    (h₁ : P ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd (planeU₁ i))} : Set Sp))
    (h₂ : P ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd (planeU₂ i))} : Set Sp)) :
    Nat.card P ≤ 60 := by
  fin_cases i
  ·
    have hle : P ≤ S2 := by
      intro g hg
      rw [mem_S2_iff]
      exact isIdOutside_of_isolated hP h₁ h₂ _ (by decide) g hg
    calc Nat.card P ≤ Nat.card S2 := Subgroup.card_le_of_le hle
      _ = Nat.card (StatedSp 1 F4) :=
        (Nat.card_congr (MonoidHom.ofInjective (embedSp_injective (K := F4)
          two_injective)).toEquiv).symm
      _ = 60 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, card_F4]
        decide
  ·
    have hC1 : P ≤ C1 := h₁
    have hId : ∀ g ∈ P, IsIdOutside c01 (mat g) :=
      isIdOutside_of_isolated hP h₁ h₂ _ (by decide)
    have hd : ∀ g : P, d2 (Subgroup.inclusion hC1 g) = 1 :=
      map_eq_one_of_isPerfect hP (d2.comp (Subgroup.inclusion hC1))
    have hle : P ≤ Levi2 := by
      intro g hg
      refine ⟨⟨⟨g, hC1 hg⟩, ?_, rfl⟩, hId g hg⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact Units.ext (hd ⟨g, hg⟩)
    calc Nat.card P ≤ Nat.card Levi2 := Subgroup.card_le_of_le hle
      _ = Nat.card rho01.range := by rw [Levi2_eq]
      _ = Nat.card (SpecialLinearGroup (Fin 2) F4) :=
        (Nat.card_congr (MonoidHom.ofInjective rho01_injective).toEquiv).symm
      _ = 60 := card_SL_two_F4
  ·
    have hId : ∀ g ∈ P, IsIdOutside ∅ (mat g) :=
      isIdOutside_of_isolated hP h₁ h₂ _ (by decide)
    have hle : P ≤ ⊥ := by
      intro g hg
      rw [Subgroup.mem_bot]
      apply mat_injective
      ext k l
      exact hId g hg k l (Or.inl (Set.notMem_empty k))
    calc Nat.card P ≤ Nat.card (⊥ : Subgroup Sp) := Subgroup.card_le_of_le hle
      _ ≤ 60 := by rw [Subgroup.card_bot]; norm_num

theorem card_le_sixty_Sp64 {B P : Subgroup Sp} (hBA : B ≤ A0) (hB9 : Nat.card B = 9)
    (hPC : P ≤ Subgroup.centralizer (B : Set Sp)) (hP : Group.IsPerfect P) :
    Nat.card P ≤ 60 := by
  obtain ⟨x, y, hxB, hyB, hx0, hy0, hyx, hyxx⟩ := exists_basis_of_card_nine δ hBA hB9
  obtain ⟨σ, s, i, ⟨a, b, hab⟩, ⟨c, d, hcd⟩⟩ := exists_plane_std x y hx0 hy0 hyx hyxx
  set φ : Sp ≃* Sp := (reindexSp (permE σ) (Jm_permE σ)).trans (reindexSp (flipE s) (Jm_flipE s))
  have hφ : ∀ v : Fin 3 → ZMod 3, φ (δ (Multiplicative.ofAdd v)) =
      δ (Multiplicative.ofAdd (flipVec s (v ∘ σ))) := by
    intro v
    change reindexSp (flipE s) (Jm_flipE s) (reindexSp (permE σ) (Jm_permE σ)
      (δ (Multiplicative.ofAdd v))) = _
    rw [reindexSp_δ _ (ext_comp_permE σ _), reindexSp_δ _ (ext_comp_flipE s _)]
  have hmem : ∀ p q : Fin 3, δ (Multiplicative.ofAdd ((p : ℕ) • x + (q : ℕ) • y)) ∈ B := by
    intro p q
    rw [ofAdd_add, map_mul, δ_nsmul, δ_nsmul]
    exact B.mul_mem (B.pow_mem hxB _) (B.pow_mem hyB _)
  have hcent : ∀ {p q : Fin 3} {u : Fin 3 → ZMod 3},
      flipVec s (((p : ℕ) • x + (q : ℕ) • y) ∘ σ) = u →
      P.map φ.toMonoidHom ≤ Subgroup.centralizer ({δ (Multiplicative.ofAdd u)} : Set Sp) := by
    intro p q u hu
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgw := Subgroup.mem_centralizer_iff.mp (hPC hg) _ (hmem p q)
    change φ g * δ (Multiplicative.ofAdd u) = δ (Multiplicative.ofAdd u) * φ g
    rw [← hu, ← hφ, ← map_mul, ← map_mul, hgw]
  let e : P ≃* P.map φ.toMonoidHom := Subgroup.equivMapOfInjective _ _ φ.injective
  have hP' : Group.IsPerfect (P.map φ.toMonoidHom) := by
    have := hP
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rw [Nat.card_congr e.toEquiv]
  exact card_le_sixty_std i hP' (hcent hab) (hcent hcd)

theorem terminalRootSmallSp64 {G : Type} [Group G] [Finite G] {I A B P : Subgroup G}
    (hAI : A ≤ I) (hAe : IsElemAbelian 3 A) (hA27 : Nat.card A = 3 ^ 3)
    (eI : I ≃* projSp 3 (GaloisField 2 2)) (hBA : B ≤ A) (hB9 : Nat.card B = 9) (hPI : P ≤ I)
    (hPB : P ≤ Subgroup.centralizer (B : Set G)) (hP : Group.IsPerfect P) :
    Nat.card P ≤ 60 := by
  set e' : I ≃* Sp := eI.trans equivSp
  have hA'e : IsElemAbelian 3 ((A.subgroupOf I).map e'.toMonoidHom) :=
    CFSG.RankThree.PartTwo.Sec21.isElemAbelian_map (isElemAbelian_subgroupOf hAe I) _
  have hcardA : Nat.card ((A.subgroupOf I).map e'.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAI).toEquiv, hA27]
  obtain ⟨x, hx⟩ := exists_map_conj_eq_A0 hA'e hcardA
  set φ : I ≃* Sp := e'.trans (MulAut.conj x)
  have hφA : (A.subgroupOf I).map φ.toMonoidHom = A0 := by
    rw [← hx, Subgroup.map_map]
    rfl
  exact card_le_of_model φ hφA hBA hAI hPI hPB hP hB9
    fun B' P' hB' hB'9 hP'C hP' => card_le_sixty_Sp64 hB' hB'9 hP'C hP'

end CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Assembly.RankThreeEven (projSL projSp)

theorem terminalRootSmall : TerminalRootSmall := by
  intro G _ _ I A B P hAI hAe hA27 hI hBA hB9 hPI hPB hP
  rcases hI with hI | hI
  · obtain ⟨eI⟩ := hI
    exact Item233Res3Proof.terminalRootSmallL44 hAI hAe hA27 eI hBA hB9 hPI hPB hP
  · obtain ⟨eI⟩ := hI
    exact Item233Res3Proof.terminalRootSmallSp64 hAI hAe hA27 eI hBA hB9 hPI hPB hP

end CFSG.RankThree.PartTwo.Sec21
