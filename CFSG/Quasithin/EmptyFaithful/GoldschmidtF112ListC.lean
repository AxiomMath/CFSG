module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112Slice

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Lists

variable {G : Type} [Group G]

@[expose] def F112ListC (L1 L2 S : Subgroup G) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .PSL 3 f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 4)) ∧
          Nonempty (↥(L2 ⊔ S) ≃* Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsSp4Over f) ∧
      ((2 ≤ f ∧ IsBlock2 L1 L1 ∧ IsLin2Type L1 f ∧ IsBlock2 L2 L2 ∧ IsLin2Type L2 f) ∨
        (f = 1 ∧ Nonempty (↥(L1 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
          Nonempty (↥(L2 ⊔ S) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))))) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsG2Over f) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsL2Quot f (oTwoQuot ↥L2) ∧
      IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 5) ∨
  (∃ f : ℕ, 1 ≤ f ∧ IsAmalgamOfGroup α (IsLieOverTwo .trialityD4 0 f) ∧
      IsL2Quot (3 * f) (oTwoQuot ↥L1) ∧
      IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot f (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 11) ∨
  (∃ a : ℕ, IsAmalgamOfGroup α (IsTwistedF4Over (2 * a + 1)) ∧
      (Nonempty (oTwoQuot ↥L1 ≃* Sz a) ∨ (a = 0 ∧ Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5))) ∧
      Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10 ∧
      IsL2Quot (2 * a + 1) (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 11) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (IsAmalgamOfGroup α (IsLieOverTwo .PSU 4 f) ∨ IsU4ExtTwo f α) ∧
      IsL2Quot f (oTwoQuot ↥L1) ∧ IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsBlock2 L2 L2 ∧ IsL2Quot (2 * f) (oTwoQuot ↥L2) ∧
      IsOmega4MinusType L2 f ∧ (f = 1 → IsAltType L2 5)) ∨
  (IsAmalgamOfGroup α (IsLieOverTwo .PSU 5 2) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ^ 2 ∧
        Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.StatedSU 3 4 F)) ∧
      IsSpecialPow 2 4 3 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧ IsL2Quot 4 (oTwoQuot ↥L2) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 16) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* PSU3 3 1)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsL2Quot 1 (oTwoQuot ↥L2) ∧
      IsZ4StarQ8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧ IsZ4Sq ↥(pCoreOf 2 (L2 ⊔ bigB L1 L2 S))) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinTits)) ∧
      (Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L1 ≃* ↥(Sz 0))) ∧
      Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = 2 ^ 9 ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 10) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinJ2)) ∧
      IsL2Quot 2 (oTwoQuot ↥L1) ∧ IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6) ∨
  (IsParabolicAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinJ2)) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* Equiv.Perm (Fin 5)) ∧
      IsQ8D8 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      Nonempty (oTwoQuot ↥L2 ≃* Equiv.Perm (Fin 3)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsQ8Sq ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 5) ∨
  (IsAmalgamOfGroup α (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)) ∧
      IsL2Quot 1 (oTwoQuot ↥L1) ∧ IsAutM12Vertex (L1 ⊔ bigB L1 L2 S) ∧
      IsL2Quot 1 (oTwoQuot ↥L2) ∧ Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = 2 ^ 6)

@[expose] def F112ConclC (L1 L2 S : Subgroup G) : Prop :=
  ∃ L1' L2' : Subgroup G, ((L1' = L1 ∧ L2' = L2) ∨ (L1' = L2 ∧ L2' = L1)) ∧
    (centerOf S ≤ Subgroup.centralizer (L1 : Set G) ∨
        centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1' : Set G)) ∧
    F112ListC L1' L2' S ∧ F112Second L1' L2' S

theorem F112ConclC.symm {L1 L2 S : Subgroup G} (h : F112ConclC L1 L2 S) : F112ConclC L2 L1 S := by
  obtain ⟨L1', L2', hsw, hZ, hl, h2⟩ := h
  exact ⟨L1', L2', hsw.symm, fun hc => hZ hc.symm, hl, h2⟩

theorem f112ConclC_comm {L1 L2 S : Subgroup G} : F112ConclC L1 L2 S ↔ F112ConclC L2 L1 S :=
  ⟨F112ConclC.symm, F112ConclC.symm⟩

theorem F112ListC.toListLegacyBare {L1 L2 S : Subgroup G} (h1 : L1 ⊔ S = L1) (h2 : L2 ⊔ S = L2)
    (hB : bigB L1 L2 S = S)
    (hD : Nonempty (oTwoQuot ↥L1 ≃* DihedralGroup 5) → Nat.card (pCoreOf 2 L1) = 2 ^ 10 →
      Nat.card (pCoreOf 2 L2) = 2 ^ 11 → False)
    (h : F112ListC L1 L2 S) : F112ListBare L1 L2 S := by
  have e1 : pCoreOf 2 (L1 ⊔ S) = pCoreOf 2 L1 := by rw [h1]
  have e2 : pCoreOf 2 (L2 ⊔ S) = pCoreOf 2 L2 := by rw [h2]
  unfold F112ListC at h
  unfold F112ListBare
  dsimp only at h ⊢
  rw [hB, e1, e2] at h
  rw [hB, e1, e2]
  rcases h with ⟨f, hf, hA, hb | ⟨rfl, ⟨i1⟩, ⟨i2⟩⟩⟩ | h | h | h |
    ⟨a, hA, hq | ⟨rfl, hd⟩, hc1, hq2, hc2⟩ | h | h | h | h | h | h | h | ⟨hA, hq1, hV, hq2, hc2⟩
  · exact Or.inl ⟨f, hf, hA, Or.inl hb⟩
  · exact Or.inl ⟨1, hf, hA, Or.inr ⟨rfl, ⟨(MulEquiv.subgroupCongr h1.symm).trans i1⟩,
      ⟨(MulEquiv.subgroupCongr h2.symm).trans i2⟩⟩⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, hA, hq, hc1, hq2, hc2⟩))))
  · exact (hD hd (by simpa using hc1) (by simpa using hc2)).elim
  · iterate 5 right
    exact Or.inl h
  · iterate 6 right
    exact Or.inl h
  · iterate 7 right
    exact Or.inl h
  · iterate 8 right
    exact Or.inl h
  · iterate 9 right
    exact Or.inl h
  · iterate 10 right
    exact Or.inl h
  · iterate 11 right
    exact Or.inl h
  · rw [h1] at hV
    iterate 12 right
    exact ⟨hA, hq1, hV, hq2, hc2⟩

theorem F112ListBare.toListC {L1 L2 S : Subgroup G} (h1 : L1 ⊔ S = L1) (h2 : L2 ⊔ S = L2)
    (hB : bigB L1 L2 S = S) (h : F112ListBare L1 L2 S) : F112ListC L1 L2 S := by
  have e1 : pCoreOf 2 (L1 ⊔ S) = pCoreOf 2 L1 := by rw [h1]
  have e2 : pCoreOf 2 (L2 ⊔ S) = pCoreOf 2 L2 := by rw [h2]
  unfold F112ListBare at h
  unfold F112ListC
  dsimp only at h ⊢
  rw [hB, e1, e2] at h
  rw [hB, e1, e2]
  rcases h with ⟨f, hf, hA, hb | ⟨rfl, ⟨i1⟩, ⟨i2⟩⟩⟩ | h | h | h | ⟨a, hA, hq, hc1, hq2, hc2⟩ |
    h | h | h | h | h | h | h | ⟨hA, hq1, hV, hq2, hc2⟩
  · exact Or.inl ⟨f, hf, hA, Or.inl hb⟩
  · exact Or.inl ⟨1, hf, hA, Or.inr ⟨rfl, ⟨(MulEquiv.subgroupCongr h1).trans i1⟩,
      ⟨(MulEquiv.subgroupCongr h2).trans i2⟩⟩⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, hA, Or.inl hq, hc1, hq2, hc2⟩))))
  · iterate 5 right
    exact Or.inl h
  · iterate 6 right
    exact Or.inl h
  · iterate 7 right
    exact Or.inl h
  · iterate 8 right
    exact Or.inl h
  · iterate 9 right
    exact Or.inl h
  · iterate 10 right
    exact Or.inl h
  · iterate 11 right
    exact Or.inl h
  · rw [← h1] at hV
    iterate 12 right
    exact ⟨hA, hq1, hV, hq2, hc2⟩


theorem f112List_iff_listC (L1 L2 S : Subgroup G) :
    F112List L1 L2 S ↔ F112ListC L1 L2 S := Iff.rfl

end Lists

@[expose] def F112ConclPredC : F112Conc :=
  fun _ _ _ L1 L2 S => F112ConclC L1 L2 S

@[expose] def F112StatementC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112Hyp L1 L2 S → F112ConclC L1 L2 S

theorem f112Statement_iff_corrected : F112Statement ↔ F112StatementC := Iff.rfl

theorem f112StatementC_of_slices (hss : F112SliceSS F112ConclPredC)
    (htits : F112SliceTits F112ConclPredC) (hs3 : F112SliceS3Big F112ConclPredC)
    (hfd : F112SliceFDBig) (hbig : F112SliceBig F112ConclPredC) (hex : F112SliceExotic) :
    F112StatementC :=
  fun G _ _ L1 L2 S h => f112_of_slices hss htits hs3 hfd hbig hex G L1 L2 S h

theorem f112Statement_of_corrected_slices (hss : F112SliceSS F112ConclPredC)
    (htits : F112SliceTits F112ConclPredC) (hs3 : F112SliceS3Big F112ConclPredC)
    (hfd : F112SliceFDBig) (hbig : F112SliceBig F112ConclPredC) (hex : F112SliceExotic) :
    F112Statement :=
  f112StatementC_of_slices hss htits hs3 hfd hbig hex

end CFSG.Quasithin
