module

public import CFSG.Quasithin.Background.F918Fine4PfHat6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Blueprint

@[expose] def IsBenderGroupU (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, LieModel X .PSL 2 2 n) ∨ (∃ n : ℕ, LieModel X .PSU 3 2 n) ∨
    ∃ n : ℕ, LieModel X .twistedB2 0 2 n

@[expose] def IsF918FourListU (Ks : Type) [Group Ks] : Prop :=
  IsBenderGroupU (Ks ⧸ Subgroup.center Ks) ∨
    (∃ n : ℕ, LieModel (Ks ⧸ Subgroup.center Ks) .PSL 3 2 n) ∨
    (Nonempty ((Ks ⧸ Subgroup.center Ks) ≃* alternatingGroup (Fin 6))) ∨
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (Ks ⧸ Subgroup.center Ks) .PSp 2 2 n) ∨
    LieModel (Ks ⧸ Subgroup.center Ks) .PSU 3 3 1 ∨
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (Ks ⧸ Subgroup.center Ks) .G2 0 2 n) ∨
    LieModel (Ks ⧸ Subgroup.center Ks) .PSL 4 2 1 ∨ LieModel (Ks ⧸ Subgroup.center Ks) .PSL 5 2 1 ∨
    (Nonempty ((Ks ⧸ Subgroup.center Ks) ≃* alternatingGroup (Fin 7)) ∧
      Nat.card (Subgroup.center Ks) ≠ 3) ∨
    Nonempty (Ks ≃* ↥CFSG.Blueprint.NativeSporadic.M22) ∨
    (Group.IsPerfect Ks ∧ Nat.card (Subgroup.center Ks) = 3 ∧
      Nonempty ((Ks ⧸ Subgroup.center Ks) ≃* ↥CFSG.Blueprint.NativeSporadic.M22))

theorem lieModel_of_isPSL {X : Type} [Group X] {n p e : ℕ} (h : IsPSL n p e X) :
    LieModel X .PSL n p e := Or.inl ⟨by decide, h⟩

theorem lieModel_of_isPSU {X : Type} [Group X] {n p e : ℕ} (h : IsPSU n p e X) :
    LieModel X .PSU n p e := Or.inl ⟨by decide, h⟩

theorem lieModel_of_isPSp4 {X : Type} [Group X] {p e : ℕ} (h : IsPSp4 p e X) :
    LieModel X .PSp 2 p e := Or.inl ⟨by decide, h⟩

theorem lieModel_of_isSz {X : Type} [Group X] {e : ℕ} (h : IsSz e X) :
    LieModel X .twistedB2 0 2 e := Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩))

theorem lieModel_of_isG2 {X : Type} [Group X] {p e : ℕ} (h : IsG2 p e X) :
    LieModel X .G2 0 p e := Or.inr (Or.inl ⟨rfl, by decide, h⟩)

section Kstar

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem isQuasisimple_autIH (h : HypF918 T V L V₁ Vp H K) :
    CFSG.IsQuasisimple ↥(autIH V₁ Vp H K) := by
  have hker := F918Fine4Pf.ker_toAutI_eq_pCore h
  have e : ↥K ⧸ (toAutI h Vp).ker ≃* ↥(autIH V₁ Vp H K) :=
    QuotientGroup.quotientKerEquivOfSurjective (toAutI h Vp) (toAutI_surjective h Vp)
  have hq : CFSG.IsQuasisimple (↥K ⧸ (pCoreOf 2 K).subgroupOf K) := h.K_quasisimple
  have e2 : ↥K ⧸ (toAutI h Vp).ker ≃* ↥K ⧸ (pCoreOf 2 K).subgroupOf K :=
    QuotientGroup.quotientMulEquivOfEq (hker.trans
      (Subgroup.comap_map_eq_self_of_injective K.subtype_injective (CFSG.pCore 2 ↥K)).symm)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e2.symm.trans e) hq


theorem isF918FourListU_of_fourListFine {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (hF : FourListFine X) : IsF918FourListU X := by
  obtain ⟨hL, hA7, hM⟩ := hF
  unfold IsF918FourListU IsBenderGroupU
  rcases hL with ⟨n, -, h | h | h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | ⟨n, hn, h⟩ | h | h | h | h | h
  · exact Or.inl (Or.inl ⟨n, lieModel_of_isPSL h⟩)
  · exact Or.inl (Or.inr (Or.inr ⟨n, lieModel_of_isSz h⟩))
  · exact Or.inl (Or.inr (Or.inl ⟨n, lieModel_of_isPSU h⟩))
  · right; left; exact ⟨n, lieModel_of_isPSL h⟩
  · iterate 3 right
    left
    exact ⟨n, hn, lieModel_of_isPSp4 h⟩
  · iterate 2 right
    left
    exact h
  · iterate 5 right
    left
    exact ⟨n, hn, lieModel_of_isG2 h⟩
  · iterate 4 right
    left
    exact lieModel_of_isPSU h
  · iterate 6 right
    left
    exact lieModel_of_isPSL h
  · iterate 7 right
    left
    exact lieModel_of_isPSL h
  · iterate 8 right
    left
    refine ⟨h, fun h3 => hA7 h ?_⟩
    obtain ⟨e⟩ := h
    exact ⟨hq, h3, ⟨e⟩⟩
  · rcases hM h with hM1 | hM2
    · iterate 9 right
      left
      exact hM1
    · obtain ⟨hq', hZ, ⟨e⟩⟩ := hM2
      iterate 10 right
      exact ⟨hq'.1, hZ, ⟨e⟩⟩

end Kstar

end CFSG.Quasithin.RonanF918
