module

public import CFSG.Quasithin.H13.StatementsL4
public import CFSG.Quasithin.Background.B1MoreNineD
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

@[expose] def List325Three (T L I : Subgroup G) : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
    (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L (fsuV T I)) ≃* ↥(StatedSp 2 K))) ∨
    Nonempty (↥(autOn L (fsuV T I)) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (↥(autOn L (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
    Nonempty (↥(autOn L (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
    Nonempty (↥(autOn L (fsuV T I)) ≃* alternatingGroup (Fin 7))

@[expose] def Type328 (T L V : Subgroup G) : Prop :=
  (∃ n : ℕ, LieModel ↥(autOn L V) .PSL 2 2 n) ∨
    (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) K)) ∨
    Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
    (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* ↥(StatedSp 2 K))) ∨
    (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn L V) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆)) ∨
    Nonempty (↥(autOn L V) ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (↥(autOn L V) ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (↥(autOn L V) ≃* alternatingGroup (Fin 6)) ∨
    Nonempty (↥(autOn (L ⊔ T) V) ≃* alternatingGroup (Fin 7)) ∨
    (Group.IsPerfect ↥(autOn L V) ∧ Nat.card (Subgroup.center ↥(autOn L V)) = 3 ∧
      Nonempty (↥(autOn L V) ⧸ Subgroup.center ↥(autOn L V) ≃* alternatingGroup (Fin 6))) ∨
    (∃ n : ℕ, (n = 4 ∨ n = 5) ∧
      Nonempty (↥(autOn (L ⊔ T) V) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) ∨
    Nonempty (↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))

theorem type328_of (h328 : Stmt3_2_8) {T L V : Subgroup G} (hfsu : FSU G T L V)
    (hL : L = conjClosure L T) (hV : V = conjClosure V T) [IsMulCommutative ↥V]
    (hFF : IsFFModule (V := ↥V) (Subgroup.normalizer (autOn L V : Set (MulAut ↥V)))) :
    Type328 T L V := by
  obtain ⟨_, h⟩ := h328 G T L V hfsu hL hV ⟨inferInstance, hFF⟩
  unfold Type328
  rcases h with ⟨n, h1, -⟩ | (⟨n, K, _, _, hK, e, -⟩ | ⟨e, -, -⟩) | ⟨n, K, _, _, hK, e, -⟩ |
      ⟨n, K, _, _, hK, e, -⟩ | (⟨e, -⟩ | ⟨e, -⟩) | ⟨e, -⟩ | ⟨e, -⟩ | ⟨hp, hc, e, -⟩ |
      ⟨n, hn, e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact Or.inl ⟨n, h1⟩
  · exact Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, hK, e⟩)
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, hK, e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, hK, e⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))))
  · iterate 8 right
    exact Or.inl e
  · iterate 9 right
    exact Or.inl ⟨hp, hc, e⟩
  · iterate 10 right
    exact Or.inl ⟨n, hn, e⟩
  · iterate 11 right
    exact e
  · iterate 10 right
    exact Or.inl ⟨5, Or.inr rfl, e⟩

theorem concl701FF_list (h325 : Stmt3_2_5) (h328 : Stmt3_2_8) {T L I : Subgroup G}
    (hfsu : FSU G T L I) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    [IsMulCommutative ↥(fsuV T I)] (hFF : Concl701FF T L I) :
    List325Three T L I ∨ (fsuV T I = I ∧ Type328 T L (fsuV T I)) := by
  have hL0 : fsuL0 T L = L :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTL ht) l).1 hl)
      (le_conjClosure L T)
  have hL : L = conjClosure L T := hL0.symm
  obtain ⟨A, hA⟩ := hFF
  have hff : IsFFModule (V := ↥(fsuV T I))
      (Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I)))) := by
    have := isFFModule_of_offender hA
    rwa [hL0] at this
  have key : fsuV T I = I → Type328 T L (fsuV T I) := by
    intro hVI
    have hfsu' : FSU G T L (fsuV T I) := by rw [hVI]; exact hfsu
    have hV0 : fsuV T I = conjClosure (fsuV T I) T := by rw [hVI]; exact hVI.symm
    exact type328_of h328 hfsu' hL hV0 hff
  rcases (h325 G T L I hfsu hL).2.2 with ⟨hV, -⟩ | ⟨hV, -⟩ | ⟨-, htype, -⟩
  · exact Or.inr ⟨hV.symm, key hV.symm⟩
  · exact Or.inr ⟨hV.symm, key hV.symm⟩
  · left
    rcases htype with ⟨n, K, _, _, hK, e, -⟩ | ⟨n, K, _, _, hK, e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ |
        ⟨e, -⟩
    · exact Or.inl ⟨n, K, inferInstance, inferInstance, hK, e⟩
    · exact Or.inr (Or.inl ⟨n, K, inferInstance, inferInstance, hK, e⟩)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))

end CFSG.Quasithin.Vol2.Ch11.SecS
