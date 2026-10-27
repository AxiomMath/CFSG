module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem lieModel_of_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {t} {n p f : ℕ}
    (h : LieModel Y t n p f) : LieModel X t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e.symm h

theorem threeA6_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Group.IsPerfect X ∧ Nat.card (Subgroup.center X) = 3 ∧
      Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))) :
    Group.IsPerfect Y ∧ Nat.card (Subgroup.center Y) = 3 ∧
      Nonempty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hp, hc, ⟨f⟩⟩ := h
  have hZ : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := Subgroup.map_center_eq e
  refine ⟨?_, ?_, ⟨(QuotientGroup.congr _ _ e hZ).symm.trans f⟩⟩
  · rw [Group.isPerfect_def, _root_.commutator_def] at hp ⊢
    rw [← Subgroup.map_top_of_surjective (e : X →* Y) e.surjective, ← Subgroup.map_commutator, hp]
  · rw [← hZ, Subgroup.card_map_of_injective e.injective, hc]

theorem shape443_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : Shape443 X) :
    Shape443 Y := by
  rcases h with ⟨n, hn, h⟩ | h | h | f | f | h | h
  · exact Or.inl ⟨n, hn, lieModel_of_mulEquiv' e.symm h⟩
  · exact Or.inr (Or.inl (lieModel_of_mulEquiv' e.symm h))
  · exact Or.inr (Or.inr (Or.inl (lieModel_of_mulEquiv' e.symm h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (f.map fun g => e.symm.trans g))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (f.map fun g => e.symm.trans g)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (threeA6_of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (lieModel_of_mulEquiv' e.symm h))))))

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem VB_le_centralizer_pCoreOf_Mp (s : Setting443 G T M L B Tp VB) :
    pCoreOf 2 (conjClosure L T) ≤ Subgroup.centralizer (VB : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCoreOf 2 (conjClosure L T) ≤ pCoreOf 2 (conjClosure L T ⊔ T) := by
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 _).trans le_sup_left) ?_ (pCoreOf_isPGroup 2 _)
    exact sup_le (le_normalizer_pCoreOf 2 _)
      ((le_normalizer_conjClosure L T).trans (normalizer_le_normalizer_pCoreOf 2 _))
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp
    (mem_quasithinOmegaOneCenter_iff.mp (s.hyp.VB_le hv)).2.1 q (hO2 hq)).symm

end CFSG.Quasithin.H13.Ch4.E443
