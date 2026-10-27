module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuCases
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.A38c15Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuPerf

public section

namespace CFSG.Quasithin.A312U3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.A38c15
open CFSG.Quasithin.A312Ru (nonabelian_of_simple)

theorem exists_hom_alt6_of_isHat {K : Type} [Group K]
    (h : IsHat K (alternatingGroup (Fin 6))) :
    ∃ f : K →* alternatingGroup (Fin 6), Function.Surjective f ∧ Group.IsSolvable f.ker := by
  obtain ⟨-, -, ⟨φ⟩⟩ := h
  refine ⟨φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)),
    φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  have hker : (φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker =
      Subgroup.center K := by
    ext x
    simp
  rw [hker]
  exact Group.isSolvable_of_comm fun a b => Subtype.ext
    ((Subgroup.mem_center_iff.mp b.2) a.1)

theorem alt6_nonabelian : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  exact nonabelian_of_simple (by rw [hcard]; norm_num)

theorem lFamily_block {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {blocks : ∀ (K : Type) [Group K], Prop}
    (hblk : ∀ (K : Type) [Group K], blocks K → ∃ f : K →* alternatingGroup (Fin 6),
      Function.Surjective f ∧ Group.IsSolvable f.ker)
    (hc : ∀ M : Subgroup X, Odd M.index → M ≠ ⊤ →
      Group.IsSolvable ↥M ∨ IsSL2 p ↥(perfectCore M) ∨ blocks ↥(perfectCore M))
    {T B : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hBtop : B ≠ ⊤) :
    B = perfectCore (B ⊔ T) ∧
      ((IsSL2 p ↥(perfectCore (B ⊔ T)) ∧ 3 < p) ∨ blocks ↥(perfectCore (B ⊔ T))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hB' : B ∈ cComp (B ⊔ T) := hB
  have hMne : B ⊔ T ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hodd : Odd (B ⊔ T).index := odd_index_of_le_isSylowTwoOf hT le_sup_right
  rcases hc (B ⊔ T) hodd hMne with hsolv | hSL | hbl
  · exfalso
    exact not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T))
        (Subgroup.inclusion_injective _))
  · have hperf : Group.IsPerfect ↥(perfectCore (B ⊔ T)) :=
      Subgroup.isPerfect_iff.mpr (perfectCore_perfect (B ⊔ T))
    have hLevi : IsLeviBlock p ↥(perfectCore (B ⊔ T)) := Or.inl hSL
    have hp3 : p ≠ 3 := ne_three_of_leviBlock hLevi
    have hp5 : 3 < p := by
      have := hp.two_le
      omega
    obtain ⟨f, hf, hker⟩ := exists_hom_psl2_of_leviBlock hLevi
    have hS : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2
        (ZMod p) le_rfl (Or.inr (by rw [Nat.card_zmod]; omega))
        (Or.inr (by rw [Nat.card_zmod]; omega))
    have hnab : ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p), a * b ≠ b * a :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        (ZMod p) (by rw [Nat.card_zmod]; omega) (by rw [Nat.card_zmod]; omega)
    exact ⟨lFamily_eq_perfectCore hB hnab f hf hker, Or.inl ⟨hSL, hp5⟩⟩
  · obtain ⟨f, hf, hker⟩ := hblk _ hbl
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact ⟨lFamily_eq_perfectCore hB alt6_nonabelian f hf hker, Or.inr hbl⟩

end CFSG.Quasithin.A312U3
