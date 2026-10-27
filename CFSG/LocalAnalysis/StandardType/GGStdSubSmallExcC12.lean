module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC12Core
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthBstar
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE6

public section

namespace CFSG.StandardType.SmallExcC12

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggStdSubTwoTorusEltInnerSmall_of_nonCentralAt {p r : ℕ} {R : Type} [Group R]
    (h : ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → NonCentralAt A) :
    GGStdSubTwoTorusEltInnerSmall p r R :=
  fun A hA hr _ a ha _ D hD hn hq _ _ => h A hA hr a ha D hD hn hq

section Recipe


theorem ggStdSubTwoTorusEltInnerSmall_of_toral {τ : Tag} {K : Type} [Field K] [Finite K]
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) {R : Type} [Group R]
    (e : R ≃* adjointGroup τ K) {V : Subgroup (adjointGroup τ K)}
    (hV : ∀ g, g ∈ V ↔ (g : ModGL τ K) ∈ torusGroup τ K ∧ g ^ p = 1)
    (hT : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ r ≤ Nat.card E →
      ∃ g : adjointGroup τ K, E.map (MulAut.conj g).toMonoidHom = V) :
    GGStdSubTwoTorusEltInnerSmall p r R := by
  have := Fact.mk hp
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  have hζp : ζ ^ p = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
    (by rw [← hζ]; exact orderOf_dvd_of_pow_eq_one h2))
  refine ggStdSubTwoTorusEltInnerSmall_of_nonCentralAt fun A hA hr => ?_
  obtain ⟨g, hg⟩ := hT (A.map e.toMonoidHom) (TableB.isElemAbelian_map hA _)
    (by rw [Subgroup.card_map_of_injective e.injective]; exact hr)
  refine nonCentralAt_of_mulEquiv (e.trans (MulAut.conj g)) ?_
  have hmap : A.map (e.trans (MulAut.conj g)).toMonoidHom = V := by
    rw [← hg, Subgroup.map_map]
    rfl
  rw [hmap]
  exact nonCentralAt_torusPow τ hp hζ2 hζp hV

theorem ggStdSubTwoTorusEltInnerSmall_E7E8 {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGStdSubTwoTorusEltInnerSmall p τ.rank (TableBExc.RecipeGroup τ K) :=
  ggStdSubTwoTorusEltInnerSmall_of_toral hp hp2 hpq (TableBExc.recipeEquiv τ K)
    (fun _ => TableBExc.mem_torusPow) (IOneRest.ggExcToralRankInput_E7E8 hτ hp hp2 hpq)

theorem ggStdSubTwoTorusEltInnerSmall_F4 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) :
    GGStdSubTwoTorusEltInnerSmall p 4 (TableBF4.RecipeGroup K) := by
  have hT : GGF4ToralRankInput K p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBF4.ggF4ToralRankInput_three hpq
    · have h5 : 5 ≤ p := by
        have := hp.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · subst h
          exact absurd hp (by decide)
        · exact h
      exact TableBF4.ggF4ToralRankInput_of_five_le hp h5 hpq
  exact ggStdSubTwoTorusEltInnerSmall_of_toral hp hp2 hpq (TableBF4.recipeEquiv K)
    (fun _ => TableBF4.mem_torusPow) hT

theorem ggStdSubTwoTorusEltInnerSmall_E6 {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hpq : p ∣ Nat.card K - 1) :
    GGStdSubTwoTorusEltInnerSmall p 6 (TableBExc.RecipeGroup .E6 K) :=
  ggStdSubTwoTorusEltInnerSmall_of_toral hp hp2 hpq (TableBExc.recipeEquiv .E6 K)
    (fun _ => TableBExc.mem_torusPow) (TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpq)

end Recipe

section ExcSplit


theorem largeEvenLabelAll_innerSmall_excTag {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4)
    (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with rfl | rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢ <;>
    obtain ⟨K, i1, i2, hK, hq⟩ := hQ <;>
    have : CharP K 2 := charP_two_of_card hK <;>
    have hpq : p ∣ Nat.card K - 1 := (by rw [hK]; exact hpn)
  · exact ⟨K, i1, i2, hK, hq, 7, TableBExc.ggTorusLift_E7 hp hp2 hpq,
      ggStdSubTwoTorusInnerSmall_of_elt hp (fun _ hφ _ => TableBExc.idImage_subset_inn_E7 K hφ)
        (TableBExc.center_recipeGroup_eq_bot .E7 K)
        (ExcSplitL.ggCenterPrime_recipe_E7 hn hK hp hp2)
        (ggStdSubTwoTorusEltInnerSmall_E7E8 (τ := .E7) (Or.inl rfl) hp hp2 hpq)⟩
  · exact ⟨K, i1, i2, hK, hq, 8, TableBExc.ggTorusLift_E8 hp hp2 hpq,
      ggStdSubTwoTorusInnerSmall_of_elt hp (fun _ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
        (TableBExc.center_recipeGroup_eq_bot .E8 K) (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2)
        (ggStdSubTwoTorusEltInnerSmall_E7E8 (τ := .E8) (Or.inr rfl) hp hp2 hpq)⟩
  · exact ⟨K, i1, i2, hK, hq, 4, TableBF4.ggTorusLift_F4 hp hp2 hpq,
      ggStdSubTwoTorusInnerSmall_of_elt hp (fun _ hφ _ => TableBF4.idImage_subset_inn K hφ)
        (TableBF4.center_recipeGroup_eq_bot K) (ExcSplitL.ggCenterPrime_recipe_F4 hp hp2)
        (ggStdSubTwoTorusEltInnerSmall_F4 hp hp2 hpq)⟩

theorem largeEvenLabelAll_innerSmall_excSplit {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneExcSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I :=
  largeEvenLabelAll_innerSmall_excTag hp hlab h.1 h.2.1

theorem largeEvenLabelAll_excSplit_innerSmall {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneExcSplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ((∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I :=
  largeEvenLabelAll_and ((largeEvenLabelAll_bstarEq_excSplit hp hlab h).mono
    fun _ _ _ _ ⟨hb, r, hr, hrk⟩ => ⟨hb, r, hr, ggINormAbove_of_iRankLe hp.one_lt hrk⟩)
    (largeEvenLabelAll_innerSmall_excSplit hp hlab h)

theorem ggStdSubSmallInputOn_excSplit : GGStdSubSmallInputOn GGIOneExcSplitLabel :=
  ggStdSubSmallInputOn_of_labels_innerSmall ggLNoncyclicInput_holds fun _ _ hp hlab h _ =>
    largeEvenLabelAll_excSplit_innerSmall hp hlab h

end ExcSplit

section E6Coprime


theorem largeEvenLabelAll_innerSmall_e6Tag {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E6) (hpn : p ∣ 2 ^ lab.n - 1)
    (hp3 : p ≠ 3) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, i1, i2, hK, hq, 6, TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq,
    ggStdSubTwoTorusInnerSmall_of_elt hp (TableBExc.ggOutdiagPrime_E6 hp hp3)
      (TableBExc.center_recipeGroup_eq_bot .E6 K) (ExcSplitL.ggCenterPrime_recipe_E6 hp hp2 hp3)
      (ggStdSubTwoTorusEltInnerSmall_E6 hp hp2 hp3 hpq)⟩

theorem largeEvenLabelAll_innerSmall_e6Coprime {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreE6CoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I :=
  largeEvenLabelAll_innerSmall_e6Tag hp hlab h.1 h.2.1 h.2.2.1

theorem largeEvenLabelAll_e6Coprime_innerSmall {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGIOneMoreE6CoprimeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ((∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I) ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorusInnerSmall p r R I :=
  largeEvenLabelAll_and ((largeEvenLabelAll_bstarEq_e6Coprime hp hlab h).mono
    fun _ _ _ _ ⟨hb, r, hr, hrk⟩ => ⟨hb, r, hr, ggINormAbove_of_iRankLe hp.one_lt hrk⟩)
    (largeEvenLabelAll_innerSmall_e6Coprime hp hlab h)

theorem ggStdSubSmallInputOn_e6Coprime : GGStdSubSmallInputOn GGIOneMoreE6CoprimeLabel :=
  ggStdSubSmallInputOn_of_labels_innerSmall ggLNoncyclicInput_holds fun _ _ hp hlab h _ =>
    largeEvenLabelAll_e6Coprime_innerSmall hp hlab h

end E6Coprime

end CFSG.StandardType.SmallExcC12

end
