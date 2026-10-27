module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2LU4Weyl
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherExcFixG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestCenter
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGNbrLangNorm
public import CFSG.LieType.Steinberg.CentralExt.G2FourMultiplier
public import CFSG.RankThree.Chevalley.G2SplitPrimeToralCentralizers

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.CentralCover

theorem cartan_G2_entry_cases_rowTwo (i j : Fin Tag.G2.rank) :
    Tag.G2.cartan i j = 2 ∨ Tag.G2.cartan i j = -1 ∨ Tag.G2.cartan i j = -3 := by
  rcases CFSG.RankThree.Chevalley.fin_G2_cases i with rfl | rfl <;> revert j <;> decide

theorem cartan_G2_connected_rowTwo (S : Finset (Fin Tag.G2.rank)) (hS : S.Nonempty)
    (hcl : ∀ i ∈ S, ∀ j, Tag.G2.cartan i j ≠ 0 → j ∈ S) : S = Finset.univ := by
  have hoff : ∀ i j : Fin Tag.G2.rank, i ≠ j → Tag.G2.cartan i j ≠ 0 := by
    intro i
    rcases CFSG.RankThree.Chevalley.fin_G2_cases i with rfl | rfl <;> decide
  obtain ⟨i, hi⟩ := hS
  rw [Finset.eq_univ_iff_forall]
  intro j
  by_cases hij : i = j
  · exact hij ▸ hi
  · exact hcl i hi j (hoff i j hij)

theorem cartan_G2_entry_ne_zero_rowTwo {p : ℕ} (hp5 : 5 ≤ p) (i j : Fin Tag.G2.rank)
    (_ : Tag.G2.cartan i j ≠ 0) : ((Tag.G2.cartan i j : ℤ) : ZMod p) ≠ 0 := by
  have hn : ∀ m : ℕ, 0 < m → m < p → ((m : ℤ) : ZMod p) ≠ 0 := by
    intro m hm hmp h
    rw [Int.cast_natCast, ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hm h) (by omega)
  rcases cartan_G2_entry_cases_rowTwo i j with h | h | h <;> rw [h]
  · exact_mod_cast hn 2 (by norm_num) (by omega)
  · rw [Int.cast_neg]
    exact neg_ne_zero.mpr (by exact_mod_cast hn 1 (by norm_num) (by omega))
  · rw [Int.cast_neg]
    exact neg_ne_zero.mpr (by exact_mod_cast hn 3 (by norm_num) (by omega))

section G2

variable {K : Type} [Field K]

theorem ggExcToralRankInput_G2_of_five_le [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) : GGExcToralRankInput .G2 K p :=
  TableBExc.ggExcToralRankInput_of_not_dvd_index hp
    (CFSG.RankThree.Chevalley.not_dvd_index_torusGroup_G2 hp (by omega) hpq)
    (TableBExc.card_torusPow_G2 hp hpq)

theorem ggWeylIrred_adjoint_G2_of_five_le [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) {E : Subgroup (adjointGroup .G2 K)}
    (hE : IsElemAbelian p E) (hcard : p ^ 2 ≤ Nat.card E) : GGWeylIrred E := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  have hdet : IsUnit ((Tag.G2.cartan.det : ℤ) : ZMod p) :=
    TableBExc.isUnit_det_cartan_of_eq hp det_cartan_G2 (Nat.coprime_one_left p)
  have hV := TableBExc.card_torusPow_G2 (K := K) hp hpq
  obtain ⟨ζ, hζo⟩ := @TableBSymp.exists_orderOf_eq_of_dvd K _ _ p ⟨hp⟩ hpq
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨g, hg⟩ := ggExcToralRankInput_G2_of_five_le hp hp5 hpq E hE hcard
  have hrange := TableBExc.range_chevTorus_eq_torusPow hζo hζ hdet hV
  have hmemE : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ (chevTorus .G2 ζ hζ).range := by
    intro x
    rw [hrange, ← hg]
    constructor
    · intro hx
      exact ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    · rintro ⟨y, hy, hyx⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : y = x := mul_left_cancel (mul_right_cancel hyx)
      exact this ▸ hy
  set e : Multiplicative (Fin Tag.G2.rank → ZMod p) →* adjointGroup .G2 K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (chevTorus .G2 ζ hζ) with he
  have heapp : ∀ x, e x = g⁻¹ * chevTorus .G2 ζ hζ x * g := fun x => by
    rw [he, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have heE : e.range = E := by
    ext x
    rw [MonoidHom.mem_range, hmemE]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [heapp]; group⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [heapp, hy]; group⟩
  set n : Fin Tag.G2.rank → adjointGroup .G2 K := fun i =>
    g⁻¹ * ⟨weylElt .G2 K i 1, weylElt_mem_adjointGroup i 1⟩ * g with hn
  have hrefl : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ =
      e (.ofAdd (v - cartanFunctional .G2 p i v • Pi.single i 1)) := by
    intro i v
    rw [heapp, heapp, ← weylElt_conj_chevTorus ζ hζ i v, hn]
    group
  have hnN : ∀ i, n i ∈ Subgroup.normalizer (E : Set (adjointGroup .G2 K)) := by
    intro i
    refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
    rw [← heE] at hb ⊢
    obtain ⟨y, rfl⟩ := hb
    refine ⟨.ofAdd (Multiplicative.toAdd y - cartanFunctional .G2 p i (Multiplicative.toAdd y) •
      Pi.single i 1), ?_⟩
    rw [← hrefl, ofAdd_toAdd]
  intro E' hE' hinv
  have hinvF : ∀ i v, Multiplicative.ofAdd v ∈ E'.comap e →
      Multiplicative.ofAdd (v - cartanFunctional .G2 p i v • Pi.single i 1) ∈ E'.comap e := by
    intro i v hv
    rw [Subgroup.mem_comap, ← hrefl]
    exact hinv (n i) (hnN i) _ hv
  have hEe : ∀ x ∈ E, ∃ y, e y = x := fun x hx => by
    rw [← heE] at hx
    exact hx
  rcases NbrInnerRest.eq_bot_or_eq_top_of_refl .G2 hp hdet cartan_G2_connected_rowTwo
      (cartan_G2_entry_ne_zero_rowTwo hp5) _ hinvF with hbot | htop
  · left
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hEe x (hE' hx)
    have hy : y ∈ E'.comap e := hx
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy, map_one]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hE' fun x hx => ?_
    obtain ⟨y, rfl⟩ := hEe x hx
    have hy : y ∈ E'.comap e := htop ▸ Subgroup.mem_top y
    exact hy

theorem ggSCWeylIrredTwoLU4_adjoint_G2 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) : GGSCWeylIrredTwoLU4 p (adjointGroup .G2 K) :=
  fun _ hE h2 _ => ggWeylIrred_adjoint_G2_of_five_le hp hp5 hpq hE h2

theorem ggSCWeylIrredTwoLU4_recipe_G2 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    GGSCWeylIrredTwoLU4 p (TableBExc.RecipeGroup .G2 K) :=
  ggSCWeylIrredTwoLU4_of_mulEquiv (TableBExc.recipeEquiv .G2 K)
    (ggSCWeylIrredTwoLU4_adjoint_G2 hp hp5 hpq)

theorem ggCenterPrime_recipe_G2 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GGCenterPrime p (TableBExc.RecipeGroup .G2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  exact (OrthRest.center_data (TableBExc.recipeEquiv .G2 K).symm center_adjointGroup_eq_bot
    (fun E _ _ π hπ hcen hc =>
      CFSG.LieType.Steinberg.CentralExt.G2Four.g2_exists_section_of_coprime E π hπ hcen hc)
    hp hp2).2

theorem ggTorusNoLineTwo_recipe_G2 [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    GGTorusNoLineTwo p (TableBExc.RecipeGroup .G2 K) (TableBExc.RecipeID .G2 K) :=
  ggTorusNoLineTwo_of_scWeylIrredTwoLU4 hp (TableBExc.center_recipeGroup_eq_bot .G2 K)
    (fun _ hφ _ => chevG2_idImage_subset_inn K hφ) (ggCenterPrime_recipe_G2 hp (by omega))
    (ggSCWeylIrredTwoLU4_recipe_G2 hp hp5 hpq)

theorem two_dvd_card_recipe_G2 [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    2 ∣ Nat.card (TableBExc.RecipeGroup .G2 K) := by
  rw [Nat.card_congr (TableBExc.recipeEquiv .G2 K).toEquiv, TableBExc.card_adjointGroup_G2_eq,
    hK]
  exact Dvd.dvd.mul_left
    (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)) _) _

theorem largeEvenLabelAll_rowPlainTwo_G2Dvd {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .G2 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlainTwo p 0) := by
  obtain ⟨ht, hpn⟩ := h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hpn
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => conj_mem_chevIDImage _ g,
    TypeA.ggTorusLift_zero (two_dvd_card_recipe_G2 hn hK),
    fun _ _ => ggTorusNoLineTwo_recipe_G2 hp hp5 hpq⟩

end G2

end CFSG.StandardType

end
