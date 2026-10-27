module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockCtx
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeList

public section

namespace CFSG.QuasithinUnique.Bridge

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

namespace L2Block

variable {S : Type} [CommGroup S] [Finite S] {G L A : Subgroup (MulAut S)} {n : ℕ}

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {m : ℕ} (h : Nat.card K = 2 ^ m) :
    CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ m := by rw [← Nat.card_eq_fintype_card, h]
  have hm : 1 ≤ m := TypeList.one_le_of_card_eq_pow h
  exact charP_of_card_eq_prime_pow (p := 2) (f := m) hcard

theorem card_statedSp_two (K : Type) [Field K] [Finite K] :
    Nat.card (StatedSp 2 K) =
      Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) :=
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two K

namespace Ctx

variable (C : Ctx G L n)

include C

theorem case2_false (h : B42Case2 G L) : False := by
  obtain ⟨-, ⟨m, hm⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hm
  have := charP_two_of_card hcard
  let f : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥L :=
    (specialLinearGroupEquivStatedSL 3 K).trans e
  have h4 : f (GoldL2.unitri3 K) ^ 4 = 1 := by
    rw [← map_pow, GoldL2.unitri3_pow_four, map_one]
  have h2 := C.no4 _ h4
  apply GoldL2.unitri3_sq_ne_one K
  apply f.injective
  rw [map_pow, map_one]
  exact h2

theorem case3_false (hq : CFSG.IsQuasisimple ↥L) {A : Subgroup (MulAut S)}
    (hA : IsFFStarOffender G A) (h : B42Case3 G L) : False := by
  obtain ⟨⟨m, hm, hm2⟩, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSp4.exists_equiv hm
  have hm1 := TypeList.one_le_of_card_eq_pow hcard
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · have h1 : m = 1 := by omega
    subst h1
    have : Fintype K := Fintype.ofFinite K
    have hK2 : Fintype.card K = 2 := by
      rw [← Nat.card_eq_fintype_card]
      simpa using hcard
    let π : Equiv.Perm (Fin 6) →* ↥(ffJ G) :=
      e.toMonoidHom.comp (Alt57Model.spEquivPerm K hK2).symm.toMonoidHom
    have hπ : Function.Surjective π :=
      e.surjective.comp (Alt57Model.spEquivPerm K hK2).symm.surjective
    have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (C.le_ffJ hA)).symm hq
    obtain ⟨f⟩ := TypeList.perm_perfect_normal_equiv (n := 6) (by norm_num) π hπ _ C.hnorm
      hq'.1.commutator_eq_top (TypeList.exists_noncomm_of_quasisimple hq')
    have h1 : Nat.card ↥L = 360 := by
      rw [← card_alt_six, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (C.le_ffJ hA)).toEquiv.symm,
        Nat.card_congr f.toEquiv]
    exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inl rfl)) (C.card_eq.symm.trans h1)
  · have heq : ffJ G = L := hm2 hge
    have h1 : Nat.card ↥L = Nat.card K ^ 4 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 4 - 1)) := by
      rw [← card_statedSp_two, Nat.card_congr e.toEquiv, Nat.card_congr
        (MulEquiv.subgroupCongr heq).toEquiv]
    rw [hcard, C.card_eq] at h1
    exact GoldL2.sl2_card_ne_sp4 C.three_le hge h1

theorem case5_false (hq : CFSG.IsQuasisimple ↥L) {A : Subgroup (MulAut S)}
    (hA : IsFFStarOffender G A) (h : B42Case5 G A) : False := by
  obtain ⟨⟨m, hm, π, hπ, -⟩, -⟩ := h
  have hm5 : 5 ≤ m := by rcases hm with rfl | rfl <;> omega
  have hq' : CFSG.IsQuasisimple ↥(L.subgroupOf (ffJ G)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (C.le_ffJ hA)).symm hq
  obtain ⟨f⟩ := TypeList.perm_perfect_normal_equiv hm5 π hπ.1 _ C.hnorm hq'.1.commutator_eq_top
    (TypeList.exists_noncomm_of_quasisimple hq')
  have h1 : Nat.card ↥L = Nat.card (alternatingGroup (Fin m)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (C.le_ffJ hA)).toEquiv.symm,
      Nat.card_congr f.toEquiv]
  rcases hm with rfl | rfl
  · rw [card_alt_five] at h1
    exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inl rfl) (C.card_eq.symm.trans h1)
  · rw [card_alt_seven] at h1
    exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inr (Or.inl rfl)))
      (C.card_eq.symm.trans h1)

theorem case6_false (h : B42Case6 G L A) : False := by
  obtain ⟨-, ⟨π, hπ⟩, -⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alt_isSimple (by norm_num)
  have := C.simple
  have : Nontrivial ↥L := C.simple.toNontrivial
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple
    (Γ := alternatingGroup (Fin 6)) (H := ↥L) π hπ.1
  have h1 := Nat.card_congr e.toEquiv
  rw [card_alt_six] at h1
  exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inl rfl)) (C.card_eq.symm.trans h1.symm)

theorem case7_false (h : B42Case7 G L A) : False := by
  obtain ⟨-, -, ⟨α, π, hπ⟩, -, -, -⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alt_isSimple (by norm_num)
  have := C.simple
  have : Nontrivial ↥L := C.simple.toNontrivial
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple
    (Γ := alternatingGroup (Fin 7)) (H := ↥L) π hπ.1
  have h1 := Nat.card_congr e.toEquiv
  rw [card_alt_seven] at h1
  exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inr (Or.inl rfl)))
    (C.card_eq.symm.trans h1.symm)

theorem case8_false (h : B42Case8 G L A) : False := by
  obtain ⟨-, -, -, K, hK, hKfin, Γ₀, hK4, -, hHat, -, π, hπ, -⟩ := h
  have hinj : Function.Injective π := hπ.injective_of_faithful (FFModel.nat_faithful _)
  have hbot : Subgroup.center ↥Γ₀ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hgL : π g ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ : ∃ y : ↥Γ₀, π y = x := hπ.1 x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg y]
    rw [C.center_bot, Subgroup.mem_bot] at hgL
    exact Subgroup.mem_bot.2 (hinj (by rw [hgL, map_one]))
  have h3 := hHat.2.1
  rw [hbot, Subgroup.card_bot] at h3
  omega

theorem case9_false (h : B42Case9 G L) : False := by
  obtain ⟨-, m, hm, hnat, -⟩ := h
  obtain ⟨K, hK, hKfin, hcard, ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hnat
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have : NeZero m := ⟨by rcases hm with rfl | rfl <;> norm_num⟩
  have hL : Nat.card ↥L = ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)) := by
    rw [← Nat.card_congr e.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL m K).toEquiv]
    exact card_sl_two_field m K hK2
  rcases hm with rfl | rfl
  · rw [Fin.prod_univ_four] at hL
    norm_num at hL
    exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (C.card_eq.symm.trans hL)
  · rw [Fin.prod_univ_five] at hL
    norm_num at hL
    exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (C.card_eq.symm.trans hL)

theorem case_sl_false {m : ℕ} (hm : m = 4 ∨ m = 5) (π : ↥(StatedSL m (ZMod 2)) →* ↥L)
    (hπ : Function.Surjective π) : False := by
  have hm3 : 3 ≤ m := by rcases hm with rfl | rfl <;> norm_num
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := isSimple_sl_zmod2 m hm3
  have : IsSimpleGroup ↥(StatedSL m (ZMod 2)) :=
    (specialLinearGroupEquivStatedSL m (ZMod 2)).symm.isSimpleGroup
  have : Nontrivial ↥L := C.simple.toNontrivial
  obtain ⟨e⟩ := exists_mulEquiv_of_surjective_of_simple π hπ
  have h1 : Nat.card ↥L = Nat.card (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := by
    rw [← Nat.card_congr e.toEquiv,
      Nat.card_congr (specialLinearGroupEquivStatedSL m (ZMod 2)).toEquiv]
  rcases hm with rfl | rfl
  · rw [card_sl4] at h1
    exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (C.card_eq.symm.trans h1)
  · rw [card_sl5] at h1
    exact GoldL2.sl2_card_ne_fixed C.three_le (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (C.card_eq.symm.trans h1)

end Ctx

end L2Block

end CFSG.QuasithinUnique.Bridge
