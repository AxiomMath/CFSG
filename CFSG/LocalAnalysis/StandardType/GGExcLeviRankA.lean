module

public import CFSG.LocalAnalysis.StandardType.GGExcLeviRankBase

public section

namespace CFSG.StandardType.E8LeviG3

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Assembly CFSG.ComponentClassification.CatLeafProof
open CFSG.StandardType.F4Rest
open scoped MatrixGroups


theorem card_le_pow_subsystemGroup_e8A {m : ℕ} (hm : 3 ≤ m) (ι : Fin m → Fin Tag.E8.rank)
    (hadj : ∀ i j : Fin m, j.val = i.val + 1 →
      ι i ≠ ι j ∧ Tag.cartan .E8 (ι i) (ι j) = -1 ∧ Tag.cartan .E8 (ι j) (ι i) = -1 ∧
        ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 (ι i) l + 2 * Tag.cartan .E8 (ι j) l)
    (hnadj : ∀ i j : Fin m, i ≠ j → ¬ j.val = i.val + 1 → ¬ i.val = j.val + 1 →
      ι i ≠ ι j ∧ Tag.cartan .E8 (ι i) (ι j) = 0 ∧ Tag.cartan .E8 (ι j) (ι i) = 0)
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card K - 1) {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range ι)) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ ((m + 1) / CFSG.StandardType.OrdPNS.ordQ K p) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by rw [← Fintype.card_eq_nat_card]; exact hK
  have hn : 1 ≤ (n : ℕ) := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hKn
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE' rfl ι hadj hnadj
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 (n : ℕ) := by
    refine ⟨Nat.prime_two, hn, by omega, ?_, ?_⟩
    · intro h
      exact absurd (congrArg Prod.fst h) (by omega)
    · intro h
      exact absurd (congrArg Prod.fst h) (by omega)
  obtain ⟨Ψ, hker, hrange, hqs, hmodel⟩ :=
    specialLinear_frame_subgroup (m := m) hadm hm hKn
      (U := fun k => CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup (ι k)) hcomm hρ hψ
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo hp hp2
  have hpker : ¬ p ∣ Nat.card Ψ.ker := by
    intro hd
    have hcenter : Nat.card (Subgroup.center (SL(m + 1, K))) ∣ Nat.card K - 1 :=
      (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := m + 1) (by omega) K).trans
        (Nat.gcd_dvd_right _ _)
    exact hpq (hd.trans ((Subgroup.card_dvd_of_le hker).trans hcenter))
  have hS : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) ≤
      (m + 1) / CFSG.StandardType.OrdPNS.ordQ K p := by
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup Ψ.range) =
        CFSG.Open.pRank p (⊤ : Subgroup (SL(m + 1, K) ⧸ Ψ.ker)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
        (QuotientGroup.quotientKerEquivRange Ψ).symm
    rw [h1, CFSG.SectionRank.pRank_quotient_eq Ψ.ker hpker]
    exact pRank_specialLinear_le_ordQ (K := K) (p := p) (d := m + 1) hp hp2
  have hEmap : E ≤ Ψ.range.map (adjointGroup Tag.E8 K).subtype := by
    rw [hrange, map_subtype_iSup_rankOne ι]
    exact hE
  exact card_le_pow_of_le_map_subtype hp hS hEmap hEel

theorem card_le_pow_two_subsystemGroup_e8A7 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A7Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have hpq := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have h := card_le_pow_subsystemGroup_e8A (m := 7) (by norm_num) e8A7Node
    e8A7_adj e8A7_nadj hp hp2 hpq hE hEel
  have h8 : (7 + 1) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 2 := by
    have hle : 8 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 8 / 3 :=
      Nat.div_le_div_left h3 (by norm_num)
    norm_num at hle
    exact hle
  exact h.trans (Nat.pow_le_pow_right hp.pos h8)

theorem card_le_pow_two_subsystemGroup_e8A6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A6Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  have hpq := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have h := card_le_pow_subsystemGroup_e8A (m := 6) (by norm_num) e8A6Node
    e8A6_adj e8A6_nadj hp hp2 hpq hE hEel
  have h7 : (6 + 1) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 2 := by
    have hle : 7 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 7 / 3 :=
      Nat.div_le_div_left h3 (by norm_num)
    norm_num at hle
    exact hle
  exact h.trans (Nat.pow_le_pow_right hp.pos h7)

theorem card_le_pow_one_subsystemGroup_e8A4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A4Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 1 := by
  have hpq := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have h := card_le_pow_subsystemGroup_e8A (m := 4) (by norm_num) e8A4Node
    e8A4_adj e8A4_nadj hp hp2 hpq hE hEel
  have h5 : (4 + 1) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    have hle : 5 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 5 / 3 :=
      Nat.div_le_div_left h3 (by norm_num)
    norm_num at hle
    exact hle
  exact h.trans (Nat.pow_le_pow_right hp.pos h5)

theorem card_le_pow_one_subsystemGroup_e8A4' {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A4Node'))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 1 := by
  have hpq := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have h := card_le_pow_subsystemGroup_e8A (m := 4) (by norm_num) e8A4Node'
    e8A4'_adj e8A4'_nadj hp hp2 hpq hE hEel
  have h5 : (4 + 1) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    have hle : 5 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 5 / 3 :=
      Nat.div_le_div_left h3 (by norm_num)
    norm_num at hle
    exact hle
  exact h.trans (Nat.pow_le_pow_right hp.pos h5)

theorem card_le_pow_one_subsystemGroup_e8A3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K (Set.range e8A3Node))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 1 := by
  have hpq := not_dvd_card_sub_one_of_three_le_ordQ hp h3
  have h := card_le_pow_subsystemGroup_e8A (m := 3) (by norm_num) e8A3Node
    e8A3_adj e8A3_nadj hp hp2 hpq hE hEel
  have h4 : (3 + 1) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    have hle : 4 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 4 / 3 :=
      Nat.div_le_div_left h3 (by norm_num)
    norm_num at hle
    exact hle
  exact h.trans (Nat.pow_le_pow_right hp.pos h4)

theorem card_le_pow_zero_subsystemGroup_e8node {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    (i : Fin Tag.E8.rank) {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K {i}) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 0 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo (K := K) hp hp2
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hinj : Function.Injective (simpleRootSL2 Tag.E8 K i) :=
    CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two h2 i
  have hrange : (simpleRootSL2 Tag.E8 K i).range = subsystemGroup Tag.E8 K {i} := by
    rw [range_simpleRootSL2, subsystemGroup]
    congr 1
    ext g
    constructor
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨i, by simp, c, Or.inl rfl⟩
      · exact ⟨i, by simp, c, Or.inr rfl⟩
    · rintro ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inl ⟨c, rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inr ⟨c, rfl⟩
  let Et : Subgroup (SL(2, K)) := E.comap (simpleRootSL2 Tag.E8 K i)
  have hEtrange : E ≤ (simpleRootSL2 Tag.E8 K i).range := hrange ▸ hE
  have hEtcard : Nat.card Et = Nat.card E := by
    calc Nat.card Et = Nat.card (Et.map (simpleRootSL2 Tag.E8 K i)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self hEtrange]
  have hEtel : IsElemAbelian p Et := isElemAbelian_comap hinj hEel
  have hbound := card_le_pow_of_injective_GL (G := SL(2, K)) (ι := Fin 2) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hEtel
  have h2d : Fintype.card (Fin 2) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 0 := by
    rw [Fintype.card_fin, Nat.div_eq_of_lt (by omega : 2 < CFSG.StandardType.OrdPNS.ordQ K p)]
  calc Nat.card E = Nat.card Et := hEtcard.symm
    _ ≤ p ^ (Fintype.card (Fin 2) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 0 := Nat.pow_le_pow_right hp.pos h2d

theorem map_subtype_pairSubgroup {K : Type} [Field K] (i j : Fin Tag.E8.rank) :
    (CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j).map
      (adjointGroup Tag.E8 K).subtype =
      subsystemGroup Tag.E8 K ({i, j} : Set (Fin Tag.E8.rank)) := by
  have h1 : (⨆ k : Fin 2, CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup
      ((![i, j] : Fin 2 → Fin Tag.E8.rank) k)) =
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
        CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun k => ?_
      fin_cases k
      · exact le_sup_left
      · exact le_sup_right
    · exact sup_le (le_iSup (fun k : Fin 2 => CFSG.LieType.CurtisTits.rankOne
        (e8Datum K).rootGroup ((![i, j] : Fin 2 → Fin Tag.E8.rank) k)) 0)
        (le_iSup (fun k : Fin 2 => CFSG.LieType.CurtisTits.rankOne
        (e8Datum K).rootGroup ((![i, j] : Fin 2 → Fin Tag.E8.rank) k)) 1)
  have h2 := map_subtype_iSup_rankOne (τ := Tag.E8) (K := K) (r := 2)
    (![i, j] : Fin 2 → Fin Tag.E8.rank)
  rw [← h1, h2]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem card_le_pow_one_subsystemGroup_e8A2 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h3 : 3 ≤ CFSG.StandardType.OrdPNS.ordQ K p)
    {i j : Fin Tag.E8.rank} (hij : i ≠ j) (hcij : Tag.cartan .E8 i j = -1)
    (hcji : Tag.cartan .E8 j i = -1)
    (hk : ∃ l, ¬ (3 : ℤ) ∣ Tag.cartan .E8 i l + 2 * Tag.cartan .E8 j l)
    {E : Subgroup (ModGL Tag.E8 K)}
    (hE : E ≤ subsystemGroup Tag.E8 K ({i, j} : Set (Fin Tag.E8.rank)))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 1 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo hp hp2
  obtain ⟨l, hl⟩ := hk
  obtain ⟨O, C, hE'⟩ := exists_e8_chevalleyExtras K
  obtain ⟨emb, hinj, hpair, -⟩ :=
    CFSG.ClassicalInvolution.WeakCT.exists_sl3Levi (D := e8Datum K) (x := e8Par K) hE' rfl
      hij hcij hcji hl
  have hpairRoots : ∀ γ : Fin Tag.E8.rank → ℤ, γ ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j →
      (e8Datum K).rootGroup γ ≤ emb.range := hpair
  have hs1 : Pi.single i 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) i, ?_⟩
    intro k hk
    have hki : k ≠ i := fun h => hk (by simp [h])
    rw [Pi.single_eq_of_ne hki]
  have hs2 : -Pi.single i 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.neg_mem_roots (CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) i), ?_⟩
    intro k hk
    have hki : k ≠ i := fun h => hk (by simp [h])
    rw [Pi.neg_apply, Pi.single_eq_of_ne hki, neg_zero]
  have ht1 : Pi.single j 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) j, ?_⟩
    intro k hk
    have hkj : k ≠ j := fun h => hk (by simp [h])
    rw [Pi.single_eq_of_ne hkj]
  have ht2 : -Pi.single j 1 ∈ CFSG.Timmesfeld.pairRoots (e8Datum K) i j := by
    rw [CFSG.Timmesfeld.mem_pairRoots_iff]
    refine ⟨CFSG.Timmesfeld.LevisExtras.neg_mem_roots (CFSG.Timmesfeld.LevisExtras.single_mem_roots (D := e8Datum K) j), ?_⟩
    intro k hk
    have hkj : k ≠ j := fun h => hk (by simp [h])
    rw [Pi.neg_apply, Pi.single_eq_of_ne hkj, neg_zero]
  have hSle : CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j ≤ emb.range :=
    sup_le (sup_le (hpairRoots _ hs1) (hpairRoots _ hs2))
      (sup_le (hpairRoots _ ht1) (hpairRoots _ ht2))
  have hErange : E ≤ (CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j).map (adjointGroup Tag.E8 K).subtype := by
    rw [map_subtype_pairSubgroup]
    exact hE
  set E' : Subgroup (adjointGroup Tag.E8 K) :=
    E.comap (adjointGroup Tag.E8 K).subtype with hE'def
  have hE'le : E' ≤ CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup i ⊔
      CFSG.LieType.CurtisTits.rankOne (e8Datum K).rootGroup j := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hErange hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hE'le_range : E' ≤ emb.range := hE'le.trans hSle
  have hcard' : Nat.card E' = Nat.card E := by
    calc Nat.card E' = Nat.card (E'.map (adjointGroup Tag.E8 K).subtype) :=
          (Subgroup.card_map_of_injective (adjointGroup Tag.E8 K).subtype_injective).symm
      _ = Nat.card E := by
        rw [hE'def, Subgroup.map_comap_eq_self]
        exact hErange.trans (Subgroup.map_le_range _ _)
  have hE'el : IsElemAbelian p E' :=
    isElemAbelian_comap (adjointGroup Tag.E8 K).subtype_injective hEel
  set E'' : Subgroup (SL(3, K)) := E'.comap emb with hE''def
  have hcard'' : Nat.card E'' = Nat.card E' := by
    have hker : emb.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 hinj
    calc Nat.card E'' = Nat.card emb.ker * Nat.card E' :=
          CFSG.LocalAnalysis.GLTheoremA.card_comap_of_le_range emb hE'le_range
      _ = Nat.card E' := by rw [hker, Subgroup.card_bot, one_mul]
  have hE''el : IsElemAbelian p E'' := isElemAbelian_comap hinj hE'el
  have hbound := card_le_pow_of_injective_GL (G := SL(3, K)) (ι := Fin 3) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hE''el
  have h31 : Fintype.card (Fin 3) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    rw [Fintype.card_fin]
    have hle : 3 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 3 / 3 :=
      Nat.div_le_div_left h3 (by norm_num)
    norm_num at hle
    exact hle
  calc Nat.card E = Nat.card E' := hcard'.symm
    _ = Nat.card E'' := hcard''.symm
    _ ≤ p ^ (Fintype.card (Fin 3) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h31

end CFSG.StandardType.E8LeviG3
