module

public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.EmptyFaithful.S14117Basic
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6Frame
public import CFSG.Quasithin.Vol2.Ch12Sec6Statements
public import CFSG.Quasithin.Vol2.Ch5Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 Equiv
open scoped IsMulCommutative

namespace S126L1a

@[expose] def supp (x : PermMod 8) : Finset (Fin 8) :=
  Finset.univ.filter fun i => Multiplicative.toAdd x i ≠ 0

theorem wt_eq_card_supp (x : PermMod 8) : wt x = (supp x).card := rfl

theorem mem_supp {x : PermMod 8} {i : Fin 8} : i ∈ supp x ↔ Multiplicative.toAdd x i ≠ 0 := by
  simp [supp]

theorem supp_permAct (σ : Perm (Fin 8)) (x : PermMod 8) :
    supp (permAct 8 σ x) = (supp x).map σ.toEmbedding := by
  ext i
  rw [Finset.mem_map, mem_supp, permAct_apply]
  constructor
  · intro h
    exact ⟨σ⁻¹ i, mem_supp.2 h, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    rw [mem_supp] at hj
    simpa using hj

theorem wt_permAct (σ : Perm (Fin 8)) (x : PermMod 8) : wt (permAct 8 σ x) = wt x := by
  rw [wt_eq_card_supp, wt_eq_card_supp, supp_permAct, Finset.card_map]

theorem zmod2_eq_of_ne {a b : ZMod 2} (h : a ≠ 0 ↔ b ≠ 0) : a = b := by
  revert a b
  decide

theorem exists_perm {x y : PermMod 8} {k : ℕ} (hk : k ≤ 6) (hx : wt x = k) (hy : wt y = k) :
    ∃ σ : ↥(alternatingGroup (Fin 8)), permAct 8 (σ : Perm (Fin 8)) x = y := by
  have h6 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 6 := by
    have := alternatingGroup.isMultiplyPretransitive (Fin 8)
    rwa [Nat.card_fin] at this
  have hkt : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) k :=
    MulAction.isMultiplyPretransitive_of_le hk (by rw [Nat.card_fin]; norm_num)
  have hx' : (supp x).card = k := hx
  have hy' : (supp y).card = k := hy
  let e := ((supp x).orderEmbOfFin hx').toEmbedding
  let e' := ((supp y).orderEmbOfFin hy').toEmbedding
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) e e'
  have hσi : ∀ i : Fin k, (σ : Perm (Fin 8)) (e i) = e' i := fun i => by
    have := congrArg (fun f : Fin k ↪ Fin 8 => f i) hσ
    simpa [Function.Embedding.smul_apply, Subgroup.smul_def] using this
  have hsupp : (supp x).map (σ : Perm (Fin 8)).toEmbedding = supp y := by
    ext j
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : a ∈ Set.range ((supp x).orderEmbOfFin hx') := by
        rw [Finset.range_orderEmbOfFin]
        exact ha
      obtain ⟨i, rfl⟩ := ha'
      have h1 := hσi i
      simp only [e, e', RelEmbedding.coe_toEmbedding] at h1
      rw [h1]
      exact Finset.orderEmbOfFin_mem _ hy' i
    · intro hj
      have hj' : j ∈ Set.range ((supp y).orderEmbOfFin hy') := by
        rw [Finset.range_orderEmbOfFin]
        exact hj
      obtain ⟨i, rfl⟩ := hj'
      refine ⟨(supp x).orderEmbOfFin hx' i, Finset.orderEmbOfFin_mem _ hx' i, ?_⟩
      have h1 := hσi i
      simp only [e, e', RelEmbedding.coe_toEmbedding] at h1
      exact h1
  refine ⟨σ, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  apply zmod2_eq_of_ne
  have h1 : i ∈ supp (permAct 8 (σ : Perm (Fin 8)) x) ↔ i ∈ supp y := by
    rw [supp_permAct, hsupp]
  simpa [supp] using h1

theorem wt_cases : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 →
    (Finset.univ.filter fun i => x i ≠ 0).card = 0 ∨
    (Finset.univ.filter fun i => x i ≠ 0).card = 2 ∨
    (Finset.univ.filter fun i => x i ≠ 0).card = 4 ∨
    (Finset.univ.filter fun i => x i ≠ 0).card = 6 ∨
    (Finset.univ.filter fun i => x i ≠ 0).card = 8 := by
  decide +kernel

@[expose] def ones8 : Fin 8 → ZMod 2 := fun _ => 1

theorem wt_add_ones : ∀ x : Fin 8 → ZMod 2,
    (Finset.univ.filter fun i => (x + ones8) i ≠ 0).card =
      8 - (Finset.univ.filter fun i => x i ≠ 0).card := by
  decide +kernel

theorem eq_zero_of_wt0 : ∀ x : Fin 8 → ZMod 2,
    (Finset.univ.filter fun i => x i ≠ 0).card = 0 → x = 0 := by
  decide +kernel

theorem eq_ones_of_wt8 : ∀ x : Fin 8 → ZMod 2,
    (Finset.univ.filter fun i => x i ≠ 0).card = 8 → x = ones8 := by
  decide +kernel

theorem mk_mul_allOnes (m : ↥(coreMod 8)) (h : (allOnes 8 : PermMod 8) ∈ coreMod 8) :
    (QuotientGroup.mk (m * ⟨allOnes 8, h⟩) : D8) = QuotientGroup.mk m := by
  rw [QuotientGroup.mk_mul, mul_eq_left]
  refine (QuotientGroup.eq_one_iff _).2 ?_
  change (allOnes 8 : PermMod 8) ∈ Subgroup.zpowers (allOnes 8)
  exact Subgroup.mem_zpowers _

theorem allOnes_mem : (allOnes 8 : PermMod 8) ∈ coreMod 8 := by
  rw [mem_coreMod]
  decide

theorem cases_of_ne_one {y : D8} (hy : y ≠ 1) : IsNonsing y ∨ HasWt 4 y := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rcases wt_cases (Multiplicative.toAdd (m : PermMod 8)) m.2 with h | h | h | h | h
  · exfalso
    apply hy
    have : (m : PermMod 8) = 1 := Multiplicative.toAdd.injective (eq_zero_of_wt0 _ h)
    rw [show m = 1 from Subtype.ext this, QuotientGroup.mk_one]
  · exact Or.inl ⟨m, rfl, h⟩
  · exact Or.inr ⟨m, rfl, h⟩
  · left
    refine ⟨m * ⟨allOnes 8, allOnes_mem⟩, mk_mul_allOnes m allOnes_mem, ?_⟩
    change (Finset.univ.filter fun i => (Multiplicative.toAdd (m : PermMod 8) +
      ones8) i ≠ 0).card = 2
    rw [wt_add_ones]
    change 8 - wt (m : PermMod 8) = 2
    rw [show wt (m : PermMod 8) = 6 from h]
  · exfalso
    apply hy
    refine (QuotientGroup.eq_one_iff _).2 ?_
    change (m : PermMod 8) ∈ Subgroup.zpowers (allOnes 8)
    have : (m : PermMod 8) = allOnes 8 := Multiplicative.toAdd.injective (eq_ones_of_wt8 _ h)
    rw [this]
    exact Subgroup.mem_zpowers _

theorem mk_eq_iff (m m' : ↥(coreMod 8)) :
    (QuotientGroup.mk m : D8) = QuotientGroup.mk m' ↔
      (m : PermMod 8) = m' ∨ (m : PermMod 8) = m' * allOnes 8 := by
  rw [QuotientGroup.eq]
  change ((m⁻¹ * m' : ↥(coreMod 8)) : PermMod 8) ∈ Subgroup.zpowers (allOnes 8) ↔ _
  have h2 : (allOnes 8 : PermMod 8) ^ 2 = 1 := by decide
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  have hmz : ∀ z ∈ Subgroup.zpowers (allOnes 8 : PermMod 8), z = 1 ∨ z = allOnes 8 := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h2' : (allOnes 8 : PermMod 8) ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, h2]
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · left
      rw [_root_.zpow_mul, h2', _root_.one_zpow]
    · right
      rw [_root_.zpow_add, _root_.zpow_mul, h2', _root_.one_zpow, one_mul, zpow_one]
  constructor
  · intro h
    rcases hmz _ h with h | h
    · left
      have := congrArg (fun z => (m : PermMod 8) * z) h
      simpa using this.symm
    · right
      have := congrArg (fun z => (m : PermMod 8) * z) h
      simp only [mul_inv_cancel_left] at this
      calc (m : PermMod 8) = (m : PermMod 8) * allOnes 8 * allOnes 8 := by
            rw [mul_assoc, ← pow_two, h2, mul_one]
        _ = m' * allOnes 8 := by rw [this]
  · rintro (h | h)
    · rw [h, inv_mul_cancel]
      exact Subgroup.one_mem _
    · rw [h, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem not_nonsing_and_wt4 {y : D8} (h2 : IsNonsing y) (h4 : HasWt 4 y) : False := by
  obtain ⟨m, rfl, hm⟩ := h2
  obtain ⟨m', hm', hm'4⟩ := h4
  rcases (mk_eq_iff m' m).1 hm' with h | h
  · rw [h] at hm'4
    rw [hm] at hm'4
    exact absurd hm'4 (by norm_num)
  · have h1 : wt (m' : PermMod 8) = 8 - wt (m : PermMod 8) := by
      rw [h]
      exact wt_add_ones _
    rw [hm'4, hm] at h1
    exact absurd h1 (by norm_num)

theorem dAct_mk (σ : Perm (Fin 8)) (m : ↥(coreMod 8)) :
    dAct σ (QuotientGroup.mk m) = QuotientGroup.mk (coreAct 8 σ m) := by
  unfold dAct
  rw [QuotientGroup.map_mk]
  rfl

theorem hasWt_dAct {k : ℕ} (σ : Perm (Fin 8)) {y : D8} (h : HasWt k y) : HasWt k (dAct σ y) := by
  obtain ⟨m, rfl, hm⟩ := h
  refine ⟨coreAct 8 σ m, (dAct_mk σ m).symm, ?_⟩
  rw [coreAct_coe, wt_permAct, hm]

theorem hasWt_dAct_iff {k : ℕ} (σ : Perm (Fin 8)) {y : D8} : HasWt k (dAct σ y) ↔ HasWt k y := by
  refine ⟨fun h => ?_, hasWt_dAct σ⟩
  have h1 := hasWt_dAct σ⁻¹ h
  have h2 : dAct σ⁻¹ (dAct σ y) = y := by
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [dAct_mk, dAct_mk]
    congr 1
    apply Subtype.ext
    rw [coreAct_coe, coreAct_coe, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rwa [h2] at h1

theorem exists_dAct {k : ℕ} (hk : k ≤ 6) {y y' : D8} (hy : HasWt k y) (hy' : HasWt k y') :
    ∃ σ : ↥(alternatingGroup (Fin 8)), dAct (σ : Perm (Fin 8)) y = y' := by
  obtain ⟨m, rfl, hm⟩ := hy
  obtain ⟨m', rfl, hm'⟩ := hy'
  obtain ⟨σ, hσ⟩ := exists_perm hk hm hm'
  refine ⟨σ, ?_⟩
  rw [dAct_mk]
  congr 1
  exact Subtype.ext hσ

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem part1 (F : Frame126 T L V) :
    ∀ u w : ↥V, F.β u ≠ 1 → F.β w ≠ 1 →
      ((∃ l ∈ L, ∃ hl : l ∈ Subgroup.normalizer (V : Set G),
          F.β ((conjAct V ⟨l, hl⟩ : MulAut ↥V) u) = F.β w) ↔
        (IsNonsing (F.β u) ↔ IsNonsing (F.β w))) := by
  intro u w hu hw
  constructor
  · rintro ⟨l, hlL, hl, hlw⟩
    have ha : conjAct V ⟨l, hl⟩ ∈ autOn L V := mem_autOn_iff_exists.mpr ⟨l, hl, hlL, rfl⟩
    obtain ⟨σ, hσ⟩ := F.π_surj ⟨_, ha⟩
    have h1 := F.equi σ u
    rw [hσ] at h1
    change F.β (conjAct V ⟨l, hl⟩ u) = _ at h1
    rw [hlw] at h1
    rw [h1]
    exact (hasWt_dAct_iff (σ : Perm (Fin 8))).symm
  · intro hiff
    obtain ⟨σ, hσ⟩ : ∃ σ : ↥(alternatingGroup (Fin 8)),
        dAct (σ : Perm (Fin 8)) (F.β u) = F.β w := by
      rcases cases_of_ne_one hu with h2u | h4u
      · exact exists_dAct (by norm_num) h2u (hiff.1 h2u)
      · rcases cases_of_ne_one hw with h2w | h4w
        · exact absurd (hiff.2 h2w) fun h => not_nonsing_and_wt4 h h4u
        · exact exists_dAct (by norm_num) h4u h4w
    obtain ⟨l, hl, hlL, hla⟩ := mem_autOn_iff_exists.mp (F.π σ).2
    refine ⟨l, hlL, hl, ?_⟩
    rw [hla, F.equi σ u, hσ]

theorem card_A8 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_of_lieModel_psl32 {Y : Type} [Group Y] (h : LieModel Y .PSL 3 2 1) :
    Nat.card Y = 168 :=
  CFSG.Blueprint.LieModel.card_psl_three_two h

omit [IsMulCommutative ↥V] in
theorem part5 (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8) (hH : Hyp126 G T L V) :
    oThreePrimeResidual (Subgroup.normalizer (L : Set G)) = L := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hO2 : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_reduced hyp.normalizes hVT hred
  obtain ⟨φ, hφ, hker⟩ := hH.alt8
  have hle : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    apply hO2
    have hx' : x ∈ CFSG.Open.pCore 2 ↥L := by
      exact hx
    exact ⟨x, hx', rfl⟩
  have hdvd : 20160 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [← card_A8]
    exact Subgroup.card_dvd_of_surjective (f := QuotientGroup.lift _ φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ _ hφ _)
  rcases h1228 G T L V hyp with h | (h | h) | ⟨⟨n, hn, -, hZ, he⟩, -⟩
  · exact h
  · exfalso
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hdvd
    norm_num [Nat.factorial] at hdvd
  · exfalso
    rw [card_of_lieModel_psl32 h] at hdvd
    exact absurd hdvd (by decide)
  · exfalso
    obtain ⟨e⟩ := he
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [Nat.card_congr e.toEquiv, hZ] at h1
    rw [h1] at hdvd
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] at hdvd <;>
      norm_num [Nat.factorial] at hdvd

end S126L1a

end CFSG.Quasithin.H13
