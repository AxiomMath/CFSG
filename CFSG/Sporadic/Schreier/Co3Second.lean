module

public import CFSG.Sporadic.Schreier.Co3Centralizers
public import CFSG.Sporadic.Schreier.Co3SecondCheck
public import CFSG.Sporadic.Schreier.M12
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCyclicCentralFactor

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Monster.B.Mathieu

theorem mem_co3FinList {n : ℕ} (hn : 0 < n) {l : List ℕ} (hl : ∀ x ∈ l, x < n) (p : Fin n) :
    p ∈ co3FinList n hn l ↔ (p : ℕ) ∈ l := by
  rw [co3FinList, List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    show x % n ∈ l
    rw [Nat.mod_eq_of_lt (hl x hx)]
    exact hx
  · intro hp
    exact ⟨p, hp, Fin.ext (Nat.mod_eq_of_lt p.2)⟩

theorem co3FinList_nodup {n : ℕ} (hn : 0 < n) {l : List ℕ} (hl : ∀ x ∈ l, x < n)
    (hnd : l.Nodup) : (co3FinList n hn l).Nodup := by
  refine hnd.map_on fun a ha b hb hab => ?_
  have := congrArg Fin.val hab
  simp only at this
  rwa [Nat.mod_eq_of_lt (hl a ha), Nat.mod_eq_of_lt (hl b hb)] at this

theorem co3FinList_getElem {n : ℕ} (hn : 0 < n) {l : List ℕ} (hl : ∀ x ∈ l, x < n) {j : ℕ}
    (hj : j < (co3FinList n hn l).length) :
    ((co3FinList n hn l)[j] : ℕ) = l[j]'(by simpa [co3FinList] using hj) := by
  simp only [co3FinList, List.getElem_map]
  exact Nat.mod_eq_of_lt (hl _ (List.getElem_mem _))

theorem co3ItNat_lt : ∀ x ∈ co3ItNat, x < 276 := by decide

theorem co3It_nodup : co3It.Nodup :=
  co3FinList_nodup (by decide) co3ItNat_lt pointList_co3ItNat.sorted.nodup

theorem mem_co3It
    (p : Fin 276) : p ∈ co3It ↔ co3Tt p = p := by
  rw [co3It, mem_co3FinList _ co3ItNat_lt, co3It_spec]

theorem co3It_length : co3It.length = 12 := rfl

theorem co3M1_preserves :
    ∀ h ∈ co3M1, ∀ p ∈ co3It, h p ∈ co3It := by
  intro h hh p hp
  rw [mem_co3It] at hp ⊢
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (co3M1_le_centralizer hh)
  rw [← Equiv.Perm.mul_apply, ← hc, Equiv.Perm.mul_apply, hp]

@[expose] def co3Kappa1 :
    co3M1 →* Equiv.Perm (Fin 12) :=
  (MulAut.conj co3C12).toMonoidHom.comp ((finCongr co3It_length).permCongrHom.toMonoidHom.comp
    (restrictHom co3It co3M1 co3M1_preserves co3It_nodup))

@[expose] def co3ItLab (k : Fin 12) : Fin 276 :=
  co3It.get ((finCongr co3It_length).symm (co3C12⁻¹ k))

theorem co3_permCongrHom_apply {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (y : β) :
    e.permCongrHom σ y = e (σ (e.symm y)) := rfl

theorem co3ItLab_kappa1
    (m : co3M1) (k : Fin 12) :
    co3ItLab (co3Kappa1 m k) = (m : Equiv.Perm (Fin 276)) (co3ItLab k) := by
  unfold co3ItLab co3Kappa1
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Equiv.Perm.mul_apply]
  rw [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, co3_permCongrHom_apply, Equiv.symm_apply_apply,
    get_restrictHom]

theorem co3C12_inv :
    isInvA 12 co3C12Arr (invCand 12 co3C12Arr) = true :=
  isInvA_co3Field12 (f := 1) (k := 0) (by norm_num) (by rw [co3Field12_size]; decide)

theorem rep_co3C12 :
    Rep 12 co3C12Arr co3C12 := (rep_permOfArr co3C12_inv).1

theorem co3ItArr_size : co3ItArr.size = co3It.length := rfl

theorem co3It_getElem {j : ℕ} (hj : j < co3It.length) :
    (co3It[j] : ℕ) = co3ItNat[j]'(by simpa [co3It, co3FinList] using hj) :=
  co3FinList_getElem (by decide) co3ItNat_lt hj

theorem co3ItArr_get (i : Fin co3It.length) : co3ItArr[(i : ℕ)]! = (co3It.get i : ℕ) := by
  have hi : (i : ℕ) < co3ItNat.length := i.2
  rw [List.get_eq_getElem, co3It_getElem, co3ItArr, getElem!_pos _ _ (by simpa using hi),
    List.getElem_toArray]

theorem co3ItArr_nodup :
    co3ItArr.toList.Nodup := pointList_co3ItNat.sorted.nodup

theorem rep_kappa1
    {a : Array ℕ} {m : co3M1} (ha : Rep 276 a (m : Equiv.Perm (Fin 276))) :
    Rep 12 (renameA 12 co3C12Arr (restrictA co3ItArr a)) (co3Kappa1 m) := by
  have h1 := rep_restrictA co3ItArr_size co3ItArr_get co3ItArr_nodup co3M1_preserves co3It_nodup ha
  have h2 : Rep 12 (restrictA co3ItArr a) ((finCongr co3It_length).permCongrHom
      (restrictHom co3It co3M1 co3M1_preserves co3It_nodup m)) := by
    intro x
    exact h1 ((finCongr co3It_length).symm x)
  exact rep_renameA rep_co3C12 co3C12_inv h2

@[expose] def co3M1GenElt (k : Fin 6) : co3M1 :=
  ⟨permOfArr 276 co3M1Arrs[(k : ℕ)]!, by rw [co3M1_eq]; exact Subgroup.subset_closure ⟨k, rfl⟩⟩

theorem co3M1_top : (⊤ : Subgroup co3M1) = Subgroup.closure (Set.range co3M1GenElt) := by
  symm
  rw [eq_top_iff]
  rintro ⟨g, hg⟩ -
  have hg' : g ∈ Subgroup.closure (Set.range fun k : Fin 6 => permOfArr 276 co3M1Arrs[(k : ℕ)]!) :=
    co3M1_eq ▸ hg
  induction hg' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact Subgroup.subset_closure ⟨k, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    exact Subgroup.mul_mem _ (ihx (co3M1_eq ▸ hx)) (ihy (co3M1_eq ▸ hy))
  | inv x hx ihx => exact Subgroup.inv_mem _ (ihx (co3M1_eq ▸ hx))

theorem co3M112Arrs_size : co3M112Arrs.size = 13 := co3Field12_size' 0 rfl

theorem co3M112Arrs_inv : ∀ j < co3M112Arrs.size,
    isInvA 12 co3M112Arrs[j]! (rawInvs 12 co3M112Arrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field12 (f := 0) (by norm_num) hj

theorem co3M112Arrays :
    ChainArrays co3M112Chain (co3M112Arrs.extract 0 co3M112GenCount)
    co3M112Arrs co3M112BaseArr (wordsArr co3M112GenCount co3M112StrongCount co3M112Derivations) :=
  chainArrays_ofArrays co3M112Arrs_inv

theorem co3M112Extract_get {j : ℕ} (hj : j < 5) :
    (co3M112Arrs.extract 0 5)[j]! = co3M112Arrs[j]! := by
  rw [getElem!_pos _ j (by simp [co3M112Arrs_size]; omega),
    getElem!_pos _ j (by rw [co3M112Arrs_size]; omega), Array.getElem_extract]
  simp

theorem co3M112Extract_size : (co3M112Arrs.extract 0 5).size = 5 := by
  simp [co3M112Arrs_size]

theorem co3X12_eq : co3X12 = Subgroup.closure
    {g | ∃ j < (co3M112Arrs.extract 0 5).size, permOfArr 12 (co3M112Arrs.extract 0 5)[j]! = g} := by
  rw [co3X12, co3M112Chain, ofArrays_originalSubgroup]
  congr 1
  ext g
  rw [Set.mem_range, Set.mem_ofPred_eq, co3M112Extract_size]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, by rw [co3M112Extract_get i.2]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by rw [co3M112Extract_get hi]⟩

theorem card_co3X12 :
    Nat.card co3X12 = 95040 := by
  rw [co3X12, card_originalSubgroup_of_chainOK co3M112Arrays (by norm_num) co3M112Chain_check.1,
    co3M112Chain_check.2]
  rfl

theorem co3Kappa1Gens_size : co3Kappa1Gens.size = 6 := by simp [co3Kappa1Gens]

theorem co3_getElem!_ofFn {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem rep_co3Kappa1Gens :
    ∀ k < co3Kappa1Gens.size,
    Rep 12 co3Kappa1Gens[k]! (if h : k < 6 then co3Kappa1 (co3M1GenElt ⟨k, h⟩) else 1) := by
  intro k hk
  rw [co3Kappa1Gens_size] at hk
  rw [dite_eq_left hk, co3Kappa1Gens, co3_getElem!_ofFn _ hk]
  exact rep_kappa1 (rep_co3M1Arr (by show k < 11; omega))

theorem rep_co3M112Gens : ∀ j < (co3M112Arrs.extract 0 5).size,
    Rep 12 (co3M112Arrs.extract 0 5)[j]! (permOfArr 12 (co3M112Arrs.extract 0 5)[j]!) := by
  intro j hj
  have hj' : j < 5 := by rwa [co3M112Extract_size] at hj
  rw [co3M112Extract_get hj']
  exact (rep_permOfArr (co3M112Arrs_inv j (by rw [co3M112Arrs_size]; omega))).1

theorem co3Kappa1_range_X12 :
    co3Kappa1.range = co3X12 := by
  rw [MonoidHom.range_eq_map, co3M1_top, MonoidHom.map_closure, co3X12_eq,
    ← closure_eq_of_coversOK rep_co3Kappa1Gens rep_co3M112Gens co3Second_check.2.2.1]
  congr 1
  ext σ
  simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq, co3Kappa1Gens_size]
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, k.2, by rw [dite_eq_left k.2]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨⟨k, hk⟩, rfl⟩, by rw [dite_eq_left hk]⟩

theorem mem_co3X12_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 12)} (hG : Rep 12 g G)
    (h : siftA 12 co3M112Levels co3M112BaseArr 0 g = true) : G ∈ co3X12 :=
  (siftA_iff_mem_originalSubgroup co3M112Arrays (by norm_num) co3M112Chain_check.1 hG).1 h

theorem co3X12_eq_M12 :
    co3X12 = NativeSporadic.M12 := by
  have hle : NativeSporadic.M12 ≤ co3X12 := by
    rw [m12_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact mem_co3X12_of_sift (rep_imageList m12gA) co3Second_check.2.2.2.1
    · exact mem_co3X12_of_sift (rep_imageList m12gB) co3Second_check.2.2.2.2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_co3X12, m12_card])).symm

theorem co3Kappa1_range :
    co3Kappa1.range = NativeSporadic.M12 := by
  rw [co3Kappa1_range_X12, co3X12_eq_M12]

theorem co3Tt_mem_M1 :
    co3Tt ∈ co3M1 := by
  rw [co3M1_eq_centralizer]
  exact Subgroup.mem_inf.2 ⟨co3Tt_mem_P, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def co3TtM1 :
    co3M1 := ⟨co3Tt, co3Tt_mem_M1⟩

theorem co3Kappa1_t :
    co3Kappa1 co3TtM1 = 1 := by
  have h : restrictHom co3It co3M1 co3M1_preserves co3It_nodup co3TtM1 = 1 :=
    restrictHom_eq_one _ _ _ _ _ fun p hp => by
      rw [co3TtM1, Subgroup.coe_mk]; exact (mem_co3It p).1 hp
  unfold co3Kappa1
  simp only [MonoidHom.coe_comp, Function.comp_apply, h, map_one]

theorem orderOf_co3TtM1 :
    orderOf co3TtM1 = 2 := by
  rw [co3TtM1, Subgroup.orderOf_mk, orderOf_co3Tt]

theorem card_ker_co3Kappa1 :
    Nat.card co3Kappa1.ker = 2 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup co3Kappa1.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange co3Kappa1).toEquiv, co3Kappa1_range,
    m12_card, card_co3M1] at h1
  omega

theorem co3Kappa1_ker :
    co3Kappa1.ker = Subgroup.zpowers co3TtM1 := by
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 co3Kappa1_t) ?_).symm
  rw [card_ker_co3Kappa1, Nat.card_zpowers, orderOf_co3TtM1]

theorem co3M1CommArrs_size : co3M1CommArrs.size = 8 := co3Field276_size' 9 rfl

theorem co3M1CommArrs_inv : ∀ j < co3M1CommArrs.size,
    isInvA 276 co3M1CommArrs[j]! (rawInvs 276 co3M1CommArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field276 (f := 9) (by norm_num) hj

theorem co3M1CommArrays : ChainArrays co3M1CommChain
    (co3M1CommArrs.extract 0 co3M1CommGenCount) co3M1CommArrs co3M1CommBaseArr
    (wordsArr co3M1CommGenCount co3M1CommStrongCount co3M1CommDerivations) :=
  chainArrays_ofArrays co3M1CommArrs_inv

theorem card_co3L :
    Nat.card co3L = 95040 := by
  rw [co3L, card_originalSubgroup_of_chainOK co3M1CommArrays (by norm_num) co3M1CommChain_check.1,
    co3M1CommChain_check.2]
  rfl

theorem co3Tt_not_mem_L :
    co3Tt ∉ co3L := by
  intro h
  have h1 : siftA 276 co3M1CommLevels co3M1CommBaseArr 0 co3TtArr = true :=
    (siftA_iff_mem_originalSubgroup co3M1CommArrays (by norm_num) co3M1CommChain_check.1
      rep_co3Tt).2 h
  rw [co3Second_check.2.1] at h1
  exact absurd h1 (by decide)

theorem rep_commA {n : ℕ} {gs : Array (Array ℕ)} {G : ℕ → Equiv.Perm (Fin n)}
    (hG : ∀ k < gs.size, Rep n gs[k]! (G k))
    (hinv : ∀ k < gs.size, isInvA n gs[k]! (invCand n gs[k]!) = true) {i j : ℕ}
    (hi : i < gs.size) (hj : j < gs.size) :
    Rep n (commA n gs i j) (G j * G i * (G j)⁻¹ * (G i)⁻¹) :=
  rep_compA (rep_compA (rep_compA (hG j hj) (hG i hi)) (rep_inv_of_isInvA (hG j hj) (hinv j hj)))
    (rep_inv_of_isInvA (hG i hi) (hinv i hi))

theorem co3L_le_M1 :
    co3L ≤ co3M1 := by
  rw [co3L, co3M1CommChain, ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨⟨k, hk3⟩, rfl⟩
  change k < 3 at hk3
  change permOfArr 276 co3M1CommArrs[k]! ∈ co3M1
  have hpairs : ∀ k < 3, (co3M1CommPairs.getD k (0, 0)).1 - 1 < 6 ∧
      (co3M1CommPairs.getD k (0, 0)).2 - 1 < 6 := by decide
  have hp := hpairs k hk3
  have hinv : ∀ k < co3M1Arrs.size, isInvA 276 co3M1Arrs[k]! (invCand 276 co3M1Arrs[k]!) = true :=
    fun k hk => isInvA_co3Field276 (f := 7) (by norm_num) hk
  have hrep := rep_commA (G := fun k => permOfArr 276 co3M1Arrs[k]!)
    (fun k hk => rep_co3M1Arr (by rw [co3M1Arrs_size] at hk; exact hk)) hinv
    (i := (co3M1CommPairs.getD k (0, 0)).1 - 1) (j := (co3M1CommPairs.getD k (0, 0)).2 - 1)
    (by rw [co3M1Arrs_size]; omega) (by rw [co3M1Arrs_size]; omega)
  have hmem : ∀ k < 6, permOfArr 276 co3M1Arrs[k]! ∈ co3M1 := fun k hk => by
    rw [co3M1_eq]; exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩
  have he := eq_of_eqA (rep_permOfArr (co3M1CommArrs_inv k (by rw [co3M1CommArrs_size]; omega))).1
    hrep (co3Second_check.1 k hk3)
  rw [he]
  exact co3M1.mul_mem (co3M1.mul_mem (co3M1.mul_mem (hmem _ hp.2) (hmem _ hp.1))
    (co3M1.inv_mem (hmem _ hp.2))) (co3M1.inv_mem (hmem _ hp.1))

@[expose] def co3L1 : Subgroup co3M1 := co3L.subgroupOf co3M1

@[expose] def co3Z1 :
    Subgroup co3M1 := Subgroup.zpowers co3TtM1

theorem co3L1_inf_ker :
    co3L1 ⊓ co3Kappa1.ker = ⊥ := by
  rw [co3Kappa1_ker, eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxZ⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxZ
  have h2 : co3TtM1 ^ 2 = 1 := by rw [← orderOf_co3TtM1, pow_orderOf_eq_one]
  have hk : co3TtM1 ^ k = co3TtM1 ^ (k % 2) := by
    rw [← zpow_mod_orderOf, orderOf_co3TtM1]
    norm_num
  rw [hk] at hxL ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero]; exact Subgroup.one_mem _
  · rw [h, zpow_one] at hxL
    exact absurd (Subgroup.mem_subgroupOf.1 hxL) co3Tt_not_mem_L

@[expose] def co3Kappa1L :
    co3L →* Equiv.Perm (Fin 12) :=
  co3Kappa1.comp (Subgroup.inclusion co3L_le_M1)

theorem co3Kappa1L_injective :
    Function.Injective co3Kappa1L := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hl' : co3Kappa1 (Subgroup.inclusion co3L_le_M1 l) = 1 := by
    rw [← MonoidHom.comp_apply]
    exact hl
  have hmem : Subgroup.inclusion co3L_le_M1 l ∈ co3L1 ⊓ co3Kappa1.ker :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 (by rw [Subgroup.coe_inclusion]; exact l.2), hl'⟩
  rw [co3L1_inf_ker, Subgroup.mem_bot] at hmem
  exact Subgroup.inclusion_injective co3L_le_M1 (hmem.trans (map_one _).symm)

theorem co3Kappa1L_range :
    co3Kappa1L.range = NativeSporadic.M12 := by
  have hle : co3Kappa1L.range ≤ NativeSporadic.M12 := by
    rintro _ ⟨l, rfl⟩
    rw [← co3Kappa1_range]
    exact ⟨Subgroup.inclusion co3L_le_M1 l, (MonoidHom.comp_apply _ _ _).symm⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [m12_card, ← card_co3L]
  exact (Nat.card_congr (MonoidHom.ofInjective co3Kappa1L_injective).toEquiv).le

@[expose] def co3LEquivM12 :
    co3L ≃* NativeSporadic.M12 :=
  (MonoidHom.ofInjective co3Kappa1L_injective).trans (MulEquiv.subgroupCongr co3Kappa1L_range)

theorem co3LEquivM12_apply
    (l : co3L) :
    (co3LEquivM12 l : Equiv.Perm (Fin 12)) = co3Kappa1 (Subgroup.inclusion co3L_le_M1 l) := rfl

theorem m12_not_comm : m12a * m12b ≠ m12b * m12a := by
  intro h
  obtain ⟨ha, hb, hab, -⟩ := at_m12_image_pair_count
  have := (Commute.orderOf_mul_eq_mul_orderOf_of_coprime h (by rw [ha, hb]; norm_num))
  rw [hab, ha, hb] at this
  omega

theorem m12_isPerfect :
    Group.IsPerfect NativeSporadic.M12 := by
  have hs : IsSimpleGroup NativeSporadic.M12 := fam_m12_simplicity.2.2
  refine ⟨?_⟩
  rcases (inferInstance : (commutator NativeSporadic.M12).Normal).eq_bot_or_eq_top with h | h
  · have hcomm := isMulCommutative_iff.mp ((commutator_eq_bot_iff NativeSporadic.M12).mp h)
    exact (m12_not_comm (hcomm m12a m12b)).elim
  · exact h

theorem m12_center :
    Subgroup.center NativeSporadic.M12 = ⊥ := by
  have hs : IsSimpleGroup NativeSporadic.M12 := fam_m12_simplicity.2.2
  rcases (inferInstance : (Subgroup.center NativeSporadic.M12).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply m12_not_comm
    have hb : m12b ∈ Subgroup.center NativeSporadic.M12 := h ▸ Subgroup.mem_top _
    exact (Subgroup.mem_center_iff.1 hb m12a)

theorem co3L_isPerfect :
    Group.IsPerfect co3L := by
  have := m12_isPerfect
  exact Group.IsPerfect.ofSurjective (f := co3LEquivM12.symm.toMonoidHom)
    co3LEquivM12.symm.surjective

theorem co3L_center :
    Subgroup.center co3L = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h : co3LEquivM12 x ∈ Subgroup.center NativeSporadic.M12 := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := co3LEquivM12.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [m12_center, Subgroup.mem_bot] at h
  rw [Subgroup.mem_bot]
  exact co3LEquivM12.injective (h.trans (map_one _).symm)

theorem co3Z1_le_center :
    co3Z1 ≤ Subgroup.center co3M1 := by
  rw [co3Z1, Subgroup.zpowers_le, Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.1 (co3M1_le_centralizer g.2)

theorem co3L1_inf_Z1 :
    co3L1 ⊓ co3Z1 = ⊥ := by
  rw [co3Z1, ← co3Kappa1_ker]
  exact co3L1_inf_ker

theorem card_co3L1 :
    Nat.card co3L1 = 95040 := by
  rw [co3L1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe co3L_le_M1).toEquiv, card_co3L]

theorem co3L1_index :
    co3L1.index = 2 := by
  have h := co3L1.card_mul_index
  rw [card_co3L1, card_co3M1] at h
  omega

theorem co3L1_normal :
    co3L1.Normal := Subgroup.normal_of_index_eq_two co3L1_index

theorem co3_xor_false_right {a : Prop} : Xor a False ↔ a := by
  rw [xor_def]
  simp

theorem co3L1_sup_Z1 :
    co3L1 ⊔ co3Z1 = ⊤ := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.1 co3L1_index
  have hta : co3TtM1 ∉ co3L1 := fun h => co3Tt_not_mem_L (Subgroup.mem_subgroupOf.1 h)
  rw [eq_top_iff]
  intro b _
  by_cases hb : b ∈ co3L1
  · exact Subgroup.mem_sup_left hb
  ·
    have hbt : b * co3TtM1 ∈ co3L1 := by
      have h1 := ha b
      have h2 := ha co3TtM1
      have h3 := ha (b * co3TtM1)
      by_contra hbt
      simp only [hb, hta, hbt, co3_xor_false_right] at h1 h2 h3
      have := co3L1.mul_mem h1 (co3L1.inv_mem h2)
      rw [show b * a * (co3TtM1 * a)⁻¹ = b * co3TtM1⁻¹ by group] at this
      have h2' : co3TtM1⁻¹ = co3TtM1 := by
        rw [inv_eq_iff_mul_eq_one, ← sq, ← orderOf_co3TtM1, pow_orderOf_eq_one]
      rw [h2'] at this
      exact hbt this
    have : b = (b * co3TtM1) * co3TtM1⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hbt)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))

instance co3L1_isPerfect :
    Group.IsPerfect co3L1 := by
  have := co3L_isPerfect
  exact Group.IsPerfect.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe co3L_le_M1).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe co3L_le_M1).symm.surjective

theorem co3L1_center :
    Subgroup.center co3L1 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  let e : co3L1 ≃* co3L := Subgroup.subgroupOfEquivOfLe co3L_le_M1
  have h : e x ∈ Subgroup.center co3L := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [co3L_center, Subgroup.mem_bot] at h
  rw [Subgroup.mem_bot]
  exact e.injective (h.trans (map_one _).symm)

instance co3Z1_isCyclic :
    IsCyclic co3Z1 := Subgroup.isCyclic_zpowers _

instance co3L1_outer_solvable :
    Group.IsSolvable (Outer co3L1) := by
  have e : co3L1 ≃* NativeSporadic.M12 :=
    (Subgroup.subgroupOfEquivOfLe co3L_le_M1).trans co3LEquivM12
  exact (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism e).2.2
    CFSG.Sporadic.Schreier.at_m12_schreier.2.2

theorem co3M1_outer_solvable :
    Group.IsSolvable (Outer co3M1) :=
  CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor.internal_outer_solvable
    co3L1 co3Z1 co3Z1_le_center co3L1_center co3L1_sup_Z1

theorem AT_Co3_second_centralizer_Schreier :
    (∀ (m : co3M1) (k : Fin 12),
      co3ItLab (co3Kappa1 m k) = (m : Equiv.Perm (Fin 276)) (co3ItLab k)) ∧
    co3Kappa1.range = NativeSporadic.M12 ∧ co3Kappa1.ker = Subgroup.zpowers co3TtM1 ∧
    Nat.card co3Kappa1.ker = 2 ∧ co3L ≤ co3M1 ∧
    (∃ e : co3L ≃* NativeSporadic.M12,
      ∀ l, (e l : Equiv.Perm (Fin 12)) = co3Kappa1 (Subgroup.inclusion co3L_le_M1 l)) ∧
    co3L1.Normal ∧ co3Z1 ≤ Subgroup.center co3M1 ∧ co3L1 ⊓ co3Z1 = ⊥ ∧ co3L1 ⊔ co3Z1 = ⊤ ∧
    Group.IsPerfect co3L ∧ Subgroup.center co3L = ⊥ ∧ Group.IsSolvable (Outer co3M1) :=
  ⟨co3ItLab_kappa1, co3Kappa1_range, co3Kappa1_ker, card_ker_co3Kappa1, co3L_le_M1,
    ⟨co3LEquivM12, co3LEquivM12_apply⟩, co3L1_normal, co3Z1_le_center, co3L1_inf_Z1,
    co3L1_sup_Z1, co3L_isPerfect, co3L_center, co3M1_outer_solvable⟩

end CFSG.Sporadic.Schreier.Co3
