module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch210

open Subgroup

@[expose] def prodSub {ι : Type} (B : ι → Type) [∀ i, Group (B i)] (F : Finset ι) :
    Subgroup (∀ i, B i) where
  carrier := {s | ∀ j ∉ F, s j = 1}
  one_mem' := fun j _ => rfl
  mul_mem' := fun {a b} ha hb j hj => by simp [ha j hj, hb j hj]
  inv_mem' := fun {a} ha j hj => by simp [ha j hj]

structure SimpleFactors {ι : Type} (B : ι → Type) [∀ i, Group (B i)] : Prop where
  simple : ∀ i, IsSimpleGroup (B i)
  nonab : ∀ i, ∃ a b : B i, a * b ≠ b * a
  three_dvd : ∀ i, 3 ∣ Nat.card (B i)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {B : ι → Type} [∀ i, Group (B i)]
  [∀ i, Finite (B i)]

omit [Fintype ι] [DecidableEq ι] [∀ i, Finite (B i)] in
private lemma a210pi_prodSub_mono {F G : Finset ι} (h : F ⊆ G) :
    prodSub B F ≤ prodSub B G := by
  intro s hs j hj
  exact hs j fun hjF => hj (h hjF)

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210pi_mulSingle_mem_singleton {j : ι} (b : B j) :
    Pi.mulSingle j b ∈ prodSub B {j} := by
  intro l hl
  exact Pi.mulSingle_eq_of_ne (fun hlj => hl (Finset.mem_singleton.mpr hlj)) b

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210pi_mulSingle_mem_prodSub {F : Finset ι} {j : ι} (hj : j ∈ F) (b : B j) :
    Pi.mulSingle j b ∈ prodSub B F :=
  a210pi_prodSub_mono (Finset.singleton_subset_iff.mpr hj) (a210pi_mulSingle_mem_singleton b)

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210pi_eq_mulSingle_of_mem_singleton {j : ι} {y : ∀ i, B i}
    (hy : y ∈ prodSub B {j}) : y = Pi.mulSingle j (y j) := by
  funext l
  by_cases hl : l = j
  · subst hl; rw [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hl]
    exact hy l (by simpa [Finset.mem_singleton] using hl)

omit [Fintype ι] [DecidableEq ι] [∀ i, Finite (B i)] in
private lemma a210pi_not_isMulCommutative (hB : SimpleFactors B) (j : ι) :
    ¬ IsMulCommutative (B j) := by
  intro hc
  obtain ⟨a, b, hab⟩ := hB.nonab j
  exact hab (hc.is_comm.comm a b)

omit [Fintype ι] [DecidableEq ι] [∀ i, Finite (B i)] in
private lemma a210pi_isPerfect (hB : SimpleFactors B) (j : ι) : Group.IsPerfect (B j) := by
  have : IsSimpleGroup (B j) := hB.simple j
  rw [Group.isPerfect_def]
  refine (Subgroup.Normal.eq_bot_or_eq_top (commutator (B j))).resolve_left ?_
  intro hb
  exact a210pi_not_isMulCommutative hB j ((commutator_eq_bot_iff (G := B j)).mp hb)

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210pi_range_mulSingle (j : ι) :
    (MonoidHom.mulSingle B j).range = prodSub B {j} := by
  apply le_antisymm
  · rintro y ⟨b, rfl⟩
    exact a210pi_mulSingle_mem_singleton b
  · intro y hy
    exact ⟨y j, (a210pi_eq_mulSingle_of_mem_singleton hy).symm⟩

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210pi_single_mem_commutator (hB : SimpleFactors B) {F : Finset ι} {j : ι}
    (hj : j ∈ F) (b : B j) :
    Pi.mulSingle j b ∈ ⁅prodSub B F, prodSub B F⁆ := by
  have hle : prodSub B {j} ≤ prodSub B F :=
    a210pi_prodSub_mono (Finset.singleton_subset_iff.mpr hj)
  have hmap : (commutator (B j)).map (MonoidHom.mulSingle B j) =
      ⁅prodSub B {j}, prodSub B {j}⁆ := by
    rw [show commutator (B j) = ⁅(⊤ : Subgroup (B j)), ⊤⁆ from rfl, Subgroup.map_commutator,
      Subgroup.map_top, a210pi_range_mulSingle]
  have hb : b ∈ commutator (B j) := by
    rw [(a210pi_isPerfect hB j).commutator_eq_top]; trivial
  have hb' : MonoidHom.mulSingle B j b ∈ (commutator (B j)).map (MonoidHom.mulSingle B j) :=
    Subgroup.mem_map_of_mem _ hb
  rw [hmap] at hb'
  exact Subgroup.commutator_mono hle hle hb'

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210pi_prodSub_le_commutator (hB : SimpleFactors B) (F : Finset ι) :
    prodSub B F ≤ ⁅prodSub B F, prodSub B F⁆ := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      intro x hx
      have hx1 : x = 1 := by
        funext j
        exact hx j (Finset.notMem_empty j)
      rw [hx1]
      exact Subgroup.one_mem _
  | insert j s hjs ih =>
      intro x hx
      have hx_eq : x = Pi.mulSingle j (x j) * ((Pi.mulSingle j (x j))⁻¹ * x) := by group
      rw [hx_eq]
      have h1 : Pi.mulSingle j (x j) ∈ ⁅prodSub B (insert j s), prodSub B (insert j s)⁆ :=
        a210pi_single_mem_commutator hB (Finset.mem_insert_self j s) (x j)
      have hzsub : (Pi.mulSingle j (x j))⁻¹ * x ∈ prodSub B s := by
        intro l hl
        by_cases hlj : l = j
        · subst hlj; simp
        · have hxl : x l = 1 := hx l (by
            simp only [Finset.mem_insert, not_or]
            exact ⟨hlj, hl⟩)
          simp [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hlj, hxl]
      have h2 : (Pi.mulSingle j (x j))⁻¹ * x ∈
          ⁅prodSub B (insert j s), prodSub B (insert j s)⁆ :=
        Subgroup.commutator_mono (a210pi_prodSub_mono (Finset.subset_insert j s))
          (a210pi_prodSub_mono (Finset.subset_insert j s)) (ih hzsub)
      exact (⁅prodSub B (insert j s), prodSub B (insert j s)⁆).mul_mem h1 h2

omit [Fintype ι] [DecidableEq ι] [∀ i, Finite (B i)] in
private lemma a210pi_center_eq_bot (hB : SimpleFactors B) (j : ι) :
    Subgroup.center (B j) = ⊥ := by
  have : IsSimpleGroup (B j) := hB.simple j
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (B j)) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h) (a210pi_not_isMulCommutative hB j)

omit [Fintype ι] [∀ i, Finite (B i)] in
private lemma a210pi_conj_commutator_mulSingle {j : ι} (c : B j) (n : ∀ i, B i) :
    Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹ =
      Pi.mulSingle j (c * n j * c⁻¹ * (n j)⁻¹) := by
  funext l
  by_cases hl : l = j
  · subst hl
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hl]
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hl, inv_one, mul_one, one_mul]
    group

omit [Fintype ι] [∀ i, Finite (B i)] in
theorem SimpleFactors.perfect_prodSub (hB : SimpleFactors B) (F : Finset ι) :
    Group.IsPerfect ↥(prodSub B F) := by
  rw [Subgroup.isPerfect_iff]
  exact le_antisymm (Subgroup.commutator_le_self _) (a210pi_prodSub_le_commutator hB F)

omit [Fintype ι] [∀ i, Finite (B i)] in
theorem SimpleFactors.exists_single_le_of_normal (hB : SimpleFactors B) {F : Finset ι}
    {N : Subgroup (∀ i, B i)} (hNF : N ≤ prodSub B F)
    (hN : ∀ s ∈ prodSub B F, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hne : N ≠ ⊥) :
    ∃ j ∈ F, prodSub B {j} ≤ N := by
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one N with h | h
    · exact absurd h hne
    · exact h
  obtain ⟨j, hnj⟩ : ∃ j, n j ≠ 1 := by
    by_contra h
    apply hn1
    funext i
    exact not_not.mp (not_exists.mp h i)
  have hjF : j ∈ F := by
    by_contra hj
    exact hnj (hNF hnN j hj)
  have : IsSimpleGroup (B j) := hB.simple j
  have hZ : Subgroup.center (B j) = ⊥ := a210pi_center_eq_bot hB j
  have hnc : n j ∉ Subgroup.center (B j) := by
    rw [hZ]
    exact fun h => hnj (Subgroup.mem_bot.mp h)
  rw [Subgroup.mem_center_iff] at hnc
  obtain ⟨c, hc⟩ := not_forall.mp hnc
  have hcomm : c * n j * c⁻¹ * (n j)⁻¹ ≠ 1 := by
    intro h
    apply hc
    calc c * n j = c * n j * c⁻¹ * (n j)⁻¹ * (n j * c) := by group
      _ = 1 * (n j * c) := by rw [h]
      _ = n j * c := by group
  let Nj : Subgroup (B j) := N.comap (MonoidHom.mulSingle B j)
  have hle : prodSub B {j} ≤ prodSub B F :=
    a210pi_prodSub_mono (Finset.singleton_subset_iff.mpr hjF)
  have hsj : Pi.mulSingle j c ∈ prodSub B F := a210pi_mulSingle_mem_prodSub hjF c
  have ht1N : Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹ ∈ N :=
    N.mul_mem (hN (Pi.mulSingle j c) hsj n hnN) (N.inv_mem hnN)
  have ht_eq : Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹ =
      Pi.mulSingle j (c * n j * c⁻¹ * (n j)⁻¹) :=
    a210pi_conj_commutator_mulSingle c n
  have htj : (Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹) j =
      c * n j * c⁻¹ * (n j)⁻¹ := by
    rw [ht_eq, Pi.mulSingle_eq_same]
  have htj_ne : (Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹) j ≠ 1 := by
    rw [htj]; exact hcomm
  have htNj : (Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹) j ∈ Nj := by
    show (Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹) j ∈
      N.comap (MonoidHom.mulSingle B j)
    rw [Subgroup.mem_comap, htj]
    show Pi.mulSingle j (c * n j * c⁻¹ * (n j)⁻¹) ∈ N
    rw [← ht_eq]
    exact ht1N
  have hNj_ne_bot : Nj ≠ ⊥ := by
    intro hbot
    have : (Pi.mulSingle j c * n * (Pi.mulSingle j c)⁻¹ * n⁻¹) j = 1 := by
      rw [Subgroup.eq_bot_iff_forall] at hbot
      exact hbot _ htNj
    exact htj_ne this
  have hNj_normal : Nj.Normal := by
    show (N.comap (MonoidHom.mulSingle B j)).Normal
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_comap] at hx ⊢
    change Pi.mulSingle j x ∈ N at hx
    show Pi.mulSingle j (g * x * g⁻¹) ∈ N
    rw [Pi.mulSingle_mul, Pi.mulSingle_mul, Pi.mulSingle_inv]
    exact hN (Pi.mulSingle j g) (a210pi_mulSingle_mem_prodSub hjF g) (Pi.mulSingle j x) hx
  have hNj_top : Nj = ⊤ := by
    have : Nj.Normal := hNj_normal
    exact (Subgroup.Normal.eq_bot_or_eq_top Nj).resolve_left hNj_ne_bot
  refine ⟨j, hjF, ?_⟩
  intro y hy
  have hyj : y j ∈ Nj := by rw [hNj_top]; trivial
  rw [a210pi_eq_mulSingle_of_mem_singleton hy]
  show MonoidHom.mulSingle B j (y j) ∈ N
  exact hyj

omit [Fintype ι] in
theorem SimpleFactors.eq_bot_of_pGroup (hB : SimpleFactors B) {F : Finset ι}
    {N : Subgroup (∀ i, B i)} (hNF : N ≤ prodSub B F)
    (hN : ∀ s ∈ prodSub B F, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (h3 : IsPGroup 3 ↥N) : N = ⊥ := by
  by_contra hne
  obtain ⟨j, hjF, hle⟩ := SimpleFactors.exists_single_le_of_normal hB hNF hN hne
  have : IsSimpleGroup (B j) := hB.simple j
  have hSingle : IsPGroup 3 ↥(prodSub B {j}) := IsPGroup.to_le h3 hle
  have hBj : IsPGroup 3 (B j) := by
    have hm := hSingle.map (Pi.evalMonoidHom B j)
    have htop : (prodSub B {j}).map (Pi.evalMonoidHom B j) = ⊤ := by
      rw [eq_top_iff]
      intro b _
      exact ⟨Pi.mulSingle j b, a210pi_mulSingle_mem_singleton b, Pi.mulSingle_eq_same j b⟩
    rw [htop] at hm
    exact hm.of_equiv Subgroup.topEquiv
  have hZ : Subgroup.center (B j) = ⊥ := a210pi_center_eq_bot hB j
  have hlt : (⊥ : Subgroup (B j)) < Subgroup.center (B j) := hBj.bot_lt_center
  rw [hZ] at hlt
  exact lt_irrefl _ hlt

omit [Fintype ι] [∀ i, Finite (B i)] in
theorem SimpleFactors.exists_normal_not_top_not_central (hB : SimpleFactors B) {F : Finset ι}
    (h2 : 2 ≤ F.card) :
    ∃ N : Subgroup ↥(prodSub B F), N.Normal ∧ N ≠ ⊤ ∧ ¬ N ≤ Subgroup.center ↥(prodSub B F) := by
  obtain ⟨i, hiF, j, hjF, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  have : IsSimpleGroup (B j) := hB.simple j
  have hHnormal : (prodSub B {i}).Normal := by
    refine ⟨fun x hx g => ?_⟩
    intro l hl
    have hxl : x l = 1 := hx l hl
    simp [Pi.mul_apply, Pi.inv_apply, hxl]
  refine ⟨(prodSub B {i}).subgroupOf (prodSub B F), hHnormal.subgroupOf (prodSub B F), ?_, ?_⟩
  · intro htop
    obtain ⟨b, hb⟩ : ∃ b : B j, b ≠ 1 := exists_ne (1 : B j)
    have hmem : (⟨Pi.mulSingle j b, a210pi_mulSingle_mem_prodSub hjF b⟩ : ↥(prodSub B F)) ∈
        (prodSub B {i}).subgroupOf (prodSub B F) := by
      rw [htop]; trivial
    rw [Subgroup.mem_subgroupOf] at hmem
    have hbj : (Pi.mulSingle j b) j = 1 :=
      hmem j (by simpa [Finset.mem_singleton] using hij.symm)
    rw [Pi.mulSingle_eq_same] at hbj
    exact hb hbj
  · intro hle
    obtain ⟨a, b, hab⟩ := hB.nonab i
    let x : ↥(prodSub B F) := ⟨Pi.mulSingle i a, a210pi_mulSingle_mem_prodSub hiF a⟩
    let y : ↥(prodSub B F) := ⟨Pi.mulSingle i b, a210pi_mulSingle_mem_prodSub hiF b⟩
    have hxN : x ∈ (prodSub B {i}).subgroupOf (prodSub B F) := by
      rw [Subgroup.mem_subgroupOf]
      show Pi.mulSingle i a ∈ prodSub B {i}
      exact a210pi_mulSingle_mem_singleton a
    have hyN : y ∈ (prodSub B {i}).subgroupOf (prodSub B F) := by
      rw [Subgroup.mem_subgroupOf]
      show Pi.mulSingle i b ∈ prodSub B {i}
      exact a210pi_mulSingle_mem_singleton b
    have hxcen : x ∈ Subgroup.center ↥(prodSub B F) := hle hxN
    have hcomm := (Subgroup.mem_center_iff.mp hxcen) y
    have hcongr := congrArg (fun z : ↥(prodSub B F) => z.1 i) hcomm
    dsimp only [x, y] at hcongr
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Subgroup.coe_mul] at hcongr
    exact hab hcongr.symm

end CFSG.LocalAnalysis.WeakClosure81.Asch210
