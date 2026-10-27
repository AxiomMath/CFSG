module

public import CFSG.RankThree.PartOne.F106.F4Three
public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Facts
public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Tr
public import CFSG.RankThree.PartOne.F106.NoQD32NATabGen
public import CFSG.RankThree.PartOne.F106.NoQD32NANab

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits TauCeti CFSG.RankThree.PartOne.SEITZX Subgroup

section Table


variable {K : Type} [Field K] [CharP K 2] {c : F4SylowCert} {tb : ℕ → ℕ}

theorem F4SylowCert.tabArr_getD {i : ℕ} : c.tabArr.getD i 0 = c.tab.getD i 0 := by
  simp [F4SylowCert.tabArr, F4SylowCert.tab]

variable (hg : ∀ i < 729, tb i = c.tab.getD i 0) (hf : c.Facts)

include hg hf

theorem hasBits_sel' {i : ℕ} (hi : i < 729) : HasBits K (c.sel (X := K) i) (tb i) := by
  rw [hg i hi]
  exact hasBits_sel hf hi

theorem cubeF_iff {i : ℕ} (hi : i < 729) : cubeF tb i = true ↔ c.sel (X := K) i ^ 3 = 1 := by
  have b3 := ((hasBits_sel' (K := K) hg hf hi).mul (hasBits_sel' hg hf hi)).mul
    (hasBits_sel' hg hf hi)
  rw [cubeF, decide_eq_true_eq]
  have e : c.sel (X := K) i ^ 3 = 1 ↔ c.sel (X := K) i * c.sel i * c.sel i = 1 := by
    rw [pow_succ, sq]
  rw [e]
  exact (b3.eq_iff hasBits_one).symm

theorem commF_iff {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    commF tb i j = true ↔ c.sel (X := K) i * c.sel j = c.sel j * c.sel i := by
  rw [commF, decide_eq_true_eq]
  exact (((hasBits_sel' (K := K) hg hf hi).mul (hasBits_sel' hg hf hj)).eq_iff
    ((hasBits_sel' hg hf hj).mul (hasBits_sel' hg hf hi))).symm

omit hg in
theorem sel_mul_path (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3) :
    ∀ p : List ℕ, (∀ g ∈ p, g < 6) → ∀ i < 729, ∃ k < 729,
      c.sel (X := K) i * (p.map (c.gen (X := K))).prod = c.sel k ∧
        c.wt w k = (c.wt w i + (p.map fun g => w.getD g 0).sum) % 3 := by
  intro p
  induction p with
  | nil =>
    intro _ i hi
    refine ⟨i, hi, by simp, ?_⟩
    have : c.wt w i < 3 := Nat.mod_lt _ (by norm_num)
    simp only [List.map_nil, List.sum_nil]
    omega
  | cons g p ih =>
    intro hp i hi
    have hg6 : g < 6 := hp g (List.mem_cons_self ..)
    obtain ⟨k, hk, hk1, hk2⟩ := ih (fun g' hg' => hp g' (List.mem_cons_of_mem _ hg'))
      (c.rtv i g) (hf.rt i hi g hg6).1
    refine ⟨k, hk, ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, ← mul_assoc, sel_rt hf hi hg6, hk1]
    · rw [hk2, hw i hi g hg6, List.map_cons, List.sum_cons]
      omega

omit hg in
theorem wt_mul (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3)
    {i j k : ℕ} (hi : i < 729) (hj : j < 729) (hk : k < 729)
    (h : c.sel (X := K) i * c.sel j = c.sel k) : c.wt w k = (c.wt w i + c.wt w j) % 3 := by
  obtain ⟨k', hk', hk1, hk2⟩ := sel_mul_path (K := K) hf w hw (c.paths.getD j [])
    (hf.path _ (path_mem hf hj)) i hi
  have hsj : c.sel (X := K) j = ((c.paths.getD j []).map (c.gen (X := K))).prod := rfl
  rw [← hsj, h] at hk1
  have := sel_inj hf hk hk' hk1
  subst this
  rw [hk2]
  unfold F4SylowCert.wt
  omega

omit hg in
theorem wt_zero (w : List ℕ) : c.wt w 0 = 0 := by
  unfold F4SylowCert.wt
  rw [hf.zero]
  rfl

section Subgroups

variable [Finite (adjointGroup ReeTag.F4.tag K)]

omit hg in
@[expose] noncomputable def f4GTab : GTab (adjointGroup ReeTag.F4.tag K) := by
  have h := table_subgroup (fun k : Fin 6 => c.gen (X := K) k) (c.sel (X := K)) (sel_zero hf)
    (fun i hi j hj h => sel_inj hf hi hj h) (fun i hi => sel_mem_closure hf hi)
    (fun i hi k => ⟨c.rtv i k, (hf.rt i hi k k.2).1, sel_rt hf hi k.2⟩)
  exact ⟨c.sel (X := K), h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2,
    fun i hi j hj h => sel_inj hf hi hj h, sel_zero hf⟩

omit hg in
theorem exists_wt_subgroup (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3) :
    ∃ H : Subgroup (adjointGroup ReeTag.F4.tag K), H ≤ (f4GTab (K := K) hf).S ∧
      ∀ i < 729, c.sel (X := K) i ∈ H ↔ c.wt w i = 0 :=
  (f4GTab (K := K) hf).exists_subgroup (fun i => c.wt w i = 0) (wt_zero hf w)
    (fun i hi j hj k hk h hPi hPj => by
      rw [wt_mul hf w hw hi hj hk h, hPi, hPj])

omit hg in
theorem exists_wt_subgroup₂ (w₁ w₂ : List ℕ)
    (hw₁ : ∀ i < 729, ∀ g < 6, c.wt w₁ (c.rtv i g) = (c.wt w₁ i + w₁.getD g 0) % 3)
    (hw₂ : ∀ i < 729, ∀ g < 6, c.wt w₂ (c.rtv i g) = (c.wt w₂ i + w₂.getD g 0) % 3) :
    ∃ H : Subgroup (adjointGroup ReeTag.F4.tag K), H ≤ (f4GTab (K := K) hf).S ∧
      ∀ i < 729, c.sel (X := K) i ∈ H ↔ (c.wt w₁ i = 0 ∧ c.wt w₂ i = 0) :=
  (f4GTab (K := K) hf).exists_subgroup (fun i => c.wt w₁ i = 0 ∧ c.wt w₂ i = 0)
    ⟨wt_zero hf w₁, wt_zero hf w₂⟩
    (fun i hi j hj k hk h hPi hPj => by
      rw [wt_mul hf w₁ hw₁ hi hj hk h, wt_mul hf w₂ hw₂ hi hj hk h, hPi.1, hPj.1, hPi.2, hPj.2]
      exact ⟨rfl, rfl⟩)

omit hg in
noncomputable def f4Y (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3) :
    Subgroup (adjointGroup ReeTag.F4.tag K) :=
  (exists_wt_subgroup (K := K) hf w hw).choose

omit hg in
theorem f4Y_le (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3) :
    f4Y (K := K) hf w hw ≤ (f4GTab (K := K) hf).S :=
  (exists_wt_subgroup (K := K) hf w hw).choose_spec.1

omit hg in
theorem mem_f4Y (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3) {i : ℕ}
    (hi : i < 729) : c.sel (X := K) i ∈ f4Y (K := K) hf w hw ↔ c.wt w i = 0 :=
  (exists_wt_subgroup (K := K) hf w hw).choose_spec.2 i hi

omit hg in
noncomputable def f4Y₂ (w₁ w₂ : List ℕ)
    (hw₁ : ∀ i < 729, ∀ g < 6, c.wt w₁ (c.rtv i g) = (c.wt w₁ i + w₁.getD g 0) % 3)
    (hw₂ : ∀ i < 729, ∀ g < 6, c.wt w₂ (c.rtv i g) = (c.wt w₂ i + w₂.getD g 0) % 3) :
    Subgroup (adjointGroup ReeTag.F4.tag K) :=
  (exists_wt_subgroup₂ (K := K) hf w₁ w₂ hw₁ hw₂).choose

omit hg in
theorem f4Y₂_le (w₁ w₂ : List ℕ)
    (hw₁ : ∀ i < 729, ∀ g < 6, c.wt w₁ (c.rtv i g) = (c.wt w₁ i + w₁.getD g 0) % 3)
    (hw₂ : ∀ i < 729, ∀ g < 6, c.wt w₂ (c.rtv i g) = (c.wt w₂ i + w₂.getD g 0) % 3) :
    f4Y₂ (K := K) hf w₁ w₂ hw₁ hw₂ ≤ (f4GTab (K := K) hf).S :=
  (exists_wt_subgroup₂ (K := K) hf w₁ w₂ hw₁ hw₂).choose_spec.1

omit hg in
theorem mem_f4Y₂ (w₁ w₂ : List ℕ)
    (hw₁ : ∀ i < 729, ∀ g < 6, c.wt w₁ (c.rtv i g) = (c.wt w₁ i + w₁.getD g 0) % 3)
    (hw₂ : ∀ i < 729, ∀ g < 6, c.wt w₂ (c.rtv i g) = (c.wt w₂ i + w₂.getD g 0) % 3) {i : ℕ}
    (hi : i < 729) : c.sel (X := K) i ∈ f4Y₂ (K := K) hf w₁ w₂ hw₁ hw₂ ↔
      (c.wt w₁ i = 0 ∧ c.wt w₂ i = 0) :=
  (exists_wt_subgroup₂ (K := K) hf w₁ w₂ hw₁ hw₂).choose_spec.2 i hi

omit hg in
open scoped _root_.Classical in
theorem card_f4Y (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3) {n : ℕ}
    (hn : ((List.range 729).filter fun i => c.wt w i == 0).length = n) :
    Nat.card (f4Y (K := K) hf w hw) = n := by
  rw [(f4GTab (K := K) hf).card_eq _ (f4Y_le hf w hw),
    card_filter_range_eq_length 729 _ (fun i => c.wt w i == 0)
      (fun i hi => by
        change c.sel (X := K) i ∈ f4Y (K := K) hf w hw ↔ _
        rw [mem_f4Y hf w hw hi]
        simp)]
  exact hn

omit hg in
open scoped _root_.Classical in
theorem card_f4Y₂ (w₁ w₂ : List ℕ)
    (hw₁ : ∀ i < 729, ∀ g < 6, c.wt w₁ (c.rtv i g) = (c.wt w₁ i + w₁.getD g 0) % 3)
    (hw₂ : ∀ i < 729, ∀ g < 6, c.wt w₂ (c.rtv i g) = (c.wt w₂ i + w₂.getD g 0) % 3) {n : ℕ}
    (hn : ((List.range 729).filter fun i => c.wt w₁ i == 0 && c.wt w₂ i == 0).length = n) :
    Nat.card (f4Y₂ (K := K) hf w₁ w₂ hw₁ hw₂) = n := by
  rw [(f4GTab (K := K) hf).card_eq _ (f4Y₂_le hf w₁ w₂ hw₁ hw₂),
    card_filter_range_eq_length 729 _ (fun i => c.wt w₁ i == 0 && c.wt w₂ i == 0)
      (fun i hi => by
        change c.sel (X := K) i ∈ f4Y₂ (K := K) hf w₁ w₂ hw₁ hw₂ ↔ _
        rw [mem_f4Y₂ hf w₁ w₂ hw₁ hw₂ hi]
        simp)]
  exact hn

omit hg in
theorem f4GTab_sel : (f4GTab (K := K) hf).sel = c.sel (X := K) := rfl

omit hg in
theorem sel_ne_one_iff {i : ℕ} (hi : i < 729) : c.sel (X := K) i ≠ 1 ↔ i ≠ 0 := by
  constructor
  · rintro h rfl
    exact h (sel_zero hf)
  · intro hne heq
    exact hne (sel_inj hf hi (by norm_num) (heq.trans (sel_zero hf).symm))

section Facts

variable (hna : c.NAFacts tb)

include hna

theorem cube_cover {y : adjointGroup ReeTag.F4.tag K} (hy : y ∈ (f4GTab (K := K) hf).S)
    (hy3 : y ^ 3 = 1) :
    y ∈ f4Y (K := K) hf f4WA hna.homA ∨ y ∈ f4Y (K := K) hf f4WB hna.homB ∨
      y ∈ f4Y (K := K) hf f4WC hna.homC := by
  obtain ⟨i, hi, rfl⟩ := (f4GTab (K := K) hf).exists_sel y hy
  have h := (hna.cover i hi).1 ((cubeF_iff (K := K) hg hf hi).2 hy3)
  rcases h with h | h | h
  · exact Or.inl ((mem_f4Y hf _ _ hi).2 h)
  · exact Or.inr (Or.inl ((mem_f4Y hf _ _ hi).2 h))
  · exact Or.inr (Or.inr ((mem_f4Y hf _ _ hi).2 h))

theorem eq_E0_of_elemAbelian_f4 {E : Subgroup (adjointGroup ReeTag.F4.tag K)}
    (hES : E ≤ (f4GTab (K := K) hf).S) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hcube : ∀ a ∈ E, a ^ 3 = 1) (h81 : 81 ≤ Nat.card E) :
    E = f4Y₂ (K := K) hf f4WA f4WY2 hna.homA hna.homY2 := by
  refine (f4GTab (K := K) hf).eq_of_elemAbelian (card_f4Y₂ hf _ _ _ _ hna.cardE0)
    (fun i hi hcb hnm => ?_) hES hcomm hcube h81
  have hwt : ¬ (c.wt f4WA i = 0 ∧ c.wt f4WY2 i = 0) := fun h =>
    hnm ((mem_f4Y₂ hf _ _ hna.homA hna.homY2 hi).2 h)
  obtain ⟨C, hC1, hC2, hC3⟩ := hna.uniq i hi ((cubeF_iff (K := K) hg hf hi).2 hcb) hwt
  refine ⟨C, fun j => ?_, hC2, ?_⟩
  · constructor
    · intro hj
      obtain ⟨hj1, hj2, hj3⟩ := (hC1 j).1 hj
      exact ⟨hj1, (cubeF_iff (K := K) hg hf hj1).1 hj2, (commF_iff (K := K) hg hf hj1 hi).1 hj3⟩
    · rintro ⟨hj1, hj2, hj3⟩
      exact (hC1 j).2 ⟨hj1, (cubeF_iff (K := K) hg hf hj1).2 hj2,
        (commF_iff (K := K) hg hf hj1 hi).2 hj3⟩
  · rcases hC3 with hlt | ⟨x, hx, y, hy, hxy⟩
    · exact Or.inl hlt
    · refine Or.inr ⟨x, hx, y, hy, fun h => ?_⟩
      have hx' := ((hC1 x).1 hx).1
      have hy' := ((hC1 y).1 hy).1
      have := (commF_iff (K := K) hg hf hx' hy').2 h
      rw [this] at hxy
      exact Bool.noConfusion hxy

omit hna in
theorem sel_central_f4Y (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3) {z : ℕ}
    (hz : z < 729) (hmem : c.sel (X := K) z ∈ f4Y (K := K) hf w hw)
    (hcomm : ∀ j < 729, c.wt w j = 0 → commF tb z j = true) :
    (⟨c.sel (X := K) z, hmem⟩ : ↥(f4Y (K := K) hf w hw)) ∈
      Subgroup.center ↥(f4Y (K := K) hf w hw) := by
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨j, hj, hjy⟩ := (f4GTab (K := K) hf).exists_sel (y : adjointGroup ReeTag.F4.tag K)
    (f4Y_le hf w hw y.2)
  have hwj : c.wt w j = 0 := by
    have : c.sel (X := K) j ∈ f4Y (K := K) hf w hw := by
      rw [← f4GTab_sel (K := K) hf, ← hjy]
      exact y.2
    exact (mem_f4Y hf w hw hj).1 this
  have h := (commF_iff (K := K) hg hf hz hj).1 (hcomm j hj hwj)
  apply Subtype.ext
  change (y : adjointGroup ReeTag.F4.tag K) * c.sel z = c.sel z * (y : adjointGroup _ K)
  rw [hjy, f4GTab_sel (K := K) hf]
  exact h.symm

omit hna in
theorem nine_le_card_center (w : List ℕ)
    (hw : ∀ i < 729, ∀ g < 6, c.wt w (c.rtv i g) = (c.wt w i + w.getD g 0) % 3)
    (L : List ℕ) (hL : L.length = 9) (hnd : L.Nodup)
    (hcent : ∀ z ∈ L, z < 729 ∧ c.wt w z = 0 ∧
      ∀ j < 729, c.wt w j = 0 → commF tb z j = true) :
    9 ≤ Nat.card (Subgroup.center ↥(f4Y (K := K) hf w hw)) := by
  classical
  set Y := f4Y (K := K) hf w hw with hY
  let Z' : Subgroup (adjointGroup ReeTag.F4.tag K) := (Subgroup.center ↥Y).map Y.subtype
  have hmemZ : ∀ z ∈ L, c.sel (X := K) z ∈ (Z' : Set (adjointGroup ReeTag.F4.tag K)) := by
    intro z hz
    obtain ⟨hz1, hz2, hz3⟩ := hcent z hz
    have hmem : c.sel (X := K) z ∈ Y := (mem_f4Y hf w hw hz1).2 hz2
    exact ⟨⟨c.sel z, hmem⟩, sel_central_f4Y hg hf w hw hz1 hmem hz3, rfl⟩
  have hinj : ∀ x ∈ L, ∀ y ∈ L, c.sel (X := K) x = c.sel y → x = y := fun x hx y hy h =>
    sel_inj hf (hcent x hx).1 (hcent y hy).1 h
  have hnd' : (L.map (c.sel (X := K))).Nodup := hnd.map_on hinj
  let F : Finset (adjointGroup ReeTag.F4.tag K) := (L.map (c.sel (X := K))).toFinset
  have hF : F.card = 9 := by
    rw [List.toFinset_card_of_nodup hnd', List.length_map, hL]
  have hsub : (F : Set (adjointGroup ReeTag.F4.tag K)) ⊆ (Z' : Set _) := by
    intro g hg'
    simp only [F, Finset.mem_coe, List.mem_toFinset, List.mem_map] at hg'
    obtain ⟨z, hz, rfl⟩ := hg'
    exact hmemZ z hz
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hF] at h1
  have h2 : (Z' : Set (adjointGroup ReeTag.F4.tag K)).ncard = Nat.card (Subgroup.center ↥Y) := by
    rw [← Nat.card_coe_set_eq]
    exact Subgroup.card_map_of_injective Y.subtype_injective
  omega

theorem nine_le_card_center_Ya :
    9 ≤ Nat.card (Subgroup.center ↥(f4Y (K := K) hf f4WA hna.homA)) :=
  nine_le_card_center hg hf f4WA hna.homA f4ZaList hna.zaLen hna.zaNodup hna.zaCent

theorem nine_le_card_center_Yc :
    9 ≤ Nat.card (Subgroup.center ↥(f4Y (K := K) hf f4WC hna.homC)) :=
  nine_le_card_center hg hf f4WC hna.homC f4ZcList hna.zcLen hna.zcNodup hna.zcCent

open scoped _root_.Classical in
theorem card_trI_E0 :
    Nat.card {y : ↥(f4Y₂ (K := K) hf f4WA f4WY2 hna.homA hna.homY2) //
      (y : adjointGroup ReeTag.F4.tag K) ≠ 1 ∧
        trI (y : adjointGroup ReeTag.F4.tag K) = 0} = 24 := by
  set E0 := f4Y₂ (K := K) hf f4WA f4WY2 hna.homA hna.homY2 with hE0
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun g => g ∈ E0)
    (fun g : adjointGroup ReeTag.F4.tag K => g ≠ 1 ∧ trI g = 0))]
  have h := card_set_eq_filter (f4GTab (K := K) hf).S (f4GTab (K := K) hf).sel
    (fun g => g ∈ E0 ∧ (g ≠ 1 ∧ trI g = 0)) (f4GTab (K := K) hf).sel_inj
    (f4GTab (K := K) hf).exists_sel (f4GTab (K := K) hf).sel_mem
  have hset : {g : adjointGroup ReeTag.F4.tag K // g ∈ E0 ∧ (g ≠ 1 ∧ trI g = 0)} =
      {g : adjointGroup ReeTag.F4.tag K // g ∈ (f4GTab (K := K) hf).S ∧
        (g ∈ E0 ∧ (g ≠ 1 ∧ trI g = 0))} := by
    congr 1
    ext g
    constructor
    · intro hg'
      exact ⟨f4Y₂_le hf _ _ hna.homA hna.homY2 hg'.1, hg'⟩
    · intro hg'
      exact hg'.2
  rw [hset, h, card_filter_range_eq_length 729 _
    (fun i => c.wt f4WA i == 0 && c.wt f4WY2 i == 0 && decide (i ≠ 0) && !trIB (tb i))]
  · exact hna.a0count
  · intro i hi
    change (c.sel (X := K) i ∈ E0 ∧ (c.sel (X := K) i ≠ 1 ∧ trI (c.sel (X := K) i) = 0)) ↔ _
    rw [hE0, mem_f4Y₂ hf _ _ hna.homA hna.homY2 hi, sel_ne_one_iff hf hi,
      trI_eq_zero_iff (hasBits_sel' (K := K) hg hf hi)]
    simp [and_assoc]

omit hna in
theorem hasBits_sel_mul {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    HasBits K (c.sel (X := K) i * c.sel j) (mul (tb i) (tb j)) :=
  (hasBits_sel' (K := K) hg hf hi).mul (hasBits_sel' hg hf hj)

open scoped _root_.Classical in
theorem card_Qset_Yb (hZ : Nat.card (Subgroup.center ↥(f4Y (K := K) hf f4WB hna.homB)) = 3) :
    Nat.card (Qset (f4Y (K := K) hf f4WB hna.homB)
      (fun g : adjointGroup ReeTag.F4.tag K => ¬ trI g = 0)) = 24 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Yb := f4Y (K := K) hf f4WB hna.homB with hYb
  have hZlt : f4NaZ < 729 := by decide
  set z : adjointGroup ReeTag.F4.tag K := c.sel (X := K) f4NaZ with hz
  have hzmem : z ∈ Yb := (mem_f4Y hf _ _ hZlt).2 hna.zbWt
  let z0 : ↥Yb := ⟨z, hzmem⟩
  have hz0coe : (z0 : adjointGroup ReeTag.F4.tag K) = z := rfl
  have hz0c : z0 ∈ Subgroup.center ↥Yb :=
    sel_central_f4Y hg hf f4WB hna.homB hZlt hzmem hna.zbComm
  have hz03 : z0 ^ 3 = 1 := Subtype.ext ((cubeF_iff (K := K) hg hf hZlt).1 hna.zbCube)
  have hz01 : z0 ≠ 1 := fun h =>
    (sel_ne_one_iff hf hZlt).2 hna.zbNe (congrArg Subtype.val h)
  have hord : orderOf z0 = 3 := orderOf_eq_prime hz03 hz01
  have hle : Subgroup.zpowers z0 ≤ Subgroup.center ↥Yb := Subgroup.zpowers_le.mpr hz0c
  have hcardz : Nat.card (Subgroup.zpowers z0) = 3 := by rw [Nat.card_zpowers, hord]
  have hZeq : Subgroup.zpowers z0 = Subgroup.center ↥Yb :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hcardz])
  have hmem : ∀ x : ↥Yb, x ∈ Subgroup.center ↥Yb ↔ x = 1 ∨ x = z0 ∨ x = z0 * z0 := by
    intro x
    rw [← hZeq, mem_zpowers_iff_mem_range_orderOf, hord, Finset.mem_image]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      interval_cases k
      · exact Or.inl (pow_zero z0)
      · exact Or.inr (Or.inl (pow_one z0))
      · exact Or.inr (Or.inr (pow_two z0))
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by simp, pow_zero _⟩
      · exact ⟨1, by simp, pow_one _⟩
      · exact ⟨2, by simp, pow_two _⟩
  let QP : adjointGroup ReeTag.F4.tag K → Prop := fun g =>
    trI g = 0 ∧ trI (g * z) = 0 ∧ trI (g * z * z) = 0
  have hQ : ∀ y : ↥Yb, y ∈ Qset Yb (fun g : adjointGroup ReeTag.F4.tag K => ¬ trI g = 0) ↔
      QP (y : adjointGroup ReeTag.F4.tag K) := by
    intro y
    have e2 : ((y * (z0 * z0) : ↥Yb) : adjointGroup ReeTag.F4.tag K) = y * z * z := by
      rw [← mul_assoc]
      rfl
    constructor
    · intro hy
      refine ⟨?_, ?_, ?_⟩
      · have := mem_Qset.mp hy 1 (Subgroup.one_mem _)
        simpa using this
      · simpa using mem_Qset.mp hy z0 hz0c
      · have := mem_Qset.mp hy (z0 * z0) ((hmem _).mpr (Or.inr (Or.inr rfl)))
        rw [e2] at this
        simpa using this
    · rintro ⟨h1, h2, h3⟩
      refine mem_Qset.mpr fun c' hc' => ?_
      rcases (hmem c').mp hc' with rfl | rfl | rfl
      · simpa using h1
      · simpa using h2
      · rw [e2]
        simpa using h3
  rw [Nat.card_congr (Equiv.subtypeEquivRight hQ),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun g => g ∈ Yb) QP)]
  have h := card_set_eq_filter (f4GTab (K := K) hf).S (f4GTab (K := K) hf).sel
    (fun g => g ∈ Yb ∧ QP g) (f4GTab (K := K) hf).sel_inj
    (f4GTab (K := K) hf).exists_sel (f4GTab (K := K) hf).sel_mem
  have hset : {g : adjointGroup ReeTag.F4.tag K // g ∈ Yb ∧ QP g} =
      {g : adjointGroup ReeTag.F4.tag K // g ∈ (f4GTab (K := K) hf).S ∧ (g ∈ Yb ∧ QP g)} := by
    congr 1
    ext g
    constructor
    · intro hg'
      exact ⟨f4Y_le hf _ _ hg'.1, hg'⟩
    · intro hg'
      exact hg'.2
  rw [hset, h, card_filter_range_eq_length 729 _ (fun i => c.wt f4WB i == 0 && qF tb i)]
  · exact hna.qcount
  · intro i hi
    change (c.sel (X := K) i ∈ Yb ∧ QP (c.sel (X := K) i)) ↔ _
    have b0 := hasBits_sel' (K := K) hg hf hi
    have b1 := hasBits_sel_mul (K := K) hg hf hi hZlt
    have b2 := (b1.mul (hasBits_sel' (K := K) hg hf hZlt))
    rw [hYb, mem_f4Y hf _ _ hi]
    show _ ∧ (trI (c.sel i) = 0 ∧ trI (c.sel i * c.sel f4NaZ) = 0 ∧
      trI (c.sel i * c.sel f4NaZ * c.sel f4NaZ) = 0) ↔ _
    rw [trI_eq_zero_iff b0, trI_eq_zero_iff b1, trI_eq_zero_iff b2]
    simp only [qF, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', and_assoc]

end Facts

end Subgroups

end Table

end CFSG.RankThree.PartOne.F106
