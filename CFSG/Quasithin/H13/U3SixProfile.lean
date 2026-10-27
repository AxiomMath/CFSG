module

public import CFSG.Quasithin.H13.U3SixForm
public import CFSG.Quasithin.H13.U3SixTransport
public import Certificates.Certificate17021


public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin CFSG.Quasithin.SteinbergCB Matrix Module

theorem s0c_spec : s0c.length = 64 ∧ s0m 0 = id6 ∧ (∀ k < 64, canon6 (s0m k) = true) ∧
    s0c.Nodup :=
  Certificates.certificate17021.1

theorem s0tab_spec : ∀ i < 64, ∀ j < 64, tab i j < 64 ∧ mul6 (s0m i) (s0m j) = s0m (tab i j) :=
  Certificates.certificate17021.2.1

theorem s0c_closed : ∀ e ∈ s0c, ∀ c ∈ [u6c 0, u6c 1, u6c 2, dc], mul6 e c ∈ s0c :=
  Certificates.certificate17021.2.2.1

theorem tab_zero : ∀ i < 64, tab i 0 = i :=
  Certificates.certificate17021.2.2.2.1

theorem S0_eq_closure
    : S0 = Subgroup.closure
    ({dGL, rho6 u33Data.a, rho6 u33Data.b, rho6 u33Data.s} : Set (GL (Fin 6) (ZMod 2))) := by
  rw [S0, rhoT, OvergroupData.T, MonoidHom.map_closure, Subgroup.zpowers_eq_closure,
    ← Subgroup.closure_union]
  congr 1
  ext g
  simp only [Set.image_insert_eq, Set.image_singleton, Set.singleton_union]

theorem id6_mem_s0c : id6 ∈ s0c := by
  rw [← s0c_spec.2.1, s0m, List.getD_eq_getElem _ _ (by rw [s0c_spec.1]; norm_num)]
  exact List.getElem_mem _

theorem exists_s0_index
    {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ S0) :
    ∃ k < 64, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (s0m k) := by
  rw [S0_eq_closure] at hg
  have hS : ∀ x ∈ ({dGL, rho6 u33Data.a, rho6 u33Data.b, rho6 u33Data.s} :
      Set (GL (Fin 6) (ZMod 2))), ∃ c ∈ [u6c 0, u6c 1, u6c 2, dc],
        Units.coeHom (Matrix (Fin 6) (Fin 6) (ZMod 2)) x = colMat c := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact ⟨dc, by simp, rfl⟩
    · exact ⟨u6c 0, by simp, by rw [Units.coeHom_apply, rho6_abs.1]; rfl⟩
    · exact ⟨u6c 1, by simp, by rw [Units.coeHom_apply, rho6_abs.2.1]; rfl⟩
    · exact ⟨u6c 2, by simp, by rw [Units.coeHom_apply, rho6_abs.2.2.1]; rfl⟩
  obtain ⟨e, he, hge⟩ := mem_list_of_closure _ hS id6_mem_s0c s0c_closed g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  refine ⟨k, s0c_spec.1 ▸ hk, ?_⟩
  rw [Units.coeHom_apply] at hge
  rw [hge, s0m, List.getD_eq_getElem _ _ hk]

theorem s0m_injective {k k' : ℕ} (hk : k < 64) (hk' : k' < 64)
    (h : colMat (s0m k) = colMat (s0m k')) : k = k' := by
  have h1 := colMat_injective (s0c_spec.2.2.1 k hk) (s0c_spec.2.2.1 k' hk') h
  have hk1 : k < s0c.length := by rw [s0c_spec.1]; exact hk
  have hk1' : k' < s0c.length := by rw [s0c_spec.1]; exact hk'
  rw [s0m, s0m, List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk1'] at h1
  exact (List.Nodup.getElem_inj_iff s0c_spec.2.2.2).1 h1

theorem exists_s0_elem
    (k : ℕ) (hk : k < 64) :
    ∃ g ∈ S0, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (s0m k) := by
  classical
  let idx : S0 → Fin 64 := fun g =>
    ⟨(exists_s0_index g.2).choose, (exists_s0_index g.2).choose_spec.1⟩
  have hidx : ∀ g : S0, ((g : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      colMat (s0m (idx g)) := fun g => (exists_s0_index g.2).choose_spec.2
  have hinj : Function.Injective idx := by
    intro g g' h
    apply Subtype.ext
    apply Units.ext
    rw [hidx g, hidx g', h]
  have hbij : Function.Bijective idx :=
    hinj.bijective_of_nat_card_le (by rw [card_S0, Nat.card_fin])
  obtain ⟨g, hg⟩ := hbij.2 ⟨k, hk⟩
  refine ⟨g, g.2, ?_⟩
  rw [hidx g, hg]

noncomputable def s0GL
    (k : ℕ) : GL (Fin 6) (ZMod 2) :=
  if hk : k < 64 then (exists_s0_elem k hk).choose else 1

theorem s0GL_mem
    {k : ℕ} (hk : k < 64) : s0GL k ∈ S0 := by
  simp only [s0GL, hk, ↓reduceDIte]
  exact (exists_s0_elem k hk).choose_spec.1

theorem coe_s0GL
    {k : ℕ} (hk : k < 64) :
    (s0GL k : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (s0m k) := by
  simp only [s0GL, hk, ↓reduceDIte]
  exact (exists_s0_elem k hk).choose_spec.2

theorem eq_s0GL
    {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ S0) : ∃ k < 64, g = s0GL k := by
  obtain ⟨k, hk, hgk⟩ := exists_s0_index hg
  exact ⟨k, hk, Units.ext (by rw [hgk, coe_s0GL hk])⟩

theorem s0GL_inj
    {k k' : ℕ} (hk : k < 64) (hk' : k' < 64) (h : s0GL k = s0GL k') : k = k' :=
  s0m_injective hk hk' (by rw [← coe_s0GL hk, ← coe_s0GL hk', h])

theorem s0GL_mul
    {i j : ℕ} (hi : i < 64) (hj : j < 64) : s0GL i * s0GL j = s0GL (tab i j) := by
  apply Units.ext
  rw [Units.val_mul, coe_s0GL hi, coe_s0GL hj, ← colMat_mul6, (s0tab_spec i hi j hj).2,
    coe_s0GL (s0tab_spec i hi j hj).1]

theorem s0GL_zero :
    s0GL 0 = 1 :=
  Units.ext (by rw [coe_s0GL (by norm_num), s0c_spec.2.1, colMat_id6, Units.val_one])

noncomputable abbrev S0L
    : Subgroup (W6 ≃ₗ[ZMod 2] W6) := S0.map glLin.toMonoidHom

noncomputable def s0L
    (k : ℕ) : W6 ≃ₗ[ZMod 2] W6 := glLin (s0GL k)

theorem s0L_vecOf
    {k : ℕ} (hk : k < 64) (c : ℕ) : s0L k (vecOf c) = vecOf (vapp (s0m k) c) := by
  rw [s0L, glLin_apply, coe_s0GL hk, colMat_mulVec_vecOf]

theorem mem_S0L
    {g : W6 ≃ₗ[ZMod 2] W6} : g ∈ S0L ↔ ∃ k < 64, g = s0L k := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨k, hk, rfl⟩ := eq_s0GL hg'
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, s0GL_mem hk, rfl⟩

theorem s0L_mul
    {i j : ℕ} (hi : i < 64) (hj : j < 64) : s0L i * s0L j = s0L (tab i j) := by
  rw [s0L, s0L, s0L, ← map_mul, s0GL_mul hi hj]

theorem s0L_zero :
    s0L 0 = 1 := by
  rw [s0L, s0GL_zero, map_one]

theorem s0L_inj
    {k k' : ℕ} (hk : k < 64) (hk' : k' < 64) (h : s0L k = s0L k') : k = k' :=
  s0GL_inj hk hk' (glLin.injective h)

noncomputable def IE
    (E : Subgroup (W6 ≃ₗ[ZMod 2] W6)) : Finset ℕ := by
  classical
  exact (Finset.range 64).filter fun k => s0L k ∈ E

theorem mem_IE
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} {k : ℕ} : k ∈ IE E ↔ k < 64 ∧ s0L k ∈ E := by
  classical
  simp [IE]

theorem mem_iff_IE
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L)
    {g : W6 ≃ₗ[ZMod 2] W6} : g ∈ E ↔ ∃ k ∈ IE E, g = s0L k := by
  constructor
  · intro hg
    obtain ⟨k, hk, rfl⟩ := mem_S0L.1 (hE hg)
    exact ⟨k, mem_IE.2 ⟨hk, hg⟩, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (mem_IE.1 hk).2

theorem card_eq_IE
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) :
    Nat.card E = (IE E).card := by
  classical
  have hset : (E : Set (W6 ≃ₗ[ZMod 2] W6)) = ((IE E).image s0L : Set _) := by
    ext g
    simp only [SetLike.mem_coe, Finset.coe_image, Set.mem_image]
    rw [mem_iff_IE hE]
    exact ⟨fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩, fun ⟨k, hk, h⟩ => ⟨k, hk, h.symm⟩⟩
  have hinj : Set.InjOn s0L (IE E : Set ℕ) := fun k hk k' hk' h =>
    s0L_inj (mem_IE.1 hk).1 (mem_IE.1 hk').1 h
  have hc : Nat.card E = Nat.card (E : Set (W6 ≃ₗ[ZMod 2] W6)) := rfl
  rw [hc, Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]

theorem zero_mem_IE
    (E : Subgroup (W6 ≃ₗ[ZMod 2] W6)) : 0 ∈ IE E :=
  mem_IE.2 ⟨by norm_num, by rw [s0L_zero]; exact E.one_mem⟩

theorem tab_mem_IE
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} {i j : ℕ} (hi : i ∈ IE E) (hj : j ∈ IE E) :
    tab i j ∈ IE E := by
  obtain ⟨hi64, hiE⟩ := mem_IE.1 hi
  obtain ⟨hj64, hjE⟩ := mem_IE.1 hj
  refine mem_IE.2 ⟨(s0tab_spec i hi64 j hj64).1, ?_⟩
  rw [← s0L_mul hi64 hj64]
  exact E.mul_mem hiE hjE

theorem tab_self_of_elem
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hab : IsElementaryAbelian 2 E)
    {i : ℕ} (hi : i ∈ IE E) : tab i i = 0 := by
  obtain ⟨hi64, hiE⟩ := mem_IE.1 hi
  have h1 : s0L i ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hiE
  rw [pow_two, s0L_mul hi64 hi64, ← s0L_zero] at h1
  exact s0L_inj (s0tab_spec i hi64 i hi64).1 (by norm_num) h1

theorem tab_comm_of_elem
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hab : IsElementaryAbelian 2 E)
    {i j : ℕ} (hi : i ∈ IE E) (hj : j ∈ IE E) : tab i j = tab j i := by
  obtain ⟨hi64, hiE⟩ := mem_IE.1 hi
  obtain ⟨hj64, hjE⟩ := mem_IE.1 hj
  have h1 : s0L i * s0L j = s0L j * s0L i :=
    congrArg Subtype.val (hab.toIsMulCommutative.is_comm.comm ⟨_, hiE⟩ ⟨_, hjE⟩)
  rw [s0L_mul hi64 hj64, s0L_mul hj64 hi64] at h1
  exact s0L_inj (s0tab_spec i hi64 j hj64).1 (s0tab_spec j hj64 i hi64).1 h1

theorem eaMasks_spec : 1 ∈ eaMasks ∧ ∀ m ∈ eaMasks, m.testBit 0 = true :=
  Certificates.certificate17021.2.2.2.2.1

theorem eaMasks_ext : ∀ m ∈ eaMasks, ∀ i < 64, m.testBit i = false → tab i i = 0 →
    (∀ j < 64, m.testBit j = true → tab i j = tab j i) → extMask m i ∈ eaMasks :=
  Certificates.certificate17021.2.2.2.2.2.1

theorem testBit_foldr_ext (m i k : ℕ) (l : List ℕ) :
    (l.foldr (fun j acc => if m.testBit j then acc ||| 2 ^ tab i j else acc) m).testBit k = true ↔
      m.testBit k = true ∨ ∃ j ∈ l, m.testBit j = true ∧ tab i j = k := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons]
    by_cases h : m.testBit j = true
    · simp only [h, ↓reduceIte]
      rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro ((hk | ⟨j', hj', hmj', htj'⟩) | htk)
        · exact Or.inl hk
        · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', hmj', htj'⟩
        · exact Or.inr ⟨j, List.mem_cons_self .., h, htk⟩
      · rintro (hk | ⟨j', hj', hmj', htj'⟩)
        · exact Or.inl (Or.inl hk)
        · rcases List.mem_cons.1 hj' with rfl | hj'
          · exact Or.inr htj'
          · exact Or.inl (Or.inr ⟨j', hj', hmj', htj'⟩)
    · simp only [h, ↓reduceIte, Bool.false_eq_true]
      rw [ih]
      constructor
      · rintro (hk | ⟨j', hj', hmj', htj'⟩)
        · exact Or.inl hk
        · exact Or.inr ⟨j', List.mem_cons_of_mem _ hj', hmj', htj'⟩
      · rintro (hk | ⟨j', hj', hmj', htj'⟩)
        · exact Or.inl hk
        · rcases List.mem_cons.1 hj' with rfl | hj'
          · exact absurd hmj' h
          · exact Or.inr ⟨j', hj', hmj', htj'⟩

theorem mem_ofMask_extMask {m i k : ℕ} :
    k ∈ ofMask (extMask m i) ↔ k < 64 ∧ (m.testBit k = true ∨ ∃ j < 64, m.testBit j = true ∧
      tab i j = k) := by
  simp only [ofMask, Finset.mem_filter, Finset.mem_range, extMask, testBit_foldr_ext,
    List.mem_range]

theorem ofMask_one : ofMask 1 = {0} :=
  Certificates.certificate17021.2.2.2.2.2.2.1

theorem exists_mask_eq
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hab : IsElementaryAbelian 2 E) :
    ∃ m ∈ eaMasks, ofMask m = IE E := by
  classical
  set I := IE E
  let C := eaMasks.toFinset.filter fun m => ofMask m ⊆ I
  have h1C : (1 : ℕ) ∈ C := by
    refine Finset.mem_filter.2 ⟨List.mem_toFinset.2 eaMasks_spec.1, ?_⟩
    rw [ofMask_one, Finset.singleton_subset_iff]
    exact zero_mem_IE E
  obtain ⟨m, hmC, hmax⟩ := C.exists_max_image (fun m => (ofMask m).card) ⟨1, h1C⟩
  obtain ⟨hm, hsub⟩ := Finset.mem_filter.1 hmC
  have hm' : m ∈ eaMasks := List.mem_toFinset.1 hm
  refine ⟨m, hm', ?_⟩
  by_contra hne
  obtain ⟨i, hiI, him⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
  have hi64 : i < 64 := (mem_IE.1 hiI).1
  have hmi : m.testBit i = false := by
    cases h : m.testBit i
    · rfl
    · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_range.2 hi64, h⟩) him
  have hmemI : ∀ j < 64, m.testBit j = true → j ∈ I := fun j hj hjm =>
    hsub (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hjm⟩)
  have hext := eaMasks_ext m hm' i hi64 hmi (tab_self_of_elem hab hiI)
    (fun j hj hjm => tab_comm_of_elem hab hiI (hmemI j hj hjm))
  have hsub' : ofMask (extMask m i) ⊆ I := by
    intro k hk
    obtain ⟨hk64, hk | ⟨j, hj, hjm, rfl⟩⟩ := mem_ofMask_extMask.1 hk
    · exact hmemI k hk64 hk
    · exact tab_mem_IE hiI (hmemI j hj hjm)
  have hlt : (ofMask m).card < (ofMask (extMask m i)).card := by
    refine Finset.card_lt_card ⟨fun k hk => ?_, fun hle => him (hle ?_)⟩
    · obtain ⟨hk64, hkm⟩ := Finset.mem_filter.1 hk
      exact mem_ofMask_extMask.2 ⟨Finset.mem_range.1 hk64, Or.inl hkm⟩
    · refine mem_ofMask_extMask.2 ⟨hi64, Or.inr ⟨0, by norm_num, eaMasks_spec.2 m hm', ?_⟩⟩
      exact tab_zero i hi64
  have := hmax _ (Finset.mem_filter.2 ⟨List.mem_toFinset.2 hext, hsub'⟩)
  omega

theorem eaMasks_class : ∀ m ∈ eaMasks, m = 1 ∨ (eaGood.any fun x => x.1 == m) ∨
    (eaFail.any fun x => x.1 == m) :=
  Certificates.certificate17021.2.2.2.2.2.2.2.1

theorem eaFail_ok : ∀ x ∈ eaFail, failOK x = true :=
  Certificates.certificate17021.2.2.2.2.2.2.2.2.1

theorem eaGood_ok : ∀ x ∈ eaGood, goodOK x = true :=
  Certificates.certificate17021.2.2.2.2.2.2.2.2.2.1

theorem invol_rank : ∀ k < 64, k ≠ 0 → tab k k = 0 → 4 ≤ rangeCard k :=
  Certificates.certificate17021.2.2.2.2.2.2.2.2.2.2

theorem sub_eq_add_W6 (a b : W6) : a - b = a + b := by
  ext i
  simp only [Pi.sub_apply, Pi.add_apply]
  generalize a i = x
  generalize b i = y
  revert x y
  decide

theorem natCard_eq_of_vecOf {P : Submodule (ZMod 2) W6} {S : Finset ℕ} (hS : ∀ c ∈ S, c < 64)
    (hP : ∀ c < 64, vecOf c ∈ P ↔ c ∈ S) : Nat.card P = S.card := by
  have hset : (P : Set W6) = vecOf '' (S : Set ℕ) := by
    ext w
    obtain ⟨c, hc, rfl⟩ := exists_vecOf w
    simp only [SetLike.mem_coe, Set.mem_image]
    rw [hP c hc]
    constructor
    · intro h
      exact ⟨c, h, rfl⟩
    · rintro ⟨d, hd, hdc⟩
      rw [← vecOf_injective (hS d hd) hc hdc]
      exact hd
  have hinj : Set.InjOn vecOf (S : Set ℕ) := fun x hx y hy h =>
    vecOf_injective (hS x hx) (hS y hy) h
  change Nat.card ((P : Set W6)) = _
  rw [Nat.card_coe_set_eq, hset, hinj.ncard_image, Set.ncard_coe_finset]

theorem finrank_eq_of_natCard {P : Submodule (ZMod 2) W6} {n : ℕ} (h : Nat.card P = 2 ^ n) :
    finrank (ZMod 2) P = n := by
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
  rw [Nat.card_zmod, h] at h1
  exact (Nat.pow_right_injective le_rfl h1).symm

theorem vapp_s0m_lt
    {k : ℕ} (hk : k < 64) (c : ℕ) : vapp (s0m k) c < 64 := by
  have hcan := s0c_spec.2.2.1 k hk
  simp only [canon6, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hcan
  refine vapp_lt_of_foldr c _ fun j _ => ?_
  rw [List.getD_eq_getElem?_getD]
  cases h : (s0m k)[j]? with
  | none => norm_num
  | some x => exact hcan.2 x (List.mem_of_getElem? h)

theorem mem_linFix_IE
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) {m : ℕ}
    (hmE : ofMask m = IE E) {c : ℕ} (hc : c < 64) : vecOf c ∈ linFix E ↔ fixP m c = true := by
  rw [mem_linFix_iff, fixP, List.all_eq_true]
  constructor
  · intro h k hk
    rw [Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
    by_cases hmk : m.testBit k = true
    · right
      have hkE : k ∈ IE E := by
        rw [← hmE]
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (List.mem_range.1 hk), hmk⟩
      have h1 := h _ (mem_IE.1 hkE).2
      rw [s0L_vecOf (List.mem_range.1 hk)] at h1
      exact vecOf_injective (vapp_s0m_lt (List.mem_range.1 hk) c) hc h1
    · left
      exact Bool.eq_false_iff.2 hmk
  · intro h g hg
    obtain ⟨k, hk, rfl⟩ := (mem_iff_IE hE).1 hg
    rw [← hmE] at hk
    obtain ⟨hk64, hmk⟩ := Finset.mem_filter.1 hk
    have h1 := h k hk64
    rw [hmk, Bool.not_true, Bool.false_or, beq_iff_eq] at h1
    rw [s0L_vecOf (Finset.mem_range.1 hk64), h1]

theorem mem_range_s0L
    {k : ℕ} (hk : k < 64) {c : ℕ} (hc : c < 64) :
    vecOf c ∈ LinearMap.range (((s0L k : W6 ≃ₗ[ZMod 2] W6) : W6 →ₗ[ZMod 2] W6) - LinearMap.id) ↔
      c ∈ (Finset.range 64).image fun d => vapp (s0m k) d ^^^ d := by
  simp only [LinearMap.mem_range, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨d, hd, rfl⟩ := exists_vecOf w
    rw [s0L_vecOf hk, sub_eq_add_W6, ← vecOf_xor] at hw
    exact ⟨d, hd, vecOf_injective (Nat.xor_lt_two_pow (n := 6) (vapp_s0m_lt hk d) hd) hc hw⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨vecOf d, by rw [s0L_vecOf hk, sub_eq_add_W6, ← vecOf_xor]⟩

theorem natCard_range_s0L
    {k : ℕ} (hk : k < 64) :
    Nat.card (LinearMap.range (((s0L k : W6 ≃ₗ[ZMod 2] W6) : W6 →ₗ[ZMod 2] W6) -
      LinearMap.id)) = rangeCard k := by
  refine natCard_eq_of_vecOf ?_ fun c hc => mem_range_s0L hk hc
  intro c hc
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hc
  exact Nat.xor_lt_two_pow (n := 6) (vapp_s0m_lt hk d) (Finset.mem_range.1 hd)

theorem two_le_linRank_of_mem_S0L
    {e : W6 ≃ₗ[ZMod 2] W6} (he : e ∈ S0L) (hord : orderOf e = 2) :
    2 ≤ linRank e := by
  obtain ⟨k, hk, rfl⟩ := mem_S0L.1 he
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [s0L_zero, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hkk : tab k k = 0 := by
    have h1 : s0L k ^ 2 = 1 := by
      have h0 := pow_orderOf_eq_one (s0L k)
      rwa [hord] at h0
    rw [pow_two, s0L_mul hk hk, ← s0L_zero] at h1
    exact s0L_inj (s0tab_spec k hk k hk).1 (by norm_num) h1
  have hcard := natCard_range_s0L hk
  have h4 := invol_rank k hk hk0 hkk
  rw [linRank]
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.range (((s0L k : W6 ≃ₗ[ZMod 2] W6) : W6 →ₗ[ZMod 2] W6) - LinearMap.id))
  rw [Nat.card_zmod, hcard] at h1
  by_contra hlt
  push Not at hlt
  have : 2 ^ finrank (ZMod 2) (LinearMap.range (((s0L k : W6 ≃ₗ[ZMod 2] W6) :
      W6 →ₗ[ZMod 2] W6) - LinearMap.id)) ≤ 2 ^ 1 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem not_hyperCond_of_fail
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) {m h c k₀ : ℕ}
    (hmE : ofMask m = IE E) (hok : failOK (m, h, c, k₀) = true) : ¬ HyperCond E := by
  simp only [failOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨hh0, hc⟩, hk₀⟩, hmk₀⟩, hmove⟩, hcard⟩, hall⟩ := hok
  have hall' : ∀ i < 64, h.testBit i = true → m.testBit i = true ∧ tab i i = 0 ∧
      vapp (s0m i) c = c ∧ ∀ j < 64, h.testBit j = true → h.testBit (tab i j) = true := by
    intro i hi hhi
    rcases hall i hi with hni | ⟨⟨⟨hmi, hii⟩, hci⟩, hcl⟩
    · rw [hhi] at hni
      exact absurd hni (by decide)
    · refine ⟨hmi, hii, hci, fun j hj hhj => ?_⟩
      rcases hcl j hj with hnj | hjt
      · rw [hhj] at hnj
        exact absurd hnj (by decide)
      · exact hjt
  let B : Subgroup (W6 ≃ₗ[ZMod 2] W6) :=
    { carrier := {g | ∃ k < 64, h.testBit k = true ∧ g = s0L k}
      one_mem' := ⟨0, by norm_num, hh0, s0L_zero.symm⟩
      mul_mem' := by
        rintro _ _ ⟨i, hi, hhi, rfl⟩ ⟨j, hj, hhj, rfl⟩
        exact ⟨tab i j, (s0tab_spec i hi j hj).1, (hall' i hi hhi).2.2.2 j hj hhj,
          s0L_mul hi hj⟩
      inv_mem' := by
        rintro _ ⟨i, hi, hhi, rfl⟩
        refine ⟨i, hi, hhi, inv_eq_of_mul_eq_one_right ?_⟩
        rw [s0L_mul hi hi, (hall' i hi hhi).2.1, s0L_zero] }
  have hmemB : ∀ g, g ∈ B ↔ ∃ k < 64, h.testBit k = true ∧ g = s0L k := fun _ => Iff.rfl
  have hBE : B ≤ E := by
    rintro _ ⟨k, hk, hhk, rfl⟩
    have : k ∈ IE E := by
      rw [← hmE]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, (hall' k hk hhk).1⟩
    exact (mem_IE.1 this).2
  have hBS : B ≤ S0L := hBE.trans hE
  have hIB : IE B = ofMask h := by
    ext k
    rw [mem_IE, ofMask, Finset.mem_filter, Finset.mem_range, hmemB]
    constructor
    · rintro ⟨hk, k', hk', hhk', hkk'⟩
      rw [s0L_inj hk hk' hkk']
      exact ⟨hk', hhk'⟩
    · rintro ⟨hk, hhk⟩
      exact ⟨hk, k, hk, hhk, rfl⟩
  intro hH
  have hidx : B.relIndex E = 2 := by
    have h1 := card_mul_relIndex hBE
    rw [card_eq_IE hBS, card_eq_IE hE, hIB, ← hmE, hcard] at h1
    have hpos : 0 < (ofMask h).card :=
      Finset.card_pos.2 ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by norm_num), hh0⟩⟩
    nlinarith
  have hfix := hH B hBE hidx
  have hcB : vecOf c ∈ linFix B := by
    rw [mem_linFix_iff]
    rintro _ ⟨k, hk, hhk, rfl⟩
    rw [s0L_vecOf hk, (hall' k hk hhk).2.2.1]
  rw [hfix, mem_linFix_iff] at hcB
  have hk₀E : s0L k₀ ∈ E := by
    have : k₀ ∈ IE E := by
      rw [← hmE]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk₀, hmk₀⟩
    exact (mem_IE.1 this).2
  have h2 := hcB _ hk₀E
  rw [s0L_vecOf hk₀] at h2
  exact hmove (vecOf_injective (vapp_s0m_lt hk₀ c) hc h2)

theorem elemConclusion_of_good
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) {m k₂ : ℕ}
    (hmE : ofMask m = IE E) (hok : goodOK (m, k₂) = true) : ElemConclusion E := by
  simp only [goodOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq,
    List.all_eq_true, List.any_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
    at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hcard, hcomm⟩, hfixc⟩, hfixcard⟩, hmk₂⟩, hk₂0⟩, hk₂⟩, hr⟩ := hok
  have hmemm : ∀ k < 64, m.testBit k = true → s0L k ∈ E := by
    intro k hk hmk
    have : k ∈ IE E := by
      rw [← hmE]
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hmk⟩
    exact (mem_IE.1 this).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card_eq_IE hE, ← hmE, hcard]
  · apply le_antisymm
    ·
      intro v hv
      obtain ⟨c, hc, rfl⟩ := exists_vecOf v
      have hfc := (mem_linFix_IE hE hmE hc).1 hv
      rcases hfixc c hc with hnf | ⟨k, hk, hmk, d, hd, hdc⟩
      · rw [hfc] at hnf
        exact absurd hnf (by decide)
      · refine Submodule.subset_span ⟨s0L k, hmemm k hk hmk, vecOf d, ?_⟩
        rw [s0L_vecOf hk, sub_eq_add_W6, ← vecOf_xor, hdc]
    ·
      rw [linComm, Submodule.span_le]
      rintro _ ⟨g, hg, w, rfl⟩
      obtain ⟨k, hk, rfl⟩ := (mem_iff_IE hE).1 hg
      rw [← hmE] at hk
      obtain ⟨hk64, hmk⟩ := Finset.mem_filter.1 hk
      obtain ⟨d, hd, rfl⟩ := exists_vecOf w
      rw [SetLike.mem_coe, s0L_vecOf (Finset.mem_range.1 hk64), sub_eq_add_W6, ← vecOf_xor,
        mem_linFix_IE hE hmE (Nat.xor_lt_two_pow (n := 6)
          (vapp_s0m_lt (Finset.mem_range.1 hk64) d) hd)]
      rcases hcomm k (Finset.mem_range.1 hk64) with hnk | hall
      · rw [hmk] at hnk
        exact absurd hnk (by decide)
      · exact hall d hd
  · apply finrank_eq_of_natCard
    rw [natCard_eq_of_vecOf (S := (Finset.range 64).filter fun c => fixP m c = true)
      (fun c hc => Finset.mem_range.1 (Finset.mem_filter.1 hc).1) fun c hc => by
        rw [mem_linFix_IE hE hmE hc, Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩, hfixcard]
    norm_num
  · refine ⟨s0L k₂, hmemm k₂ hk₂ hmk₂, fun h => hk₂0 ?_, ?_⟩
    · rw [← s0L_zero] at h
      exact s0L_inj hk₂ (by norm_num) h
    · rw [linRank]
      apply finrank_eq_of_natCard
      rw [natCard_range_s0L hk₂, hr]
      norm_num

theorem elemConclusion_of_le_S0L
    {E : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hE : E ≤ S0L) (hE1 : E ≠ ⊥)
    (hab : IsElementaryAbelian 2 E) (hH : HyperCond E) : ElemConclusion E := by
  obtain ⟨m, hm, hmE⟩ := exists_mask_eq hab
  rcases eaMasks_class m hm with h1 | hgood | hfail
  · exfalso
    apply hE1
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨k, hk, rfl⟩ := (mem_iff_IE hE).1 hg
    rw [← hmE, h1, ofMask_one, Finset.mem_singleton] at hk
    rw [hk, s0L_zero]
    exact Subgroup.one_mem _
  · obtain ⟨⟨m', k₂⟩, hx, hxm⟩ := List.any_eq_true.1 hgood
    have hxm' : m' = m := beq_iff_eq.1 hxm
    subst hxm'
    exact elemConclusion_of_good hE hmE (eaGood_ok _ hx)
  · obtain ⟨⟨m', h, c, k₀⟩, hx, hxm⟩ := List.any_eq_true.1 hfail
    have hxm' : m' = m := beq_iff_eq.1 hxm
    subst hxm'
    exact absurd hH (not_hyperCond_of_fail hE hmE (eaFail_ok _ hx))

theorem exists_conj_le_S0
    {P : Subgroup (GL (Fin 6) (ZMod 2))} (hPN : P ≤ N6)
    (hP2 : IsPGroup 2 P) : ∃ n ∈ N6, ∀ g ∈ P, n⁻¹ * g * n ∈ S0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' := S0.subgroupOf N6 with hS'
  have hS'card : Nat.card S' = 64 := by
    rw [hS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_N6).toEquiv, card_S0]
  have hS'2 : IsPGroup 2 S' := IsPGroup.of_card (n := 6) (by rw [hS'card]; norm_num)
  have hS'idx : ¬ 2 ∣ S'.index := by
    have h := Subgroup.card_mul_index S'
    rw [hS'card, card_N6] at h
    have h189 : S'.index = 189 := by omega
    rw [h189]
    norm_num
  let Syl : Sylow 2 N6 := hS'2.toSylow hS'idx
  have hP'2 : IsPGroup 2 (P.subgroupOf N6) :=
    hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  obtain ⟨Q, hPQ⟩ := hP'2.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N6 Syl Q
  refine ⟨n, n.2, fun g hg => ?_⟩
  have hgQ : (⟨g, hPN hg⟩ : N6) ∈ (Q : Subgroup N6) := hPQ (Subgroup.mem_subgroupOf.2 hg)
  rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgQ
  have h1 : n⁻¹ * ⟨g, hPN hg⟩ * n ∈ S' := by
    have h0 : n⁻¹ * (⟨g, hPN hg⟩ * n) ∈ (Syl : Subgroup N6) := by
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hgQ
    rw [mul_assoc]
    exact h0
  have h2 := Subgroup.mem_subgroupOf.1 h1
  simpa using h2

noncomputable abbrev N6L
    : Subgroup (W6 ≃ₗ[ZMod 2] W6) := N6.map glLin.toMonoidHom

theorem glLin_conj (n g : GL (Fin 6) (ZMod 2)) :
    glLin (n⁻¹ * g * n) = linConj (glLin n⁻¹) (glLin g) := by
  ext x
  rw [linConj_apply, glLin_apply, glLin_apply, glLin_apply]
  have hsymm : (glLin n⁻¹).symm x = (n : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x := by
    rw [LinearEquiv.symm_apply_eq, glLin_apply, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hsymm, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem qtBinarySixProfile_of_le_N6L
    {Γ : Subgroup (W6 ≃ₗ[ZMod 2] W6)} (hΓ : Γ ≤ N6L) :
    QTBinarySixProfile b0 Γ := by
  refine ⟨Module.finrank_fin_fun _, b0_nondegenerate, b0_isAlt, ?_, ?_, ?_⟩
  · intro g hg x y
    obtain ⟨g₀, hg₀, rfl⟩ := hΓ hg
    rw [MulEquiv.coe_toMonoidHom, glLin_apply, glLin_apply]
    exact b0_mulVec_of_mem_b0Stab (N6_le_b0Stab hg₀) x y
  · intro e he hord
    obtain ⟨e₀, he₀, rfl⟩ := hΓ he
    have hord₀ : orderOf e₀ = 2 := by
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at hord
      exact hord
    have hP2 : IsPGroup 2 (Subgroup.zpowers e₀) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord₀, pow_one])
    obtain ⟨n, -, hconj⟩ := exists_conj_le_S0 (Subgroup.zpowers_le.2 he₀) hP2
    have hmem : glLin (n⁻¹ * e₀ * n) ∈ S0L :=
      ⟨_, hconj e₀ (Subgroup.mem_zpowers e₀), rfl⟩
    have hord' : orderOf (glLin (n⁻¹ * e₀ * n)) = 2 := by
      rw [glLin_conj, orderOf_linConj, MulEquiv.orderOf_eq, hord₀]
    have hrank := two_le_linRank_of_mem_S0L hmem hord'
    rwa [glLin_conj, linRank_linConj] at hrank
  · intro E hEΓ hE1 hab hH
    set E₀ := E.comap glLin.toMonoidHom with hE₀
    have hE₀N : E₀ ≤ N6 := by
      intro g hg
      obtain ⟨g', hg', hgg'⟩ := hEΓ.trans hΓ hg
      rw [← glLin.injective hgg']
      exact hg'
    have hE₀2 : IsPGroup 2 E₀ := by
      intro g
      refine ⟨1, Subtype.ext ?_⟩
      have h1 : glLin g ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ g.2
      apply glLin.injective
      rw [Subgroup.coe_pow, pow_one, map_pow, h1, Subgroup.coe_one, map_one]
    obtain ⟨n, -, hconj⟩ := exists_conj_le_S0 hE₀N hE₀2
    set Φ := glLin n⁻¹
    have hE' : E.map (linConj Φ).toMonoidHom ≤ S0L := by
      rintro _ ⟨g, hg, rfl⟩
      have hg₀ : glLin.symm g ∈ E₀ := by
        rw [hE₀, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        exact hg
      refine ⟨_, hconj _ hg₀, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, glLin_conj,
        MulEquiv.apply_symm_apply]
    have hE'1 : E.map (linConj Φ).toMonoidHom ≠ ⊥ := by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (linConj Φ).injective]
      exact hE1
    have hE'ab : IsElementaryAbelian 2 (E.map (linConj Φ).toMonoidHom) := by
      have := hab
      exact IsElementaryAbelian.map _
    exact elemConclusion_of_map_linConj Φ
      (elemConclusion_of_le_S0L hE' hE'1 hE'ab (hyperCond_map_linConj Φ hH))

end CFSG.Quasithin.H13.U3
