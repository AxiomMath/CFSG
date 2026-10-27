module

public import CFSG.Sporadic.SuzRecog.C1ModelCert
public import CFSG.Sporadic.SuzRecog.ModelBase
public import CFSG.Sporadic.SuzRecog.LocalRFusionModel
public import CFSG.Sporadic.SuzRecog.Fibre
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check

public section

set_option linter.unusedSectionVars false

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.C1Model

open Subgroup CFSG.ComponentClassification.AS81.SuzB0 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog

@[expose] noncomputable def gc : Equiv.Perm (Fin 1782) := wPerm [6, 9, 2]

@[expose] noncomputable def r1 : Equiv.Perm (Fin 1782) := Model.rho1 * Model.w0 * Model.rho1⁻¹

@[expose] noncomputable def r2 : Equiv.Perm (Fin 1782) := Model.rho1 * r1 * Model.rho1⁻¹

@[expose] noncomputable def tau0 : Equiv.Perm (Fin 1782) := wPerm [5, 8, 6, 7, 4] * qVec 23

@[expose] noncomputable def bw : Equiv.Perm (Fin 1782) := gc * (suzB0 * suzB1) * gc⁻¹

@[expose] noncomputable def cw : Equiv.Perm (Fin 1782) := Model.w0 * bw * Model.w0 * bw⁻¹

@[expose] noncomputable def zJ0 : Equiv.Perm (Fin 1782) := (bw⁻¹ * cw ^ 7) ^ 2

@[expose] noncomputable def hB : Equiv.Perm (Fin 1782) :=
  (Model.w0 * ((suzB0 * suzB1) * suzB0 * (suzB0 * suzB1)⁻¹)) ^ 8 * (suzB0 * suzB1)

@[expose] noncomputable def decPerm (d : List ℕ × ℕ) : Equiv.Perm (Fin 1782) := wPerm d.1 * qE d.2

theorem tabRep_comp' {n : ℕ} {t s : Tab} {g h : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hs : Rep n s h) : TabRep (comp n t s) (g * h) :=
  ⟨Array.size_ofFn, fun i => by
    rw [TabRep.comp_getElem!, hs i, ht (h i), Equiv.Perm.mul_apply]⟩

theorem cWord_size (w : List ℕ) : (cWord w).size = 1782 := by
  cases w with
  | nil =>
    rw [cWord, List.foldr_nil]
    exact Array.size_ofFn
  | cons k w =>
    rw [cWord, List.foldr_cons]
    exact Array.size_ofFn

theorem tabRep_cWord {w : List ℕ} (hw : ∀ k ∈ w, k < 10) :
    TabRep (cWord w) (wPerm w) :=
  ⟨cWord_size w, rep_cWord hw⟩

theorem tabRep_decTab
    {d : List ℕ × ℕ} (hw : ∀ k ∈ d.1, k < 10) (hj : d.2 < 128) :
    TabRep (decTab d) (decPerm d) :=
  tabRep_comp' (rep_cWord hw) (rep_qE hj)

theorem tabRep_wordTab {n : ℕ} {gens : Array Tab} {f : ℕ → Equiv.Perm (Fin n)}
    (hf : ∀ k < gens.size, Rep n gens[k]! (f k)) :
    ∀ w : List ℕ, (∀ k ∈ w, k < gens.size) → TabRep (wordTab n gens w) (w.map f).prod
  | [], _ => TabRep.idTab
  | k :: w, hw => by
    rw [List.map_cons, List.prod_cons]
    exact tabRep_comp' (hf k (hw k List.mem_cons_self))
      (tabRep_wordTab hf w fun j hj => hw j (List.mem_cons_of_mem k hj)).2

theorem getElem!_pair_zero {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[0]! = a := rfl

theorem getElem!_pair_one {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[1]! = b := rfl

theorem wordProd_mem {G : Type*} [Group G] {K : Subgroup G} {f : ℕ → G} (hf : ∀ k, f k ∈ K)
    (w : List ℕ) : (w.map f).prod ∈ K :=
  list_prod_mem fun x hx => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact hf k

theorem mem_closure_pair_iff {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {g : G} :
    g ∈ closure ({a, b} : Set G) ↔ g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have hba : b * a = a * b := hab.symm
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have e3 : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [mul_assoc, e2, ha]
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have iab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right e5
  constructor
  · intro hg
    induction hg using closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [one_mul, mul_one, ha, hb, hba, e1, e2, e3, e4, e5, true_or, or_true]
    | inv x _ hx =>
      rcases hx with rfl | rfl | rfl | rfl
      · exact Or.inl inv_one
      · exact Or.inr (Or.inl ia)
      · exact Or.inr (Or.inr (Or.inl ib))
      · exact Or.inr (Or.inr (Or.inr iab))
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ rfl))

theorem mem_normalizer_of_forall_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H]
    {x : G} (key : ∀ y ∈ H, x * y * x⁻¹ ∈ H) : x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key y, fun hy => ?_⟩
  let f : H → H := fun z => ⟨x * z * x⁻¹, key z z.2⟩
  have hf : Function.Injective f := fun z z' hzz' => Subtype.ext (by
    have := congrArg Subtype.val hzz'
    simpa [f] using this)
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x * y * x⁻¹, hy⟩
  have : (z : G) = y := by
    have := congrArg Subtype.val hz
    simpa [f] using this
  exact this ▸ z.2

theorem card_centralizer_inf_conj {G : Type*} [Group G] (K : Subgroup G) {c : G} (hc : c ∈ K)
    (x : G) : Nat.card ↥(centralizer ({c * x * c⁻¹} : Set G) ⊓ K) =
      Nat.card ↥(centralizer ({x} : Set G) ⊓ K) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨c⁻¹ * y * c, mem_inf.mpr ⟨?_,
        mul_mem (mul_mem (inv_mem hc) (mem_inf.mp y.2).2) hc⟩⟩
      invFun := fun y => ⟨c * y * c⁻¹, mem_inf.mpr ⟨?_,
        mul_mem (mul_mem hc (mem_inf.mp y.2).2) (inv_mem hc)⟩⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }
  · have h := mem_centralizer_singleton_iff.1 (mem_inf.mp y.2).1
    rw [mem_centralizer_singleton_iff]
    calc c⁻¹ * ↑y * c * x = c⁻¹ * (↑y * (c * x * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * x * c⁻¹ * ↑y) * c := by rw [h]
      _ = x * (c⁻¹ * ↑y * c) := by group
  · have h := mem_centralizer_singleton_iff.1 (mem_inf.mp y.2).1
    rw [mem_centralizer_singleton_iff]
    calc c * ↑y * c⁻¹ * (c * x * c⁻¹) = c * (↑y * x) * c⁻¹ := by group
      _ = c * (x * ↑y) * c⁻¹ := by rw [h]
      _ = c * x * c⁻¹ * (c * ↑y * c⁻¹) := by group

section Base


theorem base_parts :
    permOK 1782 w0T = true ∧ permOK 1782 rhoT = true ∧ gcI.size = 1782 ∧
      comp 1782 gcI gcT = idTab 1782 ∧ w0T = comp 1782 (comp 1782 gcT l4T) gcI ∧
      rhoT = rhoDecT ∧ rhoI.size = 1782 ∧ comp 1782 rhoI rhoT = idTab 1782 ∧
      comp 1782 w0T w0T = idTab 1782 ∧ w0T ≠ idTab 1782 ∧
      comp 1782 w0T r1T = comp 1782 r1T w0T ∧ r1T ≠ w0T ∧ r2T = comp 1782 w0T r1T ∧
      comp 1782 tauT tauT = idTab 1782 ∧ comp 1782 tauT w0T = comp 1782 w0T tauT ∧
      comp 1782 tauT r1T = comp 1782 r2T tauT ∧ comp 1782 tauT rhoT = comp 1782 rhoI tauT ∧
      bgI.size = 1782 ∧ comp 1782 bgI bgT = idTab 1782 ∧ bwI.size = 1782 ∧
      comp 1782 bwI bwT = idTab 1782 ∧ comp 1782 zT w0T = comp 1782 w0T zT ∧
      comp 1782 zT r1T = comp 1782 r1T zT ∧ comp 1782 zT rhoT = comp 1782 rhoT zT ∧
      comp 1782 hT (tArr 0) = comp 1782 w0T hT := by
  have h := c1Base_check
  simp only [baseCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    and_assoc] at h
  exact h

theorem tabRep_w0 : TabRep w0T Model.w0 := tabRep_of_permOK base_parts.1

theorem tabRep_rho1 : TabRep rhoT Model.rho1 := tabRep_of_permOK base_parts.2.1

theorem tabRep_gc : TabRep gcT gc := tabRep_cWord (by decide)

theorem tabRep_gcI : TabRep gcI gc⁻¹ :=
  tabRep_gc.inv base_parts.2.2.1 base_parts.2.2.2.1

theorem tabRep_l4 : TabRep l4T (LocalR.lambda4 : Equiv.Perm (Fin 1782)) :=
  tabRep_cWord (by decide)

theorem tabRep_rhoI : TabRep rhoI Model.rho1⁻¹ :=
  tabRep_rho1.inv base_parts.2.2.2.2.2.2.1 base_parts.2.2.2.2.2.2.2.1

theorem tabRep_r1 : TabRep r1T r1 := tabRep_rho1.conjTab tabRep_w0 tabRep_rhoI

theorem tabRep_r2 : TabRep r2T r2 := tabRep_rho1.conjTab tabRep_r1 tabRep_rhoI

theorem tabRep_tau0 : TabRep tauT tau0 :=
  tabRep_comp' (rep_cWord (by decide)) (rep_qProds (by norm_num))

theorem tabRep_bg : TabRep bgT (suzB0 * suzB1) := tabRep_comp' rep_b0 rep_b1

theorem tabRep_bgI : TabRep bgI (suzB0 * suzB1)⁻¹ :=
  tabRep_bg.inv base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tabRep_bw : TabRep bwT bw := tabRep_gc.conjTab tabRep_bg tabRep_gcI

theorem tabRep_bwI : TabRep bwI bw⁻¹ :=
  tabRep_bw.inv base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tabRep_cw : TabRep cwT cw :=
  ((tabRep_w0.comp tabRep_bw).comp tabRep_w0).comp tabRep_bwI

theorem tabRep_zJ0 : TabRep zT zJ0 := (tabRep_bwI.comp (tabRep_cw.pow 7)).pow 2

theorem tabRep_hB : TabRep hT hB :=
  ((tabRep_w0.comp ((tabRep_comp' tabRep_bg.2 rep_b0).comp tabRep_bgI)).pow 8).comp tabRep_bg

theorem w0_eq_conj_lambda4 :
    Model.w0 = wPerm [6, 9, 2] * (LocalR.lambda4 : Equiv.Perm (Fin 1782)) * (wPerm [6, 9, 2])⁻¹ :=
  tabRep_w0.perm_eq (base_parts.2.2.2.2.1 ▸ (tabRep_gc.comp tabRep_l4).comp tabRep_gcI)

theorem gc_mem_invE : gc ∈ invE 1 := wPerm_mem (by decide)

theorem w0_mem_invE : Model.w0 ∈ invE 1 := by
  rw [w0_eq_conj_lambda4]
  exact mul_mem (mul_mem gc_mem_invE LocalR.lambda4.2) (inv_mem gc_mem_invE)

@[expose] noncomputable def w0E : ↥(invE 1) := ⟨Model.w0, w0_mem_invE⟩

theorem isConj_lambda4_w0 : IsConj LocalR.lambda4 w0E :=
  isConj_iff.mpr ⟨⟨gc, gc_mem_invE⟩, Subtype.ext w0_eq_conj_lambda4.symm⟩

theorem rho1_eq : Model.rho1 = wPerm [6, 8, 7, 4, 7, 4] * qVec 30 * suzInv 1 :=
  tabRep_rho1.perm_eq (base_parts.2.2.2.2.2.1 ▸
    tabRep_comp' (tabRep_comp' (rep_cWord (by decide)) (rep_qProds (by norm_num))).2 rep_tTab)

theorem rho1_mem_invE : Model.rho1 ∈ invE 1 := by
  rw [rho1_eq]
  exact mul_mem (mul_mem (wPerm_mem (by decide)) (qVec_mem_invE 30)) suzInv_mem_invE

theorem invE_le_suzM : invE 1 ≤ suzM := by
  rw [invE_eq_centM (by norm_num)]
  exact inf_le_right

theorem mem_invE_iff {g : Equiv.Perm (Fin 1782)} : g ∈ invE 1 ↔ g * suzInv 1 = suzInv 1 * g ∧ g ∈ suzM := by
  rw [invE_eq_centM (by norm_num), centM, mem_inf, mem_centralizer_singleton_iff]

theorem r1_mem_invE : r1 ∈ invE 1 :=
  mul_mem (mul_mem rho1_mem_invE w0_mem_invE) (inv_mem rho1_mem_invE)

theorem r2_mem_invE : r2 ∈ invE 1 :=
  mul_mem (mul_mem rho1_mem_invE r1_mem_invE) (inv_mem rho1_mem_invE)

theorem w0_mul_self : Model.w0 * Model.w0 = 1 :=
  (tabRep_w0.comp tabRep_w0).perm_eq (base_parts.2.2.2.2.2.2.2.2.1 ▸ TabRep.idTab)

theorem w0_ne_one : Model.w0 ≠ 1 := fun h =>
  base_parts.2.2.2.2.2.2.2.2.2.1 (tabRep_w0.tab_eq (h ▸ TabRep.idTab))

theorem w0_comm_r1 : Model.w0 * r1 = r1 * Model.w0 :=
  ((tabRep_w0.comp tabRep_r1).eq_iff (tabRep_r1.comp tabRep_w0)).mp
    base_parts.2.2.2.2.2.2.2.2.2.2.1

theorem r1_ne_w0 : r1 ≠ Model.w0 := fun h =>
  base_parts.2.2.2.2.2.2.2.2.2.2.2.1 (tabRep_r1.tab_eq (h ▸ tabRep_w0))

theorem r2_eq : r2 = Model.w0 * r1 :=
  tabRep_r2.perm_eq (base_parts.2.2.2.2.2.2.2.2.2.2.2.2.1 ▸ tabRep_w0.comp tabRep_r1)

theorem r1_mul_self : r1 * r1 = 1 := by
  rw [r1, show Model.rho1 * Model.w0 * Model.rho1⁻¹ * (Model.rho1 * Model.w0 * Model.rho1⁻¹) =
    Model.rho1 * (Model.w0 * Model.w0) * Model.rho1⁻¹ by group, w0_mul_self, mul_one,
    mul_inv_cancel]

theorem r1_ne_one : r1 ≠ 1 := fun h => w0_ne_one (by
  have e : Model.w0 = Model.rho1⁻¹ * r1 * Model.rho1 := by rw [r1]; group
  rw [e, h, mul_one, inv_mul_cancel])

theorem R0_eq : Model.R0 = closure {Model.w0, r1} := rfl

theorem mem_R0_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ Model.R0 ↔ g = 1 ∨ g = Model.w0 ∨ g = r1 ∨ g = r2 := by
  rw [R0_eq, mem_closure_pair_iff w0_mul_self r1_mul_self w0_comm_r1, r2_eq]

theorem w0_mem_R0 : Model.w0 ∈ Model.R0 := mem_R0_iff.mpr (Or.inr (Or.inl rfl))

theorem r1_mem_R0 : r1 ∈ Model.R0 := mem_R0_iff.mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem r2_mem_R0 : r2 ∈ Model.R0 := mem_R0_iff.mpr (Or.inr (Or.inr (Or.inr rfl)))

theorem r2_ne_one : r2 ≠ 1 := fun h => r1_ne_w0 (by
  rw [r2_eq] at h
  calc r1 = Model.w0 * (Model.w0 * r1) := by rw [← mul_assoc, w0_mul_self, one_mul]
    _ = Model.w0 := by rw [h, mul_one])

theorem r2_ne_w0 : r2 ≠ Model.w0 := fun h => r1_ne_one (by
  rw [r2_eq] at h
  calc r1 = Model.w0 * (Model.w0 * r1) := by rw [← mul_assoc, w0_mul_self, one_mul]
    _ = 1 := by rw [h, w0_mul_self])

theorem r2_ne_r1 : r2 ≠ r1 := fun h => w0_ne_one (by
  rw [r2_eq] at h
  calc Model.w0 = Model.w0 * r1 * r1 := by rw [mul_assoc, r1_mul_self, mul_one]
    _ = 1 := by rw [h, r1_mul_self])

theorem card_R0 : Nat.card Model.R0 = 4 := by
  classical
  have e : (Model.R0 : Set (Equiv.Perm (Fin 1782))) =
      ↑({1, Model.w0, r1, r2} : Finset (Equiv.Perm (Fin 1782))) := by
    ext g
    simp only [SetLike.mem_coe, mem_R0_iff, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem (by simp [w0_ne_one.symm, r1_ne_one.symm, r2_ne_one.symm]),
    Finset.card_insert_of_notMem (by simp [r1_ne_w0.symm, r2_ne_w0.symm]),
    Finset.card_insert_of_notMem (by simp [r2_ne_r1.symm]), Finset.card_singleton]

theorem R0_comm {x y : Equiv.Perm (Fin 1782)} (hx : x ∈ Model.R0) (hy : y ∈ Model.R0) :
    x * y = y * x := by
  have hab : Commute Model.w0 r1 := w0_comm_r1
  have h1 : Commute Model.w0 y ∧ Commute r1 y := by
    rcases mem_R0_iff.mp hy with rfl | rfl | rfl | rfl
    · exact ⟨Commute.one_right _, Commute.one_right _⟩
    · exact ⟨Commute.refl _, hab.symm⟩
    · exact ⟨hab, Commute.refl _⟩
    · rw [r2_eq]
      exact ⟨(Commute.refl _).mul_right hab, hab.symm.mul_right (Commute.refl _)⟩
  rcases mem_R0_iff.mp hx with rfl | rfl | rfl | rfl
  · exact Commute.one_left _
  · exact h1.1
  · exact h1.2
  · rw [r2_eq]
    exact h1.1.mul_left h1.2

theorem mul_self_of_mem_R0 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ Model.R0) : x * x = 1 := by
  rcases mem_R0_iff.mp hx with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact w0_mul_self
  · exact r1_mul_self
  · rw [r2_eq, show Model.w0 * r1 * (Model.w0 * r1) = Model.w0 * (r1 * Model.w0) * r1 by group,
      ← w0_comm_r1, show Model.w0 * (Model.w0 * r1) * r1 = Model.w0 * Model.w0 * (r1 * r1) by
        group, w0_mul_self, r1_mul_self, one_mul]

theorem isElemAbelian_R0 : CFSG.Open.IsElemAbelian 2 Model.R0 :=
  ⟨⟨⟨fun x y => Subtype.ext (R0_comm x.2 y.2)⟩⟩, fun x hx => by
    rw [pow_two]
    exact mul_self_of_mem_R0 hx⟩

theorem R0_le_invE : Model.R0 ≤ invE 1 := fun x hx => by
  rcases mem_R0_iff.mp hx with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact w0_mem_invE
  · exact r1_mem_invE
  · exact r2_mem_invE

theorem rho1_conj_r2 : Model.rho1 * r2 * Model.rho1⁻¹ = Model.w0 := by
  rw [r2_eq, show Model.rho1 * (Model.w0 * r1) * Model.rho1⁻¹ =
    (Model.rho1 * Model.w0 * Model.rho1⁻¹) * (Model.rho1 * r1 * Model.rho1⁻¹) by group]
  rw [show Model.rho1 * Model.w0 * Model.rho1⁻¹ = r1 from rfl,
    show Model.rho1 * r1 * Model.rho1⁻¹ = r2 from rfl, r2_eq, ← mul_assoc, ← w0_comm_r1,
    mul_assoc, r1_mul_self, mul_one]

theorem mem_normalizer_R0 {x : Equiv.Perm (Fin 1782)} (h0 : x * Model.w0 * x⁻¹ ∈ Model.R0)
    (h1 : x * r1 * x⁻¹ ∈ Model.R0) : x ∈ normalizer (Model.R0 : Set (Equiv.Perm (Fin 1782))) := by
  refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
  rcases mem_R0_iff.mp hy with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact one_mem _
  · exact h0
  · exact h1
  · rw [r2_eq, show x * (Model.w0 * r1) * x⁻¹ = x * Model.w0 * x⁻¹ * (x * r1 * x⁻¹) by group]
    exact mul_mem h0 h1

theorem rho1_mem_B0 : Model.rho1 ∈ Model.B0 :=
  ⟨rho1_mem_invE, mem_normalizer_R0 r1_mem_R0 r2_mem_R0⟩

theorem tau0_mem_invE : tau0 ∈ invE 1 := mul_mem (wPerm_mem (by decide)) (qVec_mem_invE 23)

theorem tau0_mul_self : tau0 * tau0 = 1 :=
  (tabRep_tau0.comp tabRep_tau0).perm_eq
    (base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ▸ TabRep.idTab)

theorem tau0_comm_w0 : tau0 * Model.w0 = Model.w0 * tau0 :=
  ((tabRep_tau0.comp tabRep_w0).eq_iff (tabRep_w0.comp tabRep_tau0)).mp
    base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tau0_conj_w0 : tau0 * Model.w0 * tau0⁻¹ = Model.w0 := by
  rw [tau0_comm_w0, mul_inv_cancel_right]

theorem tau0_conj_r1 : tau0 * r1 * tau0⁻¹ = r2 := by
  have h : tau0 * r1 = r2 * tau0 :=
    ((tabRep_tau0.comp tabRep_r1).eq_iff (tabRep_r2.comp tabRep_tau0)).mp
      base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [h, mul_inv_cancel_right]

theorem tau0_conj_rho1 : tau0 * Model.rho1 * tau0⁻¹ = Model.rho1⁻¹ := by
  have h : tau0 * Model.rho1 = Model.rho1⁻¹ * tau0 :=
    ((tabRep_tau0.comp tabRep_rho1).eq_iff (tabRep_rhoI.comp tabRep_tau0)).mp
      base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [h, mul_inv_cancel_right]

theorem tau0_not_comm_r1 : tau0 * r1 ≠ r1 * tau0 := fun h => r2_ne_r1 (by
  rw [← tau0_conj_r1, h, mul_inv_cancel_right])

theorem tau0_mem_B0 : tau0 ∈ Model.B0 :=
  ⟨tau0_mem_invE, mem_normalizer_R0 (by rw [tau0_conj_w0]; exact w0_mem_R0)
    (by rw [tau0_conj_r1]; exact r2_mem_R0)⟩

theorem gc_mem_suzM : gc ∈ suzM := invE_le_suzM gc_mem_invE

theorem bw_mem_suzM : bw ∈ suzM :=
  mul_mem (mul_mem gc_mem_suzM (mul_mem (subset_closure (Set.mem_insert _ _))
    (subset_closure (Set.mem_insert_of_mem _ rfl)))) (inv_mem gc_mem_suzM)

theorem zJ0_mem_suzM : zJ0 ∈ suzM := by
  have hw := invE_le_suzM w0_mem_invE
  exact pow_mem (mul_mem (inv_mem bw_mem_suzM) (pow_mem (mul_mem (mul_mem (mul_mem hw
    bw_mem_suzM) hw) (inv_mem bw_mem_suzM)) 7)) 2

theorem zJ0_comm : zJ0 * Model.w0 = Model.w0 * zJ0 ∧ zJ0 * r1 = r1 * zJ0 ∧
    zJ0 * Model.rho1 = Model.rho1 * zJ0 :=
  ⟨((tabRep_zJ0.comp tabRep_w0).eq_iff (tabRep_w0.comp tabRep_zJ0)).mp
      base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    ((tabRep_zJ0.comp tabRep_r1).eq_iff (tabRep_r1.comp tabRep_zJ0)).mp
      base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    ((tabRep_zJ0.comp tabRep_rho1).eq_iff (tabRep_rho1.comp tabRep_zJ0)).mp
      base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

@[expose] noncomputable def V0 : Subgroup (Equiv.Perm (Fin 1782)) :=
  centralizer {Model.w0} ⊓ invE 1

theorem mem_V0_iff {g : Equiv.Perm (Fin 1782)} : g ∈ V0 ↔ g * Model.w0 = Model.w0 * g ∧ g ∈ invE 1 := by
  rw [V0, mem_inf, mem_centralizer_singleton_iff]

theorem card_V0 : Nat.card V0 = 512 := by
  rw [V0, w0_eq_conj_lambda4, card_centralizer_inf_conj (invE 1) (c := wPerm [6, 9, 2]) gc_mem_invE,
    inf_comm,
    ← LocalR.card_centralizer_coe, LocalR.card_centralizer_lambda4]

theorem w0_mem_V0 : Model.w0 ∈ V0 := mem_V0_iff.mpr ⟨rfl, w0_mem_invE⟩

theorem r1_mem_V0 : r1 ∈ V0 := mem_V0_iff.mpr ⟨w0_comm_r1.symm, r1_mem_invE⟩

theorem tau0_mem_V0 : tau0 ∈ V0 := mem_V0_iff.mpr ⟨tau0_comm_w0, tau0_mem_invE⟩

theorem R0_le_V0 : Model.R0 ≤ V0 := fun _ hx =>
  mem_V0_iff.mpr ⟨R0_comm hx w0_mem_R0, R0_le_invE hx⟩

theorem hB_mem_suzM : hB ∈ suzM := by
  have hb : suzB0 * suzB1 ∈ suzM := mul_mem (subset_closure (Set.mem_insert _ _))
    (subset_closure (Set.mem_insert_of_mem _ rfl))
  exact mul_mem (pow_mem (mul_mem (invE_le_suzM w0_mem_invE) (mul_mem (mul_mem hb
    (subset_closure (Set.mem_insert _ _))) (inv_mem hb))) 8) hb

theorem hB_conj : hB * suzInv 0 * hB⁻¹ = Model.w0 := by
  have h : hB * suzInv 0 = Model.w0 * hB :=
    ((tabRep_comp' tabRep_hB.2 (rep_suzInv (i := 0) (by norm_num))).eq_iff
      (tabRep_w0.comp tabRep_hB)).mp base_parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [h, mul_inv_cancel_right]

theorem exists_conj_suzInv_zero {r : Equiv.Perm (Fin 1782)} (hr : r ∈ Model.R0) (hr1 : r ≠ 1) :
    ∃ c ∈ suzM, c * suzInv 0 * c⁻¹ = r := by
  have hrho := invE_le_suzM rho1_mem_invE
  rcases mem_R0_iff.mp hr with rfl | rfl | rfl | rfl
  · exact (hr1 rfl).elim
  · exact ⟨hB, hB_mem_suzM, hB_conj⟩
  · refine ⟨Model.rho1 * hB, mul_mem hrho hB_mem_suzM, ?_⟩
    rw [r1, ← hB_conj]
    group
  · refine ⟨Model.rho1 * (Model.rho1 * hB), mul_mem hrho (mul_mem hrho hB_mem_suzM), ?_⟩
    rw [r2, r1, ← hB_conj]
    group

theorem card_centralizer_w0 :
    Nat.card ↥(centralizer ({Model.w0} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM) = 161280 := by
  rw [← hB_conj, card_centralizer_inf_conj _ hB_mem_suzM, ← centM,
    ← invE_eq_centM (by norm_num), card_invE (by norm_num)]
  rfl

end Base

end CFSG.Sporadic.SuzRecog.C1Model
