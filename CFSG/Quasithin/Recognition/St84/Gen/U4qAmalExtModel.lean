module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtend
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open CFSG.Quasithin.H13.U4Par
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAut fieldAut_mem_unitriangular)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

@[expose] noncomputable def u4FieldInvol : MulAut (hypSU h 2 0) :=
  fieldAut h h.barEquiv

theorem coe_u4FieldInvol (g : hypSU h 2 0) :
    (((u4FieldInvol h g : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      ((g : GL Ix K) : Matrix Ix Ix K).map h.bar :=
  coe_fieldAut_u4 h h.barEquiv g

theorem u4FieldInvol_apply_apply (g : hypSU h 2 0) : u4FieldInvol h (u4FieldInvol h g) = g := by
  apply hypSU_ext h
  rw [coe_u4FieldInvol, coe_u4FieldInvol]
  ext i j
  simp only [map_apply, h.bar_bar]

theorem u4FieldInvol_mul_self : u4FieldInvol h * u4FieldInvol h = 1 :=
  MulEquiv.ext (u4FieldInvol_apply_apply h)

theorem u4FieldInvol_mem_iff_of {X : Subgroup (hypSU h 2 0)}
    (hX : ∀ g ∈ X, u4FieldInvol h g ∈ X) (g : hypSU h 2 0) : u4FieldInvol h g ∈ X ↔ g ∈ X :=
  ⟨fun hg => by simpa only [u4FieldInvol_apply_apply] using hX _ hg, hX g⟩

theorem u4FieldInvol_mem_parP_iff (g : hypSU h 2 0) : u4FieldInvol h g ∈ parP h ↔ g ∈ parP h :=
  fieldAut_mem_parP_iff_u4 h h.barEquiv g

theorem u4FieldInvol_mem_parP2_iff (g : hypSU h 2 0) :
    u4FieldInvol h g ∈ parP2 h ↔ g ∈ parP2 h :=
  fieldAut_mem_parP2_iff_u4 h h.barEquiv g

theorem u4FieldInvol_mem_hypUnitriangular_iff (g : hypSU h 2 0) :
    u4FieldInvol h g ∈ hypUnitriangular h 2 0 ↔ g ∈ hypUnitriangular h 2 0 :=
  fieldAut_mem_unitriangular h h.barEquiv g

theorem u4FieldInvol_mem_hypBorel_iff (g : hypSU h 2 0) :
    u4FieldInvol h g ∈ hypBorel h 2 0 ↔ g ∈ hypBorel h 2 0 := by
  rw [← parP_inf_parP2_eq_u4 h, Subgroup.mem_inf, Subgroup.mem_inf, u4FieldInvol_mem_parP_iff,
    u4FieldInvol_mem_parP2_iff]

theorem sMat_map_bar (x y c : K) :
    (sMat h x y c).map h.bar = sMat h (h.bar x) (h.bar y) (h.bar c) := by
  ext i j
  rw [map_apply]
  rcases ix_cases i with rfl | rfl | rfl | rfl <;> rcases ix_cases j with rfl | rfl | rfl | rfl <;>
    simp [sMat_apply, one_apply]

theorem sAdm_bar_u4Ext {x y c : K} (hc : SAdm h x y c) : SAdm h (h.bar x) (h.bar y) (h.bar c) := by
  unfold SAdm at *
  have := congrArg h.bar hc
  simpa only [map_add, map_mul] using this

theorem u4FieldInvol_mem_radQ_iff (g : hypSU h 2 0) : u4FieldInvol h g ∈ radQ h ↔ g ∈ radQ h := by
  refine u4FieldInvol_mem_iff_of h (fun g hg => ?_) g
  obtain ⟨x, y, c, hc, hgm⟩ := hg
  exact ⟨h.bar x, h.bar y, h.bar c, sAdm_bar_u4Ext h hc, by
    rw [coe_u4FieldInvol, hgm, sMat_map_bar]⟩

theorem isQ2Mat_map_bar {M : Matrix Ix Ix K} (hM : IsQ2Mat M) : IsQ2Mat (M.map h.bar) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hM
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [map_apply, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]

theorem u4FieldInvol_mem_radQ2_iff (g : hypSU h 2 0) :
    u4FieldInvol h g ∈ radQ2 h ↔ g ∈ radQ2 h := by
  refine u4FieldInvol_mem_iff_of h (fun g hg => ?_) g
  show IsQ2Mat _
  rw [coe_u4FieldInvol]
  exact isQ2Mat_map_bar h hg

theorem u4FieldInvol_mem_normalizer_iff {X : Subgroup (hypSU h 2 0)}
    (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) (g : hypSU h 2 0) :
    u4FieldInvol h g ∈ Subgroup.normalizer (X : Set (hypSU h 2 0)) ↔
      g ∈ Subgroup.normalizer (X : Set (hypSU h 2 0)) := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  refine u4FieldInvol_mem_iff_of h (fun g hg => ?_) g
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have h1 : g * u4FieldInvol h n * g⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp ((hX n).mpr hn)
  have h2 := (hX _).mpr h1
  rwa [map_mul, map_mul, map_inv, u4FieldInvol_apply_apply] at h2

theorem not_forall_u4FieldInvol_mul_eq (w : hypSU h 2 0) :
    ¬ ∀ v ∈ hypUnitriangular h 2 0, u4FieldInvol h v * w = w * v := by
  intro hw
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  set W := ((w : GL Ix K) : Matrix Ix Ix K)
  have hmat : ∀ v ∈ hypUnitriangular h 2 0,
      ((v : GL Ix K) : Matrix Ix Ix K).map h.bar * W = W * ((v : GL Ix K) : Matrix Ix Ix K) := by
    intro v hv
    have e := congrArg (fun x : hypSU h 2 0 => ((x : GL Ix K) : Matrix Ix Ix K)) (hw v hv)
    simpa only [coe_mul_hypSU, coe_u4FieldInvol] using e
  have hy : ∀ y : K, h.bar y * W if1 if1 = W if2 if2 * y := by
    intro y
    have e := congrFun (congrFun (hmat _ (radQ_le_hypUnitriangular_u4 h (syElt_mem y))) if2) if1
    rw [coe_syElt, mul_apply, sum_ix, mul_apply, sum_ix] at e
    simp [map_apply, sMat_apply, one_apply] at e
    linear_combination e
  have hz : ∀ j, j ≠ if1 → W if1 j = 0 := by
    have hadm : SAdm h 0 0 1 := (sAdm_zero_zero_iff h).mpr (map_one _)
    have hv := radQ_le_hypUnitriangular_u4 h (sElt_mem_radQ h hadm)
    intro j hj
    have e := congrFun (congrFun (hmat _ hv) ie1) j
    rw [coe_sElt, mul_apply, sum_ix, mul_apply, sum_ix] at e
    rcases ix_cases j with rfl | rfl | rfl | rfl
    · simp [map_apply, sMat_apply, one_apply] at e
      linear_combination e
    · simp [map_apply, sMat_apply, one_apply] at e
      linear_combination e
    · exact absurd rfl hj
    · simp [map_apply, sMat_apply, one_apply] at e
      linear_combination e
  have h1 := hy 1
  rw [map_one, one_mul, mul_one] at h1
  have h0 : W if1 if1 = 0 := by
    have e := hy ω
    rw [← h1] at e
    have e' : (h.bar ω - ω) * W if1 if1 = 0 := by linear_combination e
    exact (mul_eq_zero.mp e').resolve_left (sub_ne_zero.mpr hω)
  have hdet : W.det = 0 := Matrix.det_eq_zero_of_row_eq_zero if1 fun j => by
    by_cases hj : j = if1
    · rw [hj]
      exact h0
    · exact hz j hj
  have hdet1 : W.det = 1 := (mem_gramSU.mp w.2).2
  rw [hdet] at hdet1
  exact zero_ne_one hdet1

theorem z2_cases_u4Ext : ∀ s : Multiplicative (ZMod 2), s = 1 ∨ s = Multiplicative.ofAdd 1 := by
  decide

theorem card_z2_u4Ext : Nat.card (Multiplicative (ZMod 2)) = 2 :=
  (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod 2)

theorem mem_zpowers_ofAdd_one_u4Ext (s : Multiplicative (ZMod 2)) :
    s ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 2)) := by
  rcases z2_cases_u4Ext s with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.mem_zpowers _

theorem orderOf_u4FieldInvol_dvd :
    orderOf (u4FieldInvol h) ∣ orderOf (Multiplicative.ofAdd (1 : ZMod 2)) := by
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  exact orderOf_dvd_of_pow_eq_one (by rw [sq, u4FieldInvol_mul_self])

@[expose] noncomputable def u4FieldInvolHom : Multiplicative (ZMod 2) →* MulAut (hypSU h 2 0) :=
  monoidHomOfForallMemZpowers mem_zpowers_ofAdd_one_u4Ext (orderOf_u4FieldInvol_dvd h)

theorem u4FieldInvolHom_ofAdd_one :
    u4FieldInvolHom h (Multiplicative.ofAdd 1) = u4FieldInvol h := by
  rw [u4FieldInvolHom, monoidHomOfForallMemZpowers_apply_gen]

theorem u4FieldInvolHom_apply_mem {X : Subgroup (hypSU h 2 0)}
    (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) (s : Multiplicative (ZMod 2)) {x : hypSU h 2 0}
    (hx : x ∈ X) : u4FieldInvolHom h s x ∈ X := by
  rcases z2_cases_u4Ext s with rfl | rfl
  · rw [map_one, MulAut.one_apply]
    exact hx
  · rw [u4FieldInvolHom_ofAdd_one]
    exact (hX x).mpr hx

theorem u4FieldInvolHom_apply_apply (s : Multiplicative (ZMod 2)) (x : hypSU h 2 0) :
    u4FieldInvolHom h s (u4FieldInvolHom h s x) = x := by
  rcases z2_cases_u4Ext s with rfl | rfl
  · rw [map_one, MulAut.one_apply, MulAut.one_apply]
  · rw [u4FieldInvolHom_ofAdd_one, u4FieldInvol_apply_apply]

abbrev u4ExtGroup : Type := hypSU h 2 0 ⋊[u4FieldInvolHom h] Multiplicative (ZMod 2)

theorem finite_u4ExtGroup : Finite (u4ExtGroup h) := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  exact Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem index_range_inl_u4Ext :
    (SemidirectProduct.inl : hypSU h 2 0 →* u4ExtGroup h).range.index = 2 := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr SemidirectProduct.rightHom_surjective, Subgroup.card_top,
    card_z2_u4Ext]

theorem conj_inl_u4Ext (a : u4ExtGroup h) (x : hypSU h 2 0) :
    a * SemidirectProduct.inl x * a⁻¹ =
      SemidirectProduct.inl (a.left * u4FieldInvolHom h a.right x * a.left⁻¹) := by
  rw [map_mul, map_mul, map_inv, SemidirectProduct.inl_aut]
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right a]
  rw [map_inv]
  group

@[expose] def u4ExtLift (X : Subgroup (hypSU h 2 0)) (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) :
    Subgroup (u4ExtGroup h) where
  carrier := {a | a.left ∈ X}
  mul_mem' {a b} ha hb := by
    change (a * b).left ∈ X
    rw [SemidirectProduct.mul_left]
    exact X.mul_mem ha (u4FieldInvolHom_apply_mem h hX _ hb)
  one_mem' := X.one_mem
  inv_mem' {a} ha := by
    change a⁻¹.left ∈ X
    rw [SemidirectProduct.inv_left]
    exact u4FieldInvolHom_apply_mem h hX _ (X.inv_mem ha)

variable {h} in
theorem mem_u4ExtLift {X : Subgroup (hypSU h 2 0)} {hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X}
    {a : u4ExtGroup h} : a ∈ u4ExtLift h X hX ↔ a.left ∈ X :=
  Iff.rfl

theorem inl_mem_u4ExtLift {X : Subgroup (hypSU h 2 0)} {hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X}
    (g : hypSU h 2 0) :
    (SemidirectProduct.inl g : u4ExtGroup h) ∈ u4ExtLift h X hX ↔ g ∈ X :=
  Iff.rfl

theorem inr_mem_u4ExtLift {X : Subgroup (hypSU h 2 0)} {hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X}
    (s : Multiplicative (ZMod 2)) :
    (SemidirectProduct.inr s : u4ExtGroup h) ∈ u4ExtLift h X hX :=
  X.one_mem

theorem u4ExtLift_le_iff {X Z : Subgroup (hypSU h 2 0)}
    {hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X} {hZ : ∀ g, u4FieldInvol h g ∈ Z ↔ g ∈ Z} :
    u4ExtLift h X hX ≤ u4ExtLift h Z hZ ↔ X ≤ Z :=
  ⟨fun hle g hg => (inl_mem_u4ExtLift h g).mp (hle ((inl_mem_u4ExtLift h g).mpr hg)),
    fun hle _ ha => hle ha⟩

theorem le_u4ExtLift_of_comap_le {X : Subgroup (hypSU h 2 0)}
    {hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X} {H : Subgroup (u4ExtGroup h)}
    (hH : ∀ s, (SemidirectProduct.inr s : u4ExtGroup h) ∈ H)
    (hle : H.comap SemidirectProduct.inl ≤ X) : H ≤ u4ExtLift h X hX := by
  intro a ha
  apply hle
  show SemidirectProduct.inl a.left ∈ H
  rw [eq_mul_inv_of_mul_eq (SemidirectProduct.inl_left_mul_inr_right a)]
  exact H.mul_mem ha (H.inv_mem (hH _))

theorem card_u4ExtLift (X : Subgroup (hypSU h 2 0)) (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) :
    Nat.card (u4ExtLift h X hX) = Nat.card X * 2 := by
  have e : ↥(u4ExtLift h X hX) ≃ ↥X × Multiplicative (ZMod 2) :=
    { toFun := fun a => (⟨a.1.left, a.2⟩, a.1.right)
      invFun := fun p => ⟨⟨p.1.1, p.2⟩, p.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, card_z2_u4Ext]

theorem index_u4ExtLift (X : Subgroup (hypSU h 2 0)) (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) :
    (u4ExtLift h X hX).index = X.index := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have h1 := (u4ExtLift h X hX).card_mul_index
  have h2 := X.card_mul_index
  rw [card_u4ExtLift, SemidirectProduct.card, card_z2_u4Ext, ← h2] at h1
  have hpos : 0 < Nat.card X * 2 := Nat.mul_pos Nat.card_pos (by norm_num)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1]
  ring

noncomputable abbrev u4ExtSylow : Subgroup (u4ExtGroup h) :=
  u4ExtLift h (hypUnitriangular h 2 0) (u4FieldInvol_mem_hypUnitriangular_iff h)

noncomputable abbrev u4ExtBorel : Subgroup (u4ExtGroup h) :=
  u4ExtLift h (hypBorel h 2 0) (u4FieldInvol_mem_hypBorel_iff h)

noncomputable abbrev u4ExtParP : Subgroup (u4ExtGroup h) :=
  u4ExtLift h (parP h) (u4FieldInvol_mem_parP_iff h)

noncomputable abbrev u4ExtParP2 : Subgroup (u4ExtGroup h) :=
  u4ExtLift h (parP2 h) (u4FieldInvol_mem_parP2_iff h)

theorem u4ExtSylow_le_u4ExtBorel : u4ExtSylow h ≤ u4ExtBorel h :=
  (u4ExtLift_le_iff h).mpr (hypUnitriangular_le_hypBorel h)

theorem u4ExtBorel_le_u4ExtParP : u4ExtBorel h ≤ u4ExtParP h :=
  (u4ExtLift_le_iff h).mpr (UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num))

theorem u4ExtBorel_le_u4ExtParP2 : u4ExtBorel h ≤ u4ExtParP2 h :=
  (u4ExtLift_le_iff h).mpr (UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) le_rfl)

theorem u4ExtParP_ne_u4ExtParP2 : u4ExtParP h ≠ u4ExtParP2 h := fun e =>
  parP_ne_parP2 h (le_antisymm ((u4ExtLift_le_iff h).mp e.le) ((u4ExtLift_le_iff h).mp e.ge))

theorem mem_normalizer_map_inl_iff_u4Ext {X : Subgroup (hypSU h 2 0)}
    (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) (a : u4ExtGroup h) :
    a ∈ Subgroup.normalizer
        ((X.map (SemidirectProduct.inl : hypSU h 2 0 →* u4ExtGroup h) : Subgroup _) :
          Set (u4ExtGroup h)) ↔
      a.left ∈ Subgroup.normalizer (X : Set (hypSU h 2 0)) := by
  have := finite_u4ExtGroup h
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  constructor
  · intro ha
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    have hx : u4FieldInvolHom h a.right n ∈ X := u4FieldInvolHom_apply_mem h hX _ hn
    have h1 := (Subgroup.mem_normalizer_iff.mp ha _).mp (Subgroup.mem_map_of_mem _ hx)
    rwa [conj_inl_u4Ext, Subgroup.mem_map_iff_mem SemidirectProduct.inl_injective,
      u4FieldInvolHom_apply_apply] at h1
  · intro ha
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨x, hx, rfl⟩
    rw [conj_inl_u4Ext]
    exact Subgroup.mem_map_of_mem _
      ((Subgroup.mem_normalizer_iff.mp ha _).mp (u4FieldInvolHom_apply_mem h hX _ hx))

theorem normalizer_map_inl_u4Ext {X : Subgroup (hypSU h 2 0)}
    (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) :
    Subgroup.normalizer
        ((X.map (SemidirectProduct.inl : hypSU h 2 0 →* u4ExtGroup h) : Subgroup _) :
          Set (u4ExtGroup h)) =
      u4ExtLift h (Subgroup.normalizer (X : Set (hypSU h 2 0)))
        (u4FieldInvol_mem_normalizer_iff h hX) := by
  ext a
  exact mem_normalizer_map_inl_iff_u4Ext h hX a

theorem normalizer_u4ExtLift_le {X : Subgroup (hypSU h 2 0)}
    (hX : ∀ g, u4FieldInvol h g ∈ X ↔ g ∈ X) :
    Subgroup.normalizer ((u4ExtLift h X hX : Subgroup (u4ExtGroup h)) : Set (u4ExtGroup h)) ≤
      u4ExtLift h (Subgroup.normalizer (X : Set (hypSU h 2 0)))
        (u4FieldInvol_mem_normalizer_iff h hX) := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  intro a ha
  show a.left ∈ Subgroup.normalizer (X : Set (hypSU h 2 0))
  have hl : SemidirectProduct.inl a.left ∈
      Subgroup.normalizer ((u4ExtLift h X hX : Subgroup (u4ExtGroup h)) : Set (u4ExtGroup h)) := by
    rw [eq_mul_inv_of_mul_eq (SemidirectProduct.inl_left_mul_inr_right a)]
    exact Subgroup.mul_mem _ ha
      (Subgroup.le_normalizer (Subgroup.inv_mem _ (inr_mem_u4ExtLift h _)))
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  have h1 := (Subgroup.mem_normalizer_iff.mp hl (SemidirectProduct.inl n)).mp
    ((inl_mem_u4ExtLift h n).mpr hn)
  rwa [← map_inv, ← map_mul, ← map_mul, inl_mem_u4ExtLift] at h1

theorem normalizer_u4ExtSylow_le :
    Subgroup.normalizer ((u4ExtSylow h : Subgroup (u4ExtGroup h)) : Set (u4ExtGroup h)) ≤
      u4ExtBorel h := by
  refine (normalizer_u4ExtLift_le h _).trans fun a ha => ?_
  show a.left ∈ hypBorel h 2 0
  rw [← UnitaryHigher.normalizer_hypUnitriangular (r := 2) (ε := 0) h (by norm_num)
    (by norm_num)]
  exact ha

theorem normalizer_eq_of_isCoatom_u4Ext {A X : Subgroup (hypSU h 2 0)} (hA : IsCoatom A)
    (hAX : A ≤ Subgroup.normalizer (X : Set (hypSU h 2 0))) (hX : X ≠ ⊥) (hX2 : IsPGroup 2 X) :
    Subgroup.normalizer (X : Set (hypSU h 2 0)) = A := by
  refine (hA.le_iff.mp hAX).resolve_left fun htop => ?_
  have := isSimpleGroup_hypSU h
  have hXn : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h0 | h0
  · exact hX h0
  · apply not_isPGroup_hypSU h
    rw [h0] at hX2
    exact hX2.of_equiv Subgroup.topEquiv

theorem radQ_ne_bot_u4Ext : radQ h ≠ ⊥ := fun e =>
  zRad_ne_bot h (eq_bot_iff.mpr ((zRad_le_radQ h).trans e.le))

theorem radQ2_ne_bot_u4Ext : radQ2 h ≠ ⊥ := fun e =>
  zRad_ne_bot h (eq_bot_iff.mpr ((zRad_le_radQ2 h).trans e.le))

theorem u4ExtParP_eq_normalizer :
    u4ExtParP h = Subgroup.normalizer
      (((radQ h).map (SemidirectProduct.inl : hypSU h 2 0 →* u4ExtGroup h) : Subgroup _) :
        Set (u4ExtGroup h)) := by
  rw [normalizer_map_inl_u4Ext h (u4FieldInvol_mem_radQ_iff h)]
  ext a
  show a.left ∈ parP h ↔ a.left ∈ Subgroup.normalizer _
  rw [normalizer_eq_of_isCoatom_u4Ext h (isCoatom_parP h) (parP_le_normalizer_radQ h)
    (radQ_ne_bot_u4Ext h) (radQ_isPGroup h)]

theorem u4ExtParP2_eq_normalizer :
    u4ExtParP2 h = Subgroup.normalizer
      (((radQ2 h).map (SemidirectProduct.inl : hypSU h 2 0 →* u4ExtGroup h) : Subgroup _) :
        Set (u4ExtGroup h)) := by
  rw [normalizer_map_inl_u4Ext h (u4FieldInvol_mem_radQ2_iff h)]
  ext a
  show a.left ∈ parP2 h ↔ a.left ∈ Subgroup.normalizer _
  rw [normalizer_eq_of_isCoatom_u4Ext h (isCoatom_parP2 h) (parP2_le_normalizer_radQ2 h)
    (radQ2_ne_bot_u4Ext h) (radQ2_isPGroup h)]

end CFSG.Quasithin.F112R.St84

end
