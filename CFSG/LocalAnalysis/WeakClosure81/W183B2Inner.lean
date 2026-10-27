module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2One
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 CoverOf Bar2)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {R L : Subgroup (LGL 2 V)}

@[expose] def actOnMul (R : Subgroup (LGL 2 V)) : ↥R →* MulAut (Multiplicative V) where
  toFun r :=
    { toFun := fun v => Multiplicative.ofAdd ((r : LGL 2 V) (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd ((r : LGL 2 V)⁻¹ (Multiplicative.toAdd v))
      left_inv := fun v => by simp
      right_inv := fun v => by simp
      map_mul' := fun a b => by simp }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp

private theorem w183b2_actOnMul_apply (r : ↥R) (v : Multiplicative V) :
    actOnMul R r v = Multiplicative.ofAdd ((r : LGL 2 V) (Multiplicative.toAdd v)) := rfl

private theorem w183b2_actOnMul_sub (r : ↥R) (v : Multiplicative V) :
    actOnMul R r v * v⁻¹ = Multiplicative.ofAdd
      ((r : LGL 2 V) (Multiplicative.toAdd v) - Multiplicative.toAdd v) := by
  have hv : v⁻¹ = Multiplicative.ofAdd (-(Multiplicative.toAdd v)) := by
    rw [← ofAdd_toAdd v⁻¹, toAdd_inv]
  rw [w183b2_actOnMul_apply r, hv, ← ofAdd_add, sub_eq_add_neg]

theorem actOnMul_injective : Function.Injective (actOnMul R) := by
  intro r₁ r₂ h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have h' := congrArg (fun φ : MulAut (Multiplicative V) => φ (Multiplicative.ofAdd v)) h
  exact Multiplicative.ofAdd.injective (by simpa [w183b2_actOnMul_apply] using h')

theorem isQuadraticOn_actOnMul {D : Subgroup (LGL 2 V)} (hDq : commSpace D (commSub D) = ⊥) :
    IsQuadraticOn (actOnMul R) (D.subgroupOf R) := by
  intro a ha b hb v
  rw [Subgroup.mem_subgroupOf] at ha hb
  have hfix : (b : LGL 2 V) ((a : LGL 2 V) (Multiplicative.toAdd v)
        - Multiplicative.toAdd v) =
      (a : LGL 2 V) (Multiplicative.toAdd v) - Multiplicative.toAdd v :=
    (commSpace_eq_bot_iff.mp hDq) (b : LGL 2 V) hb _
      (sub_mem_commSub D ha (Multiplicative.toAdd v))
  rw [w183b2_actOnMul_sub a v, w183b2_actOnMul_apply b, toAdd_ofAdd, hfix]

private theorem w183b2_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.Open.IsQuasisimple B) : CFSG.Open.IsQuasisimple A := by
  have : Group.IsPerfect B := ⟨h.1⟩
  have : IsSimpleGroup (B ⧸ Subgroup.center B) := h.2
  have hperfect : Group.IsPerfect A :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨hperfect.commutator_eq_top,
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).isSimpleGroup⟩

private theorem w183b2_isQuasisimple_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  have hcenter : Subgroup.center X = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center X := by rw [h]; trivial
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      haveI := (commutator_eq_bot_iff X).mp h
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (mul_comm a b)
    · exact h
  · have e : X ⧸ Subgroup.center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact e.isSimpleGroup

theorem w183b2_isComponentOf_subgroupOf (h : SimpleCore R L) :
    IsComponentOf (L.subgroupOf R) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · refine IsSubnormal.step le_top ?_ (IsSubnormal.refl ⊤)
    rw [Subgroup.normal_subgroupOf_iff le_top]
    intro a b ha _
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using h.normal (b : LGL 2 V) b.2 (a : LGL 2 V) ha
  · have hqL : CFSG.Open.IsQuasisimple ↥L :=
      w183b2_isQuasisimple_of_simple h.simple (by
        obtain ⟨a, ha, b, hb, hab⟩ := h.nonab
        exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun hh => hab (congrArg Subtype.val hh)⟩)
    exact w183b2_isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.le) hqL

theorem w183b2_coverOf_subgroupOf (h : SimpleCore R L) : CoverOf ↥(L.subgroupOf R) ↥L := by
  refine ⟨(w183b2_isComponentOf_subgroupOf h).2.2, ?_⟩
  have hcenterA : Subgroup.center ↥(L.subgroupOf R) = ⊥ := by
    haveI : IsSimpleGroup ↥(L.subgroupOf R) := by
      haveI : IsSimpleGroup ↥L := h.simple
      exact (Subgroup.subgroupOfEquivOfLe h.le).isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(L.subgroupOf R)) with hc | hc
    · exact hc
    · exfalso
      haveI : IsMulCommutative ↥(L.subgroupOf R) := Subgroup.center_eq_top_iff.mp hc
      obtain ⟨a, ha, b, hb, hab⟩ := h.nonab
      let aA : ↥(L.subgroupOf R) := ⟨⟨a, h.le ha⟩, Subgroup.mem_subgroupOf.mpr ha⟩
      let bA : ↥(L.subgroupOf R) := ⟨⟨b, h.le hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
      exact hab (by
        simpa using congrArg (fun z : ↥(L.subgroupOf R) => (z : LGL 2 V)) (mul_comm aA bA))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcenterA).trans QuotientGroup.quotientBot).trans
    (Subgroup.subgroupOfEquivOfLe h.le)⟩

private theorem w183b2_card_closure_pair {G : Type*} [Group G] [Finite G] {d f : G}
    (hd2 : d * d = 1) (hf2 : f * f = 1) (hdf : d * f = f * d)
    (hd1 : d ≠ 1) (hf1 : f ≠ 1) (hne : d ≠ f) :
    Nat.card (Subgroup.closure ({d, f} : Set G)) = 4 := by
  have hmem : ∀ x : G, x ∈ Subgroup.closure ({d, f} : Set G) ↔
      x = 1 ∨ x = d ∨ x = f ∨ x = d * f := by
    have hd' : ∀ y, d * (d * y) = y := fun y => by rw [← mul_assoc, hd2, one_mul]
    have hba : ∀ y, f * (d * y) = d * (f * y) := fun y => by
      rw [← mul_assoc, ← hdf, mul_assoc]
    have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
    intro x
    constructor
    · intro hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
      | one => exact Or.inl rfl
      | mul y z hy hz ihy ihz =>
          rcases ihy with rfl | rfl | rfl | rfl <;>
            rcases ihz with rfl | rfl | rfl | rfl <;>
            simp only [mul_assoc, hd2, hf2, hd', hba, hdf.symm, mul_one, one_mul,
              true_or, or_true]
      | inv y hy ihy =>
          rcases ihy with rfl | rfl | rfl | rfl <;>
            simp only [inv_one, hdi, hfi, mul_inv_rev, hdf.symm, true_or, or_true]
    · rintro (rfl | rfl | rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
  have hdf1 : d * f ≠ 1 := by
    intro h
    apply hne
    calc d = d * (f * f) := by rw [hf2, mul_one]
      _ = (d * f) * f := by rw [mul_assoc]
      _ = 1 * f := by rw [h]
      _ = f := one_mul f
  have hd_df : d ≠ d * f := by
    intro h
    exact hf1 (mul_left_cancel (by rw [mul_one]; exact h)).symm
  have hf_df : f ≠ d * f := by
    intro h
    exact hd1 (mul_right_cancel (by rw [one_mul]; exact h.symm))
  have hTcard : ({1, d, f, d * f} : Set G).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hd1.symm, hf1.symm, hdf1.symm⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hne, hd_df⟩),
        Set.ncard_insert_of_notMem (by
          simp only [Set.mem_singleton_iff]
          exact hf_df),
        Set.ncard_singleton]
  have hsub : ({1, d, f, d * f} : Set G) ⊆ (Subgroup.closure ({d, f} : Set G) : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have hfin : (Subgroup.closure ({d, f} : Set G) : Set G).Finite := Set.toFinite _
  have hle : ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard ≤ 4 := by
    calc ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard
        ≤ ({1, d, f, d * f} : Set G).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          intro x hx
          rcases (hmem x).mp hx with h | h | h | h <;> simp [h]
      _ ≤ 4 := by omega
  have hge : 4 ≤ ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard := by
    rw [← hTcard]
    exact Set.ncard_le_ncard hsub hfin
  change ((Subgroup.closure ({d, f} : Set G) : Set G)).ncard = 4
  exact le_antisymm hle hge

theorem w183b2_inner_of_quadratic (h65f : Asch6_5Four) (hcore : SimpleCore R L)
    (hshape : IsL3 ↥L 2) {D : Subgroup (LGL 2 V)} (hDR : D ≤ R) (hDe : IsElemAbelian 2 D)
    (hDq : commSpace D (commSub D) = ⊥) (hD : 3 ≤ mRank D) :
    imgOf (psiOf R L hcore.normal) D ≤ innAutOf ↥L := by
  classical
  intro x hx
  rw [imgOf, Subgroup.mem_map] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  rw [Subgroup.mem_subgroupOf] at hd
  let dL : LGL 2 V := (d : LGL 2 V)
  by_cases hd1 : dL = 1
  · have hd_eq : d = 1 := Subtype.ext hd1
    rw [hd_eq, map_one]
    exact Subgroup.one_mem _
  · obtain ⟨f, hfD, hfz⟩ : ∃ f ∈ D, f ∉ Subgroup.zpowers dL := by
      have hcardD : 8 ≤ Nat.card D := by
        have hne : Nat.card D ≠ 0 :=
          Nat.card_ne_zero.mpr ⟨⟨1, D.one_mem⟩, inferInstance⟩
        have hlog : 3 ≤ Nat.log 2 (Nat.card D) := by simpa [mRank] using hD
        have hpow : 2 ^ 3 ≤ Nat.card D := Nat.pow_le_of_le_log hne hlog
        simpa using hpow
      have hzple : Subgroup.zpowers dL ≤ D := Subgroup.zpowers_le.mpr hd
      have hcardzp : Nat.card (Subgroup.zpowers dL) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime (hDe.2 dL hd) hd1
      have hne : Subgroup.zpowers dL ≠ D := by
        intro heq
        rw [heq] at hcardzp
        omega
      exact (SetLike.lt_iff_le_and_exists.mp (lt_of_le_of_ne hzple hne)).2
    let A : Subgroup (LGL 2 V) := Subgroup.closure ({dL, f} : Set (LGL 2 V))
    have hdA : dL ∈ A := Subgroup.subset_closure (by simp)
    have hA_le_D : A ≤ D := (Subgroup.closure_le D).mpr (by
      rintro y (rfl | rfl)
      · exact hd
      · exact hfD)
    have hA_R : A ≤ R := hA_le_D.trans hDR
    have hf1 : f ≠ 1 := fun h =>
      hfz (h ▸ Subgroup.mem_zpowers_iff.mpr ⟨0, zpow_zero dL⟩)
    have hdf : dL ≠ f := fun h =>
      hfz (h ▸ Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one dL⟩)
    have hA_card : Nat.card A = 4 :=
      w183b2_card_closure_pair (d := dL) (f := f)
        (by simpa [pow_two] using hDe.2 dL hd)
        (by simpa [pow_two] using hDe.2 f hfD)
        (hDe.comm hd hfD) hd1 hf1 hdf
    have hA_e : IsElemAbelian 2 A := CFSG.Open.IsElemAbelian.mono hDe hA_le_D
    have hA_q : commSpace A (commSub A) = ⊥ := by
      rw [eq_bot_iff]
      calc commSpace A (commSub A)
          ≤ commSpace D (commSub D) :=
            CFSG.Quasithin.G11.commSpace_mono hA_le_D (commSub_mono A D hA_le_D)
        _ = ⊥ := hDq
    have hA_cent : A.subgroupOf R ⊓
        Subgroup.centralizer ((L.subgroupOf R : Subgroup ↥R) : Set ↥R) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyA, hyC⟩ := hy
      rw [Subgroup.mem_subgroupOf] at hyA
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      apply hcore.cent ((y : LGL 2 V)) (hDR (hA_le_D hyA))
      intro l hl
      have hl' : (⟨l, hcore.le hl⟩ : ↥R) ∈ L.subgroupOf R :=
        Subgroup.mem_subgroupOf.mpr hl
      have hyl := (Subgroup.mem_centralizer_iff.mp hyC) (⟨l, hcore.le hl⟩ : ↥R) hl'
      exact (congrArg Subtype.val hyl).symm
    have hV : ∀ v : Multiplicative V, v ^ 2 = 1 := by
      intro v
      have h : (v ^ 2).toAdd = 0 := by
        rw [toAdd_pow, two_nsmul, ZModModule.add_self]
      calc v ^ 2 = Multiplicative.ofAdd (v ^ 2).toAdd := (ofAdd_toAdd _).symm
        _ = Multiplicative.ofAdd 0 := by rw [h]
        _ = 1 := rfl
    have hLcomp : IsComponentOf (L.subgroupOf R) ⊤ := w183b2_isComponentOf_subgroupOf hcore
    have hAcard : Nat.card (A.subgroupOf R) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_R).toEquiv, hA_card]
    have hAe : IsElemAbelian 2 (A.subgroupOf R) := hA_e.subgroupOf R
    have hAq : IsQuadraticOn (actOnMul R) (A.subgroupOf R) := isQuadraticOn_actOnMul hA_q
    have hL_normal : (L.subgroupOf R).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hcore.le]
      intro h k hh hk
      exact hcore.normal k hk h hh
    have hAnorm : A.subgroupOf R ≤
        Subgroup.normalizer (L.subgroupOf R : Set ↥R) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hL_normal]
      exact le_top
    have hodd : Odd (Nat.card ↥(Subgroup.center ↥(L.subgroupOf R))) := by
      have hnabS : ∃ a b : ↥(L.subgroupOf R), a * b ≠ b * a := by
        obtain ⟨a, ha, b, hb, hab⟩ := hcore.nonab
        let aS : ↥(L.subgroupOf R) := ⟨⟨a, hcore.le ha⟩, Subgroup.mem_subgroupOf.mpr ha⟩
        let bS : ↥(L.subgroupOf R) := ⟨⟨b, hcore.le hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
        exact ⟨aS, bS, fun h => hab (by
          simpa using congrArg (fun z : ↥(L.subgroupOf R) => (z : LGL 2 V)) h)⟩
      have hcenter : Subgroup.center ↥(L.subgroupOf R) = ⊥ := by
        haveI : IsSimpleGroup ↥(L.subgroupOf R) := by
          haveI : IsSimpleGroup ↥L := hcore.simple
          exact (Subgroup.subgroupOfEquivOfLe hcore.le).isSimpleGroup
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center ↥(L.subgroupOf R)) with hc | hc
        · exact hc
        · exfalso
          obtain ⟨a, b, hab⟩ := hnabS
          have ha : a ∈ Subgroup.center ↥(L.subgroupOf R) := by rw [hc]; trivial
          exact hab (Subgroup.mem_center_iff.mp ha b).symm
      rw [hcenter, Subgroup.card_bot]
      norm_num
    have hinner := h65f (↥R) (Multiplicative V) hV (actOnMul R) (actOnMul_injective (R := R))
      (L.subgroupOf R) (A.subgroupOf R) hLcomp hodd hAnorm hAcard hAe hAq hA_cent
      (↥L) (inferInstance : Group ↥L) (Or.inl hshape) (w183b2_coverOf_subgroupOf hcore)
    obtain ⟨l, hl, hdl⟩ := hinner d (by rwa [Subgroup.mem_subgroupOf])
    have hlL : (l : LGL 2 V) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hpsi_one : psiOf R L hcore.normal (d * l⁻¹) = 1 := by
      ext x v
      have hxmem : (⟨(x : LGL 2 V), hcore.le x.2⟩ : ↥R) ∈ L.subgroupOf R :=
        Subgroup.mem_subgroupOf.mpr x.2
      have hx := (Subgroup.mem_centralizer_iff.mp hdl) _ hxmem
      have hx' : ((d * l⁻¹ : ↥R) : LGL 2 V) * (x : LGL 2 V) =
          (x : LGL 2 V) * ((d * l⁻¹ : ↥R) : LGL 2 V) := by
        simpa using congrArg (fun z : ↥R => (z : LGL 2 V)) hx.symm
      rw [psiOf_apply]
      rw [hx']
      simp
    have hpsi_eq : psiOf R L hcore.normal d = psiOf R L hcore.normal l := by
      have hd_eq : d = (d * l⁻¹) * l := by group
      rw [hd_eq, map_mul, hpsi_one, one_mul]
    have hpsi_l : psiOf R L hcore.normal l = MulAut.conj (⟨(l : LGL 2 V), hlL⟩ : ↥L) :=
      psiOf_eq_conj hcore hlL
    rw [show innAutOf ↥L = (MulAut.conj : ↥L →* MulAut ↥L).range from rfl, MonoidHom.mem_range]
    exact ⟨⟨(l : LGL 2 V), hlL⟩, (hpsi_eq.trans hpsi_l).symm⟩

end CFSG.LocalAnalysis.WeakClosure81

end
