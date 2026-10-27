module

public import CFSG.LinearAlgebra.QuadraticNormalSubgroupCore
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.LinearAlgebra CFSG.Open Subgroup
open CFSG.CGT.Timmesfeld75

variable {L : Type} [Group L] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def glAct (ρ : L →* LGL 2 W) : L →* MulAut (Multiplicative W) :=
  (linearAction (⊤ : Subgroup (LGL 2 W))).comp (ρ.codRestrict ⊤ fun _ => Subgroup.mem_top _)

abbrev VGL (ρ : L →* LGL 2 W) : Type := Multiplicative W ⋊[glAct ρ] L

theorem glAct_apply (ρ : L →* LGL 2 W) (l : L) (w : W) :
    glAct ρ l (Multiplicative.ofAdd w) = Multiplicative.ofAdd (ρ l w) := rfl

instance (ρ : L →* LGL 2 W) [Finite L] [Finite W] : Finite (VGL ρ) :=
  Finite.of_injective (fun x : VGL ρ => (x.left, x.right))
    fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

@[expose] noncomputable def zHat (ρ : L →* LGL 2 W) (Z : Submodule (ZMod 2) W) : Subgroup (VGL ρ) :=
  (AddSubgroup.toSubgroup Z.toAddSubgroup).map SemidirectProduct.inl

@[expose] noncomputable def aHatL (ρ : L →* LGL 2 W) (A : Subgroup L) : Subgroup (VGL ρ) :=
  A.map SemidirectProduct.inr

@[expose] noncomputable def a1L (ρ : L →* LGL 2 W) (Z : Submodule (ZMod 2) W) (A : Subgroup L) :
    Subgroup (VGL ρ) :=
  zHat ρ Z ⊔ aHatL ρ A

structure LiftHyp (ρ : L →* LGL 2 W) (A : Subgroup L) (Z : Submodule (ZMod 2) W) : Prop where
  elemAbelian : IsElemAbelian 2 A
  ne_bot_A : A ≠ ⊥
  fix : ∀ a ∈ A, ∀ z ∈ Z, ρ a z = z
  comm_le : ∀ a ∈ A, ∀ w : W, ρ a w - w ∈ Z
  faithful : ∀ a ∈ A, (∀ w : W, ρ a w = w) → a = 1
  ne_bot_Z : Z ≠ ⊥
  ti : ∀ l : L, Z ⊓ Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) ≠ ⊥ →
    Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z
  norm : ∀ l : L, Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z →
    l ∈ Subgroup.normalizer (A : Set L)

variable {ρ : L →* LGL 2 W} {A : Subgroup L} {Z : Submodule (ZMod 2) W}

private lemma w16l_mem_zHat {x : VGL ρ} :
    x ∈ zHat ρ Z ↔ ∃ z ∈ Z, x = SemidirectProduct.inl (Multiplicative.ofAdd z) := by
  unfold zHat
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨Multiplicative.toAdd m, by simpa using hm, by rw [ofAdd_toAdd]⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Multiplicative.ofAdd z, by simpa using hz, rfl⟩

private lemma w16l_mem_aHatL {x : VGL ρ} :
    x ∈ aHatL ρ A ↔ ∃ a ∈ A, x = SemidirectProduct.inr a := by
  unfold aHatL
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩
    exact ⟨a, ha, h.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

private lemma w16l_mul_eq (z z' : W) (a a' : L) :
    ((SemidirectProduct.inl (Multiplicative.ofAdd z) * SemidirectProduct.inr a : VGL ρ) *
      (SemidirectProduct.inl (Multiplicative.ofAdd z') * SemidirectProduct.inr a')) =
      (SemidirectProduct.inl (Multiplicative.ofAdd (z + ρ a z')) *
        SemidirectProduct.inr (a * a') : VGL ρ) := by
  ext <;> simp [glAct_apply, ofAdd_add]

private lemma w16l_inr_mul_inl (l : L) (z : W) :
    (SemidirectProduct.inr l : VGL ρ) * SemidirectProduct.inl (Multiplicative.ofAdd z) =
      SemidirectProduct.inl (Multiplicative.ofAdd (ρ l z)) * SemidirectProduct.inr l := by
  have h := SemidirectProduct.inl_aut (φ := glAct ρ) l (Multiplicative.ofAdd z)
  rw [glAct_apply] at h
  calc (SemidirectProduct.inr l : VGL ρ) * SemidirectProduct.inl (Multiplicative.ofAdd z)
      = ((SemidirectProduct.inr l : VGL ρ) * SemidirectProduct.inl (Multiplicative.ofAdd z) *
          (SemidirectProduct.inr l)⁻¹) * SemidirectProduct.inr l := by group
    _ = SemidirectProduct.inl (Multiplicative.ofAdd (ρ l z)) * SemidirectProduct.inr l := by
        rw [← map_inv (SemidirectProduct.inr) l, ← h]

private def w16l_prodSet (hA : LiftHyp ρ A Z) : Subgroup (VGL ρ) where
  carrier := {x | ∃ z ∈ Z, ∃ a ∈ A,
    x = SemidirectProduct.inl (Multiplicative.ofAdd z) * SemidirectProduct.inr a}
  mul_mem' := by
    rintro x y ⟨z, hz, a, ha, rfl⟩ ⟨z', hz', a', ha', rfl⟩
    refine ⟨z + z', Z.add_mem hz hz', a * a', A.mul_mem ha ha', ?_⟩
    rw [w16l_mul_eq, hA.fix a ha z' hz']
  one_mem' := ⟨0, Z.zero_mem, 1, A.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨z, hz, a, ha, rfl⟩
    refine ⟨-z, Z.neg_mem hz, a⁻¹, A.inv_mem ha, ?_⟩
    rw [mul_inv_rev,
      show (SemidirectProduct.inr a : VGL ρ)⁻¹ = SemidirectProduct.inr a⁻¹ from
        (map_inv (SemidirectProduct.inr) a).symm,
      show (SemidirectProduct.inl (Multiplicative.ofAdd z) : VGL ρ)⁻¹ =
          SemidirectProduct.inl (Multiplicative.ofAdd (-z)) from by
        rw [← map_inv, ← ofAdd_neg],
      w16l_inr_mul_inl, hA.fix a⁻¹ (A.inv_mem ha) (-z) (Z.neg_mem hz)]

private lemma w16l_mem_prodSet (hA : LiftHyp ρ A Z) {x : VGL ρ} :
    x ∈ w16l_prodSet hA ↔ ∃ z ∈ Z, ∃ a ∈ A,
      x = SemidirectProduct.inl (Multiplicative.ofAdd z) * SemidirectProduct.inr a :=
  Iff.rfl

private lemma w16l_le_prodSet (hA : LiftHyp ρ A Z) : a1L ρ Z A ≤ w16l_prodSet hA := by
  refine sup_le ?_ ?_
  · intro x hx
    rw [w16l_mem_zHat] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨z, hz, 1, A.one_mem, by simp⟩
  · intro x hx
    rw [w16l_mem_aHatL] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨0, Z.zero_mem, a, ha, by simp⟩

private lemma w16l_prodSet_le (hA : LiftHyp ρ A Z) : w16l_prodSet hA ≤ a1L ρ Z A := by
  intro x hx
  rw [w16l_mem_prodSet hA] at hx
  obtain ⟨z, hz, a, ha, rfl⟩ := hx
  exact mul_mem_sup ((w16l_mem_zHat).2 ⟨z, hz, rfl⟩) ((w16l_mem_aHatL).2 ⟨a, ha, rfl⟩)

private lemma w16l_mem_a1L_iff (hA : LiftHyp ρ A Z) {x : VGL ρ} :
    x ∈ a1L ρ Z A ↔ ∃ z ∈ Z, ∃ a ∈ A,
      x = SemidirectProduct.inl (Multiplicative.ofAdd z) * SemidirectProduct.inr a := by
  constructor
  · intro hx
    exact (w16l_mem_prodSet hA).1 (w16l_le_prodSet hA hx)
  · intro hx
    exact w16l_prodSet_le hA ((w16l_mem_prodSet hA).2 hx)

private lemma w16l_rho_conj_apply (l a : L) (u : W) :
    ρ (l * a * l⁻¹) u = ρ l (ρ a ((ρ l).symm u)) := by
  rw [map_mul, map_mul, map_inv]
  rfl

private lemma w16l_conj_gen (u z : W) (l a : L) :
    ((SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr l : VGL ρ) *
      (SemidirectProduct.inl (Multiplicative.ofAdd z) * SemidirectProduct.inr a) *
      (SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr l)⁻¹) =
      (SemidirectProduct.inl (Multiplicative.ofAdd (u + ρ l z - ρ (l * a * l⁻¹) u)) *
        SemidirectProduct.inr (l * a * l⁻¹) : VGL ρ) := by
  rw [← mul_right_cancel_iff (a := SemidirectProduct.inl (Multiplicative.ofAdd u) *
    SemidirectProduct.inr l)]
  rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [w16l_mul_eq, w16l_mul_eq]
  rw [show (u + ρ l z - ρ (l * a * l⁻¹) u) + ρ (l * a * l⁻¹) u = u + ρ l z by abel,
    show l * a * l⁻¹ * l = l * a by group]

private lemma w16l_conj_trans_mem (hA : LiftHyp ρ A Z) (u : W) (l : L) {z : W} (hz : z ∈ Z)
    {a : L} (ha : a ∈ A) :
    u + ρ l z - ρ (l * a * l⁻¹) u ∈
      Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) := by
  rw [Submodule.mem_map]
  refine ⟨z + ((ρ l).symm u - ρ a ((ρ l).symm u)), ?_, ?_⟩
  · refine Z.add_mem hz ?_
    simpa only [neg_sub] using Z.neg_mem (hA.comm_le a ha ((ρ l).symm u))
  · have hρ : ρ (l * a * l⁻¹) u = ρ l (ρ a ((ρ l).symm u)) := w16l_rho_conj_apply l a u
    simp only [map_add, map_sub, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hρ]
    abel

private lemma w16l_conj_mem_representation (hA : LiftHyp ρ A Z) (u : W) (l : L) {x : VGL ρ}
    (hx : x ∈ conjSubgroup (SemidirectProduct.inl (Multiplicative.ofAdd u) *
      SemidirectProduct.inr l) (a1L ρ Z A)) :
    ∃ z ∈ Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W),
      ∃ a ∈ A.map (MulAut.conj l).toMonoidHom,
        x = SemidirectProduct.inl (Multiplicative.ofAdd z) * SemidirectProduct.inr a := by
  unfold conjSubgroup at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [w16l_mem_a1L_iff hA] at hy
  obtain ⟨z, hz, a, ha, hy⟩ := hy
  have hx' : x = SemidirectProduct.inl (Multiplicative.ofAdd (u + ρ l z - ρ (l * a * l⁻¹) u)) *
      SemidirectProduct.inr (l * a * l⁻¹) := by
    rw [← hyx, hy]
    change MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd u) *
        SemidirectProduct.inr l) (SemidirectProduct.inl (Multiplicative.ofAdd z) *
        SemidirectProduct.inr a) =
      (SemidirectProduct.inl (Multiplicative.ofAdd (u + ρ l z - ρ (l * a * l⁻¹) u)) *
        SemidirectProduct.inr (l * a * l⁻¹) : VGL ρ)
    rw [MulAut.conj_apply, w16l_conj_gen]
  exact ⟨u + ρ l z - ρ (l * a * l⁻¹) u, w16l_conj_trans_mem hA u l hz ha,
    l * a * l⁻¹, by rw [Subgroup.mem_map]; exact ⟨a, ha, rfl⟩, hx'⟩

theorem LiftHyp.mem_a1L_iff (hA : LiftHyp ρ A Z) {x : VGL ρ} :
    x ∈ a1L ρ Z A ↔ ∃ z ∈ Z, ∃ a ∈ A,
      x = SemidirectProduct.inl (Multiplicative.ofAdd z) * SemidirectProduct.inr a :=
  w16l_mem_a1L_iff hA

theorem LiftHyp.isElemAbelian_a1L [Finite L] [Finite W] (hA : LiftHyp ρ A Z) :
    IsElemAbelian 2 (a1L ρ Z A) := by
  refine ⟨IsMulCommutative.of_comm fun x y => ?_, ?_⟩
  · apply Subtype.ext
    change (x : VGL ρ) * (y : VGL ρ) = (y : VGL ρ) * (x : VGL ρ)
    obtain ⟨z, hz, a, ha, hx⟩ := (w16l_mem_a1L_iff hA).1 x.2
    obtain ⟨z', hz', a', ha', hy⟩ := (w16l_mem_a1L_iff hA).1 y.2
    rw [hx, hy, w16l_mul_eq, w16l_mul_eq]
    rw [hA.fix a ha z' hz', hA.fix a' ha' z hz]
    congr 1
    · rw [SemidirectProduct.inl_inj]
      exact congrArg Multiplicative.ofAdd (add_comm (z : W) (z' : W))
    · rw [SemidirectProduct.inr_inj]
      haveI : IsMulCommutative A := hA.elemAbelian.1
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨a', ha'⟩ : A))
  · intro x hx
    rw [pow_two]
    obtain ⟨z, hz, a, ha, hx⟩ := (w16l_mem_a1L_iff hA).1 hx
    rw [hx, w16l_mul_eq, hA.fix a ha z hz]
    have hzz : (z : W) + (z : W) = 0 := by
      rw [← two_smul (ZMod 2) (z : W), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    have haa : (a : L) * (a : L) = 1 := by
      have := hA.elemAbelian.2 a ha
      rwa [pow_two] at this
    rw [hzz, haa]
    simp

theorem LiftHyp.card_a1L [Finite L] [Finite W] (hA : LiftHyp ρ A Z) :
    Nat.card (a1L ρ Z A) = Nat.card Z * Nat.card A := by
  let f : Z × A → a1L ρ Z A := fun p =>
    ⟨SemidirectProduct.inl (Multiplicative.ofAdd (p.1 : W)) *
        SemidirectProduct.inr (p.2 : L),
      (w16l_mem_a1L_iff hA).2 ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨z, a⟩ ⟨z', a'⟩ hxy
      have h : SemidirectProduct.inl (Multiplicative.ofAdd (z : W)) *
            SemidirectProduct.inr (a : L) =
          SemidirectProduct.inl (Multiplicative.ofAdd (z' : W)) *
            SemidirectProduct.inr (a' : L) := congrArg Subtype.val hxy
      have hright : (a : L) = (a' : L) := by
        have := congrArg SemidirectProduct.right h
        simpa using this
      have hleft : (z : W) = (z' : W) := by
        have := congrArg SemidirectProduct.left h
        exact Multiplicative.ofAdd.injective (by simpa using this)
      exact Prod.ext (Subtype.ext hleft) (Subtype.ext hright)
    · rintro ⟨x, hx⟩
      obtain ⟨z, hz, a, ha, hx⟩ := (w16l_mem_a1L_iff hA).1 hx
      exact ⟨(⟨z, hz⟩, ⟨a, ha⟩), Subtype.ext hx.symm⟩
  rw [← Nat.card_eq_of_bijective f hf]
  exact Nat.card_prod Z A

theorem LiftHyp.isTI_a1L [Finite L] [Finite W] (hA : LiftHyp ρ A Z) : IsTI (a1L ρ Z A) := by
  intro g
  obtain ⟨u, l, hg⟩ : ∃ u : W, ∃ l : L,
      g = SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr l :=
    ⟨Multiplicative.toAdd g.left, g.right, by
      rw [ofAdd_toAdd, SemidirectProduct.inl_left_mul_inr_right]⟩
  let gg : VGL ρ := SemidirectProduct.inl (Multiplicative.ofAdd u) * SemidirectProduct.inr l
  have hgg : g = gg := hg
  rw [hgg]
  let Z' : Submodule (ZMod 2) W := Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
  let A' : Subgroup L := A.map (MulAut.conj l).toMonoidHom
  by_cases htriv : a1L ρ Z A ⊓ conjSubgroup gg (a1L ρ Z A) = ⊥
  · exact Or.inl htriv
  · right
    have hZne : Z ⊓ Z' ≠ ⊥ := by
      obtain ⟨x, hxne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 htriv
      have hxT : (x : VGL ρ) ∈ a1L ρ Z A := x.2.1
      have hxconj : (x : VGL ρ) ∈ conjSubgroup gg (a1L ρ Z A) := x.2.2
      obtain ⟨z1, hz1, a1, ha1, hx1⟩ := (w16l_mem_a1L_iff hA).1 hxT
      obtain ⟨z2, hz2, a2, ha2, hx2⟩ := w16l_conj_mem_representation hA u l hxconj
      have hright : a1 = a2 := by
        have h := congrArg SemidirectProduct.right (hx1.symm.trans hx2)
        simpa using h
      have hleft : z1 = z2 := by
        have h := congrArg SemidirectProduct.left (hx1.symm.trans hx2)
        exact Multiplicative.ofAdd.injective (by simpa using h)
      have hz1Z' : z1 ∈ Z' := by rw [hleft]; exact hz2
      have hmem : z1 ∈ Z ⊓ Z' := ⟨hz1, hz1Z'⟩
      by_cases hz1zero : z1 = 0
      · have ha1ne : a1 ≠ 1 := by
          intro h
          apply hxne
          apply Subtype.ext
          rw [hx1, hz1zero, h]
          simp
        have hnotfix : ¬ ∀ w : W, ρ a1 w = w :=
          fun h => ha1ne (hA.faithful a1 ha1 h)
        obtain ⟨w, hw⟩ := not_forall.1 hnotfix
        obtain ⟨a0, ha0, ha0eq⟩ := (Subgroup.mem_map).1 ha2
        have ha2eq : a2 = l * a0 * l⁻¹ := by
          have h2 : a2 = MulAut.conj l a0 := ha0eq.symm
          rwa [MulAut.conj_apply] at h2
        have hρa : ρ a1 w = ρ l (ρ a0 ((ρ l).symm w)) := by
          rw [hright, ha2eq, w16l_rho_conj_apply]
        have hzZ' : ρ a1 w - w ∈ Z' := by
          change ρ a1 w - w ∈ Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
          rw [hρa, Submodule.mem_map]
          refine ⟨ρ a0 ((ρ l).symm w) - (ρ l).symm w, hA.comm_le a0 ha0 ((ρ l).symm w), ?_⟩
          simp only [map_sub, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        exact (Submodule.ne_bot_iff (Z ⊓ Z')).2
          ⟨ρ a1 w - w, ⟨hA.comm_le a1 ha1 w, hzZ'⟩, sub_ne_zero.2 hw⟩
      · exact (Submodule.ne_bot_iff (Z ⊓ Z')).2 ⟨z1, hmem, hz1zero⟩
    have hZ' : Z' = Z := by
      change Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z
      exact hA.ti l hZne
    have hA' : A' = A := by
      have hmapZ : Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z := by
        change Z' = Z
        exact hZ'
      have hl : l ∈ Subgroup.normalizer (A : Set L) := hA.norm l hmapZ
      have hmem := (Subgroup.mem_normalizer_iff_map_conj_eq (H := A) (g := l)).1 hl
      change A.map (MulAut.conj l).toMonoidHom = A
      simpa only [MulEquiv.toMonoidHom_eq_coe] using hmem
    have hZmap : Z.map ((ρ l : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = Z := hZ'
    have hAmap : A.map (MulAut.conj l).toMonoidHom = A := hA'
    have hconj : conjSubgroup gg (a1L ρ Z A) = a1L ρ Z A := by
      have hle : conjSubgroup gg (a1L ρ Z A) ≤ a1L ρ Z A := by
        intro x hx
        obtain ⟨z, hz, a, ha, rfl⟩ := w16l_conj_mem_representation hA u l hx
        rw [w16l_mem_a1L_iff hA]
        refine ⟨z, ?_, a, ?_, rfl⟩
        · rwa [hZmap] at hz
        · rwa [hAmap] at ha
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      exact le_of_eq (Subgroup.card_map_of_injective
        (K := a1L ρ Z A) (f := (MulAut.conj gg).toMonoidHom) (MulAut.conj gg).injective).symm
    rw [hconj, inf_idem]

theorem LiftHyp.hyp7_a1L [Finite L] [Finite W] (hA : LiftHyp ρ A Z) : Hyp7 (a1L ρ Z A) := by
  refine ⟨hA.isElemAbelian_a1L, ?_, hA.isTI_a1L⟩
  rw [hA.card_a1L]
  have hZ2 : 2 ≤ Nat.card Z := by
    haveI : Nontrivial Z := (Submodule.nontrivial_iff_ne_bot).2 hA.ne_bot_Z
    exact Nat.succ_le_of_lt Finite.one_lt_card
  have hA2 : 2 ≤ Nat.card A := by
    haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA.ne_bot_A
    exact Nat.succ_le_of_lt Finite.one_lt_card
  calc 2 < 2 * 2 := by norm_num
    _ ≤ Nat.card Z * Nat.card A := Nat.mul_le_mul hZ2 hA2

end CFSG.LocalAnalysis.WeakClosure81

end
