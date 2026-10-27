module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarFanoB
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private def s16t3_char (L : Subgroup (MulAut W)) (x y z : Subgroup W) : Prop :=
  z ∈ irrSet L ∧ z ≠ x ∧ z ≠ y ∧
    tilde L (⊤ : Subgroup W) z ≤ tilde L (⊤ : Subgroup W) x ⊔ tilde L (⊤ : Subgroup W) y

private theorem s16t3_char_comm (L : Subgroup (MulAut W)) (x y z : Subgroup W)
    (h : s16t3_char L x y z) : s16t3_char L y x z := by
  obtain ⟨hz, hzx, hzy, hle⟩ := h
  exact ⟨hz, hzy, hzx, by rwa [sup_comm]⟩

private noncomputable def s16t3_third (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (x y : ↥(irrSet L)) : ↥(irrSet L) := by
  classical
  exact if hxy : x = y then x
  else
    ⟨Classical.choose ((s16t3_exists_unique_third h h7 x.2 y.2
        (fun hsub => hxy (Subtype.ext hsub))).1.exists),
      (Classical.choose_spec ((s16t3_exists_unique_third h h7 x.2 y.2
        (fun hsub => hxy (Subtype.ext hsub))).1.exists)).1⟩

private theorem s16t3_third_self (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (x : ↥(irrSet L)) :
    s16t3_third h h7 x x = x := by
  unfold s16t3_third
  rw [dif_pos rfl]

private theorem s16t3_third_of_ne (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) {x y : ↥(irrSet L)} (hxy : x ≠ y) :
    (s16t3_third h h7 x y : Subgroup W) =
      Classical.choose ((s16t3_exists_unique_third h h7 x.2 y.2
        (fun hsub => hxy (Subtype.ext hsub))).1.exists) := by
  unfold s16t3_third
  rw [dif_neg hxy]

private theorem s16t3_third_spec (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) {x y : ↥(irrSet L)} (hxy : x ≠ y) :
    s16t3_char L (x : Subgroup W) (y : Subgroup W) (s16t3_third h h7 x y : Subgroup W) := by
  rw [s16t3_third_of_ne h h7 hxy]
  exact Classical.choose_spec ((s16t3_exists_unique_third h h7 x.2 y.2
    (fun hsub => hxy (Subtype.ext hsub))).1.exists)

private theorem s16t3_third_eq_of_char (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) {x y : ↥(irrSet L)} (hxy : x ≠ y) {z : Subgroup W}
    (hz : s16t3_char L (x : Subgroup W) (y : Subgroup W) z) :
    z = (s16t3_third h h7 x y : Subgroup W) := by
  have hexu : ∃! w : Subgroup W, s16t3_char L (x : Subgroup W) (y : Subgroup W) w :=
    (s16t3_exists_unique_third h h7 x.2 y.2 (fun hsub => hxy (Subtype.ext hsub))).1
  have hspec : s16t3_char L (x : Subgroup W) (y : Subgroup W)
      (s16t3_third h h7 x y : Subgroup W) := s16t3_third_spec h h7 hxy
  exact (ExistsUnique.unique hexu hspec hz).symm

private theorem s16t3_map_mem_irrSet_of_mem {A L : Subgroup (MulAut W)}
    (hA : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {g : MulAut W} (hg : g ∈ A)
    {I : Subgroup W} (hI : I ∈ irrSet L) : I.map g.toMonoidHom ∈ irrSet L :=
  CFSG.LocalAnalysis.WeakClosure81.map_mem_irrSet
    (fun x hx => (Subgroup.mem_normalizer_iff.1 (hA hg) x).1 hx)
    (fun x hx => by
      have := (Subgroup.mem_normalizer_iff.1 (hA (A.inv_mem hg)) x).1 hx
      simpa using this) hI

private noncomputable def s16t3_ptActFun (h : ThreeNat A L T) (a : ↥A) :
    Equiv.Perm ↥(irrSet L) :=
  Equiv.ofBijective
    (fun I : ↥(irrSet L) =>
      ⟨(I : Subgroup W).map (a : MulAut W).toMonoidHom,
        s16t3_map_mem_irrSet_of_mem h.normal a.2 I.2⟩)
    ⟨fun I I' hII' => Subtype.ext
        (Subgroup.map_injective (MulEquiv.injective (a : MulAut W))
          (Subtype.ext_iff.mp hII')),
     fun I' => ⟨⟨(I' : Subgroup W).map ((a : MulAut W)⁻¹).toMonoidHom,
        s16t3_map_mem_irrSet_of_mem h.normal (A.inv_mem a.2) I'.2⟩, by
       apply Subtype.ext
       show ((I' : Subgroup W).map ((a : MulAut W)⁻¹).toMonoidHom).map
           (a : MulAut W).toMonoidHom = (I' : Subgroup W)
       rw [Subgroup.map_map]
       have hcomp : (a : MulAut W).toMonoidHom.comp ((a : MulAut W)⁻¹).toMonoidHom =
           MonoidHom.id W := by ext w; simp
       rw [hcomp, Subgroup.map_id]⟩⟩

private noncomputable def s16t3_ptAct (h : ThreeNat A L T) :
    ↥A →* Equiv.Perm ↥(irrSet L) where
  toFun := s16t3_ptActFun h
  map_one' := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    change (I : Subgroup W).map (1 : MulAut W).toMonoidHom = (I : Subgroup W)
    rw [show (1 : MulAut W).toMonoidHom = MonoidHom.id W from rfl, Subgroup.map_id]
  map_mul' a b := by
    apply Equiv.ext
    intro I
    apply Subtype.ext
    change (I : Subgroup W).map ((a * b : ↥A) : MulAut W).toMonoidHom =
      ((I : Subgroup W).map (b : MulAut W).toMonoidHom).map (a : MulAut W).toMonoidHom
    rw [Subgroup.map_map]
    congr 1

private theorem s16t3_ptAct_apply (h : ThreeNat A L T) (a : ↥A) (x : ↥(irrSet L)) :
    (s16t3_ptAct h a x : Subgroup W) =
      (x : Subgroup W).map (a : MulAut W).toMonoidHom := rfl

private theorem s16t3_tilde_map_le_sup {A L : Subgroup (MulAut W)}
    (hA : A ≤ Subgroup.normalizer (L : Set (MulAut W))) {a : MulAut W} (ha : a ∈ A)
    {J₁ J₂ J₃ : Subgroup W}
    (hle : tilde L (⊤ : Subgroup W) J₁ ≤
      tilde L (⊤ : Subgroup W) J₂ ⊔ tilde L (⊤ : Subgroup W) J₃) :
    tilde L (⊤ : Subgroup W) (J₁.map a.toMonoidHom) ≤
      tilde L (⊤ : Subgroup W) (J₂.map a.toMonoidHom) ⊔
        tilde L (⊤ : Subgroup W) (J₃.map a.toMonoidHom) := by
  letI : MulDistribMulAction ↥(Subgroup.normalizer (L : Set (MulAut W)))
      (W ⧸ modFix L (⊤ : Subgroup W)) :=
    quotAct (X := L) (W := (⊤ : Subgroup W)) le_rfl (fun _ _ _ _ => trivial)
  let t : ↥(Subgroup.normalizer (L : Set (MulAut W))) := ⟨a, hA ha⟩
  let f : (W ⧸ modFix L (⊤ : Subgroup W)) →* (W ⧸ modFix L (⊤ : Subgroup W)) :=
    MulDistribMulAction.toMonoidEnd (↥(Subgroup.normalizer (L : Set (MulAut W))))
      (W ⧸ modFix L (⊤ : Subgroup W)) t
  have hmap : ∀ J : Subgroup W,
      tilde L (⊤ : Subgroup W) (J.map a.toMonoidHom) = (tilde L (⊤ : Subgroup W) J).map f := by
    intro J
    have h1 := tilde_smul (X := L) (W := (⊤ : Subgroup W)) le_rfl
      (fun _ _ _ _ => trivial) t J
    rw [Subgroup.pointwise_smul_def] at h1
    exact h1.symm
  calc tilde L (⊤ : Subgroup W) (J₁.map a.toMonoidHom)
      = (tilde L (⊤ : Subgroup W) J₁).map f := hmap J₁
    _ ≤ ((tilde L (⊤ : Subgroup W) J₂ ⊔ tilde L (⊤ : Subgroup W) J₃).map f) :=
        Subgroup.map_mono hle
    _ = (tilde L (⊤ : Subgroup W) J₂).map f ⊔ (tilde L (⊤ : Subgroup W) J₃).map f :=
        Subgroup.map_sup _ _ f
    _ = tilde L (⊤ : Subgroup W) (J₂.map a.toMonoidHom) ⊔
          tilde L (⊤ : Subgroup W) (J₃.map a.toMonoidHom) := by rw [hmap J₂, hmap J₃]

theorem s16t3_exists_fano_structure (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7) :
    ∃ (third : ↥(irrSet L) → ↥(irrSet L) → ↥(irrSet L))
      (ptAct : ↥A →* Equiv.Perm ↥(irrSet L)),
      (∀ a x, (ptAct a x : Subgroup W) =
        (x : Subgroup W).map (a : MulAut W).toMonoidHom) ∧
      (∀ x y, x ≠ y → third x y ≠ x ∧ third x y ≠ y) ∧
      (∀ x y, third x y = third y x) ∧
      (∀ x y, x ≠ y → third x (third x y) = y) ∧
      (∀ a x y, ptAct a (third x y) = third (ptAct a x) (ptAct a y)) := by
  classical
  refine ⟨s16t3_third h h7, s16t3_ptAct h, ?_, ?_, ?_, ?_, ?_⟩
  · intro a x
    rfl
  · intro x y hxy
    have hz := s16t3_third_spec h h7 hxy
    exact ⟨fun heq => hz.2.1 (congrArg Subtype.val heq),
      fun heq => hz.2.2.1 (congrArg Subtype.val heq)⟩
  · intro x y
    by_cases hxy : x = y
    · rw [hxy]
    · have hchar : s16t3_char L (y : Subgroup W) (x : Subgroup W)
          (s16t3_third h h7 x y : Subgroup W) :=
        s16t3_char_comm L _ _ _ (s16t3_third_spec h h7 hxy)
      have h1 := s16t3_third_eq_of_char (h := h) (h7 := h7) (x := y) (y := x)
        (Ne.symm hxy) hchar
      exact Subtype.ext h1
  · intro x y hxy
    have hz := s16t3_third_spec h h7 hxy
    have hxz : x ≠ s16t3_third h h7 x y :=
      fun heq => hz.2.1 (congrArg Subtype.val heq).symm
    have hpair := (s16t3_exists_unique_third h h7 x.2 y.2
      (fun hsub => hxy (Subtype.ext hsub))).2
    have hsup := hpair (s16t3_third h h7 x y) hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    have hle : tilde L (⊤ : Subgroup W) (y : Subgroup W) ≤
        tilde L (⊤ : Subgroup W) (x : Subgroup W) ⊔
          tilde L (⊤ : Subgroup W) (s16t3_third h h7 x y : Subgroup W) := by
      rw [hsup]
      exact le_sup_right
    have hchar : s16t3_char L (x : Subgroup W)
        (s16t3_third h h7 x y : Subgroup W) (y : Subgroup W) :=
      ⟨y.2, fun hsub => hxy (Subtype.ext hsub.symm), fun heq => hz.2.2.1 heq.symm, hle⟩
    have h2 := s16t3_third_eq_of_char (h := h) (h7 := h7) (x := x)
      (y := s16t3_third h h7 x y) hxz hchar
    exact Subtype.ext h2.symm
  · intro a x y
    by_cases hxy : x = y
    · rw [hxy, s16t3_third_self, s16t3_third_self]
    · have hz := s16t3_third_spec h h7 hxy
      have hchar : s16t3_char L (s16t3_ptAct h a x : Subgroup W)
          (s16t3_ptAct h a y : Subgroup W)
          (s16t3_ptAct h a (s16t3_third h h7 x y) : Subgroup W) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [s16t3_ptAct_apply]
          exact s16t3_map_mem_irrSet_of_mem h.normal a.2 hz.1
        · rw [s16t3_ptAct_apply, s16t3_ptAct_apply]
          exact fun hsub =>
            hz.2.1 (Subgroup.map_injective (MulEquiv.injective (a : MulAut W)) hsub)
        · rw [s16t3_ptAct_apply, s16t3_ptAct_apply]
          exact fun hsub =>
            hz.2.2.1 (Subgroup.map_injective (MulEquiv.injective (a : MulAut W)) hsub)
        · rw [s16t3_ptAct_apply, s16t3_ptAct_apply, s16t3_ptAct_apply]
          exact s16t3_tilde_map_le_sup h.normal a.2 hz.2.2.2
      have hne' : s16t3_ptAct h a x ≠ s16t3_ptAct h a y :=
        fun heq => hxy ((s16t3_ptAct h a).injective heq)
      have h2 := s16t3_third_eq_of_char (h := h) (h7 := h7)
        (x := s16t3_ptAct h a x) (y := s16t3_ptAct h a y) hne' hchar
      exact Subtype.ext h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
