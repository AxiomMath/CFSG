module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNCells
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def bCoordExtFun {p m : ℕ} (i0 : Fin (m + 1))
    (u : MulAut (Fin m → Multiplicative (ZMod p)))
    (f : Fin (m + 1) → Multiplicative (ZMod p)) :
    Fin (m + 1) → Multiplicative (ZMod p) :=
  Fin.insertNth i0 (f i0) (u (fun j => f (i0.succAbove j)))

private lemma bCoordExtFun_comp {p m : ℕ} (i0 : Fin (m + 1))
    (u v : MulAut (Fin m → Multiplicative (ZMod p)))
    (f : Fin (m + 1) → Multiplicative (ZMod p)) :
    bCoordExtFun i0 u (bCoordExtFun i0 v f) = bCoordExtFun i0 (u * v) f := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove i0 i with rfl | ⟨j, rfl⟩ <;>
    simp [bCoordExtFun]

private lemma bCoordExtFun_one {p m : ℕ} (i0 : Fin (m + 1))
    (f : Fin (m + 1) → Multiplicative (ZMod p)) :
    bCoordExtFun i0 (1 : MulAut (Fin m → Multiplicative (ZMod p))) f = f := by
  change Fin.insertNth i0 (f i0) (Fin.removeNth i0 f) = f
  exact Fin.insertNth_self_removeNth i0 f

private lemma bCoordExtFun_mul {p m : ℕ} (i0 : Fin (m + 1))
    (u : MulAut (Fin m → Multiplicative (ZMod p)))
    (f g : Fin (m + 1) → Multiplicative (ZMod p)) :
    bCoordExtFun i0 u (f * g) = bCoordExtFun i0 u f * bCoordExtFun i0 u g := by
  funext i
  rcases Fin.eq_self_or_eq_succAbove i0 i with rfl | ⟨j, rfl⟩
  · simp [bCoordExtFun]
  · unfold bCoordExtFun
    simp only [Fin.insertNth_apply_succAbove, Pi.mul_apply]
    change u ((fun j => f (i0.succAbove j)) * (fun j => g (i0.succAbove j))) j =
      u (fun j => f (i0.succAbove j)) j * u (fun j => g (i0.succAbove j)) j
    rw [map_mul]
    rfl

private def bCoordExt (p m : ℕ) (i0 : Fin (m + 1)) :
    MulAut (Fin m → Multiplicative (ZMod p)) →*
      MulAut (Fin (m + 1) → Multiplicative (ZMod p)) where
  toFun u :=
    { toFun := bCoordExtFun i0 u
      invFun := bCoordExtFun i0 u⁻¹
      left_inv f := by
        rw [bCoordExtFun_comp, inv_mul_cancel, bCoordExtFun_one]
      right_inv f := by
        rw [bCoordExtFun_comp, mul_inv_cancel, bCoordExtFun_one]
      map_mul' f g := bCoordExtFun_mul i0 u f g }
  map_one' := by
    apply MulEquiv.ext
    intro f
    exact bCoordExtFun_one i0 f
  map_mul' u v := by
    apply MulEquiv.ext
    intro f
    change bCoordExtFun i0 (u * v) f = bCoordExtFun i0 u (bCoordExtFun i0 v f)
    exact (bCoordExtFun_comp i0 u v f).symm

private lemma bCoordExt_apply {p m : ℕ} (i0 : Fin (m + 1))
    (u : MulAut (Fin m → Multiplicative (ZMod p)))
    (f : Fin (m + 1) → Multiplicative (ZMod p)) :
    bCoordExt p m i0 u f = bCoordExtFun i0 u f := rfl

private lemma bCoordExt_sgnAut {p m : ℕ} (i0 : Fin (m + 1)) (j : Fin m) :
    bCoordExt p m i0 (SpCoord.sgnAut j) = SpCoord.sgnAut (i0.succAbove j) := by
  ext f i
  rcases Fin.eq_self_or_eq_succAbove i0 i with h | ⟨k, hk⟩
  · subst i
    simp [bCoordExt_apply, bCoordExtFun, SpCoord.sgnAut_apply]
  · subst i
    simp only [bCoordExt_apply, bCoordExtFun, SpCoord.sgnAut_apply,
      Fin.insertNth_apply_succAbove]
    by_cases h : k = j
    · subst h
      simp
    · have h' : i0.succAbove k ≠ i0.succAbove j :=
        fun hh => h (Fin.succAbove_right_injective hh)
      rw [Function.update_of_ne h, Function.update_of_ne h']

private lemma bCoordExt_permAut {p m : ℕ} (i0 : Fin (m + 1)) (a b : Fin m) :
    bCoordExt p m i0 (SpCoord.permAut (Equiv.swap a b)) =
      SpCoord.permAut (Equiv.swap (i0.succAbove a) (i0.succAbove b)) := by
  ext f i
  rcases Fin.eq_self_or_eq_succAbove i0 i with h | ⟨k, hk⟩
  · subst i
    rw [bCoordExt_apply, bCoordExtFun, Fin.insertNth_apply_same, SpCoord.permAut_apply,
      Equiv.swap_inv, Function.comp_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Fin.succAbove_ne i0 a).symm (Fin.succAbove_ne i0 b).symm]
  · subst i
    simp only [bCoordExt_apply, bCoordExtFun, SpCoord.permAut_apply, Function.comp_apply,
      Fin.insertNth_apply_succAbove, Equiv.swap_inv]
    rw [(Fin.succAbove_right_injective (p := i0)).swap_apply a b k]

private lemma bCoordExt_injective (p m : ℕ) (i0 : Fin (m + 1)) :
    Function.Injective (bCoordExt p m i0) := by
  intro u v h
  ext g j
  have h2 := congrFun (congrArg (fun e : MulAut (Fin (m + 1) → Multiplicative (ZMod p)) =>
      e (Fin.insertNth i0 (1 : Multiplicative (ZMod p)) g)) h) (i0.succAbove j)
  simpa [bCoordExt_apply, bCoordExtFun] using h2

theorem card_bCoordinateBlock {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (i0 : Fin n) :
    Nat.card ↥(bCoordinateBlock n p i0) = 2 ^ (n - 1) * (n - 1).factorial := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fin.pos i0).ne'
  have hm : m + 1 - 1 = m := by omega
  rw [hm]
  have hmap : (bSignedFull m p).map (bCoordExt p m i0) = bCoordinateBlock (m + 1) p i0 := by
    rw [bSignedFull, bCoordinateBlock, MonoidHom.map_closure]
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      rcases hs with ⟨j, rfl⟩ | ⟨a, b, hab, rfl⟩
      · rw [bCoordExt_sgnAut]
        exact Or.inl ⟨i0.succAbove j, Fin.succAbove_ne i0 j, rfl⟩
      · rw [bCoordExt_permAut i0 a b]
        exact Or.inr ⟨i0.succAbove a, i0.succAbove b,
          fun h => hab (Fin.succAbove_right_injective h), Fin.succAbove_ne i0 a,
          Fin.succAbove_ne i0 b, rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨a, b, hab, ha, hb, rfl⟩)
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
        exact ⟨SpCoord.sgnAut j, Or.inl ⟨j, rfl⟩, bCoordExt_sgnAut i0 j⟩
      · obtain ⟨a', rfl⟩ := Fin.exists_succAbove_eq ha
        obtain ⟨b', rfl⟩ := Fin.exists_succAbove_eq hb
        have hab' : a' ≠ b' := fun h => hab (by rw [h])
        refine ⟨SpCoord.permAut (Equiv.swap a' b'), Or.inr ⟨a', b', hab', rfl⟩, ?_⟩
        rw [bCoordExt_permAut i0 a' b']
  have hcard : Nat.card ↥(bCoordinateBlock (m + 1) p i0) = Nat.card ↥(bSignedFull m p) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (bCoordExt_injective p m i0)
  rw [hcard, bSignedFull_eq_signedPermSubgroup,
    SignedPermCount.card_signedPermSubgroup (p := p) (k := m) hp hp2]

private noncomputable def bBlockRes {n p : ℕ} (I : Finset (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) : Fin I.card → Multiplicative (ZMod p) :=
  fun j => f (I.equivFin.symm j)

private lemma bBlockRes_apply {n p : ℕ} (I : Finset (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) (j : Fin I.card) :
    bBlockRes I f j = f (I.equivFin.symm j) :=
  rfl

private lemma bBlockRes_mul {n p : ℕ} (I : Finset (Fin n))
    (f g : Fin n → Multiplicative (ZMod p)) :
    bBlockRes I (f * g) = bBlockRes I f * bBlockRes I g :=
  rfl

private noncomputable def bBlockExtFun {n p : ℕ} (I : Finset (Fin n))
    (u : MulAut (Fin I.card → Multiplicative (ZMod p)))
    (f : Fin n → Multiplicative (ZMod p)) :
    Fin n → Multiplicative (ZMod p) :=
  fun i => if h : i ∈ I then u (bBlockRes I f) (I.equivFin ⟨i, h⟩) else f i

private lemma bBlockExtFun_of_mem {n p : ℕ} {I : Finset (Fin n)}
    {u : MulAut (Fin I.card → Multiplicative (ZMod p))} {f : Fin n → Multiplicative (ZMod p)}
    {i : Fin n} (h : i ∈ I) :
    bBlockExtFun I u f i = u (bBlockRes I f) (I.equivFin ⟨i, h⟩) :=
  dif_pos h

private lemma bBlockExtFun_of_not_mem {n p : ℕ} {I : Finset (Fin n)}
    {u : MulAut (Fin I.card → Multiplicative (ZMod p))} {f : Fin n → Multiplicative (ZMod p)}
    {i : Fin n} (h : i ∉ I) :
    bBlockExtFun I u f i = f i :=
  dif_neg h

private lemma bBlockRes_bBlockExtFun {n p : ℕ} (I : Finset (Fin n))
    (u : MulAut (Fin I.card → Multiplicative (ZMod p))) (f : Fin n → Multiplicative (ZMod p)) :
    bBlockRes I (bBlockExtFun I u f) = u (bBlockRes I f) := by
  funext j
  rw [bBlockRes_apply, bBlockExtFun_of_mem (I.equivFin.symm j).2, Subtype.coe_eta,
    Equiv.apply_symm_apply]

private lemma bBlockExtFun_comp {n p : ℕ} (I : Finset (Fin n))
    (u v : MulAut (Fin I.card → Multiplicative (ZMod p)))
    (f : Fin n → Multiplicative (ZMod p)) :
    bBlockExtFun I u (bBlockExtFun I v f) = bBlockExtFun I (u * v) f := by
  funext i
  by_cases h : i ∈ I
  · rw [bBlockExtFun_of_mem h, bBlockExtFun_of_mem h, bBlockRes_bBlockExtFun, MulAut.mul_apply]
  · rw [bBlockExtFun_of_not_mem h, bBlockExtFun_of_not_mem h, bBlockExtFun_of_not_mem h]

private lemma bBlockExtFun_one {n p : ℕ} (I : Finset (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) :
    bBlockExtFun I (1 : MulAut (Fin I.card → Multiplicative (ZMod p))) f = f := by
  funext i
  by_cases h : i ∈ I
  · rw [bBlockExtFun_of_mem h, MulAut.one_apply, bBlockRes_apply, Equiv.symm_apply_apply]
  · exact bBlockExtFun_of_not_mem h

private lemma bBlockExtFun_mul {n p : ℕ} (I : Finset (Fin n))
    (u : MulAut (Fin I.card → Multiplicative (ZMod p)))
    (f g : Fin n → Multiplicative (ZMod p)) :
    bBlockExtFun I u (f * g) = bBlockExtFun I u f * bBlockExtFun I u g := by
  funext i
  rw [Pi.mul_apply]
  by_cases h : i ∈ I
  · rw [bBlockExtFun_of_mem h, bBlockExtFun_of_mem h, bBlockExtFun_of_mem h, bBlockRes_mul,
      map_mul, Pi.mul_apply]
  · rw [bBlockExtFun_of_not_mem h, bBlockExtFun_of_not_mem h, bBlockExtFun_of_not_mem h,
      Pi.mul_apply]

private noncomputable def bBlockExt {n p : ℕ} (I : Finset (Fin n)) :
    MulAut (Fin I.card → Multiplicative (ZMod p)) →*
      MulAut (Fin n → Multiplicative (ZMod p)) where
  toFun u :=
    { toFun := bBlockExtFun I u
      invFun := bBlockExtFun I u⁻¹
      left_inv f := by rw [bBlockExtFun_comp, inv_mul_cancel, bBlockExtFun_one]
      right_inv f := by rw [bBlockExtFun_comp, mul_inv_cancel, bBlockExtFun_one]
      map_mul' f g := bBlockExtFun_mul I u f g }
  map_one' := MulEquiv.ext fun f => bBlockExtFun_one I f
  map_mul' u v := MulEquiv.ext fun f => (bBlockExtFun_comp I u v f).symm

private lemma bBlockExt_apply {n p : ℕ} (I : Finset (Fin n))
    (u : MulAut (Fin I.card → Multiplicative (ZMod p))) (f : Fin n → Multiplicative (ZMod p)) :
    bBlockExt I u f = bBlockExtFun I u f :=
  rfl

private lemma bBlockExt_injective {n p : ℕ} (I : Finset (Fin n)) :
    Function.Injective (bBlockExt (p := p) I) := by
  intro u v h
  ext g j
  let f : Fin n → Multiplicative (ZMod p) := fun i =>
    if hi : i ∈ I then g (I.equivFin ⟨i, hi⟩) else 1
  have hf : bBlockRes I f = g := by
    funext l
    rw [bBlockRes_apply]
    simp only [f, dif_pos (I.equivFin.symm l).2, Subtype.coe_eta, Equiv.apply_symm_apply]
  have h2 : bBlockExtFun I u f = bBlockExtFun I v f := by
    rw [← bBlockExt_apply, ← bBlockExt_apply, h]
  have h3 := congrArg (bBlockRes I) h2
  rw [bBlockRes_bBlockExtFun, bBlockRes_bBlockExtFun, hf] at h3
  exact congrFun h3 j

private lemma bBlockExt_sgnAut {n p : ℕ} (I : Finset (Fin n)) (j : Fin I.card) :
    bBlockExt I (SpCoord.sgnAut (p := p) j) =
      SpCoord.sgnAut (p := p) ((I.equivFin.symm j).val) := by
  ext f i
  rw [bBlockExt_apply, SpCoord.sgnAut_apply]
  by_cases h : i ∈ I
  · rw [bBlockExtFun_of_mem h, SpCoord.sgnAut_apply]
    by_cases hij : I.equivFin ⟨i, h⟩ = j
    · have hi : i = (I.equivFin.symm j).val := congrArg Subtype.val
        ((I.equivFin.symm_apply_apply ⟨i, h⟩).symm.trans (congrArg I.equivFin.symm hij))
      rw [hij, Function.update_self, hi, Function.update_self, bBlockRes_apply]
    · have hi : i ≠ (I.equivFin.symm j).val := fun hi => hij
        ((congrArg I.equivFin (Subtype.ext hi : (⟨i, h⟩ : I) = I.equivFin.symm j)).trans
          (I.equivFin.apply_symm_apply j))
      rw [Function.update_of_ne hij, Function.update_of_ne hi, bBlockRes_apply]
      simp only [Equiv.symm_apply_apply]
  · rw [bBlockExtFun_of_not_mem h, Function.update_of_ne]
    rintro rfl
    exact h (I.equivFin.symm j).2

private lemma bBlockExt_permAut {n p : ℕ} (I : Finset (Fin n)) (a b : Fin I.card) :
    bBlockExt I (SpCoord.permAut (p := p) (Equiv.swap a b)) =
      SpCoord.permAut (p := p)
        (Equiv.swap ((I.equivFin.symm a).val) ((I.equivFin.symm b).val)) := by
  ext f i
  rw [bBlockExt_apply, SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv]
  by_cases h : i ∈ I
  · rw [bBlockExtFun_of_mem h, SpCoord.permAut_apply, Function.comp_apply, Equiv.swap_inv,
      bBlockRes_apply]
    refine congrArg f ?_
    have he : Function.Injective (fun l : Fin I.card => (I.equivFin.symm l).val) :=
      Subtype.val_injective.comp I.equivFin.symm.injective
    calc ((I.equivFin.symm (Equiv.swap a b (I.equivFin ⟨i, h⟩))) : Fin n)
        = Equiv.swap ((I.equivFin.symm a) : Fin n) (I.equivFin.symm b)
            (I.equivFin.symm (I.equivFin ⟨i, h⟩)) := (he.swap_apply a b _).symm
      _ = Equiv.swap ((I.equivFin.symm a) : Fin n) (I.equivFin.symm b) i := by
          simp only [Equiv.symm_apply_apply]
  · rw [bBlockExtFun_of_not_mem h, Equiv.swap_apply_of_ne_of_ne]
    · rintro rfl
      exact h (I.equivFin.symm a).2
    · rintro rfl
      exact h (I.equivFin.symm b).2

theorem card_bBlockOn {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (I : Finset (Fin n)) :
    Nat.card ↥(bBlockOn n p I) = 2 ^ I.card * I.card.factorial := by
  let k := I.card
  have hmap : (bSignedFull k p).map (bBlockExt I) = bBlockOn n p I := by
    rw [bSignedFull, bBlockOn, MonoidHom.map_closure]
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, rfl⟩
      rcases hs with ⟨j, rfl⟩ | ⟨a, b, hab, rfl⟩
      · rw [bBlockExt_sgnAut]
        exact Or.inl ⟨(I.equivFin.symm j).val, (I.equivFin.symm j).2, rfl⟩
      · rw [bBlockExt_permAut]
        exact Or.inr ⟨(I.equivFin.symm a).val, (I.equivFin.symm a).2,
          (I.equivFin.symm b).val, (I.equivFin.symm b).2,
          fun h => hab (I.equivFin.symm.injective (Subtype.ext h)), rfl⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
      · let j : Fin k := I.equivFin ⟨i, hi⟩
        refine ⟨SpCoord.sgnAut j, Or.inl ⟨j, rfl⟩, ?_⟩
        rw [bBlockExt_sgnAut]
        congr 1
        simp [j, Equiv.symm_apply_apply]
      · let a' : Fin k := I.equivFin ⟨a, ha⟩
        let b' : Fin k := I.equivFin ⟨b, hb⟩
        have hab' : a' ≠ b' := by
          intro h
          have hval : a = b := by
            have h' := I.equivFin.injective h
            exact congrArg Subtype.val h'
          exact hab hval
        refine ⟨SpCoord.permAut (Equiv.swap a' b'), Or.inr ⟨a', b', hab', rfl⟩, ?_⟩
        rw [bBlockExt_permAut]
        congr 1
        simp [a', b', Equiv.symm_apply_apply]
  have hcard : Nat.card ↥(bBlockOn n p I) = Nat.card ↥(bSignedFull k p) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (bBlockExt_injective I)
  rw [hcard, bSignedFull_eq_signedPermSubgroup,
    SignedPermCount.card_signedPermSubgroup (p := p) (k := k) hp hp2]

theorem card_ggAutomizer_of_bCoordinateBlock {G : Type} [Group G] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs L : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (i0 : Fin n)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    Nat.card ↥(ggAutomizer L Bs) = 2 ^ (n - 1) * (n - 1).factorial := by
  rw [← card_bCoordinateBlock hp hp2 i0, ← hAut]
  exact (Subgroup.card_map_of_injective (MulAut.congr eta).injective).symm

theorem card_ggAutomizer_of_bBlockOn {G : Type} [Group G] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs K : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (I : Finset (Fin n))
    (hAut : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bBlockOn n p I) :
    Nat.card ↥(ggAutomizer K Bs) = 2 ^ I.card * I.card.factorial := by
  rw [← card_bBlockOn hp hp2 I, ← hAut]
  exact (Subgroup.card_map_of_injective (MulAut.congr eta).injective).symm

theorem GGConfig.exists_row_card_automizer_L (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop}
    (hL : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ P r m N C M) p Bs L) :
    ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      P r m N C M ∧ Nat.card ↥(ggAutomizer L Bs) = Nat.card M.Group := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨_lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hP, hBsI, hlift, hW, -⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2 P hL
  have hTor := hW ↥L (ggQuotHom θ) (ggGamma L hN).range
    (ggTorusTBGroup_of_L hcfg hperf θ hN hBsI hlift)
  obtain ⟨hom, hpm, -, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨r, m, N, C, M, hP, ggTD_card_automizer hp2 hom hpm hBs hS hN hTor⟩

theorem GGConfig.exists_row_card_automizer_nbr (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop}
    (hK : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧ P r m N C M) p Bs K) :
    ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
      P r m N C M ∧ Nat.card ↥(ggAutomizer K Bs) = Nat.card M.Group := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨_lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hP, hBsI, hlift, hW, -⟩ :=
    l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2 P hK
  have hTor := hW ↥K (ggQuotHom θ) (ggGamma K hN).range
    (ggTorusTBGroup_of_nbr hcfg hnb hperf θ hN hBsI hlift)
  obtain ⟨hom, hpm, -, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨r, m, N, C, M, hP, ggTD_card_automizer hp2 hom hpm hBs hS hN hTor⟩

theorem two_pow_mul_factorial_strictMono :
    StrictMono fun a : ℕ => 2 ^ a * a.factorial := by
  intro a b hab
  have h1 : a.factorial ≤ b.factorial := Nat.factorial_le (le_of_lt hab)
  have h2 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  calc 2 ^ a * a.factorial < 2 ^ b * a.factorial :=
        Nat.mul_lt_mul_of_pos_right h2 (Nat.factorial_pos a)
    _ ≤ 2 ^ b * b.factorial := Nat.mul_le_mul le_rfl h1

theorem eq_of_two_pow_mul_factorial_eq {a b : ℕ}
    (h : 2 ^ a * a.factorial = 2 ^ b * b.factorial) : a = b :=
  two_pow_mul_factorial_strictMono.injective h

theorem two_pow_pred_mul_factorial_ne {a k : ℕ} (ha : 2 ≤ a)
    (h : 2 ^ (a - 1) * a.factorial = 2 ^ k * k.factorial) : False := by
  have h₁ : 2 ^ (a - 1) * (a - 1).factorial < 2 ^ (a - 1) * a.factorial :=
    Nat.mul_lt_mul_of_pos_left
      (Nat.factorial_lt_of_lt (by omega) (by omega : a - 1 < a)) (Nat.two_pow_pos (a - 1))
  have h₂ : 2 ^ (a - 1) * a.factorial < 2 ^ a * a.factorial :=
    Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by norm_num) (by omega))
      (Nat.factorial_pos a)
  rw [h] at h₁ h₂
  have h₃ := two_pow_mul_factorial_strictMono.lt_iff_lt.mp h₁
  have h₄ := two_pow_mul_factorial_strictMono.lt_iff_lt.mp h₂
  omega

theorem two_pow_mul_factorial_ne_of_between {a c k : ℕ}
    (h₁ : 2 ^ a * a.factorial < c) (h₂ : c < 2 ^ (a + 1) * (a + 1).factorial)
    (h : 2 ^ k * k.factorial = c) : False := by
  have h₁' : 2 ^ a * a.factorial < 2 ^ k * k.factorial := by rw [h]; exact h₁
  have h₂' : 2 ^ k * k.factorial < 2 ^ (a + 1) * (a + 1).factorial := by rw [h]; exact h₂
  have h₃ := two_pow_mul_factorial_strictMono.lt_iff_lt.mp h₁'
  have h₄ := two_pow_mul_factorial_strictMono.lt_iff_lt.mp h₂'
  omega

theorem ggTBTorRowAt_coordB_of_card
    {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hrow : GGTBTorRowAt p lab r m N C M) {k : ℕ} (hk : 3 ≤ k)
    (hcard : Nat.card M.Group = 2 ^ k * k.factorial) :
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = k) ∨
      (((lab.tag = .D ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank) ∨
        (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank)))) ∧
          lab.rank = k + 1) ∨
      (lab.rank = 5 ∧ ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)) ∧
        k = 3) := by
  have hk2 : 2 ≤ k := by omega
  cases hrow with
  | aDep _ _ _ _ _ =>
      exfalso
      rw [l05nK3a_card_coxeterA] at hcard
      exact factorial_succ_ne_two_pow_mul_factorial hk2 hcard
  | e6Three _ _ _ =>
      exfalso
      rw [card_coxeterE6_group] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 6) (c := 51840)
        (by norm_num) (by norm_num) hcard.symm
  | e8Three _ _ =>
      exfalso
      rw [card_coxeterE8_group] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 9) (c := 696729600)
        (by norm_num) (by norm_num) hcard.symm
  | aInd _ _ _ =>
      exfalso
      rw [l05nK3a_card_coxeterA] at hcard
      exact factorial_succ_ne_two_pow_mul_factorial hk2 hcard
  | c htag _ =>
      have h2 : 2 ≤ lab.rank := by
        rcases htag with htag | htag <;>
          · have h := hlab.2
            rw [htag] at h
            exact h.1
      refine Or.inl ⟨htag, ?_⟩
      rw [ggCoxeterB_card lab.rank h2] at hcard
      exact eq_of_two_pow_mul_factorial_eq hcard
  | d hdisj =>
      exfalso
      have h3 : 3 ≤ lab.rank := by
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -, hodd⟩
        · have h := hlab.2
          rw [hD] at h
          exact h
        · have h := hlab.2
          rw [htwD] at h
          obtain ⟨j, hj⟩ := hodd
          omega
      rcases (show lab.rank = 3 ∨ 4 ≤ lab.rank by omega) with hrank | h4
      · have hle : Nat.card (ggCoxeterMatrixD lab.rank).Group ≤ 24 := by
          rw [hrank]
          have h := SpJoinRefl.card_coxeterD_le 3 (by norm_num)
          norm_num [Nat.factorial] at h ⊢
          exact h
        rw [hcard] at hle
        have hmono : 2 ^ 3 * (3).factorial ≤ 2 ^ k * k.factorial :=
          two_pow_mul_factorial_strictMono.monotone hk
        norm_num [Nat.factorial] at hmono
        omega
      · have hD := OrthF3.card_coxeterD_eq lab.rank h4
        rw [hD] at hcard
        exact two_pow_pred_mul_factorial_ne (by omega) hcard
  | e6Ind _ _ _ =>
      exfalso
      rw [card_coxeterE6_group] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 6) (c := 51840)
        (by norm_num) (by norm_num) hcard.symm
  | e7 _ _ =>
      exfalso
      rw [card_coxeterE7_group] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 7) (c := 2903040)
        (by norm_num) (by norm_num) hcard.symm
  | e8Ind _ _ _ =>
      exfalso
      rw [card_coxeterE8_group] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 9) (c := 696729600)
        (by norm_num) (by norm_num) hcard.symm
  | f4 _ _ _ =>
      exfalso
      rw [l04fFRC_ord_card_coxeterF4] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 4) (c := 1152)
        (by norm_num) (by norm_num) hcard.symm
  | g2 _ =>
      exfalso
      rw [l04fFRC_card_coxeterG2] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 2) (c := 12)
        (by norm_num) (by norm_num) hcard.symm
  | relD hdisj =>
      refine Or.inr (Or.inl ⟨hdisj, ?_⟩)
      have h1 : 1 ≤ lab.rank - 1 := by
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -⟩
        · have h := hlab.2
          rw [hD] at h
          omega
        · have h := hlab.2
          rw [htwD] at h
          omega
      rcases (show lab.rank - 1 = 1 ∨ 2 ≤ lab.rank - 1 by omega) with hone | h2
      · exfalso
        rw [hone] at hcard
        have hle : Nat.card (CoxeterMatrix.B 1).Group ≤ 2 := by
          have h := card_coxeterB_le 1
          norm_num [Nat.factorial] at h
          exact h
        rw [hcard] at hle
        have hmono : 2 ^ 3 * (3).factorial ≤ 2 ^ k * k.factorial :=
          two_pow_mul_factorial_strictMono.monotone hk
        norm_num [Nat.factorial] at hmono
        omega
      · have hB := ggCoxeterB_card (lab.rank - 1) h2
        rw [hB] at hcard
        have heq := eq_of_two_pow_mul_factorial_eq hcard
        omega
  | relE6 _ _ =>
      exfalso
      rw [l04fFRC_ord_card_coxeterF4] at hcard
      exact two_pow_mul_factorial_ne_of_between (a := 4) (c := 1152)
        (by norm_num) (by norm_num) hcard.symm
  | relA5 h5 hd =>
      refine Or.inr (Or.inr ⟨h5, hd, ?_⟩)
      rw [ggCoxeterB_card 3 (by norm_num)] at hcard
      have heq := eq_of_two_pow_mul_factorial_eq hcard
      omega

private theorem largeEvenSplit_dvd_sub_of_untwisted {p : ℕ} {lab : LargeEvenLabel}
    (hS : LargeEvenSplit p lab) (hu : LargeEvenUntwisted lab.tag) :
    p ∣ 2 ^ lab.n - 1 ∨ (lab.n = 1 ∧ p = 3) := by
  obtain ⟨t, ℓ, e⟩ := lab
  rcases hS with ⟨-, h⟩ | ⟨hu', -⟩ | ⟨ht, -⟩ | h
  · exact Or.inl h
  · exact absurd hu hu'
  · rcases ht with ht | ht
    · subst ht
      exact absurd hu (by simp [LargeEvenUntwisted])
    · subst ht
      exact absurd hu (by simp [LargeEvenUntwisted])
  · exact Or.inr h

private theorem largeEvenSplit_dvd_add_of_not_untwisted {p : ℕ} {lab : LargeEvenLabel}
    (hS : LargeEvenSplit p lab) (hu : ¬ LargeEvenUntwisted lab.tag)
    (htwD : lab.tag ≠ .twD) (htri : lab.tag ≠ .triD4) :
    p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, ℓ, e⟩ := lab
  rcases hS with ⟨hu', -⟩ | ⟨-, -, h⟩ | ⟨ht, -⟩ | h
  · exact absurd hu' hu
  · exact h
  · rcases ht with ht | ht
    · exact absurd ht htwD
    · exact absurd ht htri
  · obtain ⟨rfl, rfl⟩ := h
    norm_num

private theorem largeEvenSplit_twD_sub_or_add {p : ℕ} {lab : LargeEvenLabel}
    (hS : LargeEvenSplit p lab) (ht : lab.tag = .twD) :
    p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  obtain ⟨t, ℓ, e⟩ := lab
  subst ht
  rcases hS with ⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | h
  · exact absurd hu (by simp [LargeEvenUntwisted])
  · exact Or.inr h
  · exact Or.inl h
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inr (by norm_num)

theorem ggSecFiveBCoordBLabel_of_coordB {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hS : LargeEvenSplit p lab) {n : ℕ} (hn : 4 ≤ n)
    (h : ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = n - 1) ∨
      (((lab.tag = .D ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank) ∨
        (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank)))) ∧
          lab.rank = n - 1 + 1) ∨
      (lab.rank = 5 ∧ ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)) ∧
        n - 1 = 3)) :
    GGSecFiveBCoordBLabel n p lab := by
  obtain ⟨t, ℓ, e⟩ := lab
  rcases h with ⟨hBC, hr⟩ | ⟨hDt, hr⟩ | ⟨hr5, hA, hn3⟩
  · rcases hBC with ht | ht
    · have hu : LargeEvenUntwisted t := by
        have ht' : t = .B := ht
        subst ht'
        simp [LargeEvenUntwisted]
      rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
      · exact Or.inl ⟨Or.inl ht, hr, Or.inl hd⟩
      · exact Or.inl ⟨Or.inl ht, hr, Or.inr h3⟩
    · have hu : LargeEvenUntwisted t := by
        have ht' : t = .C := ht
        subst ht'
        simp [LargeEvenUntwisted]
      rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
      · exact Or.inl ⟨Or.inr ht, hr, Or.inl hd⟩
      · exact Or.inl ⟨Or.inr ht, hr, Or.inr h3⟩
  · rcases hDt with ⟨ht, hplus, hodd⟩ | ⟨ht, hdvd⟩
    · have hu : LargeEvenUntwisted t := by
        have ht' : t = .D := ht
        subst ht'
        simp [LargeEvenUntwisted]
      rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hsub | h3
      · exact (not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hsub hplus).elim
      · obtain ⟨rfl, rfl⟩ := h3
        change ℓ = n - 1 + 1 at hr
        have hrn : ℓ = n := by omega
        refine Or.inr (Or.inr (Or.inl ⟨ht, hrn, ?_, rfl, rfl⟩))
        rw [← hrn]
        exact hodd
    · change ℓ = n - 1 + 1 at hr
      have hrn : ℓ = n := by omega
      rcases hdvd with hsub | ⟨hplus, heven⟩
      · exact Or.inr (Or.inl ⟨ht, hrn, Or.inl hsub⟩)
      · refine Or.inr (Or.inl ⟨ht, hrn, Or.inr ⟨?_, hplus⟩⟩)
        rw [← hrn]
        exact heven
  · have hn4 : n = 4 := by omega
    subst hn4
    rcases hA with ⟨ht, hplus⟩ | ⟨ht, hsub⟩
    · have hu : LargeEvenUntwisted t := by
        have ht' : t = .A := ht
        subst ht'
        simp [LargeEvenUntwisted]
      rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hsub' | h3
      · exact (not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hsub' hplus).elim
      · obtain ⟨rfl, rfl⟩ := h3
        exact Or.inr (Or.inr (Or.inr ⟨ht, Or.inl (by omega), rfl, rfl⟩))
    · exact (not_split_twA_dvd_sub hp hp2 ht hS hsub).elim

theorem ggSecFiveBCoordBLabel_nbr_of_coordB_four
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {n : ℕ} (hn : 4 ≤ n) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    {labK : LargeEvenLabel} (hLambda : LargeEvenInLambda2 labK) (hcov : GGTBTorCov p labK)
    (hKmark : GGInnerDiagOnLabel (fun _ lab => lab = labK) p Bs K)
    (hAut : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ((labK.tag = .B ∨ labK.tag = .C) ∧ labK.rank = n - 1) ∨
      (((labK.tag = .D ∧ p ∣ 2 ^ labK.n + 1 ∧ Odd labK.rank) ∨
        (labK.tag = .twD ∧ (p ∣ 2 ^ labK.n - 1 ∨ (p ∣ 2 ^ labK.n + 1 ∧ Even labK.rank)))) ∧
          labK.rank = n) ∨
      (n = 4 ∧ labK.rank = 5 ∧
        ((labK.tag = .A ∧ p ∣ 2 ^ labK.n + 1) ∨ (labK.tag = .twA ∧ p ∣ 2 ^ labK.n - 1))) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hcardK : Nat.card ↥(ggAutomizer K Bs) = 2 ^ (n - 1) * (n - 1).factorial :=
    card_ggAutomizer_of_bCoordinateBlock hp hp2 eta i0 hAut
  have hK : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        GGTBTorRowAt p labK r m N C M) p Bs K := by
    unfold GGInnerDiagOnLabel at hKmark ⊢
    refine largeEvenMarking_mono ?_ hKmark
    rintro lab' R _ I F θ ⟨hlab, hQ⟩
    obtain ⟨r, m, N, C, M, hrow⟩ := hcov
    rw [hlab]
    exact ⟨⟨r, m, N, C, M, hrow, hrow⟩, hQ⟩
  obtain ⟨r, m, N, C, M, hrow, hcardM⟩ :=
    GGConfig.exists_row_card_automizer_nbr hT hLift hcfg hnb
      (P := fun r m N C M => GGTBTorRowAt p labK r m N C M) hK
  have hk : 3 ≤ n - 1 := by omega
  have hcard : Nat.card M.Group = 2 ^ (n - 1) * (n - 1).factorial := hcardM ▸ hcardK
  have hmatch := ggTBTorRowAt_coordB_of_card hLambda hrow hk hcard
  rcases hmatch with hBC | hD | hA5
  · exact Or.inl hBC
  · refine Or.inr (Or.inl ⟨hD.1, ?_⟩)
    omega
  · exact Or.inr (Or.inr ⟨by omega, hA5.1, hA5.2.1⟩)

theorem ggSplit_not_tbTorCov_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hS : LargeEvenSplit p lab) (hnc : ¬ GGTBTorCov p lab) :
    GGSecFiveBCoordBResLabel p lab ∨ ggRowP_Small p lab ∨
      (((lab.tag = .A ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧
        p ∣ 2 ^ lab.n + 1) := by
  obtain ⟨t, ℓ, e⟩ := lab
  have htor : ∀ {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)},
      GGTBTorRowAt p ⟨t, ℓ, e⟩ r m N C M → False :=
    fun hrow => hnc ⟨_, _, _, _, _, hrow⟩
  cases t <;> dsimp only [LargeEvenInLambda2] at hlab
  ·
    have hu : LargeEvenUntwisted .A := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · by_cases hsmall : ℓ ≤ 2
      · exact Or.inr (Or.inl (by simp [ggRowP_Small, hsmall]))
      · have h3le : 3 ≤ ℓ := by omega
        by_cases hdiv : p ∣ ℓ + 1
        · by_cases h4 : 4 ≤ ℓ
          · have hnot : ¬ p ∣ 2 ^ e + 1 :=
              not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hd
            have hbad : ¬ (p = 3 ∧ ℓ = 5 ∧ p ∣ 2 ^ e + 1) := by
              rintro ⟨-, -, h⟩
              exact hnot h
            exact (htor (GGTBTorRowAt.aDep (Or.inl rfl) h4 hdiv
              (by simpa [ggTorM] using hd) hbad)).elim
          · have hle2 : ℓ ≤ 2 := by
              by_contra h2
              have hℓ3 : ℓ = 3 := by omega
              subst hℓ3
              have h4dvd : p ∣ 4 := by simpa using hdiv
              have h2dvd : p ∣ 2 := by
                have h22 : p ∣ 2 * 2 := by simpa using h4dvd
                rcases hp.dvd_mul.mp h22 with h | h
                · exact h
                · exact h
              exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)
            exact absurd hle2 hsmall
        · exact (htor (GGTBTorRowAt.aInd (Or.inl rfl) hdiv
            (by simpa [ggTorM] using hd))).elim
    · obtain ⟨rfl, rfl⟩ := h3
      have hℓ2 : 2 ≤ ℓ := by
        have h1 : 1 ≤ ℓ := hlab.2.1
        have hne : ℓ ≠ 1 := by
          rintro rfl
          have h21 : 2 ≤ (1 : ℕ) := hlab.2.2 rfl
          omega
        omega
      rcases lt_or_ge ℓ 3 with hlt3 | hge3
      · have hℓeq : ℓ = 2 := by omega
        subst hℓeq
        exact Or.inr (Or.inl (by simp [ggRowP_Small]))
      rcases lt_or_ge ℓ 5 with hlt5 | hge5
      · have hℓ34 : ℓ = 3 ∨ ℓ = 4 := by omega
        exact Or.inr (Or.inr ⟨Or.inl ⟨rfl, hℓ34⟩, by norm_num⟩)
      rcases lt_or_ge ℓ 6 with hlt6 | hge6
      · have hℓ5 : ℓ = 5 := by omega
        subst hℓ5
        exact (htor (GGTBTorRowAt.relA5 rfl (Or.inl ⟨rfl, by norm_num⟩))).elim
      · exact Or.inl ⟨rfl, Or.inl ⟨rfl, hge6, rfl⟩⟩
  ·
    have hu : ¬ LargeEvenUntwisted .twA := by simp [LargeEvenUntwisted]
    have hq1 := largeEvenSplit_dvd_add_of_not_untwisted hS hu (by simp) (by simp)
    by_cases hdiv : p ∣ ℓ + 1
    · by_cases h4 : 4 ≤ ℓ
      · by_cases hbad : p = 3 ∧ ℓ = 5
        · obtain ⟨rfl, rfl⟩ := hbad
          exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hq1⟩)))⟩
        · have hbad' : ¬ (p = 3 ∧ ℓ = 5 ∧ p ∣ 2 ^ e + 1) := by
            rintro ⟨h1, h2, -⟩
            exact hbad ⟨h1, h2⟩
          exact (htor (GGTBTorRowAt.aDep (Or.inr rfl) h4 hdiv
            (by simpa [ggTorM] using hq1) hbad')).elim
      · have hle3 : ℓ ≤ 3 := by omega
        have hℓ2 : 2 ≤ ℓ := hlab.2.1
        rcases (by omega : ℓ = 2 ∨ ℓ = 3) with h2 | h3
        · subst h2
          exact Or.inr (Or.inl (by simp [ggRowP_Small]))
        · subst h3
          have h2dvd : p ∣ 2 := by
            have h4dvd : p ∣ 4 := by simpa using hdiv
            have h22 : p ∣ 2 * 2 := by simpa using h4dvd
            rcases hp.dvd_mul.mp h22 with h | h
            · exact h
            · exact h
          exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd) hp2
    · exact (htor (GGTBTorRowAt.aInd (Or.inr rfl) hdiv
        (by simpa [ggTorM] using hq1))).elim
  ·
    have hu : LargeEvenUntwisted .B := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · exact (htor (GGTBTorRowAt.c (Or.inl rfl) (dvd_mul_of_dvd_left hd _))).elim
    · obtain ⟨rfl, rfl⟩ := h3
      exact (htor (GGTBTorRowAt.c (Or.inl rfl) (by norm_num))).elim
  ·
    have hu : LargeEvenUntwisted .C := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · exact (htor (GGTBTorRowAt.c (Or.inr rfl) (dvd_mul_of_dvd_left hd _))).elim
    · obtain ⟨rfl, rfl⟩ := h3
      exact (htor (GGTBTorRowAt.c (Or.inr rfl) (by norm_num))).elim
  ·
    have hu : LargeEvenUntwisted .D := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · exact (htor (GGTBTorRowAt.d (Or.inl ⟨rfl, Or.inl hd⟩))).elim
    · obtain ⟨rfl, rfl⟩ := h3
      by_cases hEven : Even ℓ
      · exact (htor (GGTBTorRowAt.d
          (Or.inl ⟨rfl, Or.inr ⟨by norm_num, hEven⟩⟩))).elim
      · have hOdd : Odd ℓ := Nat.not_even_iff_odd.mp hEven
        exact (htor (GGTBTorRowAt.relD (Or.inl ⟨rfl, by norm_num, hOdd⟩))).elim
  ·
    rcases largeEvenSplit_twD_sub_or_add hS rfl with hd | ha
    · exact (htor (GGTBTorRowAt.relD (Or.inr ⟨rfl, Or.inl hd⟩))).elim
    · by_cases hOdd : Odd ℓ
      · exact (htor (GGTBTorRowAt.d (Or.inr ⟨rfl, ha, hOdd⟩))).elim
      · have hEven : Even ℓ := Nat.not_odd_iff_even.mp hOdd
        exact (htor (GGTBTorRowAt.relD
          (Or.inr ⟨rfl, Or.inr ⟨ha, hEven⟩⟩))).elim
  ·
    have hu : LargeEvenUntwisted .E6 := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · by_cases hp3 : p = 3
      · subst hp3
        exact (htor (GGTBTorRowAt.e6Three rfl rfl
          (by simpa [ggTorM] using hd))).elim
      · exact (htor (GGTBTorRowAt.e6Ind hp3 (Or.inl rfl)
          (by simpa [ggTorM] using hd))).elim
    · obtain ⟨rfl, rfl⟩ := h3
      exact Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  ·
    have hu : LargeEvenUntwisted .E7 := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · exact (htor (GGTBTorRowAt.e7 rfl (dvd_mul_of_dvd_left hd _))).elim
    · obtain ⟨rfl, rfl⟩ := h3
      exact (htor (GGTBTorRowAt.e7 rfl (by norm_num))).elim
  ·
    have hu : LargeEvenUntwisted .E8 := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · by_cases hp3 : p = 3
      · subst hp3
        exact (htor (GGTBTorRowAt.e8Three rfl rfl)).elim
      · exact (htor (GGTBTorRowAt.e8Ind hp3 rfl
          (dvd_mul_of_dvd_left hd _))).elim
    · obtain ⟨rfl, rfl⟩ := h3
      exact (htor (GGTBTorRowAt.e8Three rfl rfl)).elim
  ·
    have hu : LargeEvenUntwisted .F4 := by simp [LargeEvenUntwisted]
    rcases largeEvenSplit_dvd_sub_of_untwisted hS hu with hd | h3
    · have hnot : ¬ (p = 3 ∧ p ∣ 2 ^ e + 1) := by
        rintro ⟨-, hdiv⟩
        exact not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hd hdiv
      exact (htor (GGTBTorRowAt.f4 rfl (dvd_mul_of_dvd_left hd _) hnot)).elim
    · obtain ⟨rfl, rfl⟩ := h3
      exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  ·
    have hu : ¬ LargeEvenUntwisted .twE6 := by simp [LargeEvenUntwisted]
    have hq1 := largeEvenSplit_dvd_add_of_not_untwisted hS hu (by simp) (by simp)
    by_cases hp3 : p = 3
    · subst hp3
      exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hq1⟩)))⟩
    · exact (htor (GGTBTorRowAt.e6Ind hp3 (Or.inr rfl)
        (by simpa [ggTorM] using hq1))).elim
  all_goals exact Or.inr (Or.inl (by simp [ggRowP_Small]))

theorem ggTBTorCov_of_untwisted_dvd_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hu : LargeEvenUntwisted lab.tag)
    (hn : 2 ≤ lab.n) (hpq : p ∣ 2 ^ lab.n - 1) (hsmall : ¬ ggRowP_Small p lab) :
    GGTBTorCov p lab := by
  by_contra hnc
  rcases ggSplit_not_tbTorCov_cases hp hp2 hlab (Or.inl ⟨hu, hpq⟩) hnc with hres | hsm | hsp
  · obtain ⟨-, hA | hE6 | hF4 | htwE6 | htwA⟩ := hres
    · obtain ⟨-, -, hn1⟩ := hA
      omega
    · obtain ⟨-, hn1⟩ := hE6
      omega
    · obtain ⟨-, hn1⟩ := hF4
      omega
    · obtain ⟨ht, -⟩ := htwE6
      rw [ht] at hu
      exact absurd hu (by simp [LargeEvenUntwisted])
    · obtain ⟨ht, -, -⟩ := htwA
      rw [ht] at hu
      exact absurd hu (by simp [LargeEvenUntwisted])
  · exact hsmall hsm
  · exact not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq hsp.2

private theorem largeEvenSplit_of_halfSplit_of_tag {p : ℕ} {lab : LargeEvenLabel} {c : Prop}
    (hs : LargeEvenHalfSplit p lab c) (ht : lab.tag = .triD4 ∨ lab.tag = .twF4) :
    LargeEvenSplit p lab := by
  rcases hs with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -, -, -⟩ | ⟨h, -, -, -⟩ | ⟨h, -, -⟩
  · exact h
  · rcases ht with ht | ht <;>
      (rcases h with h | h | h | h | h <;> rw [h] at ht <;> exact absurd ht (by decide))
  · rcases ht with ht | ht <;>
      (rcases h with ⟨h, -⟩ | h <;> rw [h] at ht <;> exact absurd ht (by decide))
  · rcases ht with ht | ht <;> rw [h] at ht <;> exact absurd ht (by decide)
  · rcases ht with ht | ht <;> rw [h] at ht <;> exact absurd ht (by decide)
  · rcases ht with ht | ht <;> rw [h] at ht <;> exact absurd ht (by decide)

theorem ggX_absurd_of_small_halfSplit
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G}
    (hX : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X) {c : Prop}
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_Small p lab ∧ LargeEvenHalfSplit p lab c)
      p Bs X) :
    False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  obtain ⟨hXc, lab, hlab, hraw⟩ := ggX_inndiag_pRank_ge_three hcfg hX h
  obtain ⟨-, -, -, -, -, -, -, hS, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hSrow, hSsplit⟩ := hS
  have key : ∀ T : LargeEvenLabel → Prop, T lab → LargeEvenMarking ↥X
      (fun lab R _ I _ _ => T lab ∧ ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧
        IsElemAbelian p E ∧ p ^ 3 ≤ Nat.card E) := fun T hT =>
    ⟨hXc, lab, hlab, largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _, hE⟩ =>
      ⟨hs, hna, θ, hT, hE⟩) hraw⟩
  obtain ⟨t, r, n⟩ := lab
  dsimp only [ggRowP_Small] at hSrow
  rcases hSrow with
    ⟨rfl, hr⟩ | hBC | rfl | rfl | rfl | ⟨rfl, hr⟩ | ⟨rfl, hr⟩ | rfl | rfl | rfl | rfl
  · have h1 : 1 ≤ r := hlab.2.1
    rcases (by omega : r = 1 ∨ r = 2) with hr | hr
    · exact (ggInndiag_pRank_le_two_A1 hp hp2 (key _ ⟨rfl, hr⟩)).elim
    · exact (ggInndiag_pRank_le_two_A2 hp hp2 (key _ ⟨rfl, hr⟩)).elim
  · exact (ggInndiag_pRank_le_two_B2 hp hp2 (key _ hBC)).elim
  · exact (ggInndiag_pRank_le_two_B2der hp hp2 (key _ rfl)).elim
  · exact (ggInndiag_pRank_le_two_G2 hp hp2 (key _ rfl)).elim
  · exact (ggInndiag_pRank_le_two_G2der hp hp2 (key _ rfl)).elim
  · have h2 : 2 ≤ r := hlab.2.1
    exact (ggInndiag_pRank_le_two_twA2 hp hp2 (key _ ⟨rfl, (by omega : r = 2)⟩)).elim
  · exact (ggInndiag_pRank_le_two_twD2 hp hp2 (key _ ⟨rfl, hr⟩)).elim
  · exact (ggInndiag_pRank_le_two_triD4 hp
      (key _ ⟨rfl, dvd_sub_or_add_of_split_triD4
        (largeEvenSplit_of_halfSplit_of_tag hSsplit (Or.inl rfl)) rfl⟩)).elim
  · exact (ggInndiag_pRank_le_two_twB2 hp hp2 (key _ rfl)).elim
  · exact (ggInndiag_pRank_le_two_twF4 hp hp2
      (key _ ⟨rfl, dvd_sub_or_add_of_split_twF4
        (largeEvenSplit_of_halfSplit_of_tag hSsplit (Or.inr rfl)) rfl⟩)).elim
  · exact (ggInndiag_pRank_le_two_twF4der hp hp2 (key _ rfl)).elim

theorem ggL_absurd_of_small_split
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (h : GGInnerDiagOnLabel (fun p lab => ggRowP_Small p lab ∧ LargeEvenSplit p lab) p Bs L) :
    False := by
  exact ggX_absurd_of_small_halfSplit hcfg (Or.inl rfl) (c := True)
    (largeEvenMarking_mono
      (fun lab R _ I _ θ hP => ⟨⟨hP.1.1, Or.inl hP.1.2⟩, hP.2⟩) h)

theorem ggSecFiveBCoordBLabel_core
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    GGInnerDiagOnLabel
      (fun p lab => GGSecFiveBCoordBLabel n p lab ∨ GGSecFiveBCoordBResLabel p lab) p Bs L := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  have hcardL : Nat.card ↥(ggAutomizer L Bs) = 2 ^ (n - 1) * (n - 1).factorial :=
    card_ggAutomizer_of_bCoordinateBlock hp hp2 eta i0 hAut
  have hST : LargeEvenStandardType p B x L := hR.1.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hST.1
  have hmark := ggInnerDiagOn_relabel ggLabelRigidInput_holds hR.1.2.2.1.1 hlab hhas
  have hS : LargeEvenSplit p lab := hP.1
  have hfin : ∀ {T : ℕ → LargeEvenLabel → Prop}, T p lab → GGInnerDiagOnLabel T p Bs L := by
    intro T hTl
    unfold GGInnerDiagOnLabel
    refine largeEvenMarking_mono ?_ hmark
    rintro lab' R _ I F θ ⟨rfl, hQ⟩
    exact ⟨hTl, hQ⟩
  by_cases hcov : GGTBTorCov p lab
  · obtain ⟨r, m, N, C, M, hrow⟩ := hcov
    have hL : GGInnerDiagOnLabel (fun p lab' => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
        (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab' r m N C M ∧
          GGTBTorRowAt p lab r m N C M) p Bs L :=
      hfin ⟨r, m, N, C, M, hrow, hrow⟩
    obtain ⟨r', m', N', C', M', hrow', hcardM⟩ :=
      GGConfig.exists_row_card_automizer_L hT hLift hR.1.1 hL
    have hk : 3 ≤ n - 1 := by omega
    have hmatch := ggTBTorRowAt_coordB_of_card hlab hrow' hk (hcardM ▸ hcardL)
    exact hfin (Or.inl (ggSecFiveBCoordBLabel_of_coordB hp hp2 hS hn hmatch))
  · rcases ggSplit_not_tbTorCov_cases hp hp2 hlab hS hcov with hres | hsm | hsp
    · exact hfin (Or.inr hres)
    · exact (ggL_absurd_of_small_split hR (hfin ⟨hsm, hS⟩)).elim
    · exact (ggX_row_absurd_of_pRank ggRowPRankLeTwo_smallPlus hR (Or.inl rfl) (hfin hsp)).elim

theorem ggSecFiveBCoordBLabelInput_of_res
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hRes : GGSecFiveBCoordBResInput) :
    GGSecFiveBCoordBLabelInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR n hn eta i0 hAut
  exact (ggSecFiveBCoordBLabel_core hT hLift hR hn eta i0 hAut).elim_or.elim id
    (hRes G p B Bs x L D J 𝒦 hR n hn eta i0 hAut)

end CFSG.StandardType

end
