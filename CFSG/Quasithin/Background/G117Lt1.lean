module

public import CFSG.Quasithin.Background.E11Stmt
public import CFSG.Quasithin.Background.G10Clifford
public import CFSG.Quasithin.Background.G93ApplyRestrict
public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

abbrev IrrSet (Γ L : Subgroup (GLV V)) : Type :=
  {J : Submodule (ZMod 2) V // IrrPlus (normalClosure Γ L) J}

instance finite_irrSet (Γ L : Subgroup (GLV V)) : Finite (IrrSet Γ L) :=
  Finite.of_injective (fun J : IrrSet Γ L => (J.1 : Set V)) fun _ _ h =>
    Subtype.ext (SetLike.coe_injective h)

section Action

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
  (h108 : G108Hyp B Γ v₁ W X X₀ L)

include h108

theorem irrPlus_conjSub {γ : GLV V} (hγ : γ ∈ Γ) {J : Submodule (ZMod 2) V}
    (hJ : IrrPlus (normalClosure Γ L) J) : IrrPlus (normalClosure Γ L) (conjSub γ J) :=
  ((hJ.isIrr h108.fixedSpace_H).conj_of_normal (normalClosure_normal Γ L) hγ).irrPlus
    h108.fixedSpace_H

omit h108 in
@[expose] noncomputable def irrAct (h108 : G108Hyp B Γ v₁ W X X₀ L) :
    ↥Γ →* Equiv.Perm (IrrSet Γ L) where
  toFun γ :=
    { toFun := fun J => ⟨conjSub (γ : GLV V) J.1, irrPlus_conjSub h108 γ.2 J.2⟩
      invFun := fun J => ⟨conjSub (γ : GLV V)⁻¹ J.1, irrPlus_conjSub h108 (Γ.inv_mem γ.2) J.2⟩
      left_inv := fun _ => Subtype.ext (conjSub_inv_conjSub _ _)
      right_inv := fun _ => Subtype.ext (conjSub_conjSub_inv _ _) }
  map_one' := Equiv.ext fun _ => Subtype.ext (conjSub_one _)
  map_mul' _ _ := Equiv.ext fun _ => Subtype.ext (conjSub_mul _ _ _)

omit h108 in
theorem irrAct_apply_val (h108 : G108Hyp B Γ v₁ W X X₀ L) (γ : ↥Γ) (J : IrrSet Γ L) :
    ((irrAct h108 γ J : IrrSet Γ L) : Submodule (ZMod 2) V) = conjSub (γ : GLV V) J.1 := rfl

@[expose] def irrOrbit (J : IrrSet Γ L) : Set (IrrSet Γ L) :=
  Set.range fun γ : ↥Γ => irrAct h108 γ J

theorem exists_conjSub_ne {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J)
    (hne : J ≠ ⊤) : ∃ γ ∈ Γ, conjSub γ J ≠ J := by
  by_contra h
  push Not at h
  have hinv : Invariant Γ J := fun γ hγ u hu => by
    rw [← h γ hγ]
    exact apply_mem_conjSub hu
  rcases h108.irreducible.eq_bot_or_eq hinv le_top with h0 | h1
  · exact (hJ.isIrr h108.fixedSpace_H).ne_bot h0
  · exact hne h1

theorem two_le_ncard_irrOrbit {J : IrrSet Γ L} (hne : J.1 ≠ ⊤) :
    2 ≤ (irrOrbit h108 J).ncard := by
  obtain ⟨γ, hγ, hγJ⟩ := exists_conjSub_ne h108 J.2 hne
  have hne' : irrAct h108 ⟨γ, hγ⟩ J ≠ J := fun h => hγJ (congrArg Subtype.val h)
  have hsub : ({J, irrAct h108 ⟨γ, hγ⟩ J} : Set (IrrSet Γ L)) ⊆ irrOrbit h108 J := by
    rintro x (rfl | rfl)
    · exact ⟨1, by simp⟩
    · exact ⟨⟨γ, hγ⟩, rfl⟩
  have h2 : ({J, irrAct h108 ⟨γ, hγ⟩ J} : Set (IrrSet Γ L)).ncard = 2 :=
    Set.ncard_pair (Ne.symm hne')
  rw [← h2]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem mem_irrOrbit_of_card_three (hcard : Nat.card (IrrSet Γ L) = 3)
    (hne : ∀ J : IrrSet Γ L, J.1 ≠ ⊤) (I₀ J : IrrSet Γ L) : J ∈ irrOrbit h108 I₀ := by
  by_contra hJ
  have hdisj : Disjoint (irrOrbit h108 I₀) (irrOrbit h108 J) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    have hb' : irrAct h108 b J = irrAct h108 a I₀ := hb
    apply hJ
    refine ⟨b⁻¹ * a, ?_⟩
    show irrAct h108 (b⁻¹ * a) I₀ = J
    rw [map_mul, Equiv.Perm.mul_apply, ← hb']
    show (irrAct h108 b⁻¹ * irrAct h108 b) J = J
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  have h1 := two_le_ncard_irrOrbit h108 (hne I₀)
  have h2 := two_le_ncard_irrOrbit h108 (hne J)
  have h3 := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have h4 : (irrOrbit h108 I₀ ∪ irrOrbit h108 J).ncard ≤ Nat.card (IrrSet Γ L) :=
    Set.ncard_le_card _
  omega

omit h108 [Finite V] in
theorem stabilizerOf_le_self (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) :
    stabilizerOf K U ≤ K := fun _ hk =>
  And.left (show _ ∈ K ∧ conjSub _ U = U from hk)

theorem card_eq_three_mul_card_stabilizer (hcard : Nat.card (IrrSet Γ L) = 3)
    (hne : ∀ J : IrrSet Γ L, J.1 ≠ ⊤) (I₀ : IrrSet Γ L) :
    Nat.card ↥Γ = 3 * Nat.card ↥(stabilizerOf Γ I₀.1) := by
  let _ : MulAction ↥Γ (IrrSet Γ L) := MulAction.compHom (IrrSet Γ L) (irrAct h108)
  have h1 := MulAction.index_stabilizer ↥Γ I₀
  have horb : MulAction.orbit ↥Γ I₀ = Set.univ := by
    ext J
    simp only [Set.mem_univ, iff_true]
    exact mem_irrOrbit_of_card_three h108 hcard hne I₀ J
  have h2 : (MulAction.orbit ↥Γ I₀).ncard = 3 := by
    rw [horb, Set.ncard_univ, hcard]
  have hst : MulAction.stabilizer ↥Γ I₀ = (stabilizerOf Γ I₀.1).subgroupOf Γ := by
    ext γ
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨γ.2, congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  have h3 : Nat.card (MulAction.stabilizer ↥Γ I₀) = Nat.card ↥(stabilizerOf Γ I₀.1) := by
    rw [hst]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (stabilizerOf_le_self Γ I₀.1)).toEquiv
  have h4 := Subgroup.card_mul_index (MulAction.stabilizer ↥Γ I₀)
  rw [h1, h2, h3] at h4
  rw [← h4, mul_comm]

omit h108 [Finite V] in
theorem endOn_eq_endCommutant {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hH : Invariant H I) : endOn H I = endCommutant (restrictRange H I hH) := by
  unfold endOn endCommutant
  congr 1
  ext f
  constructor
  · rintro ⟨h, hh, hmem, rfl⟩
    exact ⟨restrictEquiv h I hh, restrictEquiv_mem_restrictRange hH hmem, rfl⟩
  · rintro ⟨h', hh', rfl⟩
    obtain ⟨k, hk, rfl⟩ := (mem_restrictRange_iff' hH).1 hh'
    exact ⟨k, hH.conjSub_eq hk, hk, rfl⟩

theorem card_irrSet_eq_three (hE11 : E11Stmt) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) (hhom : Homogeneous (normalClosure Γ L))
    (hH : Invariant (normalClosure Γ L) I) (hI4 : Module.finrank (ZMod 2) ↥I = 4)
    (hV8 : Module.finrank (ZMod 2) V = 8)
    (hend : EndIsField (restrictRange (normalClosure Γ L) I hH) 1) :
    Nat.card (IrrSet Γ L) = 3 := by
  obtain ⟨D⟩ := hE11 V (normalClosure Γ L) I hhom hI h108.fixedSpace_H h108.sSup_isIrr
  obtain ⟨e⟩ := hend
  have hF : Nat.card D.F = 2 := by
    have h1 : Nat.card D.F = Nat.card ↥(endOn (normalClosure Γ L) I) :=
      (Nat.card_congr D.endEquiv.toEquiv).symm
    rw [h1, endOn_eq_endCommutant hH, Nat.card_congr e.toEquiv, GaloisField.card 2 1 one_ne_zero]
    norm_num
  have hk : Module.finrank D.F D.U = 2 := by
    have h4 : Module.finrank D.F D.U * Module.finrank (ZMod 2) ↥I = Module.finrank (ZMod 2) V :=
      D.finrank_mul
    rw [hI4, hV8] at h4
    omega
  have h3 := Projectivization.card_of_finrank_two D.F D.U hk
  rw [Nat.card_congr D.ψ, h3, hF]

end Action

end G117

end G11

end CFSG.Quasithin
