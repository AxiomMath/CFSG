module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCSelfNorm
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.FlagBorel
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.SL3Parabolic
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

section Lin

variable {F : Type} [Field F]

@[expose] def stabAct (w : Fin 3 → F) : Subgroup (GL (Fin 3) F) where
  carrier := {g | glAct g w = w}
  mul_mem' := fun {a b} ha hb => by
    have ha' : glAct a w = w := ha
    have hb' : glAct b w = w := hb
    show glAct (a * b) w = w
    rw [glAct_mul, hb', ha']
  one_mem' := glAct_one w
  inv_mem' := fun {g} hg => by
    have hg' : glAct g w = w := hg
    show glAct g⁻¹ w = w
    refine glAct_injective g ?_
    rw [← glAct_mul, mul_inv_cancel, glAct_one, hg']

theorem mem_stabAct {w : Fin 3 → F} {g : GL (Fin 3) F} : g ∈ stabAct w ↔ glAct g w = w := Iff.rfl

end Lin

section Z2

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC
open scoped Matrix

theorem card_filter_stab : ∀ w : Fin 3 → ZMod 2, w ≠ 0 →
    (Finset.univ.filter fun M : Mat3 => M.det ≠ 0 ∧ M *ᵥ w = w).card = 24 := by
  decide +kernel

theorem card_stabAct_Z2 (w : Fin 3 → ZMod 2) (hw : w ≠ 0) :
    Nat.card (stabAct w : Subgroup (GL (Fin 3) (ZMod 2))) = 24 := by
  rw [natCard_eq_card_of (stabAct w) (Finset.univ.filter fun M : Mat3 => M.det ≠ 0 ∧ M *ᵥ w = w)]
  · exact card_filter_stab w hw
  · intro g hg
    have hg' : (g : Mat3) *ᵥ w = w := hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨det_ne_zero_of_unit g, hg'⟩
  · intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hM.1, hM.2, rfl⟩

end Z2

section Gen

variable {F : Type} [Field F] [Fintype F]

theorem stab_max_of_card {w : Fin 3 → F} (hF : Fintype.card F = 2)
    (hcard : Nat.card (stabAct w : Subgroup (GL (Fin 3) F)) = 24)
    (P : Subgroup (GL (Fin 3) F)) (hP : stabAct w ≤ P) {g : GL (Fin 3) F} (hg : g ∈ P)
    (hgw : g ∉ stabAct w) : P = ⊤ := by
  have h168 := Stellmacher.PU.L3YC.card_gl3 hF
  have hs7 : (stabAct w : Subgroup (GL (Fin 3) F)).index = 7 := by
    have := Subgroup.card_mul_index (stabAct w : Subgroup (GL (Fin 3) F))
    rw [hcard, h168] at this
    omega
  have hdvd : P.index ∣ 7 := hs7 ▸ Subgroup.index_dvd_of_le hP
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd with h1 | h7
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    have hP24 : Nat.card P = 24 := by
      have := Subgroup.card_mul_index P
      rw [h7, h168] at this
      omega
    have heq : stabAct w = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hP24, hcard])
    exact hgw (heq ▸ hg)

@[expose] noncomputable def glZ2 [CharP F 2] (hF : Fintype.card F = 2) :
    GL (Fin 3) F ≃* GL (Fin 3) (ZMod 2) :=
  Units.mapEquiv (RingEquiv.mapMatrix (ZMod.ringEquiv F hF).symm).toMulEquiv

theorem glAct_glZ2 [CharP F 2] (hF : Fintype.card F = 2) (g : GL (Fin 3) F) (x : Fin 3 → F) :
    glAct (glZ2 hF g) (fun i => ((ZMod.ringEquiv F hF).symm (x i))) =
      fun i => (ZMod.ringEquiv F hF).symm (glAct g x i) := by
  funext i
  have h1 : ((glZ2 hF g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (g : Matrix (Fin 3) (Fin 3) F).map ((ZMod.ringEquiv F hF).symm : F →+* ZMod 2) := rfl
  show ((glZ2 hF g : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec _ i = _
  rw [h1]
  exact (RingHom.map_mulVec ((ZMod.ringEquiv F hF).symm : F →+* ZMod 2)
    (g : Matrix (Fin 3) (Fin 3) F) x i).symm

theorem card_stabAct (hF : Fintype.card F = 2) {w : Fin 3 → F} (hw : w ≠ 0) :
    Nat.card (stabAct w : Subgroup (GL (Fin 3) F)) = 24 := by
  have : CharP F 2 := charP_of_card_eq_prime (p := 2) hF
  let φ := glZ2 hF
  let e := (ZMod.ringEquiv F hF).symm
  have hw' : (fun i => e (w i)) ≠ 0 := by
    intro h
    apply hw
    funext i
    have := congrFun h i
    simpa using this
  have hmap : (stabAct w : Subgroup (GL (Fin 3) F)).map φ.toMonoidHom =
      stabAct (fun i => e (w i)) := by
    ext g
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨g', hg', rfl⟩
      have h1 := glAct_glZ2 hF g' w
      show glAct (φ g') (fun i => e (w i)) = _
      rw [h1, show glAct g' w = w from hg']
    · intro hg
      refine ⟨φ.symm g, ?_, by simp⟩
      have hg' : glAct g (fun i => e (w i)) = fun i => e (w i) := hg
      have h1 := glAct_glZ2 hF (φ.symm g) w
      rw [show φ (φ.symm g) = g from φ.apply_symm_apply g, hg'] at h1
      show glAct (φ.symm g) w = w
      funext i
      exact e.injective (congrFun h1.symm i)
  have := card_stabAct_Z2 (fun i => e (w i)) hw'
  rw [← hmap] at this
  exact (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).symm.trans this

theorem stab_max (hF : Fintype.card F = 2) {w : Fin 3 → F} (hw : w ≠ 0)
    (P : Subgroup (GL (Fin 3) F)) (hP : stabAct w ≤ P) {g : GL (Fin 3) F} (hg : g ∈ P)
    (hgw : g ∉ stabAct w) : P = ⊤ :=
  stab_max_of_card hF (card_stabAct hF hw) P hP hg hgw

theorem eq_top_of_gen (hF : Fintype.card F = 2) {w : Fin 3 → F} (hw : w ≠ 0)
    {Q D : Subgroup (GL (Fin 3) F)} (hD : Nat.card D = 8) (hDQ : D ≤ Q) (hDw : D ≤ stabAct w)
    {g₃ : GL (Fin 3) F} (hg₃Q : g₃ ∈ Q) (hg₃w : g₃ ∈ stabAct w) (hg₃ : orderOf g₃ = 3)
    {h : GL (Fin 3) F} (hhQ : h ∈ Q) (hhw : h ∉ stabAct w) : Q = ⊤ := by
  have hc := card_stabAct hF hw
  set Q' : Subgroup (GL (Fin 3) F) := Q ⊓ stabAct w with hQ'
  have hDQ' : D ≤ Q' := le_inf hDQ hDw
  have h8 : 8 ∣ Nat.card Q' := hD ▸ Subgroup.card_dvd_of_le hDQ'
  have h3 : 3 ∣ Nat.card Q' := by
    have hm : g₃ ∈ Q' := ⟨hg₃Q, hg₃w⟩
    have := orderOf_dvd_natCard (⟨g₃, hm⟩ : ↥Q')
    rwa [Subgroup.orderOf_mk, hg₃] at this
  have h24 : 24 ∣ Nat.card Q' := by
    have : Nat.Coprime 8 3 := by norm_num
    simpa using this.mul_dvd_of_dvd_of_dvd h8 h3
  have hle : Nat.card Q' ∣ 24 := hc ▸ Subgroup.card_dvd_of_le (inf_le_right : Q' ≤ stabAct w)
  have hQ24 : Nat.card Q' = 24 := Nat.dvd_antisymm hle h24
  have heq : Q' = stabAct w :=
    Subgroup.eq_of_le_of_card_ge (inf_le_right : Q' ≤ stabAct w) (by rw [hQ24, hc])
  have hsQ : stabAct w ≤ Q := heq ▸ (inf_le_left : Q' ≤ Q)
  exact stab_max hF hw Q hsQ hhQ hhw

end Gen

end Stellmacher.L3YC

end CFSG.Quasithin
