
module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Tab
public import Mathlib.GroupTheory.GroupAction.SubMulAction

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open scoped Pointwise

@[expose] def actN (g : G24) (p : ℕ) : ℕ := (tab 24 g).getD p p

theorem actN_of_lt (g : G24) {p : ℕ} (hp : p < 24) :
    actN g p = ((g • (⟨p, hp⟩ : Fin 24) : Fin 24) : ℕ) := by
  have := tab_getD (n := 24) g ⟨p, hp⟩
  unfold actN
  have hlen : p < (tab 24 g).length := by simp [tab, hp]
  rw [List.getD_eq_getElem _ _ hlen]
  rw [List.getD_eq_getElem _ _ hlen] at this
  exact this

theorem actN_of_ge (g : G24) {p : ℕ} (hp : 24 ≤ p) : actN g p = p := by
  unfold actN
  rw [List.getD_eq_default]
  simp [tab, hp]

instance instMulActionNat : MulAction G24 ℕ where
  smul := actN
  one_smul p := by
    show actN 1 p = p
    by_cases hp : p < 24
    · rw [actN_of_lt _ hp]
      simp
    · exact actN_of_ge 1 (by omega)
  mul_smul g h p := by
    show actN (g * h) p = actN g (actN h p)
    by_cases hp : p < 24
    · have h1 := actN_of_lt h hp
      have h2 : actN h p < 24 := by rw [h1]; exact (h • (⟨p, hp⟩ : Fin 24)).2
      rw [actN_of_lt (g * h) hp, actN_of_lt g h2]
      simp only [mul_smul]
      congr 2
      exact Fin.ext h1.symm
    · have hp' : 24 ≤ p := by omega
      rw [actN_of_ge (g * h) hp', actN_of_ge h hp', actN_of_ge g hp']

theorem smul_nat (g : G24) (p : ℕ) : g • p = (tab 24 g).getD p p := rfl

theorem smul_finset_eq_image (g : G24) (T : Finset ℕ) :
    g • T = T.image (fun p => (tab 24 g).getD p p) := by
  rw [Finset.smul_finset_def]
  exact Finset.image_congr fun p _ => smul_nat g p

theorem smul_finset_finset_eq_image (g : G24) (X : Finset (Finset ℕ)) :
    g • X = X.image (fun T => T.image (fun p => (tab 24 g).getD p p)) := by
  rw [Finset.smul_finset_def]
  exact Finset.image_congr fun T _ => smul_finset_eq_image g T

section ListHom

variable {Γ α : Type} [Group Γ] [MulAction Γ α] [DecidableEq α]

@[expose] def listSub (Z : Subgroup Γ) (L : List α) (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) :
    SubMulAction ↥Z α where
  carrier := {x | x ∈ L}
  smul_mem' c _ hx := hZ c c.2 _ hx

@[expose] def listEquiv (L : List α) (hnd : L.Nodup) (Z : Subgroup Γ)
    (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) : Fin L.length ≃ ↥(listSub Z L hZ) where
  toFun i := ⟨L[i], List.getElem_mem i.2⟩
  invFun x := ⟨L.idxOf x.1, List.idxOf_lt_length_iff.mpr x.2⟩
  left_inv i := by
    apply Fin.ext
    exact List.get_idxOf hnd i
  right_inv x := by
    apply Subtype.ext
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr x.2)

@[expose] def permCongrEquiv {β γ : Type} (e : β ≃ γ) : Equiv.Perm β ≃* Equiv.Perm γ where
  toEquiv := e.permCongr
  map_mul' f g := by ext x; simp [Equiv.permCongr_apply]

@[expose] def listHom (Z : Subgroup Γ) (L : List α) (hnd : L.Nodup)
    (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) : ↥Z →* Equiv.Perm (Fin L.length) :=
  (permCongrEquiv (listEquiv L hnd Z hZ).symm).toMonoidHom.comp
    (MulAction.toPermHom ↥Z ↥(listSub Z L hZ))

theorem listHom_spec (Z : Subgroup Γ) (L : List α) (hnd : L.Nodup)
    (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) (z : ↥Z) (i : Fin L.length) :
    L[(listHom Z L hnd hZ z i : ℕ)]'(listHom Z L hnd hZ z i).2 = (z : Γ) • L[i] := by
  have h := (listEquiv L hnd Z hZ).apply_symm_apply
    (MulAction.toPermHom ↥Z ↥(listSub Z L hZ) z (listEquiv L hnd Z hZ i))
  show ((listEquiv L hnd Z hZ) ((listEquiv L hnd Z hZ).symm
      (MulAction.toPermHom ↥Z ↥(listSub Z L hZ) z (listEquiv L hnd Z hZ i)))).1 = _
  rw [h]
  rfl

theorem listHom_eq_of (Z : Subgroup Γ) (L : List α) (hnd : L.Nodup)
    (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) (z : ↥Z) (i j : Fin L.length)
    (h : L[(j : ℕ)] = (z : Γ) • L[i]) : listHom Z L hnd hZ z i = j := by
  have h1 := listHom_spec Z L hnd hZ z i
  rw [← h] at h1
  exact Fin.ext ((hnd.getElem_inj_iff).mp h1)

theorem listHom_val (Z : Subgroup Γ) (L : List α) (hnd : L.Nodup)
    (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) (z : ↥Z) (i : Fin L.length) :
    ((listHom Z L hnd hZ z i : Fin L.length) : ℕ) = L.idxOf ((z : Γ) • L[i]) := by
  have h := listHom_spec Z L hnd hZ z i
  conv_rhs => rw [← h]
  exact (List.get_idxOf hnd (listHom Z L hnd hZ z i)).symm

end ListHom

theorem map_finRange_getElem {β γ : Type} (L : List β) (g : β → γ) :
    (List.finRange L.length).map (fun i => g L[i]) = L.map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem tab_listHom {α : Type} [MulAction G24 α] [DecidableEq α] (act' : List ℕ → α → α)
    (hact : ∀ (g : G24) (x : α), g • x = act' (tab 24 g) x) (Z : Subgroup G24) (L : List α)
    (hnd : L.Nodup) (hZ : ∀ z ∈ Z, ∀ x ∈ L, z • x ∈ L) (z : ↥Z) :
    tab L.length (listHom Z L hnd hZ z) = L.map (fun x => L.idxOf (act' (tab 24 z.1) x)) := by
  unfold tab
  have h1 : ∀ i : Fin L.length, ((listHom Z L hnd hZ z • i : Fin L.length) : ℕ) =
      L.idxOf (act' (tab 24 z.1) L[i]) := by
    intro i
    rw [Equiv.Perm.smul_def, listHom_val, hact]
  simp only [h1]
  exact map_finRange_getElem L (fun x => L.idxOf (act' (tab 24 z.1) x))

end CFSG.Quasithin.A312M24
