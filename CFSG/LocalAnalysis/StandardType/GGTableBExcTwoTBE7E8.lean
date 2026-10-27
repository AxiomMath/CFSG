module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open TableBExcTwo

namespace TableBExcTwoTB

def wordE7 : List (Fin 7) := [3, 5, 4, 3, 2, 6, 4, 5, 1, 3, 0, 2, 3, 1, 4, 3, 2, 0]

def permE7 : Fin 7 → Fin 7 := ![2, 0, 3, 4, 5, 6, 1]

theorem permE7_root : ∀ a : Fin 7, wAct Tag.E7 wordE7 (frameE7Root a) =
    frameE7Root (permE7 a) ∨ wAct Tag.E7 wordE7 (frameE7Root a) = -frameE7Root (permE7 a) := by
  decide +kernel

theorem htrans_E7 : ∀ S : Finset (Fin 7), S.Nonempty → (∀ a ∈ S, permE7 a ∈ S) →
    (∀ a ∈ S, permE7 a ∈ S) → S = Finset.univ := by
  decide +kernel

def wordE8c : List (Fin 8) := [3, 5, 4, 3, 2, 6, 4, 5, 1, 3, 0, 2, 3, 1, 4, 3, 2, 0]

def permE8c : Fin 8 → Fin 8 := ![0, 3, 1, 4, 5, 6, 7, 2]

def wordE8g : List (Fin 8) := [7, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]

def permE8g : Fin 8 → Fin 8 := ![1, 0, 2, 3, 4, 5, 7, 6]

theorem permE8c_root : ∀ a : Fin 8, wAct Tag.E8 wordE8c (frameE8Root a) =
    frameE8Root (permE8c a) ∨ wAct Tag.E8 wordE8c (frameE8Root a) = -frameE8Root (permE8c a) := by
  decide +kernel

theorem permE8g_root : ∀ a : Fin 8, wAct Tag.E8 wordE8g (frameE8Root a) =
    frameE8Root (permE8g a) ∨ wAct Tag.E8 wordE8g (frameE8Root a) = -frameE8Root (permE8g a) := by
  decide +kernel

theorem htrans_E8 : ∀ S : Finset (Fin 8), S.Nonempty → (∀ a ∈ S, permE8c a ∈ S) →
    (∀ a ∈ S, permE8g a ∈ S) → S = Finset.univ := by
  decide +kernel

theorem secEltAt_map_conj {p : ℕ} {R : Type} [Group R] {E : Subgroup R}
    (h : E6TwoTB.SecEltAt p E) (g : R) :
    E6TwoTB.SecEltAt p (E.map (MulAut.conj g).toMonoidHom) := by
  refine E6TwoTB.SecEltAt.of_map (MulAut.conj g⁻¹) ?_
  have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id R :=
    MonoidHom.ext fun x => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
  rw [Subgroup.map_map, hc, Subgroup.map_id]
  exact h

theorem selfCent_map {R R' : Type} [Group R] [Group R'] (φ : R ≃* R') {E : Subgroup R}
    (h : ∀ g : R, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) :
    ∀ g' : R', g' ^ 3 = 1 → (∀ e ∈ E.map φ.toMonoidHom, g' * e = e * g') →
      g' ∈ E.map φ.toMonoidHom := by
  intro g' hg3 hc
  have hg : φ.symm g' ^ 3 = 1 := by
    rw [← map_pow, hg3, map_one]
  have hcomm : ∀ e ∈ E, φ.symm g' * e = e * φ.symm g' := by
    intro e he
    have h1 := hc (φ e) ⟨e, he, rfl⟩
    have h2 := congrArg φ.symm h1
    simpa only [map_mul, MulEquiv.symm_apply_apply] using h2
  exact ⟨φ.symm g', h _ hg hcomm, MulEquiv.apply_symm_apply φ g'⟩

section Frames


theorem permutesFrame_E7 : PermutesFrame frameE7 wordE7 permE7 := fun a => permE7_root a

theorem permutesFrame_E8c : PermutesFrame frameE8 wordE8c permE8c := fun a => permE8c_root a

theorem permutesFrame_E8g : PermutesFrame frameE8 wordE8g permE8g := fun a => permE8g_root a

theorem secEltAt_E7 {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) :
    E6TwoTB.SecEltAt 3 (tE K frameE7).range :=
  secEltAt_frame hK frameE7 permutesFrame_E7 permutesFrame_E7
    (fun S hne h1 h2 => htrans_E7 S hne h1 h2)

theorem secEltAt_E8 {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) :
    E6TwoTB.SecEltAt 3 (tE K frameE8).range :=
  secEltAt_frame hK frameE8 permutesFrame_E8c permutesFrame_E8g htrans_E8

@[expose] def GGE7TwoSCToral (K : Type) [Field K] [CharP K 2] : Prop :=
  ∀ E : Subgroup (adjointGroup .E7 K), IsElemAbelian 3 E → 3 ^ 6 ≤ Nat.card E →
    (∀ g : adjointGroup .E7 K, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
    ∃ c : adjointGroup .E7 K, E = (tE K frameE7).range.map (MulAut.conj c).toMonoidHom

@[expose] def GGE8TwoSCToral (K : Type) [Field K] [CharP K 2] : Prop :=
  ∀ E : Subgroup (adjointGroup .E8 K), IsElemAbelian 3 E → 3 ^ 7 ≤ Nat.card E →
    (∀ g : adjointGroup .E8 K, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
    ∃ c : adjointGroup .E8 K, E = (tE K frameE8).range.map (MulAut.conj c).toMonoidHom

end Frames

end TableBExcTwoTB

end CFSG.StandardType

end
