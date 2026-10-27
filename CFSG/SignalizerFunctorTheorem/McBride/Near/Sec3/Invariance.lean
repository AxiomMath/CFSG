module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Defs

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {G : Type u} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem admits_iff_map {Q X : Subgroup G} :
    Admits Q X ↔ ∀ g ∈ Q, X.map (MulAut.conj g).toMonoidHom = X :=
  forall₂_congr fun _ _ => Subgroup.mem_normalizer_iff_map_conj_eq

theorem Admits.inf {Q X Y : Subgroup G} (hX : Admits Q X) (hY : Admits Q Y) :
    Admits Q (X ⊓ Y) :=
  fun _ hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hX hg, hY hg⟩

theorem Admits.iSup {Q : Subgroup G} {ι : Sort*} {f : ι → Subgroup G}
    (h : ∀ i, Admits Q (f i)) : Admits Q (⨆ i, f i) := by
  rw [admits_iff_map]
  intro g hg
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => (admits_iff_map.mp (h i)) g hg

theorem Admits.sup {Q X Y : Subgroup G} (hX : Admits Q X) (hY : Admits Q Y) :
    Admits Q (X ⊔ Y) := by
  rw [admits_iff_map] at hX hY ⊢
  intro g hg
  rw [Subgroup.map_sup, hX g hg, hY g hg]

theorem Admits.mono_left {Q Q' X : Subgroup G} (h : Admits Q X) (hQ : Q' ≤ Q) : Admits Q' X :=
  hQ.trans h

theorem commute_of_mem {A : Subgroup G} (hA : IsMulCommutative A) {g a : G} (hg : g ∈ A)
    (ha : a ∈ A) : Commute g a :=
  congrArg Subtype.val (hA.is_comm.comm (⟨g, hg⟩ : A) ⟨a, ha⟩)

theorem commute_conj_iff {a u k : G} (hu : Commute u a) :
    Commute (u * k * u⁻¹) a ↔ Commute k a := by
  have h1 : u * a * u⁻¹ = a := by rw [hu.eq, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : u⁻¹ * a * u = a := by
    have := hu.inv_left.eq
    rw [this, mul_assoc, inv_mul_cancel, mul_one]
  constructor
  · intro h
    have := h.map (MulAut.conj u⁻¹).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc, h2] using this
  · intro h
    have := h.map (MulAut.conj u).toMonoidHom
    simpa [MulAut.conj_apply, mul_assoc, h1] using this

theorem admits_centralizer_singleton {Q : Subgroup G} {a : G}
    (hQ : Q ≤ Subgroup.centralizer {a}) : Admits Q (Subgroup.centralizer {a}) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hga : Commute g a := Subgroup.mem_centralizer_singleton_iff.mp (hQ hg)
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact (commute_conj_iff hga).symm

theorem admits_self (X : Subgroup G) : Admits X X :=
  Subgroup.le_normalizer

end CFSG.SignalizerFunctorTheorem.McBride.Near
