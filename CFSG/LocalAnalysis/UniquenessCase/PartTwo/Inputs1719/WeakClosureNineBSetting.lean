module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open Subgroup CFSG.Quasithin

variable {X : Type} [Group X]

theorem map_conj_mul (g h : X) (H : Subgroup X) :
    H.map (MulAut.conj (g * h)).toMonoidHom =
      (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_injective (g : X) {H K : Subgroup X}
    (h : H.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj g).toMonoidHom) : H = K :=
  map_injective (MulAut.conj g).injective h

theorem mem_map_conj_iff {g x : X} {H : Subgroup X} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_eq_self_iff {g : X} {H : Subgroup X} :
    H.map (MulAut.conj g).toMonoidHom = H ↔ g ∈ normalizer (H : Set X) :=
  mem_normalizer_iff_map_conj_eq.symm

structure Setting (L L' Tb : Subgroup X) (t₀ : X) : Prop where
  t₀_mem : t₀ ∈ Tb
  conj_t₀ : L' = L.map (MulAut.conj t₀).toMonoidHom
  ne : L ≠ L'
  perm : ∀ t ∈ Tb, L.map (MulAut.conj t).toMonoidHom = L ∨ L.map (MulAut.conj t).toMonoidHom = L'
  comm : ⁅L, L'⁆ = ⊥
  normal : (L ⊔ L').Normal
  cent : centralizer ((L ⊔ L' : Subgroup X) : Set X) = ⊥
  top : L ⊔ L' ⊔ Tb = ⊤

namespace Setting

variable {L L' Tb : Subgroup X} {t₀ : X} (hS : Setting L L' Tb t₀)
include hS

theorem le_centralizer : L' ≤ centralizer (L : Set X) := by
  rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
  exact hS.comm

theorem le_centralizer' : L ≤ centralizer (L' : Set X) :=
  commutator_eq_bot_iff_le_centralizer.mp hS.comm

theorem commute {l l' : X} (hl : l ∈ L) (hl' : l' ∈ L') : l' * l = l * l' :=
  (mem_centralizer_iff.mp (hS.le_centralizer hl') l hl).symm

theorem sup_le_normalizer : L ⊔ L' ≤ normalizer (L : Set X) :=
  sup_le le_normalizer (hS.le_centralizer.trans (centralizer_le_normalizer _))

theorem sup_le_normalizer' : L ⊔ L' ≤ normalizer (L' : Set X) :=
  sup_le (hS.le_centralizer'.trans (centralizer_le_normalizer _)) le_normalizer

theorem t₀_not_mem : t₀ ∉ normalizer (L : Set X) := by
  intro h
  exact hS.ne (by rw [hS.conj_t₀, map_conj_eq_self_iff.mpr h])

theorem swap_of_mem {t : X} (ht : t ∈ Tb) (htn : t ∉ normalizer (L : Set X)) :
    L.map (MulAut.conj t).toMonoidHom = L' ∧ L'.map (MulAut.conj t).toMonoidHom = L := by
  have h1 : L.map (MulAut.conj t).toMonoidHom = L' :=
    (hS.perm t ht).resolve_left fun h => htn (map_conj_eq_self_iff.mp h)
  refine ⟨h1, ?_⟩
  have h2 : L'.map (MulAut.conj t).toMonoidHom = L.map (MulAut.conj (t * t₀)).toMonoidHom := by
    rw [map_conj_mul, ← hS.conj_t₀]
  rcases hS.perm (t * t₀) (Tb.mul_mem ht hS.t₀_mem) with h3 | h3
  · rw [h2, h3]
  · exfalso
    rw [← h2] at h3
    exact hS.ne (map_conj_injective t (h3.trans h1.symm)).symm

theorem swap {x : X} (hx : x ∉ normalizer (L : Set X)) :
    L.map (MulAut.conj x).toMonoidHom = L' ∧ L'.map (MulAut.conj x).toMonoidHom = L := by
  have : (L ⊔ L').Normal := hS.normal
  have hx' : x ∈ ((L ⊔ L' ⊔ Tb : Subgroup X) : Set X) := by rw [hS.top]; exact mem_top x
  rw [normal_mul] at hx'
  obtain ⟨n, hn, t, ht, rfl⟩ := hx'
  have hnL : n ∈ normalizer (L : Set X) := hS.sup_le_normalizer hn
  have hnL' : n ∈ normalizer (L' : Set X) := hS.sup_le_normalizer' hn
  have htn : t ∉ normalizer (L : Set X) := fun h => hx (mul_mem hnL h)
  obtain ⟨h1, h2⟩ := hS.swap_of_mem ht htn
  rw [map_conj_mul, map_conj_mul, h1, h2, map_conj_eq_self_iff.mpr hnL,
    map_conj_eq_self_iff.mpr hnL']
  exact ⟨rfl, rfl⟩

theorem index_normalizer : (normalizer (L : Set X)).index = 2 := by
  rw [index_eq_two_iff]
  refine ⟨t₀, fun b => ?_⟩
  by_cases hb : b ∈ normalizer (L : Set X)
  · refine Or.inr ⟨hb, fun h => hS.t₀_not_mem ?_⟩
    simpa using mul_mem (inv_mem hb) h
  · refine Or.inl ⟨?_, hb⟩
    rw [← map_conj_eq_self_iff, map_conj_mul, ← hS.conj_t₀]
    exact (hS.swap hb).2

theorem mul_mem_iff {a b : X} :
    a * b ∈ normalizer (L : Set X) ↔ (a ∈ normalizer (L : Set X) ↔ b ∈ normalizer (L : Set X)) :=
  mul_mem_iff_of_index_two hS.index_normalizer

theorem conj_t₀_inv : L.map (MulAut.conj t₀⁻¹).toMonoidHom = L' := by
  rw [← (hS.swap hS.t₀_not_mem).2, ← map_conj_mul, inv_mul_cancel]
  ext x
  simp

theorem mem_L'_of_mem {l : X} (hl : l ∈ L) : t₀⁻¹ * l * t₀ ∈ L' := by
  rw [← hS.conj_t₀_inv, mem_map_conj_iff, inv_inv]
  simpa [mul_assoc] using hl

theorem mem_L_of_mem' {l : X} (hl : l ∈ L') : t₀⁻¹ * l * t₀ ∈ L := by
  rw [hS.conj_t₀, mem_map_conj_iff] at hl
  exact hl

theorem mem_L'_of_mem_conj {l : X} (hl : l ∈ L) : t₀ * l * t₀⁻¹ ∈ L' := by
  rw [hS.conj_t₀, mem_map_conj_iff]
  simpa [mul_assoc] using hl

end Setting

end CFSG.LocalAnalysis.WeakClosure81.NGM
