module

public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.Monster.B.Co2.PermArr

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2 CFSG.ComponentClassification.PSL3Four

structure PointsList (n m : ℕ) (L : List ℕ) : Prop where
  len : L.length = m
  lt : ∀ x ∈ L, x < n
  nodup : L.Nodup

namespace PointsList

variable {n m : ℕ} {L : List ℕ} (hL : PointsList n m L)

@[expose] def pt (i : Fin m) : Fin n :=
  ⟨L[i.val]'(by rw [hL.len]; exact i.2), hL.lt _ (List.getElem_mem _)⟩

theorem pt_val (i : Fin m) : ((hL.pt i : Fin n) : ℕ) = L[i.val]'(by rw [hL.len]; exact i.2) :=
  rfl

theorem pt_mem (i : Fin m) : ((hL.pt i : Fin n) : ℕ) ∈ L := List.getElem_mem _

theorem pt_injective : Function.Injective hL.pt := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [pt_val] at h'
  exact Fin.ext ((hL.nodup.getElem_inj_iff).1 h')

theorem exists_pt {x : Fin n} (hx : (x : ℕ) ∈ L) : ∃ i, hL.pt i = x := by
  obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
  exact ⟨⟨k, by rw [← hL.len]; exact hk⟩, Fin.ext hkx⟩

theorem idxOf_pt (i : Fin m) : L.idxOf ((hL.pt i : Fin n) : ℕ) = i := by
  have hi : i.val < L.length := by rw [hL.len]; exact i.2
  have hlt : L.idxOf L[i.val] < L.length := List.idxOf_lt_length_of_mem (List.getElem_mem hi)
  have := List.getElem_idxOf hlt
  rw [pt_val]
  exact (hL.nodup.getElem_inj_iff).1 this

@[expose] def eqv : Fin m ≃ {x : Fin n // (x : ℕ) ∈ L} :=
  Equiv.ofBijective (fun i => ⟨hL.pt i, hL.pt_mem i⟩)
    ⟨fun i j h => hL.pt_injective (congrArg Subtype.val h), fun x => by
      obtain ⟨i, hi⟩ := hL.exists_pt x.2
      exact ⟨i, Subtype.ext hi⟩⟩

@[expose] def restrPerm (g : Equiv.Perm (Fin n)) (hg : ∀ x : Fin n, (x : ℕ) ∈ L ↔ (g x : ℕ) ∈ L) :
    Equiv.Perm (Fin m) :=
  hL.eqv.symm.permCongr (g.subtypePerm fun x => (hg x).symm)

theorem pt_restrPerm (g : Equiv.Perm (Fin n)) (hg : ∀ x : Fin n, (x : ℕ) ∈ L ↔ (g x : ℕ) ∈ L)
    (i : Fin m) : hL.pt (hL.restrPerm g hg i) = g (hL.pt i) := by
  have h := hL.eqv.apply_symm_apply ((g.subtypePerm fun x => (hg x).symm) (hL.eqv i))
  have h' := congrArg Subtype.val h
  exact h'

theorem restrPerm_eq_iff (g : Equiv.Perm (Fin n)) (hg : ∀ x : Fin n, (x : ℕ) ∈ L ↔ (g x : ℕ) ∈ L)
    (σ : Equiv.Perm (Fin m)) : hL.restrPerm g hg = σ ↔ ∀ i, hL.pt (σ i) = g (hL.pt i) := by
  constructor
  · rintro rfl i
    exact hL.pt_restrPerm g hg i
  · intro h
    ext i
    exact congrArg Fin.val (hL.pt_injective ((hL.pt_restrPerm g hg i).trans (h i).symm))

theorem tabRep_restrictArr {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hg : ∀ x : Fin n, (x : ℕ) ∈ L ↔ (g x : ℕ) ∈ L) :
    TabRep (restrictArr L t) (hL.restrPerm g hg) := by
  refine ⟨by simp [restrictArr, hL.len], fun i => ?_⟩
  have hi : i.val < L.length := by rw [hL.len]; exact i.2
  rw [restrictArr, getElem!_pos _ _ (by simpa using hi), List.getElem_toArray,
    List.getElem_map]
  have e1 : t[L[i.val]]! = ((g (hL.pt i) : Fin n) : ℕ) := ht (hL.pt i)
  rw [e1, ← hL.pt_restrPerm g hg i, hL.idxOf_pt]

section Hom

variable (H : Subgroup (Equiv.Perm (Fin n)))
  (hH : ∀ g ∈ H, ∀ x : Fin n, (x : ℕ) ∈ L → (g x : ℕ) ∈ L)

include hH in
theorem mem_iff_of_mem {g : Equiv.Perm (Fin n)} (hg : g ∈ H) (x : Fin n) :
    (x : ℕ) ∈ L ↔ (g x : ℕ) ∈ L := by
  refine ⟨hH g hg x, fun h => ?_⟩
  have := hH g⁻¹ (H.inv_mem hg) (g x) h
  simpa using this

@[expose] def restrHom : H →* Equiv.Perm (Fin m) where
  toFun g := hL.restrPerm g.1 (mem_iff_of_mem H hH g.2)
  map_one' := by
    rw [restrPerm_eq_iff]
    intro i
    rfl
  map_mul' g h := by
    rw [restrPerm_eq_iff]
    intro i
    rw [Equiv.Perm.mul_apply, hL.pt_restrPerm, hL.pt_restrPerm, Subgroup.coe_mul,
      Equiv.Perm.mul_apply]

theorem pt_restrHom (g : H) (i : Fin m) :
    hL.pt (hL.restrHom H hH g i) = (g : Equiv.Perm (Fin n)) (hL.pt i) :=
  hL.pt_restrPerm _ (mem_iff_of_mem H hH g.2) i

theorem tabRep_restrHom {t : Array ℕ} (g : H) (ht : Rep n t g) :
    TabRep (restrictArr L t) (hL.restrHom H hH g) :=
  hL.tabRep_restrictArr ht (mem_iff_of_mem H hH g.2)

theorem restrHom_eq_one_iff (g : H) :
    hL.restrHom H hH g = 1 ↔ ∀ x : Fin n, (x : ℕ) ∈ L → (g : Equiv.Perm (Fin n)) x = x := by
  constructor
  · intro h x hx
    obtain ⟨i, rfl⟩ := hL.exists_pt hx
    have := hL.pt_restrHom H hH g i
    rw [h] at this
    exact this.symm
  · intro h
    ext i
    have := hL.pt_restrHom H hH g i
    rw [h _ (hL.pt_mem i)] at this
    exact congrArg Fin.val (hL.pt_injective this)

end Hom

end PointsList

end CFSG.Sporadic.SuzOddCore
