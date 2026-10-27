module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG

section Tools

variable {G : Type} [Group G]

theorem mem_conjBy_iff {g x : G} {H : Subgroup G} : x ∈ conjBy g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conjBy_conjBy_inv (g : G) (H : Subgroup G) : conjBy g⁻¹ (conjBy g H) = H := by
  ext x
  rw [mem_conjBy_iff, mem_conjBy_iff]
  simp [mul_assoc]

theorem normal_subgroupOf_of_conj {H M : Subgroup G} (hMH : M ≤ H)
    (hn : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) : (M.subgroupOf H).Normal := by
  refine ⟨fun n hn' g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn' ⊢
  simpa using hn g g.2 n hn'

theorem Op_le (p : ℕ) (H : Subgroup G) : Op p H ≤ H := Subgroup.map_subtype_le _

theorem Op_isPGroup (p : ℕ) (H : Subgroup G) : IsPGroup p (Op p H) :=
  (CFSG.pCore_isPGroup (p := p) (G := H)).map H.subtype

theorem le_Op_of_normal (p : ℕ) (H M : Subgroup G) (hMH : M ≤ H) (hM : IsPGroup p M)
    (hn : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M) : M ≤ Op p H := by
  have hMn := normal_subgroupOf_of_conj hMH hn
  have hMp : IsPGroup p (M.subgroupOf H) :=
    IsPGroup.of_injective hM (Subgroup.subgroupOfEquivOfLe hMH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hMH).injective
  have hle : M.subgroupOf H ≤ pCore p H := by
    unfold pCore
    exact le_sSup ⟨hMn, hMp⟩
  intro m hm
  have hmem : (⟨m, hMH hm⟩ : H) ∈ M.subgroupOf H := hm
  exact Subgroup.mem_map.2 ⟨⟨m, hMH hm⟩, hle hmem, rfl⟩

theorem Op_conj_mem (p : ℕ) {H : Subgroup G} {h : G} (hh : h ∈ Nor H) {x : G}
    (hx : x ∈ Op p H) : h * x * h⁻¹ ∈ Op p H := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  let α : MulAut H := H.normalizerMonoidHom ⟨h, hh⟩
  have hmap := pCore_map_iso p α
  have hmem : α y ∈ pCore p H := by
    rw [← hmap]
    exact Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  refine Subgroup.mem_map.2 ⟨α y, hmem, ?_⟩
  have h5 : ((α y : H) : G) = h * (y : G) * h⁻¹ := by
    show ((H.normalizerMonoidHom ⟨h, hh⟩ y : H) : G) = h * (y : G) * h⁻¹
    simp
  exact h5

theorem inSubgroup_map_aut (F : ∀ (K : Type) [Group K], Subgroup K)
    (hF : ∀ (A B : Type) [Group A] [Group B] (e : A ≃* B), (F A).map e.toMonoidHom = F B)
    (φ : G ≃* G) (M : Subgroup G) :
    inSubgroup F (M.map φ.toMonoidHom) = (inSubgroup F M).map φ.toMonoidHom := by
  unfold inSubgroup
  let e : ↥M ≃* ↥(M.map φ.toMonoidHom) := MulEquiv.subgroupMap φ M
  have h1 := hF ↥M ↥(M.map φ.toMonoidHom) e
  have hcomp : (M.map φ.toMonoidHom).subtype.comp e.toMonoidHom =
      φ.toMonoidHom.comp M.subtype := by
    ext x
    rfl
  rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem Op_conjBy (p : ℕ) (g : G) (H : Subgroup G) :
    Op p (conjBy g H) = conjBy g (Op p H) :=
  inSubgroup_map_aut (pCore p) (fun _ _ _ _ e => pCore_map_iso p e) (MulAut.conj g) H

theorem Opp_conjBy (p : ℕ) (g : G) (H : Subgroup G) :
    Opp p (conjBy g H) = conjBy g (Opp p H) :=
  inSubgroup_map_aut (pPrimeCore p) (fun _ _ _ _ e => pPrimeCore_map_iso p e) (MulAut.conj g) H

theorem Nor_conjBy (g : G) (H : Subgroup G) : Nor (conjBy g H) = conjBy g (Nor H) := by
  ext x
  rw [mem_conjBy_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    have := h (g * y * g⁻¹)
    rw [mem_conjBy_iff, mem_conjBy_iff] at this
    simpa [mul_assoc] using this
  · intro h y
    rw [mem_conjBy_iff, mem_conjBy_iff]
    have := h (g⁻¹ * y * g)
    simpa [mul_assoc] using this

theorem Cen_conjBy (g x : G) : Cen (g * x * g⁻¹) = conjBy g (Cen x) := by
  ext y
  rw [mem_conjBy_iff, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : g⁻¹ * y * g * x = x * (g⁻¹ * y * g) := by
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    first | exact h' | exact h'.symm
  · intro h
    have := congrArg (fun z => g * z * g⁻¹) h
    first | simpa [mul_assoc] using this | simpa [mul_assoc] using this.symm

end Tools

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
