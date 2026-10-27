module

public import CFSG.Timmesfeld.Bridge.RootStructR2DegenClass
public import CFSG.Timmesfeld.Bridge.RootStructR2DegenBasic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity RootClosure

namespace RootDegen

namespace DegenConf

variable {G : Type} [Group G] {D : Set G} {a b x : G} (C : DegenConf D a b x)
include C

theorem conj_mem_L {g : G} (hg : g ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)
    (hgb : g * b * g⁻¹ ∈ rootGroup D b ⊔ rootGroup D a) {s : G} (hs : s ∈ D)
    (hsL : s ∈ rootGroup D b ⊔ rootGroup D a) : g * s * g⁻¹ ∈ rootGroup D b ⊔ rootGroup D a :=
  C.mem_line_of_commute (conj_mem_classIn (C.mem_classIn_of_mem_L hs hsL) hg)
    (C.conj_mem g C.hb) hgb ((C.commute_of_mem_L hsL C.b_mem_L).conj g)

theorem exists_conj_eq {t : G} (ht : t ∈ D) (htL : t ∈ rootGroup D b ⊔ rootGroup D a) :
    ∃ g ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x, g * b * g⁻¹ = t := by
  have h1 := C.mem_classIn_of_mem_L ht htL
  rw [← classIn_eq_of_mem C.b_mem_classIn] at h1
  obtain ⟨g, hg, hgt⟩ := h1
  exact ⟨g, hg, hgt.symm⟩

theorem conj_mem_rootSet {h' : G} (hh' : h' ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)
    (hb' : h' * b * h'⁻¹ ∈ rootSet D b) {t : G} (ht : t ∈ D)
    (htL : t ∈ rootGroup D b ⊔ rootGroup D a) : h' * t * h'⁻¹ ∈ rootSet D t := by
  have := C.finite
  have hD := C.root
  obtain ⟨g, hg, hgt⟩ := C.exists_conj_eq ht htL
  have hb'L : h' * b * h'⁻¹ ∈ rootGroup D b ⊔ rootGroup D a :=
    Subgroup.mem_sup_left (rootSet_subset_rootGroup D b hb')
  have hgL : g * b * g⁻¹ ∈ rootGroup D b ⊔ rootGroup D a := hgt ▸ htL
  have hbX : b ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x := le_X C.b_mem_L
  have hsL : g * (h' * b * h'⁻¹) * g⁻¹ ∈ rootGroup D b ⊔ rootGroup D a :=
    C.conj_mem_L hg hgL hb'.1 hb'L
  have hsX : g * (h' * b * h'⁻¹) * g⁻¹ ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x :=
    le_X hsL
  have hk := conj_eq_of_isBender C.isBenderGroup
    (E := subClass (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x)
    (S := {s | (s : G) ∈ D ∧ (s : G) ∈ rootGroup D b ⊔ rootGroup D a})
    (fun g' e he => by
      show ((g' * e * g'⁻¹ : ↥(rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)) : G) ∈
        classIn (rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x) x
      simpa using conj_mem_classIn he g'.2)
    (fun e he f hf hef => C.eq_of_mk_eq he hf hef)
    (fun s hs => C.mem_classIn_of_mem_L hs.1 hs.2)
    (fun s hs => Subtype.ext (by simpa using hD.mul_self_eq_one hs.1))
    (fun s hs s' hs' => Subtype.ext (C.commute_of_mem_L hs.2 hs'.2).eq)
    (s₀ := ⟨b, hbX⟩) ⟨C.hb, C.b_mem_L⟩ (C.not_mem_zStar C.hb)
    (g₁ := ⟨h', hh'⟩) (g₂ := ⟨g, hg⟩)
    (fun s hs => ⟨C.conj_mem h' hs.1, C.conj_mem_L hh' hb'L hs.1 hs.2⟩)
    (fun s hs => ⟨C.conj_mem g hs.1, C.conj_mem_L hg hgL hs.1 hs.2⟩)
    (s := ⟨g * (h' * b * h'⁻¹) * g⁻¹, hsX⟩) ⟨C.conj_mem g hb'.1, hsL⟩
  have hk' := congrArg Subtype.val hk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hk'
  have heq : h' * t * h'⁻¹ = g * (h' * b * h'⁻¹) * g⁻¹ := by
    rw [← hk', ← hgt]
    group
  rw [heq, ← hgt, rootSet_conj C.isClass]
  exact ⟨_, hb', rfl⟩

theorem conj_mem_rootGroup {h' : G} (hh' : h' ∈ rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x)
    (hb' : h' * b * h'⁻¹ ∈ rootSet D b) {t : G} (ht : t ∈ D)
    (htL : t ∈ rootGroup D b ⊔ rootGroup D a) {u : G} (hu : u ∈ rootGroup D t) :
    h' * u * h'⁻¹ ∈ rootGroup D t := by
  rcases (mem_rootGroup_iff_of_rootClosure C.root C.closure ht).1 hu with rfl | huT
  · simp
  · have hAt : rootGroup D t ≤ rootGroup D b ⊔ rootGroup D a :=
      rootGroup_le_sup_of_mem C.hyp C.closure C.special C.hb C.ha C.hba C.hbaD C.haT htL
        (C.root.ne_one ht)
    have huL : u ∈ rootGroup D b ⊔ rootGroup D a := hAt (rootSet_subset_rootGroup D t huT)
    have h1 := C.conj_mem_rootSet hh' hb' huT.1 huL
    rw [rootSet_eq_of_mem huT] at h1
    exact rootSet_subset_rootGroup D t h1

end DegenConf

end RootDegen

end CFSG.Timmesfeld.Bridge
