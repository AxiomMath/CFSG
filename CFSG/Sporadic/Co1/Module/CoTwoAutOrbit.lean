module

public import CFSG.Sporadic.Co1.Module.CoTwoPerfect
public import CFSG.Sporadic.Co1.Module.OddNative
public import CFSG.Monster.GMS.Leech.Linear
public import Certificates.Data.CFSGNative.Co1.CoTwoAutData
public import Certificates.Data.CFSGNative.Co1.CoTwoAutOrbit
public import CFSG.Sporadic.Co1.Module.CoTwoAutLit
public import Certificates.Certificate10066
public meta import CFSG.Sporadic.Co1.Module.CoTwoData
public meta import CFSG.Sporadic.Co1.Module.Orbits
public meta import CFSG.Sporadic.Co1.Module.Forms
public meta import Certificates.Data.CFSGNative.Co1.CoTwoAutData
public meta import Certificates.Data.CFSGNative.Co1.CoTwoAutOrbit
public import CFSG.Sporadic.Co1.Module.CoTwoData
public import CFSG.Sporadic.Co1.Module.OddFacts
public meta import Certificates.Certificate10067
public meta import Certificates.Kernel.Co1B.Tri2045
public import Certificates.Kernel.Co1B.Tri2045

public section

namespace CFSG.Sporadic.Co1.Module.CoTwoAut

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.CoTwoNative CFSG.Sporadic.Co1.CoTwoAutNative
  CFSG.Sporadic.Co1.Module.CoTwo Matrix

theorem ncard_orbitSet_gt
    {w : Vec24} (hP : bil₀ w v₂ = 0) (h0 : w ≠ 0) (h2 : w ≠ v₂)
    (hw : w ∉ CFSG.Monster.GMS.co1Orbit 0) (hw' : v₂ + w ∉ CFSG.Monster.GMS.co1Orbit 0) :
    46575 < (orbitSet co1Act kc w).ncard :=
  ncard_orbitSet_gt_lit Certificates.certificate10066 hP h0 h2 hw hw'

open CFSG.Monster.GMS (co1Orbit)

theorem co1Act_add (g : NativeSporadic.Co1) (a b : Vec24) :
    co1Act g (a + b) = co1Act g a + co1Act g b := Matrix.mulVec_add _ _ _

theorem orbitSet_cls
    {j : ℕ} (hj : j < 4) {y : Vec24} (hy : y ∈ Pairs.cls j) :
    orbitSet co1Act kc y = Pairs.cls j := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact Pairs.cls_smul_mem (g := g) (show g • v₂ = v₂ from mem_kc_iff.1 hg) hy
  · intro hz
    obtain ⟨g, hg1, hg2⟩ := Pairs.cls_trans hj hy hz
    exact ⟨g, mem_kc_iff.2 hg1, hg2⟩

theorem ncard_orbitSet_cls_three
    {y : Vec24} (hy : y ∈ Pairs.cls 3) :
    (orbitSet co1Act kc y).ncard = 4600 := by
  rw [orbitSet_cls (by norm_num) hy, Pairs.cls_ncard (by norm_num)]
  decide

@[expose] def Tadj : Set Vec24 := {u | u ∈ Pairs.cls 1 ∨ v₂ + u ∈ Pairs.cls 1}

theorem ncard_orbitSet_Tadj
    {u : Vec24} (hu : u ∈ Tadj) :
    (orbitSet co1Act kc u).ncard = 46575 := by
  rcases hu with hu | hu
  · rw [orbitSet_cls (by norm_num) hu, Pairs.cls_ncard (by norm_num)]
    decide
  · have himg : orbitSet co1Act kc u = (fun z => v₂ + z) '' Pairs.cls 1 := by
      ext z
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hgv : co1Act g v₂ = v₂ := mem_kc_iff.1 hg
        refine ⟨co1Act g (v₂ + u), Pairs.cls_smul_mem (g := g) (show g • v₂ = v₂ from hgv) hu, ?_⟩
        show v₂ + co1Act g (v₂ + u) = co1Act g u
        rw [co1Act_add, hgv, ← add_assoc, vec_add_self, zero_add]
      · rintro ⟨z', hz', rfl⟩
        obtain ⟨g, hg1, hg2⟩ := Pairs.cls_trans (j := 1) (by norm_num) hu hz'
        refine ⟨g, mem_kc_iff.2 hg1, ?_⟩
        have hu' : u = v₂ + (v₂ + u) := by rw [← add_assoc, vec_add_self, zero_add]
        have h1 : co1Act g (v₂ + u) = z' := hg2
        have h2 : co1Act g v₂ = v₂ := hg1
        show co1Act g u = v₂ + z'
        conv_lhs => rw [hu']
        rw [co1Act_add, h1, h2]
    rw [himg, Set.ncard_image_of_injective _ (add_right_injective v₂),
      Pairs.cls_ncard (by norm_num)]
    decide

theorem ncard_orbitSet_zero : (orbitSet co1Act kc 0).ncard = 1 := by
  have : orbitSet co1Act kc 0 = {0} := by
    ext z
    constructor
    · rintro ⟨g, -, rfl⟩
      exact Matrix.mulVec_zero _
    · rintro (rfl)
      exact ⟨1, kc.one_mem, Matrix.mulVec_zero _⟩
  rw [this, Set.ncard_singleton]

theorem ncard_orbitSet_v₂ : (orbitSet co1Act kc v₂).ncard = 1 := by
  have : orbitSet co1Act kc v₂ = {v₂} := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact mem_kc_iff.1 hg
    · rintro (rfl)
      exact ⟨1, kc.one_mem, Odd.co1Act_one' _⟩
  rw [this, Set.ncard_singleton]

theorem perp_type2
    {y : Vec24} (hy : y ∈ co1Orbit 0) (hP : bil₀ y v₂ = 0) :
    y = v₂ ∨ y ∈ Pairs.cls 1 ∨ y ∈ Pairs.cls 3 := by
  by_cases hu : v₂ + y = 0
  · left
    calc y = v₂ + (v₂ + y) := by rw [← add_assoc, vec_add_self, zero_add]
      _ = v₂ := by rw [hu, add_zero]
  · obtain ⟨i, hi, -⟩ := CFSG.Monster.GMS.Leech.existsUnique_co1Orbit hu
    fin_cases i
    · exact Or.inr (Or.inr ⟨hy, hi⟩)
    · exfalso
      have h1 : q₀ (v₂ + y) = 1 := CFSG.Monster.GMS.Leech.q₀_eq_one_of_mem_co1Orbit_one hi
      rw [q₀_add, q₀_v₂, CFSG.Monster.GMS.Leech.q₀_eq_zero_of_mem_co1Orbit_zero hy,
        bil₀_comm, hP] at h1
      exact absurd h1 (by decide)
    · exact Or.inr (Or.inl ⟨hy, hi⟩)

theorem classify_perp
    {w : Vec24} (hP : bil₀ w v₂ = 0) :
    w = 0 ∨ w = v₂ ∨ w ∈ Pairs.cls 3 ∨ w ∈ Tadj ∨ 46575 < (orbitSet co1Act kc w).ncard := by
  by_cases hw : w ∈ co1Orbit 0
  · rcases perp_type2 hw hP with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl h))
  by_cases hw' : v₂ + w ∈ co1Orbit 0
  · have hP' : bil₀ (v₂ + w) v₂ = 0 := by
      rw [CFSG.Monster.GMS.Leech.bil₀_add_left, bil₀_self, hP, add_zero]
    rcases perp_type2 hw' hP' with h | h | h
    · left
      calc w = v₂ + (v₂ + w) := by rw [← add_assoc, vec_add_self, zero_add]
        _ = 0 := by rw [h, vec_add_self]
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr h))))
    · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
      · have := h.2
        rwa [show v₂ + (v₂ + w) = w by rw [← add_assoc, vec_add_self, zero_add]] at this
      · exact h.1
  by_cases h0 : w = 0
  · exact Or.inl h0
  by_cases h2 : w = v₂
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr (Or.inr (Or.inr (ncard_orbitSet_gt hP h0 h2 hw hw'))))

end CFSG.Sporadic.Co1.Module.CoTwoAut
