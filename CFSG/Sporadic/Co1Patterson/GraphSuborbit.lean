module

public import CFSG.Sporadic.Co1Patterson.GraphOrbits
public import CFSG.Sporadic.Co1Patterson.GraphNative
public import CFSG.Sporadic.Co1Patterson.GraphTree

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

theorem nrep_aNC :
    NRep iotaARows aNC := by
  refine nrep_of_mrep ?_
  rw [nativeEmb_aNC]
  exact rep_iotaA

abbrev repJ (i : ℕ) : ℕ := repIdx.getD i 0

theorem repJ_mem {i : ℕ} (hi : i < 10) : 1 ≤ repJ i ∧ repJ i ≤ 190 := by
  interval_cases i <;> decide

@[expose] noncomputable def repElt (i : ℕ) : NativeSporadic.Co1 :=
  gElt (repJ i) * aNC * (gElt (repJ i))⁻¹

theorem isConj_repElt (i : ℕ) : IsConj aNC (repElt i) := isConj_iff.2 ⟨gElt (repJ i), rfl⟩

@[expose] noncomputable def repV (i : ℕ) : Vt := ⟨repElt i, isConj_repElt i⟩

theorem repV_eq_smul (i : ℕ) : repV i = gElt (repJ i) • vA := rfl

theorem nrep_conjA {x xi : Native.Rows} {g : NativeSporadic.Co1} (hx : NRep x g)
    (hxi : NRep xi g⁻¹) :
    NRep (conjA x xi) (g * aNC * g⁻¹) :=
  (hx.mul nrep_aNC).mul hxi

theorem nrep_repRows (hdag : dagOK = true) {i : ℕ} (hi : i < 10) :
    NRep (repRows i) (repElt i) :=
  nrep_conjA (nrep_gEl (dagOK_parts hdag).1 _)
    (nrep_gElInv hdag (repJ_mem hi).1 (repJ_mem hi).2)

theorem nrep_repX (hdag : dagOK = true) (i : ℕ) : NRep (repX i) (gElt (repJ i)) :=
  nrep_gEl (dagOK_parts hdag).1 _

theorem nrep_repXi (hdag : dagOK = true) {i : ℕ} (hi : i < 10) :
    NRep (repXi i) (gElt (repJ i))⁻¹ :=
  nrep_gElInv hdag (repJ_mem hi).1 (repJ_mem hi).2

theorem le_ncard_of_orbOK {G Gi : Array Native.Rows} {root : Native.Rows} {o : Orb}
    (h : orbOK G Gi root o = true) (S : Subgroup NativeSporadic.Co1) (k : ℕ → NativeSporadic.Co1)
    (hk : ∀ l < G.size, NRep G[l]! (k l)) (hkS : ∀ l < G.size, k l ∈ S) (b : Vt)
    (hb : NRep root b) :
    o.c.pts.size ≤ {v : Vt | ∃ g ∈ S, v = g • b}.ncard := by
  have hsound := orbOK_sound matHom h k hk b hb
  choose! g hg hgh hghi hgp using hsound
  have hcl : ∀ i < o.c.pts.size, g i ∈ S := fun i hi =>
    (Subgroup.closure_le S).2 (by rintro _ ⟨l, hl, rfl⟩; exact hkS l hl) (hg i hi)
  let f : ℕ → Vt := fun i => g i • b
  have hinj : Set.InjOn f (Set.Iio o.c.pts.size) := by
    intro i hi j hj hij
    refine orbOK_injective h hi hj ?_
    rw [← hgp i hi, ← hgp j hj]
    have h1 := congrArg Subtype.val hij
    simp only [f, coe_smul_conjVert] at h1
    rw [h1]
  have himg : f '' Set.Iio o.c.pts.size ⊆ {v : Vt | ∃ g ∈ S, v = g • b} := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨g i, hcl i hi, rfl⟩
  calc o.c.pts.size = (f '' Set.Iio o.c.pts.size).ncard := by
        rw [Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat]
    _ ≤ _ := Set.ncard_le_ncard himg (Set.toFinite _)

theorem brayNC_mem (l : ℕ) (hl : l < brayArr.size) :
    brayNC l ∈ centralizer ({aNC} : Set NativeSporadic.Co1) := by
  rw [← closure_brayNC]
  exact Subgroup.subset_closure ⟨l, by rw [brayArr_size] at hl; exact hl, rfl⟩

theorem closure_brayArr :
    Subgroup.closure (brayNC '' {l | l < brayArr.size}) =
      centralizer ({aNC} : Set NativeSporadic.Co1) := by
  rw [brayArr_size]
  exact closure_brayNC

theorem mem_cOrb_iff_of_exactOK {o : Orb} {root : Native.Rows} {n : ℕ} (h : exactOK o root n = true)
    (b : Vt) (hb : NRep root b) (v : Vt) :
    v ∈ cOrb b ↔ ∃ i < o.c.pts.size, NRep o.c.pts[i]! v := by
  unfold exactOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hok, hcl⟩, -⟩ := h
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← closure_brayArr] at hg
    obtain ⟨i, hi, hp⟩ := orbClosed_sound matHom hok hcl brayNC (fun l hl => nrep_brayArr l hl)
      b hb g hg
    exact ⟨i, hi, hp⟩
  · rintro ⟨i, hi, hv⟩
    obtain ⟨g, hg, -, -, hp⟩ := orbOK_sound matHom hok brayNC (fun l hl => nrep_brayArr l hl) b
      hb i hi
    rw [closure_brayArr] at hg
    refine ⟨g, hg, Subtype.ext (NRep.unique hv hp)⟩

theorem ncard_cOrb_of_exactOK {o : Orb} {root : Native.Rows} {n : ℕ} (h : exactOK o root n = true)
    (b : Vt) (hb : NRep root b) : (cOrb b).ncard = n := by
  have h' := h
  unfold exactOK at h'
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨hok, -⟩, hn⟩ := h'
  have hsound := orbOK_sound matHom hok brayNC (fun l hl => nrep_brayArr l hl) b hb
  choose! g hg _ _ hgp using hsound
  let f : ℕ → Vt := fun i => g i • b
  have hinj : Set.InjOn f (Set.Iio o.c.pts.size) := by
    intro i hi j hj hij
    refine orbOK_injective hok hi hj ?_
    rw [← hgp i hi, ← hgp j hj]
    have h1 := congrArg Subtype.val hij
    simp only [f, coe_smul_conjVert] at h1
    rw [h1]
  have himg : f '' Set.Iio o.c.pts.size = cOrb b := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨g i, closure_brayArr ▸ hg i hi, rfl⟩
    · intro hv
      obtain ⟨i, hi, hiv⟩ := (mem_cOrb_iff_of_exactOK h b hb v).1 hv
      exact ⟨i, hi, Subtype.ext (NRep.unique (hgp i hi) hiv)⟩
  rw [← himg, Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat, hn]

end CFSG.Sporadic.Co1Patterson
