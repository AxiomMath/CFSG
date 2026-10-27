module

public import CFSG.Timmesfeld.Moufang.LinePres
public import CFSG.Timmesfeld.Moufang.A6Check
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixGenerators

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration Equiv

namespace A6

abbrev Pres : Type := PresentedGroup (wordRels (lineRels 2 false))

theorem card_pres_le : Finite Pres ∧ Nat.card Pres ≤ 1080 := by
  have h := card_le_of_facts_presented (rels := wordRels (lineRels 2 false)) (N := 1080)
    (F := 4320) (fx := A6Data.fx) (fc := A6Data.fc) (fy := A6Data.fy) (kind := A6Data.kind)
    (wi := A6Data.wi) (fs := A6Data.fs) (ft := A6Data.ft) (fo := A6Data.fo)
    (refs := A6Data.refs) (pl := A6Data.pl) (ffi := A6Data.ffi) (live := A6Data.live)
    (lineRels 2 false) A6Data.words (fun w hw => ⟨w, hw, rfl⟩)
    (by decide +kernel) A6Data.live_zero (by norm_num) A6Data.facts_all A6Data.cover_all
  rw [A6Data.liveCount_eq] at h
  exact h

@[expose] def permD : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def permC : Perm (Fin 6) := swap 1 2 * swap 3 4

@[expose] def permX0 : Perm (Fin 6) := swap 0 1 * swap 4 5

@[expose] def permX1 : Perm (Fin 6) := swap 0 3 * swap 1 2

@[expose] def altD : alternatingGroup (Fin 6) := ⟨permD, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def altC : alternatingGroup (Fin 6) := ⟨permC, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def altX : Fin 2 → alternatingGroup (Fin 6) :=
  ![⟨permX0, Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨permX1, Perm.mem_alternatingGroup.mpr (by decide)⟩]

theorem lineConfig_alt : LineConfig altD altC altX where
  d_sq := by decide +kernel
  c_sq := by decide +kernel
  x_sq := by decide +kernel
  dc_pow := by decide +kernel
  d_comm := by unfold Commute SemiconjBy; decide +kernel
  sq_eq := by decide +kernel
  cx_pow := by decide +kernel
  cdx_pow := by decide +kernel

noncomputable def toAlt : Pres →* alternatingGroup (Fin 6) :=
  wordsHom (lineRels 2 false) (lineGens altD altC altX)
    (lineConfig_alt.signedProd_lineRels (by simp))

open CFSG.ComponentClassification.CatalogueSchreierAlternating in
theorem toAlt_surjective : Function.Surjective toAlt := by
  rw [← MonoidHom.range_eq_top, toAlt, range_wordsHom, range_lineGens, eq_top_iff,
    ← DegreeSix.generating_pair, Subgroup.closure_le]
  set K := Subgroup.closure (insert altD (insert altC (Set.range altX)))
  have hd : altD ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hc : altC ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hx : ∀ i, altX i ∈ K := fun i =>
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  rintro g (rfl | rfl)
  · have h : DegreeSix.x = altD * altC * altD * altX 1 * altC * altD * altC := by
      decide +kernel
    rw [h]
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem hd hc) hd) (hx 1))
      hc) hd) hc
  · have h : DegreeSix.y = altD * altX 1 * altC * altX 0 := by decide +kernel
    rw [h]
    exact K.mul_mem (K.mul_mem (K.mul_mem hd (hx 1)) hc) (hx 0)

theorem card_ker_toAlt_le : Nat.card toAlt.ker ≤ 3 := by
  have h1 := toAlt.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr toAlt_surjective, Subgroup.card_top,
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.card_alternating_six]
    at h1
  have := card_pres_le.2
  omega

end A6

open A6 in
theorem a6Endgame : A6Endgame := by
  intro H _ d c x hcfg hdc hgen
  refine ⟨hcfg.isConj, fun hZ => ?_⟩
  have hfin := card_pres_le.1
  set φ : Pres →* H := wordsHom (lineRels 2 false) (lineGens d c x)
    (hcfg.signedProd_lineRels (by simp))
  have hφ : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, range_wordsHom, range_lineGens, hgen]
  set N := toAlt.ker.map φ
  have hN : N.Normal := toAlt.normal_ker.map φ hφ
  set g : toAlt.ker → N := fun k => ⟨φ k, Subgroup.mem_map_of_mem φ k.2⟩
  have hg : Function.Surjective g := by
    rintro ⟨y, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hNfin : Finite N := Finite.of_surjective g hg
  have hNcard : Nat.card N ≤ 3 := (Nat.card_le_card_of_surjective g hg).trans card_ker_toAlt_le
  have hNc := le_center_of_card_le_three (hcfg.commutator_eq_top le_rfl hgen) hNcard
  have hle : toAlt.ker ≤ φ.ker := by
    intro k hk
    have h1 := hNc (Subgroup.mem_map_of_mem φ hk)
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  set θ : alternatingGroup (Fin 6) →* H := (QuotientGroup.lift toAlt.ker φ hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective toAlt toAlt_surjective).symm.toMonoidHom
  have hθ : ∀ p, θ (toAlt p) = φ p := by
    intro p
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective toAlt toAlt_surjective).symm (toAlt p) =
        (p : Pres ⧸ toAlt.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [θ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h1,
      QuotientGroup.lift_mk]
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨p, rfl⟩ := hφ y
    exact ⟨toAlt p, hθ p⟩
  have hθi : Function.Injective θ := by
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff θ).mp h
    · exfalso
      apply hdc
      obtain ⟨a, ha⟩ := hθs (d * c)
      rw [← ha]
      exact (MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top a)
  exact ⟨(MulEquiv.ofBijective θ ⟨hθi, hθs⟩).symm⟩

end CFSG.Timmesfeld.Moufang
