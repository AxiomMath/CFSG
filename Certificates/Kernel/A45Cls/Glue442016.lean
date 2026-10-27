module

public import Certificates.Data.OmegaOuter
public import Certificates.Kernel.A45Cls.Check442016
public import Certificates.Kernel.A45Cls.Glue218c
public import CFSG.Certificates.Kernel.A45Cls.OuterSound
public import CFSG.GH74.KGroups.PermCheck

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.KC.ConjOrb
  CFSG.Certificates.Kernel.PkCV.B0T Certificates.OmegaB0

local notation "P45" => Equiv.Perm (Fin 45)

theorem o16_cOf_one : cOf (1 : P45) = 1 := ev_injective (by rw [ev_cOf, ev_one])

theorem o16_cOf_prod (L : List P45) : cOf L.prod = (L.map cOf).prod := by
  apply ev_injective
  rw [ev_cOf]
  change L.prod = evHom 45 (L.map cOf).prod
  rw [map_list_prod, List.map_map]
  conv_lhs => rw [← List.map_id L]
  exact congrArg List.prod (List.map_congr_left fun σ _ => (ev_cOf σ).symm)

theorem o16_getD_cOf (B : List P45) (j : Nat) : (B.map cOf).getD j 1 = cOf (B.getD j 1) := by
  rw [← o16_cOf_one, List.getD_map]

theorem o16_phiTable_map (B : List P45) : (phiTable B).toList.map cOf = phiC (B.map cOf) := by
  unfold phiTable phiC
  rw [List.toList_toArray, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, tab_eq, o16_cOf_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  split
  · exact (o16_getD_cOf B j).symm
  · exact o16_cOf_one

theorem o16_phi0_ev (Φ : Array P45) (v : Fin 5 → ZMod 2) :
    phi0 Φ v = ev (phi0C (Φ.toList.map cOf) v) := by
  unfold phi0 phi0C
  rw [← o16_cOf_one, List.getD_map, ev_cOf, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD,
    Array.getElem?_toList]

theorem o16_bElems_ev (Φ : Array P45) (allV : List (Fin 5 → ZMod 2)) :
    bElems Φ allV = (bElemsC (Φ.toList.map cOf) allV).map ev := by
  unfold bElems bElemsC
  rw [List.map_map]
  exact List.map_congr_left fun v _ => o16_phi0_ev Φ v

theorem b0Elems_eq : Certificates.OmegaOuter.b0Elems () = blC.map ev := by
  rw [Certificates.OmegaOuter.b0Elems, o16_bElems_ev, o16_phiTable_map, blC.eq_1, phC.eq_1]

theorem K16_eq : Outer442016.K16.B = blC.map Subtype.val := by
  have h := kB16
  rwa [beq_iff_eq] at h

theorem prep_ev16 (c : CV 45) : PRep 45 6 c.1 (ev c) := by
  intro x
  rw [ev_apply c x]
  change pg 6 (mask 6) c.1 x = pg (wC 45) (mask (wC 45)) c.1 x
  rw [wC45]

theorem wit_of {a : P45} {P : ℕ} (hP : PRep 45 6 P a)
    (hw : nrmInvL P Outer442016.K16.B = true → witL P Outer442016.K16.B = true)
    (hn : ∀ x ∈ Certificates.OmegaOuter.b0Elems (), a * x * a⁻¹ ∈ Certificates.OmegaOuter.b0Elems ()) :
    ∃ β ∈ Certificates.OmegaOuter.b0Elems (), a * β = β * a ∧
      Certificates.OmegaInv.fixCnt (a * β) = 15 := by
  have hnrm : nrmInvL P Outer442016.K16.B = true := by
    unfold nrmInvL
    refine allL_of fun b hb => ?_
    rw [K16_eq] at hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    have hx : ev c ∈ Certificates.OmegaOuter.b0Elems () := by
      rw [b0Elems_eq]
      exact List.mem_map_of_mem hc
    have hy := hn _ hx
    rw [b0Elems_eq] at hy
    obtain ⟨d, hd, e⟩ := List.mem_map.1 hy
    refine anyL_of (x := d.1) ?_ (by rw [K16_eq]; exact List.mem_map_of_mem hd)
    refine eq22_of_eq hP (prep_ev16 c) (prep_ev16 d) hP ?_
    rw [e]
    group
  obtain ⟨β, hβ, hf⟩ := anyL_spec (hw hnrm)
  rw [K16_eq] at hβ
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hβ
  cases he : eq22 45 6 (mask 6) P c.1 c.1 P
  · rw [he] at hf
    exact absurd hf Bool.false_ne_true
  · rw [he] at hf
    refine ⟨ev c, by rw [b0Elems_eq]; exact List.mem_map_of_mem hc,
      comm_of_eq22 hP (prep_ev16 c) he, ?_⟩
    have h := fixK_eq (prep_pcomp hn45 hP (prep_ev16 c))
    rw [Nat.eq_of_beq_eq_true hf] at h
    exact h.symm

theorem mem_cls {N r : ℕ} {G GI T E D S : ℕ → ℕ} {t : P45}
    (hh : headK 45 6 3 G GI = true) (hg : ∀ k < 3, PRep 45 6 (G k) (gA' k))
    (hcl : ∀ i < N, closPt 45 6 3 N G GI T E i = true)
    (htr : ∀ i < N, treePt 3 N r E D i = true) (hr : r < N) (ht : PRep 45 6 (T r) t)
    (hK : distinctK N (fun i => pkeyK 45 6 ps (T i)) S = true) {g : P45} (hgA : g ∈ A) :
    ∃ i < N, PRep 45 6 (T i) (g * t * g⁻¹) := by
  obtain ⟨c, hc, -, hcl', -⟩ := conjOrb_reps (g := gA') (t := t) hn45 hh hg hcl htr hr ht
    ps_lt hK
  have hcr : c r = t := prep_eq (hc r hr) ht
  rw [← closure_gA] at hgA
  obtain ⟨i, hi, e⟩ := conj_closed_A (O := {y | ∃ i < N, c i = y}) (by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hcl' i hi k hk
      exact ⟨j, hj, e.symm⟩) g hgA t ⟨r, hr, hcr⟩
  refine ⟨i, hi, ?_⟩
  rw [← e]
  exact hc i hi

theorem mem_cls36 {g : P45} (hg : g ∈ A) :
    ∃ i < 36, PRep 45 6 (K36.T i) (g * Certificates.P43Twin.t36 () * g⁻¹) := by
  obtain ⟨-, -, -, -, -, -, h0, h1, h2, -, -, -, -, -, bt, -⟩ := binds
  obtain ⟨i, hi, hp⟩ := mem_cls K36.h (prep_gens h0 h1 h2) K36.cl K36.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K36.k hg
  exact ⟨i, by have e := orders.2.2.1; omega, hp⟩

theorem mem_cls540 {g : P45} (hg : g ∈ A) :
    ∃ i < 540, PRep 45 6 (K540.T i) (g * Certificates.P43Twin.t540 () * g⁻¹) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h0, h1, h2, -, -, -, bt⟩ := binds
  obtain ⟨i, hi, hp⟩ := mem_cls K540.h (prep_gens h0 h1 h2) K540.cl K540.tr0 (by decide)
    (by rw [← bt]; exact prep_cOf _) K540.k hg
  exact ⟨i, by have e := orders.2.2.2.1; omega, hp⟩

theorem tA_mem_P :
    Certificates.P43Twin.tA () ∈ QP45.originalSubgroup := by
  rw [mem_iff_sift QP45 QP45_ok, eq_ev_cOf (Certificates.P43Twin.tA ()), sift_ev]
  exact kTA

theorem tB_mem_P :
    Certificates.P43Twin.tB () ∈ QP45.originalSubgroup := by
  rw [mem_iff_sift QP45 QP45_ok, eq_ev_cOf (Certificates.P43Twin.tB ()), sift_ev]
  exact kTB

theorem outer_wit {a : P45} (haA : a ∈ A) (h2 : a * a = 1)
    (hP : a ∉ QP45.originalSubgroup)
    (hN : ∀ x ∈ Certificates.OmegaOuter.b0Elems (), a * x * a⁻¹ ∈ Certificates.OmegaOuter.b0Elems ()) :
    ∃ β ∈ Certificates.OmegaOuter.b0Elems (), a * β = β * a ∧
      Certificates.OmegaInv.fixCnt (a * β) = 15 := by
  have h1 : a ≠ 1 := by
    rintro rfl
    exact hP (one_mem _)
  obtain ⟨t, ht, g, hg, rfl⟩ := inCls_of_inv haA h2 h1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact absurd (conj_mem_P hg tA_mem_P) hP
  · exact absurd (conj_mem_P hg tB_mem_P) hP
  · obtain ⟨i, hi, hp⟩ := mem_cls36 hg
    exact wit_of hp (outL_spec kOut36 hi) hN
  · obtain ⟨i, hi, hp⟩ := mem_cls540 hg
    exact wit_of hp (outL_spec kOut540 hi) hN

theorem check442016 : Certificates.OmegaOuter.check () = true := by
  unfold Certificates.OmegaOuter.check Certificates.OmegaOuter.outerChk
  rw [List.all_eq_true]
  intro a ha
  have haA : a ∈ A := (mem_elemsT QA45 QA45_ok a).1 ha
  by_cases h2 : a * a = 1
  · by_cases hP : a ∈ elemsT QP45
    · simp [hP]
    · have hP' : a ∉ QP45.originalSubgroup := fun h => hP ((mem_elemsT QP45 QP45_ok a).2 h)
      by_cases hN : ∀ x ∈ Certificates.OmegaOuter.b0Elems (),
          a * x * a⁻¹ ∈ Certificates.OmegaOuter.b0Elems ()
      · obtain ⟨β, hβ, hc, hf⟩ := outer_wit haA h2 hP' hN
        have hany : (Certificates.OmegaOuter.b0Elems ()).any (fun β => decide (a * β = β * a) &&
            decide (Certificates.OmegaInv.fixCnt (a * β) = 15)) = true :=
          List.any_eq_true.2 ⟨β, hβ, by
            rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
            exact ⟨hc, hf⟩⟩
        simp [hany]
      · have hall : ((Certificates.OmegaOuter.b0Elems ()).all fun x =>
            decide (a * x * a⁻¹ ∈ Certificates.OmegaOuter.b0Elems ())) = false := by
          rw [Bool.eq_false_iff]
          intro h
          exact hN fun x hx => of_decide_eq_true (List.all_eq_true.1 h x hx)
        simp [hall]
  · simp [h2]

end CertificateChecks.KernelA45

end
