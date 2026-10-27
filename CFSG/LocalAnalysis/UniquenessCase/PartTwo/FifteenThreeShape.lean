module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeShapeT1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeShapeT2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeShapeT3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Shape

variable {D : Data G} {V₀ V L : Subgroup G}

private theorem s15_Three_dirProd_transfer (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))}
    (hdir : IsDirectProdOfConj (s15AW h) B (s15NW h)) :
    IsDirectProdOfConj (lBar V₀ V h.isElemAbelian L)
      (barSub V₀ V h.isElemAbelian (s15K0 h B))
      (s15NBar D V₀ V h.isElemAbelian L) := by
  refine isDirectProdOfConj_of_mulEquiv (s15AWEquiv h1217 h hL)
    (barSub_mono V₀ V h.isElemAbelian (s15_Three_K0_le h B))
    (fun y => s15_Three_mem_barSub_K0_iff h1217 h hL B y) ?_ ?_ hdir
  · intro n hn
    rw [s15_Three_nBar_range h] at hn
    obtain ⟨g, rfl⟩ := hn
    exact ⟨s15Phi h g, by rw [s15_Three_NW_eq h]; exact ⟨g, rfl⟩,
      fun x => ⟨s15_Three_psi_conj_mem h g x.2, s15_Three_AWEquiv_conj h1217 h hL g x⟩⟩
  · intro n' hn'
    rw [s15_Three_NW_eq h] at hn'
    obtain ⟨g, rfl⟩ := hn'
    exact ⟨s15Psi h g, by rw [s15_Three_nBar_range h]; exact ⟨g, rfl⟩,
      fun x => ⟨s15_Three_psi_conj_mem h g x.2, s15_Three_AWEquiv_conj h1217 h hL g x⟩⟩

private theorem s15_Three_wStarConj_eq (h : Hyp151 D V₀ V L) :
    wStarConj D.M V₀ V h.isElemAbelian L =
      {Z | ∃ e ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        Z = (wStar D.M V₀ V h.isElemAbelian L).map e.toMonoidHom} := by
  have hV := h.isElemAbelian
  ext Z
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hms := s15_Three_M_le_stabTil_star h hm
    exact ⟨(actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹,
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV).inv_mem (actTil_mem_barSub _ V hV hm hms),
      s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV hms⟩
  · rintro ⟨e, he, rfl⟩
    exact s15_Infra_map_wStar_mem_wStarConj h.hyp125 hV he

private theorem s15_Three_commSub_star (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h) :
    commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B)) =
      (commSub ⊤ B).map (wStar D.M V₀ V h.isElemAbelian L).subtype := by
  have hV := h.isElemAbelian
  obtain ⟨hind, htop⟩ := fifteen_two_directSum D h1217 h hV hL
  rw [s15_Three_wStarConj_eq h] at hind htop
  have hKM : barSub (v1Sub D.M V₀ V hV L) V hV (s15K0 h B) ≤
      Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    barSub_mono _ V hV ((s15_Three_K0_le h B).trans h.le)
  have hKL : barSub (v1Sub D.M V₀ V hV L) V hV (s15K0 h B) ≤ lStar D.M V₀ V hV L :=
    barSub_mono _ V hV (s15_Three_K0_le h B)
  have hstab : barSub (v1Sub D.M V₀ V hV L) V hV (s15K0 h B) ≤
      stabSub (wStar D.M V₀ V hV L) := by
    intro k hk
    obtain ⟨g, hgK, rfl⟩ := (mem_barSub _ _ _ _ _).1 hk
    obtain ⟨hgn, -, -⟩ := (s15_Three_mem_K0 h B).1 hgK
    exact s15PsiStar_mem_stabSub h ⟨(g : G), hgn⟩
  have hAut : autSub (barSub (v1Sub D.M V₀ V hV L) V hV (s15K0 h B)) (wStar D.M V₀ V hV L) =
      B := by
    ext φ
    rw [mem_autSub]
    constructor
    · rintro ⟨s, hsK, rfl⟩
      obtain ⟨g, hgK, hgs⟩ := (mem_barSub _ _ _ _ _).1 hsK
      obtain ⟨hgn, -, hgB⟩ := (s15_Three_mem_K0 h B).1 hgK
      have hres : resHom (wStar D.M V₀ V hV L) s = s15Phi h ⟨(g : G), hgn⟩ := by
        change resHom _ s = resHom _ ((s15PsiStar h).codRestrict _ (s15PsiStar_mem_stabSub h)
          ⟨(g : G), hgn⟩)
        congr 1
        exact Subtype.ext hgs.symm
      rw [hres]
      exact hgB
    · intro hφ
      have hφA : φ ∈ s15AW h := hBA hφ
      rw [s15_Three_AW_eq] at hφA
      obtain ⟨l, hlL, rfl⟩ := Subgroup.mem_map.1 hφA
      have hlK : (l : G) ∈ s15K0 h B := (s15_Three_mem_K0 h B).2 ⟨l.2, hlL, hφ⟩
      exact ⟨⟨s15PsiStar h l, s15PsiStar_mem_stabSub h l⟩,
        actTil_mem_barSub _ V hV hlK
          (s15_Three_M_le_stabTil_star h (s15_Three_nBar_le_M h l.2)), rfl⟩
  have hWmem : wStar D.M V₀ V hV L ∈
      {Z | ∃ e ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV,
        Z = (wStar D.M V₀ V hV L).map e.toMonoidHom} :=
    ⟨1, (Mbar D.M (v1Sub D.M V₀ V hV L) V hV).one_mem, by ext x; simp [Subgroup.mem_map]⟩
  calc commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV (s15K0 h B))
      = (commSub ⊤ (autSub (barSub (v1Sub D.M V₀ V hV L) V hV (s15K0 h B))
          (wStar D.M V₀ V hV L))).map (wStar D.M V₀ V hV L).subtype :=
        commSub_top_eq_map_autSub hind htop hWmem hstab
          (by
            rintro k hk _ ⟨e, he, rfl⟩
            refine ⟨k * e, (Mbar D.M (v1Sub D.M V₀ V hV L) V hV).mul_mem (hKM hk) he, ?_⟩
            rw [Subgroup.map_map]
            rfl)
          (by
            intro k hk v
            have h1 : k v * v⁻¹ ∈ commSub ⊤ (lStar D.M V₀ V hV L) :=
              Subgroup.subset_closure ⟨k, hKL hk, v, Subgroup.mem_top v, rfl⟩
            rwa [s15_Three_commSub_top_lStar h hV] at h1)
    _ = (commSub ⊤ B).map (wStar D.M V₀ V hV L).subtype := by rw [hAut]

private theorem s15_Three_family_eq (h : Hyp151 D V₀ V L) (K₀ : Subgroup G) :
    {Z : Subgroup (vStar D.M V₀ V h.isElemAbelian L) | ∃ m ∈ D.M,
      Z = commSub (⊤ : Subgroup (vStar D.M V₀ V h.isElemAbelian L))
        (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (conjSubgroup K₀ m))} =
    {Y : Subgroup (vStar D.M V₀ V h.isElemAbelian L) |
      ∃ e ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        Y = (commSub (⊤ : Subgroup (vStar D.M V₀ V h.isElemAbelian L))
          (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian K₀)).map
            e.toMonoidHom} := by
  have hV := h.isElemAbelian
  ext Y
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hms := s15_Three_M_le_stabTil_star h hm
    refine ⟨(actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹,
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV).inv_mem (actTil_mem_barSub _ V hV hm hms), ?_⟩
    rw [s15_Infra_barSub_conjSubgroup _ V hV hms K₀]
    exact s15_Infra_commSub_top_map_conj _ _
  · rintro ⟨e, he, rfl⟩
    obtain ⟨g, hgM, rfl⟩ := (mem_barSub _ _ _ _ _).1 he
    have hms := s15_Three_M_le_stabTil_star h (D.M.inv_mem hgM)
    refine ⟨(g : G)⁻¹, D.M.inv_mem hgM, ?_⟩
    rw [s15_Infra_barSub_conjSubgroup _ V hV hms K₀, s15_Infra_commSub_top_map_conj]
    have hα : (actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G)⁻¹, hms⟩)⁻¹ =
        actTil (v1Sub D.M V₀ V hV L) V hV g := by
      rw [show (⟨(g : G)⁻¹, hms⟩ : stabTil (v1Sub D.M V₀ V hV L) V) = g⁻¹ from rfl, map_inv,
        inv_inv]
    rw [hα]

private theorem s15_Three_family_eq_W (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) :
    {Z : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L) | ∃ n ∈ s15NW h,
      Z = commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L))
        (B.map (MulAut.conj n).toMonoidHom)} =
    {Y : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L) | ∃ n ∈ s15NW h,
      Y = (commSub ⊤ B).map n.toMonoidHom} := by
  ext Z
  simp only [Set.mem_setOf_eq, s15_Infra_commSub_top_map_conj]

private theorem s15_Three_indep_transfer (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h)
    (hind : sSupIndep {Z : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L) |
      ∃ n ∈ s15NW h, Z = commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L))
        (B.map (MulAut.conj n).toMonoidHom)}) :
    sSupIndep {Z : Subgroup (vStar D.M V₀ V h.isElemAbelian L) | ∃ m ∈ D.M,
      Z = commSub (⊤ : Subgroup (vStar D.M V₀ V h.isElemAbelian L))
        (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
          (conjSubgroup (s15K0 h B) m))} := by
  rw [s15_Three_family_eq h, s15_Three_commSub_star h1217 h hL hBA]
  rw [s15_Three_family_eq_W h B] at hind
  refine sSupIndep_orbit_of_autSub _ _ _ ?_ hind
  rw [← s15_Three_wStarConj_eq h]
  exact (fifteen_two_directSum D h1217 h h.isElemAbelian hL).1

private theorem s15_Three_sup_transfer (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h)
    (hsup : sSup {Z : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L) |
      ∃ n ∈ s15NW h, Z = commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L))
        (B.map (MulAut.conj n).toMonoidHom)} = ⊤) :
    sSup {Z : Subgroup (vStar D.M V₀ V h.isElemAbelian L) | ∃ m ∈ D.M,
      Z = commSub (⊤ : Subgroup (vStar D.M V₀ V h.isElemAbelian L))
        (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
          (conjSubgroup (s15K0 h B) m))} = ⊤ := by
  rw [s15_Three_family_eq h, s15_Three_commSub_star h1217 h hL hBA]
  rw [s15_Three_family_eq_W h B] at hsup
  refine sSup_orbit_of_autSub _ _ _ ?_ hsup
  rw [← s15_Three_wStarConj_eq h]
  exact (fifteen_two_directSum D h1217 h h.isElemAbelian hL).2

theorem s15_Three_shape (hMcL : RMcLaughlin) (hDer : RJPrime153) (hNorm : RNormNat153)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hsemi : s15Semisimple (s15AW h))
    (htrans : ∀ I I' : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L),
      IsIrrOn (s15AW h) I ⊥ → IsIrrOn (s15AW h) I' ⊥ →
        ∃ n ∈ s15NW h, s15SecIso (s15AW h) (I.map (n : MulAut _).toMonoidHom) ⊥ I' ⊥)
    (htr : ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L)) :
    ∃ K₀ : Subgroup G, s15Shape D V₀ V h.isElemAbelian L K₀ := by
  obtain ⟨t, htN, ht⟩ := s15_Three_exists_transvection h htr
  obtain ⟨B, hB, hBA, hdir, hnat, hind, hsup⟩ :=
    s15_Three_abstract_AW hMcL hDer hNorm h1217 h hL hsemi htrans htN ht
  refine ⟨s15K0 h B, s15_Three_K0_le h B, s15_Three_kbar_le_comm h1217 h hL htN hB,
    s15_Three_dirProd_transfer h1217 h hL hdir, s15_Four_natural h1217 h hL hBA hnat,
    s15_Three_indep_transfer h1217 h hL hBA hind, s15_Three_sup_transfer h1217 h hL hBA hsup⟩

end Shape

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
