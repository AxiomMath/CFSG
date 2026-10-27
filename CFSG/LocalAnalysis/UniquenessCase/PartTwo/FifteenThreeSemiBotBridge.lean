module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotTransv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

private theorem s15_semiBot_commutator_subgroupOf {X : Type*} [Group X] {B P Q : Subgroup X}
    (hP : P ≤ B) (hQ : Q ≤ B) :
    ⁅P.subgroupOf B, Q.subgroupOf B⁆ = (⁅P, Q⁆).subgroupOf B := by
  apply Subgroup.map_injective B.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hP,
    Subgroup.map_subgroupOf_eq_of_le hQ,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hP hQ)]

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_wStar_eq_map (h : Hyp151 D V₀ V L) :
    wStar D.M V₀ V h.isElemAbelian L =
      (wTil V₀ V h.isElemAbelian L).map
        (s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
          (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)) :=
  s15_T7_imgTil_preTil_eq_map V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
    (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L) (wTil V₀ V h.isElemAbelian L)

theorem s15_semiBot_awHom_kappa (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (x : ↥(barSub V₀ V h.isElemAbelian L)) (w : Vtil V₀ V h.isElemAbelian)
    (u : ↥(wStar D.M V₀ V h.isElemAbelian L))
    (hu : (u : vStar D.M V₀ V h.isElemAbelian L) =
      s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L) w) :
    ((s15AWHom h1217 h x : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) u :
        vStar D.M V₀ V h.isElemAbelian L) =
      s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)
        ((x : MulAut (Vtil V₀ V h.isElemAbelian)) w) := by
  obtain ⟨y, rfl⟩ := s15_Three_psiL_surjective h x
  rw [s15AWHom_apply]
  change ((s15Phi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L))) u :
      vStar D.M V₀ V h.isElemAbelian L) =
    s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
      (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)
      ((s15Psi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L))) w)
  have hg₀ : ((y : ↥(nBar D.M V₀ V h.isElemAbelian L)) : G) ∈ stabTil V₀ V :=
    s15_Three_M_le_stabTil h
      (s15_Three_nBar_le_M h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)).2)
  have hg₁ : ((y : ↥(nBar D.M V₀ V h.isElemAbelian L)) : G) ∈
      stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V :=
    s15_Three_M_le_stabTil_star h
      (s15_Three_nBar_le_M h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)).2)
  have hpsi : s15Psi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) =
      actTil V₀ V h.isElemAbelian
        ⟨((y : ↥(nBar D.M V₀ V h.isElemAbelian L)) : G), hg₀⟩ := rfl
  have hpsiStar : s15PsiStar h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) =
      actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        ⟨((y : ↥(nBar D.M V₀ V h.isElemAbelian L)) : G), hg₁⟩ := rfl
  have hstep : (((s15Phi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L))) u :
      ↥(wStar D.M V₀ V h.isElemAbelian L)) : vStar D.M V₀ V h.isElemAbelian L) =
      (s15PsiStar h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)))
        (u : vStar D.M V₀ V h.isElemAbelian L) := rfl
  rw [hstep, hu, hpsiStar, hpsi]
  exact (s15_T7_kappa_act V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
    (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L) hg₀ hg₁ w).symm

theorem s15_semiBot_commSub_top_map_awHom (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {P : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hPL : P ≤ barSub V₀ V h.isElemAbelian L)
    (hP : commSub (wTil V₀ V h.isElemAbelian L) P = wTil V₀ V h.isElemAbelian L) :
    commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L))
      (((P.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
        (s15AW h).subtype) = ⊤ := by
  set AP : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) :=
    ((P.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
      (s15AW h).subtype with hAP
  let gens : Set (Vtil V₀ V h.isElemAbelian) :=
    {c | ∃ x ∈ P, ∃ w ∈ wTil V₀ V h.isElemAbelian L, x w * w⁻¹ = c}
  rw [eq_top_iff]
  intro u _
  have hgen : (s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
      (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)) '' gens ⊆
      (commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)) AP).map
        (wStar D.M V₀ V h.isElemAbelian L).subtype := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, hpP, w, hw, hz⟩ := hz
    rw [← hz]
    let κ : Vtil V₀ V h.isElemAbelian →*
        Vtil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian :=
      s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)
    let a : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L) :=
      (s15AWHom h1217 h ⟨p, hPL hpP⟩ : ↥(s15AW h))
    have haP : a ∈ AP := by
      rw [hAP]
      exact Subgroup.mem_map_of_mem (s15AW h).subtype
        (Subgroup.mem_map_of_mem (s15AWHom h1217 h) (Subgroup.mem_subgroupOf.2 hpP))
    have hkw : κ w ∈ wStar D.M V₀ V h.isElemAbelian L := by
      rw [show wStar D.M V₀ V h.isElemAbelian L =
          (wTil V₀ V h.isElemAbelian L).map κ from s15_semiBot_wStar_eq_map h]
      exact Subgroup.mem_map_of_mem κ hw
    let u₀ : ↥(wStar D.M V₀ V h.isElemAbelian L) := ⟨κ w, hkw⟩
    have hkey : ((a u₀ : ↥(wStar D.M V₀ V h.isElemAbelian L)) :
        vStar D.M V₀ V h.isElemAbelian L) = κ (p w) := by
      have h := s15_semiBot_awHom_kappa h1217 h ⟨p, hPL hpP⟩ w u₀ rfl
      simpa [a, κ] using h
    let q : ↥(wStar D.M V₀ V h.isElemAbelian L) := a u₀ * u₀⁻¹
    have hq : q ∈ commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)) AP :=
      Subgroup.mem_closure_of_mem ⟨a, haP, u₀, Subgroup.mem_top u₀, rfl⟩
    have hqval : (q : vStar D.M V₀ V h.isElemAbelian L) = κ (p w * w⁻¹) := by
      have h2 : (u₀ : vStar D.M V₀ V h.isElemAbelian L) = κ w := rfl
      show ((a u₀ * u₀⁻¹ : ↥(wStar D.M V₀ V h.isElemAbelian L)) :
          vStar D.M V₀ V h.isElemAbelian L) = κ (p w * w⁻¹)
      rw [show ((a u₀ * u₀⁻¹ : ↥(wStar D.M V₀ V h.isElemAbelian L)) :
            vStar D.M V₀ V h.isElemAbelian L) =
          ((a u₀ : ↥(wStar D.M V₀ V h.isElemAbelian L)) :
            vStar D.M V₀ V h.isElemAbelian L) *
          (((u₀ : ↥(wStar D.M V₀ V h.isElemAbelian L)) :
            vStar D.M V₀ V h.isElemAbelian L))⁻¹ from rfl]
      rw [hkey, h2, ← map_inv, ← map_mul]
    exact ⟨q, hq, hqval⟩
  have hstar : wStar D.M V₀ V h.isElemAbelian L =
      Subgroup.closure ((s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V
        h.isElemAbelian (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)) '' gens) := by
    rw [s15_semiBot_wStar_eq_map h, ← hP]
    exact MonoidHom.map_closure _ gens
  have hle : Subgroup.closure ((s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V
      h.isElemAbelian (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)) '' gens) ≤
      (commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)) AP).map
        (wStar D.M V₀ V h.isElemAbelian L).subtype :=
    (Subgroup.closure_le _).2 hgen
  have hu' : (u : vStar D.M V₀ V h.isElemAbelian L) ∈
      (commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)) AP).map
        (wStar D.M V₀ V h.isElemAbelian L).subtype := by
    apply hle
    rw [← hstar]
    exact u.2
  obtain ⟨q', hq', hqeq⟩ := Subgroup.mem_map.1 hu'
  rw [← Subtype.ext hqeq]
  exact hq'

theorem s15_semiBot_conj_mem_map_awHom (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {P : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hPL : P ≤ barSub V₀ V h.isElemAbelian L)
    (hN : ∀ n ∈ Mbar D.M V₀ V h.isElemAbelian ⊓
        normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _),
      ∀ p ∈ P, n * p * n⁻¹ ∈ P)
    {t : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)} (ht : t ∈ s15NW h)
    {a : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)}
    (ha : a ∈ ((P.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
      (s15AW h).subtype) :
    t * a * t⁻¹ ∈ ((P.subgroupOf (barSub V₀ V h.isElemAbelian L)).map
      (s15AWHom h1217 h)).map (s15AW h).subtype := by
  rw [s15_Three_NW_eq] at ht
  obtain ⟨g, rfl⟩ := ht
  obtain ⟨c, hcA, hac⟩ := ha
  obtain ⟨b, hbP, hbc⟩ := hcA
  rw [← hac, ← hbc]
  obtain ⟨y, hy⟩ := s15_Three_psiL_surjective h b
  have hbval : (b : MulAut (Vtil V₀ V h.isElemAbelian)) =
      s15Psi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) := by
    rw [← hy]; rfl
  have haval : (s15AW h).subtype (s15AWHom h1217 h b) =
      s15Phi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) := by
    rw [← hy, s15AWHom_apply]; rfl
  rw [haval]
  have hg₀ : (g : G) ∈ stabTil V₀ V :=
    s15_Three_M_le_stabTil h (s15_Three_nBar_le_M h g.2)
  have hbP' : (b : MulAut (Vtil V₀ V h.isElemAbelian)) ∈ P :=
    Subgroup.mem_subgroupOf.1 hbP
  have hnM : s15Psi h g ∈ Mbar D.M V₀ V h.isElemAbelian :=
    actTil_mem_barSub V₀ V h.isElemAbelian (s15_Three_nBar_le_M h g.2) hg₀
  have hnN : s15Psi h g ∈ normalizer
      ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _) :=
    s15_Three_psi_mem_normalizer h g
  let p' : MulAut (Vtil V₀ V h.isElemAbelian) :=
    s15Psi h g * (b : MulAut (Vtil V₀ V h.isElemAbelian)) * (s15Psi h g)⁻¹
  have hp' : p' ∈ P :=
    hN (s15Psi h g) ⟨hnM, hnN⟩ (b : MulAut (Vtil V₀ V h.isElemAbelian)) hbP'
  obtain ⟨l', hl'L, hl'eq⟩ := s15_Three_exists_mem_L h (hPL hp')
  have hker : g * (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) * g⁻¹ * l'⁻¹ ∈
      (s15Psi h).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hl'eq, ← hbval]
    change s15Psi h g * (b : MulAut (Vtil V₀ V h.isElemAbelian)) * (s15Psi h g)⁻¹ *
      p'⁻¹ = 1
    rw [show p' = s15Psi h g * (b : MulAut (Vtil V₀ V h.isElemAbelian)) *
      (s15Psi h g)⁻¹ from rfl]
    group
  have hphieq : s15Phi h (g * (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) * g⁻¹) =
      s15Phi h l' := by
    have h1 := s15_Three_ker_psi_le_phi h1217 h hker
    rw [MonoidHom.mem_ker] at h1
    have h2 : s15Phi h g * s15Phi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) *
        (s15Phi h g)⁻¹ * (s15Phi h l')⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    rw [map_mul, map_mul, map_inv]
    exact mul_inv_eq_one.mp h2
  rw [show s15Phi h g * s15Phi h (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) *
      (s15Phi h g)⁻¹ =
      s15Phi h (g * (y : ↥(nBar D.M V₀ V h.isElemAbelian L)) * g⁻¹)
        from by rw [map_mul, map_mul, map_inv], hphieq]
  let b' : ↥(barSub V₀ V h.isElemAbelian L) := s15PsiL h ⟨l', hl'L⟩
  have hb'P : b' ∈ P.subgroupOf (barSub V₀ V h.isElemAbelian L) := by
    rw [Subgroup.mem_subgroupOf]
    change s15Psi h (l' : ↥(nBar D.M V₀ V h.isElemAbelian L)) ∈ P
    rw [hl'eq]
    exact hp'
  have hb'A : ((s15AWHom h1217 h b' : ↥(s15AW h)) :
      MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) = s15Phi h l' := by
    change (s15AWHom h1217 h (s15PsiL h ⟨l', hl'L⟩) :
      MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) = s15Phi h l'
    rw [s15AWHom_apply]; rfl
  rw [← hb'A]
  exact Subgroup.mem_map_of_mem (s15AW h).subtype
    (Subgroup.mem_map_of_mem (s15AWHom h1217 h) hb'P)

theorem s15_semiBot_false_of_pair (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (htr : ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L))
    {P Q : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hPL : P ≤ barSub V₀ V h.isElemAbelian L) (hQL : Q ≤ barSub V₀ V h.isElemAbelian L)
    (hPQ : ⁅P, Q⁆ = ⊥) (hQ : ⁅Q, Q⁆ = Q)
    (hWP : commSub (wTil V₀ V h.isElemAbelian L) P = wTil V₀ V h.isElemAbelian L)
    (hWQ : commSub (wTil V₀ V h.isElemAbelian L) Q = wTil V₀ V h.isElemAbelian L)
    (hN : ∀ n ∈ Mbar D.M V₀ V h.isElemAbelian ⊓
        normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _),
      ∀ p ∈ P, n * p * n⁻¹ ∈ P) : False := by
  obtain ⟨t, htN, ht⟩ := s15_Three_exists_transvection h htr
  have hAB : ⁅((P.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
        (s15AW h).subtype,
      ((Q.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
        (s15AW h).subtype⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      s15_semiBot_commutator_subgroupOf hPL hQL, hPQ, Subgroup.bot_subgroupOf,
      Subgroup.map_bot, Subgroup.map_bot]
  have hB : ⁅((Q.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
        (s15AW h).subtype,
      ((Q.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
        (s15AW h).subtype⁆ =
      ((Q.subgroupOf (barSub V₀ V h.isElemAbelian L)).map (s15AWHom h1217 h)).map
        (s15AW h).subtype := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,
      s15_semiBot_commutator_subgroupOf hQL hQL, hQ]
  exact s15_semiBot_noTransv (s15_Three_wStar_exp h) hAB hB
    (s15_semiBot_commSub_top_map_awHom h1217 h hPL hWP)
    (s15_semiBot_commSub_top_map_awHom h1217 h hQL hWQ) ht
    (fun a ha => s15_semiBot_conj_mem_map_awHom h1217 h hPL hN htN ha)

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
