module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Transfer

variable {D : Data G} {V₀ V L : Subgroup G}

@[expose] noncomputable def s15K0 (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) : Subgroup G :=
  ((B.comap (s15Phi h)) ⊓ L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L)).map
    (nBar D.M V₀ V h.isElemAbelian L).subtype

theorem s15_Three_mem_K0 (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) {g : G} :
    g ∈ s15K0 h B ↔
      ∃ hg : g ∈ nBar D.M V₀ V h.isElemAbelian L, g ∈ L ∧ s15Phi h ⟨g, hg⟩ ∈ B := by
  constructor
  · rintro ⟨x, ⟨hxB, hxL⟩, rfl⟩
    exact ⟨x.2, hxL, hxB⟩
  · rintro ⟨hg, hgL, hB⟩
    exact ⟨⟨g, hg⟩, ⟨hB, hgL⟩, rfl⟩

theorem s15_Three_K0_le (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) : s15K0 h B ≤ L := by
  intro g hg
  obtain ⟨-, hgL, -⟩ := (s15_Three_mem_K0 h B).1 hg
  exact hgL

theorem s15_Three_nBar_range (h : Hyp151 D V₀ V L) :
    s15NBar D V₀ V h.isElemAbelian L = (s15Psi h).range := by
  ext x
  constructor
  · rintro ⟨hxM, hxN⟩
    obtain ⟨g, hgM, rfl⟩ := (mem_barSub _ _ _ _ _).1 hxM
    have hgn : (g : G) ∈ nBar D.M V₀ V h.isElemAbelian L :=
      (mem_preBarSub _ _ _ _ _).2 ⟨hgM, g.2, hxN⟩
    exact ⟨⟨(g : G), hgn⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨actTil_mem_barSub V₀ V h.isElemAbelian (s15_Three_nBar_le_M h g.2)
      (s15_Three_M_le_stabTil h (s15_Three_nBar_le_M h g.2)), s15_Three_psi_mem_normalizer h g⟩

theorem s15_Three_psi_conj_mem (h : Hyp151 D V₀ V L)
    (g : ↥(nBar D.M V₀ V h.isElemAbelian L)) {x : MulAut (Vtil V₀ V h.isElemAbelian)}
    (hx : x ∈ barSub V₀ V h.isElemAbelian L) :
    s15Psi h g * x * (s15Psi h g)⁻¹ ∈ barSub V₀ V h.isElemAbelian L :=
  (Subgroup.mem_normalizer_iff.1 (s15_Three_psi_mem_normalizer h g) x).1 hx

theorem s15_Three_AWEquiv_conj (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) (g : ↥(nBar D.M V₀ V h.isElemAbelian L))
    (x : ↥(barSub V₀ V h.isElemAbelian L)) :
    ((s15AWEquiv h1217 h hL ⟨s15Psi h g * (x : MulAut (Vtil V₀ V h.isElemAbelian)) *
        (s15Psi h g)⁻¹, s15_Three_psi_conj_mem h g x.2⟩ : ↥(s15AW h)) :
        MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) =
      s15Phi h g * ((s15AWEquiv h1217 h hL x : ↥(s15AW h)) :
        MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) * (s15Phi h g)⁻¹ := by
  obtain ⟨⟨l, hl⟩, rfl⟩ := s15_Three_psiL_surjective h x
  have hxl : ((s15PsiL h ⟨l, hl⟩ : ↥(barSub V₀ V h.isElemAbelian L)) :
      MulAut (Vtil V₀ V h.isElemAbelian)) = s15Psi h l := rfl
  obtain ⟨l', hl'L, hl'eq⟩ := s15_Three_exists_mem_L h
    (s15_Three_psi_conj_mem h g (s15_Three_psi_mem_barSub h l hl))
  have hker : g * l * g⁻¹ * l'⁻¹ ∈ (s15Psi h).ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hl'eq]
    simp
  have hphi := s15_Three_ker_psi_le_phi h1217 h hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hphi
  have hsub : (⟨s15Psi h g * (s15PsiL h ⟨l, hl⟩ : MulAut (Vtil V₀ V h.isElemAbelian)) *
      (s15Psi h g)⁻¹, s15_Three_psi_conj_mem h g (s15PsiL h ⟨l, hl⟩).2⟩ :
      ↥(barSub V₀ V h.isElemAbelian L)) = s15PsiL h ⟨l', hl'L⟩ :=
    Subtype.ext hl'eq.symm
  rw [hsub, s15AWEquiv_apply, s15AWEquiv_apply]
  change s15Phi h l' = _
  rw [← hphi, map_mul, map_mul, map_inv]
  rfl

theorem s15_Three_mem_barSub_K0_iff (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)))
    (y : ↥(barSub V₀ V h.isElemAbelian L)) :
    (y : MulAut (Vtil V₀ V h.isElemAbelian)) ∈ barSub V₀ V h.isElemAbelian (s15K0 h B) ↔
      ((s15AWEquiv h1217 h hL y : ↥(s15AW h)) :
        MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) ∈ B := by
  constructor
  · intro hy
    obtain ⟨k, hkK, hk⟩ := (mem_barSub _ _ _ _ _).1 hy
    obtain ⟨hkn, hkL, hkB⟩ := (s15_Three_mem_K0 h B).1 hkK
    have hyk : y = s15PsiL h ⟨⟨(k : G), hkn⟩, hkL⟩ := Subtype.ext hk.symm
    rw [hyk, s15AWEquiv_apply]
    exact hkB
  · intro hy
    obtain ⟨⟨l, hl⟩, rfl⟩ := s15_Three_psiL_surjective h y
    rw [s15AWEquiv_apply] at hy
    have hlK : (l : G) ∈ s15K0 h B := (s15_Three_mem_K0 h B).2 ⟨l.2, hl, hy⟩
    exact actTil_mem_barSub V₀ V h.isElemAbelian hlK (s15_Three_M_le_stabTil h
      (s15_Three_nBar_le_M h l.2))

private theorem s15_Three_comm_transfer {Γ Δ : Type*} [Group Γ] [Group Δ]
    {Lb Mb : Subgroup Γ} {A : Subgroup Δ} (θ : ↥Lb ≃* ↥A) (hLM : Lb ≤ Mb) {t : Δ}
    (p : ℤ → Γ) (hpM : ∀ j, p j ∈ Mb) (hpn : ∀ j (x : ↥Lb), p j * (x : Γ) * (p j)⁻¹ ∈ Lb)
    (hθ : ∀ j (x : ↥Lb), ((θ ⟨p j * (x : Γ) * (p j)⁻¹, hpn j x⟩ : ↥A) : Δ) =
      t ^ j * ((θ x : ↥A) : Δ) * (t ^ j)⁻¹)
    (y : ↥Lb) (hy : ((θ y : ↥A) : Δ) ∈ ⁅A, Subgroup.zpowers t⁆) : (y : Γ) ∈ ⁅Mb, Mb⁆ := by
  classical
  let φ₀ : ↥Lb →* Δ := A.subtype.comp θ.toMonoidHom
  have hφ₀ : Function.Injective φ₀ := Subtype.val_injective.comp θ.injective
  have hBS : ⁅A, Subgroup.zpowers t⁆ ≤ Subgroup.map φ₀ ((⁅Mb, Mb⁆).subgroupOf Lb) := by
    rw [Subgroup.commutator_le]
    intro a ha s hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    obtain ⟨x, hx⟩ := θ.surjective ⟨a, ha⟩
    have hxa : ((θ x : ↥A) : Δ) = a := congrArg Subtype.val hx
    refine ⟨x * ⟨p j * ((x⁻¹ : ↥Lb) : Γ) * (p j)⁻¹, hpn j x⁻¹⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have hc : ((x * ⟨p j * ((x⁻¹ : ↥Lb) : Γ) * (p j)⁻¹, hpn j x⁻¹⟩ : ↥Lb) : Γ) =
          ⁅(x : Γ), p j⁆ := by
        simp [commutatorElement_def, mul_assoc]
      rw [hc]
      exact Subgroup.commutator_mem_commutator (hLM x.2) (hpM j)
    · have h1 := hθ j x⁻¹
      have h2 : ((θ x⁻¹ : ↥A) : Δ) = (((θ x : ↥A) : Δ))⁻¹ := by
        rw [map_inv]; rfl
      change ((θ (x * ⟨p j * ((x⁻¹ : ↥Lb) : Γ) * (p j)⁻¹, hpn j x⁻¹⟩) : ↥A) : Δ) = _
      rw [map_mul, Subgroup.coe_mul, h1, h2, hxa, commutatorElement_def]
      group
  obtain ⟨z, hz, hzy⟩ := hBS hy
  have hzy' : z = y := hφ₀ hzy
  subst hzy'
  exact (Subgroup.mem_subgroupOf).1 hz

theorem s15_Three_kbar_le_comm (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) {t : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)}
    (htN : t ∈ s15NW h) {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))}
    (hB : B = ⁅s15AW h, Subgroup.zpowers t⁆) :
    barSub V₀ V h.isElemAbelian (s15K0 h B) ≤
      ⁅Mbar D.M V₀ V h.isElemAbelian, Mbar D.M V₀ V h.isElemAbelian⁆ := by
  classical
  have hV := h.isElemAbelian
  obtain ⟨g0, rfl⟩ : t ∈ (s15Phi h).range := by rwa [s15_Three_NW_eq] at htN
  intro y hy
  have hyL : y ∈ barSub V₀ V hV L := barSub_mono V₀ V hV (s15_Three_K0_le h B) hy
  have hyB := (s15_Three_mem_barSub_K0_iff h1217 h hL B ⟨y, hyL⟩).1 hy
  rw [hB] at hyB
  have hpM : ∀ j : ℤ, s15Psi h (g0 ^ j) ∈ Mbar D.M V₀ V hV := fun j =>
    actTil_mem_barSub V₀ V hV (s15_Three_nBar_le_M h (g0 ^ j).2)
      (s15_Three_M_le_stabTil h (s15_Three_nBar_le_M h (g0 ^ j).2))
  have hpn : ∀ (j : ℤ) (x : ↥(barSub V₀ V hV L)),
      s15Psi h (g0 ^ j) * (x : MulAut (Vtil V₀ V hV)) * (s15Psi h (g0 ^ j))⁻¹ ∈
        barSub V₀ V hV L := fun j x => s15_Three_psi_conj_mem h (g0 ^ j) x.2
  exact s15_Three_comm_transfer (Lb := barSub V₀ V hV L) (Mb := Mbar D.M V₀ V hV)
    (A := s15AW h) (s15AWEquiv h1217 h hL) (barSub_mono V₀ V hV h.le) (t := s15Phi h g0)
    (fun j => s15Psi h (g0 ^ j)) hpM hpn
    (fun j x => by
      rw [s15_Three_AWEquiv_conj h1217 h hL (g0 ^ j) x, map_zpow]) ⟨y, hyL⟩ hyB

end Transfer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
