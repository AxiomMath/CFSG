module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinCells
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GuardedLargeEvenLabel (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank) ∨
    ((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
    (lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) ∨
    (lab.tag = .A ∧ 5 ≤ lab.rank ∧ lab.n = 1)

theorem GuardedLargeEvenLabel.not_ggLabelIso_unitary
    {lab : LargeEvenLabel} (hg : GuardedLargeEvenLabel lab) (r k : ℕ) :
    ¬ GGLabelIso lab ⟨.twA, r, k⟩ := by
  intro hi
  rcases hi with he | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · rw [he] at hg
    simpa [GuardedLargeEvenLabel] using hg
  · simp at hBC
  · simp at hDA
  · simp at hAD
  · rw [hD3A3.1] at hg
    norm_num [GuardedLargeEvenLabel] at hg
  · simp at hA3D3
  · simp at hD2A1
  · simp at hA1D2

theorem GuardedLargeEvenLabel.linear_bounds_of_ggLabelIso
    {lab : LargeEvenLabel} (hg : GuardedLargeEvenLabel lab) {r k : ℕ}
    (hi : GGLabelIso lab ⟨.A, r, k⟩) : 5 ≤ r ∧ k = 1 := by
  rcases hi with he | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · rw [he] at hg
    simpa [GuardedLargeEvenLabel] using hg
  · simp at hBC
  · rw [hDA.1] at hg
    norm_num [GuardedLargeEvenLabel] at hg
  · rw [hAD.1] at hg
    norm_num [GuardedLargeEvenLabel] at hg
  · simp at hD3A3
  · simp at hA3D3
  · rw [hD2A1.1] at hg
    norm_num [GuardedLargeEvenLabel] at hg
  · simp at hA1D2

theorem ggActualMember_internal_component
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hq : CFSG.Assembly.IsQuasisimple ↥X) :
    ∃ z : G, ((X = L ∧ z = x) ∨ GGNbr p B x D J z X) ∧
      z ∈ ggG0 p B x L D J ∧ z ^ p = 1 ∧
        CFSG.Assembly.IsComponentOf X
          (ggG0 p B x L D J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have hBs : CFSG.Open.IsElemAbelian p Bs := hcfg.2.1.2.1
  rcases horigin with ⟨hXL, hxG⟩ | ⟨y, hNb, hyG⟩
  · subst X
    have hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
      hcfg.1.2.2.2.2.2.2.1.2.2.2.1
    have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
    refine ⟨x, Or.inl ⟨rfl, rfl⟩, hxG, hBs.2 x hxBs, ?_⟩
    exact hL.of_le_of_le (le_inf (le_ggG0_left p B x L D J) hL.1) inf_le_right
  · have hPC : CFSG.Assembly.LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) X :=
      hNb.1.2.2.2.2.1
    have hX : CFSG.Assembly.IsComponentOf X (Subgroup.centralizer ({y} : Set G)) :=
      ⟨hPC.1, hPC.2.1, hq⟩
    have hyBs : y ∈ Bs := hcfg.2.1.1 hNb.1.2.1
    refine ⟨y, Or.inr hNb, hyG, hBs.2 y hyBs, ?_⟩
    exact hX.of_le_of_le (le_inf (le_ggG0_of_ggNbr hNb) hX.1) inf_le_right

theorem ggActualMember_injective_model
    {G U : Type} [Group G] [Finite G] [Group U] {p : ℕ}
    {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) (psi : U →* G) (hinj : Function.Injective psi)
    (hrange : psi.range = ggG0 p B x L D J)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hq : CFSG.Assembly.IsQuasisimple ↥X) :
    ∃ z : U, Odd (orderOf z) ∧
      ((X = L ∧ psi z = x) ∨ GGNbr p B x D J (psi z) X) ∧
      CFSG.Assembly.IsComponentOf (X.comap psi) (Subgroup.centralizer ({z} : Set U)) ∧
      (X.comap psi).map psi = X := by
  obtain ⟨z0, hz0, hzG, hzp, hX⟩ := ggActualMember_internal_component hcfg horigin hq
  have hXR : X ≤ psi.range := by rw [hrange]; exact hX.1.trans inf_le_left
  obtain ⟨z, hz⟩ : z0 ∈ psi.range := hrange.symm ▸ hzG
  have hzp' : z ^ p = 1 := by
    apply hinj
    rw [map_pow, hz, hzp, map_one]
  obtain ⟨hp, hp2, -⟩ :=
    (hcfg.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hodd : Odd (orderOf z) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hzp')
  have hmap : (X.comap psi).map psi = X := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hXR]
  let eX : ↥(X.comap psi) ≃* ↥X :=
    ((X.comap psi).equivMapOfInjective psi hinj).trans (MulEquiv.subgroupCongr hmap)
  have hq' : CFSG.Assembly.IsQuasisimple ↥(X.comap psi) := hq.of_mulEquiv eX
  have hC : (ggG0 p B x L D J ⊓ Subgroup.centralizer ({z0} : Set G)).comap psi =
      Subgroup.centralizer ({z} : Set U) := by
    ext u
    constructor
    · intro hu
      apply Subgroup.mem_centralizer_iff.mpr
      intro a ha
      have ha' := Set.mem_singleton_iff.mp ha
      subst a
      apply hinj
      rw [map_mul, map_mul, hz]
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hu).2 z0 rfl
    · intro hu
      apply Subgroup.mem_comap.mpr
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
      · rw [← hrange]
        exact ⟨u, rfl⟩
      · intro a ha
        have ha' := Set.mem_singleton_iff.mp ha
        subst a
        have hc := Subgroup.mem_centralizer_iff.mp hu z rfl
        simpa only [map_mul, hz] using congrArg psi hc
  have hsub := hX.2.1.comap psi
  rw [hC] at hsub
  have hle := Subgroup.comap_mono hX.1 (f := psi)
  rw [hC] at hle
  refine ⟨z, hodd, ?_, ⟨hle, hsub, hq'⟩, hmap⟩
  simpa only [hz] using hz0

section Cells

@[expose] def MemberSelectedSL2At {G : Type} [Group G] (X S : Subgroup G) : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ) (lam : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f ∧ 2 ≤ (ggU t n f).D.rank ∧
      lam.ker ≤ Subgroup.center (ggU t n f).K ∧ lam.range = X ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
        (δ : Fin (ggU t n f).D.rank → ℤ)
        (model : SelectedRoot.SelectedSL2Model (ggU t n f).D k δ),
        (lam.comp model.phi).range = S

@[expose] def PresentedSelectedSL2At {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (ψ : (ggU t n f).K →* G) (S : Subgroup G) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
    (γ : Fin (ggU t n f).D.rank → ℤ) (model : SelectedRoot.SelectedSL2Model (ggU t n f).D k γ)
    (u : (ggU t n f).K), ((ψ.comp (MulAut.conj u).toMonoidHom).comp model.phi).range = S

theorem MemberSelectedSL2At.map_of_injective {G H : Type} [Group G] [Group H]
    (φ : G →* H) (hφ : Function.Injective φ) {X S : Subgroup G}
    (h : MemberSelectedSL2At X S) : MemberSelectedSL2At (X.map φ) (S.map φ) := by
  obtain ⟨t, n, f, lam, hadm, hrk, hker, hrange, k, hk, hkfin, hkchar, δ, model, hmem⟩ := h
  refine ⟨t, n, f, φ.comp lam, hadm, hrk, ?_, ?_, k, hk, hkfin, hkchar, δ, model, ?_⟩
  · intro y hy
    have h1 : φ (lam y) = 1 := MonoidHom.mem_ker.mp hy
    have h2 : lam y = 1 := hφ (by simpa only [map_one] using h1)
    exact hker (MonoidHom.mem_ker.mpr h2)
  · rw [MonoidHom.range_comp, hrange]
  · change (φ.comp (lam.comp model.phi)).range = S.map φ
    rw [MonoidHom.range_comp, hmem]

theorem PresentedSelectedSL2At.map {G H : Type} [Group G] [Group H]
    (φ : G →* H) {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    {S : Subgroup G} (h : PresentedSelectedSL2At ψ S) :
    PresentedSelectedSL2At (φ.comp ψ) (S.map φ) := by
  obtain ⟨k, hk, hkfin, hkchar, γ, model, u, hprs⟩ := h
  refine ⟨k, hk, hkfin, hkchar, γ, model, u, ?_⟩
  change (φ.comp ((ψ.comp (MulAut.conj u).toMonoidHom).comp model.phi)).range = S.map φ
  rw [MonoidHom.range_comp, hprs]

theorem ggCompat_of_selected_packages {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G}
    {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ) {X : Subgroup G}
    (hX : X = L ∨ ∃ y : G, GGNbr p B x D J y X) {S : Subgroup G} (hM : MemberSelectedSL2At X S)
    (hP : PresentedSelectedSL2At ψ S) : GGSecFiveCompat p B x L D J := by
  obtain ⟨t', n', f', lam, hadm, hrk, hker, hrange, k, hk, hkfin, hkchar, δ, model', hmem⟩ := hM
  obtain ⟨k', hk', hk'fin, hk'char, γ, model, u, hprs⟩ := hP
  exact ggSecFiveCompat_of_selectedSL2 hpres hX hadm hrk hker hrange model model' u
    (hprs.trans hmem.symm)

@[expose] def KnownActualMemberSelectedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ∀ X : Subgroup G,
            ((X = L ∧ x ∈ ggG0 p B x L D J) ∨
              ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J) →
            LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab) →
              ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S

end Cells

end CFSG.StandardType
