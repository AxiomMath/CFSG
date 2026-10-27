module

public import CFSG.Quasithin.Background.G10FifteenSD
public import CFSG.Quasithin.Background.G10Clifford

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_one_of_fixes_sSup {S : Set (Submodule (ZMod 2) V)} (hS : sSup S = ⊤) {γ : GLV V}
    (h : ∀ J ∈ S, ∀ u ∈ J, γ u = u) : γ = 1 := by
  have hle : sSup S ≤ LinearMap.eqLocus (γ : V →ₗ[ZMod 2] V) LinearMap.id :=
    sSup_le fun J hJ u hu => h J hJ u hu
  rw [hS] at hle
  ext v
  exact hle Submodule.mem_top

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem exists_irr_fixed : ∃ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I ∧
    ∀ x ∈ X, HIso (normalClosure Γ L) I (conjSub x I) → conjSub x I = I := by
  obtain ⟨J₀, hJ₀⟩ := hyp.exists_isIrr
  obtain ⟨I, hI, -, hfix⟩ := _root_.CFSG.Quasithin.G11.exists_irr_fixed (X := X)
    hyp.X_le (normalClosure_normal Γ L) hyp.X_sq hJ₀
  exact ⟨I, hI.irrPlus hyp.fixedSpace_H, hfix⟩

theorem eq_one_of_fixes_irrPlus {γ : GLV V}
    (h : ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → ∀ u ∈ J, γ u = u) :
    γ = 1 :=
  eq_one_of_fixes_sSup hyp.sSup_irrPlus h

theorem hiso_of_invariant (h10 : G1010Concl Γ v₁ X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) (hX : Invariant X I) (hv : v₁ ∈ I)
    {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) :
    HIso (normalClosure Γ L) J I := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hJirr : IsIrr (normalClosure Γ L) J := hJ.isIrr hyp.fixedSpace_H
  by_contra hJI
  let S : Set (Submodule (ZMod 2) V) :=
    {J | IsIrr (normalClosure Γ L) J ∧ ¬ HIso (normalClosure Γ L) J I}
  have hSirr : ∀ J ∈ S, IsIrr (normalClosure Γ L) J := fun J hJ => hJ.1
  have hSI : ∀ J ∈ S, ¬ HIso (normalClosure Γ L) J I := fun J hJ => hJ.2
  have hDH : Invariant (normalClosure Γ L) (sSup S) := invariant_sSup fun J hJ => hJ.1.1
  have hDX : Invariant X (sSup S) := by
    rw [invariant_iff_conjSub_le]
    intro x hx
    rw [conjSub_sSup]
    refine sSup_le ?_
    rintro _ ⟨K, hK, rfl⟩
    refine le_sSup ⟨hK.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx), fun hiso => hK.2 ?_⟩
    have h1 := hiso_conj (normalClosure_normal Γ L) (hyp.X_le (X.inv_mem hx)) hiso
    rw [conjSub_inv_conjSub, hX.conjSub_eq (X.inv_mem hx)] at h1
    exact h1
  have hDHX : Invariant (normalClosure Γ L ⊔ X) (sSup S) := hDH.sup_subgroup hDX
  have hD0 : sSup S = ⊥ := by
    by_contra hne
    have hvD : v₁ ∈ sSup S := (h10 _ hne hDHX).1
    have hvI : v₁ ∈ homComp (normalClosure Γ L) I := le_homComp hirr hv
    have := homComp_inf_eq_bot hirr S hSirr hSI
    have hmem : v₁ ∈ homComp (normalClosure Γ L) I ⊓ sSup S := ⟨hvI, hvD⟩
    rw [this, Submodule.mem_bot] at hmem
    exact hyp.point hmem
  have hJS : J ∈ S := ⟨hJirr, hJI⟩
  have : J ≤ sSup S := le_sSup hJS
  rw [hD0, le_bot_iff] at this
  exact hJirr.ne_bot this

theorem case1 (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h13 : G1013Concl B Γ v₁ L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I) (hX : Invariant X I) : G1015Concl B Γ v₁ W X L := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hv : v₁ ∈ I := (h11 I hI).1 hX
  have hhiso := fun J (hJ : IrrPlus (normalClosure Γ L) J) => hyp.hiso_of_invariant h10 hI hX hv hJ
  have hhom : Homogeneous (normalClosure Γ L) := fun J J' hJ hJ' =>
    hiso_trans (hJ.1) hirr.1 hJ'.1 (hhiso J hJ) (hiso_symm hJ'.1 hirr.1 (hhiso J' hJ'))
  have huniq : ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → Invariant X J →
      J = I := by
    intro J hJ hJX
    have hvJ : v₁ ∈ J := (h11 J hJ).1 hJX
    have hJirr : IsIrr (normalClosure Γ L) J := hJ.isIrr hyp.fixedSpace_H
    have h1 : I ≤ J := by
      rcases hirr.eq_bot_or_eq (hirr.1.inf hJirr.1) inf_le_left with h | h
      · exfalso
        have : v₁ ∈ I ⊓ J := ⟨hv, hvJ⟩
        rw [h, Submodule.mem_bot] at this
        exact hyp.point this
      · rw [← h]
        exact inf_le_right
    have h2 : J ≤ I := by
      rcases hJirr.eq_bot_or_eq (hJirr.1.inf hirr.1) inf_le_left with h | h
      · exfalso
        have : v₁ ∈ J ⊓ I := ⟨hvJ, hv⟩
        rw [h, Submodule.mem_bot] at this
        exact hyp.point this
      · rw [← h]
        exact inf_le_right
    exact le_antisymm h2 h1
  have hfaith : FaithfulOn (normalClosure Γ L) I := by
    rw [faithfulOn_iff]
    intro k hk hki
    have hkΓ : k ∈ Γ := hyp.H_le hk
    have : (⟨k, hkΓ⟩ : Γ) = 1 := by
      apply Subtype.ext
      refine hyp.eq_one_of_fixes_irrPlus fun J hJ u hu => ?_
      have hJI := hhiso J hJ
      have hc := centralizerOn_eq_of_hiso hJ.1 hI.1 hJI
      have hkI : k ∈ centralizerOn (normalClosure Γ L) I := ⟨hk, hki⟩
      rw [← hc] at hkI
      exact hkI.2 u hu
    exact congrArg Subtype.val this
  have hsd : SelfDual (normalClosure Γ L) I := by
    rcases h13 I hI hv with hiso | ⟨htop, -⟩
    · obtain ⟨J, hJ, hd, -⟩ := hyp.exists_dual hirr hiso
      exact selfDual_of_isDualOf_hiso hd (hhom I J hI hJ)
    · refine selfDual_of_nondegOn hyp.toG101Hyp.isRefl hyp.H_isometry ?_
      rw [htop]
      intro u _ hu
      exact hyp.nondegenerate u fun w => hu w Submodule.mem_top
  refine ⟨I, hI, Or.inl ⟨hhom, hX, hv, huniq⟩, Or.inl ⟨hhom, hsd, hfaith, ?_⟩,
    Or.inl (not_autAll_of_selfDual (hyp.two_lt_finrank hirr) hsd)⟩
  rcases h13 I hI hv with hiso | ⟨htop, -⟩
  · exact Or.inl hiso
  · exact Or.inr htop

end G108Hyp

end G11

end CFSG.Quasithin
