module

public import CFSG.Quasithin.Background.G10FifteenNondegG
public import CFSG.Quasithin.Background.G10FifteenCase2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem nondegOn_conj {B : LinearMap.BilinForm (ZMod 2) V} {I : Submodule (ZMod 2) V}
    (hnd : NondegOn B I) {x : GLV V} (hx : ∀ v w, B (x v) (x w) = B v w) :
    NondegOn B (conjSub x I) := by
  intro u hu hall
  have hw : x.symm u ∈ I := mem_conjSub.1 hu
  have h0 : x.symm u = 0 := by
    refine hnd _ hw fun w hw' => ?_
    have h1 := hall (x w) (apply_mem_conjSub hw')
    rw [← hx (x.symm u) w]
    have : x (x.symm u) = u := LinearEquiv.apply_symm_apply x u
    rw [this]
    exact h1
  have : u = x (x.symm u) := (LinearEquiv.apply_symm_apply x u).symm
  rw [this, h0, map_zero]

theorem isSubnormal_of_normal_normal {Γ H R : Subgroup (GLV V)} (hHΓ : H ≤ Γ) (hRH : R ≤ H)
    (hH : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hR : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) :
    IsSubnormal R Γ := by
  refine IsSubnormal.step hRH ?_ (IsSubnormal.step hHΓ ?_ (IsSubnormal.refl Γ))
  · rw [Subgroup.normal_subgroupOf_iff hRH]
    intro r h hr hh
    exact hR h hh r hr
  · rw [Subgroup.normal_subgroupOf_iff hHΓ]
    intro h γ hh hγ
    exact hH γ hγ h hh

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem component_le_centralizer {I : Submodule (ZMod 2) V} (hI : Invariant (normalClosure Γ L) I)
    {x : GLV V} (hx : x ∈ X) (hc : IsCompl I (conjSub x I))
    (hsplit : ∀ h ∈ normalClosure Γ L, ∃ r ∈ centralizerOn (normalClosure Γ L) I,
      ∃ r' ∈ centralizerOn (normalClosure Γ L) (conjSub x I), h = r * r') :
    L ≤ centralizerOn (normalClosure Γ L) (conjSub x I) ∨
      L ≤ centralizerOn (normalClosure Γ L) I := by
  have hI' : Invariant (normalClosure Γ L) (conjSub x I) :=
    hI.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  have hsubR := isSubnormal_of_normal_normal (Γ := Γ) (R := centralizerOn (normalClosure Γ L) I)
    hyp.H_le (fun r hr => hr.1) (normalClosure_normal Γ L) (centralizerOn_normal hI)
  have hsubR' := isSubnormal_of_normal_normal (Γ := Γ)
    (R := centralizerOn (normalClosure Γ L) (conjSub x I))
    hyp.H_le (fun r hr => hr.1) (normalClosure_normal Γ L) (centralizerOn_normal hI')
  obtain ⟨l₀, hl₀L, hl₀1⟩ := hyp.exists_ne_one_mem_L
  rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hyp.component hsubR with h1 | h1
  · rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hyp.component hsubR' with h2 | h2
    · exfalso
      exact hl₀1 (eq_one_of_centralizes_compl hc (h1 hl₀L).2 (h2 hl₀L).2)
    · exact Or.inr h1
  · rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hyp.component hsubR' with h2 | h2
    · exact Or.inl h2
    · exfalso
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h1 h2
      have hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
        intro a ha b hb
        obtain ⟨r, hr, r', hr', hbeq⟩ := hsplit b (le_normalClosure Γ L hb)
        have hr1 : a * r = r * a := (Subgroup.mem_centralizer_iff.1 (h1 ha) r hr).symm
        have hr2 : a * r' = r' * a := (Subgroup.mem_centralizer_iff.1 (h2 ha) r' hr').symm
        rw [hbeq, ← mul_assoc, hr1, mul_assoc, hr2, ← mul_assoc]
      have hperf : Group.IsPerfect ↥L := ⟨hyp.component.2.2.1⟩
      have hcm : IsMulCommutative ↥L := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
      have hsub := Group.IsPerfect.subsingleton_of_isMulCommutative (G := ↥L)
      exact hl₀1 (congrArg Subtype.val (Subsingleton.elim (⟨l₀, hl₀L⟩ : ↥L) 1))


theorem case2 (hq : IsQuotientOfSQTKTauCeti ↥Γ) (hOut : OuterGLInput) (hSQT : SectionSQTInput)
    (h1212 : G1212Stmt) (hSimple : InspectSimple) (hOuter : InspectOuter)
    (hSylow : InspectSylow) (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) : G1015Concl B Γ v₁ W X L := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  rcases hyp.isotropic_or_nondegOn hirr with hiso | hnd
  · obtain ⟨hII, h3⟩ := hyp.caseTwo_isotropic hOut h10 h11 h12 hI hfix hx hne hiso
    exact ⟨I, hI, Or.inr (hyp.caseOne_ii h10 h11 h12 hI hfix hx hne), Or.inr (Or.inl hII), h3⟩
  · have hc := hyp.isCompl_sup_conj h10 h11 h12 hI hfix hx hne
    obtain ⟨i, hi, hi0, hv, hY⟩ := hyp.exists_i h10 hI hfix hx hne
    have hFT := hyp.fullTransvections hI hfix hx hne hi hv
    have horth := hyp.conj_le_orthogonal h10 h11 h12 hI hfix hx hne hnd
    have hnle := hyp.not_le_perp_of_nondeg hi.1 hi0 hv hnd horth
    obtain ⟨hsplit, -⟩ := hyp.split_structure hq hSQT h1212 hSimple hOuter hSylow h10 h11 h12 hI
      hfix hx hne hc hi hi0 hFT hnd hnle
    have hx2 : x * x = 1 := hyp.X_sq x hx
    rcases hyp.component_le_centralizer hI.1 hx hc hsplit with hL | hL
    · have hIII := hyp.III_of_nondeg hq hSQT h1212 hSimple hOuter hSylow h10 h11 h12 hI hfix hx hne
        hnd hL
      exact ⟨I, hI, Or.inr (hyp.caseOne_ii h10 h11 h12 hI hfix hx hne), Or.inr (Or.inr hIII),
        Or.inl (not_autAll_of_selfDual (hyp.two_lt_finrank hirr) hIII.2.1)⟩
    · have hI' : IrrPlus (normalClosure Γ L) (conjSub x I) := hyp.irrPlus_conj hI hx
      have hirr' : IsIrr (normalClosure Γ L) (conjSub x I) := hI'.isIrr hyp.fixedSpace_H
      have hfix' := hyp.fix_conj hI hfix hx hne
      have hne' := hyp.conj_conj_ne (I := I) hx hne
      have hnd' : NondegOn B (conjSub x I) := nondegOn_conj hnd (hyp.isometry x (hyp.X_le hx))
      have hL' : L ≤ centralizerOn (normalClosure Γ L) (conjSub x (conjSub x I)) := by
        rw [conjSub_conjSub_of_sq hx2]
        exact hL
      have hIII := hyp.III_of_nondeg hq hSQT h1212 hSimple hOuter hSylow h10 h11 h12 hI' hfix' hx
        hne' hnd' hL'
      exact ⟨conjSub x I, hI', Or.inr (hyp.caseOne_ii h10 h11 h12 hI' hfix' hx hne'),
        Or.inr (Or.inr hIII), Or.inl (not_autAll_of_selfDual (hyp.two_lt_finrank hirr') hIII.2.1)⟩

end G108Hyp

end G11

end CFSG.Quasithin
