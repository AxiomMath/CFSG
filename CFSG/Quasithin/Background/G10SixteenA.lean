module

public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.G10Clifford

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem exists_noncomm {a : GLV V} (ha1 : a ≠ 1)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2) :
    ∃ h ∈ normalClosure Γ L, a * h ≠ h * a := by
  by_contra hcon
  push Not at hcon
  set R := LinearMap.range (a.toLinearMap - LinearMap.id) with hR
  have hRinv : Invariant (normalClosure Γ L) R := by
    rintro h hh _ ⟨v, rfl⟩
    refine ⟨h v, ?_⟩
    have := congrArg (fun g : GLV V => g v) (hcon h hh)
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub]
    have h2 : a (h v) = h (a v) := this
    rw [h2]
  have hR0 : R ≠ ⊥ := by
    intro h0
    apply ha1
    ext v
    have hmem : (a.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) v ∈ R := ⟨v, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    have : a v - v = 0 := hmem
    exact sub_eq_zero.1 this
  obtain ⟨J, hJR, hJ⟩ := exists_isIrr_le hRinv hR0
  have hJ' : IrrPlus (normalClosure Γ L) J := hJ.irrPlus hyp.fixedSpace_H
  have h1 := hyp.two_lt_finrank hJ
  have h2 := Submodule.finrank_mono hJR
  omega

theorem conj_eq_of_finrank_le {a : GLV V} (ha : a ∈ X)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I) : conjSub a I = I := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  by_contra hne
  have hbot : conjSub a I ⊓ I = ⊥ := by
    rcases hirr.conj_eq_or_inf_eq_bot (normalClosure_normal Γ L) (hyp.X_le ha) with h | h
    · exact absurd h hne
    · exact h
  let φ : ↥I →ₗ[ZMod 2] V := (a.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V).domRestrict I
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : a (u : V) - (u : V) = 0 := hu
    have h2 : a (u : V) = (u : V) := sub_eq_zero.1 h1
    have h3 : (u : V) ∈ conjSub a I ⊓ I := ⟨by
      have := apply_mem_conjSub (g := a) u.2
      rwa [h2] at this, u.2⟩
    rw [hbot, Submodule.mem_bot] at h3
    exact Subtype.ext h3
  have hle : LinearMap.range φ ≤ LinearMap.range (a.toLinearMap - LinearMap.id) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨(u : V), rfl⟩
  have h1 := LinearEquiv.finrank_eq (LinearEquiv.ofInjective φ hφ)
  have h2 := Submodule.finrank_mono hle
  have h3 := hyp.two_lt_finrank hirr
  omega


theorem le_normalClosure_zpowers {a : GLV V} (ha : a ∈ X)
    (hcomm : ∃ h ∈ normalClosure Γ L, a * h ≠ h * a) :
    normalClosure Γ L ≤ normalClosure Γ (Subgroup.zpowers a) := by
  have haΓ : Subgroup.zpowers a ≤ Γ := (Subgroup.zpowers_le).2 (hyp.X_le ha)
  have hKΓ : normalClosure Γ (Subgroup.zpowers a) ≤ Γ := normalClosure_le haΓ
  have hKnorm := normalClosure_normal Γ (Subgroup.zpowers a)
  have haK : a ∈ normalClosure Γ (Subgroup.zpowers a) :=
    Subgroup.subset_closure ⟨1, Γ.one_mem, a, Subgroup.mem_zpowers a, by simp⟩
  have hsubK : IsSubnormal (normalClosure Γ (Subgroup.zpowers a)) Γ := by
    refine IsSubnormal.step hKΓ ?_ (IsSubnormal.refl Γ)
    rw [Subgroup.normal_subgroupOf_iff hKΓ]
    intro h k hh hk
    exact hKnorm k hk h hh
  rcases CFSG.Quasithin.B113.component_le_or_commutator_eq_bot hyp.component hsubK with hLK | hLK
  · unfold normalClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    exact hKnorm γ hγ l (hLK hl)
  · exfalso
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hLK
    obtain ⟨h, hh, hne⟩ := hcomm
    apply hne
    have hle : normalClosure Γ L ≤ Subgroup.centralizer ({a} : Set (GLV V)) := by
      unfold normalClosure
      rw [Subgroup.closure_le]
      rintro _ ⟨γ, hγ, l, hl, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      have ha' : γ⁻¹ * b * γ⁻¹⁻¹ ∈ normalClosure Γ (Subgroup.zpowers b) :=
        hKnorm γ⁻¹ (Γ.inv_mem hγ) b haK
      have h1 := Subgroup.mem_centralizer_iff.1 (hLK hl) _ ha'
      calc b * (γ * l * γ⁻¹) = γ * ((γ⁻¹ * b * γ⁻¹⁻¹) * l) * γ⁻¹ := by group
        _ = γ * (l * (γ⁻¹ * b * γ⁻¹⁻¹)) * γ⁻¹ := by rw [h1]
        _ = γ * l * γ⁻¹ * b := by group
    exact Subgroup.mem_centralizer_iff.1 (hle hh) a rfl


theorem irrPlus_conj_of_mem {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J)
    {γ : GLV V} (hγ : γ ∈ Γ) : IrrPlus (normalClosure Γ L) (conjSub γ J) :=
  ((hJ.isIrr hyp.fixedSpace_H).conj_of_normal (normalClosure_normal Γ L) hγ).irrPlus
    hyp.fixedSpace_H

theorem invariant_normalClosure_zpowers {a : GLV V} (ha : a ∈ X)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2)
    {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) :
    Invariant (normalClosure Γ (Subgroup.zpowers a)) J := by
  have hstab : normalClosure Γ (Subgroup.zpowers a) ≤ stabilizerOf ⊤ J := by
    unfold normalClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨γ, hγ, g, hg, rfl⟩
    have hJ' : IrrPlus (normalClosure Γ L) (conjSub γ⁻¹ J) :=
      hyp.irrPlus_conj_of_mem hJ (Γ.inv_mem hγ)
    have hfixJ' : conjSub a (conjSub γ⁻¹ J) = conjSub γ⁻¹ J :=
      hyp.conj_eq_of_finrank_le ha hrank hJ'
    have hz : Subgroup.zpowers a ≤ stabilizerOf ⊤ (conjSub γ⁻¹ J) :=
      (Subgroup.zpowers_le).2 ⟨Subgroup.mem_top _, hfixJ'⟩
    refine ⟨Subgroup.mem_top _, ?_⟩
    have := (hz hg).2
    rw [conjSub_mul, conjSub_mul, this, conjSub_conjSub_inv]
  intro k hk u hu
  have h1 : k u ∈ conjSub k J := apply_mem_conjSub hu
  rwa [(hstab hk).2] at h1

theorem irrPlus_iff {a : GLV V} (ha : a ∈ X)
    (hrank : Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2)
    (hcomm : ∃ h ∈ normalClosure Γ L, a * h ≠ h * a) {I : Submodule (ZMod 2) V} :
    IrrPlus (normalClosure Γ L) I ↔ IrrPlus (normalClosure Γ (Subgroup.zpowers a)) I := by
  have hHK := hyp.le_normalClosure_zpowers ha hcomm
  have hfixK : fixedSpace (normalClosure Γ (Subgroup.zpowers a)) = ⊥ :=
    le_bot_iff.1 (hyp.fixedSpace_H ▸ fixedSpace_anti hHK)
  constructor
  · intro hI
    have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
    have hKinv := hyp.invariant_normalClosure_zpowers ha hrank hI
    refine IsIrr.irrPlus hfixK ⟨hKinv, hirr.2.1, fun J hJ hJ0 hJI => hirr.2.2 J (hJ.mono hHK) hJ0 hJI⟩
  · intro hI
    have hirrK : IsIrr (normalClosure Γ (Subgroup.zpowers a)) I := hI.isIrr hfixK
    refine IsIrr.irrPlus hyp.fixedSpace_H ⟨hirrK.1.mono hHK, hirrK.2.1, fun J hJ hJ0 hJI => ?_⟩
    by_cases hJbot : J = ⊥
    · exact Or.inl hJbot
    · right
      obtain ⟨J₀, hJ₀J, hJ₀⟩ := exists_isIrr_le hJ hJbot
      have hJ₀' : IrrPlus (normalClosure Γ L) J₀ := hJ₀.irrPlus hyp.fixedSpace_H
      have hJ₀K := hyp.invariant_normalClosure_zpowers ha hrank hJ₀'
      rcases hirrK.eq_bot_or_eq hJ₀K (hJ₀J.trans hJI) with h0 | h1
      · exact absurd h0 hJ₀.ne_bot
      · exact le_antisymm hJI (h1 ▸ hJ₀J)

end G108Hyp

end G11

end CFSG.Quasithin
