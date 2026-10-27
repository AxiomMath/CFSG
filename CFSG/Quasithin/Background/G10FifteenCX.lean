module

public import CFSG.Quasithin.Background.G10FifteenDecomp
public import CFSG.Quasithin.Background.G10FifteenCase1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_of_hiso_of_le_sup [Finite V] {H : Subgroup (GLV V)} {I I' J : Submodule (ZMod 2) V}
    (hI : IsIrr H I) (hI' : IsIrr H I') (hn : ¬ HIso H I' I) (hJ : IsIrr H J)
    (hJle : J ≤ I ⊔ I') (h : HIso H J I) : J = I := by
  let S : Set (Submodule (ZMod 2) V) := {K | IsIrr H K ∧ ¬ HIso H K I}
  have hbot := homComp_inf_eq_bot hI S (fun K hK => hK.1) (fun K hK => hK.2)
  have hJI : J ≤ I := by
    intro j hj
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hJle hj)
    have hb1 : b ∈ homComp H I := by
      have h1 : a + b ∈ homComp H I := le_homComp_of_hiso hJ h hj
      have h2 : a ∈ homComp H I := le_homComp hI ha
      have : b = (a + b) - a := by abel
      rw [this]
      exact (homComp H I).sub_mem h1 h2
    have hb2 : b ∈ sSup S := le_sSup (show I' ∈ S from ⟨hI', hn⟩) hb
    have : b ∈ homComp H I ⊓ sSup S := ⟨hb1, hb2⟩
    rw [hbot, Submodule.mem_bot] at this
    rw [this, add_zero]
    exact ha
  rcases hI.eq_bot_or_eq hJ.1 hJI with h0 | h0
  · exact absurd h0 hJ.ne_bot
  · exact h0

namespace G108Hyp

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} (hyp : G108Hyp B Γ v₁ W X X₀ L)

include hyp

theorem le_of_le_sup_conj {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {U : Submodule (ZMod 2) V}
    (hU : Invariant (normalClosure Γ L) U) (hUle : U ≤ I ⊔ conjSub x I) (hU0 : U ≠ ⊥) :
    I ≤ U ∨ conjSub x I ≤ U := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hirr' : IsIrr (normalClosure Γ L) (conjSub x I) :=
    hirr.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  have hn : ¬ HIso (normalClosure Γ L) I (conjSub x I) := fun h => hne (hfix x hx h)
  have hn' : ¬ HIso (normalClosure Γ L) (conjSub x I) I := fun h =>
    hn (hiso_symm hirr'.1 hirr.1 h)
  obtain ⟨J, hJU, hJ⟩ := exists_isIrr_le hU hU0
  have hJle : J ≤ sSup {I, conjSub x I} := by
    rw [sSup_pair]
    exact hJU.trans hUle
  obtain ⟨K, hK, hJK⟩ := irr_le_sSup hJ (S := {I, conjSub x I}) (fun K hK => by
    rcases hK with rfl | rfl
    · exact hirr
    · exact hirr') hJle
  rcases hK with rfl | rfl
  · left
    have := eq_of_hiso_of_le_sup hirr hirr' hn' hJ (by rw [← sSup_pair]; exact hJle) hJK
    rw [← this]
    exact hJU
  · right
    have := eq_of_hiso_of_le_sup hirr' hirr hn hJ (by rw [sup_comm, ← sSup_pair]; exact hJle) hJK
    rw [← this]
    exact hJU

theorem no_irrPlus_contains (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {J : Submodule (ZMod 2) V}
    (hJ : IrrPlus (normalClosure Γ L) J) : v₁ ∉ J := by
  intro hv
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hJirr : IsIrr (normalClosure Γ L) J := hJ.isIrr hyp.fixedSpace_H
  have hXJ : Invariant X J := (h11 J hJ).2 hv
  obtain ⟨i, hiI, hi0, hvd, -⟩ := hyp.exists_decomp h10 hI hfix hx hne
  have hvsup : v₁ ∈ I ⊔ conjSub x I := by
    rw [hvd]
    exact Submodule.add_mem_sup hiI (apply_mem_conjSub hiI)
  have hU : Invariant (normalClosure Γ L) (J ⊓ (I ⊔ conjSub x I)) :=
    hJ.1.inf (hI.1.sup (hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)))
  have hU0 : J ⊓ (I ⊔ conjSub x I) ≠ ⊥ := by
    intro h
    have : v₁ ∈ J ⊓ (I ⊔ conjSub x I) := ⟨hv, hvsup⟩
    rw [h, Submodule.mem_bot] at this
    exact hyp.point this
  have hIJ : I ≤ J := by
    rcases hyp.le_of_le_sup_conj hI hfix hx hne hU inf_le_right hU0 with h | h
    · exact h.trans inf_le_left
    · have h1 : conjSub x (conjSub x I) ≤ conjSub x J :=
        conjSub_mono x (h.trans inf_le_left)
      rw [conjSub_conjSub_of_sq (hyp.X_sq x hx), hXJ.conjSub_eq hx] at h1
      exact h1
  rcases hJirr.eq_bot_or_eq hI.1 hIJ with h0 | h0
  · exact hirr.ne_bot h0
  · apply hne
    have : Invariant X I := h0 ▸ hXJ
    exact this.conjSub_eq hx

theorem centralizer_X_eq_one (h10 : G1010Concl Γ v₁ X L) (h11 : G1011Concl Γ v₁ X L)
    (h12 : G1012Concl Γ v₁ W X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {y : GLV V} (hy : y ∈ X)
    (hc : ∀ h ∈ normalClosure Γ L, y * h = h * y) : y = 1 := by
  have hyc : ∀ h ∈ normalClosure Γ L, ∀ v, y (h v) = h (y v) := fun h hh v =>
    congrArg (fun g : GLV V => g v) (hc h hh)
  refine hyp.eq_one_of_fixes_irrPlus fun J hJ u hu => ?_
  by_contra hcon
  have hJirr : IsIrr (normalClosure Γ L) J := hJ.isIrr hyp.fixedSpace_H
  let ρ : V →ₗ[ZMod 2] V := (y : V →ₗ[ZMod 2] V) + LinearMap.id
  have hρ : ∀ v, ρ v = y v + v := fun v => rfl
  have hρu : ρ u ≠ 0 := by
    intro h0
    apply hcon
    have h1 : y u + u = 0 := h0
    have h2 : y u = -u := eq_neg_of_add_eq_zero_left h1
    rw [h2]
    exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 u)
  have hρinv : ∀ h ∈ normalClosure Γ L, ∀ v, ρ (h v) = h (ρ v) := fun h hh v => by
    rw [hρ, hρ, map_add, hyc h hh v]
  have hinj : ∀ v ∈ J, ρ v = 0 → v = 0 := by
    have hJ₀ : Invariant (normalClosure Γ L) (J ⊓ LinearMap.ker ρ) := by
      refine hJ.1.inf ?_
      intro h hh v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hρinv h hh, hv, map_zero]
    rcases hJirr.eq_bot_or_eq hJ₀ inf_le_left with h0 | h0
    · intro v hv hρv
      have : v ∈ J ⊓ LinearMap.ker ρ := ⟨hv, hρv⟩
      rw [h0, Submodule.mem_bot] at this
      exact this
    · exfalso
      have : u ∈ J ⊓ LinearMap.ker ρ := by rw [h0]; exact hu
      exact hρu this.2
  let N : Submodule (ZMod 2) V := J.map ρ
  have hNinv : Invariant (normalClosure Γ L) N := by
    rintro h hh _ ⟨j, hj, rfl⟩
    exact ⟨h j, hJ.1 h hh j hj, hρinv h hh j⟩
  have hNirr : IsIrr (normalClosure Γ L) N := by
    refine ⟨hNinv, bot_lt_iff_ne_bot.2 fun h0 => hρu ?_, fun N' hN' _ hN'N => ?_⟩
    · have : ρ u ∈ N := ⟨u, hu, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact this
    · have hJ' : Invariant (normalClosure Γ L) (J ⊓ N'.comap ρ) := by
        refine hJ.1.inf ?_
        intro h hh v hv
        show ρ (h v) ∈ N'
        rw [hρinv h hh]
        exact hN' h hh _ hv
      rcases hJirr.eq_bot_or_eq hJ' inf_le_left with h0 | h0
      · left
        rw [eq_bot_iff]
        intro n hn
        obtain ⟨j, hj, rfl⟩ := hN'N hn
        have : j ∈ J ⊓ N'.comap ρ := ⟨hj, hn⟩
        rw [h0, Submodule.mem_bot] at this
        rw [this, map_zero]
        exact Submodule.zero_mem _
      · right
        refine le_antisymm hN'N ?_
        rintro _ ⟨j, hj, rfl⟩
        have : j ∈ J ⊓ N'.comap ρ := by rw [h0]; exact hj
        exact this.2
  have hNI : IrrPlus (normalClosure Γ L) N := hNirr.irrPlus hyp.fixedSpace_H
  have hvN : v₁ ∉ N := hyp.no_irrPlus_contains h10 h11 hI hfix hx hne hNI
  have hfin := (h12 N hNI hvN).1
  have hT : 2 ≤ Module.finrank (ZMod 2) ↥(J ⊓ perp B v₁) := by
    have h1 := finrank_le_finrank_inf_perp_add_one hyp.toG101Hyp.nondegenerate' hyp.point J
    have h2 := hyp.two_lt_finrank hJirr
    omega
  have hρT : Function.Injective (ρ.domRestrict (J ⊓ perp B v₁)) := by
    intro a b hab
    apply Subtype.ext
    have h1 : ρ (a : V) = ρ (b : V) := hab
    have h2 : ρ ((a : V) + (b : V)) = 0 := by
      rw [map_add, h1]
      exact add_self_eq_zero_of_zmod2 _
    have h3 : (a : V) + (b : V) = 0 := hinj _ (J.add_mem a.2.1 b.2.1) h2
    have : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left h3
    rw [this]
    exact neg_eq_of_add_eq_zero_left (add_self_eq_zero_of_zmod2 _)
  have hrange : LinearMap.range (ρ.domRestrict (J ⊓ perp B v₁)) ≤ N ⊓ W := by
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨t, t.2.1, rfl⟩, hyp.phi_mem_W hy t.2.2⟩
  have h1 : Module.finrank (ZMod 2) ↥(J ⊓ perp B v₁) = Module.finrank (ZMod 2) ↥(LinearMap.range (ρ.domRestrict (J ⊓ perp B v₁))) :=
    LinearEquiv.finrank_eq (LinearEquiv.ofInjective (ρ.domRestrict (J ⊓ perp B v₁)) hρT)
  have h2 := Submodule.finrank_mono hrange
  omega

theorem conj_mem_pair {I : Submodule (ZMod 2) V} (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {y : GLV V} (hy : y ∈ X) {M : Submodule (ZMod 2) V}
    (hM : M = I ∨ M = conjSub x I) : conjSub y M = I ∨ conjSub y M = conjSub x I := by
  have hperm := hyp.permutes hI hfix hx hne
  have hxx : conjSub x (conjSub x I) = I := conjSub_conjSub_of_sq (hyp.X_sq x hx) I
  have hcomm : conjSub y (conjSub x I) = conjSub x (conjSub y I) :=
    (conjSub_comm (hyp.X_comm x hx y hy) I).symm
  rcases hM with rfl | rfl
  · exact hperm y hy
  · rw [hcomm]
    rcases hperm y hy with h | h
    · rw [h]
      exact Or.inr rfl
    · rw [h, hxx]
      exact Or.inl rfl

theorem hiso_or_hiso_of_isIrr (h10 : G1010Concl Γ v₁ X L) {I : Submodule (ZMod 2) V}
    (hI : IrrPlus (normalClosure Γ L) I)
    (hfix : ∀ z ∈ X, HIso (normalClosure Γ L) I (conjSub z I) → conjSub z I = I) {x : GLV V}
    (hx : x ∈ X) (hne : conjSub x I ≠ I) {J : Submodule (ZMod 2) V}
    (hJ : IsIrr (normalClosure Γ L) J) :
    HIso (normalClosure Γ L) J I ∨ HIso (normalClosure Γ L) J (conjSub x I) := by
  have hirr : IsIrr (normalClosure Γ L) I := hI.isIrr hyp.fixedSpace_H
  have hirr' : IsIrr (normalClosure Γ L) (conjSub x I) :=
    hirr.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx)
  by_contra hcon
  push Not at hcon
  let S₂ : Set (Submodule (ZMod 2) V) := {K | IsIrr (normalClosure Γ L) K ∧
    ¬ HIso (normalClosure Γ L) K I ∧ ¬ HIso (normalClosure Γ L) K (conjSub x I)}
  have hDH : Invariant (normalClosure Γ L) (sSup S₂) := invariant_sSup fun K hK => hK.1.1
  have hXD : Invariant X (sSup S₂) := by
    rw [invariant_iff_conjSub_le]
    intro y hy
    rw [conjSub_sSup]
    refine sSup_le ?_
    rintro _ ⟨K, hK, rfl⟩
    have hyirr : IsIrr (normalClosure Γ L) (conjSub y K) :=
      hK.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hy)
    have key : ∀ M : Submodule (ZMod 2) V, (M = I ∨ M = conjSub x I) →
        HIso (normalClosure Γ L) (conjSub y K) M → HIso (normalClosure Γ L) K (conjSub y⁻¹ M) := by
      intro M _ hiso
      have h1 := hiso_conj (normalClosure_normal Γ L) (hyp.X_le (X.inv_mem hy)) hiso
      rwa [conjSub_inv_conjSub] at h1
    refine le_sSup ⟨hyirr, fun hiso => ?_, fun hiso => ?_⟩
    · have h1 := key I (Or.inl rfl) hiso
      rcases hyp.conj_mem_pair hI hfix hx hne (X.inv_mem hy) (Or.inl rfl : I = I ∨ I = conjSub x I)
        with h | h
      · rw [h] at h1
        exact hK.2.1 h1
      · rw [h] at h1
        exact hK.2.2 h1
    · have h1 := key (conjSub x I) (Or.inr rfl) hiso
      rcases hyp.conj_mem_pair hI hfix hx hne (X.inv_mem hy)
        (Or.inr rfl : conjSub x I = I ∨ conjSub x I = conjSub x I) with h | h
      · rw [h] at h1
        exact hK.2.1 h1
      · rw [h] at h1
        exact hK.2.2 h1
  have hDHX : Invariant (normalClosure Γ L ⊔ X) (sSup S₂) := hDH.sup_subgroup hXD
  obtain ⟨i, hiI, hi0, hvd, -⟩ := hyp.exists_decomp h10 hI hfix hx hne
  have hvsup : v₁ ∈ I ⊔ conjSub x I := by
    rw [hvd]
    exact Submodule.add_mem_sup hiI (apply_mem_conjSub hiI)
  have hD0 : sSup S₂ = ⊥ := by
    by_contra hne0
    have hvD : v₁ ∈ sSup S₂ := (h10 _ hne0 hDHX).1
    have hint : (I ⊔ conjSub x I) ⊓ sSup S₂ = ⊥ := by
      by_contra hne1
      have hinv : Invariant (normalClosure Γ L) ((I ⊔ conjSub x I) ⊓ sSup S₂) :=
        (hI.1.sup (hI.1.conj_of_normal (normalClosure_normal Γ L) (hyp.X_le hx))).inf hDH
      rcases hyp.le_of_le_sup_conj hI hfix hx hne hinv inf_le_left hne1 with h | h
      · have h2 : I ≤ sSup S₂ := h.trans inf_le_right
        obtain ⟨K, hK, hIK⟩ := irr_le_sSup hirr (fun K hK => hK.1) h2
        exact hK.2.1 (hiso_symm hirr.1 hK.1.1 hIK)
      · have h2 : conjSub x I ≤ sSup S₂ := h.trans inf_le_right
        obtain ⟨K, hK, hIK⟩ := irr_le_sSup hirr' (fun K hK => hK.1) h2
        exact hK.2.2 (hiso_symm hirr'.1 hK.1.1 hIK)
    have : v₁ ∈ (I ⊔ conjSub x I) ⊓ sSup S₂ := ⟨hvsup, hvD⟩
    rw [hint, Submodule.mem_bot] at this
    exact hyp.point this
  have hJS : J ∈ S₂ := ⟨hJ, hcon.1, hcon.2⟩
  have : J ≤ sSup S₂ := le_sSup hJS
  rw [hD0, le_bot_iff] at this
  exact hJ.ne_bot this

end G108Hyp

end G11

end CFSG.Quasithin
