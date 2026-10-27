module

public import CFSG.Quasithin.Background.A1cModuleBridge

public section

namespace CFSG.Quasithin

open scoped Pointwise

namespace Z3A1

variable {V : Type} [CommGroup V] {D X : Subgroup (MulAut V)}

theorem isInv_iff {I : Subgroup V} :
    XMod.IsInv ↥D I ↔ ∀ y ∈ D, ∀ v ∈ I, y v ∈ I :=
  ⟨fun h y hy v hv => h ⟨y, hy⟩ v hv, fun h a v hv => h a a.2 v hv⟩

theorem isIrr_iff {I : Subgroup V} :
    XMod.IsIrr ↥D I ↔ I ≠ ⊥ ∧ (∀ y ∈ D, ∀ v ∈ I, y v ∈ I) ∧
      ∀ U ≤ I, (∀ y ∈ D, ∀ v ∈ U, y v ∈ U) → U = ⊥ ∨ U = I := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨bot_lt_iff_ne_bot.mp h2, isInv_iff.mp h1,
      fun U hU hUD => h3 U (isInv_iff.mpr hUD) bot_le hU⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨isInv_iff.mpr h2, bot_lt_iff_ne_bot.mpr h1,
      fun U hU _ hUI => h3 U hUI (isInv_iff.mp hU)⟩

theorem normalizes_of_comm (h : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g) :
    XMod.Normalizes ↥D ↥X V := by
  intro t a
  refine ⟨a, fun q => ?_⟩
  have := congrArg (fun f : MulAut V => f q) (h a a.2 t t.2)
  change (t : MulAut V) ((a : MulAut V) q) = (a : MulAut V) ((t : MulAut V) q)
  simpa using this.symm

theorem normalizes_of_conj {A : Subgroup (MulAut V)} (h : ∀ a ∈ A, ∀ y ∈ D, a * y * a⁻¹ ∈ D) :
    XMod.Normalizes ↥D ↥A V := by
  intro t a
  refine ⟨⟨(t : MulAut V) * (a : MulAut V) * (t : MulAut V)⁻¹, h t t.2 a a.2⟩, fun q => ?_⟩
  change (t : MulAut V) ((a : MulAut V) q) =
    ((t : MulAut V) * (a : MulAut V) * (t : MulAut V)⁻¹) ((t : MulAut V) q)
  simp

theorem isIrr_smul {T : Type*} [Group T] [MulDistribMulAction T V]
    (h : XMod.Normalizes ↥D T V) (t : T) {L : Subgroup V} (hL : XMod.IsIrr ↥D L) :
    XMod.IsIrr ↥D (t • L) := by
  refine ⟨XMod.isInv_smul_of_normalizes h t hL.1, ?_, ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    have h1 : L = ⊥ := by
      have := congrArg (fun J => t⁻¹ • J) h0
      simpa [smul_smul, Subgroup.smul_bot] using this
    exact hL.2.1.ne' h1
  · intro J hJ _ hJL
    have hJ' : XMod.IsInv ↥D (t⁻¹ • J) := XMod.isInv_smul_of_normalizes h t⁻¹ hJ
    have hle : t⁻¹ • J ≤ L := by
      have := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t⁻¹)).2 hJL
      simpa [inv_smul_smul] using this
    have hJeq : J = t • (t⁻¹ • J) := by rw [smul_inv_smul]
    rcases hL.2.2 (t⁻¹ • J) hJ' bot_le hle with h1 | h1
    · left
      rw [hJeq, h1, Subgroup.smul_bot]
    · right
      rw [hJeq, h1]

theorem exists_iso_of_le_iSup_smul {T : Type*} [Group T] [MulDistribMulAction T V]
    (h : XMod.Normalizes ↥D T V) {S J : Subgroup V} (hS : XMod.IsIrr ↥D S)
    (hJ : XMod.IsIrr ↥D J) (hle : J ≤ ⨆ t : T, t • S) : ∃ t : T, XMod.Iso ↥D J (t • S) := by
  let _ := XMod.twistAction h
  have hinv : ∀ t : T, XMod.IsInv ↥D (t • S) := fun t => XMod.isInv_smul_of_normalizes h t hS.1
  have hP : XMod.IsInv ↥D (⨆ t : T, t • S) := XMod.isInv_iSup hinv
  have h1 : XMod.toSubmod hJ.1 ≤ ⨆ t : T, XMod.toSubmod (hinv t) := by
    rw [← XMod.toSubmod_iSup hinv]
    exact (XMod.toSubmod_le_iff (hL := hJ.1) (hL' := hP)).2 hle
  rw [← sSup_range] at h1
  have hsimple : ∀ m : ↥(Set.range fun t : T => XMod.toSubmod (hinv t)),
      IsSimpleModule ↥(XMod.opRing ↥D V) ↥(m : Submodule ↥(XMod.opRing ↥D V) (Additive V)) := by
    rintro ⟨_, t, rfl⟩
    exact (XMod.isIrr_iff (hinv t)).1 (isIrr_smul h t hS)
  have hVs : IsSimpleModule ↥(XMod.opRing ↥D V) ↥(XMod.toSubmod hJ.1) :=
    (XMod.isIrr_iff hJ.1).1 hJ
  obtain ⟨S', ⟨t, rfl⟩, ⟨e⟩⟩ := Submodule.linearEquiv_of_le_sSup (XMod.toSubmod hJ.1) _ h1
  exact ⟨t, (XMod.iso_iff hJ.1 (hinv t)).2 ⟨e⟩⟩

theorem iso_smul_of_comm (h : ∀ g ∈ D, ∀ x ∈ X, g * x = x * g) (t : ↥X) (L : Subgroup V) :
    XMod.Iso ↥D L (t • L) := by
  refine ⟨XMod.smulEquiv t L, fun a l l' hl => ?_⟩
  have h1 : (a : MulAut V) ((t : MulAut V) (l : V)) = (t : MulAut V) ((a : MulAut V) (l : V)) := by
    have := congrArg (fun f : MulAut V => f (l : V)) (h a a.2 t t.2)
    simpa using this
  change (a : MulAut V) ((t : MulAut V) (l : V)) = (t : MulAut V) (l' : V)
  rw [h1]
  exact congrArg (fun w : V => (t : MulAut V) w) hl

end Z3A1

end CFSG.Quasithin
