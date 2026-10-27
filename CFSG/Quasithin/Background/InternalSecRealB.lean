module

public import CFSG.Quasithin.Background.InternalSecReal
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Bridge

section LeAutSec

variable {V : Type} [CommGroup V] {X : Subgroup (MulAut V)} {C : Subgroup V}

theorem realizes_of_le_autSec (hX : X ≤ stabSub C) (hfX : X ⊓ centSec ⊤ C = ⊥)
    {H' : Subgroup (MulAut (Sec ⊤ C))} (hH' : H' ≤ autSec X ⊤ C) {D : FFModel}
    (h : D.Realizes H' ⊤ ⊥) :
    ∃ H : Subgroup (MulAut V), H ≤ X ∧ autSec H ⊤ C = H' ∧ D.Realizes H ⊤ C := by
  have hXs : X ≤ stabSub ⊤ ⊓ stabSub C := fun g hg => ⟨mem_stabSub_top g, hX hg⟩
  set H : Subgroup (MulAut V) :=
    ((H'.subgroupOf (autSec X ⊤ C)).comap (secRestrict hXs)).map X.subtype with hHdef
  have hHX : H ≤ X := Subgroup.map_subtype_le _
  have hHs : H ≤ stabSub ⊤ ⊓ stabSub C := hHX.trans hXs
  have hmemH : ∀ g : ↥(stabSub ⊤ ⊓ stabSub C), (g : MulAut V) ∈ H ↔
      (g : MulAut V) ∈ X ∧ secHom ⊤ C g ∈ H' := by
    intro g
    constructor
    · rintro ⟨x, hx, hxg⟩
      have hx' : secHom ⊤ C (Subgroup.inclusion hXs x) ∈ H' := hx
      have he : Subgroup.inclusion hXs x = g := Subtype.ext hxg
      rw [he] at hx'
      exact ⟨hxg ▸ x.2, hx'⟩
    · rintro ⟨hgX, hgH⟩
      refine ⟨⟨g, hgX⟩, ?_, rfl⟩
      show secHom ⊤ C (Subgroup.inclusion hXs ⟨g, hgX⟩) ∈ H'
      have he : Subgroup.inclusion hXs ⟨(g : MulAut V), hgX⟩ = g := Subtype.ext rfl
      rw [he]
      exact hgH
  have hAut : autSec H ⊤ C = H' := by
    ext ψ
    rw [mem_autSec_iff_secHom hHs]
    constructor
    · rintro ⟨g, hgH, rfl⟩
      exact ((hmemH g).1 hgH).2
    · intro hψ
      obtain ⟨g, hgX, rfl⟩ := (mem_autSec_iff_secHom hXs).1 (hH' hψ)
      exact ⟨g, (hmemH g).2 ⟨hgX, hψ⟩, rfl⟩
  have hfH : H ⊓ centSec ⊤ C = ⊥ := le_bot_iff.1 (hfX ▸ inf_le_inf_right _ hHX)
  have h' : D.Realizes (autSec H ⊤ C) ⊤ ⊥ := by rw [hAut]; exact h
  exact ⟨H, hHX, hAut, realizes_of_autSec (hHX.trans hX) hfH h'⟩

end LeAutSec

section Equiv

variable {V : Type} [CommGroup V] {K : Subgroup (MulAut V)} {C : Subgroup V}
  (hK : K ≤ stabSub C) (hf : K ⊓ centSec ⊤ C = ⊥)

include hK hf

theorem equiv_of_faithful_of_autSec {D : FFModel} (hD : D.Faithful)
    (h : D.Realizes (autSec K ⊤ C) ⊤ ⊥) : Nonempty (D.Gam ≃* ↥K) := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨(MulEquiv.ofBijective π ⟨hπ.injective_of_faithful hD, hπ.1⟩).trans
    (B5.secEquiv K (le_stabSub_top K) hK hf).symm⟩

theorem BinaryNaturalSL.equiv_of_autSec {d a : ℕ}
    (h : BinaryNaturalSL (autSec K ⊤ C) ⊤ ⊥ d a) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ a ∧
      Nonempty (↥(StatedSL d F) ≃* ↥K) := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

theorem BinaryNaturalSp4.equiv_of_autSec {a : ℕ}
    (h : BinaryNaturalSp4 (autSec K ⊤ C) ⊤ ⊥ a) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ a ∧
      Nonempty (↥(StatedSp 2 F) ≃* ↥K) := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

theorem BinaryNaturalSU3.equiv_of_autSec {a : ℕ}
    (h : BinaryNaturalSU3 (autSec K ⊤ C) ⊤ ⊥ a) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ a) ^ 2 ∧
      Nonempty (↥(StatedSU 3 (2 ^ a) F) ≃* ↥K) := by
  obtain ⟨F, _, _, hc, hR⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

theorem BinaryNaturalSz.equiv_of_autSec {f : ℕ} (h : BinaryNaturalSz (autSec K ⊤ C) ⊤ ⊥ f) :
    ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ a ∧ f = 2 * a + 1 ∧
      Nat.card F = 2 ^ f ∧ Nonempty (↥(CFSG.Blueprint.suzukiGroup a F) ≃* ↥K) := by
  obtain ⟨a, ha, hfa, F, _, _, hc, hR⟩ := h
  exact ⟨a, F, inferInstance, inferInstance, ha, hfa, hc,
    equiv_of_faithful_of_autSec hK hf (FFModel.nat_faithful _) hR⟩

end Equiv

end CFSG.Quasithin.InternalSec
