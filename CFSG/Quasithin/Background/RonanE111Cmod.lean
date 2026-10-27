module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.EmptyFaithful.E111RDiag

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {Q : Type} [Group Q]

@[expose] def Cmod (S Y : Subgroup Q) [Y.Normal] : Subgroup Q :=
  (Subgroup.centralizer ((S.map (QuotientGroup.mk' Y) : Subgroup (Q ⧸ Y)) : Set (Q ⧸ Y))).comap
    (QuotientGroup.mk' Y)

theorem mem_Cmod_iff {S Y : Subgroup Q} [Y.Normal] {x : Q} :
    x ∈ Cmod S Y ↔ ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ Y := by
  rw [Cmod, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h s hs
    have h1 := h (QuotientGroup.mk' Y s) ⟨s, hs, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' Y (x * s * x⁻¹ * s⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [← h1]
    group
  · rintro h _ ⟨s, hs, rfl⟩
    have h1 : QuotientGroup.mk' Y (x * s * x⁻¹ * s⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (h s hs)
    simp only [map_mul, map_inv] at h1
    have h2 := congrArg (fun z => z * QuotientGroup.mk' Y s * QuotientGroup.mk' Y x) h1
    simpa [mul_assoc] using h2.symm

section Cent

variable {Y D : Subgroup Q} [Y.Normal]

@[expose] def centMod (D Y : Subgroup Q) [Y.Normal] : Subgroup (Q ⧸ Y) :=
  Subgroup.centralizer ((D.map (QuotientGroup.mk' Y) : Subgroup (Q ⧸ Y)) : Set (Q ⧸ Y))

theorem centMod_normal [hD : D.Normal] : (centMod D Y).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hDn : (D.map (QuotientGroup.mk' Y)).Normal :=
    Subgroup.Normal.map hD _ (QuotientGroup.mk'_surjective Y)
  rw [centMod, Subgroup.mem_centralizer_iff] at hx ⊢
  intro d hd
  have h1 := hx (g⁻¹ * d * g⁻¹⁻¹) (hDn.conj_mem d hd g⁻¹)
  calc d * (g * x * g⁻¹) = g * ((g⁻¹ * d * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * d * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
    _ = (g * x * g⁻¹) * d := by group

instance centMod_normal' [D.Normal] : (centMod D Y).Normal := centMod_normal

end Cent

end CFSG.Quasithin.RonanE111
