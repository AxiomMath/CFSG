module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumH


public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def SporSimple (L : Type) [Group L] : Prop :=
  ∃ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) ∧
    Nonempty (L ≃* NativeSporadic.Carrier s)

theorem center_eq_pCore_of_simple_quotient {L : Type} [Group L] [Finite L] (hq : CFSG.IsQuasisimple L)
    {X : Type} [Group X] (hX : IsSimpleGroup X) (e : (L ⧸ CFSG.pCore 2 L) ≃* X) :
    Subgroup.center L = CFSG.pCore 2 L := by
  have hQZ : CFSG.pCore 2 L ≤ Subgroup.center L := pCore_le_center_of_quasisimple hq
  have hsimple : IsSimpleGroup (L ⧸ CFSG.pCore 2 L) := e.isSimpleGroup_congr.mpr hX
  refine le_antisymm ?_ hQZ
  have hN : ((Subgroup.center L).map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hN.eq_bot_or_eq_top with h0 | h0
  · intro x hx
    have : (QuotientGroup.mk' (CFSG.pCore 2 L)) x ∈
        (Subgroup.center L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · exfalso
    have hall : ∀ x : L, x ∈ Subgroup.center L := by
      intro x
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 L)) x ∈
          (Subgroup.center L).map (QuotientGroup.mk' (CFSG.pCore 2 L)) := by rw [h0]; trivial
      obtain ⟨y, hy, hxy⟩ := hmem
      have : y⁻¹ * x ∈ CFSG.pCore 2 L := by
        rw [← QuotientGroup.eq_one_iff]
        simp only [QuotientGroup.mk'_apply] at hxy
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hxy, inv_mul_cancel]
      have h3 : y⁻¹ * x ∈ Subgroup.center L := hQZ this
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ hy h3
    obtain ⟨a, b, hab⟩ := hq.2.2
    apply hab
    have : Subsingleton (L ⧸ Subgroup.center L) := by
      have htop : Subgroup.center L = ⊤ := eq_top_iff.mpr fun x _ => hall x
      rw [htop]; exact QuotientGroup.subsingleton_quotient_top
    exact Subsingleton.elim _ _

theorem numFactAt_sporSmall
    (hsimple : ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (h : NumFactAt SporSimple) : NumFactAt SporSmall :=
  numFactAt_cover (G' := SporSimple)
    (fun L _ _ hq ⟨s, hs, ⟨e⟩⟩ => by
      have hc := center_eq_pCore_of_simple_quotient hq (hsimple s hs) e
      exact ⟨s, hs, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e⟩⟩) h

theorem lemma14320Inspect_of_simple_groups
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallSimple) (hT : NumFactAt LargeReeTits) (hO : NumFactAt L33Fam)
    (hP : NumFactAt SporSimple) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_simple hbig hS hT hO (numFactAt_sporSmall hsimple hP)

end Insp7

end CFSG.Quasithin
