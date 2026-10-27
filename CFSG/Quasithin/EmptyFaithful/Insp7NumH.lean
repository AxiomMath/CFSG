module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumF

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.ComponentClassification.PerfectAutomorphisms

namespace Insp7

theorem numFactAt_cover {F G' : ∀ (L : Type) [Group L], Prop}
    (hF : ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → F L →
      G' (L ⧸ Subgroup.center L))
    (hG : NumFactAt G') : NumFactAt F := by
  intro L _ _ hq hFL z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  have hperf : Group.IsPerfect L := hq.1
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hqb : CFSG.IsQuasisimple (L ⧸ Subgroup.center L) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hq.2.2).1
  let ρb : Gc →* MulAut (L ⧸ Subgroup.center L) := (centerQuotientHom L).comp ρ
  have hρb : Function.Injective ρb := (centerQuotientHom_injective L).comp hρ
  have hconj : ∀ l : L, MulAut.conj (QuotientGroup.mk l : L ⧸ Subgroup.center L) =
      centerQuotientHom L (MulAut.conj l) := by
    intro l
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    show (QuotientGroup.mk l : L ⧸ Subgroup.center L) * QuotientGroup.mk x *
        (QuotientGroup.mk l)⁻¹ = (centerQuotientHom L (MulAut.conj l)) (QuotientGroup.mk x)
    have := onCenterQuotient_apply_mk (MulAut.conj l) x
    simp only [QuotientGroup.mk'_apply] at this
    show _ = onCenterQuotient (MulAut.conj l) (QuotientGroup.mk x)
    rw [this]
    simp [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hinnb : ∀ l : L ⧸ Subgroup.center L, MulAut.conj l ∈ ρb.range := by
    intro l
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
    obtain ⟨g, hg⟩ := hinn l
    exact ⟨g, by simp only [ρb, MonoidHom.comp_apply, hg, hconj]⟩
  have hžb : ρb ž = MulAut.conj (QuotientGroup.mk z : L ⧸ Subgroup.center L) := by
    simp only [ρb, MonoidHom.comp_apply, hž, hconj]
  have hz2b : (QuotientGroup.mk z : L ⧸ Subgroup.center L) * QuotientGroup.mk z = 1 := by
    rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
  have hcenterb : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
    rcases (Subgroup.center (L ⧸ Subgroup.center L)).normal_of_characteristic.eq_bot_or_eq_top
      with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hqb.2.2
      apply hab
      have : Subsingleton ((L ⧸ Subgroup.center L) ⧸
          Subgroup.center (L ⧸ Subgroup.center L)) := by
        rw [h0]; exact QuotientGroup.subsingleton_quotient_top
      exact Subsingleton.elim _ _
  have hzcb : (QuotientGroup.mk z : L ⧸ Subgroup.center L) ∉
      Subgroup.center (L ⧸ Subgroup.center L) := by
    rw [hcenterb, Subgroup.mem_bot]
    intro h1
    exact hzc ((QuotientGroup.eq_one_iff z).mp h1)
  exact hG (L ⧸ Subgroup.center L) hqb (hF L hq hFL) _ hz2b hzcb Gc ρb hρb hinnb ž hžb Ŝ hŜ2
    hŜodd hŜC hcard

@[expose] def SmallSimple (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 2 2 ∨ StatedClassicalModel L .PSU 3 2 2 ∨
    StatedClassicalModel L .PSp 2 2 2 ∨ StatedClassicalModel L .PSL 4 2 1 ∨
    Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel L .PSU 3 3 1 ∨
    SuzukiModel L 2 3

theorem numFactAt_coverL34 (h : NumFactAt (fun L _ => StatedClassicalModel L .PSL 3 2 2)) :
    NumFactAt (fun L _ => Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
      StatedClassicalModel (L ⧸ CFSG.pCore 2 L) .PSL 3 2 2) :=
  numFactAt_cover (G' := fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (fun L _ _ _ ⟨_, hc, hm⟩ => by
      obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e'⟩⟩ := hm
      exact ⟨hadm, K, hKf, hKfin, hK, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e'⟩⟩) h

theorem numFactAt_smallRest (hS : NumFactAt SmallSimple) : NumFactAt SmallRest :=
  numFactAt_of_cover (G := SmallSimple)
    (H := fun L _ => Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
      StatedClassicalModel (L ⧸ CFSG.pCore 2 L) .PSL 3 2 2)
    (fun L _ h => by
      unfold SmallRest at h
      unfold SmallSimple
      tauto) hS
    (numFactAt_coverL34 (numFactAt_of_cover (G := SmallSimple) (H := SmallSimple)
      (fun L _ h => Or.inl (by unfold SmallSimple; tauto)) hS hS))

theorem lemma14320Inspect_of_simple
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hS : NumFactAt SmallSimple) (hT : NumFactAt LargeReeTits) (hO : NumFactAt L33Fam)
    (hP : NumFactAt SporSmall) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_small hbig (numFactAt_smallRest hS) hT hO hP

end Insp7

end CFSG.Quasithin
