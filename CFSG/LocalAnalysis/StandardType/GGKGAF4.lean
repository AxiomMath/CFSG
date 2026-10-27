module

public import CFSG.LocalAnalysis.StandardType.GGKGAF4Defs
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Self
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Witness
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Rank
public import CFSG.LocalAnalysis.StandardType.GGKGAF4AutCard
public import CFSG.LocalAnalysis.StandardType.GGKGAF4Aut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace KGA

theorem ggTorusAutCardSCF4_of_facts
    (hRig : GGLabelRigidInput) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ (2 ^ f) ^ 2 - 1) (hf : 1 ≤ f) {R : Type} [Group R] {I : Set (MulAut R)}
    (hsimple : IsSimpleGroup R) (hnab : ∃ a b : R, a * b ≠ b * a)
    (hF4 : GGHasLabel ⟨.F4, 4, f⟩ R) (hI : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (hcent : GGF4CentAt p f R I) (hAO : GGF4AutOrderAt p R) :
    GGTorusAutCardSCF4 p f R I 4 1152 := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ hsc hex
  haveI := hsimple
  have h4 : p ^ 4 ≤ Nat.card A :=
    ggF4_card_ge_pow_four hRig hp hp2 hpq hf hnab hF4 hcent ψ hψ hker hperf A hA hAI hsc hex
  have hZ : Subgroup.center R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  exact ⟨h4, ggF4_transport hZ hI hAO ψ hψ hker hperf A hA hAI h4⟩

theorem ggPumpCAutKnownF4_of_cent
    (hRig : GGLabelRigidInput) (hC : GGF4C3CentInputStrong) :
    GGPumpCAutKnownF4 := by
  intro p hp hp2 f hf hpq
  have h12 := largeEvenLabelAll_and (hC p hp hp2 f hf) (ggF4_basics_label (f := f))
  have h123 := largeEvenLabelAll_and h12 (ggF4_autOrder_label hp hp2)
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ (h123 Q hQ)
  rintro R _ I F ⟨hq, ⟨hcent, hsimple, hnab, hF4, hI⟩, hAO⟩
  exact ⟨hq, ggTorusAutCardSCF4_of_facts hRig hp hp2 hpq hf hsimple hnab hF4 hI hcent hAO⟩

end KGA

end CFSG.StandardType

end
