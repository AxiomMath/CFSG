module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.Defs

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

theorem exists_mulEquiv_of_cover_odd {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (hodd : Odd (Nat.card (Subgroup.center L)))
    {S : Type} [Group S] (e : (L ⧸ Subgroup.center L) ≃* S)
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    ∃ f : L ≃* S, ∀ l : L, f l = e (QuotientGroup.mk l) := by
  let ρ : L →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hρsurj : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff, ← QuotientGroup.eq_one_iff]
  have : Group.IsPerfect L := ⟨hq.1⟩
  have hker1 : ρ.ker = ⊥ := hCover L ρ hρsurj (by rw [hker]) (by rw [hker]; exact hodd)
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff _).1 hker1
  exact ⟨MulEquiv.ofBijective ρ ⟨hinj, hρsurj⟩, fun l => rfl⟩

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
