module

public import CFSG.Quasithin.Background.SmithD39TwoSocle
public import CFSG.Quasithin.Background.F918V2Defs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private theorem s16t3_isEqv_end_eq_one_or_id [Finite Q] {Λ : Subgroup Γ} {P : Subgroup Q}
    (hP : XMod.IsIrr ↥Λ P) (hE : Z391.EndUnitsTrivial Λ P) (θ : ↥P →* ↥P)
    (hθ : SmithD391.IsEqv Λ (P.subtype.comp θ)) :
    θ = 1 ∨ θ = MonoidHom.id ↥P := by
  by_cases h1 : θ = 1
  · exact Or.inl h1
  right
  have hker : θ.ker = ⊥ := by
    set K : Subgroup Q := θ.ker.map P.subtype with hK
    have hKinv : XMod.IsInv ↥Λ K := by
      rintro l _ ⟨k, hk, rfl⟩
      have hw : (l : Γ) • (k : Q) ∈ P := hP.1 l k k.2
      refine ⟨⟨_, hw⟩, ?_, rfl⟩
      have h2 := hθ l k ⟨_, hw⟩ rfl
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at h2
      show θ ⟨_, hw⟩ = 1
      apply Subtype.ext
      rw [h2, show θ k = 1 from hk]
      simp
    rcases hP.2.2 K hKinv bot_le (Subgroup.map_subtype_le _) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
      have : (k : Q) ∈ K := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · exfalso
      apply h1
      refine MonoidHom.ext fun v => ?_
      have : (v : Q) ∈ K := by rw [h]; exact v.2
      obtain ⟨v', hv', he⟩ := this
      rw [show v' = v from Subtype.ext he] at hv'
      exact hv'
  have hθinj : Function.Injective θ := (MonoidHom.ker_eq_bot_iff θ).1 hker
  have hθbij : Function.Bijective θ := by
    have : Finite ↥P := inferInstance
    exact ⟨hθinj, Finite.surjective_of_injective hθinj⟩
  let θe : ↥P ≃* ↥P := MulEquiv.ofBijective θ hθbij
  have hθe : θe = MulEquiv.refl _ := by
    apply hE
    intro l x y hxy
    have h2 := hθ l x y hxy
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at h2
    show l • ((θe x : ↥P) : Q) = ((θe y : ↥P) : Q)
    exact h2.symm
  refine MonoidHom.ext fun v => ?_
  change θ v = v
  have h3 : (θe : ↥P → ↥P) = (MulEquiv.refl (↥P) : ↥P → ↥P) :=
    congrArg (fun e : ↥P ≃* ↥P => (e : ↥P → ↥P)) hθe
  exact congrFun h3 v

private theorem s16t3_card_eqv_end_le_two [Finite Q] {Λ : Subgroup Γ} {P : Subgroup Q}
    (hP : XMod.IsIrr ↥Λ P) (hE : Z391.EndUnitsTrivial Λ P) :
    Nat.card {θ : ↥P →* ↥P // SmithD391.IsEqv Λ (P.subtype.comp θ)} ≤ 2 := by
  classical
  have hf : Function.Injective
      (fun θ : {θ : ↥P →* ↥P // SmithD391.IsEqv Λ (P.subtype.comp θ)} =>
        if θ.1 = 1 then (0 : Fin 2) else 1) := by
    intro a b hab
    by_cases ha : a.1 = 1
    · have hb : b.1 = 1 := by
        by_contra hb
        have hthis : (if a.1 = 1 then (0 : Fin 2) else 1) =
            (if b.1 = 1 then (0 : Fin 2) else 1) := hab
        rw [if_pos ha, if_neg hb] at hthis
        exact absurd hthis (by decide)
      exact Subtype.ext (ha.trans hb.symm)
    · have hb : b.1 ≠ 1 := by
        intro hb
        have hthis : (if a.1 = 1 then (0 : Fin 2) else 1) =
            (if b.1 = 1 then (0 : Fin 2) else 1) := hab
        rw [if_neg ha, if_pos hb] at hthis
        exact absurd hthis (by decide)
      rcases s16t3_isEqv_end_eq_one_or_id hP hE a.1 a.2 with h | h
      · exact absurd h ha
      · rcases s16t3_isEqv_end_eq_one_or_id hP hE b.1 b.2 with h' | h'
        · exact absurd h' hb
        · exact Subtype.ext (h.trans h'.symm)
  calc Nat.card {θ : ↥P →* ↥P // SmithD391.IsEqv Λ (P.subtype.comp θ)}
      ≤ Nat.card (Fin 2) := Nat.card_le_card_of_injective _ hf
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]

theorem s16t3_card_end_eq_two_of_endUnits [Finite Q] {Λ : Subgroup Γ} {P : Subgroup Q}
    (hP : XMod.IsIrr ↥Λ P) (hE : Z391.EndUnitsTrivial Λ P) :
    Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hP.1)) = 2 := by
  haveI : IsSimpleModule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hP.1) :=
    (XMod.isIrr_iff hP.1).1 hP
  haveI : Nontrivial ↥(XMod.toSubmod hP.1) :=
    IsSimpleModule.nontrivial ↥(XMod.opRing ↥Λ Q) _
  haveI : Finite (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hP.1)) :=
    Finite.of_injective
      (fun g : Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hP.1) =>
        (g : ↥(XMod.toSubmod hP.1) → ↥(XMod.toSubmod hP.1)))
      DFunLike.coe_injective
  have h1 := SmithD39Two.card_end_le hP.1
  have h2 := s16t3_card_eqv_end_le_two hP hE
  have h3 : 1 < Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hP.1)) :=
    Finite.one_lt_card
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
