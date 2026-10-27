module

public import CFSG.Quasithin.Background.G9GolayQuot
public import CFSG.Quasithin.Background.G9GolayAction
public import CFSG.Quasithin.Background.G11Bridge

public section

namespace CFSG.Quasithin.G11

theorem isGolaySectionModule_of_realizes {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {H : Subgroup (GLV V)} {Model : Type} [Group Model] (m₀ : ↥H ≃* Model) (small : Bool)
    (T : Equiv.Perm (Fin 24)) {Γ : Subgroup (Equiv.Perm (Fin 24))}
    {numer denom : Subgroup (G6.PermMod 24)} {numS denS : Submodule (ZMod 2) GolayAmbient}
    (hΓ : ∀ g : Equiv.Perm (Fin 24), g ∈ Γ ↔
      ((∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
          permAct (T⁻¹ * g * T) w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
        (small = true → (T⁻¹ * g * T) 0 = 0 ∧ (T⁻¹ * g * T) 1 = 1)))
    (hnum : GolayCorr T numS numer) (hden : GolayCorr T denS denom)
    (hreal : (FFModel.golaySec Γ numer denom).Realizes (toMulSub H) ⊤ ⊥)
    (hcard : Nat.card ↥Γ ≤ Nat.card Model) :
    IsGolaySectionModule (Model := Model) H small numS denS := by
  obtain ⟨π, hπs, -, hkerle, -, -, hnuminv, -, β, hβs, hβk, hβe⟩ := hreal
  let π' : ↥Γ →* ↥(toMulSub H) := π
  have hπs' : Function.Surjective π' := hπs
  have hbij : Function.Bijective π' := by
    refine hπs'.bijective_of_nat_card_le ?_
    rw [Nat.card_congr (toMulSubEquiv H).symm.toEquiv, Nat.card_congr m₀.toEquiv]
    exact hcard
  let ψ : ↥H ≃* ↥Γ := (toMulSubEquiv H).trans (MulEquiv.ofBijective π' hbij).symm
  let φ : Model ≃* ↥Γ := m₀.symm.trans ψ
  have hπψ : ∀ h : ↥H, π' (ψ h) = toMulSubEquiv H h := fun h =>
    MulEquiv.ofBijective_apply_symm_apply π' hbij
  obtain ⟨action, hinj, hact, himg⟩ := exists_golay_action small T hΓ φ
  obtain ⟨q, hqs, hqk, hq⟩ := exists_golay_quotientMap hnum hden β hβs hβk
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext ((Subgroup.mem_bot).1 ((hβk u).1 hu))
  have hact' : ∀ h : ↥H, action (m₀ h) = T⁻¹ * (ψ h : Equiv.Perm (Fin 24)) * T := fun h => by
    rw [hact]
    simp [φ]
  have hconj : ∀ (γ : Equiv.Perm (Fin 24)) (w : GolayAmbient),
      permAct T (permAct (T⁻¹ * γ * T) w) = permAct γ (permAct T w) := fun γ w => by
    rw [← golay_permAct_mul, ← golay_permAct_mul]
    congr 1
    group
  refine ⟨m₀, action, hinj, himg, ?_, ?_, q, hqs, hqk, ?_⟩
  · intro w hw
    exact (hnum w).2 (hkerle ((hden w).1 hw))
  · intro h w
    rw [hact' h, hnum, hconj]
    exact hnuminv (ψ h) _ ((hnum w).1 w.2)
  · intro h w image himage
    have hwm : Multiplicative.ofAdd (permAct T (w : GolayAmbient)) ∈ numer := (hnum w).1 w.2
    have hm : permSubAct Γ (ψ h) (Multiplicative.ofAdd (permAct T (w : GolayAmbient))) ∈ numer :=
      hnuminv (ψ h) _ hwm
    have key := hβe (ψ h) ⟨Multiplicative.ofAdd (q w), Subgroup.mem_top _⟩
      ⟨Multiplicative.ofAdd (permAct T (w : GolayAmbient)), hwm⟩ (Subgroup.mem_top _) hm (hq w)
    have hπh : ((π' (ψ h) : ↥(toMulSub H)) : MulAut (Multiplicative V))
        (Multiplicative.ofAdd (q w)) = Multiplicative.ofAdd ((h : GLV V) (q w)) := by
      rw [hπψ]
      rfl
    have hperm : permAct T (image : GolayAmbient) =
        permAct (ψ h : Equiv.Perm (Fin 24)) (permAct T (w : GolayAmbient)) := by
      rw [himage, hact' h, hconj]
    have hval : Multiplicative.ofAdd (permAct T (image : GolayAmbient)) =
        permSubAct Γ (ψ h) (Multiplicative.ofAdd (permAct T (w : GolayAmbient))) := by
      rw [hperm]
      rfl
    have hlhs : (⟨Multiplicative.ofAdd (permAct T (image : GolayAmbient)), (hnum image).1 image.2⟩ :
        ↥numer) = ⟨permSubAct Γ (ψ h) (Multiplicative.ofAdd (permAct T (w : GolayAmbient))), hm⟩ :=
      Subtype.ext hval
    have hrhs : (⟨(π' (ψ h) : MulAut (Multiplicative V)) (Multiplicative.ofAdd (q w)),
        Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Multiplicative V))) =
        ⟨Multiplicative.ofAdd ((h : GLV V) (q w)), Subgroup.mem_top _⟩ := Subtype.ext hπh
    have h1 : β ⟨Multiplicative.ofAdd (q image), Subgroup.mem_top _⟩ =
        β ⟨Multiplicative.ofAdd ((h : GLV V) (q w)), Subgroup.mem_top _⟩ :=
      calc β ⟨Multiplicative.ofAdd (q image), Subgroup.mem_top _⟩
          = QuotientGroup.mk ⟨Multiplicative.ofAdd (permAct T (image : GolayAmbient)),
              (hnum image).1 image.2⟩ := hq image
        _ = QuotientGroup.mk ⟨permSubAct Γ (ψ h)
              (Multiplicative.ofAdd (permAct T (w : GolayAmbient))), hm⟩ :=
          congrArg QuotientGroup.mk hlhs
        _ = β ⟨(π' (ψ h) : MulAut (Multiplicative V)) (Multiplicative.ofAdd (q w)),
              Subgroup.mem_top _⟩ := key.symm
        _ = β ⟨Multiplicative.ofAdd ((h : GLV V) (q w)), Subgroup.mem_top _⟩ :=
          congrArg β hrhs
    have h2 := congrArg (fun x : ↥(⊤ : Subgroup (Multiplicative V)) =>
      Multiplicative.toAdd (x : Multiplicative V)) (hβinj h1)
    simpa using h2

end CFSG.Quasithin.G11
