module

public import CFSG.Quasithin.Background.SzG11TwoG2Coord
public import CFSG.Quasithin.Background.SzG11TwoG2Low
public import CFSG.Quasithin.Background.SzG11TwoCommonSyl

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin CFSG.Quasithin.SzG11NC CFSG.QuasithinUnique CFSG.Open
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {B : LinearMap.BilinForm (ZMod 2) V}
  {Γ X X₀ : Subgroup (GLV V)} {v₁ : V} {W : Submodule (ZMod 2) V}

theorem g2_low [Finite V] (hyp : G111Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (hE : Nat.card (CommF H hirr) = 4)
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K] (hK : Nat.card K = 4)
    {φ : ↥H ≃* ↥(cayleyGroup K)} {π : quasithinZorn K →ₗ[ZMod 2] V}
    (hM : IsG2Model H (cayleyGroup K) φ π) (hπ : π (zU0 K) = v₁)
    (eqv : K ≃+* CommF H hirr) {sc : K →+* Module.End (ZMod 2) V}
    (hscπ : ∀ (κ : K) (x : quasithinZorn K), x.1 + x.2.2.2 = 0 → sc κ (π x) = π (κ • x))
    (heqv : ∀ (κ : K) (v : V), eqv κ • v = sc κ v)
    (hY : ∀ w : Ix3 → K,
      thetaHom π w ∈ Ysp (CommF H hirr) B v₁ ↔ w (Sum.inr 0) = 0) :
    2 ^ 7 ∣ Nat.card (rhoStab hyp.toG101Hyp hirr hHΓ).range := by
  classical
  have hbij := thetaHom_bijective hM
  have hΘsmul : ∀ (κ : K) (w : Ix3 → K), thetaHom π (κ • w) = eqv κ • thetaHom π w := by
    intro κ w
    rw [thetaHom_smul hscπ, heqv]
  have hw₁ : thetaHom π (q6 1 0 0 0 0 0) = v₁ := thetaHom_q6_one hπ
  have h2 : (2 : CommF H hirr) = 0 := two_eq_zero_of_card_four hE
  have : Finite (Mq (CommF H hirr) B v₁) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hMadd : ∀ n : Mq (CommF H hirr) B v₁, n + n = 0 := fun n => by
    rw [← two_smul (CommF H hirr) n, h2, zero_smul]
  let θY : ↥(YQ K) →+ ↥(Ysp (CommF H hirr) B v₁) :=
    { toFun := fun w => ⟨thetaHom π (w : Ix3 → K), (hY _).2 w.2⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun a b => Subtype.ext (map_add _ _ _) }
  have hθY : ∀ w : ↥(YQ K), ((θY w : ↥(Ysp (CommF H hirr) B v₁)) : V) =
      thetaHom π (w : Ix3 → K) := fun w => rfl
  let m : ↥(YQ K) →+ Mq (CommF H hirr) B v₁ :=
    (Submodule.mkQ (Nsp (CommF H hirr) B v₁)).toAddMonoidHom.comp θY
  have hm : ∀ w : ↥(YQ K), m w = Submodule.Quotient.mk (θY w) := fun w => rfl

  have hsurj : Function.Surjective m := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨w, hw⟩ := hbij.2 (y : V)
    have hwY : w (Sum.inr 0) = 0 := (hY w).1 (by rw [hw]; exact y.2)
    refine ⟨⟨w, hwY⟩, ?_⟩
    rw [hm]
    congr 1
    exact Subtype.ext hw
  have hΘq : ∀ κ : K, thetaHom π (q6 κ 0 0 0 0 0) = eqv κ • v₁ := by
    intro κ
    have := hΘsmul κ (q6 1 0 0 0 0 0)
    rw [q6_smul, hw₁] at this
    simpa using this
  have hker : ∀ w w' : ↥(YQ K), m w = m w' ↔
      ∃ c : K, (w : Ix3 → K) - (w' : Ix3 → K) = q6 c 0 0 0 0 0 := by
    intro w w'
    rw [hm, hm, Submodule.Quotient.eq, mem_Nsp]
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨κ, rfl⟩ := eqv.surjective c
      have hc' : eqv κ • v₁ = thetaHom π (w : Ix3 → K) - thetaHom π (w' : Ix3 → K) := by
        rw [hc]
        simp [hθY]
      refine ⟨κ, hbij.1 ?_⟩
      rw [map_sub, hΘq, hc']
    · rintro ⟨c, hc⟩
      refine ⟨eqv c, ?_⟩
      rw [← hΘq, ← hc, map_sub]
      simp [hθY]
  have hfix : ∀ g : ↥(stabU0 K), g2Act (g : ↥(cayleyGroup K)) (q6 1 0 0 0 0 0) =
      q6 1 0 0 0 0 0 := by
    intro g
    have hg : cgE (g : ↥(cayleyGroup K)) (zU0 K) = zU0 K := g.2
    rw [g2Act_apply, zI_q6]
    change zP (cgE (g : ↥(cayleyGroup K)) (zU0 K)) = _
    rw [hg]
    rfl
  have hsv : ∀ g : ↥(stabU0 K), ((φ.symm (g : ↥(cayleyGroup K)) : ↥H) : GLV V) v₁ = v₁ := by
    intro g
    have := thetaHom_equiv hM (φ.symm (g : ↥(cayleyGroup K))) (q6 1 0 0 0 0 0)
    rw [MulEquiv.apply_symm_apply, hfix, hw₁] at this
    exact this
  let s : ↥(stabU0 K) →* ↥(H ⊓ MulAction.stabilizer (GLV V) v₁) :=
    { toFun := fun g => ⟨((φ.symm (g : ↥(cayleyGroup K)) : ↥H) : GLV V),
        ⟨(φ.symm (g : ↥(cayleyGroup K))).2, hsv g⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hs : ∀ g : ↥(stabU0 K), ((s g : ↥(H ⊓ MulAction.stabilizer (GLV V) v₁)) : GLV V) =
      ((φ.symm (g : ↥(cayleyGroup K)) : ↥H) : GLV V) := fun g => rfl
  have hsΘ : ∀ (g : ↥(stabU0 K)) (w : Ix3 → K),
      ((s g : ↥(H ⊓ MulAction.stabilizer (GLV V) v₁)) : GLV V) (thetaHom π w) =
        thetaHom π (g2Act (g : ↥(cayleyGroup K)) w) := by
    intro g w
    rw [hs, thetaHom_equiv hM, MulEquiv.apply_symm_apply]
  let Ξ : ↥(stabU0 K) →* (Mq (CommF H hirr) B v₁ ≃ₗ[CommF H hirr] Mq (CommF H hirr) B v₁) :=
    (rhoStab hyp.toG101Hyp hirr hHΓ).comp s
  have hΞ : ∀ (g : ↥(stabU0 K)) (w : ↥(YQ K)), ∃ w' : ↥(YQ K),
      (w' : Ix3 → K) = g2Act (g : ↥(cayleyGroup K)) (w : Ix3 → K) ∧ Ξ g (m w) = m w' := by
    intro g w
    have hmem : thetaHom π (g2Act (g : ↥(cayleyGroup K)) (w : Ix3 → K)) ∈
        Ysp (CommF H hirr) B v₁ := by
      rw [← hsΘ]
      exact (stab_prop hyp.toG101Hyp hirr hHΓ (s g : GLV V) (s g).2).2.2 _ ((θY w).2)
    refine ⟨⟨g2Act (g : ↥(cayleyGroup K)) (w : Ix3 → K), (hY _).1 hmem⟩, rfl, ?_⟩
    show rhoStab hyp.toG101Hyp hirr hHΓ (s g) (Submodule.Quotient.mk (θY w)) =
      Submodule.Quotient.mk _
    rw [rhoStab_mk]
    congr 1
    exact Subtype.ext (hsΘ g w)
  have hlow := two_pow_seven_dvd hK hMadd m hsurj hker Ξ hΞ
  have hle : Ξ.range ≤ (rhoStab hyp.toG101Hyp hirr hHΓ).range := by
    rintro x ⟨g, rfl⟩
    exact ⟨s g, rfl⟩
  exact hlow.trans (Subgroup.card_dvd_of_le hle)


end CFSG.Quasithin.G11.SzG11S.Two
