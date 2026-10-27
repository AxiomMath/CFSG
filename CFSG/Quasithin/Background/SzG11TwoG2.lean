module

public import CFSG.Quasithin.Background.SzG11TwoG2Plumb
public import CFSG.Quasithin.Background.SzG11TwoG2Point
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.Quasithin.Background.SzG11TwoG2Abs

public section

namespace CFSG.Quasithin.G11.SzG11S

open CFSG.Quasithin CFSG.Quasithin.SzG11NC CFSG.Quasithin.G11.SzG11S.Two

theorem g2Two_card_gf4 : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem g2Two_main {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
    (hs : Conf B Γ v₁ W X X₀ L) (hp : G116Props B Γ v₁ X L ⊤)
    (hnat : IsG2NaturalModule (normalClosure Γ L)
      ⁅CFSG.Open.quasithinG2 (GaloisField 2 2), CFSG.Open.quasithinG2 (GaloisField 2 2)⁆)
    (hex : ∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)) : False := by
  classical
  have hK : Nat.card (GaloisField 2 2) = 4 := g2Two_card_gf4
  obtain ⟨c, hc0, hc1, -⟩ := E4_cases hK (two_eq_zero_of_card_four hK)
  have hc : ⁅CFSG.Open.quasithinG2 (GaloisField 2 2), CFSG.Open.quasithinG2 (GaloisField 2 2)⁆ =
      CFSG.Quasithin.Explicit.cayleyGroup (GaloisField 2 2) := by
    rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      CFSG.Quasithin.JonesParshall.cayley_commutator_eq hc0 hc1]
  rw [hc] at hnat
  obtain ⟨φ₀, π₀, hM₀⟩ := isG2NaturalModule_iff.1 hnat
  have hirr := isIrr_top_of_conf hs hp
  have hHΓ := normalClosure_le_conf hs
  have hnorm := normalClosure_normal Γ L
  obtain ⟨φ, π, hM, hπ⟩ := exists_pointed_model hM₀ hs.hyp.point
  have hG₀ : CFSG.Quasithin.Explicit.cayleyGroup (GaloisField 2 2) ≤
      CFSG.Open.quasithinG2 (GaloisField 2 2) :=
    (CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup).ge
  obtain ⟨sc, hsc, hscπ⟩ := exists_scalars_of_model (GaloisField 2 2) hG₀ hM
  have hd : 6 ≤ Module.finrank (ZMod 2) V :=
    le_trans (by norm_num) (twelve_le_finrank_of_g2 (GaloisField 2 2) (by omega) hnat)
  have hE : Nat.card (CommF (normalClosure Γ L) hirr) = 4 :=
    card_commF_of_scalars hs hp (GaloisField 2 2) hK sc hsc hd
  have : Nontrivial V := nontrivial_of_isIrr_top hirr
  let g : GaloisField 2 2 →+* CommF (normalClosure Γ L) hirr :=
    { toFun := fun κ => CommF.mk (sc κ) (mem_commutantOf.2 (hsc κ))
      map_one' := CommF.val_injective (by rw [CommF.val_mk, CommF.val_one, map_one])
      map_mul' := fun a b => CommF.val_injective (by
        rw [CommF.val_mk, CommF.val_mul, CommF.val_mk, CommF.val_mk, map_mul])
      map_zero' := CommF.val_injective (by rw [CommF.val_mk, CommF.val_zero, map_zero])
      map_add' := fun a b => CommF.val_injective (by
        rw [CommF.val_mk, CommF.val_add, CommF.val_mk, CommF.val_mk, map_add]) }
  have hginj : Function.Injective g := fun a b h => sc.injective (congrArg CommF.val h)
  have hgbij : Function.Bijective g := hginj.bijective_of_nat_card_le (by rw [hK, hE])
  let eqv : GaloisField 2 2 ≃+* CommF (normalClosure Γ L) hirr := RingEquiv.ofBijective g hgbij
  have heqv : ∀ (κ : GaloisField 2 2) (v : V), eqv κ • v = sc κ v := fun κ v => by
    rw [CommF.smul_def]
    rfl
  have hbij := thetaHom_bijective hM
  let Θe : (CFSG.Quasithin.JonesParshall.Ix3 → GaloisField 2 2) ≃+ V :=
    AddEquiv.ofBijective (thetaHom π) hbij
  have hΘe : ∀ w, Θe w = thetaHom π w := fun w => rfl
  have hΘsmul : ∀ (κ : GaloisField 2 2) w, Θe (κ • w) = eqv κ • Θe w := by
    intro κ w
    rw [hΘe, hΘe, thetaHom_smul hscπ, heqv]
  have hsymm_smul : ∀ (e : CommF (normalClosure Γ L) hirr) (v : V),
      Θe.symm (e • v) = eqv.symm e • Θe.symm v := by
    intro e v
    apply Θe.injective
    rw [AddEquiv.apply_symm_apply, hΘsmul, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let J : LinearMap.BilinForm (CommF (normalClosure Γ L) hirr) V :=
    LinearMap.mk₂ _ (fun u v => eqv (CFSG.Quasithin.JonesParshall.bilQ (Θe.symm u) (Θe.symm v)))
      (fun u u' v => by
        simp only [map_add, CFSG.Quasithin.JonesParshall.bilQ_add_left])
      (fun e u v => by
        simp only [hsymm_smul, CFSG.Quasithin.JonesParshall.bilQ_smul_left, map_mul,
          RingEquiv.apply_symm_apply, smul_eq_mul])
      (fun u v v' => by
        simp only [map_add, bilQ_add_right])
      (fun e u v => by
        simp only [hsymm_smul, bilQ_smul_right, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul])
  have hJapp : ∀ u v, J u v =
      eqv (CFSG.Quasithin.JonesParshall.bilQ (Θe.symm u) (Θe.symm v)) := fun u v => rfl
  have hJalt : ∀ v, J v v = 0 := fun v => by rw [hJapp, bilQ_self, map_zero]
  have hJnd : J.Nondegenerate := by
    refine ⟨fun u hu => ?_, fun v hv => ?_⟩
    · apply Θe.symm.injective
      rw [map_zero]
      apply bilQ_left_nondeg
      intro w'
      have := hu (Θe w')
      rw [hJapp, AddEquiv.symm_apply_apply] at this
      exact eqv.injective (by rw [this, map_zero])
    · apply Θe.symm.injective
      rw [map_zero]
      apply bilQ_right_nondeg
      intro w'
      have := hv (Θe w')
      rw [hJapp, AddEquiv.symm_apply_apply] at this
      exact eqv.injective (by rw [this, map_zero])
  have hJinv : ∀ h ∈ normalClosure Γ L, ∀ u v, J (h u) (h v) = J u v := by
    intro h hh u v
    obtain ⟨w, rfl⟩ := Θe.surjective u
    obtain ⟨w', rfl⟩ := Θe.surjective v
    have e1 : h (Θe w) = Θe (CFSG.Quasithin.JonesParshall.g2Act (φ ⟨h, hh⟩) w) :=
      thetaHom_equiv hM ⟨h, hh⟩ w
    have e2 : h (Θe w') = Θe (CFSG.Quasithin.JonesParshall.g2Act (φ ⟨h, hh⟩) w') :=
      thetaHom_equiv hM ⟨h, hh⟩ w'
    rw [e1, e2, hJapp, hJapp, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
      AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
      CFSG.Quasithin.JonesParshall.bilQ_g2Act]
  have hV : Nat.card V = 4096 := by
    rw [card_eq_pow_six hM, hK]
    norm_num
  refine g2_abstract hs.hyp hirr hHΓ hnorm hE hV J hJalt hJnd hJinv (fun hYker => ?_) hex
  have hw₁ : Θe.symm v₁ = CFSG.Quasithin.JonesParshall.q6 1 0 0 0 0 0 := by
    apply Θe.injective
    rw [AddEquiv.apply_symm_apply]
    exact (thetaHom_q6_one hπ).symm
  refine g2_low hs.hyp hirr hHΓ hE hK hM hπ eqv hscπ heqv (fun w => ?_)
  rw [show thetaHom π w = Θe w from rfl, hYker, LinearMap.mem_ker, hJapp, hw₁,
    AddEquiv.symm_apply_apply, map_eq_zero_iff _ eqv.injective]
  simp [CFSG.Quasithin.JonesParshall.bilQ, CFSG.Quasithin.JonesParshall.q6]

theorem noConfigG2Two : NoConfigG2Two := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp hnat hex
  exact g2Two_main hs hp hnat hex

end CFSG.Quasithin.G11.SzG11S
