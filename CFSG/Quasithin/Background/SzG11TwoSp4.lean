module

public import CFSG.Quasithin.Background.SzG11TwoSp4Abs
public import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerTransvection

public section

namespace CFSG.Quasithin.G11.SzG11S

open CFSG.Quasithin CFSG.Quasithin.SzG11NC CFSG.Quasithin.G11.SzG11S.Two
open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull CFSG.Assembly.LowTwoRank

theorem commutator_statedSp_gf4 :
    ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆ =
      StatedSp 2 (GaloisField 2 2) := by
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 (GaloisField 2 2) (by norm_num)
    (Or.inl (Or.inr (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num)))
  exact (Subgroup.isPerfect_iff).1 hq.1

theorem sp4Two_main {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
    {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}
    (hs : Conf B Γ v₁ W X X₀ L) (hp : G116Props B Γ v₁ X L ⊤)
    (hnat : IsNaturalMatrixModule (normalClosure Γ L)
      ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆)
    (hex : ∃ x ∈ X, ∃ f ∈ endCommutant (normalClosure Γ L), ∃ v, x (f v) ≠ f (x v)) : False := by
  classical
  have hK : Nat.card (GaloisField 2 2) = 4 := card_galoisField_two_two
  have hd : Module.finrank (ZMod 2) V = 8 := by
    rw [finrank_of_natural hnat, GaloisField.finrank 2 (n := 2) (by norm_num)]
    simp
  have hV : Nat.card V = 256 := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod, hd] at this
    simpa using this
  obtain ⟨φ, ψ, hψ⟩ := hnat
  have hirr := isIrr_top_of_conf hs hp
  have hHΓ := normalClosure_le_conf hs
  have hnorm := normalClosure_normal Γ L
  have hsc : ∀ κ, ∀ h ∈ normalClosure Γ L, ∀ v, scalarHom ψ κ (h v) = h (scalarHom ψ κ v) := by
    intro κ h hh v
    show scalarEnd ψ κ (h v) = h (scalarEnd ψ κ v)
    rw [scalarEnd_apply, scalarEnd_apply, hψ ⟨h, hh⟩ v]
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply, hψ ⟨h, hh⟩, LinearEquiv.apply_symm_apply,
      Matrix.mulVec_smul]
  have hE : Nat.card (CommF (normalClosure Γ L) hirr) = 4 :=
    card_commF_of_scalars hs hp (GaloisField 2 2) hK (scalarHom ψ) hsc (by omega)
  let g : GaloisField 2 2 →+* CommF (normalClosure Γ L) hirr :=
    { toFun := fun κ => CommF.mk (scalarHom ψ κ) (mem_commutantOf.2 (hsc κ))
      map_one' := CommF.val_injective (by rw [CommF.val_mk, CommF.val_one, map_one])
      map_mul' := fun a b => CommF.val_injective (by
        rw [CommF.val_mk, CommF.val_mul, CommF.val_mk, CommF.val_mk, map_mul])
      map_zero' := CommF.val_injective (by rw [CommF.val_mk, CommF.val_zero, map_zero])
      map_add' := fun a b => CommF.val_injective (by
        rw [CommF.val_mk, CommF.val_add, CommF.val_mk, CommF.val_mk, map_add]) }
  have : Nontrivial V := nontrivial_of_isIrr_top hirr
  have hginj : Function.Injective g := fun a b h => (scalarHom ψ).injective (congrArg CommF.val h)
  have hgbij : Function.Bijective g := hginj.bijective_of_nat_card_le (by rw [hK, hE])
  let eqv : GaloisField 2 2 ≃+* CommF (normalClosure Γ L) hirr := RingEquiv.ofBijective g hgbij
  have heqv_smul : ∀ (κ : GaloisField 2 2) (v : V), (eqv κ) • v = ψ.symm (κ • ψ v) := by
    intro κ v
    rw [CommF.smul_def]
    rfl
  have hpsi_smul : ∀ (e : CommF (normalClosure Γ L) hirr) (v : V),
      ψ (e • v) = eqv.symm e • ψ v := by
    intro e v
    obtain ⟨κ, rfl⟩ := eqv.surjective e
    rw [heqv_smul, LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
  let JV : LinearMap.BilinForm (CommF (normalClosure Γ L) hirr) V :=
    LinearMap.mk₂ _ (fun u v => eqv (spForm 2 (GaloisField 2 2) (ψ u) (ψ v)))
      (fun u u' v => by simp only [map_add, LinearMap.add_apply])
      (fun e u v => by
        simp only [hpsi_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul,
          RingEquiv.apply_symm_apply])
      (fun u v v' => by simp only [map_add])
      (fun e u v => by
        simp only [hpsi_smul, map_smul, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply])
  have hJapp : ∀ u v, JV u v = eqv (spForm 2 (GaloisField 2 2) (ψ u) (ψ v)) := fun u v => rfl
  have hJalt : ∀ v, JV v v = 0 := fun v => by
    rw [hJapp, spForm_isAlt (ψ v), map_zero]
  have hJnd : JV.Nondegenerate := by
    refine ⟨fun u hu => ?_, fun w hw => ?_⟩
    · apply ψ.injective
      rw [map_zero]
      apply (spForm_nondegenerate (r := 2) (K := GaloisField 2 2)).1
      intro w'
      have := hu (ψ.symm w')
      rw [hJapp, LinearEquiv.apply_symm_apply] at this
      exact eqv.injective (by rw [this, map_zero])
    · apply ψ.injective
      rw [map_zero]
      apply (spForm_nondegenerate (r := 2) (K := GaloisField 2 2)).2
      intro u'
      have := hw (ψ.symm u')
      rw [hJapp, LinearEquiv.apply_symm_apply] at this
      exact eqv.injective (by rw [this, map_zero])
  have hSmem : ∀ h : ↥(normalClosure Γ L),
      ((φ h : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) :
        GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) ∈ StatedSp 2 (GaloisField 2 2) := by
    intro h
    exact commutator_statedSp_gf4.le (φ h).2
  have hJinv : ∀ h ∈ normalClosure Γ L, ∀ u v, JV (h u) (h v) = JV u v := by
    intro h hh u v
    rw [hJapp, hJapp, hψ ⟨h, hh⟩ u, hψ ⟨h, hh⟩ v]
    have := CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup.mp
      (spLin_mem ⟨_, hSmem ⟨h, hh⟩⟩) (ψ u) (ψ v)
    rw [spEnd_apply, spEnd_apply] at this
    rw [this]
  have htv : ∀ (u : V) (t : CommF (normalClosure Γ L) hirr), ∃ h ∈ normalClosure Γ L,
      ∀ v, h v = v + (t * JV v u) • u := by
    intro u t
    let gsp : StatedSp 2 (GaloisField 2 2) := spTransvection (ψ u) (eqv.symm t)
    have hmem : (gsp : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) ∈
        ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆ := by
      rw [commutator_statedSp_gf4]
      exact gsp.2
    obtain ⟨h, hh⟩ := φ.surjective ⟨(gsp : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2)), hmem⟩
    refine ⟨(h : GLV V), h.2, fun v => ?_⟩
    apply ψ.injective
    have h1 : ψ ((h : GLV V) v) = spEnd gsp (ψ v) := by
      rw [hψ h v, spEnd_apply]
      have := congrArg (fun x : ↥⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆ =>
        ((x : GL (Fin 2 ⊕ Fin 2) (GaloisField 2 2)) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2)
          (GaloisField 2 2))) hh
      simp only at this
      rw [this]
    rw [h1, spEnd_spTransvection, map_add, hpsi_smul, map_mul, hJapp, RingEquiv.symm_apply_apply]
  exact sp4_abstract hs.hyp hirr hHΓ hnorm hE hV JV hJalt hJnd hJinv htv hex

theorem noConfigSp4Two : NoConfigSp4Two := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs hp hnat hex
  exact sp4Two_main hs hp hnat hex

end CFSG.Quasithin.G11.SzG11S
