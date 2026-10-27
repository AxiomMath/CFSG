module

public import CFSG.Quasithin.Background.Sp4InfConc
public import CFSG.Quasithin.Background.Sp4InfAut6
public import CFSG.Quasithin.Background.Sp4InfA6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H Matrix
open CFSG.QuasithinUnique.Bridge.Alt57Model (spEquivPerm normal_eq_bot_or_alt_le)
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauEquiv)

@[expose] noncomputable def iotaSp : StatedSp 2 (ZMod 2) ≃* Perm (Fin 6) :=
  spEquivPerm (ZMod 2) (ZMod.card 2)

@[expose] def IsAlt6Sub (D : Subgroup (StatedSp 2 (ZMod 2))) : Prop :=
  D.map iotaSp.toMonoidHom = alternatingGroup (Fin 6)

theorem isAlt6Sub_comap : IsAlt6Sub ((alternatingGroup (Fin 6)).comap iotaSp.toMonoidHom) :=
  Subgroup.map_comap_eq_self_of_surjective iotaSp.surjective _

theorem mem_of_odd_pow {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    {g : StatedSp 2 (ZMod 2)} {k : ℕ} (hk : Odd k) (hg : g ^ k = 1) : g ∈ D := by
  have hD' : D.map iotaSp.toMonoidHom = alternatingGroup (Fin 6) := hD
  have h1 : Perm.sign (iotaSp g) = 1 := by
    have : Perm.sign (iotaSp g) ^ k = 1 := by
      rw [← map_pow, ← map_pow, hg, map_one, map_one]
    rcases Int.units_eq_one_or (Perm.sign (iotaSp g)) with h | h
    · exact h
    · rw [h, hk.neg_one_pow] at this
      exact absurd this (by decide)
  have h2 : iotaSp g ∈ D.map iotaSp.toMonoidHom := by
    rw [hD']
    exact Perm.mem_alternatingGroup.2 h1
  obtain ⟨d, hd, hdg⟩ := h2
  have : d = g := iotaSp.injective hdg
  rwa [← this]

theorem aSp_mem {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D) : aSp ∈ D :=
  mem_of_odd_pow hD (by decide) aSp_pow_three

theorem bSp_mem {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D) : bSp ∈ D :=
  mem_of_odd_pow hD (by decide) bSp_pow_five

theorem aSp_ne_one : aSp ≠ 1 := by
  intro h
  have h1 : aM = 1 := by
    have := congrArg (fun g : StatedSp 2 (ZMod 2) => ((g : GL I4 (ZMod 2)) : Matrix I4 I4 (ZMod 2))) h
    simpa [coe_aSp] using this
  exact absurd h1 (by decide)

theorem eq_one_of_commute
    {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    (f : MulAut (StdMod I4 (ZMod 2)))
    (hf : ∀ γ ∈ D, ∀ x, f (matAut ((γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) x) =
      matAut ((γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) (f x)) : f = 1 := by
  have h0 : toAddMap f 0 = 0 := by
    have := map_one f
    simp [toAddMap]
  let Fl : (I4 → ZMod 2) →ₗ[ZMod 2] (I4 → ZMod 2) :=
    { toFun := toAddMap f
      map_add' := toAddMap_add f
      map_smul' := fun c v => by
        have hc : c = 0 ∨ c = 1 := by revert c; decide
        rcases hc with rfl | rfl
        · simp [h0]
        · simp }
  let M : Matrix I4 I4 (ZMod 2) := LinearMap.toMatrix' Fl
  have hM : ∀ v, M *ᵥ v = toAddMap f v := fun v => by
    have h := congrArg (fun L : (I4 → ZMod 2) →ₗ[ZMod 2] (I4 → ZMod 2) => L v)
      (Matrix.toLin'_toMatrix' Fl)
    simp only [Matrix.toLin'_apply] at h
    exact h
  have hcomm : ∀ γ ∈ D, M * ((γ : GL I4 (ZMod 2)) : Matrix I4 I4 (ZMod 2)) =
      ((γ : GL I4 (ZMod 2)) : Matrix I4 I4 (ZMod 2)) * M := by
    intro γ hγ
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, hM]
    exact congrArg (fun x : StdMod I4 (ZMod 2) => Multiplicative.toAdd x)
      (hf γ hγ (Multiplicative.ofAdd v))
  have h1 := hcomm aSp (aSp_mem hD)
  have h2 := hcomm bSp (bSp_mem hD)
  rw [coe_aSp] at h1
  rw [coe_bSp] at h2
  rcases commutant_ab M h1 h2 with h0 | h0
  · exfalso
    have hz : ∀ x : StdMod I4 (ZMod 2), f x = 1 := fun x => by
      apply Multiplicative.toAdd.injective
      rw [show Multiplicative.toAdd (f x) = toAddMap f (Multiplicative.toAdd x) by
        simp [toAddMap], ← hM, h0]
      simp
    have : (Multiplicative.ofAdd (Pi.single (Sum.inl 0 : I4) (1 : ZMod 2)) : StdMod I4 (ZMod 2)) = 1 :=
      f.injective ((hz _).trans (map_one f).symm)
    have := congrArg (fun x : StdMod I4 (ZMod 2) => Multiplicative.toAdd x (Sum.inl 0)) this
    simp at this
  · refine toAddMap_injective fun v => ?_
    rw [← hM, h0, Matrix.one_mulVec]
    rfl

theorem no_tau_iso {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    (Φ : StdMod I4 (ZMod 2) ≃* StdMod I4 (ZMod 2))
    (hΦ : ∀ γ ∈ D, ∀ x, Φ (matAut ((γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) x) =
      matAut ((tauSp γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) (Φ x)) : False := by
  have hinj : Function.Injective (fun v : {v : StdMod I4 (ZMod 2) //
      matAut ((aSp : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) v = v} =>
      (⟨Φ v.1, by
        rw [← hΦ aSp (aSp_mem hD) v.1, v.2]⟩ : {v : StdMod I4 (ZMod 2) //
          matAut ((tauSp aSp : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) v = v})) := by
    intro v w h
    exact Subtype.ext (Φ.injective (congrArg Subtype.val h))
  have := Nat.card_le_card_of_injective _ hinj
  rw [card_fix_aSp, card_fix_tau_aSp] at this
  omega

theorem normal_of_isAlt6Sub {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D) : D.Normal := by
  have hD' : D.map iotaSp.toMonoidHom = alternatingGroup (Fin 6) := hD
  have h : D = (alternatingGroup (Fin 6)).comap iotaSp.toMonoidHom := by
    rw [← hD']
    exact (Subgroup.comap_map_eq_self_of_injective iotaSp.injective D).symm
  rw [h]
  exact (alternatingGroup.normal (α := Fin 6)).comap _

theorem eq_normalClosure_odd {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D) :
    D = Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) | ∃ k : ℕ, Odd k ∧ g ^ k = 1} := by
  have hD' : D.map iotaSp.toMonoidHom = alternatingGroup (Fin 6) := hD
  have hDn : D.Normal := normal_of_isAlt6Sub hD
  have hle : Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) | ∃ k : ℕ, Odd k ∧ g ^ k = 1} ≤ D :=
    Subgroup.normalClosure_le_normal fun g ⟨k, hk, hg⟩ => mem_of_odd_pow hD hk hg
  refine le_antisymm ?_ hle
  have hOn : (Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) | ∃ k : ℕ, Odd k ∧ g ^ k = 1}).Normal :=
    inferInstance
  have ha : aSp ∈ Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) | ∃ k : ℕ, Odd k ∧ g ^ k = 1} :=
    Subgroup.subset_normalClosure ⟨3, by decide, aSp_pow_three⟩
  have hne : (Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) | ∃ k : ℕ, Odd k ∧ g ^ k = 1}).map
      iotaSp.toMonoidHom ≠ ⊥ := by
    intro h
    have h1 : iotaSp aSp ∈ (Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) |
        ∃ k : ℕ, Odd k ∧ g ^ k = 1}).map iotaSp.toMonoidHom := ⟨aSp, ha, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact aSp_ne_one (iotaSp.injective (h1.trans (map_one iotaSp).symm))
  have hnorm : ((Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) | ∃ k : ℕ, Odd k ∧ g ^ k = 1}).map
      iotaSp.toMonoidHom).Normal := hOn.map _ iotaSp.surjective
  rcases normal_eq_bot_or_alt_le hnorm with h | h
  · exact absurd h hne
  · intro x hx
    have hx' : iotaSp x ∈ (Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) |
        ∃ k : ℕ, Odd k ∧ g ^ k = 1}).map iotaSp.toMonoidHom := by
      apply h
      rw [← hD']
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := iotaSp.injective hyx
    rwa [← this]

theorem map_le_of_isAlt6Sub {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    (φ : StatedSp 2 (ZMod 2) →* StatedSp 2 (ZMod 2)) : D.map φ ≤ D := by
  have : (D.comap φ).Normal := (normal_of_isAlt6Sub hD).comap φ
  rw [Subgroup.map_le_iff_le_comap]
  calc D = Subgroup.normalClosure {g : StatedSp 2 (ZMod 2) | ∃ k : ℕ, Odd k ∧ g ^ k = 1} :=
        eq_normalClosure_odd hD
    _ ≤ D.comap φ := Subgroup.normalClosure_le_normal fun g ⟨k, hk, hg⟩ => by
        show φ g ∈ D
        exact mem_of_odd_pow hD hk (by rw [← map_pow, hg, map_one])

theorem tau_mem_alt {x : StatedSp 2 (ZMod 2)} (hx : iotaSp x ∈ alternatingGroup (Fin 6)) :
    iotaSp (tauSp x) ∈ alternatingGroup (Fin 6) := by
  have : tauSp x ∈ (alternatingGroup (Fin 6)).comap iotaSp.toMonoidHom :=
    map_le_of_isAlt6Sub isAlt6Sub_comap tauSp ⟨x, hx, rfl⟩
  exact this

theorem tauInv_mem_alt {x : StatedSp 2 (ZMod 2)} (hx : iotaSp x ∈ alternatingGroup (Fin 6)) :
    iotaSp (tauEquiv.symm x) ∈ alternatingGroup (Fin 6) := by
  have hmem := Subgroup.mem_map_of_mem tauEquiv.symm.toMonoidHom
    (show x ∈ (alternatingGroup (Fin 6)).comap iotaSp.toMonoidHom from hx)
  exact map_le_of_isAlt6Sub isAlt6Sub_comap _ hmem

theorem tauEquiv_symm_tauSp (x : StatedSp 2 (ZMod 2)) : tauEquiv.symm (tauSp x) = x :=
  tauEquiv.symm_apply_apply x

theorem tauSp_tauEquiv_symm (x : StatedSp 2 (ZMod 2)) : tauSp (tauEquiv.symm x) = x :=
  tauEquiv.apply_symm_apply x

@[expose] noncomputable def tau6 : MulAut ↥(alternatingGroup (Fin 6)) where
  toFun y := ⟨iotaSp (tauSp (iotaSp.symm (y : Perm (Fin 6)))),
    tau_mem_alt (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  invFun y := ⟨iotaSp (tauEquiv.symm (iotaSp.symm (y : Perm (Fin 6)))),
    tauInv_mem_alt (by rw [MulEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv y := by
    apply Subtype.ext
    simp [tauEquiv_symm_tauSp]
  right_inv y := by
    apply Subtype.ext
    simp [tauSp_tauEquiv_symm]
  map_mul' x y := by
    apply Subtype.ext
    simp [map_mul]

theorem coe_tau6 (y : ↥(alternatingGroup (Fin 6))) :
    ((tau6 y : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
      iotaSp (tauSp (iotaSp.symm (y : Perm (Fin 6)))) := rfl

theorem matAut_mul' (g h : GL I4 (ZMod 2)) : matAut (g * h) = matAut g * matAut h :=
  map_mul matHom g h

theorem card_fix_conj (x γ : StatedSp 2 (ZMod 2)) :
    Nat.card {v : StdMod I4 (ZMod 2) //
        matAut (((γ * x * γ⁻¹ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))) v = v} =
      Nat.card {v : StdMod I4 (ZMod 2) // matAut ((x : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) v = v} := by
  have hc : ∀ v : StdMod I4 (ZMod 2),
      matAut (((γ * x * γ⁻¹ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))) v =
        matAut (γ : GL I4 (ZMod 2)) (matAut (x : GL I4 (ZMod 2)) (matAut (γ : GL I4 (ZMod 2))⁻¹ v)) := by
    intro v
    have h1 : matAut (((γ * x * γ⁻¹ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))) =
        matAut (γ : GL I4 (ZMod 2)) * matAut (x : GL I4 (ZMod 2)) * matAut (γ : GL I4 (ZMod 2))⁻¹ := by
      show matAut ((γ : GL I4 (ZMod 2)) * (x : GL I4 (ZMod 2)) * (γ : GL I4 (ZMod 2))⁻¹) = _
      rw [matAut_mul', matAut_mul']
    rw [h1]
    rfl
  have hγ : ∀ v : StdMod I4 (ZMod 2), matAut (γ : GL I4 (ZMod 2)) (matAut (γ : GL I4 (ZMod 2))⁻¹ v) = v := by
    intro v
    have : matAut (γ : GL I4 (ZMod 2)) * matAut (γ : GL I4 (ZMod 2))⁻¹ = 1 := by
      rw [← matAut_mul', mul_inv_cancel]
      exact map_one matHom
    exact congrArg (fun f : MulAut (StdMod I4 (ZMod 2)) => f v) this
  have hγ' : ∀ v : StdMod I4 (ZMod 2), matAut (γ : GL I4 (ZMod 2))⁻¹ (matAut (γ : GL I4 (ZMod 2)) v) = v := by
    intro v
    have : matAut (γ : GL I4 (ZMod 2))⁻¹ * matAut (γ : GL I4 (ZMod 2)) = 1 := by
      rw [← matAut_mul', inv_mul_cancel]
      exact map_one matHom
    exact congrArg (fun f : MulAut (StdMod I4 (ZMod 2)) => f v) this
  refine Nat.card_congr
    { toFun := fun v => ⟨matAut (γ : GL I4 (ZMod 2))⁻¹ v.1, ?_⟩
      invFun := fun w => ⟨matAut (γ : GL I4 (ZMod 2)) w.1, ?_⟩
      left_inv := fun v => Subtype.ext (hγ v.1)
      right_inv := fun w => Subtype.ext (hγ' w.1) }
  · have h := v.2
    rw [hc] at h
    have h2 := congrArg (fun z => matAut (γ : GL I4 (ZMod 2))⁻¹ z) h
    simp only [hγ'] at h2
    exact h2
  · have h := w.2
    show matAut (((γ * x * γ⁻¹ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))) (matAut (γ : GL I4 (ZMod 2)) w.1) =
      matAut (γ : GL I4 (ZMod 2)) w.1
    rw [hc, hγ', h]

theorem aSp_mem_alt : iotaSp aSp ∈ alternatingGroup (Fin 6) := by
  have : aSp ∈ (alternatingGroup (Fin 6)).comap iotaSp.toMonoidHom := aSp_mem isAlt6Sub_comap
  exact this

theorem tau6_not_mem_range : tau6 ∉ conjAlt6.range := by
  rintro ⟨g, hg⟩
  have h1 := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin 6)) =>
    ((φ ⟨iotaSp aSp, aSp_mem_alt⟩ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6))) hg
  simp only [coe_conjAlt6, coe_tau6, MulEquiv.symm_apply_apply] at h1
  have key : tauSp aSp = iotaSp.symm g * aSp * (iotaSp.symm g)⁻¹ := by
    apply iotaSp.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h1.symm
  have h2 := card_fix_conj aSp (iotaSp.symm g)
  rw [← key, card_fix_tau_aSp, card_fix_aSp] at h2
  omega

theorem ext_alt6 (c : MulAut ↥(alternatingGroup (Fin 6))) :
    InducedByS6 c ∨ ∃ γ : StatedSp 2 (ZMod 2), ∀ y : ↥(alternatingGroup (Fin 6)),
      ((c y : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
        iotaSp (γ * tauSp (iotaSp.symm (y : Perm (Fin 6))) * γ⁻¹) := by
  by_cases hc : c ∈ conjAlt6.range
  · left
    obtain ⟨g, rfl⟩ := hc
    exact ⟨g, fun x => coe_conjAlt6 g x⟩
  · right
    obtain ⟨g, hg⟩ := exists_conj_mul_of_not_induced tau6_not_mem_range hc
    refine ⟨iotaSp.symm g, fun y => ?_⟩
    rw [hg, MulAut.mul_apply, coe_conjAlt6, coe_tau6]
    simp [map_mul]

end Sp4Inf

end CFSG.Quasithin
