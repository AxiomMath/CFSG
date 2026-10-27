module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMap
public import CFSG.LieType.SpinGeom.Elt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LieType.SpinGeom
open scoped Matrix

attribute [-instance] CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

private theorem sixteenC8SpinStabS_isElemAbelianOfRank_of_card {X : Type*} [Group X] [Finite X]
    (hc : ∀ x y : X, x * y = y * x) (hsq : ∀ x : X, x * x = 1) {n : ℕ}
    (hcard : Nat.card X = 2 ^ n) :
    CFSG.Quasithin.IsElemAbelianOfRank 2 n X := by
  let _ : CommGroup X := { ‹Group X› with mul_comm := hc }
  have h2 : ∀ x : Additive X, (2 : ℕ) • x = 0 := by
    intro x
    have : (2 : ℕ) • Additive.ofMul (Additive.toMul x) = Additive.ofMul (Additive.toMul x ^ 2) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at this
    rw [this, pow_two, hsq]
    rfl
  let _ : Module (ZMod 2) (Additive X) := AddCommGroup.zmodModule h2
  have : Finite (Additive X) := inferInstanceAs (Finite X)
  have : Module.Finite (ZMod 2) (Additive X) := Module.Finite.of_finite
  let bas := Module.finBasis (ZMod 2) (Additive X)
  have hd : Module.finrank (ZMod 2) (Additive X) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
    have hcard' : Nat.card (Additive X) = 2 ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive X ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    bas.equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

private theorem sixteenC8SpinStabS_mem_P_iff (p : MulAut SpinW) :
    p ∈ ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0)) ↔
      ∃ t : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) ×
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        spinHom (sE t.1 t.2.1 t.2.2) = p := by
  constructor
  · intro hp
    change p ∈ spinH ⊓ MulAction.stabilizer (MulAut SpinW)
      (Multiplicative.ofAdd (frameE (ZMod 2) 0)) at hp
    rw [Subgroup.mem_inf] at hp
    obtain ⟨hpH, hpstab⟩ := hp
    obtain ⟨g, hgS, hgg⟩ := (mem_spinH_iff p).1 hpH
    have hfixw : spinHom g (Multiplicative.ofAdd (frameE (ZMod 2) 0)) =
        Multiplicative.ofAdd (frameE (ZMod 2) 0) := by
      have h := MulAction.mem_stabilizer_iff.mp hpstab
      rw [← hgg] at h
      exact h
    have hfix : (((g : GL (Fin (2 * 4)) (ZMod 2)) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ frameE (ZMod 2) 0) =
        frameE (ZMod 2) 0 := by
      have h := hfixw
      rw [spinHom_apply] at h
      exact Multiplicative.ofAdd.injective h
    obtain ⟨c, m, gm, hgdet, hact⟩ := spinStabNormalForm_of_count (K := ZMod 2)
      (fun c m g hg => exists_mem_spinSeven_spinElt c m g hg)
      (fun b hb hQ => spinSeven_transitive (ZMod 2) b hb hQ) g hgS hfix
    refine ⟨(c, m, ⟨gm, hgdet⟩), ?_⟩
    have hg_eq : g = sE c m ⟨gm, hgdet⟩ := sE_eq_of_act hact
    rw [← hg_eq]
    exact hgg
  · rintro ⟨t, rfl⟩
    change spinHom (sE t.1 t.2.1 t.2.2) ∈ spinH ⊓ MulAction.stabilizer (MulAut SpinW)
      (Multiplicative.ofAdd (frameE (ZMod 2) 0))
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.mem_map_of_mem spinHom (sE_mem t.1 t.2.1 t.2.2), ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    change spinHom (sE t.1 t.2.1 t.2.2) (Multiplicative.ofAdd (frameE (ZMod 2) 0)) =
      Multiplicative.ofAdd (frameE (ZMod 2) 0)
    rw [spinHom_apply]
    exact congrArg Multiplicative.ofAdd (sE_fix t.1 t.2.1 t.2.2)

private theorem sixteenC8SpinStabS_sE_sl_inj {c m c' m' : Fin 3 → ZMod 2}
    {s s' : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (h : sE c m s = sE c' m' s') : s = s' := by
  have h2 : ∀ v, spinElt (ZMod 2) c m (s : Matrix (Fin 3) (Fin 3) (ZMod 2)) v =
      spinElt (ZMod 2) c' m' (s' : Matrix (Fin 3) (Fin 3) (ZMod 2)) v := by
    intro v
    rw [← sE_act c m s v, ← sE_act c' m' s' v]
    exact congrArg (fun x : CFSG.StandardType.Triality.Om8 (ZMod 2) =>
      (((x : GL (Fin (2 * 4)) (ZMod 2)) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ v)) h
  exact Subtype.ext (spinElt_injective h2).2.2

private noncomputable def sixteenC8SpinStabS_data
    (p : ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0)))) :
    (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) × Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  Classical.choose ((sixteenC8SpinStabS_mem_P_iff p.1).1 p.2)

private theorem sixteenC8SpinStabS_data_spec
    (p : ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0)))) :
    spinHom (sE (sixteenC8SpinStabS_data p).1
      (sixteenC8SpinStabS_data p).2.1 (sixteenC8SpinStabS_data p).2.2) = p.1 :=
  Classical.choose_spec ((sixteenC8SpinStabS_mem_P_iff p.1).1 p.2)

private noncomputable abbrev sixteenC8SpinStabS_phiFun
    (p : ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0)))) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (sixteenC8SpinStabS_data p).2.2

private theorem sixteenC8SpinStabS_sE_one_mul (c₁ m₁ c₂ m₂ : Fin 3 → ZMod 2) :
    sE c₁ m₁ 1 * sE c₂ m₂ 1 =
      sE (c₁ + c₂ + CFSG.LieType.SpinGeom.altMat (ZMod 2) m₂ *ᵥ m₁) (m₁ + m₂) 1 := by
  rw [sE_mul]
  simp [Matrix.adjugate_one]

private theorem sixteenC8SpinStabS_phiFun_mul
    (p q : ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0)))) :
    sixteenC8SpinStabS_phiFun (p * q) =
      sixteenC8SpinStabS_phiFun p * sixteenC8SpinStabS_phiFun q := by
  have hmul : sE (sixteenC8SpinStabS_data (p * q)).1
        (sixteenC8SpinStabS_data (p * q)).2.1 (sixteenC8SpinStabS_data (p * q)).2.2 =
      sE (sixteenC8SpinStabS_data p).1
          (sixteenC8SpinStabS_data p).2.1 (sixteenC8SpinStabS_data p).2.2 *
        sE (sixteenC8SpinStabS_data q).1
          (sixteenC8SpinStabS_data q).2.1 (sixteenC8SpinStabS_data q).2.2 := by
    apply spinHom_injective
    rw [map_mul, sixteenC8SpinStabS_data_spec (p * q),
      sixteenC8SpinStabS_data_spec p, sixteenC8SpinStabS_data_spec q]
    rfl
  rw [sE_mul] at hmul
  exact sixteenC8SpinStabS_sE_sl_inj hmul

private noncomputable def sixteenC8SpinStabS_phi :
    ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0))) →*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun := sixteenC8SpinStabS_phiFun
  map_one' := by
    have hone : sE (sixteenC8SpinStabS_data 1).1
          (sixteenC8SpinStabS_data 1).2.1 (sixteenC8SpinStabS_data 1).2.2 =
        sE 0 0 1 := by
      apply spinHom_injective
      rw [sixteenC8SpinStabS_data_spec 1, sE_one, map_one]
      rfl
    exact sixteenC8SpinStabS_sE_sl_inj hone
  map_mul' := sixteenC8SpinStabS_phiFun_mul

private theorem sixteenC8SpinStabS_phi_surjective :
    Function.Surjective sixteenC8SpinStabS_phi := by
  intro s
  let p : ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0))) :=
    ⟨spinHom (sE 0 0 s),
      (sixteenC8SpinStabS_mem_P_iff _).2 ⟨(0, 0, s), rfl⟩⟩
  refine ⟨p, ?_⟩
  show (sixteenC8SpinStabS_data p).2.2 = s
  have h : sE (sixteenC8SpinStabS_data p).1
        (sixteenC8SpinStabS_data p).2.1 (sixteenC8SpinStabS_data p).2.2 =
      sE 0 0 s := by
    apply spinHom_injective
    rw [sixteenC8SpinStabS_data_spec p]
  exact sixteenC8SpinStabS_sE_sl_inj h

private theorem sixteenC8SpinStabS_mem_ker_iff
    (p : ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0)))) :
    p ∈ sixteenC8SpinStabS_phi.ker ↔
      ∃ c m : Fin 3 → ZMod 2, spinHom (sE c m 1) = p.1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hp
    have hp' : (sixteenC8SpinStabS_data p).2.2 = 1 := hp
    refine ⟨(sixteenC8SpinStabS_data p).1, (sixteenC8SpinStabS_data p).2.1, ?_⟩
    have h1 : sE (sixteenC8SpinStabS_data p).1
          (sixteenC8SpinStabS_data p).2.1 (sixteenC8SpinStabS_data p).2.2 =
        sE (sixteenC8SpinStabS_data p).1 (sixteenC8SpinStabS_data p).2.1 1 := by
      rw [hp']
    rw [← h1, sixteenC8SpinStabS_data_spec p]
  · rintro ⟨c, m, h⟩
    change (sixteenC8SpinStabS_data p).2.2 = 1
    have h1 : sE (sixteenC8SpinStabS_data p).1
          (sixteenC8SpinStabS_data p).2.1 (sixteenC8SpinStabS_data p).2.2 =
        sE c m 1 := by
      apply spinHom_injective
      rw [sixteenC8SpinStabS_data_spec p, h]
    exact sixteenC8SpinStabS_sE_sl_inj h1

private noncomputable def sixteenC8SpinStabS_kappa
    (cm : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) :
    ↥sixteenC8SpinStabS_phi.ker where
  val := ⟨spinHom (sE cm.1 cm.2 1),
    (sixteenC8SpinStabS_mem_P_iff _).2 ⟨(cm.1, cm.2, 1), rfl⟩⟩
  property := (sixteenC8SpinStabS_mem_ker_iff _).2 ⟨cm.1, cm.2, rfl⟩

private theorem sixteenC8SpinStabS_kappa_injective :
    Function.Injective sixteenC8SpinStabS_kappa := by
  intro a b hab
  have hab' : spinHom (sE a.1 a.2 1) = spinHom (sE b.1 b.2 1) := by
    have h := congrArg (fun x : ↥sixteenC8SpinStabS_phi.ker => (x.1.1 : MulAut SpinW)) hab
    exact h
  have h2 : sE a.1 a.2 1 = sE b.1 b.2 1 := spinHom_injective hab'
  have h3 : ∀ v, spinElt (ZMod 2) a.1 a.2 ((1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) v =
      spinElt (ZMod 2) b.1 b.2 ((1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) v := by
    intro v
    rw [← sE_act a.1 a.2 (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) v,
      ← sE_act b.1 b.2 (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) v]
    exact congrArg (fun x : CFSG.StandardType.Triality.Om8 (ZMod 2) =>
      (((x : GL (Fin (2 * 4)) (ZMod 2)) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ v)) h2
  obtain ⟨hc, hm, _⟩ := spinElt_injective h3
  exact Prod.ext hc hm

private theorem sixteenC8SpinStabS_kappa_surjective :
    Function.Surjective sixteenC8SpinStabS_kappa := by
  intro x
  obtain ⟨c, m, hcm⟩ := (sixteenC8SpinStabS_mem_ker_iff x.1).1 x.2
  refine ⟨(c, m), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hcm

private theorem sixteenC8SpinStabS_card_ker :
    Nat.card ↥sixteenC8SpinStabS_phi.ker = 2 ^ 6 := by
  let e : (Fin 3 → ZMod 2) × (Fin 3 → ZMod 2) ≃ ↥sixteenC8SpinStabS_phi.ker :=
    Equiv.ofBijective sixteenC8SpinStabS_kappa
      ⟨sixteenC8SpinStabS_kappa_injective, sixteenC8SpinStabS_kappa_surjective⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  norm_num

private theorem sixteenC8SpinStabS_ker_comm (x y : ↥sixteenC8SpinStabS_phi.ker) :
    x * y = y * x := by
  obtain ⟨c₁, m₁, h₁⟩ := (sixteenC8SpinStabS_mem_ker_iff x.1).1 x.2
  obtain ⟨c₂, m₂, h₂⟩ := (sixteenC8SpinStabS_mem_ker_iff y.1).1 y.2
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  show x.1.1 (y.1.1 w) = y.1.1 (x.1.1 w)
  rw [← h₁, ← h₂]
  show (spinHom (sE c₁ m₁ 1) * spinHom (sE c₂ m₂ 1)) w =
    (spinHom (sE c₂ m₂ 1) * spinHom (sE c₁ m₁ 1)) w
  rw [← map_mul, ← map_mul, sixteenC8SpinStabS_sE_one_mul, sixteenC8SpinStabS_sE_one_mul]
  rw [show c₁ + c₂ + CFSG.LieType.SpinGeom.altMat (ZMod 2) m₂ *ᵥ m₁ =
      c₂ + c₁ + CFSG.LieType.SpinGeom.altMat (ZMod 2) m₁ *ᵥ m₂ from by
        rw [CFSG.LieType.SpinGeom.altMat_mulVec_comm]; abel,
    show m₁ + m₂ = m₂ + m₁ from add_comm _ _]

private theorem sixteenC8SpinStabS_ker_sq (x : ↥sixteenC8SpinStabS_phi.ker) :
    x * x = 1 := by
  obtain ⟨c, m, h⟩ := (sixteenC8SpinStabS_mem_ker_iff x.1).1 x.2
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  show x.1.1 (x.1.1 w) = w
  rw [← h]
  show (spinHom (sE c m 1) * spinHom (sE c m 1)) w = w
  rw [← map_mul, sixteenC8SpinStabS_sE_one_mul]
  have hc : c + c + CFSG.LieType.SpinGeom.altMat (ZMod 2) m *ᵥ m = 0 := by
    rw [CFSG.LieType.SpinGeom.altMat_mulVec_self, add_zero]
    ext i
    exact CharTwo.add_self_eq_zero (c i)
  have hm : m + m = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero (m i)
  rw [hc, hm, sE_one, map_one]
  rfl

private theorem sixteenC8SpinStabS_ker_elemAbelian :
    IsElemAbelianOfRank 2 6 ↥sixteenC8SpinStabS_phi.ker :=
  sixteenC8SpinStabS_isElemAbelianOfRank_of_card
    (fun x y => sixteenC8SpinStabS_ker_comm x y)
    (fun x => sixteenC8SpinStabS_ker_sq x)
    sixteenC8SpinStabS_card_ker

theorem exists_stabHom_E0 :
    ∃ φ : ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0))) →*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective φ ∧ IsElemAbelianOfRank 2 6 ↥φ.ker :=
  ⟨sixteenC8SpinStabS_phi, sixteenC8SpinStabS_phi_surjective,
    sixteenC8SpinStabS_ker_elemAbelian⟩

theorem isE64L3_ptCent_E0 :
    IsE64L3 ↥(ptCent spinH (Multiplicative.ofAdd (frameE (ZMod 2) 0))) := by
  obtain ⟨φ, hφ, hab⟩ := exists_stabHom_E0
  exact ⟨φ.ker, inferInstance, hab,
    CFSG.LocalAnalysis.WeakClosure81.ThreeOne.isL3_of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
