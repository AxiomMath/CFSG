module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKMcLDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Adapters.RankTwoModelTransports Matrix

theorem s15k_norm_nat_extract {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : (FFModel.nat Γ).Realizes J R ⊥) :
    ∃ (π : ↥Γ →* ↥J) (b : ↥R ≃* Multiplicative (ι → K)), Function.Surjective π ∧
      (∀ (j : ↥J) (r : ↥R), (j : MulAut W) (r : W) ∈ R) ∧
      ∀ (γ : ↥Γ) (r : ↥R) (hr : ((π γ : ↥J) : MulAut W) (r : W) ∈ R),
        b ⟨((π γ : ↥J) : MulAut W) (r : W), hr⟩ = natAct Γ γ (b r) := by
  obtain ⟨π, hsurj, -, -, hUinv, -, -, -, β, hβs, hβk, hβe⟩ := h
  let q : ↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
      (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤ ≃* Multiplicative (ι → K) :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf ⊤)).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  let b0 : ↥R →* Multiplicative (ι → K) := q.toMonoidHom.comp β
  have hinj : Function.Injective b0 := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : β u = 1 := by
      have h0 : q (β u) = 1 := hu
      exact q.injective (h0.trans (map_one q).symm)
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 h1))
  have hsur : Function.Surjective b0 := by
    intro y
    obtain ⟨u, hu⟩ := hβs (q.symm y)
    exact ⟨u, by
      show q (β u) = y
      rw [hu]
      exact q.apply_symm_apply y⟩
  refine ⟨π, MulEquiv.ofBijective b0 ⟨hinj, hsur⟩, hsurj, fun j r => hUinv j r r.2, ?_⟩
  intro γ r hr
  have hmem : (b0 r : Multiplicative (ι → K)) ∈ (FFModel.nat Γ).sec := trivial
  have hm' : (FFModel.nat Γ).act γ (b0 r) ∈ (FFModel.nat Γ).sec := trivial
  have hβr : β r = QuotientGroup.mk (⟨b0 r, hmem⟩ : ↥(FFModel.nat Γ).sec) := by
    apply q.injective
    exact rfl
  have h1 := hβe γ r ⟨b0 r, hmem⟩ hr hm' hβr
  exact congrArg q h1

theorem s15k_norm_nat_zmod2 {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι (ZMod 2))}
    (hN : ∀ M : Matrix.GeneralLinearGroup ι (ZMod 2),
      (∀ g ∈ Γ, M * g * M⁻¹ ∈ Γ) → M ∈ Γ)
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : (FFModel.nat Γ).Realizes J R ⊥)
    {x : MulAut W} (hx : x ∈ stabSub R) (hxJ : ∀ j : MulAut W, j ∈ J ↔ x * j * x⁻¹ ∈ J) :
    ∃ j ∈ J, ∀ r ∈ R, x r = j r := by
  obtain ⟨π, b, hπ, hstab, hb⟩ := s15k_norm_nat_extract h
  have hxi : x⁻¹ ∈ stabSub R := (stabSub R).inv_mem hx
  let xe : ↥R ≃* ↥R :=
    { toFun := fun r => ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩
      invFun := fun r => ⟨x⁻¹ r, (mem_stabSub.1 hxi r).2 r.2⟩
      left_inv := fun r => Subtype.ext (MulAut.inv_apply_self W x r)
      right_inv := fun r => Subtype.ext (MulAut.apply_inv_self W x r)
      map_mul' := fun a c => Subtype.ext (map_mul x (a : W) (c : W)) }
  let Ae : Multiplicative (ι → ZMod 2) ≃* Multiplicative (ι → ZMod 2) :=
    b.symm.trans (xe.trans b)
  let Ae' : (ι → ZMod 2) ≃+ (ι → ZMod 2) := AddEquiv.toMultiplicative.symm Ae
  have hAe : ∀ r : ↥R, Ae' (Multiplicative.toAdd (b r)) =
      Multiplicative.toAdd (b ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩) := by
    intro r
    show Multiplicative.toAdd (Ae (Multiplicative.ofAdd (Multiplicative.toAdd (b r)))) = _
    simp [Ae, xe]
  let Alin : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
    { toFun := Ae'
      map_add' := Ae'.map_add
      map_smul' := fun c v => by
        have hc : c = 0 ∨ c = 1 := by
          revert c
          decide
        rcases hc with rfl | rfl
        · simp
        · simp
      invFun := Ae'.symm
      left_inv := Ae'.left_inv
      right_inv := Ae'.right_inv }
  let M : Matrix.GeneralLinearGroup ι (ZMod 2) :=
    Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2)).symm Alin)
  have hM : ∀ v, (M : Matrix ι ι (ZMod 2)) *ᵥ v = Ae' v := by
    intro v
    have h1 := Matrix.GeneralLinearGroup.toLin_apply M v
    rw [Matrix.mulVecLin_apply] at h1
    rw [← h1]
    have h2 : Matrix.GeneralLinearGroup.toLin M =
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (ι → ZMod 2)).symm Alin :=
      MulEquiv.apply_symm_apply _ _
    rw [h2, ← LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, MulEquiv.apply_symm_apply]
    rfl
  have hMb : ∀ r : ↥R, (M : Matrix ι ι (ZMod 2)) *ᵥ Multiplicative.toAdd (b r) =
      Multiplicative.toAdd (b ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩) := fun r => (hM _).trans (hAe r)
  have hbγ : ∀ (γ : ↥Γ) (r : ↥R) (hr : ((π γ : ↥J) : MulAut W) (r : W) ∈ R),
      Multiplicative.toAdd (b ⟨((π γ : ↥J) : MulAut W) (r : W), hr⟩) =
        ((γ : Matrix.GeneralLinearGroup ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
          Multiplicative.toAdd (b r) := fun γ r hr => congrArg Multiplicative.toAdd (hb γ r hr)
  have hnorm : ∀ g ∈ Γ, M * g * M⁻¹ ∈ Γ := by
    intro g hg
    have hmem : x * ((π ⟨g, hg⟩ : ↥J) : MulAut W) * x⁻¹ ∈ J := (hxJ _).1 (π ⟨g, hg⟩).2
    obtain ⟨γ', hγ'⟩ := hπ ⟨x * ((π ⟨g, hg⟩ : ↥J) : MulAut W) * x⁻¹, hmem⟩
    have hγ'' : ((π γ' : ↥J) : MulAut W) = x * ((π ⟨g, hg⟩ : ↥J) : MulAut W) * x⁻¹ :=
      congrArg Subtype.val hγ'
    have key : M * g = (γ' : Matrix.GeneralLinearGroup ι (ZMod 2)) * M := by
      apply Units.ext
      apply Matrix.ext_iff_mulVec.2
      intro v
      obtain ⟨r, hr⟩ := b.surjective (Multiplicative.ofAdd v)
      have hv : v = Multiplicative.toAdd (b r) := by rw [hr]; rfl
      subst hv
      have hjr : ((π ⟨g, hg⟩ : ↥J) : MulAut W) (r : W) ∈ R := hstab _ r
      have h1 : ((M * g : Matrix.GeneralLinearGroup ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
          Multiplicative.toAdd (b r) = Multiplicative.toAdd (b ⟨x (((π ⟨g, hg⟩ : ↥J) :
            MulAut W) (r : W)), (mem_stabSub.1 hx _).2 hjr⟩) := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        have := hbγ ⟨g, hg⟩ r hjr
        rw [← this]
        exact hMb ⟨_, hjr⟩
      have h2 : (((γ' : Matrix.GeneralLinearGroup ι (ZMod 2)) * M : Matrix.GeneralLinearGroup ι
          (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ Multiplicative.toAdd (b r) =
          Multiplicative.toAdd (b ⟨x (((π ⟨g, hg⟩ : ↥J) : MulAut W) (r : W)),
            (mem_stabSub.1 hx _).2 hjr⟩) := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, hMb r]
        have hxr : ((π γ' : ↥J) : MulAut W) (x (r : W)) ∈ R :=
          hstab _ ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩
        have := hbγ γ' ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩ hxr
        rw [← this]
        congr 3
        show ((π γ' : ↥J) : MulAut W) (x (r : W)) = x (((π ⟨g, hg⟩ : ↥J) : MulAut W) (r : W))
        rw [hγ'']
        simp
      exact h1.trans h2.symm
    have : M * g * M⁻¹ = (γ' : Matrix.GeneralLinearGroup ι (ZMod 2)) := by
      rw [key, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact γ'.2
  have hMΓ : M ∈ Γ := hN M hnorm
  refine ⟨((π ⟨M, hMΓ⟩ : ↥J) : MulAut W), (π ⟨M, hMΓ⟩).2, fun r hr => ?_⟩
  have hjr : ((π ⟨M, hMΓ⟩ : ↥J) : MulAut W) r ∈ R := hstab _ ⟨r, hr⟩
  have h1 := hbγ ⟨M, hMΓ⟩ ⟨r, hr⟩ hjr
  have h2 := hMb ⟨r, hr⟩
  have h3 : b ⟨((π ⟨M, hMΓ⟩ : ↥J) : MulAut W) r, hjr⟩ =
      b ⟨x r, (mem_stabSub.1 hx r).2 hr⟩ := by
    apply Multiplicative.toAdd.injective
    rw [h1]
    exact h2
  have h4 := congrArg Subtype.val (b.injective h3)
  exact h4.symm

theorem s15k_norm_nat_of_field {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (e : K ≃+* ZMod 2) {ΓK : Subgroup (Matrix.GeneralLinearGroup ι K)}
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι (ZMod 2))}
    (hΓ : ΓK.map (glCongr (ι := ι) e).toMonoidHom = Γ)
    (hN : ∀ M : Matrix.GeneralLinearGroup ι (ZMod 2),
      (∀ g ∈ Γ, M * g * M⁻¹ ∈ Γ) → M ∈ Γ)
    {J : Subgroup (MulAut W)} {R : Subgroup W} (h : (FFModel.nat ΓK).Realizes J R ⊥)
    {x : MulAut W} (hx : x ∈ stabSub R) (hxJ : ∀ j : MulAut W, j ∈ J ↔ x * j * x⁻¹ ∈ J) :
    ∃ j ∈ J, ∀ r ∈ R, x r = j r :=
  s15k_norm_nat_zmod2 hN (s15k_jp_nat_transport e hΓ h) hx hxJ

theorem s15k_norm_mcrep {W : Type} [CommGroup W] {J : Subgroup (MulAut W)} {R : Subgroup W}
    (D : McRep J R)
    (hN : ∀ A : LinearMap.GeneralLinearGroup (ZMod 2) D.V,
      (∀ y ∈ D.ρ.range, A * y * A⁻¹ ∈ D.ρ.range) → A ∈ D.ρ.range)
    {x : MulAut W} (hx : x ∈ stabSub R) (hxJ : ∀ j : MulAut W, j ∈ J ↔ x * j * x⁻¹ ∈ J) :
    ∃ j ∈ J, ∀ r ∈ R, x r = j r := by
  have hxi : x⁻¹ ∈ stabSub R := (stabSub R).inv_mem hx
  let xe : ↥R ≃* ↥R :=
    { toFun := fun r => ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩
      invFun := fun r => ⟨x⁻¹ r, (mem_stabSub.1 hxi r).2 r.2⟩
      left_inv := fun r => Subtype.ext (MulAut.inv_apply_self W x r)
      right_inv := fun r => Subtype.ext (MulAut.apply_inv_self W x r)
      map_mul' := fun a c => Subtype.ext (map_mul x (a : W) (c : W)) }
  let Ae : Multiplicative D.V ≃* Multiplicative D.V := D.e.symm.trans (xe.trans D.e)
  let Ae' : D.V ≃+ D.V := AddEquiv.toMultiplicative.symm Ae
  have hAe : ∀ r : ↥R, Ae' (Multiplicative.toAdd (D.e r)) =
      Multiplicative.toAdd (D.e ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩) := by
    intro r
    show Multiplicative.toAdd (Ae (Multiplicative.ofAdd (Multiplicative.toAdd (D.e r)))) = _
    simp [Ae, xe]
  let Alin : D.V ≃ₗ[ZMod 2] D.V :=
    { toFun := Ae'
      map_add' := Ae'.map_add
      map_smul' := fun c v => by
        have hc : c = 0 ∨ c = 1 := by
          revert c
          decide
        rcases hc with rfl | rfl
        · simp
        · simp
      invFun := Ae'.symm
      left_inv := Ae'.left_inv
      right_inv := Ae'.right_inv }
  let A : LinearMap.GeneralLinearGroup (ZMod 2) D.V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) D.V).symm Alin
  have hA : ∀ v : D.V, (A : D.V →ₗ[ZMod 2] D.V) v = Ae' v := by
    intro v
    rw [← LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, MulEquiv.apply_symm_apply]
    rfl
  have hAr : ∀ r : ↥R, (A : D.V →ₗ[ZMod 2] D.V) (Multiplicative.toAdd (D.e r)) =
      Multiplicative.toAdd (D.e ⟨x r, (mem_stabSub.1 hx r).2 r.2⟩) := fun r => (hA _).trans (hAe r)
  have hAi : ∀ r : ↥R, ((A⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
      D.V →ₗ[ZMod 2] D.V) (Multiplicative.toAdd (D.e r)) =
      Multiplicative.toAdd (D.e ⟨x⁻¹ r, (mem_stabSub.1 hxi r).2 r.2⟩) := by
    intro r
    have h1 := hAr ⟨x⁻¹ r, (mem_stabSub.1 hxi r).2 r.2⟩
    have h2 : (⟨x (x⁻¹ (r : W)), (mem_stabSub.1 hx _).2 (mem_stabSub.1 hxi r |>.2 r.2)⟩ : ↥R) =
        r := Subtype.ext (MulAut.apply_inv_self W x r)
    rw [h2] at h1
    have h3 := congrArg (fun v => ((A⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
      D.V →ₗ[ZMod 2] D.V) v) h1
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel] at h3
    exact h3.symm
  have hnorm : ∀ y ∈ D.ρ.range, A * y * A⁻¹ ∈ D.ρ.range := by
    rintro y ⟨j, rfl⟩
    have hmem : x * (j : MulAut W) * x⁻¹ ∈ J := (hxJ _).1 j.2
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext v
    obtain ⟨r, hr⟩ := D.e.surjective (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (D.e r) := by rw [hr]; rfl
    subst hv
    have hxi' : (x⁻¹ : MulAut W) (r : W) ∈ R := (mem_stabSub.1 hxi r).2 r.2
    have hj : (j : MulAut W) (x⁻¹ (r : W)) ∈ R := D.stable j j.2 _ hxi'
    have h1 := D.hρ j ⟨x⁻¹ r, hxi'⟩ hj
    have h2 := D.hρ ⟨_, hmem⟩ r (by
      show (x * (j : MulAut W) * x⁻¹) (r : W) ∈ R
      exact (mem_stabSub.1 hx _).2 hj)
    show ((D.ρ ⟨_, hmem⟩ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) : D.V →ₗ[ZMod 2] D.V)
      (Multiplicative.toAdd (D.e r)) =
      ((A * D.ρ j * A⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) : D.V →ₗ[ZMod 2] D.V)
        (Multiplicative.toAdd (D.e r))
    have h3 : ((A * D.ρ j * A⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) :
        D.V →ₗ[ZMod 2] D.V) (Multiplicative.toAdd (D.e r)) =
        (A : D.V →ₗ[ZMod 2] D.V) ((D.ρ j : D.V →ₗ[ZMod 2] D.V)
          (((A⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) D.V) : D.V →ₗ[ZMod 2] D.V)
            (Multiplicative.toAdd (D.e r)))) := rfl
    rw [h3, hAi r]
    have h4 : (D.ρ j : D.V →ₗ[ZMod 2] D.V) (Multiplicative.toAdd (D.e ⟨x⁻¹ r, hxi'⟩)) =
        Multiplicative.toAdd (D.e ⟨(j : MulAut W) (x⁻¹ (r : W)), hj⟩) := by
      rw [h1, toAdd_ofAdd]
    rw [h4, hAr ⟨(j : MulAut W) (x⁻¹ (r : W)), hj⟩]
    have h5 := congrArg Multiplicative.toAdd h2
    rw [toAdd_ofAdd] at h5
    rw [← h5]
    rfl
  obtain ⟨j, hj⟩ := hN A hnorm
  refine ⟨(j : MulAut W), j.2, fun r hr => ?_⟩
  have hjr : (j : MulAut W) r ∈ R := D.stable j j.2 r hr
  have h1 := D.hρ j ⟨r, hr⟩ hjr
  have h2 := hAr ⟨r, hr⟩
  have h3 : D.e ⟨(j : MulAut W) r, hjr⟩ = D.e ⟨x r, (mem_stabSub.1 hx r).2 hr⟩ := by
    apply Multiplicative.toAdd.injective
    rw [h1, toAdd_ofAdd, hj, h2]
  exact (congrArg Subtype.val (D.e.injective h3)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
