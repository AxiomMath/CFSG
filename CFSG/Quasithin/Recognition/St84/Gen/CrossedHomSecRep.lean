module

public import CFSG.Quasithin.Recognition.St84.Gen.CrossedHomPrincipal
public import CFSG.Quasithin.Recognition.St84.Gen.H1HomForm
public import CFSG.Quasithin.Recognition.St84.Gen.InvariantBilinUnique
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LMod

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.H13.NFa2 CFSG.GroupTheory

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']

private noncomputable def secFactor {Q Z N : Subgroup G} {W H : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [CommGroup H]
    (s : SecRep N Z Q W) (f : ↥Q →* H)
    (hf : ∀ z : ↥Q, (z : G) ∈ Z → f z = 1) (w : W) : Additive H :=
  Additive.ofMul (f (Classical.choose (s.exists_cl w)))

private theorem secFactor_cl {Q Z N : Subgroup G} {W H : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [CommGroup H]
    (s : SecRep N Z Q W) (f : ↥Q →* H)
    (hf : ∀ z : ↥Q, (z : G) ∈ Z → f z = 1) (u : ↥Q) :
    secFactor s f hf (s.cl u) = Additive.ofMul (f u) := by
  classical
  set u₀ := Classical.choose (s.exists_cl (s.cl u)) with hu₀
  have hu₀' : s.cl u₀ = s.cl u := Classical.choose_spec (s.exists_cl (s.cl u))
  have hmem : ((u₀⁻¹ * u : ↥Q) : G) ∈ Z := by
    simpa using (s.cl_eq_iff u₀ u).mp hu₀'.symm
  have h1 : f u = f u₀ := by
    rw [show u = u₀ * (u₀⁻¹ * u) from (mul_inv_cancel_left u₀ u).symm, map_mul,
      hf _ hmem, mul_one]
  change Additive.ofMul (f u₀) = Additive.ofMul (f u)
  rw [h1]

private theorem secFactor_add {Q Z N : Subgroup G} {W H : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [CommGroup H]
    (s : SecRep N Z Q W) (f : ↥Q →* H)
    (hf : ∀ z : ↥Q, (z : G) ∈ Z → f z = 1) (w₁ w₂ : W) :
    secFactor s f hf (w₁ + w₂) = secFactor s f hf w₁ + secFactor s f hf w₂ := by
  classical
  obtain ⟨u₁, hu₁⟩ := s.exists_cl w₁
  obtain ⟨u₂, hu₂⟩ := s.exists_cl w₂
  rw [← hu₁, ← hu₂, ← s.cl_mul, secFactor_cl s f hf (u₁ * u₂),
    secFactor_cl s f hf u₁, secFactor_cl s f hf u₂, map_mul]
  exact ofMul_mul _ _

private noncomputable def secFactorAddHom {Q Z N : Subgroup G} {W H : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [CommGroup H]
    (s : SecRep N Z Q W) (f : ↥Q →* H)
    (hf : ∀ z : ↥Q, (z : G) ∈ Z → f z = 1) : W →+ Additive H where
  toFun := secFactor s f hf
  map_zero' := by
    have h := secFactor_cl s f hf (1 : ↥Q)
    rw [show s.cl (1 : ↥Q) = 0 from by simp [SecRep.cl]] at h
    simpa using h
  map_add' := secFactor_add s f hf

private noncomputable def secFactorLin {Q Z N : Subgroup G} {W H : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [CommGroup H]
    [Module (ZMod 2) (Additive H)]
    (s : SecRep N Z Q W) (f : ↥Q →* H)
    (hf : ∀ z : ↥Q, (z : G) ∈ Z → f z = 1) : W →ₗ[ZMod 2] Additive H :=
  (secFactorAddHom s f hf).toZModLinearMap 2

private theorem secFactorLin_cl {Q Z N : Subgroup G} {W H : Type}
    [AddCommGroup W] [Module (ZMod 2) W] [CommGroup H]
    [Module (ZMod 2) (Additive H)]
    (s : SecRep N Z Q W) (f : ↥Q →* H)
    (hf : ∀ z : ↥Q, (z : G) ∈ Z → f z = 1) (u : ↥Q) :
    secFactorLin s f hf (s.cl u) = Additive.ofMul (f u) :=
  secFactor_cl s f hf u

private theorem zmod_two_smul_eq_zero {Z' : Subgroup G'}
    (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1) (v : Additive ↥Z') : 2 • v = 0 := by
  rw [two_nsmul]
  change Additive.ofMul (Additive.toMul v * Additive.toMul v) = Additive.ofMul (1 : ↥Z')
  rw [← pow_two]
  congr 1
  apply Subtype.ext
  simpa using hZ'2 ((Additive.toMul v : ↥Z') : G') (Additive.toMul v).2

theorem crossedHomPrincipalOn_of_secRep {Q Z R N : Subgroup G} {Z' R' : Subgroup G'}
    (e : ↥R ≃* ↥R') (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (hNR : N ≤ R)
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a) (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (hNZ' : ∀ n : ↥R, (n : G) ∈ N → ∀ z ∈ Z', (e n : G') * z * (e n : G')⁻¹ = z)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (s : SecRep N Z Q W)
    (ρ : Representation (ZMod 2) ↥N W) (hρ : ∀ n w, ρ n w = s.ρ n w)
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hB : ∀ n x y, B (ρ n x) (ρ n y) = B x y)
    (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hH1 : ∀ φ : ↥N → W, φ ∈ Z1 ρ → φ ∈ B1 ρ) :
    CrossedHomPrincipalOn Q Z R N Z' R' e := by
  classical
  intro δ hZδ hcoc
  haveI hZ'comm : IsMulCommutative ↥Z' :=
    ⟨⟨fun a b => Subtype.ext (hZ'c (a : G') a.2 (b : G') b.2)⟩⟩
  letI : CommGroup ↥Z' := IsMulCommutative.instCommGroup
  haveI : Finite ↥Z' := Subtype.finite
  letI : Module (ZMod 2) (Additive ↥Z') :=
    AddCommGroup.zmodModule (zmod_two_smul_eq_zero hZ'2)
  haveI : Finite (Additive ↥Z') := inferInstanceAs (Finite ↥Z')
  haveI : Module.Finite (ZMod 2) (Additive ↥Z') := Module.Finite.of_finite
  have hNZ : ∀ (n : ↥N) (z : ↥Q), (z : G) ∈ Z → ((n : G) * (z : G) * (n : G)⁻¹) ∈ Z := by
    intro n z hz
    have hz0 : s.cl z = 0 := (s.cl_eq_zero_iff z).mpr hz
    let w : ↥Q := conjHom Q R hRQ ⟨n, hNR n.2⟩ z
    have hw : (w : G) = (n : G) * (z : G) * (n : G)⁻¹ :=
      conjHom_apply hRQ ⟨n, hNR n.2⟩ z
    have hact : s.ρ n (s.cl z) = s.cl w := s.act n z w hw
    rw [hz0, map_zero] at hact
    have hwZ : (w : G) ∈ Z := (s.cl_eq_zero_iff w).mp hact.symm
    rwa [hw] at hwZ
  let fN (n : ↥N) : ↥Q →* ↥Z' :=
    (δ ⟨n, hNR n.2⟩).comp (conjHom Q R hRQ (⟨n, hNR n.2⟩⁻¹)).toMonoidHom
  have hfN : ∀ (n : ↥N) (z : ↥Q), (z : G) ∈ Z → fN n z = 1 := by
    intro n z hz
    have hmem : (((conjHom Q R hRQ (⟨n, hNR n.2⟩⁻¹)) z : ↥Q) : G) ∈ Z := by
      rw [conjHom_apply hRQ (⟨n, hNR n.2⟩⁻¹) z]
      have h := hNZ n⁻¹ z hz
      simpa using h
    exact hZδ ⟨n, hNR n.2⟩ _ hmem
  let D (n : ↥N) : W →ₗ[ZMod 2] Additive ↥Z' := secFactorLin s (fN n) (hfN n)
  have hρeq : ∀ n : ↥N, ρ n = (s.ρ n : W →ₗ[ZMod 2] W) := fun n =>
    LinearMap.ext (hρ n)
  have hlin : ∀ (n : ↥N) (ψ : W →ₗ[ZMod 2] Additive ↥Z'),
      (ρ.linHom (Representation.trivial (ZMod 2) ↥N (Additive ↥Z'))) n ψ =
        ψ.comp (ρ n⁻¹) := by
    intro n ψ
    rw [Representation.linHom_apply,
      Representation.isTrivial_def (Representation.trivial (ZMod 2) ↥N (Additive ↥Z')) n,
      LinearMap.id_comp]
  have hDcoc : D ∈ Z1 (ρ.linHom (Representation.trivial (ZMod 2) ↥N (Additive ↥Z'))) := by
    intro n m
    refine LinearMap.ext fun x => ?_
    obtain ⟨u, rfl⟩ := s.exists_cl x
    let nR : ↥R := ⟨n, hNR n.2⟩
    let mR : ↥R := ⟨m, hNR m.2⟩
    let w0 : ↥Q := (conjHom Q R hRQ nR⁻¹) u
    let v : ↥Q := (conjHom Q R hRQ mR⁻¹) w0
    have hw0 : (w0 : G) = (n : G)⁻¹ * (u : G) * (n : G) := by
      change (((conjHom Q R hRQ nR⁻¹) u : ↥Q) : G) = _
      rw [conjHom_apply hRQ nR⁻¹ u]
      change (n : G)⁻¹ * (u : G) * ((n : G)⁻¹)⁻¹ = (n : G)⁻¹ * (u : G) * (n : G)
      group
    have hv : (v : G) = (m : G)⁻¹ * (w0 : G) * (m : G) := by
      change (((conjHom Q R hRQ mR⁻¹) w0 : ↥Q) : G) = _
      rw [conjHom_apply hRQ mR⁻¹ w0]
      change (m : G)⁻¹ * (w0 : G) * ((m : G)⁻¹)⁻¹ =
        (m : G)⁻¹ * (w0 : G) * (m : G)
      group
    have hwu : (u : G) = (n : G) * (w0 : G) * (n : G)⁻¹ := by
      rw [hw0]
      group
    have hact : s.ρ n (s.cl w0) = s.cl u := s.act n w0 u hwu
    have hsymm : (ρ n⁻¹) (s.cl u) = s.cl w0 := by
      rw [hρeq (n⁻¹), map_inv]
      change (s.ρ n).symm (s.cl u) = s.cl w0
      apply (s.ρ n).injective
      rw [LinearEquiv.apply_symm_apply]
      exact hact.symm
    have hnmR : (⟨n * m, hNR (n * m).2⟩ : ↥R) = nR * mR := Subtype.ext rfl
    have hfn_nm : fN (n * m) u = δ (nR * mR) v := by
      have harg : ((conjHom Q R hRQ (⟨n * m, hNR (n * m).2⟩⁻¹)) u : ↥Q) = v := by
        apply Subtype.ext
        rw [conjHom_apply hRQ (⟨n * m, hNR (n * m).2⟩⁻¹) u, hv, hw0]
        simp only [Subgroup.coe_inv, Subgroup.coe_mul]
        group
      change (δ ⟨n * m, hNR (n * m).2⟩)
        (((conjHom Q R hRQ (⟨n * m, hNR (n * m).2⟩⁻¹)) u)) = δ (nR * mR) v
      rw [harg, hnmR]
    have hfn_n : fN n u = δ nR w0 := rfl
    have hfn_m : fN m w0 = δ mR v := rfl
    rw [LinearMap.add_apply, hlin n (D m), LinearMap.comp_apply, hsymm,
      secFactorLin_cl s (fN (n * m)) (hfN (n * m)) u,
      secFactorLin_cl s (fN n) (hfN n) u,
      secFactorLin_cl s (fN m) (hfN m) w0, hfn_nm, hfn_n, hfn_m,
      ← ofMul_mul]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    have hv' : (w0 : G) = (m : G) * (v : G) * (m : G)⁻¹ := by
      rw [hv]
      group
    have hc := hcoc nR mR v w0 hv'
    have hcent := hNZ' nR n.2 (δ mR v : G') (δ mR v).2
    rw [hcent] at hc
    simpa using hc
  have hD_b1 : D ∈ B1 (ρ.linHom (Representation.trivial (ZMod 2) ↥N (Additive ↥Z'))) :=
    mem_B1_linHom_trivial ρ B hB hBnd hH1 hDcoc
  obtain ⟨φbar, hφbar⟩ := hD_b1
  have hDn : ∀ n : ↥N, D n =
      (ρ.linHom (Representation.trivial (ZMod 2) ↥N (Additive ↥Z'))) n φbar - φbar := by
    intro n
    rw [← congrFun hφbar n]
    rfl
  let φ : ↥Q →* ↥Z' :=
    { toFun := fun u => Additive.toMul (φbar (s.cl u))
      map_one' := by
        simp [SecRep.cl]
      map_mul' := fun a b => by
        rw [s.cl_mul, map_add, toMul_add] }
  have hφZ : ∀ v : ↥Q, (v : G) ∈ Z → φ v = 1 := by
    intro v hv
    change Additive.toMul (φbar (s.cl v)) = 1
    rw [(s.cl_eq_zero_iff v).mpr hv, map_zero, toMul_zero]
  refine ⟨φ, hφZ, ?_⟩
  intro r hr v w hw
  let nN : ↥N := ⟨r, hr⟩
  have hR : (⟨nN, hNR nN.2⟩ : ↥R) = r := Subtype.ext rfl
  have hw' : (w : G) = (nN : G) * (v : G) * (nN : G)⁻¹ := by
    rw [hw]
  have hact : s.ρ nN (s.cl v) = s.cl w := s.act nN v w hw'
  have hsymm : (ρ nN⁻¹) (s.cl w) = s.cl v := by
    rw [hρeq (nN⁻¹), map_inv]
    change (s.ρ nN).symm (s.cl w) = s.cl v
    apply (s.ρ nN).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hact.symm
  have hDv : D nN (s.cl w) = Additive.ofMul (δ r v) := by
    rw [show D nN (s.cl w) = Additive.ofMul (fN nN w) from
      secFactorLin_cl s (fN nN) (hfN nN) w]
    have harg : ((conjHom Q R hRQ (⟨nN, hNR nN.2⟩⁻¹)) w : ↥Q) = v := by
      apply Subtype.ext
      rw [conjHom_apply hRQ (⟨nN, hNR nN.2⟩⁻¹) w]
      have hcoe : ((⟨nN, hNR nN.2⟩⁻¹ : ↥R) : G) = (r : G)⁻¹ := rfl
      rw [hcoe, hw]
      group
    change Additive.ofMul
      (δ ⟨nN, hNR nN.2⟩ ((conjHom Q R hRQ (⟨nN, hNR nN.2⟩⁻¹)) w)) =
      Additive.ofMul (δ r v)
    rw [harg, hR]
  have hval : Additive.ofMul (δ r v) = Additive.ofMul (φ v) - Additive.ofMul (φ w) := by
    have hDnval := congrArg (fun L : W →ₗ[ZMod 2] Additive ↥Z' => L (s.cl w)) (hDn nN)
    rw [LinearMap.sub_apply] at hDnval
    rw [hDv] at hDnval
    have h1 : ((ρ.linHom (Representation.trivial (ZMod 2) ↥N (Additive ↥Z'))) nN φbar)
        (s.cl w) = φbar (s.cl v) := by
      rw [hlin nN φbar, LinearMap.comp_apply, hsymm]
    rw [h1] at hDnval
    change Additive.ofMul (δ r v) = Additive.ofMul (φ v) - Additive.ofMul (φ w) at hDnval
    exact hDnval
  have hsq : ∀ z : ↥Z', z * z = 1 := by
    intro z
    apply Subtype.ext
    have h := hZ'2 (z : G') z.2
    rwa [pow_two] at h
  have hinv : ∀ z : ↥Z', z⁻¹ = z := fun z => inv_eq_of_mul_eq_one_right (hsq z)
  have hconv : (Additive.ofMul (φ v) - Additive.ofMul (φ w)).toMul = φ w * (φ v)⁻¹ := by
    rw [toMul_sub, toMul_ofMul, toMul_ofMul, div_eq_mul_inv, hinv, hinv]
    exact mul_comm _ _
  have hδeq : δ r v = φ w * (φ v)⁻¹ := by
    have h := congrArg (fun x : Additive ↥Z' => Additive.toMul x) hval
    simpa [hconv] using h
  have hcentral := hNZ' r hr (φ v : G') (φ v).2
  calc ((δ r v : ↥Z') : G') = (φ w * (φ v)⁻¹ : ↥Z').1 := by rw [hδeq]
    _ = (φ w : G') * (φ v : G')⁻¹ := rfl
    _ = (φ w : G') * ((e r : G') * (φ v : G') * (e r : G')⁻¹)⁻¹ := by rw [hcentral]

theorem eq_one_of_secRep_of_fixed {Q Z R N : Subgroup G} {Z' R' : Subgroup G'}
    (e : ↥R ≃* ↥R') (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (hNR : N ≤ R)
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a) (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (hNZ' : ∀ n : ↥R, (n : G) ∈ N → ∀ z ∈ Z', (e n : G') * z * (e n : G')⁻¹ = z)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (s : SecRep N Z Q W)
    (ρ : Representation (ZMod 2) ↥N W) (hρ : ∀ n w, ρ n w = s.ρ n w) [Fact ρ.IsIrreducible]
    (hnt : ∃ n, ρ n ≠ 1) (φ : ↥Q →* ↥Z') (hφZ : ∀ v : ↥Q, (v : G) ∈ Z → φ v = 1)
    (hφN : ∀ n : ↥R, (n : G) ∈ N → ∀ (v w : ↥Q), (w : G) = (n : G) * v * (n : G)⁻¹ →
      (φ w : G') = (e n : G') * (φ v : G') * (e n : G')⁻¹) :
    φ = 1 := by
  classical
  haveI hZ'comm : IsMulCommutative ↥Z' :=
    ⟨⟨fun a b => Subtype.ext (hZ'c (a : G') a.2 (b : G') b.2)⟩⟩
  letI : CommGroup ↥Z' := IsMulCommutative.instCommGroup
  haveI : Finite ↥Z' := Subtype.finite
  letI : Module (ZMod 2) (Additive ↥Z') :=
    AddCommGroup.zmodModule (zmod_two_smul_eq_zero hZ'2)
  haveI : Finite (Additive ↥Z') := inferInstanceAs (Finite ↥Z')
  let φbar : W →ₗ[ZMod 2] Additive ↥Z' := secFactorLin s φ hφZ
  have hφbar : ∀ (n : ↥N) (x : W), φbar (ρ n x) = φbar x := by
    intro n x
    obtain ⟨v, rfl⟩ := s.exists_cl x
    let nR : ↥R := ⟨n, hNR n.2⟩
    let w : ↥Q := conjHom Q R hRQ nR v
    have hw : (w : G) = (n : G) * (v : G) * (n : G)⁻¹ :=
      conjHom_apply hRQ nR v
    have hact : s.ρ n (s.cl v) = s.cl w := s.act n v w hw
    have hφw : φ w = φ v := by
      apply Subtype.ext
      have h1 := hφN nR n.2 v w hw
      have h2 := hNZ' nR n.2 (φ v : G') (φ v).2
      rw [h2] at h1
      exact h1
    rw [hρ n, hact, secFactorLin_cl s φ hφZ w, secFactorLin_cl s φ hφZ v, hφw]
  have hzero : φbar = 0 := eq_zero_of_invariant_linearMap ρ hnt φbar hφbar
  have hφval : ∀ u : ↥Q, φ u = Additive.toMul (φbar (s.cl u)) := by
    intro u
    have h := congrArg Additive.toMul (secFactorLin_cl s φ hφZ u)
    simpa using h.symm
  refine MonoidHom.ext fun u => ?_
  rw [hφval u, hzero, LinearMap.zero_apply, toMul_zero]
  rfl

theorem crossedHomPrincipal_of_secRep {Q Z R N : Subgroup G} {Z' R' : Subgroup G'}
    (e : ↥R ≃* ↥R') (hRQ : R ≤ Subgroup.normalizer (Q : Set G))
    (hRZ : ∀ r ∈ R, ∀ z ∈ Z, r * z * r⁻¹ ∈ Z) (hR'Z' : ∀ r ∈ R', ∀ z ∈ Z', r * z * r⁻¹ ∈ Z')
    (hZ'c : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a) (hZ'2 : ∀ z ∈ Z', z ^ 2 = 1)
    (hNR : N ≤ R) (hNnorm : ∀ r ∈ R, ∀ n ∈ N, r * n * r⁻¹ ∈ N)
    (hNZ' : ∀ n : ↥R, (n : G) ∈ N → ∀ z ∈ Z', (e n : G') * z * (e n : G')⁻¹ = z)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (s : SecRep N Z Q W)
    (ρ : Representation (ZMod 2) ↥N W) (hρ : ∀ n w, ρ n w = s.ρ n w) [Fact ρ.IsIrreducible]
    (hnt : ∃ n, ρ n ≠ 1)
    (B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (hB : ∀ n x y, B (ρ n x) (ρ n y) = B x y)
    (hBnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hH1 : ∀ φ : ↥N → W, φ ∈ Z1 ρ → φ ∈ B1 ρ) :
    CrossedHomPrincipal Q Z R Z' R' e :=
  crossedHomPrincipal_of_normal e hRQ hRZ hR'Z' hZ'c hNR hNnorm
    (crossedHomPrincipalOn_of_secRep e hRQ hNR hZ'c hZ'2 hNZ' s ρ hρ B hB hBnd hH1)
    (fun φ hφZ hφN =>
      eq_one_of_secRep_of_fixed e hRQ hNR hZ'c hZ'2 hNZ' s ρ hρ hnt φ hφZ hφN)

end CFSG.Quasithin.F112R.St84

end
