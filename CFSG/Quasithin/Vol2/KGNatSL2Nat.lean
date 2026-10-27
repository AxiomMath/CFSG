module

public import CFSG.Quasithin.Vol2.KGNatSL3Real
public import CFSG.Quasithin.Vol2.KGNatSL2

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.CGT.Timmesfeld75
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open scoped MatrixGroups

section Ext

variable {W : Type*} [CommGroup W] {M : Type} [AddCommGroup M] {K : Type} [Field K] [Module K M]

theorem exists_scalar_ext (hW : ∀ w : W, w ^ 2 = 1) {U : Subgroup W} {f : W → M}
    (hmul : ∀ u ∈ U, ∀ u' ∈ U, f (u * u') = f u + f u') (hker : ∀ u ∈ U, f u = 0 → u = 1)
    (hsurj : ∀ m : M, ∃ u ∈ U, f u = m) (c : K) :
    ∃ μ : W →* W, (∀ u ∈ U, μ u ∈ U) ∧ ∀ u ∈ U, f (μ u) = c • f u := by
  classical
  have : IsElementaryAbelian 2 W := ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hW⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 W U
  let φ : ↥U × ↥C →* W := MonoidHom.coprod U.subtype C.subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, c'⟩ h
    change (u : W) * (c' : W) = 1 at h
    have h1 : (u : W) = (c' : W)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hu : (u : W) ∈ U ⊓ C := ⟨u.2, h1 ▸ C.inv_mem c'.2⟩
    rw [disjoint_iff.mp hC.disjoint, Subgroup.mem_bot] at hu
    have hc : (c' : W) = 1 := by
      rw [hu, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hc)
  have hφsurj : Function.Surjective φ := by
    intro w
    have hw : w ∈ U ⊔ C := by rw [codisjoint_iff.mp hC.codisjoint]; exact Subgroup.mem_top w
    obtain ⟨u, hu, c', hc', rfl⟩ := Subgroup.mem_sup.mp hw
    exact ⟨(⟨u, hu⟩, ⟨c', hc'⟩), rfl⟩
  let e := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have he : ∀ u : ↥U, e.symm (u : W) = (u, 1) := fun u => by
    rw [MulEquiv.symm_apply_eq]
    show (u : W) = (u : W) * 1
    rw [mul_one]
  let fU : ↥U →* Multiplicative M :=
    { toFun := fun u => Multiplicative.ofAdd (f u)
      map_one' := by
        have h := hmul 1 U.one_mem 1 U.one_mem
        rw [mul_one] at h
        exact congrArg Multiplicative.ofAdd (add_eq_left.mp h.symm)
      map_mul' := fun u u' => congrArg Multiplicative.ofAdd (hmul u u.2 u' u'.2) }
  have hfUinj : Function.Injective fU := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (hker u u.2 (congrArg Multiplicative.toAdd hu))
  have hfUsurj : Function.Surjective fU := fun m => by
    obtain ⟨u, hu, hfu⟩ := hsurj (Multiplicative.toAdd m)
    exact ⟨⟨u, hu⟩, congrArg Multiplicative.ofAdd hfu⟩
  let eU := MulEquiv.ofBijective fU ⟨hfUinj, hfUsurj⟩
  let sc : Multiplicative M →* Multiplicative M :=
    { toFun := fun x => Multiplicative.ofAdd (c • Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' := fun x y => by simp [smul_add] }
  refine ⟨U.subtype.comp (eU.symm.toMonoidHom.comp (sc.comp (fU.comp
    ((MonoidHom.fst ↥U ↥C).comp e.symm.toMonoidHom)))), fun u _ => Subtype.prop _,
    fun u hu => ?_⟩
  have h1 : (MonoidHom.fst ↥U ↥C) (e.symm u) = ⟨u, hu⟩ := by
    have h0 : e.symm u = (⟨u, hu⟩, 1) := he ⟨u, hu⟩
    rw [h0]
    rfl
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  have h2 := congrArg Multiplicative.toAdd (eU.apply_symm_apply (sc (fU ⟨u, hu⟩)))
  exact h2

end Ext

section SecCoord

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (GL ι K)} {W : Type*} [CommGroup W]

structure IsSecCoord (H : Subgroup (MulAut W)) (U : Subgroup W) (π : ↥Γ →* ↥H)
    (f : W → (ι → K)) : Prop where
  map_mul : ∀ u ∈ U, ∀ u' ∈ U, f (u * u') = f u + f u'
  ker : ∀ u ∈ U, f u = 0 → u = 1
  surj : ∀ x, ∃ u ∈ U, f u = x
  act : ∀ γ : ↥Γ, ∀ u ∈ U,
    f (((π γ : ↥H) : MulAut W) u) = ((γ : GL ι K) : Matrix ι ι K) *ᵥ f u
  stab : ∀ h ∈ H, ∀ u ∈ U, h u ∈ U
  onto : Function.Surjective π

variable {H : Subgroup (MulAut W)} {U : Subgroup W} {π : ↥Γ →* ↥H} {f : W → (ι → K)}

theorem exists_isSecCoord (h : (FFModel.nat Γ).RealizesVia H U ⊥ π) :
    ∃ f : W → (ι → K), IsSecCoord H U π f := by
  obtain ⟨f, hmul, hker, hsurj, hact⟩ := exists_coord (linModelNat Γ) h
  exact ⟨f, ⟨hmul, fun u hu h0 => Subgroup.mem_bot.mp ((hker u hu).mp h0), hsurj,
    fun γ u hu => (hact γ u hu).trans (linModelNat_lin Γ γ (f u)),
    fun h' hh u hu => h.2.2.2.1 ⟨h', hh⟩ u hu, h.1⟩⟩

namespace IsSecCoord

variable (hf : IsSecCoord H U π f)
include hf

theorem map_one : f 1 = 0 := by
  have h := hf.map_mul 1 U.one_mem 1 U.one_mem
  rw [mul_one] at h
  exact add_eq_left.mp h.symm

theorem map_inv {u : W} (hu : u ∈ U) : f u⁻¹ = - f u := by
  have h := hf.map_mul u hu u⁻¹ (U.inv_mem hu)
  rw [mul_inv_cancel, hf.map_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem map_mul_inv {u v : W} (hu : u ∈ U) (hv : v ∈ U) : f (u * v⁻¹) = f u - f v := by
  rw [hf.map_mul u hu v⁻¹ (U.inv_mem hv), hf.map_inv hv, sub_eq_add_neg]

theorem inj {u v : W} (hu : u ∈ U) (hv : v ∈ U) (h : f u = f v) : u = v :=
  mul_inv_eq_one.mp (hf.ker _ (U.mul_mem hu (U.inv_mem hv))
    (by rw [hf.map_mul_inv hu hv, h, sub_self]))

theorem injective : Function.Injective π := by
  intro γ γ' h
  have hlin : ∀ x, ((γ : GL ι K) : Matrix ι ι K) *ᵥ x = ((γ' : GL ι K) : Matrix ι ι K) *ᵥ x := by
    intro x
    obtain ⟨u, hu, rfl⟩ := hf.surj x
    rw [← hf.act γ u hu, ← hf.act γ' u hu, h]
  apply Subtype.ext
  apply Units.ext
  exact Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact hlin x)

end IsSecCoord

end SecCoord

section SL2

variable {F : Type} [Field F]

theorem conjSL_mulVec {n : Type} [Fintype n] [DecidableEq n] (g B : SpecialLinearGroup n F)
    (x : n → F) :
    ((g * B * g⁻¹ : SpecialLinearGroup n F) : Matrix n n F) *ᵥ x =
      (g : Matrix n n F) *ᵥ ((B : Matrix n n F) *ᵥ
        (((g⁻¹ : SpecialLinearGroup n F) : Matrix n n F) *ᵥ x)) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem sl_mul_inv_mulVec {n : Type} [Fintype n] [DecidableEq n] (g : SpecialLinearGroup n F)
    (x : n → F) :
    (g : Matrix n n F) *ᵥ (((g⁻¹ : SpecialLinearGroup n F) : Matrix n n F) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem sl_inv_mul_mulVec {n : Type} [Fintype n] [DecidableEq n] (g : SpecialLinearGroup n F)
    (x : n → F) :
    ((g⁻¹ : SpecialLinearGroup n F) : Matrix n n F) *ᵥ ((g : Matrix n n F) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVec_two_apply (A : Matrix (Fin 2) (Fin 2) F) (x : Fin 2 → F) (i : Fin 2) :
    (A *ᵥ x) i = A i 0 * x 0 + A i 1 * x 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_e0 (A : Matrix (Fin 2) (Fin 2) F) : A *ᵥ ![1, 0] = ![A 0 0, A 1 0] := by
  ext i
  fin_cases i <;> simp [mulVec_two_apply]

theorem sl2_e0_ne_zero (g : SL(2, F)) : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] ≠ 0 := by
  intro h0
  have h := congrArg (fun x => ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) h0
  simp only [sl_inv_mul_mulVec, Matrix.mulVec_zero] at h
  exact one_ne_zero (congrFun h 0)

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {U : Subgroup W}
  {π : ↥(StatedSL 2 F) →* ↥H} {f : W → (Fin 2 → F)}

@[expose] noncomputable def rho2 (π : ↥(StatedSL 2 F) →* ↥H) : SL(2, F) →* ↥H :=
  π.comp (specialLinearGroupEquivStatedSL 2 F).toMonoidHom

theorem rho2_bijective (hf : IsSecCoord H U π f) : Function.Bijective (rho2 π) :=
  ⟨hf.injective.comp (specialLinearGroupEquivStatedSL 2 F).injective,
    hf.onto.comp (specialLinearGroupEquivStatedSL 2 F).surjective⟩

theorem IsSecCoord.act2 (hf : IsSecCoord H U π f) (A : SL(2, F)) {u : W} (hu : u ∈ U) :
    f (((rho2 π A : ↥H) : MulAut W) u) = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ f u :=
  hf.act _ u hu

variable [Finite F] [CharP F 2]

theorem exists_sylow_eq_conj_utri (hf : IsSecCoord H U π f) {S : Subgroup (MulAut W)}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S H) :
    ∃ g : SL(2, F), ∀ x : MulAut W,
      x ∈ S ↔ ∃ v ∈ utri F, x = ((rho2 π (g * v * g⁻¹) : ↥H) : MulAut W) := by
  obtain ⟨hSH, hS2, hSi⟩ := hS
  obtain ⟨hinj, hsurj⟩ := rho2_bijective hf
  have hQ2 := isPGroup_comap (rho2 π) hinj hS2
  have hQi : ¬ 2 ∣ ((S.subgroupOf H).comap (rho2 π)).index := by
    rw [index_comap (rho2 π) hsurj]
    exact hSi
  obtain ⟨g, hg⟩ := exists_conj_utri_eq_of_index hQ2 hQi
  refine ⟨g, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨A, hA⟩ := hsurj ⟨x, hSH hx⟩
    have hAQ : A ∈ (S.subgroupOf H).comap (rho2 π) := by
      rw [Subgroup.mem_comap, hA, Subgroup.mem_subgroupOf]
      exact hx
    rw [← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup] at hAQ
    refine ⟨g⁻¹ * A * g, hAQ, ?_⟩
    rw [show g * (g⁻¹ * A * g) * g⁻¹ = A by group, hA]
  · rintro ⟨v, hv, rfl⟩
    have hmem : g * v * g⁻¹ ∈ (S.subgroupOf H).comap (rho2 π) := by
      rw [← hg, CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
      rwa [show g⁻¹ * (g * v * g⁻¹) * g = v by group]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at hmem
    exact hmem

omit [Finite F] [CharP F 2] in
theorem fixed2_iff (hf : IsSecCoord H U π f) {S : Subgroup (MulAut W)} {g : SL(2, F)}
    (hg : ∀ x : MulAut W, x ∈ S ↔ ∃ v ∈ utri F, x = ((rho2 π (g * v * g⁻¹) : ↥H) : MulAut W))
    {u : W} (hu : u ∈ U) :
    (∀ s ∈ S, s u = u) ↔ ∃ t : F, f u = t • ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) := by
  constructor
  · intro hfix
    have h1 := congrArg f (hfix _ ((hg _).mpr ⟨utriElt 1, utriElt_mem_utri 1, rfl⟩))
    rw [hf.act2 _ hu, conjSL_mulVec] at h1
    set z := ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ f u with hz
    have h2 : ((utriElt 1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ z = z := by
      have h3 := congrArg (fun x => ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) h1
      simp only [sl_inv_mul_mulVec] at h3
      exact h3
    have hz1 : z 1 = 0 := by
      have h3 := congrFun h2 0
      rw [mulVec_two_apply] at h3
      have h00 : ((utriElt 1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := utriElt_apply_00 1
      have h01 : ((utriElt 1 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = 1 := utriElt_apply_01 1
      rw [h00, h01] at h3
      linear_combination h3
    refine ⟨z 0, ?_⟩
    have hz' : z = z 0 • ![1, 0] := by
      ext i
      fin_cases i <;> simp [hz1]
    rw [← Matrix.mulVec_smul, ← hz', hz, sl_mul_inv_mulVec]
  · rintro ⟨t, ht⟩ s hs
    obtain ⟨v, hv, rfl⟩ := (hg s).mp hs
    refine hf.inj (hf.stab _ (rho2 π _).2 u hu) hu ?_
    rw [hf.act2 _ hu, ht, Matrix.mulVec_smul, conjSL_mulVec, sl_inv_mul_mulVec, mulVec_e0]
    have h10 : (v : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hv.1
    have h00 : (v : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := hv.2
    rw [h10, h00]

end SL2

end CFSG.Quasithin.Vol2.KGNat
