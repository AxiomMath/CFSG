module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BKG
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.Assembly.GL83LieDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.HatA7

open Polynomial CFSG.Quasithin

noncomputable abbrev polyF4 : (ZMod 2)[X] := X ^ 2 + X + 1

theorem natDegree_polyF4 : polyF4.natDegree = 2 := by
  unfold polyF4
  compute_degree!

theorem irreducible_polyF4 : Irreducible polyF4 :=
  Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (by rw [natDegree_polyF4]; decide) (fun x => by
      rw [Polynomial.IsRoot.def]
      simp only [polyF4, eval_add, eval_pow, eval_X, eval_one]
      fin_cases x <;> decide)

instance : Fact (Irreducible polyF4) := ⟨irreducible_polyF4⟩

abbrev FF4 : Type := AdjoinRoot polyF4

instance : Module.Finite (ZMod 2) FF4 :=
  (AdjoinRoot.powerBasis irreducible_polyF4.ne_zero).finite

instance : Finite FF4 := Module.finite_of_finite (ZMod 2)

theorem card_FF4 : Nat.card FF4 = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := FF4),
    (AdjoinRoot.powerBasis irreducible_polyF4.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    natDegree_polyF4, Nat.card_zmod]
  norm_num

abbrev modTwo {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) :
    Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    change Additive.ofMul (Additive.toMul x * Additive.toMul x) = 0
    rw [← sq, hV]
    rfl

theorem not_injective_of_isHat {X : Type} [Group X] [Finite X]
    (hX : IsHat X (alternatingGroup (Fin 7))) {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ v : V, v ^ 2 = 1) (hV : Nat.card V ≤ 2 ^ 11) (φ : X →* MulAut V) :
    ¬ Function.Injective φ := by
  intro hφ
  obtain ⟨hqs, hZ3, ⟨eZ⟩⟩ := hX
  let _ := modTwo hV2
  let L : X → Additive V →ₗ[ZMod 2] Additive V := fun g =>
    ((MulEquiv.toAdditive (φ g) : Additive V ≃+ Additive V).toLinearEquiv
      (fun c x => ZMod.map_smul _ c x)).toLinearMap
  have hLmul : ∀ g h : X, L (g * h) = L g ∘ₗ L h := fun g h => by
    ext x
    simp [L, map_mul]
  have hLone : L 1 = LinearMap.id := by
    ext x
    simp [L]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 3 (by rw [hZ3])
  set z : X := (z₀ : X) with hz
  have hzc : ∀ g : X, z * g = g * z := fun g => (Subgroup.mem_center_iff.mp z₀.2 g).symm
  have hz3 : orderOf z = 3 := by rw [hz, Subgroup.orderOf_coe, hz₀]
  set t := L z with ht
  have ht3 : t ∘ₗ t ∘ₗ t = LinearMap.id := by
    rw [ht, ← hLmul, ← hLmul, ← hLone]
    congr 1
    rw [← pow_three, ← hz3, pow_orderOf_eq_one]
  have ht1 : t ≠ LinearMap.id := by
    intro h1
    have h2 : φ z = 1 := by
      ext v
      have := congrArg (fun f : Additive V →ₗ[ZMod 2] Additive V => f (Additive.ofMul v)) h1
      exact this
    have h3 : z = 1 := hφ (h2.trans (map_one φ).symm)
    rw [h3, orderOf_one] at hz3
    norm_num at hz3
  have hLt : ∀ g : X, L g ∘ₗ t = t ∘ₗ L g := fun g => by rw [ht, ← hLmul, ← hLmul, hzc g]
  have h2A : ∀ x : Additive V, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  set p : Additive V →ₗ[ZMod 2] Additive V := t ∘ₗ t + t + LinearMap.id with hp
  set W := LinearMap.ker p with hW
  have hLW : ∀ g : X, ∀ w ∈ W, L g w ∈ W := by
    intro g w hw
    have e : ∀ u, t (L g u) = L g (t u) := fun u => (congrArg (fun f => f u) (hLt g)).symm
    have h1 : p (L g w) = L g (p w) := by
      simp only [hp, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add, e]
    rw [LinearMap.mem_ker] at hw ⊢
    rw [h1, hw, map_zero]
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply ht1
    ext v
    have hmem : t v + v ∈ W := by
      rw [LinearMap.mem_ker]
      have h3 : t (t (t v)) = v := congrArg (fun f => f v) ht3
      have e : p (t v + v) = (v + v) + (t (t v) + t (t v)) + (t v + t v) := by
        simp only [hp, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, map_add, h3]
        abel
      rw [e]
      simp only [h2A]
    rw [hbot, Submodule.mem_bot] at hmem
    show t v = v
    calc t v = t v + (v + v) := by rw [h2A, add_zero]
      _ = (t v + v) + v := by abel
      _ = v := by rw [hmem, zero_add]
  have htW : ∀ w ∈ W, t w ∈ W := hLW z
  set tW : Module.End (ZMod 2) ↥W := t.restrict htW with htWdef
  have htW2 : tW * tW + tW + 1 = 0 := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hw : p w = 0 := w.2
    rw [hp] at hw
    simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      LinearMap.zero_apply, Submodule.coe_add, Submodule.coe_zero, htWdef,
      LinearMap.coe_restrict_apply, LinearMap.comp_apply, LinearMap.id_apply] using hw
  have hpoly : Polynomial.aeval tW polyF4 = 0 := by
    rw [show polyF4 = Polynomial.X * Polynomial.X + Polynomial.X + 1 by rw [polyF4, sq],
      map_add, map_add, map_mul,
      Polynomial.aeval_X, map_one]
    exact htW2
  set ι : FF4 →+* Module.End (ZMod 2) ↥W :=
    Ideal.Quotient.lift (Ideal.span {polyF4}) (Polynomial.aeval tW).toRingHom (fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hpoly]) with hι
  let _ : Module FF4 ↥W := Module.compHom ↥W ι
  have hsmul : ∀ (c : FF4) (w : ↥W), c • w = ι c w := fun c w => rfl
  let LW : X → Module.End (ZMod 2) ↥W := fun g => (L g).restrict (hLW g)
  have hLWt : ∀ g, Commute (LW g) tW := fun g => by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact congrArg (fun f => f (w : Additive V)) (hLt g)
  have hLWι : ∀ g (c : FF4), Commute (ι c) (LW g) := by
    intro g c
    induction c using AdjoinRoot.induction_on with
    | ih f =>
      have e : ι (AdjoinRoot.mk polyF4 f) = Polynomial.aeval tW f := Ideal.Quotient.lift_mk _ _ _
      rw [e]
      exact (Algebra.commute_of_mem_adjoin_singleton_of_commute
        (Polynomial.aeval_mem_adjoin_singleton (ZMod 2) tW) (hLWt g)).symm
  let ρW : X → (↥W →ₗ[FF4] ↥W) := fun g =>
    { toFun := LW g
      map_add' := (LW g).map_add
      map_smul' := fun c w => by
        rw [hsmul, hsmul, RingHom.id_apply]
        exact (congrArg (fun f => f w) (hLWι g c)).symm }
  have hρmul : ∀ g h : X, ρW (g * h) = ρW g ∘ₗ ρW h := fun g h => by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact congrArg (fun f => f (w : Additive V)) (hLmul g h)
  have hρone : ρW 1 = LinearMap.id := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact congrArg (fun f => f (w : Additive V)) hLone
  set ρU : X →* (Module.End FF4 ↥W)ˣ :=
    { toFun := fun g => ⟨ρW g, ρW g⁻¹,
          by rw [Module.End.mul_eq_comp, ← hρmul, mul_inv_cancel, hρone]; rfl,
          by rw [Module.End.mul_eq_comp, ← hρmul, inv_mul_cancel, hρone]; rfl⟩
      map_one' := Units.ext hρone
      map_mul' := fun g h => Units.ext (hρmul g h) } with hρU
  have hρz : ρU z ≠ 1 := by
    intro h1
    have h2 : tW = 1 := by
      have := congrArg (fun u : (Module.End FF4 ↥W)ˣ => (u : Module.End FF4 ↥W)) h1
      refine LinearMap.ext fun w => ?_
      exact congrArg (fun f : Module.End FF4 ↥W => f w) this
    apply hWne
    rw [eq_bot_iff]
    intro w hw
    have h3 := congrArg (fun f : Module.End (ZMod 2) ↥W => f ⟨w, hw⟩) htW2
    simp only [h2, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      LinearMap.zero_apply] at h3
    have h4 : (⟨w, hw⟩ : ↥W) = 0 := by
      have h5 : (⟨w, hw⟩ : ↥W) + ⟨w, hw⟩ = 0 := Subtype.ext (h2A w)
      rw [h5, zero_add] at h3
      exact h3
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val h4
  have hzZ : Subgroup.zpowers z = Subgroup.center X := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact z₀.2
    · rw [hZ3, Nat.card_zpowers, hz3]
  have hρinj : Function.Injective ρU := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs (MonoidHom.normal_ker ρU) with h | h
    · exact absurd (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top z)) hρz
    · rw [eq_bot_iff]
      intro g hg
      have hgZ : g ∈ Subgroup.zpowers z := hzZ ▸ h hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgZ
      have hk : ρU z ^ k = 1 := by rw [← map_zpow]; exact MonoidHom.mem_ker.mp hg
      have h3 : orderOf (ρU z) ∣ 3 := by
        rw [← hz3]
        exact orderOf_map_dvd ρU z
      have h1 : orderOf (ρU z) ≠ 1 := fun h1 => hρz (orderOf_eq_one_iff.mp h1)
      have h33 : orderOf (ρU z) = 3 :=
        ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left h1
      have hk3 : ((orderOf (ρU z) : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hk
      rw [h33] at hk3
      have hk3' : ((orderOf z : ℕ) : ℤ) ∣ k := by rw [hz3]; exact hk3
      exact Subgroup.mem_bot.mpr (orderOf_dvd_iff_zpow_eq_one.mp hk3')
  set r : FF4 := AdjoinRoot.root polyF4 with hr
  have hιr : ι r = tW := by
    rw [hr, show AdjoinRoot.root polyF4 = AdjoinRoot.mk polyF4 Polynomial.X from rfl]
    exact (Ideal.Quotient.lift_mk _ _ _).trans (Polynomial.aeval_X tW)
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hιr
    apply hWne
    rw [eq_bot_iff]
    intro w hw
    have h3 := congrArg (fun f : Module.End (ZMod 2) ↥W => f ⟨w, hw⟩) htW2
    simp only [← hιr, mul_zero, zero_add, Module.End.one_apply, LinearMap.zero_apply] at h3
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val h3
  set u : FF4ˣ := Units.mk0 r hr0 with hu
  have hr2 : r ^ 2 + r + 1 = 0 := by
    have h := AdjoinRoot.mk_self (f := polyF4)
    simpa [polyF4, map_add, map_pow, AdjoinRoot.mk_X] using h
  have h11 : (1 : FF4) + 1 = 0 := by
    have h : algebraMap (ZMod 2) FF4 (1 + 1) = 0 := by
      rw [show (1 + 1 : ZMod 2) = 0 from rfl, map_zero]
    simpa using h
  have hu3 : orderOf u = 3 := by
    refine orderOf_eq_prime (Units.ext ?_) (fun h1 => ?_)
    · rw [Units.val_pow_eq_pow_val, hu, Units.val_mk0, Units.val_one]
      linear_combination (r - 1) * hr2
    · have h1' : r = 1 := congrArg Units.val h1
      rw [h1', one_pow, h11, zero_add] at hr2
      exact one_ne_zero hr2
  have hscal : ∀ {m : ℕ} (b' : Module.Basis (Fin m) FF4 ↥W),
      (Matrix.GeneralLinearGroup.toLin' b').symm (ρU z) =
        Matrix.GeneralLinearGroup.scalar (Fin m) u := by
    intro m b'
    rw [MulEquiv.symm_apply_eq]
    refine Units.ext (LinearMap.ext fun w => ?_)
    change ρW z w = _
    have h1 : ρW z w = r • w := by
      rw [hsmul, hιr]
      rfl
    rw [h1]
    change r • w = (Matrix.GeneralLinearGroup.toLin' b'
      (Matrix.GeneralLinearGroup.scalar (Fin m) u)).toLinearEquiv w
    rw [Matrix.GeneralLinearGroup.toLin'_apply]
    simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, Matrix.scalar_apply, hu, Units.val_mk0]
    rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, map_smul,
      Fintype.linearCombination_apply, b'.sum_repr]
  have hdetG : ∀ {m : ℕ} (b' : Module.Basis (Fin m) FF4 ↥W) (x : X),
      (((Matrix.GeneralLinearGroup.toLin' b').symm (ρU x) : GL (Fin m) FF4) :
        Matrix (Fin m) (Fin m) FF4).det = 1 := by
    intro m b' x
    have h1 : x ∈ (Matrix.GeneralLinearGroup.det.comp
        ((Matrix.GeneralLinearGroup.toLin' b').symm.toMonoidHom.comp ρU)).ker :=
      Abelianization.commutator_subset_ker _ (by rw [hqs.1.commutator_eq_top]; trivial)
    have h2 := congrArg Units.val (MonoidHom.mem_ker.mp h1)
    simpa using h2
  have : Finite ↥W := inferInstance
  have : Module.Finite FF4 ↥W := Module.Finite.of_finite
  have : Fintype FF4 := Fintype.ofFinite FF4
  set k := Module.finrank FF4 ↥W with hk
  have hcardW : Nat.card ↥W = 4 ^ k := by
    rw [Module.natCard_eq_pow_finrank (K := FF4) (V := ↥W), card_FF4]
  have hk5 : k ≤ 5 := by
    have h1 : Nat.card ↥W ≤ Nat.card V := by
      rw [show Nat.card V = Nat.card (Additive V) from rfl]
      exact Nat.card_le_card_of_injective _ Subtype.val_injective
    rw [hcardW] at h1
    by_contra hk6
    have : 4 ^ 6 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk0 : k ≠ 0 := by
    intro h0
    apply hWne
    have h1 : Nat.card ↥W = 1 := by rw [hcardW, h0, pow_zero]
    have : Subsingleton ↥W := (Nat.card_eq_one_iff_unique.mp h1).1
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val (Subsingleton.elim (⟨w, hw⟩ : ↥W) 0)
  let b := Module.finBasisOfFinrankEq FF4 ↥W hk.symm
  have h3k : 3 ∣ k := by
    have h1 := hdetG b z
    rw [hscal b] at h1
    have h2 : ((Matrix.GeneralLinearGroup.scalar (Fin k) u : GL (Fin k) FF4) :
        Matrix (Fin k) (Fin k) FF4).det = (u : FF4) ^ k := by
      simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    have h3 : u ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ← h2, h1, Units.val_one])
    rw [← hu3]
    exact orderOf_dvd_of_pow_eq_one h3
  have hkeq : k = 3 := by omega
  let b3 := Module.finBasisOfFinrankEq FF4 ↥W (hk.symm.trans hkeq)
  set ρ3 : X →* GL (Fin 3) FF4 :=
    (Matrix.GeneralLinearGroup.toLin' b3).symm.toMonoidHom.comp ρU with hρ3
  have hρ3inj : Function.Injective ρ3 :=
    (Matrix.GeneralLinearGroup.toLin' b3).symm.injective.comp hρinj
  have hρ3z : ρ3 z = Matrix.GeneralLinearGroup.scalar (Fin 3) u := hscal b3
  have hdet : ∀ x : X, (ρ3 x : Matrix (Fin 3) (Fin 3) FF4).det = 1 := fun x => hdetG b3 x
  have hSL : ∀ x : X, ρ3 x ∈ CFSG.Assembly.LowTwoRank.StatedSL 3 FF4 := fun x =>
    Subgroup.subset_closure (hdet x)
  set N := (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) FF4).subgroupOf
    (CFSG.Assembly.LowTwoRank.StatedSL 3 FF4) with hN
  set σ : X →* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 FF4) :=
    (QuotientGroup.mk' N).comp (ρ3.codRestrict _ hSL) with hσ
  have hσker : σ.ker = Subgroup.center X := by
    ext x
    rw [MonoidHom.mem_ker, hσ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf, MonoidHom.codRestrict_apply]
    constructor
    · rintro ⟨v, hv⟩
      have hv' : Matrix.GeneralLinearGroup.scalar (Fin 3) v = ρ3 x := hv
      rw [Subgroup.mem_center_iff]
      intro y
      apply hρ3inj
      rw [map_mul, map_mul, ← hv']
      exact Units.ext (Matrix.scalar_commute (v : FF4) (fun r' => Commute.all _ _)
        (ρ3 y : Matrix (Fin 3) (Fin 3) FF4)).eq.symm
    · intro hx
      rw [← hzZ] at hx
      obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      show ρ3 (z ^ k') ∈ _
      rw [map_zpow, hρ3z]
      exact ⟨u ^ k', by rw [map_zpow]⟩
  set ψ : alternatingGroup (Fin 7) →*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 FF4) :=
    (QuotientGroup.kerLift σ).comp
      ((QuotientGroup.quotientMulEquivOfEq hσker.symm).toMonoidHom.comp eZ.symm.toMonoidHom)
    with hψ
  have hψinj : Function.Injective ψ :=
    (QuotientGroup.kerLift_injective σ).comp
      ((QuotientGroup.quotientMulEquivOfEq hσker.symm).injective.comp eZ.symm.injective)
  have hL : IsPSL 3 2 2
      (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 3 FF4)) :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, FF4, inferInstance,
      inferInstance, by rw [card_FF4]; norm_num, ⟨MulEquiv.refl _⟩⟩
  have hcent :=
    (CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated.{0} _ hL).2.1
  set a : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ with ha
  set c : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 4 5 * Equiv.swap 5 6, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ with hc
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (Subtype.ext (by rw [ha]; decide)) (fun h => by
      have := congrArg Subtype.val h; revert this; decide)
  have hc3 : orderOf c = 3 :=
    orderOf_eq_prime (Subtype.ext (by rw [hc]; decide)) (fun h => by
      have := congrArg Subtype.val h; revert this; decide)
  have hac : a * c = c * a := Subtype.ext (by rw [ha, hc]; decide)
  have h64 := hcent (ψ a) (by rw [orderOf_injective ψ hψinj, ha2])
  have hmem : ψ c ∈ Subgroup.centralizer ({ψ a} : Set _) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hac]
  have hdvd : orderOf (⟨ψ c, hmem⟩ : Subgroup.centralizer ({ψ a} : Set _)) ∣ 64 := by
    rw [← h64]
    exact orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, orderOf_injective ψ hψinj, hc3] at hdvd
  norm_num at hdvd

theorem hatA7Faithful6_holds : HatA7Faithful6 :=
  fun _ _ _ hX _ _ _ hV2 hV φ => not_injective_of_isHat hX hV2 (hV.trans (by norm_num)) φ

end CFSG.Quasithin.H13.HatA7
