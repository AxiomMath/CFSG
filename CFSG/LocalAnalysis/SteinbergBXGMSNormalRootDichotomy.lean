module

public import CFSG.LocalAnalysis.SteinbergBXGMSNormalRootPartition
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.LocalAnalysis.SteinbergBX

open Subgroup CFSG CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV
open scoped Pointwise LinearAlgebra.Projectivization

section Defs

variable {D : Type*} [Group D]

@[expose] def gmsSingerPermImage (X U R : Subgroup D) :
    Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) :=
  ((X ⊓ normalizer (U : Set D)).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D))).map
    (gmsRootConjugateAction (U ⊔ R) R)

@[expose] def gmsPermStabilizer (U R : Subgroup D) :
    Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) :=
  (gmsRootConjugateAction (U ⊔ R) R).range ⊓
    MulAction.stabilizer _ (⟨R, gms_R_mem⟩ : gmsRootConjugates (U ⊔ R) R)

instance gmsRootKernel_normal (V R : Subgroup D) : (gmsRootKernel V R).Normal := by
  rw [← ker_gmsRootConjugateAction]
  infer_instance

end Defs

namespace GMSDichotomy

section Singer

variable {D : Type*} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem mem_gmsPermStabilizer {x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)} :
    x ∈ gmsPermStabilizer U R ↔
      x ∈ (gmsRootConjugateAction (U ⊔ R) R).range ∧ x ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ := by
  rw [gmsPermStabilizer, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

theorem action_R_eq_iff (l : normalizer ((U ⊔ R : Subgroup D) : Set D)) :
    gmsRootConjugateAction (U ⊔ R) R l ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ ↔
      (l : D) ∈ normalizer (R : Set D) := by
  rw [← map_conj_eq_self_iff, Subtype.ext_iff, gmsRootConjugateAction_apply]

theorem gmsPermStabilizer_eq_map :
    gmsPermStabilizer U R = ((normalizer (R : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D))).map (gmsRootConjugateAction (U ⊔ R) R) := by
  ext x
  rw [mem_gmsPermStabilizer]
  constructor
  · rintro ⟨⟨l, rfl⟩, hl⟩
    exact ⟨l, mem_subgroupOf.2 ((action_R_eq_iff l).1 hl), rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, rfl⟩, (action_R_eq_iff l).2 (mem_subgroupOf.1 hl)⟩

theorem rho_smul_eq_iff {V Q Z : Subgroup D} (hQ : Q ≤ V) (hZ : Z ≤ V)
    (l : normalizer (V : Set D)) :
    V.normalizerMonoidHom l • Q.subgroupOf V = Z.subgroupOf V ↔
      Q.map (MulAut.conj (l : D)).toMonoidHom = Z := by
  rw [← gms_map_rho hQ l]
  constructor
  · intro h1
    change (Q.subgroupOf V).map (V.normalizerMonoidHom l).toMonoidHom = Z.subgroupOf V at h1
    rw [h1, Subgroup.map_subgroupOf_eq_of_le hZ]
  · intro h1
    change (Q.subgroupOf V).map (V.normalizerMonoidHom l).toMonoidHom = Z.subgroupOf V
    apply Subgroup.map_injective V.subtype_injective
    rw [h1, Subgroup.map_subgroupOf_eq_of_le hZ]

theorem le_of_mem_gmsRootConjugates {W Q : Subgroup D} (hQ : Q ∈ gmsRootConjugates W R) :
    Q ≤ W := by
  obtain ⟨-, -, hle⟩ := hQ
  exact hle

theorem gmsSingerPermImage_le (h : GMSNormalRootData J R X U P n) :
    gmsSingerPermImage X U R ≤ gmsPermStabilizer U R := by
  have hXC : X ≤ centralizer (R : Set D) := h.2.2.2.1.2.2
  rintro _ ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hl
  rw [mem_gmsPermStabilizer]
  exact ⟨⟨l, rfl⟩, (action_R_eq_iff l).2 (centralizer_le_normalizer _ (hXC (mem_inf.1 hl).1))⟩

theorem gmsSingerPermImage_normal [Finite D] (h : GMSNormalRootData J R X U P n) :
    ((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)).Normal := by
  constructor
  intro t ht x
  rw [mem_subgroupOf] at ht ⊢
  obtain ⟨y, hy, hyt⟩ := ht
  obtain ⟨l, hl, hlx⟩ : (x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) ∈
      ((normalizer (R : Set D)).subgroupOf (normalizer ((U ⊔ R : Subgroup D) : Set D))).map
        (gmsRootConjugateAction (U ⊔ R) R) := by
    rw [← gmsPermStabilizer_eq_map]
    exact x.2
  rw [SetLike.mem_coe, mem_subgroupOf] at hy hl
  obtain ⟨-, -, hlY, -⟩ := gms_LR_normalizes h l.2 hl
  refine ⟨l * y * l⁻¹, mem_subgroupOf.2 ((mem_normalizer_iff.1 hlY y).1 hy), ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hlx, hyt]

theorem eq_one_of_mem_gmsSingerPermImage [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    {t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)} (ht : t ∈ gmsSingerPermImage X U R)
    {Q : gmsRootConjugates (U ⊔ R) R} (hQ : (Q : Subgroup D) ≠ R) (htQ : t Q = Q) : t = 1 := by
  obtain ⟨l, hl, rfl⟩ := ht
  rw [SetLike.mem_coe, mem_subgroupOf] at hl
  obtain ⟨-, -, -, -, -, -, -, -, hHreg, -, -, -, -, -, -, hπY, hρY⟩ :=
    gms_normal_root_partition_and_two_transitivity h h3
  have hQ' : (Q : Subgroup D) ∈ gmsRootConjugates (U ⊔ R) R \ {R} := ⟨Q.2, hQ⟩
  have hQV := le_of_mem_gmsRootConjugates Q.2
  have hfix : (U ⊔ R).normalizerMonoidHom l • (Q : Subgroup D).subgroupOf (U ⊔ R) =
      (Q : Subgroup D).subgroupOf (U ⊔ R) := by
    rw [rho_smul_eq_iff hQV hQV, ← gmsRootConjugateAction_apply, htQ]
  have hH : (U ⊔ R).normalizerMonoidHom l ∈ gmsSingerImage X U (U ⊔ R) :=
    ⟨l, mem_subgroupOf.2 hl, rfl⟩
  obtain ⟨α, -, huniq⟩ := hHreg Q hQ' Q hQ'
  have h1 : (⟨_, hH⟩ : gmsSingerImage X U (U ⊔ R)) = 1 :=
    (huniq ⟨_, hH⟩ hfix).trans (huniq 1 (one_smul _ _)).symm
  exact (hπY l hl).2 ((hρY l hl).1 (congrArg Subtype.val h1))

theorem exists_mem_gmsSingerPermImage_apply_eq [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) {Q Z : gmsRootConjugates (U ⊔ R) R}
    (hQ : (Q : Subgroup D) ≠ R) (hZ : (Z : Subgroup D) ≠ R) :
    ∃ t ∈ gmsSingerPermImage X U R, t Q = Z := by
  obtain ⟨-, -, -, -, -, -, -, -, hHreg, -⟩ := gms_normal_root_partition_and_two_transitivity h h3
  obtain ⟨⟨_, l, hl, rfl⟩, hα, -⟩ := hHreg Q ⟨Q.2, hQ⟩ Z ⟨Z.2, hZ⟩
  refine ⟨gmsRootConjugateAction (U ⊔ R) R l, ⟨l, hl, rfl⟩, Subtype.ext ?_⟩
  rw [gmsRootConjugateAction_apply]
  exact (rho_smul_eq_iff (le_of_mem_gmsRootConjugates Q.2) (le_of_mem_gmsRootConjugates Z.2) l).1
    hα

theorem nonempty_gmsSingerPermImage_equiv [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    Nonempty (GMSNormalizerQuotient X U ≃* gmsSingerPermImage X U R) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hπY, -⟩ :=
    gms_normal_root_partition_and_two_transitivity h h3
  have hNV := gms_NXU_le_L h
  set φ := (gmsRootConjugateAction (U ⊔ R) R).comp (Subgroup.inclusion hNV) with hφ
  have hker : φ.ker = (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, hφ, MonoidHom.comp_apply]
    exact hπY g g.2
  have hrange : φ.range = gmsSingerPermImage X U R := by
    ext t
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨Subgroup.inclusion hNV g, g.2, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem isCyclic_gmsSingerPermImage [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    IsCyclic (gmsSingerPermImage X U R) ∧ Nat.card (gmsSingerPermImage X U R) = 2 ^ n - 1 := by
  obtain ⟨e⟩ := nonempty_gmsSingerPermImage_equiv h h3
  obtain ⟨-, -, -, -, -, ⟨hcyc, hcard, -⟩, -⟩ := h
  exact ⟨isCyclic_of_surjective e.toMonoidHom e.surjective,
    (Nat.card_congr e.symm.toEquiv).trans hcard⟩

theorem gmsSingerPermImage_comm [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) {a b : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)}
    (ha : a ∈ gmsSingerPermImage X U R) (hb : b ∈ gmsSingerPermImage X U R) : a * b = b * a := by
  have := (isCyclic_gmsSingerPermImage h h3).1
  let _ : CommGroup (gmsSingerPermImage X U R) := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : gmsSingerPermImage X U R) ⟨b, hb⟩)

theorem mem_gmsSingerPermImage_of_commute [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    {x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)} (hx : x ∈ gmsPermStabilizer U R)
    (hxT : ∀ t ∈ gmsSingerPermImage X U R, x * t = t * x) : x ∈ gmsSingerPermImage X U R := by
  obtain ⟨Q₀, hQ₀, hQ₀R⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := gmsRootConjugates (U ⊔ R) R) (by omega) R
  set q₀ : gmsRootConjugates (U ⊔ R) R := ⟨Q₀, hQ₀⟩ with hq₀
  have hxR := (mem_gmsPermStabilizer.1 hx).2
  have hxq₀ : ((x q₀ : gmsRootConjugates (U ⊔ R) R) : Subgroup D) ≠ R := by
    intro h1
    apply hQ₀R
    have h2 : x q₀ = ⟨R, gms_R_mem⟩ := Subtype.ext h1
    rw [← hxR] at h2
    exact congrArg Subtype.val (x.injective h2)
  obtain ⟨t₀, ht₀, ht₀q⟩ := exists_mem_gmsSingerPermImage_apply_eq h h3 (Q := q₀) hQ₀R hxq₀
  suffices hxt : x = t₀ by rw [hxt]; exact ht₀
  ext1 Q
  by_cases hQR : (Q : Subgroup D) = R
  · have hQ : Q = ⟨R, gms_R_mem⟩ := Subtype.ext hQR
    rw [hQ, hxR, (mem_gmsPermStabilizer.1 (gmsSingerPermImage_le h ht₀)).2]
  · obtain ⟨t, ht, rfl⟩ := exists_mem_gmsSingerPermImage_apply_eq h h3 (Q := q₀) hQ₀R hQR
    rw [← Equiv.Perm.mul_apply, hxT t ht, Equiv.Perm.mul_apply, ← ht₀q, ← Equiv.Perm.mul_apply,
      gmsSingerPermImage_comm h h3 ht ht₀, Equiv.Perm.mul_apply]

end Singer

section Field

variable {D : Type*} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem exists_conj_eq_pow [Finite D] (h : GMSNormalRootData J R X U P n) {l : D}
    (hlV : l ∈ normalizer ((U ⊔ R : Subgroup D) : Set D)) (hlR : l ∈ normalizer (R : Set D)) :
    ∃ j : ℕ, ∀ y ∈ X ⊓ normalizer (U : Set D), ∀ u ∈ U,
      (l * y * l⁻¹) * u * (l * y * l⁻¹)⁻¹ = y ^ (2 ^ j) * u * (y ^ (2 ^ j))⁻¹ := by
  classical
  obtain ⟨⟨K, _, _, _, -, e, hsc1, hsc2, -⟩, -⟩ :=
    SteinbergBT.gms_normal_root_singer_action_and_weak_closure h
  obtain ⟨-, hlU, hlY, -⟩ := gms_LR_normalizes h hlV hlR
  set cl : MulAut U := U.normalizerMonoidHom ⟨l, hlU⟩ with hcl
  have hcl_apply : ∀ u : U, ((cl u : U) : D) = l * u * l⁻¹ := fun u => rfl
  set φ : K ≃+ K := (e.symm.trans (MulEquiv.toAdditive cl)).trans e with hφ
  have hφe : ∀ u : U, φ (e (Additive.ofMul u)) = e (Additive.ofMul (cl u)) := by
    intro u
    rw [hφ, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
    rfl
  have hkey : ∀ c : Kˣ, ∃ c' : Kˣ, ∀ k : K, φ (c * k) = c' * φ k := by
    intro c
    obtain ⟨g, hg, hgc⟩ := hsc2 c
    have hg' : l * g * l⁻¹ ∈ X ⊓ normalizer (U : Set D) := (mem_normalizer_iff.1 hlY g).1 hg
    obtain ⟨c', hc'⟩ := hsc1 _ hg'
    refine ⟨c', fun k => ?_⟩
    obtain ⟨u, rfl⟩ : ∃ u : U, e (Additive.ofMul u) = k :=
      ⟨Additive.toMul (e.symm k), by rw [ofMul_toMul, AddEquiv.apply_symm_apply]⟩
    have hgN : g ∈ normalizer (U : Set D) := (mem_inf.1 hg).2
    obtain ⟨v, hv⟩ : ∃ v : U, (v : D) = g * u * g⁻¹ :=
      ⟨⟨_, (mem_normalizer_iff.1 hgN u).1 u.2⟩, rfl⟩
    rw [← hgc u v hv, hφe, hφe]
    exact hc' (cl u) (cl v) (by rw [hcl_apply, hcl_apply, hv]; group)
  have hsemi : ∀ a k : K, φ (a * k) = φ (a * φ.symm 1) * φ k := by
    intro a k
    by_cases ha : a = 0
    · rw [ha, zero_mul, zero_mul, map_zero, zero_mul]
    · obtain ⟨c', hc'⟩ := hkey (Units.mk0 a ha)
      rw [Units.val_mk0] at hc'
      rw [hc', hc', AddEquiv.apply_symm_apply, mul_one]
  let σ : K →+* K :=
    { toFun := fun a => φ (a * φ.symm 1)
      map_one' := by simp only [one_mul, AddEquiv.apply_symm_apply]
      map_mul' := fun a b => by
        simp only [mul_assoc]
        exact hsemi a (b * φ.symm 1)
      map_zero' := by simp only [zero_mul, map_zero]
      map_add' := fun a b => by simp only [add_mul, map_add] }
  have hσinj : Function.Injective σ := σ.injective
  let σe : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨hσinj, Finite.injective_iff_surjective.1 hσinj⟩
  let σa : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := σe) fun x =>
    DFunLike.congr_fun
      (RingHom.ext_zmod (σe.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K)) x
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) K).2 σa
  have hσpow : ∀ a : K, φ (a * φ.symm 1) = a ^ (2 ^ (j : ℕ)) := by
    intro a
    have h1 : σa a = a ^ (2 ^ (j : ℕ)) := by
      rw [← hj]
      change ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ (j : ℕ)) a = _
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]
    exact h1
  refine ⟨j, fun y hy u hu => ?_⟩
  obtain ⟨c, hc⟩ := hsc1 y hy
  have hyN : y ∈ normalizer (U : Set D) := (mem_inf.1 hy).2
  have hpow : ∀ m : ℕ, ∀ u v : U, (v : D) = y ^ m * u * (y ^ m)⁻¹ →
      e (Additive.ofMul v) = (c : K) ^ m * e (Additive.ofMul u) := by
    intro m
    induction m with
    | zero =>
      intro u v huv
      rw [pow_zero, one_mul, inv_one, mul_one] at huv
      rw [pow_zero, one_mul, Subtype.ext huv]
    | succ m ih =>
      intro u v huv
      obtain ⟨w, hw⟩ : ∃ w : U, (w : D) = y ^ m * u * (y ^ m)⁻¹ :=
        ⟨⟨_, (mem_normalizer_iff.1 (pow_mem hyN m) u).1 u.2⟩, rfl⟩
      rw [hc w v (by rw [huv, hw, pow_succ']; group), ih u w hw, pow_succ', mul_assoc]
  have hu'mem : l⁻¹ * u * l ∈ U := by
    have h1 := (mem_normalizer_iff.1 (inv_mem hlU) u).1 hu
    rwa [inv_inv] at h1
  obtain ⟨u', hu'⟩ : ∃ u' : U, (u' : D) = l⁻¹ * u * l := ⟨⟨_, hu'mem⟩, rfl⟩
  obtain ⟨w₁, hw₁⟩ : ∃ w : U, (w : D) = y * u' * y⁻¹ :=
    ⟨⟨_, (mem_normalizer_iff.1 hyN u').1 u'.2⟩, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ v : U, (v : D) = y ^ (2 ^ (j : ℕ)) * u * (y ^ (2 ^ (j : ℕ)))⁻¹ :=
    ⟨⟨_, (mem_normalizer_iff.1 (pow_mem hyN _) u).1 hu⟩, rfl⟩
  have hcu' : cl u' = ⟨u, hu⟩ := Subtype.ext (by rw [hcl_apply, hu']; group)
  have h1 : e (Additive.ofMul (cl w₁)) = e (Additive.ofMul v₂) := by
    rw [← hφe, hc u' w₁ hw₁, hsemi, hσpow, hφe, hcu', hpow _ ⟨u, hu⟩ v₂ hv₂]
  have h2 : cl w₁ = v₂ := Additive.ofMul.injective (e.injective h1)
  calc (l * y * l⁻¹) * u * (l * y * l⁻¹)⁻¹ = ((cl w₁ : U) : D) := by
        rw [hcl_apply, hw₁, hu']
        group
    _ = y ^ (2 ^ (j : ℕ)) * u * (y ^ (2 ^ (j : ℕ)))⁻¹ := by rw [h2, hv₂]

theorem exists_conj_eq_pow_perm [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    {x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)} (hx : x ∈ gmsPermStabilizer U R) :
    ∃ j : ℕ, ∀ t ∈ gmsSingerPermImage X U R, x * t * x⁻¹ = t ^ (2 ^ j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hπY, -⟩ :=
    gms_normal_root_partition_and_two_transitivity h h3
  obtain ⟨l, hl, rfl⟩ : x ∈ ((normalizer (R : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D))).map (gmsRootConjugateAction (U ⊔ R) R) := by
    rw [← gmsPermStabilizer_eq_map]
    exact hx
  rw [SetLike.mem_coe, mem_subgroupOf] at hl
  obtain ⟨j, hj⟩ := exists_conj_eq_pow h l.2 hl
  obtain ⟨-, -, hlY, -⟩ := gms_LR_normalizes h l.2 hl
  refine ⟨j, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hy
  have ha : ((l * y * l⁻¹ : normalizer ((U ⊔ R : Subgroup D) : Set D)) : D) ∈
      X ⊓ normalizer (U : Set D) := (mem_normalizer_iff.1 hlY y).1 hy
  have hb : ((y ^ (2 ^ j) : normalizer ((U ⊔ R : Subgroup D) : Set D)) : D) ∈
      X ⊓ normalizer (U : Set D) := by
    rw [SubgroupClass.coe_pow]
    exact pow_mem hy _
  have hba : (((y ^ (2 ^ j))⁻¹ * (l * y * l⁻¹) : normalizer ((U ⊔ R : Subgroup D) : Set D)) :
      D) ∈ X ⊓ centralizer (U : Set D) := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (mem_inf.1 hb).1) (mem_inf.1 ha).1,
      mem_centralizer_iff.2 fun u hu => ?_⟩
    have h1 := hj y hy u hu
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
    calc u * (((y : D) ^ 2 ^ j)⁻¹ * (l * y * (l : D)⁻¹)) =
        ((y : D) ^ 2 ^ j)⁻¹ * ((y : D) ^ 2 ^ j * u * ((y : D) ^ 2 ^ j)⁻¹) *
          (l * y * (l : D)⁻¹) := by group
      _ = ((y : D) ^ 2 ^ j)⁻¹ * ((l * y * (l : D)⁻¹) * u * (l * y * (l : D)⁻¹)⁻¹) *
          (l * y * (l : D)⁻¹) := by rw [h1]
      _ = ((y : D) ^ 2 ^ j)⁻¹ * (l * y * (l : D)⁻¹) * u := by group
  have h1 := (hπY _ (mul_mem (inv_mem hb) ha)).2 hba
  have h2 : gmsRootConjugateAction (U ⊔ R) R ((y ^ (2 ^ j))⁻¹ * (l * y * l⁻¹)) = 1 := h1
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← map_pow, h2, map_mul, map_mul, map_inv]

theorem isCyclic_quotient_and_card_dvd [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    [((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)).Normal] :
    IsCyclic (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) ∧
      Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) ∣ n := by
  classical
  set T' := (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R) with hT'
  have hle := gmsSingerPermImage_le h (X := X)
  have hT'card : Nat.card T' = 2 ^ n - 1 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (isCyclic_gmsSingerPermImage h h3).2
  have hcomm : ∀ a b : T', a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (gmsSingerPermImage_comm h h3 a.2 b.2))
  let sqHom : T' →* T' :=
    { toFun := fun a => a * a
      map_one' := mul_one 1
      map_mul' := fun a b => by
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hcomm b a]
          _ = a * a * (b * b) := by group }
  have hn1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd : (2 ^ n - 1 + 1) / 2 * 2 = 2 ^ n - 1 + 1 := by
    have h0 : 0 < n := by have := h.1; omega
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 h0.ne'
    omega
  have hsurj : Function.Surjective sqHom := fun a =>
    ⟨a ^ ((2 ^ n - 1 + 1) / 2), by
      change a ^ ((2 ^ n - 1 + 1) / 2) * a ^ ((2 ^ n - 1 + 1) / 2) = a
      rw [← pow_add, ← two_mul, mul_comm, hodd, pow_succ, ← hT'card, pow_card_eq_one', one_mul]⟩
  let sqAut : MulAut T' :=
    MulEquiv.ofBijective sqHom ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  have hsq_apply : ∀ a : T', sqAut a = a * a := fun a => rfl
  have hsqpow : ∀ (j : ℕ) (a : T'), (sqAut ^ j) a = a ^ (2 ^ j) := by
    intro j
    induction j with
    | zero => intro a; rfl
    | succ j ih =>
      intro a
      rw [pow_succ, MulAut.mul_apply, ih, hsq_apply, ← pow_two, ← pow_mul, ← pow_succ']
  have hsqn : sqAut ^ n = 1 := by
    ext1 a
    rw [hsqpow, MulAut.one_apply, show 2 ^ n = 2 ^ n - 1 + 1 by omega, pow_succ, ← hT'card,
      pow_card_eq_one', one_mul]
  set κ : gmsPermStabilizer U R →* MulAut T' := MulAut.conjNormal with hκ
  have hκrange : κ.range ≤ zpowers sqAut := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨j, hj⟩ := exists_conj_eq_pow_perm h h3 x.2
    have hκx : κ x = sqAut ^ j := by
      ext1 a
      rw [hsqpow]
      apply Subtype.ext
      apply Subtype.ext
      rw [hκ, MulAut.conjNormal_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
      exact hj _ a.2
    rw [hκx]
    exact pow_mem (mem_zpowers sqAut) j
  have hker : κ.ker = T' := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hxT : ∀ t ∈ gmsSingerPermImage X U R,
          (x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) * t = t * (x : Equiv.Perm _) := by
        intro t ht
        have h1 := congrArg (fun φ : MulAut T' => ((φ ⟨⟨t, hle ht⟩, ht⟩ : T') :
          gmsPermStabilizer U R)) hx
        simp only [hκ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
        have h2 := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
        calc (x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) * t =
            ((x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) * t * (x : Equiv.Perm _)⁻¹) *
              (x : Equiv.Perm _) := by group
          _ = t * (x : Equiv.Perm _) := by rw [h2]
      exact mem_gmsSingerPermImage_of_commute h h3 x.2 hxT
    · intro hx
      ext1 a
      apply Subtype.ext
      rw [hκ, MulAut.conjNormal_apply, MulAut.one_apply]
      have h1 := hcomm ⟨x, hx⟩ a
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul] at h2
      rw [h2, mul_inv_cancel_right]
  let e : gmsPermStabilizer U R ⧸ T' ≃* κ.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange κ)
  have hcyc : IsCyclic κ.range := Subgroup.isCyclic_of_le hκrange
  refine ⟨isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact (Subgroup.card_dvd_of_le hκrange).trans
    ((Nat.card_zpowers sqAut).symm ▸ orderOf_dvd_of_pow_eq_one hsqn)

end Field

section Affine

variable {D : Type*} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem affine_branch [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    (A : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)))
    (hAN : A ≤ (gmsRootConjugateAction (U ⊔ R) R).range)
    (hAn : (A.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal)
    (hreg : ∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : A, (a : Equiv.Perm _) Q = Z) :
    IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ n ∧
      A ⊔ gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      ((A ⊔ gmsSingerPermImage X U R).subgroupOf
        (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      Nat.card (A ⊔ gmsSingerPermImage X U R : Subgroup _) = 2 ^ n * (2 ^ n - 1) ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃ f ∈ A ⊔ gmsSingerPermImage X U R, f Q = Z) ∧
      ∀ f ∈ A ⊔ gmsSingerPermImage X U R, f ≠ 1 → ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
        f Q = Q → f Z = Z → Q = Z := by
  classical
  set R₀ : gmsRootConjugates (U ⊔ R) R := ⟨R, gms_R_mem⟩ with hR₀
  have hTN : gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range :=
    (gmsSingerPermImage_le h).trans inf_le_left
  have htR : ∀ t ∈ gmsSingerPermImage X U R, t R₀ = R₀ := fun t ht =>
    (mem_gmsPermStabilizer.1 (gmsSingerPermImage_le h ht)).2
  have hconjA : ∀ x ∈ (gmsRootConjugateAction (U ⊔ R) R).range, ∀ a ∈ A, x * a * x⁻¹ ∈ A :=
    fun x hx a ha => hAn.conj_mem ⟨a, hAN ha⟩ (mem_subgroupOf.2 ha) ⟨x, hx⟩
  have hAfree : ∀ a ∈ A, ∀ Q, a Q = Q → a = 1 := by
    intro a ha Q haQ
    obtain ⟨b, -, hb⟩ := hreg Q Q
    exact congrArg Subtype.val ((hb ⟨a, ha⟩ haQ).trans (hb 1 rfl).symm)
  have hΔcard : Nat.card (gmsRootConjugates (U ⊔ R) R) = 2 ^ n := by
    rw [Nat.card_coe_set_eq]
    exact (gms_normal_root_partition_and_two_transitivity h h3).2.1
  have hAcard : Nat.card A = 2 ^ n := by
    rw [← hΔcard]
    refine Nat.card_congr (Equiv.ofBijective (fun a : A => (a : Equiv.Perm _) R₀) ⟨?_, ?_⟩)
    · intro a b hab
      obtain ⟨c, -, hc⟩ := hreg R₀ ((a : Equiv.Perm _) R₀)
      exact (hc a rfl).trans (hc b hab.symm).symm
    · intro Q
      obtain ⟨a, ha, -⟩ := hreg R₀ Q
      exact ⟨a, ha⟩
  have hconj : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 →
      ∃ t ∈ gmsSingerPermImage X U R, t * a * t⁻¹ = b := by
    intro a ha b hb ha1 hb1
    have haR : ((a R₀ : gmsRootConjugates (U ⊔ R) R) : Subgroup D) ≠ R := fun h1 =>
      ha1 (hAfree a ha R₀ (Subtype.ext h1))
    have hbR : ((b R₀ : gmsRootConjugates (U ⊔ R) R) : Subgroup D) ≠ R := fun h1 =>
      hb1 (hAfree b hb R₀ (Subtype.ext h1))
    obtain ⟨t, ht, hta⟩ := exists_mem_gmsSingerPermImage_apply_eq h h3 haR hbR
    refine ⟨t, ht, ?_⟩
    have htinv : t⁻¹ R₀ = R₀ := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (htR t ht).symm
    obtain ⟨c, -, hc⟩ := hreg R₀ (b R₀)
    have h1 := hc ⟨t * a * t⁻¹, hconjA t (hTN ht) a ha⟩ (by
      change (t * a * t⁻¹) R₀ = b R₀
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htinv, hta])
    exact congrArg Subtype.val (h1.trans (hc ⟨b, hb⟩ rfl).symm)
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := A) 2
      (by rw [hAcard]; exact dvd_pow_self 2 (by have := h.1; omega))
    have ha₀sq : (a₀ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) ^ 2 = 1 := by
      have h1 := pow_orderOf_eq_one a₀
      rw [ha₀] at h1
      exact congrArg Subtype.val h1
    have ha₀1 : (a₀ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) ≠ 1 := by
      intro h1
      have h2 : a₀ = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at ha₀
      omega
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1, one_pow]
    · obtain ⟨t, -, hta⟩ := hconj (a₀ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) a₀.2 a ha ha₀1 ha1
      rw [← hta, conj_pow, ha₀sq, mul_one, mul_inv_cancel]
  have hAcomm : ∀ a b : A, a * b = b * a := by
    intro a b
    have hsq : ∀ c : A, c * c = 1 := fun c => by
      rw [← pow_two]
      exact Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hA2 c c.2)
    have h1 := mul_eq_one_iff_eq_inv.1 (hsq (a * b))
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq a), inv_eq_of_mul_eq_one_right (hsq b)]
  have hel : IsElementaryAbelian 2 A :=
    { is_comm := ⟨hAcomm⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun c =>
        Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hA2 c c.2) }
  have hFmem : ∀ f ∈ A ⊔ gmsSingerPermImage X U R,
      ∃ a ∈ A, ∃ t ∈ gmsSingerPermImage X U R, f = a * t := by
    let F₀ : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) :=
      { carrier := {f | ∃ a ∈ A, ∃ t ∈ gmsSingerPermImage X U R, f = a * t}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, t, ht, rfl⟩ ⟨b, hb, s, hs, rfl⟩
          exact ⟨a * (t * b * t⁻¹), mul_mem ha (hconjA t (hTN ht) b hb), t * s, mul_mem ht hs,
            by group⟩
        inv_mem' := by
          rintro _ ⟨a, ha, t, ht, rfl⟩
          exact ⟨t⁻¹ * a⁻¹ * t⁻¹⁻¹, hconjA t⁻¹ (inv_mem (hTN ht)) a⁻¹ (inv_mem ha), t⁻¹,
            inv_mem ht, by group⟩ }
    have hle : A ⊔ gmsSingerPermImage X U R ≤ F₀ :=
      sup_le (fun a ha => ⟨a, ha, 1, one_mem _, (mul_one a).symm⟩)
        (fun t ht => ⟨1, one_mem _, t, ht, (one_mul t).symm⟩)
    exact fun f hf => hle hf
  refine ⟨hel, hAcard, sup_le hAN hTN, ?_, ?_, ?_, ?_⟩
  ·
    constructor
    intro f hf x
    rw [mem_subgroupOf] at hf ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    obtain ⟨⟨a, ha⟩, haR, -⟩ := hreg R₀ ((x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) R₀)
    set m : Equiv.Perm (gmsRootConjugates (U ⊔ R) R) := a⁻¹ * (x : Equiv.Perm _) with hm
    have hmN : m ∈ (gmsRootConjugateAction (U ⊔ R) R).range := mul_mem (inv_mem (hAN ha)) x.2
    have hmR : m R₀ = R₀ := by
      rw [hm, Equiv.Perm.mul_apply, ← haR, ← Equiv.Perm.mul_apply, inv_mul_cancel,
        Equiv.Perm.one_apply]
    have hmNR : m ∈ gmsPermStabilizer U R := mem_gmsPermStabilizer.2 ⟨hmN, hmR⟩
    obtain ⟨b, hb, t, ht, hft⟩ := hFmem f hf
    rw [hft]
    have hmb := hconjA _ hmN b hb
    have hmt : m * t * m⁻¹ ∈ gmsSingerPermImage X U R := by
      have h1 := (gmsSingerPermImage_normal h).conj_mem ⟨t, gmsSingerPermImage_le h ht⟩
        (mem_subgroupOf.2 ht) ⟨_, hmNR⟩
      rw [mem_subgroupOf] at h1
      exact h1
    have heq : (x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) * (b * t) *
        (x : Equiv.Perm (gmsRootConjugates (U ⊔ R) R))⁻¹ =
        a * (m * b * m⁻¹) * (m * t * m⁻¹) * a⁻¹ := by
      rw [hm]
      group
    rw [heq]
    exact mul_mem (mul_mem (mul_mem (mem_sup_left ha) (mem_sup_left hmb)) (mem_sup_right hmt))
      (inv_mem (mem_sup_left ha))
  ·
    rw [← (isCyclic_gmsSingerPermImage h h3).2, ← hAcard, ← Nat.card_prod]
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun p : A × gmsSingerPermImage X U R =>
      (⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ :
        (A ⊔ gmsSingerPermImage X U R : Subgroup _))) ⟨?_, ?_⟩)
    · rintro ⟨a, t⟩ ⟨a', t'⟩ hEq
      obtain ⟨a, ha⟩ := a
      obtain ⟨a', ha'⟩ := a'
      obtain ⟨t, ht⟩ := t
      obtain ⟨t', ht'⟩ := t'
      have h1 : a * t = a' * t' := congrArg Subtype.val hEq
      have h2 : a'⁻¹ * a = t' * t⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * t) * t⁻¹ := by group
          _ = a'⁻¹ * (a' * t') * t⁻¹ := by rw [h1]
          _ = t' * t⁻¹ := by group
      have htinv : t⁻¹ R₀ = R₀ := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (htR t ht).symm
      have h3 : a'⁻¹ * a = 1 := hAfree _ (mul_mem (inv_mem ha') ha) R₀ (by
        rw [h2, Equiv.Perm.mul_apply, htinv, htR t' ht'])
      have haa : a = a' := by
        rw [← mul_inv_cancel_left a' a, h3, mul_one]
      subst haa
      have htt : t = t' := mul_left_cancel h1
      subst htt
      rfl
    · rintro ⟨f, hf⟩
      obtain ⟨a, ha, t, ht, rfl⟩ := hFmem f hf
      exact ⟨(⟨a, ha⟩, ⟨t, ht⟩), rfl⟩
  ·
    intro Q Z
    obtain ⟨a, ha, -⟩ := hreg Q Z
    exact ⟨a, mem_sup_left a.2, ha⟩
  ·
    intro f hf hf1 Q Z hfQ hfZ
    by_contra hQZ
    obtain ⟨⟨a₀, ha₀⟩, ha₀Q, -⟩ := hreg R₀ Q
    have ha₀Q' : a₀ R₀ = Q := ha₀Q
    have hf' : a₀⁻¹ * f * a₀ ∈ A ⊔ gmsSingerPermImage X U R :=
      mul_mem (mul_mem (inv_mem (mem_sup_left ha₀)) hf) (mem_sup_left ha₀)
    obtain ⟨a, ha, t, ht, hat⟩ := hFmem _ hf'
    have hf'R : (a₀⁻¹ * f * a₀) R₀ = R₀ := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha₀Q', hfQ, ← ha₀Q', ← Equiv.Perm.mul_apply,
        inv_mul_cancel, Equiv.Perm.one_apply]
    have ha1 : a = 1 := hAfree a ha R₀ (by
      rw [hat, Equiv.Perm.mul_apply, htR t ht] at hf'R
      exact hf'R)
    have hZ' : ((a₀⁻¹ Z : gmsRootConjugates (U ⊔ R) R) : Subgroup D) ≠ R := by
      intro h1
      apply hQZ
      have h2 : a₀⁻¹ Z = R₀ := Subtype.ext h1
      rw [← ha₀Q', ← h2, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
    have htZ : t (a₀⁻¹ Z) = a₀⁻¹ Z := by
      have h1 : (a₀⁻¹ * f * a₀) (a₀⁻¹ Z) = a₀⁻¹ Z := by
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply a₀,
          mul_inv_cancel, Equiv.Perm.one_apply, hfZ]
      rw [hat, ha1, one_mul] at h1
      exact h1
    have ht1 := eq_one_of_mem_gmsSingerPermImage h h3 ht hZ' htZ
    apply hf1
    have h1 : a₀⁻¹ * f * a₀ = 1 := by rw [hat, ha1, ht1, one_mul]
    calc f = a₀ * (a₀⁻¹ * f * a₀) * a₀⁻¹ := by group
      _ = 1 := by rw [h1, mul_one, mul_inv_cancel]

end Affine

section Arith

theorem lt_two_pow_pred_sub_one {n : ℕ} (hn : 4 ≤ n) : n < 2 ^ (n - 1) - 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
      rw [Nat.add_sub_cancel, ← pow_succ']
      congr 1
      omega
    omega

theorem psl_branch_arith {n p s d c : ℕ} (hn : 3 ≤ n) (hp : p + 1 = 2 ^ n)
    (hc : c * 2 = p * (p ^ 2 - 1)) (hs : s * 2 ^ n = c) (hsd : s ∣ d * p) (hd : d ∣ n) :
    (p - 1) / 2 ∣ n ∧ n = 3 ∧ p = 7 ∧ d = 3 := by
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨2 ^ (n - 1) - 1, by omega⟩
  have hk : (2 * k + 1 - 1) / 2 = k := by omega
  rw [hk]
  have hs' : s = k * (2 * k + 1) := by
    have h1 : s * (2 * k + 2) * 2 = (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) := by
      rw [← hc, ← hs, ← hp]
    have h2 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
      have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
      omega
    rw [h2] at h1
    have h3 : (4 * (k + 1)) * s = (4 * (k + 1)) * (k * (2 * k + 1)) := by
      calc (4 * (k + 1)) * s = s * (2 * k + 2) * 2 := by ring
        _ = (2 * k + 1) * (4 * k * (k + 1)) := h1
        _ = (4 * (k + 1)) * (k * (2 * k + 1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  rw [hs'] at hsd
  have hkd : k ∣ d := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < 2 * k + 1) hsd
  have hkn : k ∣ n := hkd.trans hd
  have hn3 : n = 3 := by
    by_contra hne
    have hkle : k ≤ n := Nat.le_of_dvd (by omega) hkn
    have hlt := lt_two_pow_pred_sub_one (show 4 ≤ n by omega)
    omega
  subst hn3
  have hk3 : k = 3 := by
    norm_num at hp
    omega
  subst hk3
  refine ⟨hkn, rfl, rfl, ?_⟩
  have hd3 : d ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  obtain ⟨m, hm⟩ := hkd
  rcases m with _ | _ | m
  · rw [hm] at hd
    simp at hd
  · omega
  · omega

theorem zmod_seven_three : (3 : ZMod 7) ≠ 0 ∧ (3 : ZMod 7) ^ 2 ≠ 1 := by decide

theorem card_PSL_two_mul_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) * 2 = p * (p ^ 2 - 1) := by
  have hp : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp2)
  have : Fact (2 < p) := ⟨hp⟩
  have hcenter : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = 2 := by
    rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
      Fintype.card_fin]
    exact (IsPrimitiveRoot.neg_one p hp2).card_rootsOfUnity
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
    rw [Matrix.card_SL_field, ZMod.card, Fin.prod_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    have hp1 : 0 < p - 1 := by omega
    have h1 : (p ^ 2 - 1) * (p ^ 2 - p) = p * (p ^ 2 - 1) * (p - 1) := by
      have h2 : p ^ 2 - p = p * (p - 1) := by
        rw [Nat.mul_sub_one, sq]
      rw [h2]
      ring
    rw [h1, Nat.mul_div_cancel _ hp1]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
  rw [hcenter, hSL] at h
  exact h.symm

end Arith

section PSL

variable {D : Type} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem psl_branch [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (p : ℕ) (hpp : p.Prime) (hp : p + 1 = 2 ^ n)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p)
    (S : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)))
    (hSN : S ≤ (gmsRootConjugateAction (U ⊔ R) R).range)
    (β : gmsRootConjugates (U ⊔ R) R ≃ ℙ K (Fin 2 → K))
    (hβ : ∀ σ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R), σ ∈ S ↔
      ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, ∀ Q, β (σ Q) = g • β Q) :
    (p - 1) / 2 ∣ n ∧ n = 3 ∧
      Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 3 ∧
      (gmsRootConjugateAction (U ⊔ R) R).range = S ∧
      ⁅(gmsRootConjugateAction (U ⊔ R) R).range, (gmsRootConjugateAction (U ⊔ R) R).range⁆ =
        (gmsRootConjugateAction (U ⊔ R) R).range ∧
      Nonempty (↥⁅(gmsRootConjugateAction (U ⊔ R) R).range,
          (gmsRootConjugateAction (U ⊔ R) R).range⁆ ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) := by
  classical
  have : Fact p.Prime := ⟨hpp⟩
  set R₀ : gmsRootConjugates (U ⊔ R) R := ⟨R, gms_R_mem⟩ with hR₀
  have hn3 : 3 ≤ n := h.1
  have hΔcard : Nat.card (gmsRootConjugates (U ⊔ R) R) = 2 ^ n := by
    rw [Nat.card_coe_set_eq]
    exact (gms_normal_root_partition_and_two_transitivity h h3).2.1
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hKcard : Fintype.card K = Fintype.card (ZMod p) := by rw [ZMod.card, hK]
  let φ : K ≃+* ZMod p := FiniteField.ringEquivOfCardEq hKcard
  let ψ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K →*
      Equiv.Perm (gmsRootConjugates (U ⊔ R) R) :=
    β.symm.permCongrHom.toMonoidHom.comp Projectivization.PSLAction.toPermHom
  have hψ : ∀ g Q, β (ψ g Q) = g • β Q := fun g Q => by
    change β (β.symm _) = _
    rw [Equiv.apply_symm_apply]
    rfl
  have hψinj : Function.Injective ψ :=
    β.symm.permCongrHom.injective.comp Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective
  have hSψ : S = ψ.range := by
    ext σ
    rw [hβ σ, MonoidHom.mem_range]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, Equiv.ext fun Q => β.injective (by rw [hψ, hg])⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, hψ g⟩
  have hScard : Nat.card S * 2 = p * (p ^ 2 - 1) := by
    rw [← card_PSL_two_mul_two p (by omega), hSψ]
    congr 1
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv.symm).trans
      (Nat.card_congr (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2)).toEquiv)
  have : MulAction.IsPretransitive S (gmsRootConjugates (U ⊔ R) R) := ⟨fun Q Z => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (β Q) (β Z)
    refine ⟨⟨ψ g, by rw [hSψ]; exact ⟨g, rfl⟩⟩, β.injective ?_⟩
    change β (ψ g Q) = β Z
    rw [hψ, hg]⟩
  have hSstab := Subgroup.card_mul_index (MulAction.stabilizer S R₀)
  rw [MulAction.index_stabilizer_of_transitive, hΔcard] at hSstab
  have hstabdvd : Nat.card (MulAction.stabilizer S R₀) ∣ Nat.card (gmsPermStabilizer U R) := by
    have hle : (MulAction.stabilizer S R₀).map S.subtype ≤ gmsPermStabilizer U R := by
      rintro _ ⟨s, hs, rfl⟩
      exact mem_gmsPermStabilizer.2 ⟨hSN s.2, MulAction.mem_stabilizer_iff.1 hs⟩
    rw [← Subgroup.card_map_of_injective (K := MulAction.stabilizer S R₀) S.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hnorm := gmsSingerPermImage_normal h (X := X)
  have hT'card : Nat.card ((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (gmsSingerPermImage_le h)).toEquiv,
      (isCyclic_gmsSingerPermImage h h3).2]
    omega
  have hNR := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R))
  rw [hT'card] at hNR
  have hd := (isCyclic_quotient_and_card_dvd h h3).2
  obtain ⟨hdvd, hn, hp7, hd3⟩ := psl_branch_arith hn3 hp hScard hSstab (hNR ▸ hstabdvd) hd
  subst hn hp7
  have : MulAction.IsPretransitive (gmsRootConjugateAction (U ⊔ R) R).range
      (gmsRootConjugates (U ⊔ R) R) := ⟨fun Q Z => by
    have := gms_isPretransitive h
    obtain ⟨l, hl⟩ := MulAction.exists_smul_eq (normalizer ((U ⊔ R : Subgroup D) : Set D)) Q Z
    exact ⟨⟨gmsRootConjugateAction (U ⊔ R) R l, l, rfl⟩, hl⟩⟩
  have hNstab := Subgroup.card_mul_index
    (MulAction.stabilizer (gmsRootConjugateAction (U ⊔ R) R).range R₀)
  rw [MulAction.index_stabilizer_of_transitive, hΔcard] at hNstab
  have hNRstab : (MulAction.stabilizer (gmsRootConjugateAction (U ⊔ R) R).range R₀).map
      (gmsRootConjugateAction (U ⊔ R) R).range.subtype = gmsPermStabilizer U R := by
    ext x
    rw [mem_gmsPermStabilizer]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, MulAction.mem_stabilizer_iff.1 hy⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨x, hx⟩, MulAction.mem_stabilizer_iff.2 hxR, rfl⟩
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at hNstab
  rw [hNRstab, hNR, hd3] at hNstab
  have hNcard : Nat.card (gmsRootConjugateAction (U ⊔ R) R).range = 168 := by
    rw [← hNstab]
    norm_num
  have hScard' : Nat.card S = 168 := by
    norm_num at hScard
    omega
  have hSN' : S = (gmsRootConjugateAction (U ⊔ R) R).range :=
    Subgroup.eq_of_le_of_card_ge hSN (by rw [hNcard, hScard'])
  have hF : ∃ a : K, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    refine ⟨φ.symm 3, fun h0 => ?_, fun h1 => ?_⟩
    · have h2 := congrArg φ h0
      rw [RingEquiv.apply_symm_apply, map_zero] at h2
      exact zmod_seven_three.1 h2
    · have h2 := congrArg φ h1
      rw [map_pow, RingEquiv.apply_symm_apply, map_one] at h2
      exact zmod_seven_three.2 h2
  have hperf : ⁅S, S⁆ = S := by
    rw [hSψ, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      SL2Simple.PSL_commutator_eq_top hF]
  refine ⟨hdvd, rfl, hd3, hSN'.symm, by rw [← hSN', hperf], ?_⟩
  rw [← hSN', hperf, hSψ]
  exact ⟨(MonoidHom.ofInjective hψinj).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))⟩

theorem lieModel_psl_three_two_of_mulEquiv {G : Type} [Group G]
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :
    CFSG.Blueprint.LieModel G .PSL 3 2 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₄⟩ := ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ ComponentInitial.bijective_toGL_three_zmod_two
  have hadm : Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
  have hmem : Assembly.LowTwoRank.StatedLieTag.PSL ∈ CFSG.Blueprint.classicalTags := by decide
  exact Or.inl ⟨hmem, hadm, ZMod 2, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(((e.trans e₄.symm).trans e₃.symm).trans e₂.symm).trans
      (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2))⟩⟩

end PSL

section Kernel

variable {D : Type*} [Group D]

theorem map_commutator_gmsRootConjugateAction (V R : Subgroup D) :
    (commutator (normalizer (V : Set D))).map (gmsRootConjugateAction V R) =
      ⁅(gmsRootConjugateAction V R).range, (gmsRootConjugateAction V R).range⁆ := by
  rw [_root_.commutator_def, Subgroup.map_commutator, MonoidHom.range_eq_map]

theorem ker_comp_commutator_subtype (V R : Subgroup D) :
    ((gmsRootConjugateAction V R).comp (commutator (normalizer (V : Set D))).subtype).ker =
      (gmsRootKernel V R).subgroupOf (commutator (normalizer (V : Set D))) := by
  rw [← MonoidHom.comap_ker, ker_gmsRootConjugateAction]
  rfl

theorem nonempty_commutator_quotient_equiv (V R : Subgroup D) :
    Nonempty (↥(commutator (normalizer (V : Set D))) ⧸
        (gmsRootKernel V R).subgroupOf (commutator (normalizer (V : Set D))) ≃*
      ↥⁅(gmsRootConjugateAction V R).range, (gmsRootConjugateAction V R).range⁆) := by
  have hrange : ((gmsRootConjugateAction V R).comp
      (commutator (normalizer (V : Set D))).subtype).range =
      ⁅(gmsRootConjugateAction V R).range, (gmsRootConjugateAction V R).range⁆ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, map_commutator_gmsRootConjugateAction]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq (ker_comp_commutator_subtype V R).symm).trans
    (QuotientGroup.quotientKerEquivRange _)).trans (MulEquiv.subgroupCongr hrange)⟩

end Kernel

end GMSDichotomy

open GMSDichotomy

variable {D : Type} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_normal_root_action_dichotomy_branch_completion [Finite D]
    (h : GMSNormalRootData J R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) :
    gmsPermStabilizer U R = ((normalizer (R : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D))).map (gmsRootConjugateAction (U ⊔ R) R) ∧
    IsCyclic (gmsSingerPermImage X U R) ∧ Nat.card (gmsSingerPermImage X U R) = 2 ^ n - 1 ∧
    gmsSingerPermImage X U R ≤ gmsPermStabilizer U R ∧
    ((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)).Normal ∧
    (∀ Q Z : gmsRootConjugates (U ⊔ R) R, (Q : Subgroup D) ≠ R → (Z : Subgroup D) ≠ R →
      ∃! t : gmsSingerPermImage X U R, (t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) ∧
    (∀ [((gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)).Normal],
      IsCyclic (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R))) ∧
    Nat.card (gmsPermStabilizer U R ⧸
      (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) ∣ n ∧
    (∀ A : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      A ≤ (gmsRootConjugateAction (U ⊔ R) R).range →
      (A.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal →
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : A,
        (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) →
      IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ n ∧
      A ⊔ gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      ((A ⊔ gmsSingerPermImage X U R).subgroupOf
        (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      Nat.card (A ⊔ gmsSingerPermImage X U R : Subgroup _) = 2 ^ n * (2 ^ n - 1) ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃ f ∈ A ⊔ gmsSingerPermImage X U R, f Q = Z) ∧
      ∀ f ∈ A ⊔ gmsSingerPermImage X U R, f ≠ 1 → ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
        f Q = Q → f Z = Z → Q = Z) ∧
    (∀ p : ℕ, p.Prime → p + 1 = 2 ^ n →
      ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = p →
      ∀ S : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      S ≤ (gmsRootConjugateAction (U ⊔ R) R).range →
      ∀ β : gmsRootConjugates (U ⊔ R) R ≃ ℙ K (Fin 2 → K),
      (∀ σ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R), σ ∈ S ↔
        ∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, ∀ Q, β (σ Q) = g • β Q) →
      (p - 1) / 2 ∣ n ∧ n = 3 ∧
      Nat.card (gmsPermStabilizer U R ⧸
        (gmsSingerPermImage X U R).subgroupOf (gmsPermStabilizer U R)) = 3 ∧
      (gmsRootConjugateAction (U ⊔ R) R).range = S ∧
      ⁅(gmsRootConjugateAction (U ⊔ R) R).range, (gmsRootConjugateAction (U ⊔ R) R).range⁆ =
        (gmsRootConjugateAction (U ⊔ R) R).range ∧
      CFSG.Blueprint.LieModel ↥⁅(gmsRootConjugateAction (U ⊔ R) R).range,
        (gmsRootConjugateAction (U ⊔ R) R).range⁆ .PSL 3 2 1 ∧
      CFSG.Blueprint.LieModel (↥(commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))) ⧸
        (gmsRootKernel (U ⊔ R) R).subgroupOf
          (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D)))) .PSL 3 2 1) ∧
    (gmsRootConjugateAction (U ⊔ R) R).ker = gmsRootKernel (U ⊔ R) R ∧
    (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))).map
        (gmsRootConjugateAction (U ⊔ R) R) =
      ⁅(gmsRootConjugateAction (U ⊔ R) R).range, (gmsRootConjugateAction (U ⊔ R) R).range⁆ ∧
    ((gmsRootConjugateAction (U ⊔ R) R).comp
        (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))).subtype).ker =
      (gmsRootKernel (U ⊔ R) R).subgroupOf
        (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))) ∧
    (U ⊔ R).normalizerMonoidHom.ker = (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ∧
    (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ≤ gmsRootKernel (U ⊔ R) R ∧
    (gmsConjAct X U).ker =
      (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) ∧
    ∀ g (hg : g ∈ X ⊓ normalizer (U : Set D)),
      gmsRootConjugateAction (U ⊔ R) R ⟨g, gms_NXU_le_L h hg⟩ = 1 ↔
        g ∈ X ⊓ centralizer (U : Set D) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hρker, hπker, -, -, -, hCK, hπY, -⟩ :=
    gms_normal_root_partition_and_two_transitivity h h3
  have hkerU := (SteinbergBT.gms_normal_root_singer_action_and_weak_closure h).2.2.2.2.2.2.2.2.1
  have hTN := gmsSingerPermImage_normal h (X := X)
  refine ⟨gmsPermStabilizer_eq_map, (isCyclic_gmsSingerPermImage h h3).1,
    (isCyclic_gmsSingerPermImage h h3).2, gmsSingerPermImage_le h, hTN, ?_,
    (isCyclic_quotient_and_card_dvd h h3).1, (isCyclic_quotient_and_card_dvd h h3).2,
    fun A hAN hAn hreg => affine_branch h h3 A hAN hAn hreg, ?_, hπker,
    map_commutator_gmsRootConjugateAction (U ⊔ R) R, ker_comp_commutator_subtype (U ⊔ R) R, hρker,
    hCK, hkerU, hπY⟩
  · intro Q Z hQ hZ
    obtain ⟨t, ht, htQ⟩ := exists_mem_gmsSingerPermImage_apply_eq h h3 hQ hZ
    refine ⟨⟨t, ht⟩, htQ, fun s hs => Subtype.ext ?_⟩
    have h1 : ((t⁻¹ * s : Equiv.Perm (gmsRootConjugates (U ⊔ R) R))) Q = Q := by
      rw [Equiv.Perm.mul_apply, hs, ← htQ, ← Equiv.Perm.mul_apply, inv_mul_cancel,
        Equiv.Perm.one_apply]
    have h2 := eq_one_of_mem_gmsSingerPermImage h h3 (mul_mem (inv_mem ht) s.2) hQ h1
    exact (inv_mul_eq_one.1 h2).symm
  · intro p hp hpn K _ _ hK S hSN β hβ
    obtain ⟨hdvd, hn3, hd3, hNS, hperf, ⟨e⟩⟩ := psl_branch h h3 p hp hpn K hK S hSN β hβ
    obtain ⟨e'⟩ := nonempty_commutator_quotient_equiv (U ⊔ R) R
    exact ⟨hdvd, hn3, hd3, hNS, hperf, lieModel_psl_three_two_of_mulEquiv e,
      lieModel_psl_three_two_of_mulEquiv (e'.trans e)⟩

end CFSG.LocalAnalysis.SteinbergBX
