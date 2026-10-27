module

public import CFSG.LieType.Chevalley.ParabolicRadicalSelfCentralizing
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2QPlusTorus
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRankOne

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical CFSG.RankThree.QuadraticSL2

section Scalars

variable {t : TwistTag} {L : Type} [Field L] {σ : L →+* L}

theorem orbitScalar_perm {X Y : Fin t.tag.rank → L → ModGL t.tag L}
    (hX : ∀ j c, twistHom t L σ (X j c) = X (t.perm j) (σ c))
    (hY : ∀ j c, twistHom t L σ (Y j c) = Y (t.perm j) (σ c))
    (hYinj : ∀ j, Function.Injective (Y j)) {g : ModGL t.tag L}
    (hg : twistHom t L σ g = g) {μ : Fin t.tag.rank → L}
    (hμ : ∀ j c, g * X j c * g⁻¹ = Y j (μ j * c)) (j : Fin t.tag.rank) :
    μ (t.perm j) = σ (μ j) := by
  have h := congrArg (twistHom t L σ) (hμ j 1)
  rw [map_mul, map_mul, map_inv, hg, hX, hY, map_one, hμ] at h
  simp only [mul_one] at h
  exact hYinj _ h

theorem orbitScalar_pow {X Y : Fin t.tag.rank → L → ModGL t.tag L}
    (hX : ∀ j c, twistHom t L σ (X j c) = X (t.perm j) (σ c))
    (hY : ∀ j c, twistHom t L σ (Y j c) = Y (t.perm j) (σ c))
    (hYinj : ∀ j, Function.Injective (Y j)) {g : ModGL t.tag L}
    (hg : twistHom t L σ g = g) {μ : Fin t.tag.rank → L}
    (hμ : ∀ j c, g * X j c * g⁻¹ = Y j (μ j * c)) (i : Fin t.tag.rank) (k : ℕ) :
    μ ((t.perm ^ k) i) = (σ ^ k) (μ i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, orbitScalar_perm hX hY hYinj hg hμ, ih, pow_succ']
    rfl

theorem conj_orbit_prod {X Y : Fin t.tag.rank → L → ModGL t.tag L} {g : ModGL t.tag L}
    {μ : Fin t.tag.rank → L} (hμ : ∀ j c, g * X j c * g⁻¹ = Y j (μ j * c)) (i : Fin t.tag.rank)
    (hpow : ∀ k, μ ((t.perm ^ k) i) = (σ ^ k) (μ i)) (n : ℕ) (c : L) :
    g * ((List.range n).map fun k => X ((t.perm ^ k) i) ((σ ^ k) c)).prod * g⁻¹ =
      ((List.range n).map fun k => Y ((t.perm ^ k) i) ((σ ^ k) (μ i * c))).prod := by
  rw [← MulAut.conj_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, MulAut.conj_apply, hμ, hpow, map_mul]

theorem mem_orbitField_of_orbitScalar {μ : Fin t.tag.rank → L} (b : Fin t.foldedTag.rank)
    (hpow : ∀ k, μ ((t.perm ^ k) (t.orbitMin b)) = (σ ^ k) (μ (t.orbitMin b))) :
    μ (t.orbitMin b) ∈ orbitField t L σ b := by
  rw [mem_orbitField, ← hpow, t.perm_pow_card_orbitMin]

theorem twistHom_xUnit'
    (j : Fin t.tag.rank) (c : L) :
    twistHom t L σ (xUnit t.tag L j c) = xUnit t.tag L (t.perm j) (σ c) :=
  twistHom_xUnit t L σ j c

theorem twistHom_yUnit'
    (j : Fin t.tag.rank) (c : L) :
    twistHom t L σ (yUnit t.tag L j c) = yUnit t.tag L (t.perm j) (σ c) :=
  twistHom_yUnit t L σ j c

theorem xUnit_injective' (j : Fin t.tag.rank) : Function.Injective (xUnit t.tag L j) :=
  fun c c' h => by
    rw [← pinnedX_single, ← pinnedX_single] at h
    exact pinnedX_injective t.tag L _ h

theorem yUnit_injective' (j : Fin t.tag.rank) : Function.Injective (yUnit t.tag L j) :=
  fun c c' h => by
    rw [← pinnedX_neg_single, ← pinnedX_neg_single] at h
    exact pinnedX_injective t.tag L _ h

end Scalars

section OrbitWords

variable {t : TwistTag} {L : Type} [Field L] {σ : L →+* L}

theorem exists_conj_orbitX_eq_orbitY
    {z : ModGL t.tag L} (hz : z ∈ monomialSubgroup t.tag L)
    (hw : ∀ v : Fin t.tag.rank → ℤ, weylQuotientHom t.tag L ⟨z, hz⟩ • v = -v)
    (hzΓ : twistHom t L σ z = z) (b : Fin t.foldedTag.rank) :
    ∃ μ μ' : (orbitField t L σ b)ˣ, (∀ c, z * (orbitX t L σ b c : ModGL t.tag L) * z⁻¹ =
        orbitY t L σ b (μ * c)) ∧
      ∀ c, z * (orbitY t L σ b c : ModGL t.tag L) * z⁻¹ = orbitX t L σ b (μ' * c) := by
  have hx : ∀ j, ∃ m : Lˣ, ∀ c, z * xUnit t.tag L j c * z⁻¹ = yUnit t.tag L j (m * c) := by
    intro j
    obtain ⟨m, hm⟩ := conj_pinnedX_of_smul_eq_neg hz hw (isRoot_single t.tag j)
    exact ⟨m, fun c => by rw [← pinnedX_single, hm, pinnedX_neg_single]⟩
  have hy : ∀ j, ∃ m : Lˣ, ∀ c, z * yUnit t.tag L j c * z⁻¹ = xUnit t.tag L j (m * c) := by
    intro j
    obtain ⟨m, hm⟩ := conj_pinnedX_of_smul_eq_neg hz hw (isRoot_neg_single t.tag j)
    exact ⟨m, fun c => by rw [← pinnedX_neg_single, hm, neg_neg, pinnedX_single]⟩
  choose m hm using hx
  choose m' hm' using hy
  have hμ : ∀ j c, z * xUnit t.tag L j c * z⁻¹ = yUnit t.tag L j ((fun j => (m j : L)) j * c) :=
    hm
  have hμ' : ∀ j c, z * yUnit t.tag L j c * z⁻¹ = xUnit t.tag L j ((fun j => (m' j : L)) j * c) :=
    hm'
  set i := t.orbitMin b
  have hpow := orbitScalar_pow twistHom_xUnit' twistHom_yUnit' yUnit_injective' hzΓ hμ i
  have hpow' := orbitScalar_pow twistHom_yUnit' twistHom_xUnit' xUnit_injective' hzΓ hμ' i
  have hmem := mem_orbitField_of_orbitScalar (μ := fun j => (m j : L)) b hpow
  have hmem' := mem_orbitField_of_orbitScalar (μ := fun j => (m' j : L)) b hpow'
  refine ⟨Units.mk0 ⟨m i, hmem⟩ fun h => (m i).ne_zero (congrArg Subtype.val h),
    Units.mk0 ⟨m' i, hmem'⟩ fun h => (m' i).ne_zero (congrArg Subtype.val h), fun c => ?_,
    fun c => ?_⟩
  · rw [coe_orbitX, coe_orbitY, conj_orbit_prod hμ i hpow]
    rfl
  · rw [coe_orbitY, coe_orbitX, conj_orbit_prod hμ' i hpow']
    rfl

theorem exists_conj_orbitX_of_mem_graphFixedTorus
    {h : ModGL t.tag L}
    (hh : h ∈ graphFixedTorus t L σ) (b : Fin t.foldedTag.rank) :
    ∃ l : (orbitField t L σ b)ˣ, (∀ c, h * (orbitX t L σ b c : ModGL t.tag L) * h⁻¹ =
        orbitX t L σ b (l * c)) ∧
      ∀ c, h * (orbitY t L σ b c : ModGL t.tag L) * h⁻¹ = orbitY t L σ b (l⁻¹ * c) := by
  obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
  have hhF : twistHom t L σ h = h := ((mem_twistedFixedGroup_iff_twistHom t L σ).1 hhΓ).2
  obtain ⟨d, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  have hμ : ∀ j c, rootDiagUnit t.tag d * xUnit t.tag L j c * (rootDiagUnit t.tag d)⁻¹ =
      xUnit t.tag L j ((fun j => (d j : L)) j * c) := fun j c => by
    rw [← pinnedX_single, rootDiagUnit_conj_pinnedX d (isRoot_single t.tag j), rootChar_single,
      pinnedX_single]
  have hν : ∀ j c, rootDiagUnit t.tag d * yUnit t.tag L j c * (rootDiagUnit t.tag d)⁻¹ =
      yUnit t.tag L j ((fun j => (((d j)⁻¹ : Lˣ) : L)) j * c) := fun j c => by
    rw [← pinnedX_neg_single, rootDiagUnit_conj_pinnedX d (isRoot_neg_single t.tag j),
      rootChar_neg_eq_inv, rootChar_single, pinnedX_neg_single]
  set i := t.orbitMin b
  have hpow := orbitScalar_pow twistHom_xUnit' twistHom_xUnit' xUnit_injective' hhF hμ i
  have hpow' := orbitScalar_pow twistHom_yUnit' twistHom_yUnit' yUnit_injective' hhF hν i
  have hmem := mem_orbitField_of_orbitScalar (μ := fun j => (d j : L)) b hpow
  refine ⟨Units.mk0 ⟨d i, hmem⟩ fun h => (d i).ne_zero (congrArg Subtype.val h), fun c => ?_,
    fun c => ?_⟩
  · rw [coe_orbitX, coe_orbitX, conj_orbit_prod hμ i hpow]
    rfl
  · rw [coe_orbitY, coe_orbitY, conj_orbit_prod hν i hpow']
    refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
    congr 2
    simp only [Units.val_inv_eq_inv_val, Subfield.coe_mul, Subfield.coe_inv, Units.val_mk0]

end OrbitWords

section Restrict

variable {t : TwistTag} {L : Type} [Field L] {σ : L →+* L}

theorem ringHom_pow_apply_comm_ringEquiv {τ : L ≃+* L} (hτ : ∀ c, τ (σ c) = σ (τ c)) (n : ℕ)
    (c : L) : τ ((σ ^ n) c) = (σ ^ n) (τ c) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', RingHom.coe_mul, Function.comp_apply, Function.comp_apply, hτ, ih]

theorem map_mem_orbitField {τ : L ≃+* L} (hτ : ∀ c, τ (σ c) = σ (τ c))
    {b : Fin t.foldedTag.rank} {c : L} (hc : c ∈ orbitField t L σ b) :
    τ c ∈ orbitField t L σ b := by
  rw [mem_orbitField] at hc ⊢
  rw [← ringHom_pow_apply_comm_ringEquiv hτ, hc]

theorem symm_comm_of_comm {τ : L ≃+* L} (hτ : ∀ c, τ (σ c) = σ (τ c)) (c : L) :
    τ.symm (σ c) = σ (τ.symm c) := by
  rw [RingEquiv.symm_apply_eq, hτ, RingEquiv.apply_symm_apply]

@[expose] def orbitFieldRestrict (τ : L ≃+* L) (hτ : ∀ c, τ (σ c) = σ (τ c))
    (b : Fin t.foldedTag.rank) : orbitField t L σ b ≃+* orbitField t L σ b where
  toFun c := ⟨τ (c : L), map_mem_orbitField hτ c.2⟩
  invFun c := ⟨τ.symm (c : L), map_mem_orbitField (symm_comm_of_comm hτ) c.2⟩
  left_inv c := Subtype.ext (τ.symm_apply_apply (c : L))
  right_inv c := Subtype.ext (τ.apply_symm_apply (c : L))
  map_mul' c d := Subtype.ext (map_mul τ (c : L) d)
  map_add' c d := Subtype.ext (map_add τ (c : L) d)

theorem coe_orbitFieldRestrict (τ : L ≃+* L) (hτ : ∀ c, τ (σ c) = σ (τ c))
    (b : Fin t.foldedTag.rank) (c : orbitField t L σ b) :
    (orbitFieldRestrict τ hτ b c : L) = τ c :=
  rfl

theorem units_map_entrywiseHom_orbitX
    (τ : L ≃+* L) (hτ : ∀ c, τ (σ c) = σ (τ c))
    (b : Fin t.foldedTag.rank) (c : orbitField t L σ b) :
    Units.map (entrywiseHom τ.toRingHom) (orbitX t L σ b c : ModGL t.tag L) =
      orbitX t L σ b (orbitFieldRestrict τ hτ b c) := by
  rw [coe_orbitX, coe_orbitX, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, units_map_entrywiseHom_xUnit, coe_orbitFieldRestrict]
  exact congrArg _ (ringHom_pow_apply_comm_ringEquiv hτ k c)

theorem units_map_entrywiseHom_orbitY
    (τ : L ≃+* L) (hτ : ∀ c, τ (σ c) = σ (τ c))
    (b : Fin t.foldedTag.rank) (c : orbitField t L σ b) :
    Units.map (entrywiseHom τ.toRingHom) (orbitY t L σ b c : ModGL t.tag L) =
      orbitY t L σ b (orbitFieldRestrict τ hτ b c) := by
  rw [coe_orbitY, coe_orbitY, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  rw [Function.comp_apply, units_map_entrywiseHom_yUnit, coe_orbitFieldRestrict]
  exact congrArg _ (ringHom_pow_apply_comm_ringEquiv hτ k c)

end Restrict

section Induced

variable {t : TwistTag} {L : Type} [Field L] {σ : L →+* L}

theorem conj_orbitConjRankOneHom_eq
    {w : WeylGroup t.tag} {b : Fin t.foldedTag.rank}
    (g : ModGL t.tag L) (A : SL2 (orbitField t L σ b)) :
    g * orbitConjRankOneHom t L σ w b A * g⁻¹ =
      canonicalRep (coxeterSystem t.tag) L w *
        ((canonicalRep (coxeterSystem t.tag) L w)⁻¹ * g * canonicalRep (coxeterSystem t.tag) L w *
          orbitRankOneHom t L σ b A *
          ((canonicalRep (coxeterSystem t.tag) L w)⁻¹ * g *
            canonicalRep (coxeterSystem t.tag) L w)⁻¹) *
        (canonicalRep (coxeterSystem t.tag) L w)⁻¹ := by
  rw [orbitConjRankOneHom_apply]
  group

theorem conj_canonicalRep_weyl_neg
    {z : ModGL t.tag L} (hz : z ∈ monomialSubgroup t.tag L)
    (hw : ∀ v : Fin t.tag.rank → ℤ, weylQuotientHom t.tag L ⟨z, hz⟩ • v = -v)
    (w : WeylGroup t.tag) :
    ∃ hz' : (canonicalRep (coxeterSystem t.tag) L w)⁻¹ * z * canonicalRep (coxeterSystem t.tag) L w
        ∈ monomialSubgroup t.tag L,
      ∀ v : Fin t.tag.rank → ℤ, weylQuotientHom t.tag L ⟨_, hz'⟩ • v = -v := by
  have hn := canonicalRep_mem_monomialSubgroup L w
  have hz' := mul_mem (mul_mem (inv_mem hn) hz) hn
  refine ⟨hz', fun v => ?_⟩
  have hmaps := ((mapsRootLines_canonicalRep (R := L) w).inv.mul
    (mapsRootLines_weylQuotientHom ⟨z, hz⟩)).mul (mapsRootLines_canonicalRep (R := L) w)
  rw [weylQuotientHom_eq hmaps, mul_smul, mul_smul, hw, smul_neg, inv_smul_smul]

theorem units_map_entrywiseHom_orbitConjRankOneHom_uSL
    {τ : L ≃+* L}
    (hτ : ∀ c, τ (σ c) = σ (τ c)) (w : WeylGroup t.tag) (b : Fin t.foldedTag.rank)
    (c : orbitField t L σ b) :
    Units.map (entrywiseHom τ.toRingHom) (orbitConjRankOneHom t L σ w b (uSL c)) =
      orbitConjRankOneHom t L σ w b (uSL (orbitFieldRestrict τ hτ b c)) := by
  rw [orbitConjRankOneHom_apply, map_mul, map_mul, map_inv, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_canonicalRep, orbitRankOneHom_uSL, units_map_entrywiseHom_orbitX τ hτ,
    ← orbitRankOneHom_uSL, ← orbitConjRankOneHom_apply]

theorem units_map_entrywiseHom_orbitConjRankOneHom_vSL
    {τ : L ≃+* L}
    (hτ : ∀ c, τ (σ c) = σ (τ c)) (w : WeylGroup t.tag) (b : Fin t.foldedTag.rank)
    (c : orbitField t L σ b) :
    Units.map (entrywiseHom τ.toRingHom) (orbitConjRankOneHom t L σ w b (vSL c)) =
      orbitConjRankOneHom t L σ w b (vSL (orbitFieldRestrict τ hτ b c)) := by
  rw [orbitConjRankOneHom_apply, map_mul, map_mul, map_inv, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_canonicalRep, orbitRankOneHom_vSL, units_map_entrywiseHom_orbitY τ hτ,
    ← orbitRankOneHom_vSL, ← orbitConjRankOneHom_apply]

theorem exists_twistedEntrywise_orbitConjRankOneHom
    {τ : L ≃+* L}
    (hτ : ∀ c, τ (σ c) = σ (τ c)) {z : ModGL t.tag L} (hz : z ∈ monomialSubgroup t.tag L)
    (hw : ∀ v : Fin t.tag.rank → ℤ, weylQuotientHom t.tag L ⟨z, hz⟩ • v = -v)
    (hzΓ : z ∈ twistedFixedGroup t L σ) {w : WeylGroup t.tag}
    (hwρ : w ∈ relWeylTwist t) (b : Fin t.foldedTag.rank) :
    ∃ μ μ' : (orbitField t L σ b)ˣ,
      (∀ c, twistedEntrywise z τ.toRingHom (orbitConjRankOneHom t L σ w b (uSL c)) =
        orbitConjRankOneHom t L σ w b (vSL (μ * orbitFieldRestrict τ hτ b c))) ∧
      ∀ c, twistedEntrywise z τ.toRingHom (orbitConjRankOneHom t L σ w b (vSL c)) =
        orbitConjRankOneHom t L σ w b (uSL (μ' * orbitFieldRestrict τ hτ b c)) := by
  have hnΓ : canonicalRep (coxeterSystem t.tag) L w ∈ twistedFixedGroup t L σ :=
    canonicalRep_mem_twistedFixedGroup t L σ ((mem_relWeylTwist t).1 hwρ)
  have hz'Γ : (canonicalRep (coxeterSystem t.tag) L w)⁻¹ * z *
      canonicalRep (coxeterSystem t.tag) L w ∈ twistedFixedGroup t L σ :=
    mul_mem (mul_mem (inv_mem hnΓ) hzΓ) hnΓ
  obtain ⟨hz', hw'⟩ := conj_canonicalRep_weyl_neg hz hw w
  obtain ⟨μ, μ', hμ, hμ'⟩ := exists_conj_orbitX_eq_orbitY hz' hw'
    ((mem_twistedFixedGroup_iff_twistHom t L σ).1 hz'Γ).2 b
  refine ⟨μ, μ', fun c => ?_, fun c => ?_⟩
  · rw [twistedEntrywise_apply, units_map_entrywiseHom_orbitConjRankOneHom_uSL hτ,
      conj_orbitConjRankOneHom_eq, orbitRankOneHom_uSL, hμ, ← orbitRankOneHom_vSL,
      ← orbitConjRankOneHom_apply]
  · rw [twistedEntrywise_apply, units_map_entrywiseHom_orbitConjRankOneHom_vSL hτ,
      conj_orbitConjRankOneHom_eq, orbitRankOneHom_vSL, hμ', ← orbitRankOneHom_uSL,
      ← orbitConjRankOneHom_apply]

theorem exists_semilinearConj_orbitConjRankOneHom
    {τ : L ≃+* L}
    (hτ : ∀ c, τ (σ c) = σ (τ c)) {z : ModGL t.tag L} (hz : z ∈ monomialSubgroup t.tag L)
    (hw : ∀ v : Fin t.tag.rank → ℤ, weylQuotientHom t.tag L ⟨z, hz⟩ • v = -v)
    (hzΓ : z ∈ twistedFixedGroup t L σ) {w : WeylGroup t.tag}
    (hwρ : w ∈ relWeylTwist t) (b : Fin t.foldedTag.rank)
    (hinj : Function.Injective (orbitConjRankOneHom t L σ w b)) :
    ∃ M : GL (Fin 2) (orbitField t L σ b), ∀ A,
      orbitConjRankOneHom t L σ w b (semilinearConj M (orbitFieldRestrict τ hτ b) A) =
        twistedEntrywise z τ.toRingHom (orbitConjRankOneHom t L σ w b A) := by
  obtain ⟨a, a', hu, hl⟩ := exists_twistedEntrywise_orbitConjRankOneHom hτ hz hw hzΓ hwρ b
  set Φ := orbitConjRankOneHom t L σ w b
  have hmem : ∀ A, twistedEntrywise z τ.toRingHom (Φ A) ∈ Φ.range := by
    have hle : (⊤ : Subgroup (SL2 (orbitField t L σ b))) ≤ Φ.range.comap
        ((twistedEntrywise z τ.toRingHom).comp Φ) := by
      rw [← sl2_closure_upper_lower, Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨vSL (a * orbitFieldRestrict τ hτ b c), (hu c).symm⟩
      · exact ⟨uSL (a' * orbitFieldRestrict τ hτ b c), (hl c).symm⟩
    exact fun A => hle (Subgroup.mem_top A)
  let T : SL2 (orbitField t L σ b) →* SL2 (orbitField t L σ b) :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp
      (((twistedEntrywise z τ.toRingHom).comp Φ).codRestrict _ hmem)
  have hT : ∀ A, Φ (T A) = twistedEntrywise z τ.toRingHom (Φ A) := fun A => by
    rw [← MonoidHom.ofInjective_apply hinj]
    change ((MonoidHom.ofInjective hinj ((MonoidHom.ofInjective hinj).symm _)) :
      ModGL t.tag L) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hTu : ∀ c, T (sl2Upper (orbitField t L σ b) c) =
      sl2Lower (orbitField t L σ b) (a * orbitFieldRestrict τ hτ b c) := fun c => hinj (by
    rw [hT]
    exact hu c)
  have hTl : ∀ c, T (sl2Lower (orbitField t L σ b) c) =
      sl2Upper (orbitField t L σ b) (a' * orbitFieldRestrict τ hτ b c) := fun c => hinj (by
    rw [hT]
    exact hl c)
  obtain ⟨-, M, -, hM⟩ :=
    sl2_semilinear_exchanged_root_compatibility (orbitFieldRestrict τ hτ b) a a' T hTu hTl
  refine ⟨M, fun A => ?_⟩
  have hTA : T A = semilinearConj M (orbitFieldRestrict τ hτ b) A := Subtype.ext (by
    rw [hM A]
    rfl)
  rw [← hTA, hT]

theorem exists_conj_orbitConjRankOneHom_eq_conjSL
    {h : ModGL t.tag L}
    (hh : h ∈ graphFixedTorus t L σ) {w : WeylGroup t.tag} (hwρ : w ∈ relWeylTwist t)
    (b : Fin t.foldedTag.rank) :
    ∃ l : (orbitField t L σ b)ˣ, ∀ A, h * orbitConjRankOneHom t L σ w b A * h⁻¹ =
      orbitConjRankOneHom t L σ w b (conjSL (diagUnitOne l) A) := by
  set n := canonicalRep (coxeterSystem t.tag) L w
  have hnΓ : n ∈ twistedFixedGroup t L σ :=
    canonicalRep_mem_twistedFixedGroup t L σ ((mem_relWeylTwist t).1 hwρ)
  have hh' : n⁻¹ * h * n ∈ graphFixedTorus t L σ := by
    obtain ⟨hhT, hhΓ⟩ := Subgroup.mem_inf.1 hh
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (inv_mem hnΓ) hhΓ) hnΓ⟩
    have hN := inv_mem ((canonical_weyl_root_transport t.tag L).2.2 w)
    have := (Subgroup.mem_normalizer_iff.1 hN h).1 hhT
    rwa [inv_inv] at this
  obtain ⟨l, hlx, hly⟩ := exists_conj_orbitX_of_mem_graphFixedTorus hh' b
  refine ⟨l, fun A => ?_⟩
  set Φ := orbitConjRankOneHom t L σ w b
  have hgen : ((MulAut.conj h).toMonoidHom.comp Φ) =
      Φ.comp (conjSL (diagUnitOne l)) :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [conj_orbitConjRankOneHom_eq, conjSL_sl2Upper]
        change n * (n⁻¹ * h * n * orbitRankOneHom t L σ b (uSL c) * (n⁻¹ * h * n)⁻¹) * n⁻¹ =
          Φ (uSL (l * c))
        rw [orbitRankOneHom_uSL, hlx, orbitConjRankOneHom_apply, orbitRankOneHom_uSL]
      · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [conj_orbitConjRankOneHom_eq, conjSL_sl2Lower]
        change n * (n⁻¹ * h * n * orbitRankOneHom t L σ b (vSL c) * (n⁻¹ * h * n)⁻¹) * n⁻¹ =
          Φ (vSL ((l⁻¹ : (orbitField t L σ b)ˣ) * c))
        rw [orbitRankOneHom_vSL, hly, orbitConjRankOneHom_apply, orbitRankOneHom_vSL]
  exact congrArg (fun f => f A) hgen

end Induced

end CFSG.RankThree.Chevalley
