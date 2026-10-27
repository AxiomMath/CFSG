
module


public import CFSG.Monster.B.TwoA.Par3.Coset
public import CFSG.Monster.B.TwoA.Par2.Class

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Par3

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Par2

open scoped IsMulCommutative

theorem orderOf_of_mem_cE3
    {d : Dfull} (hd : d ∈ cE3) : orderOf d = 2 := by
  rw [← K3_class_eq] at hd
  obtain ⟨k, -, rfl⟩ := hd
  rw [show k * cQ * k⁻¹ = MulAut.conj k cQ from rfl, MulEquiv.orderOf_eq, orderOf_cQ]

@[expose, instance_reducible] def kAction :
    MulAction K3 cE3 where
  smul k d := ⟨(k : Dfull) * d * (k : Dfull)⁻¹, conj_mem_cE3 k.2 d.2⟩
  one_smul d := Subtype.ext (by
    change ((1 : K3) : Dfull) * d * ((1 : K3) : Dfull)⁻¹ = d
    simp)
  mul_smul g h d := Subtype.ext (by
    change ((g * h : K3) : Dfull) * d * ((g * h : K3) : Dfull)⁻¹ =
      (g : Dfull) * ((h : Dfull) * d * (h : Dfull)⁻¹) * (g : Dfull)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

@[expose, instance_reducible] def rAction :
    MulAction R3 cE3 where
  smul r d := ⟨(r : Dfull) * d * (r : Dfull)⁻¹, conj_mem_cE3 (R3_le_K3 r.2) d.2⟩
  one_smul d := Subtype.ext (by
    change ((1 : R3) : Dfull) * d * ((1 : R3) : Dfull)⁻¹ = d
    simp)
  mul_smul g h d := Subtype.ext (by
    change ((g * h : R3) : Dfull) * d * ((g * h : R3) : Dfull)⁻¹ =
      (g : Dfull) * ((h : Dfull) * d * (h : Dfull)⁻¹) * (g : Dfull)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group)

theorem cE3_eq_range : cE3 = Set.range fun e : E3 => cQ * e := by
  ext d
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, e.2, rfl⟩

theorem natCard_cE3 :
    Nat.card cE3 = 8 := by
  rw [cE3_eq_range, Nat.card_range_of_injective (fun e e' h => Subtype.ext (mul_left_cancel h)),
    natCard_E3]

theorem ncard_cE3 :
    cE3.ncard = 8 := by
  rw [← Nat.card_coe_set_eq, natCard_cE3]

attribute [local instance] kAction rAction

theorem stabilizer_iff (n : Dfull) : n * cQ * n⁻¹ = cQ ↔ n ∈ Subgroup.centralizer {cQ} := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem pCore_quotient_eq_bot {G : Type*} [Group G] {p : ℕ} (N : Subgroup G) [N.Normal]
    (hN : N = CFSG.pCore p G) : CFSG.pCore p (G ⧸ N) = ⊥ := by
  have hP : IsPGroup p N := by
    rw [hN]
    exact CFSG.pCore_isPGroup
  have hM : (CFSG.pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) ≤ CFSG.pCore p G :=
    le_pCore_of_normal (CFSG.pCore_normal.comap _)
      (IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup _
        (by rw [QuotientGroup.ker_mk']; exact hP))
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_bot]
  have hg : g ∈ N := by
    rw [hN]
    exact hM hx
  exact (QuotientGroup.eq_one_iff g).2 hg

@[expose] def sigP3 :
    P3 →* K3 ⧸ R3.subgroupOf K3 :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion P3_le_K3)

theorem R3_inf_le_P3 :

    R3 ⊓ Subgroup.centralizer {cQ} ≤ P3 := inf_le_inf_right _ R3_le_K3

theorem ker_sigP3 :

    sigP3.ker = (R3 ⊓ Subgroup.centralizer {cQ}).subgroupOf P3 := by
  ext p
  rw [MonoidHom.mem_ker, sigP3, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h, (Subgroup.mem_inf.1 p.2).2⟩, fun h => h.1⟩

@[expose] def bE :
    Additive E3 ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  haveI : Module.Finite (ZMod 2) (Additive E3) := Module.Finite.of_finite
  (Module.finBasisOfFinrankEq (ZMod 2) (Additive E3)
    (finrank_additive_of_card natCard_E3_pow)).equivFun

@[expose] def eV
    (v : Fin 3 → ZMod 2) : Dfull := ((Additive.toMul (bE.symm v) : E3) : Dfull)

theorem eV_mem
    (v : Fin 3 → ZMod 2) : eV v ∈ E3 := (Additive.toMul (bE.symm v)).2

theorem eV_add
    (v w : Fin 3 → ZMod 2) : eV (v + w) = eV v * eV w := by
  rw [eV, map_add, toMul_add]
  rfl

theorem eV_bE
    (x : E3) : eV (bE (Additive.ofMul x)) = x := by
  rw [eV, LinearEquiv.symm_apply_apply, toMul_ofMul]

theorem eV_injective :
    Function.Injective eV := fun _ _ h =>
  bE.symm.injective (Additive.toMul.injective (Subtype.ext h))

theorem cQ_mul_mem
    {d : Dfull} (hd : ∃ e ∈ E3, cQ * e = d) : cQ * d ∈ E3 := by
  obtain ⟨e, he, rfl⟩ := hd
  rw [← mul_assoc, cQ_mul_self', one_mul]
  exact he

@[expose] def iotaC :
    (Fin 3 → ZMod 2) ≃ {d : Dfull // ∃ e ∈ E3, cQ * e = d} where
  toFun v := ⟨cQ * eV v, eV v, eV_mem v, rfl⟩
  invFun d := bE (Additive.ofMul ⟨cQ * d, cQ_mul_mem d.2⟩)
  left_inv v := by
    have e : (⟨cQ * (cQ * eV v), cQ_mul_mem ⟨eV v, eV_mem v, rfl⟩⟩ : E3) =
        Additive.toMul (bE.symm v) := Subtype.ext (by
      change cQ * (cQ * eV v) = eV v
      rw [← mul_assoc, cQ_mul_self', one_mul])
    change bE (Additive.ofMul ⟨cQ * (cQ * eV v), _⟩) = v
    rw [e, ofMul_toMul, LinearEquiv.apply_symm_apply]
  right_inv d := Subtype.ext (by
    change cQ * eV (bE (Additive.ofMul ⟨cQ * d, cQ_mul_mem d.2⟩)) = d
    rw [eV_bE]
    change cQ * (cQ * (d : Dfull)) = d
    rw [← mul_assoc, cQ_mul_self', one_mul])

theorem coe_iotaC
    (v : Fin 3 → ZMod 2) : (iotaC v : Dfull) = cQ * eV v := rfl

@[expose] def linK
    (k : K3) : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
  bE.symm.trans ((mulAutEquivLinear E3 (conjE E3 k)).trans bE)

theorem eV_linK
    (k : K3) (v : Fin 3 → ZMod 2) :
    eV (linK k v) = (k : Dfull) * eV v * (k : Dfull)⁻¹ := by
  rw [eV, linK, LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact coe_conjE E3 k (Additive.toMul (bE.symm v))

attribute [local instance] kAction rAction

theorem index_P3 :
    (P3.subgroupOf K3).index = 8 := by
  have : MulAction.IsPretransitive K3 cE3 := ⟨fun x y => by
    obtain ⟨r, hr, hxy⟩ := cE3_R3_transitive x.2 y.2
    exact ⟨⟨r, R3_le_K3 hr⟩, Subtype.ext hxy⟩⟩
  have hs : MulAction.stabilizer K3 (⟨cQ, cQ_mem_cE3⟩ : cE3) = P3.subgroupOf K3 := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, P3, Subgroup.mem_inf,
      ← Subtype.coe_inj]
    change (k : Dfull) * cQ * (k : Dfull)⁻¹ = cQ ↔ _
    rw [stabilizer_iff]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  rw [← hs, MulAction.index_stabilizer_of_transitive, natCard_cE3]

theorem natCard_P3 :
    Nat.card P3 = 86586540687360 := by
  have h := (P3.subgroupOf K3).card_mul_index
  rw [index_P3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe P3_le_K3).toEquiv, natCard_K3] at h
  omega

theorem index_R3c :

    ((R3 ⊓ Subgroup.centralizer {cQ}).subgroupOf R3).index = 8 := by
  have : MulAction.IsPretransitive R3 cE3 := ⟨fun x y => by
    obtain ⟨r, hr, hxy⟩ := cE3_R3_transitive x.2 y.2
    exact ⟨⟨r, hr⟩, Subtype.ext hxy⟩⟩
  have hs : MulAction.stabilizer R3 (⟨cQ, cQ_mem_cE3⟩ : cE3) =
      (R3 ⊓ Subgroup.centralizer {cQ}).subgroupOf R3 := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      ← Subtype.coe_inj]
    change (k : Dfull) * cQ * (k : Dfull)⁻¹ = cQ ↔ _
    rw [stabilizer_iff]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  rw [← hs, MulAction.index_stabilizer_of_transitive, natCard_cE3]

theorem natCard_R3c :
    Nat.card ↥(R3 ⊓ Subgroup.centralizer {cQ}) = 2 ^ 32 := by
  have h := ((R3 ⊓ Subgroup.centralizer {cQ}).subgroupOf R3).card_mul_index
  rw [index_R3c, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    natCard_R3] at h
  omega

theorem R3_subgroupOf_eq_pCore :
    R3.subgroupOf K3 = CFSG.pCore 2 K3 := by
  rw [R3_subgroupOf_eq, pCore_K3_eq]

theorem sigP3_surjective :
    Function.Surjective sigP3 := by
  intro x
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨r, hr, hrc⟩ := cE3_R3_transitive (conj_cQ_mem_cE3 k.2) cQ_mem_cE3
  have hm : r * k ∈ P3 := by
    refine ⟨K3.mul_mem (R3_le_K3 hr) k.2, (stabilizer_iff _).1 ?_⟩
    calc r * (k : Dfull) * cQ * (r * k)⁻¹ = r * ((k : Dfull) * cQ * (k : Dfull)⁻¹) * r⁻¹ := by
          group
      _ = cQ := hrc
  refine ⟨⟨_, hm⟩, QuotientGroup.eq.2 ?_⟩
  rw [Subgroup.mem_subgroupOf]
  have h := conj_mem_R3 (K3.inv_mem k.2) (R3.inv_mem hr)
  rw [inv_inv] at h
  simpa [mul_assoc] using h

theorem natCard_ker_sigP3 :
    Nat.card sigP3.ker = 2 ^ 32 := by
  rw [ker_sigP3, Nat.card_congr (Subgroup.subgroupOfEquivOfLe R3_inf_le_P3).toEquiv, natCard_R3c]

theorem ker_sigP3_eq_pCore :
    sigP3.ker = CFSG.pCore 2 P3 :=
  ker_eq_pCore_of_surjective sigP3_surjective (IsPGroup.of_card natCard_ker_sigP3)
    (pCore_quotient_eq_bot _ R3_subgroupOf_eq_pCore)

theorem map_pCore_P3 :

    (CFSG.pCore 2 P3).map P3.subtype = R3 ⊓ Subgroup.centralizer {cQ} := by
  rw [← ker_sigP3_eq_pCore, ker_sigP3, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 R3_inf_le_P3]

@[expose] noncomputable def p3QuotK3 :
    P3 ⧸ CFSG.pCore 2 P3 ≃* K3 ⧸ R3.subgroupOf K3 :=
  (QuotientGroup.quotientMulEquivOfEq ker_sigP3_eq_pCore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective sigP3 sigP3_surjective)

theorem exists_p3QuotEquiv :
    Nonempty (P3 ⧸ CFSG.pCore 2 P3 ≃* GL (Fin 3) (ZMod 2) × Equiv.Perm (Fin 5)) := by
  obtain ⟨e, -⟩ := exists_k3QuotProd
  exact ⟨p3QuotK3.trans e⟩

@[expose] def trK
    (k : K3) : Fin 3 → ZMod 2 :=
  bE (Additive.ofMul ⟨cQ * ((k : Dfull) * cQ * (k : Dfull)⁻¹), cQ_mul_mem (conj_cQ_mem_cE3 k.2)⟩)

theorem eV_trK
    (k : K3) : eV (trK k) = cQ * ((k : Dfull) * cQ * (k : Dfull)⁻¹) := by
  rw [trK, eV_bE]

@[expose] def alphaFun
    (k : K3) : (Fin 3 → ZMod 2) ≃ᵃ[ZMod 2] (Fin 3 → ZMod 2) :=
  (linK k).toAffineEquiv.trans (AffineEquiv.constVAdd (ZMod 2) (Fin 3 → ZMod 2) (trK k))

theorem alphaFun_apply
    (k : K3) (v : Fin 3 → ZMod 2) : alphaFun k v = trK k + linK k v := rfl

theorem conj_iotaC_alphaFun
    (k : K3) (v : Fin 3 → ZMod 2) :
    (k : Dfull) * iotaC v * (k : Dfull)⁻¹ = iotaC (alphaFun k v) := by
  rw [coe_iotaC, coe_iotaC, alphaFun_apply, eV_add, eV_trK, eV_linK]
  calc (k : Dfull) * (cQ * eV v) * (k : Dfull)⁻¹ =
      ((k : Dfull) * cQ * (k : Dfull)⁻¹) * ((k : Dfull) * eV v * (k : Dfull)⁻¹) := by group
    _ = cQ * (cQ * ((k : Dfull) * cQ * (k : Dfull)⁻¹) * ((k : Dfull) * eV v * (k : Dfull)⁻¹)) := by
      rw [← mul_assoc cQ (cQ * _), ← mul_assoc cQ cQ, cQ_mul_self', one_mul]

@[expose] def alphaK :
    K3 →* ((Fin 3 → ZMod 2) ≃ᵃ[ZMod 2] (Fin 3 → ZMod 2)) where
  toFun := alphaFun
  map_one' := AffineEquiv.ext fun v => iotaC.injective (Subtype.ext (by
    rw [← conj_iotaC_alphaFun]
    simp))
  map_mul' k k' := AffineEquiv.ext fun v => iotaC.injective (Subtype.ext (by
    rw [AffineEquiv.coe_mul, Function.comp_apply, ← conj_iotaC_alphaFun, ← conj_iotaC_alphaFun,
      ← conj_iotaC_alphaFun, Subgroup.coe_mul]
    group))

theorem conj_iotaC
    (k : K3) (v : Fin 3 → ZMod 2) :
    (k : Dfull) * iotaC v * (k : Dfull)⁻¹ = iotaC (alphaK k v) :=
  conj_iotaC_alphaFun k v

theorem alphaK_surjective :
    Function.Surjective alphaK := by
  intro f
  obtain ⟨k₁, hk₁⟩ := conjE_E3_surjective
    ((mulAutEquivLinear E3).symm (bE.trans (f.linear.trans bE.symm)))
  have hL : ∀ v, linK k₁ v = f.linear v := fun v => by
    rw [linK, LinearEquiv.trans_apply, LinearEquiv.trans_apply, hk₁, MulEquiv.apply_symm_apply,
      LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
  obtain ⟨r, hr, hrc⟩ := exists_R3_translate (eV_mem (f 0 - trK k₁))
  have hlin : ∀ w, linK ⟨r, R3_le_K3 hr⟩ w = w := fun w => eV_injective (by
    rw [eV_linK]
    change r * eV w * r⁻¹ = eV w
    rw [← (Subgroup.mem_centralizer_iff.1 (R3_le_C3 hr) _ (eV_mem w)), mul_inv_cancel_right])
  have htr : trK ⟨r, R3_le_K3 hr⟩ = f 0 - trK k₁ := eV_injective (by
    rw [eV_trK]
    change cQ * (r * cQ * r⁻¹) = eV (f 0 - trK k₁)
    rw [hrc, ← mul_assoc, cQ_mul_self', one_mul])
  refine ⟨⟨r, R3_le_K3 hr⟩ * k₁, AffineEquiv.ext fun v => ?_⟩
  rw [map_mul, AffineEquiv.coe_mul, Function.comp_apply]
  change trK ⟨r, R3_le_K3 hr⟩ + linK ⟨r, R3_le_K3 hr⟩ (trK k₁ + linK k₁ v) = f v
  rw [hlin, htr, hL]
  have hf : f v = f.linear v + f 0 := by
    have h := f.map_vadd 0 v
    rwa [vadd_eq_add, vadd_eq_add, add_zero] at h
  rw [hf]
  abel

theorem short_third_parabolic_involution_centralizer :
    CFSG.IsElementaryAbelian 2 (Subgroup.closure (insert cQ (E3 : Set Dfull))) ∧
    Nat.card (Subgroup.closure (insert cQ (E3 : Set Dfull))) = 16 ∧
    {d : Dfull | ∃ k ∈ K3, k * cQ * k⁻¹ = d} = {d | ∃ e ∈ E3, cQ * e = d} ∧
    {d : Dfull | ∃ e ∈ E3, cQ * e = d}.ncard = 8 ∧
    (∀ d ∈ {d : Dfull | ∃ e ∈ E3, cQ * e = d}, orderOf d = 2) ∧
    (∃ (ι : (Fin 3 → ZMod 2) ≃ {d : Dfull // ∃ e ∈ E3, cQ * e = d})
      (α : K3 →* ((Fin 3 → ZMod 2) ≃ᵃ[ZMod 2] (Fin 3 → ZMod 2))),
      Function.Surjective α ∧
        ∀ (k : K3) (v : Fin 3 → ZMod 2), (k : Dfull) * ι v * (k : Dfull)⁻¹ = ι (α k v)) ∧
    P3 = K3 ⊓ Subgroup.centralizer {cQ} ∧
    (P3.subgroupOf K3).index = 8 ∧
    (CFSG.pCore 2 P3).map P3.subtype = R3 ⊓ Subgroup.centralizer {cQ} ∧
    Nat.card ↥(R3 ⊓ Subgroup.centralizer {cQ}) = 2 ^ 32 ∧
    Nonempty (P3 ⧸ CFSG.pCore 2 P3 ≃* GL (Fin 3) (ZMod 2) × Equiv.Perm (Fin 5)) ∧
    Nat.card P3 = 86586540687360 := by
  rw [closure_eq_E4]
  exact ⟨isElementaryAbelian_E4, natCard_E4, K3_class_eq, ncard_cE3,
    fun d hd => orderOf_of_mem_cE3 hd, ⟨iotaC, alphaK, alphaK_surjective, conj_iotaC⟩, rfl,
    index_P3, map_pCore_P3, natCard_R3c, exists_p3QuotEquiv, natCard_P3⟩

end CFSG.Monster.B.TwoA.Par3
