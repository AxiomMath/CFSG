module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derFixOrth

public section

namespace CFSG.StandardType

open Module CFSG.Open


private theorem l48dC_comm {G : Type*} [Group G] {E : Subgroup G} (hE : IsElemAbelian 3 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  haveI : IsMulCommutative E := hE.1
  have h : (⟨a, ha⟩ : E) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := mul_comm' _ _
  simpa using congrArg Subtype.val h

private def l48dC_res {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V]
    {U : Submodule K V} (u : Module.End K V) (hu : ∀ v ∈ U, u v ∈ U) :
    Module.End K U where
  toFun v := ⟨u v.1, hu v.1 v.2⟩
  map_add' v w := Subtype.ext (map_add u v.1 w.1)
  map_smul' c v := Subtype.ext (map_smul u c v.1)

private def l48dC_resUnit {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {U : Submodule K V} (u : (Module.End K V)ˣ)
    (hu : ∀ v ∈ U, (u : Module.End K V) v ∈ U)
    (hu' : ∀ v ∈ U, ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ U) :
    (Module.End K U)ˣ where
  val := l48dC_res (u : Module.End K V) hu
  inv := l48dC_res ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) hu'
  val_inv := by
    apply LinearMap.ext; intro v
    rw [Module.End.mul_apply, Module.End.one_apply]
    apply Subtype.ext
    change (u : Module.End K V) (((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) v.1) = v.1
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  inv_val := by
    apply LinearMap.ext; intro v
    rw [Module.End.mul_apply, Module.End.one_apply]
    apply Subtype.ext
    change ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((u : Module.End K V) v.1) = v.1
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]

private def l48dC_psi0 {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {G' : Type*} [Group G'] (φ : G' →* (Module.End K V)ˣ)
    (H : Subgroup G') (U : Submodule K V)
    (hU : ∀ a ∈ H, ∀ v ∈ U, (φ a : Module.End K V) v ∈ U) : H →* (Module.End K U)ˣ where
  toFun a := l48dC_resUnit (φ (a : G')) (hU a a.2)
    (by
      intro v hv
      rw [← map_inv]
      exact hU a⁻¹ (H.inv_mem a.2) v hv)
  map_one' := by
    apply Units.ext
    apply LinearMap.ext; intro v
    apply Subtype.ext
    change ((φ (((1 : H) : G')) : (Module.End K V)ˣ) : Module.End K V) v.1 = v.1
    rw [Subgroup.coe_one, map_one, Units.val_one, Module.End.one_apply]
  map_mul' a b := by
    apply Units.ext
    rw [Units.val_mul]
    apply LinearMap.ext; intro v
    rw [Module.End.mul_apply]
    apply Subtype.ext
    change ((φ (((a * b : H) : G')) : (Module.End K V)ˣ) : Module.End K V) v.1 =
      ((φ (a : G') : (Module.End K V)ˣ) : Module.End K V)
        (((φ (b : G') : (Module.End K V)ˣ) : Module.End K V) v.1)
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, Module.End.mul_apply]

private def l48dC_fixVec {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (v : V) : Subgroup G where
  carrier := {a | (ρ a : Module.End K V) v = v}
  mul_mem' {a b} ha hb := by
    change (ρ (a * b) : Module.End K V) v = v
    rw [map_mul, Units.val_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by
    change (ρ 1 : Module.End K V) v = v
    rw [map_one, Units.val_one, Module.End.one_apply]
  inv_mem' {a} ha := by
    show ((ρ a⁻¹ : (Module.End K V)ˣ) : Module.End K V) v = v
    rw [map_inv]
    have h1 : ((ρ a : (Module.End K V)ˣ) : Module.End K V)
        ((((ρ a)⁻¹ : (Module.End K V)ˣ) : Module.End K V) v) = v := by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have h2 : ((ρ a : (Module.End K V)ˣ) : Module.End K V) v = v := ha
    have hc := congrArg (fun w => (((ρ a)⁻¹ : (Module.End K V)ˣ) : Module.End K V) w)
      (h1.trans h2.symm)
    rwa [TwoThree.val_inv_apply_apply, TwoThree.val_inv_apply_apply] at hc

private theorem l48dC_mem_fixSpace_zpowers {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (g : G) (v : V) :
    v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers g) ↔ (ρ g : Module.End K V) v = v := by
  rw [SmallRule.mem_fixSpaceOf]
  constructor
  · intro h; exact h g (Subgroup.mem_zpowers g)
  · intro h a ha
    have hle : Subgroup.zpowers g ≤ l48dC_fixVec ρ v := Subgroup.zpowers_le.mpr h
    exact (hle ha)

private theorem l48dC_fixSpace_eq_ker {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (g : G) :
    SmallRule.fixSpaceOf ρ (Subgroup.zpowers g) =
      LinearMap.ker ((ρ g : Module.End K V) - 1) := by
  ext v
  rw [l48dC_mem_fixSpace_zpowers, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
    sub_eq_zero]

private def l48dC_fixSub {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (E : Subgroup G) (U : Submodule K V) :
    Subgroup E :=
  Subgroup.comap (ρ.comp E.subtype) (TwoThree.fixG U)

private theorem l48dC_mem_fixSub {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    {ρ : G →* (Module.End K V)ˣ} {E : Subgroup G}
    {U : Submodule K V} {a : E} :
    a ∈ l48dC_fixSub ρ E U ↔ ∀ v ∈ U, (ρ (a : G) : Module.End K V) v = v :=
  Iff.rfl

private def l48dC_Efix {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (E : Subgroup G) (U : Submodule K V) :
    Subgroup G :=
  (l48dC_fixSub ρ E U).map E.subtype

private theorem l48dC_mem_Efix {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    {ρ : G →* (Module.End K V)ˣ} {E : Subgroup G}
    {U : Submodule K V} {x : G} :
    x ∈ l48dC_Efix ρ E U ↔ x ∈ E ∧ ∀ v ∈ U, (ρ x : Module.End K V) v = v := by
  rw [l48dC_Efix, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, (l48dC_mem_fixSub.mp hh)⟩
  · rintro ⟨hxE, hx⟩
    exact ⟨⟨x, hxE⟩, l48dC_mem_fixSub.mpr hx, rfl⟩

@[instance_reducible] private def l48dC_actionT {K : Type*} [Field K] [CharP K 2] [Finite K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (E : Subgroup G) (T : Submodule K V)
    (hTE : ∀ a ∈ E, ∀ v ∈ T, (ρ a : Module.End K V) v ∈ T) : MulAction E T where
  smul a v := ⟨(ρ (a : G) : Module.End K V) v.1, hTE (a : G) a.2 v.1 v.2⟩
  one_smul v := Subtype.ext (by
    change ((ρ (((1 : E) : G)) : (Module.End K V)ˣ) : Module.End K V) v.1 = v.1
    rw [Subgroup.coe_one, map_one, Units.val_one, Module.End.one_apply])
  mul_smul a b v := Subtype.ext (by
    change ((ρ (((a * b : E) : G)) : (Module.End K V)ˣ) : Module.End K V) v.1 =
      ((ρ (a : G) : (Module.End K V)ˣ) : Module.End K V)
        (((ρ (b : G) : (Module.End K V)ˣ) : Module.End K V) v.1)
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, Module.End.mul_apply])

theorem ggB2der_six_dim_fixer {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (hK : Nat.card K = 2) (ρ : G →* (Module.End K V)ˣ)
    (hρ : Function.Injective ρ) (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hr : B.IsRefl)
    (hiso : ∀ g v w, B ((ρ g : Module.End K V) v) ((ρ g : Module.End K V) w) = B v w)
    (hdim : Module.finrank K V = 8) {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 27) {z : G} (hzE : z ∈ E) (hz1 : z ≠ 1)
    (hW0 : Module.finrank K (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z)) = 4)
    (hker : ∀ a ∈ E, (∀ v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers z),
        (ρ a : Module.End K V) v = v) → a ∈ Subgroup.zpowers z)
    {T : Submodule K V} (hT2 : Module.finrank K T = 2) (hTiso : ∀ u ∈ T, ∀ v ∈ T, B u v = 0)
    (hTE : ∀ a ∈ E, ∀ v ∈ T, (ρ a : Module.End K V) v ∈ T)
    (hTW : T ≤ B.orthogonal (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z))) :
    ∃ e ∈ E, e ≠ 1 ∧
      Module.finrank K (SmallRule.fixSpaceOf ρ (Subgroup.zpowers e)) = 6 ∧
      ∀ a ∈ E, (∀ v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers e),
        (ρ a : Module.End K V) v = v) → a ∈ Subgroup.zpowers e := by
  classical
  haveI : Finite E := (Nat.card_pos_iff.mp (by rw [hEc]; norm_num)).2
  have hz3 : z ^ 3 = 1 := hE.2 z hzE
  obtain ⟨hcompl, hW0inv0, hW1inv0, hzfix0⟩ :=
    ggB2der_fix_orth_decomp hK ρ B hB hr hiso hz3
  set W0 : Submodule K V := SmallRule.fixSpaceOf ρ (Subgroup.zpowers z) with hW0def
  set W1 : Submodule K V := B.orthogonal W0 with hW1def
  have hcomplW : IsCompl W0 W1 := by rw [hW1def, hW0def]; exact hcompl
  have hW0fr : Module.finrank K W0 = 4 := by rw [hW0def]; exact hW0
  have hTWW : T ≤ B.orthogonal W0 := by rw [hW0def]; exact hTW
  have hTW1 : T ≤ W1 := by rw [hW1def]; exact hTWW
  have hTne : T ≠ ⊥ := by intro h; rw [h, finrank_bot] at hT2; omega
  have hW0invW : ∀ a ∈ E, ∀ v ∈ W0, (ρ a : Module.End K V) v ∈ W0 := by
    intro a ha v hv
    rw [hW0def] at hv ⊢
    exact hW0inv0 a (l48dC_comm hE ha hzE) v hv
  have hW1invW : ∀ a ∈ E, ∀ v ∈ W1, (ρ a : Module.End K V) v ∈ W1 := by
    intro a ha v hv
    rw [hW1def, hW0def] at hv
    rw [hW1def, hW0def]
    exact hW1inv0 a (l48dC_comm hE ha hzE) v hv
  have hzfixW : ∀ v ∈ W1, (ρ z : Module.End K V) v = v → v = 0 := by
    intro v hv h
    rw [hW1def, hW0def] at hv
    exact hzfix0 v hv h
  have hW1T : B.orthogonal T ⊓ W1 = T := by
    have hinf : W0 ⊓ T = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ W0 ⊓ W1 := ⟨hx.1, hTW1 hx.2⟩
      rw [hcomplW.inf_eq_bot] at hx'
      exact hx'
    have horth : W0 ⊔ T = B.orthogonal T := by
      apply Submodule.eq_of_le_of_finrank_eq
      · refine sup_le ?_ ?_
        · intro w hw t ht
          exact hr w t (hTWW ht w hw)
        · intro t ht t' ht'
          exact hTiso t' ht' t ht
      · have h1 : Module.finrank K (W0 ⊔ T : Submodule K V) = 6 := by
          have h := Submodule.finrank_sup_add_finrank_inf_eq W0 T
          rw [hinf, finrank_bot, add_zero] at h
          omega
        have h2 : Module.finrank K (B.orthogonal T) = 6 := by
          rw [LinearMap.BilinForm.finrank_orthogonal hB T, hdim, hT2]
        omega
    rw [← horth]
    apply le_antisymm
    · intro x hx
      obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp hx.1
      have hw_eq : w = x - t := (eq_sub_iff_add_eq).mpr hwt
      have hwW1 : w ∈ W1 := by
        rw [hw_eq]
        exact W1.sub_mem hx.2 (hTW1 ht)
      have hwbot : w = 0 := by
        have hx' : w ∈ W0 ⊓ W1 := ⟨hw, hwW1⟩
        rw [hcomplW.inf_eq_bot] at hx'
        simpa using hx'
      have hxt : x = t := by rw [← hwt, hwbot, zero_add]
      rw [hxt]; exact ht
    · intro x hx
      exact ⟨Submodule.mem_sup_right hx, hTW1 hx⟩
  set ET : Subgroup G := l48dC_Efix ρ E T with hETdef
  set K1 : Subgroup G := l48dC_Efix ρ E W1 with hK1def
  have hETmem : ∀ {x : G}, x ∈ ET ↔ x ∈ E ∧ ∀ v ∈ T, (ρ x : Module.End K V) v = v := by
    intro x; rw [hETdef, l48dC_mem_Efix]
  have hK1mem : ∀ {x : G}, x ∈ K1 ↔ x ∈ E ∧ ∀ v ∈ W1, (ρ x : Module.End K V) v = v := by
    intro x; rw [hK1def, l48dC_mem_Efix]
  have hTE_le_W1 : ET ≤ K1 := by
    intro a ha
    rw [hETmem] at ha
    rw [hK1mem]
    refine ⟨ha.1, ?_⟩
    intro v hv
    have hAv : (ρ a : Module.End K V) v = v := by
      have hw_orth : ((ρ a : Module.End K V) - 1) v ∈ B.orthogonal T := by
        intro t ht
        have hainv : (((ρ a)⁻¹ : (Module.End K V)ˣ) : Module.End K V) t = t := by
          have h := congrArg (fun w => (((ρ a)⁻¹ : (Module.End K V)ˣ) : Module.End K V) w)
            (ha.2 t ht)
          rw [TwoThree.val_inv_apply_apply] at h
          exact h.symm
        have h1 : B t ((ρ a : Module.End K V) v) = B t v := by
          have h := hiso a⁻¹ t ((ρ a : Module.End K V) v)
          rw [map_inv, hainv, TwoThree.val_inv_apply_apply] at h
          exact h.symm
        show B t (((ρ a : Module.End K V) - 1) v) = 0
        rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, sub_self]
      have hw_W1 : ((ρ a : Module.End K V) - 1) v ∈ W1 := by
        rw [LinearMap.sub_apply, Module.End.one_apply]
        exact W1.sub_mem (hW1invW a ha.1 v hv) hv
      have hw_T : ((ρ a : Module.End K V) - 1) v ∈ T := by
        rw [← hW1T]
        exact ⟨hw_orth, hw_W1⟩
      have h2 : ((ρ a : Module.End K V) - 1) (((ρ a : Module.End K V) - 1) v) = 0 := by
        rw [LinearMap.sub_apply, Module.End.one_apply, ha.2 _ hw_T, sub_self]
      have hsq : ((ρ a : Module.End K V) - 1) * ((ρ a : Module.End K V) - 1) =
          (ρ a : Module.End K V) * (ρ a : Module.End K V) + 1 := by
        calc ((ρ a : Module.End K V) - 1) * ((ρ a : Module.End K V) - 1)
            = (ρ a : Module.End K V) * (ρ a : Module.End K V) -
                2 * (ρ a : Module.End K V) + 1 := by noncomm_ring
          _ = (ρ a : Module.End K V) * (ρ a : Module.End K V) + 1 := by
              rw [show (2 : Module.End K V) * (ρ a : Module.End K V) = 0 by
                rw [TwoThree.two_eq_zero_end, zero_mul]]
              rw [sub_zero]
      have hAAv : (ρ a : Module.End K V) ((ρ a : Module.End K V) v) = v := by
        have hsqv : ((ρ a : Module.End K V) * (ρ a : Module.End K V) + 1) v = 0 := by
          rw [← hsq, Module.End.mul_apply]
          exact h2
        have h0 : (ρ a : Module.End K V) ((ρ a : Module.End K V) v) + v = 0 := by
          simpa [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] using hsqv
        have hneg : (ρ a : Module.End K V) ((ρ a : Module.End K V) v) = -v :=
          (eq_neg_iff_add_eq_zero).mpr h0
        have hvv : v + v = 0 := by
          rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
        have hnegv : -v = v := (neg_eq_iff_add_eq_zero).mpr hvv
        rwa [hnegv] at hneg
      have hA3 : (ρ a : Module.End K V) ^ 3 = 1 := by
        have h1 : (ρ a) ^ 3 = 1 := by rw [← map_pow, hE.2 a ha.1, map_one]
        have := congrArg (fun u : (Module.End K V)ˣ => (u : Module.End K V)) h1
        simpa [Units.val_pow_eq_pow_val] using this
      have hA3v : (ρ a : Module.End K V)
          ((ρ a : Module.End K V) ((ρ a : Module.End K V) v)) = v := by
        have := congrArg (fun f : Module.End K V => f v) hA3
        simpa [pow_succ, Module.End.mul_apply, Module.End.one_apply] using this
      have hAAv' : (ρ a : Module.End K V)
          ((ρ a : Module.End K V) ((ρ a : Module.End K V) v)) = (ρ a : Module.End K V) v := by
        rw [hAAv]
      exact hAAv'.symm.trans hA3v
    exact hAv
  have hK1eq : K1 = ET := by
    apply le_antisymm
    · intro a ha
      rw [hK1mem] at ha
      exact hETmem.mpr ⟨ha.1, fun v hv => ha.2 v (hTW1 hv)⟩
    · exact hTE_le_W1
  letI : MulAction E T := l48dC_actionT ρ E T hTE
  let ψT : E →* Equiv.Perm T := MulAction.toPermHom E T
  have hETker : l48dC_fixSub ρ E T = ψT.ker := by
    ext a
    rw [l48dC_mem_fixSub]
    constructor
    · intro ha
      rw [MonoidHom.mem_ker]
      apply Equiv.ext
      intro v
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
      apply Subtype.ext
      exact ha v.1 v.2
    · intro ha v hv
      rw [MonoidHom.mem_ker] at ha
      have h1 : (ψT a) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [ha]; rfl
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at h1
      exact congrArg Subtype.val h1
  have hzETn : z ∉ ET := by
    intro hz
    have hzT : ∀ v ∈ T, (ρ z : Module.End K V) v = v := (hETmem.mp hz).2
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
    exact ht0 (hzfixW t (hTW1 ht) (hzT t ht))
  have hfixSub_card : Nat.card (l48dC_fixSub ρ E T) = 9 := by
    rw [hETker]
    have hcard := Subgroup.card_ker_mul_card_range ψT
    rw [hEc] at hcard
    haveI : Finite V := Module.finite_of_finite K
    haveI : Finite T := Finite.of_injective (Subtype.val) Subtype.val_injective
    have hcardT : Nat.card T = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := K), hK, hT2]
      norm_num
    have hcardPerm : Nat.card (Equiv.Perm T) = 24 := by
      rw [Nat.card_perm, hcardT]; norm_num
    have hdvd24 : Nat.card ψT.range ∣ 24 := by
      rw [← hcardPerm]; exact Subgroup.card_subgroup_dvd_card ψT.range
    have hdvd27 : Nat.card ψT.range ∣ 27 := by
      rw [← hEc]; exact Subgroup.card_range_dvd ψT
    have hdvd3 : Nat.card ψT.range ∣ 3 := by
      have h := Nat.dvd_gcd hdvd24 hdvd27
      rwa [show Nat.gcd 24 27 = 3 by norm_num] at h
    have hne27 : Nat.card ψT.ker ≠ 27 := by
      intro h27
      have htop : ψT.ker = ⊤ := Subgroup.eq_top_of_card_eq ψT.ker (by rw [h27, hEc])
      have hthis : (⟨z, hzE⟩ : E) ∈ ψT.ker := by rw [htop]; exact Subgroup.mem_top _
      rw [← hETker] at hthis
      refine hzETn ?_
      rw [hETdef]
      exact Subgroup.mem_map.mpr ⟨⟨z, hzE⟩, hthis, rfl⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with hr1 | hr3
    · rw [hr1, mul_one] at hcard
      exact absurd hcard hne27
    · rw [hr3] at hcard
      omega
  have hETcard : Nat.card ET = 9 := by
    rw [hETdef, l48dC_Efix, Subgroup.card_map_of_injective (Subgroup.subtype_injective E)]
    exact hfixSub_card
  have hW0invET : ∀ a ∈ ET, ∀ v ∈ W0, (ρ a : Module.End K V) v ∈ W0 := by
    intro a ha v hv
    exact hW0invW a (hETmem.mp ha).1 v hv
  let ψ0 : ET →* (Module.End K W0)ˣ := l48dC_psi0 ρ ET W0 hW0invET
  let X : Subgroup (Module.End K W0)ˣ := ψ0.range
  have hkerψ0 : ψ0.ker = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at ha
    have haE : (a : G) ∈ E := (hETmem.mp a.2).1
    have haT : ∀ v ∈ T, (ρ (a : G) : Module.End K V) v = v := (hETmem.mp a.2).2
    have hfixa : ∀ v ∈ W0, (ρ (a : G) : Module.End K V) v = v := by
      intro v hv
      have h1 : (ψ0 a : Module.End K W0) ⟨v, hv⟩ = ⟨v, hv⟩ := by
        rw [ha, Units.val_one, Module.End.one_apply]
      exact congrArg Subtype.val h1
    have hza : (a : G) ∈ Subgroup.zpowers z := hker (a : G) haE hfixa
    by_contra ha1
    have hane : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hord : orderOf (a : G) = 3 := orderOf_eq_prime (hE.2 (a : G) haE) hane
    have hzEsub : Subgroup.zpowers z ≤ E := Subgroup.zpowers_le.mpr hzE
    haveI : Finite (Subgroup.zpowers z) :=
      Finite.of_injective (fun x : Subgroup.zpowers z => (⟨x.1, hzEsub x.2⟩ : E))
        (by intro x y h; exact Subtype.ext (congrArg (fun w : E => (w : G)) h))
    have hcarda : Nat.card (Subgroup.zpowers (a : G)) = 3 := by rw [Nat.card_zpowers, hord]
    have hcardz : Nat.card (Subgroup.zpowers z) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
    have hle : Subgroup.zpowers (a : G) ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hza
    have heq : Subgroup.zpowers (a : G) = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcarda, hcardz])
    have hzET : z ∈ ET := by
      have hzmem : z ∈ Subgroup.zpowers (a : G) := by rw [heq]; exact Subgroup.mem_zpowers z
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzmem
      rw [← hk]
      exact (a ^ k).2
    exact hzETn hzET
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
    have hab : a * b = b * a :=
      Subtype.ext (l48dC_comm hE (hETmem.mp a.2).1 (hETmem.mp b.2).1)
    rw [← map_mul, ← map_mul, hab]
  have hXexp : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [← map_pow]
    have ha3 : a ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE.2 (a : G) (hETmem.mp a.2).1
    rw [ha3, map_one]
  have hXcard9 : Nat.card X = 9 := by
    have hcard := Subgroup.card_ker_mul_card_range ψ0
    rw [hkerψ0, Subgroup.card_bot, one_mul] at hcard
    rw [hETcard] at hcard
    exact hcard
  have hXne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXcard9
    norm_num at hXcard9
  have hXcard : 3 ^ Module.finrank K W0 ≤ 3 * Nat.card X ^ 2 := by
    rw [hW0fr, hXcard9]
    norm_num
  obtain ⟨g, hgX, hgrange, hgend⟩ :=
    TwoThree.exists_end_node (K := K) (V := W0) hK X hXcomm hXexp hXne hXcard
  obtain ⟨e, rfl⟩ := MonoidHom.mem_range.mp hgX
  have he_ne : e ≠ 1 := by
    intro h
    have hzero : (((1 : (Module.End K W0)ˣ) : Module.End K W0) - 1) = 0 := by
      rw [Units.val_one, sub_self]
    rw [h, map_one] at hgrange
    rw [hzero, LinearMap.range_zero, finrank_bot] at hgrange
    omega
  have hdimC : Module.finrank K (SmallRule.fixSpaceOf ρ (Subgroup.zpowers (e : G))) = 6 := by
    rw [l48dC_fixSpace_eq_ker]
    have hrange : Module.finrank K
        (LinearMap.range ((ρ (e : G) : Module.End K V) - 1)) = 2 := by
      have heW1 : ∀ v ∈ W1, (ρ (e : G) : Module.End K V) v = v :=
        (hK1mem.mp (hTE_le_W1 e.2)).2
      have h1 : LinearMap.range ((ρ (e : G) : Module.End K V) - 1) =
          W0.map ((ρ (e : G) : Module.End K V) - 1) := by
        apply le_antisymm
        · rintro y ⟨x, rfl⟩
          have hx : x ∈ W0 ⊔ W1 := by rw [hcomplW.sup_eq_top]; exact Submodule.mem_top
          obtain ⟨w0, hw0, w1, hw1, hxw⟩ := Submodule.mem_sup.mp hx
          have hfw1 : ((ρ (e : G) : Module.End K V) - 1) w1 = 0 := by
            rw [LinearMap.sub_apply, Module.End.one_apply, heW1 w1 hw1, sub_self]
          refine ⟨w0, hw0, ?_⟩
          rw [← hxw, map_add, hfw1, add_zero]
        · rintro y ⟨w, hw, rfl⟩
          exact ⟨w, rfl⟩
      have h2 : W0.map ((ρ (e : G) : Module.End K V) - 1) =
          (LinearMap.range ((ψ0 e : Module.End K W0) - 1)).map W0.subtype := by
        ext y
        constructor
        · rintro ⟨w, hw, rfl⟩
          refine ⟨(ψ0 e : Module.End K W0) ⟨w, hw⟩ - ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
          rfl
        · rintro ⟨z, hz, rfl⟩
          obtain ⟨w, hwz⟩ := LinearMap.mem_range.mp hz
          refine ⟨w.1, w.2, ?_⟩
          rw [← hwz]
          rfl
      rw [h1, h2, Submodule.finrank_map_subtype_eq, hgrange]
    have hrn := LinearMap.finrank_range_add_finrank_ker ((ρ (e : G) : Module.End K V) - 1)
    omega
  refine ⟨(e : G), (hETmem.mp e.2).1, fun h => he_ne (Subtype.ext h), hdimC, ?_⟩
  intro a haE hafix
  have haW1 : a ∈ K1 := by
    rw [hK1mem]
    refine ⟨haE, ?_⟩
    intro v hv
    have hvC : v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers (e : G)) := by
      rw [l48dC_mem_fixSpace_zpowers]
      exact (hK1mem.mp (hTE_le_W1 e.2)).2 v hv
    exact hafix v hvC
  have haET : a ∈ ET := by rw [← hK1eq]; exact haW1
  have hx : ψ0 ⟨a, haET⟩ ∈ X := MonoidHom.mem_range.mpr ⟨⟨a, haET⟩, rfl⟩
  have hfixW : ∀ w : W0, (ψ0 e : Module.End K W0) w = w →
      (ψ0 ⟨a, haET⟩ : Module.End K W0) w = w := by
    intro w hw
    apply Subtype.ext
    have hew : (ρ (e : G) : Module.End K V) w.1 = w.1 := by
      have h := congrArg Subtype.val hw
      change (ρ (e : G) : Module.End K V) w.1 = w.1 at h
      exact h
    have hwC : w.1 ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers (e : G)) := by
      rw [l48dC_mem_fixSpace_zpowers]; exact hew
    change (ρ a : Module.End K V) w.1 = w.1
    exact hafix w.1 hwC
  have hmem : ψ0 ⟨a, haET⟩ ∈ Subgroup.zpowers (ψ0 e) := hgend _ hx hfixW
  have hinj : Function.Injective ψ0 := (MonoidHom.ker_eq_bot_iff ψ0).mp hkerψ0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hb : (e : ET) ^ k = ⟨a, haET⟩ := hinj (by rw [map_zpow, hk])
  have hval : (e : G) ^ k = a := by
    have := congrArg (fun x : ET => (x : G)) hb
    simpa [Subgroup.coe_zpow] using this
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, hval⟩

end CFSG.StandardType

end
