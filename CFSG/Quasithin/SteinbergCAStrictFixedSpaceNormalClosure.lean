module

public import CFSG.Quasithin.SteinbergBQStrictFixedSpaceThompson

public section

namespace CFSG.Quasithin.SteinbergCA

open Subgroup CFSG CFSG.Quasithin.SteinbergBQ Group

variable {H : Type*} [Group H]

theorem map_conj_centralizer (g : H) (Y : Subgroup H) :
    (centralizer (Y : Set H)).map (MulAut.conj g).toMonoidHom =
      centralizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 := mem_centralizer_iff.1 hc y hy
    calc g * y * g⁻¹ * (g * c * g⁻¹) = g * (y * c) * g⁻¹ := by group
      _ = g * (c * y) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, mem_centralizer_iff.2 fun y hy => ?_, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
    have h1 := mem_centralizer_iff.1 hx (g * y * g⁻¹) ⟨y, hy, rfl⟩
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * y := by group

theorem relIndex_centralizer_map_conj (g : H) (X Y : Subgroup H) :
    (centralizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H)).relIndex
        (X.map (MulAut.conj g).toMonoidHom) =
      (centralizer (Y : Set H)).relIndex X := by
  rw [← map_conj_centralizer, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem isElementaryAbelian_normalClosure {p : ℕ} {V : Subgroup H} [IsElementaryAbelian p V]
    (hcomm : ∀ g : H, ∀ x ∈ V, ∀ y ∈ V, x * (g * y * g⁻¹) = (g * y * g⁻¹) * x) :
    IsElementaryAbelian p (normalClosure (V : Set H)) := by
  have hconj : ∀ a ∈ conjugatesOfSet (V : Set H), ∀ b ∈ conjugatesOfSet (V : Set H),
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, hxa⟩ := mem_conjugatesOfSet_iff.1 ha
    obtain ⟨y, hy, hyb⟩ := mem_conjugatesOfSet_iff.1 hb
    obtain ⟨c, rfl⟩ := isConj_iff.1 hxa
    obtain ⟨d, rfl⟩ := isConj_iff.1 hyb
    have h1 := hcomm (c⁻¹ * d) x hx y hy
    calc c * x * c⁻¹ * (d * y * d⁻¹) = c * (x * (c⁻¹ * d * y * (c⁻¹ * d)⁻¹)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * d * y * (c⁻¹ * d)⁻¹) * x) * c⁻¹ := by rw [h1]
      _ = d * y * d⁻¹ * (c * x * c⁻¹) := by group
  have hcl : normalClosure (V : Set H) = closure (conjugatesOfSet (V : Set H)) := rfl
  have hab : ∀ a ∈ closure (conjugatesOfSet (V : Set H)),
      ∀ b ∈ closure (conjugatesOfSet (V : Set H)), Commute a b := by
    intro a ha b hb
    induction ha using closure_induction with
    | mem x hx =>
      induction hb using closure_induction with
      | mem y hy => exact hconj x hx y hy
      | one => exact Commute.one_right x
      | mul y z _ _ hy hz => exact hy.mul_right hz
      | inv y _ hy => exact hy.inv_right
    | one => exact Commute.one_left b
    | mul x z _ _ hx hz => exact hx.mul_left hz
    | inv x _ hx => exact hx.inv_left
  have hpow : ∀ y ∈ closure (conjugatesOfSet (V : Set H)), y ^ p = 1 := by
    intro y hy
    induction hy using closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, hvy⟩ := mem_conjugatesOfSet_iff.1 hy
      obtain ⟨c, rfl⟩ := isConj_iff.1 hvy
      rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian (p := p) v hv, mul_one,
        mul_inv_cancel]
    | one => rw [one_pow]
    | mul y z hy hz ihy ihz => rw [(hab y hy z hz).mul_pow p, ihy, ihz, one_mul]
    | inv y _ ihy => rw [inv_pow, ihy, inv_one]
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
             (hab a (hcl ▸ a.2) b (hcl ▸ b.2))⟩⟩
           exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext ?_
  rw [coe_pow, coe_one]
  exact hpow x (hcl ▸ x.2)

theorem relIndex_lt_of_strict_fixed_space {p : ℕ} [Fact p.Prime] {T : Subgroup H}
    (V : Subgroup T) [V.Normal]
    (hstrict : ∀ E : Subgroup (MulAut V), E ≤ (MulAut.conjNormal : T →* MulAut V).range →
      E ≠ ⊥ → IsElementaryAbelian p E → Nat.card E < (FixedPoints.subgroup E V).index)
    {W : Subgroup H} (hWT : W ≤ T) [IsElementaryAbelian p W]
    (hWV : ¬ W ≤ centralizer ((V.map T.subtype : Subgroup H) : Set H)) :
    (centralizer ((V.map T.subtype : Subgroup H) : Set H)).relIndex W <
      (centralizer (W : Set H)).relIndex (V.map T.subtype) := by
  set W' : Subgroup T := W.subgroupOf T with hW'
  have : IsElementaryAbelian p W' := IsElementaryAbelian.subgroupOf hWT
  set E := W'.map (MulAut.conjNormal : T →* MulAut V) with hE
  have hW'map : W'.map T.subtype = W := by
    rw [hW', subgroupOf_map_subtype, inf_of_le_left hWT]
  have hE1 : E ≠ ⊥ := by
    intro hbot
    apply hWV
    have hle : W' ≤ (MulAut.conjNormal : T →* MulAut V).ker := by
      rw [hE] at hbot
      exact (Subgroup.map_eq_bot_iff _).1 hbot
    rw [ker_conjNormal] at hle
    intro w hw
    rw [mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have h1 := mem_centralizer_iff.1 (hle (show (⟨w, hWT hw⟩ : T) ∈ W' from hw)) v hv
    exact congrArg Subtype.val h1
  have hlt := hstrict E (map_le_range _ _) hE1 (IsElementaryAbelian.map _)
  have hcardE : Nat.card E = (centralizer ((V.map T.subtype : Subgroup H) : Set H)).relIndex W := by
    rw [hE, card_map_eq_relIndex_ker, ker_conjNormal]
    rw [← relIndex_map_map_of_injective (f := T.subtype) _ _ T.subtype_injective, hW'map,
      ← inf_relIndex_right, ← inf_relIndex_right (centralizer _) W]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hxW⟩
      refine ⟨mem_centralizer_iff.2 ?_, hxW⟩
      rintro _ ⟨v, hv, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.1 ht v hv)
    · rintro ⟨hxC, hxW⟩
      refine ⟨⟨⟨x, hWT hxW⟩, mem_centralizer_iff.2 fun v hv => Subtype.ext ?_, rfl⟩, hxW⟩
      exact mem_centralizer_iff.1 hxC (v : H) ⟨v, hv, rfl⟩
  set φ : V →* H := T.subtype.comp V.subtype with hφ
  have hφinj : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  have hφtop : (⊤ : Subgroup V).map φ = V.map T.subtype := by
    rw [hφ, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  have hindex : (FixedPoints.subgroup E V).index =
      (centralizer (W : Set H)).relIndex (V.map T.subtype) := by
    rw [← relIndex_top_right, ← relIndex_map_map_of_injective _ _ hφinj, hφtop,
      ← inf_relIndex_right, ← inf_relIndex_right (centralizer _) _]
    congr 1
    ext x
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hxV⟩
      refine ⟨mem_centralizer_iff.2 fun w hw => ?_, hxV⟩
      have h1 := (mem_fixedPoints_subgroup_mulAut_iff.1 hv)
        (MulAut.conjNormal (⟨w, hWT hw⟩ : T)) ⟨⟨w, hWT hw⟩, hw, rfl⟩
      have h2 := congrArg (fun u : V => ((u : T) : H)) h1
      simp only [MulAut.conjNormal_apply, coe_mul, coe_inv] at h2
      simp only [hφ, MonoidHom.comp_apply, coe_subtype]
      calc w * ((v : T) : H) = w * ((v : T) : H) * w⁻¹ * w := by group
        _ = ((v : T) : H) * w := by rw [h2]
    · rintro ⟨hxC, hxV⟩
      obtain ⟨t, ht, rfl⟩ := hxV
      refine ⟨⟨⟨t, ht⟩, mem_fixedPoints_subgroup_mulAut_iff.2 ?_, rfl⟩, ⟨t, ht, rfl⟩⟩
      rintro σ ⟨w, hw, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, coe_mul, coe_inv]
      have h1 := mem_centralizer_iff.1 hxC ((w : T) : H) hw
      simp only [coe_subtype] at h1
      calc ((w : T) : H) * (t : H) * ((w : T) : H)⁻¹ =
            (t : H) * ((w : T) : H) * ((w : T) : H)⁻¹ := by rw [h1]
        _ = (t : H) := by group
  rw [← hcardE, ← hindex]
  exact hlt

theorem strict_fixed_space_inequality_makes_core_contained_normal_closure_elementary
    [Finite H] (T : Sylow 2 H) (V : Subgroup (T : Subgroup H)) [V.Normal]
    (hV : IsElementaryAbelian 2 V) (hVO : V.map (T : Subgroup H).subtype ≤ pCore 2 H)
    (hstrict : ∀ E : Subgroup (MulAut V),
      E ≤ (MulAut.conjNormal : (T : Subgroup H) →* MulAut V).range → E ≠ ⊥ →
        IsElementaryAbelian 2 E → Nat.card E < (FixedPoints.subgroup E V).index) :
    IsElementaryAbelian 2 (normalClosure ((V.map (T : Subgroup H).subtype : Subgroup H) : Set H)) ∧
      (normalClosure ((V.map (T : Subgroup H).subtype : Subgroup H) : Set H)).Normal ∧
      normalClosure ((V.map (T : Subgroup H).subtype : Subgroup H) : Set H) ≤ pCore 2 H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Vh : Subgroup H := V.map (T : Subgroup H).subtype with hVh
  have : IsElementaryAbelian 2 Vh := IsElementaryAbelian.map_subtype
  set Q := pCore 2 H with hQ
  have : Q.Normal := pCore_normal
  have hQT : Q ≤ T := IsPGroup.le_sylow_of_normal pCore_isPGroup T
  have hconjQ : ∀ g : H, Vh.map (MulAut.conj g).toMonoidHom ≤ Q := by
    rintro g _ ⟨v, hv, rfl⟩
    exact (inferInstance : Q.Normal).conj_mem v (hVO hv) g
  have hel : ∀ g : H, IsElementaryAbelian 2 (Vh.map (MulAut.conj g).toMonoidHom) := fun g =>
    IsElementaryAbelian.map _
  have hlt : ∀ g : H, ¬ Vh.map (MulAut.conj g).toMonoidHom ≤ centralizer (Vh : Set H) →
      (centralizer (Vh : Set H)).relIndex (Vh.map (MulAut.conj g).toMonoidHom) <
        (centralizer ((Vh.map (MulAut.conj g).toMonoidHom : Subgroup H) : Set H)).relIndex Vh :=
    fun g hg => by
      have := hel g
      exact relIndex_lt_of_strict_fixed_space V hstrict ((hconjQ g).trans hQT) hg
  have hcomm : ∀ g : H, Vh.map (MulAut.conj g).toMonoidHom ≤ centralizer (Vh : Set H) := by
    intro g
    by_contra hg
    have h1 := hlt g hg
    have hmap : (Vh.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = Vh := by
      ext x
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        have e : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom y) = y := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [e]
        exact hy
      · intro hx
        refine ⟨g⁻¹ * x * g⁻¹⁻¹, ⟨x, hx, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have hg' : ¬ Vh.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (Vh : Set H) := by
      intro h
      apply hg
      intro x hx
      rw [mem_centralizer_iff]
      intro v hv
      obtain ⟨y, hy, rfl⟩ := hx
      have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ Vh.map (MulAut.conj g⁻¹).toMonoidHom := ⟨v, hv, rfl⟩
      have h2 := mem_centralizer_iff.1 (h hv') y hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h2 ⊢
      calc v * (g * y * g⁻¹) = g * ((g⁻¹ * v * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * v * g)) * g⁻¹ := by rw [← h2]
        _ = g * y * g⁻¹ * v := by group
    have h2 := hlt g⁻¹ hg'
    rw [← relIndex_centralizer_map_conj g, hmap,
      ← relIndex_centralizer_map_conj g (Vh) (Vh.map (MulAut.conj g⁻¹).toMonoidHom),
      hmap] at h2
    omega
  refine ⟨isElementaryAbelian_normalClosure fun g x hx y hy => ?_, normalClosure_normal,
    normalClosure_le_normal fun x hx => hVO hx⟩
  have h1 := mem_centralizer_iff.1 (hcomm g ⟨y, hy, rfl⟩) x hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  exact h1

end CFSG.Quasithin.SteinbergCA
