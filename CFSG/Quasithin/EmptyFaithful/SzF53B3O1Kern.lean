module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5Split
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBinary
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.SzF53MNatL2

public section

namespace CFSG.Quasithin.F53B3.O1

open CFSG.QuasithinUnique.Setup CFSG.Quasithin.F53Mod CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

theorem kernel_bot_of_alt5 {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] {Γ : Type*} [Group Γ]
    (α : Γ →* ↥(alternatingGroup (Fin 5))) (hα : Function.Surjective α)
    (ρ : Γ →* (E ≃ₗ[ZMod 2] E)) (hker : ∀ g, α g = 1 → ρ g = 1)
    (π : E →ₗ[ZMod 2] ↥(SL2Modules.evenWeight (Fin 5))) (hπs : Function.Surjective π)
    (hπ : ∀ g e, π (ρ g e) =
      SL2Modules.deletedRep (alternatingGroup (Fin 5)) (Fin 5) (α g) (π e))
    (hfix : ∀ g e, π e = 0 → ρ g e = e)
    (hgen : Submodule.span (ZMod 2) (Set.range fun p : Γ × E => ρ p.1 p.2 - p.2) = ⊤) :
    LinearMap.ker π = ⊥ := by
  have hker' : α.ker ≤ ρ.ker := fun g hg => hker g hg
  let ρ' : ↥(alternatingGroup (Fin 5)) →* (E ≃ₗ[ZMod 2] E) := α.liftOfSurjective hα ⟨ρ, hker'⟩
  have hρ' : ∀ g, ρ' (α g) = ρ g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
      (Function.rightInverse_surjInv hα) ⟨ρ, hker'⟩ g
  let ρR : Representation (ZMod 2) ↥(alternatingGroup (Fin 5)) E :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ'
  have hρR : ∀ g e, ρR (α g) e = ρ g e := fun g e => by
    show (ρ' (α g)) e = _
    rw [hρ']
  refine (SL2Modules.deleted_five_quotient_kernel_trivial (Fintype.card_fin 5) ρR π hπs ?_ ?_
    ?_).1
  · intro s e
    obtain ⟨g, rfl⟩ := hα s
    rw [hρR]
    exact hπ g e
  · intro s e he
    obtain ⟨g, rfl⟩ := hα s
    rw [hρR]
    exact hfix g e he
  · rw [eq_top_iff, ← hgen]
    refine Submodule.span_mono ?_
    rintro _ ⟨⟨g, e⟩, rfl⟩
    exact ⟨⟨α g, e⟩, by simp only [hρR]⟩

section QMod

variable {G : Type} [Group G]

instance instFactSq {V : Subgroup G} {hV : IsElemAbelian 2 V} :
    Fact (∀ w : IntMod V hV, w * w = 1) :=
  ⟨fun w => by rw [← pow_two]; exact IntMod.sq_eq_one w⟩

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

abbrev ModV : Type := Additive (IntMod V hV)

@[expose] def subZ (Z : Subgroup G) : Submodule (ZMod 2) (ModV hV) where
  carrier := {x | (Additive.toMul x : IntMod V hV).val ∈ Z}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [toMul_add, IntMod.val_mul]
    exact Z.mul_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, toMul_zero, IntMod.val_one]
    exact Z.one_mem
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases SL2Modules.zmod2_cases c with rfl | rfl
    · simp only [zero_smul, toMul_zero, IntMod.val_one]
      exact Z.one_mem
    · simpa only [one_smul] using hx

abbrev QMod (Z : Subgroup G) : Type := ModV hV ⧸ subZ hV Z

variable {hV}

@[expose] def mkE (Z : Subgroup G) (v : ↥V) : QMod hV Z :=
  Submodule.Quotient.mk (Additive.ofMul (IntMod.mk hV v))

theorem mkE_surjective (Z : Subgroup G) : Function.Surjective (mkE (hV := hV) Z) := by
  intro e
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ e
  exact ⟨(Additive.toMul x : IntMod V hV), rfl⟩

theorem mkE_mul (Z : Subgroup G) (v w : ↥V) : mkE (hV := hV) Z (v * w) = mkE Z v + mkE Z w := rfl

theorem mkE_one (Z : Subgroup G) : mkE (hV := hV) Z 1 = 0 := rfl

theorem mkE_eq_zero_iff (Z : Subgroup G) (v : ↥V) : mkE (hV := hV) Z v = 0 ↔ (v : G) ∈ Z :=
  Submodule.Quotient.mk_eq_zero _

@[expose] noncomputable def linAct (hV : IsElemAbelian 2 V)
    (g : ↥(Subgroup.normalizer (V : Set G))) : ModV hV ≃ₗ[ZMod 2] ModV hV :=
  Family.binaryLin (convI hV g)

theorem linAct_val (hV : IsElemAbelian 2 V) (g : ↥(Subgroup.normalizer (V : Set G)))
    (x : ModV hV) :
    (Additive.toMul (linAct hV g x) : IntMod V hV).val =
      (g : G) * (Additive.toMul x : IntMod V hV).val * (g : G)⁻¹ := by
  show (Additive.toMul (Family.binaryLin (convI hV g) x) : IntMod V hV).val = _
  rw [Family.toMul_binaryLin]
  exact convI_apply_val hV g _

theorem mem_subZ {Z : Subgroup G} {x : ModV hV} :
    x ∈ subZ hV Z ↔ (Additive.toMul x : IntMod V hV).val ∈ Z := Iff.rfl

theorem linAct_mem_subZ_iff {Z : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (x : ModV hV) :
    linAct hV ⟨g, hg⟩ x ∈ subZ hV Z ↔ x ∈ subZ hV Z := by
  rw [mem_subZ, mem_subZ, linAct_val]
  exact ((Subgroup.mem_normalizer_iff.mp hgZ) _).symm

theorem map_subZ (Z : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    (subZ hV Z).map (linAct hV ⟨g, hg⟩ : ModV hV →ₗ[ZMod 2] ModV hV) = subZ hV Z := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (linAct_mem_subZ_iff hg hgZ x).mpr hx
  · intro hy
    refine ⟨(linAct hV ⟨g, hg⟩).symm y, ?_, by simp⟩
    rw [← linAct_mem_subZ_iff hg hgZ]
    simpa using hy

variable (hV) in
@[expose] noncomputable def repQ (Z : Subgroup G) :
    ↥(Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G)) →*
      (QMod hV Z ≃ₗ[ZMod 2] QMod hV Z) where
  toFun g := Submodule.Quotient.equiv _ _ (linAct hV ⟨g.1, g.2.1⟩) (map_subZ Z g.2.1 g.2.2)
  map_one' := by
    refine LinearEquiv.ext fun e => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ e
    rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
    show Submodule.Quotient.mk (linAct hV (1 : ↥(Subgroup.normalizer (V : Set G))) x) = _
    have : linAct hV (1 : ↥(Subgroup.normalizer (V : Set G))) = LinearEquiv.refl (ZMod 2) _ := by
      ext y
      show Family.binaryLin (convI hV 1) y = y
      rw [map_one]
      rfl
    rw [this]
    rfl
  map_mul' := by
    intro g h
    refine LinearEquiv.ext fun e => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ e
    simp only [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe,
      LinearEquiv.mul_apply]
    congr 1
    show linAct hV ⟨(g * h).1, _⟩ x = _
    have : linAct hV ⟨(g * h).1, (g * h).2.1⟩ =
        (linAct hV ⟨h.1, h.2.1⟩).trans (linAct hV ⟨g.1, g.2.1⟩) := by
      ext y
      show Family.binaryLin (convI hV ⟨(g * h).1, (g * h).2.1⟩) y =
        Family.binaryLin (convI hV ⟨g.1, g.2.1⟩) (Family.binaryLin (convI hV ⟨h.1, h.2.1⟩) y)
      have hmul : (⟨(g * h).1, (g * h).2.1⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨g.1, g.2.1⟩ * ⟨h.1, h.2.1⟩ := Subtype.ext rfl
      rw [hmul, map_mul, map_mul]
      rfl
    rw [this]
    rfl

theorem repQ_mkE (Z : Subgroup G)
    (g : ↥(Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G))) (v : ↥V) :
    repQ hV Z g (mkE Z v) =
      mkE Z ⟨(g : G) * v * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp g.2.1 v).mp v.2⟩ := by
  simp only [repQ, MonoidHom.coe_mk, OneHom.coe_mk, mkE, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply]
  congr 1

theorem mkE_inv (Z : Subgroup G) (v : ↥V) : mkE (hV := hV) Z v⁻¹ = - mkE Z v := by
  have : mkE (hV := hV) Z v + mkE Z v⁻¹ = 0 := by
    rw [← mkE_mul, mul_inv_cancel, mkE_one]
  exact eq_neg_of_add_eq_zero_right this

theorem mkE_eq_iff (Z : Subgroup G) (a b : ↥V) :
    mkE (hV := hV) Z a = mkE Z b ↔ (a : G) * (b : G)⁻¹ ∈ Z := by
  rw [← sub_eq_zero, sub_eq_add_neg, ← mkE_inv, ← mkE_mul, mkE_eq_zero_iff]
  rfl

end QMod

section Model

@[expose] def toEven (w : orth.W) : ↥(SL2Modules.evenWeight (Fin 5)) :=
  ⟨Multiplicative.toAdd (w : ↥(G6.coreMod 5)).1, G6.mem_coreMod.mp (w : ↥(G6.coreMod 5)).2⟩

theorem toEven_mul (a b : orth.W) : toEven (a * b) = toEven a + toEven b := rfl

theorem toEven_one : toEven 1 = 0 := rfl

theorem toEven_injective : Function.Injective toEven := by
  intro a b h
  have h1 : ((toEven a : ↥(SL2Modules.evenWeight (Fin 5))) : Fin 5 → ZMod 2) =
      (toEven b : Fin 5 → ZMod 2) := congrArg Subtype.val h
  exact Subtype.ext (Multiplicative.toAdd.injective h1)

theorem toEven_surjective : Function.Surjective toEven := by
  intro y
  exact ⟨⟨Multiplicative.ofAdd (y : Fin 5 → ZMod 2), G6.mem_coreMod.mpr y.2⟩, rfl⟩

theorem toEven_act (σ : Equiv.Perm (Fin 5)) (w : orth.W) :
    ((toEven (orth.act σ w) : ↥(SL2Modules.evenWeight (Fin 5))) : Fin 5 → ZMod 2) =
      SL2Modules.permAct σ (toEven w : Fin 5 → ZMod 2) := rfl

end Model

section Bridge

variable {G : Type} [Group G]

theorem conj_mem_of_normalizer {V : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (v : ↥V) : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg v).mp v.2

theorem eq_of_orth_kernel [Finite G] {F V Z C : Subgroup G} (hV : IsElemAbelian 2 V)
    (hFV : F ≤ Subgroup.normalizer (V : Set G)) (hFZ : F ≤ Subgroup.normalizer (Z : Set G))
    (hZC : Z ≤ C) (hCV : C ≤ V) (horth : IsOrthSec F C V)
    (hC : ∀ g ∈ oTwoRes F ⊔ cSecIn F C V, ∀ c ∈ C, g * c * g⁻¹ * c⁻¹ ∈ Z)
    (hQ : ∀ q ∈ cSecIn F C V, ∀ v ∈ V, q * v * q⁻¹ * v⁻¹ ∈ Z)
    (hgen : V ≤ ⁅V, oTwoRes F ⊔ cSecIn F C V⁆ ⊔ Z) : C ≤ Z := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := horth
  have hCF : cSecIn F C V ≤ F := (Subgroup.closure_le F).mpr fun _ hx => hx.1
  have hFpF : oTwoRes F ⊔ cSecIn F C V ≤ F := sup_le (oTwoRes_le F) hCF
  have hFp_iff : ∀ (f : G) (hf : f ∈ F), f ∈ oTwoRes F ⊔ cSecIn F C V ↔
      θ ⟨f, hf⟩ ∈ alternatingGroup (Fin 5) := fun f hf => mem_oTwoRes_sup_iff hθs hθk hf
  set Fp := oTwoRes F ⊔ cSecIn F C V with hFp
  let α : ↥Fp →* ↥(alternatingGroup (Fin 5)) :=
    (θ.comp (Subgroup.inclusion hFpF)).codRestrict _ (fun f => (hFp_iff f.1 (hFpF f.2)).mp f.2)
  have hαval : ∀ f : ↥Fp,
      ((α f : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = θ ⟨f.1, hFpF f.2⟩ :=
    fun f => rfl
  have hαs : Function.Surjective α := by
    intro s
    obtain ⟨f, hf⟩ := hθs s.1
    have hfFp : (f : G) ∈ Fp := (hFp_iff f.1 f.2).mpr (by rw [hf]; exact s.2)
    exact ⟨⟨f.1, hfFp⟩, Subtype.ext (by rw [hαval]; exact hf)⟩
  have hFpN : Fp ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) :=
    le_inf (hFpF.trans hFV) (hFpF.trans hFZ)
  let ρ : ↥Fp →* (QMod hV Z ≃ₗ[ZMod 2] QMod hV Z) :=
    (repQ hV Z).comp (Subgroup.inclusion hFpN)
  have hρ : ∀ (g : ↥Fp) (v : ↥V), ρ g (mkE Z v) =
      mkE Z ⟨(g : G) * v * (g : G)⁻¹, conj_mem_of_normalizer (hFV (hFpF g.2)) v⟩ :=
    fun g v => repQ_mkE Z (Subgroup.inclusion hFpN g) v
  let ι : ↥V →* orth.W :=
    ((MulEquiv.ofBijective β ⟨hsd.inj, hsd.surj⟩).symm).toMonoidHom.comp
      (QuotientGroup.mk' (C.subgroupOf V))
  have hβι : ∀ v : ↥V, β (ι v) = QuotientGroup.mk v := fun v =>
    (MulEquiv.ofBijective β ⟨hsd.inj, hsd.surj⟩).apply_symm_apply _
  have hιeq : ∀ v : ↥V, ι v = 1 ↔ (v : G) ∈ C := by
    intro v
    constructor
    · intro h
      have h1 : β (ι v) = 1 := by rw [h, map_one]
      rw [hβι] at h1
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    · intro h
      apply hsd.inj
      rw [hβι, map_one]
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)
  have hιact : ∀ (g : ↥F) (v : ↥V), ι ⟨(g : G) * v * (g : G)⁻¹,
      conj_mem_of_normalizer (hFV g.2) v⟩ = orth.act (θ g) (ι v) := by
    intro g v
    apply hsd.inj
    obtain ⟨hkx, h2⟩ := hsd.equiv g (ι v) v (hβι v)
    rw [h2, hβι]
  let π0 : ModV hV →+ ↥(SL2Modules.evenWeight (Fin 5)) :=
    { toFun := fun x => toEven (ι (Additive.toMul x : ↥V))
      map_zero' := by
        show toEven (ι 1) = 0
        rw [map_one, toEven_one]
      map_add' := fun x y => by
        show toEven (ι ((Additive.toMul x : ↥V) * (Additive.toMul y : ↥V))) = _
        rw [map_mul, toEven_mul] }
  let π1 : ModV hV →ₗ[ZMod 2] ↥(SL2Modules.evenWeight (Fin 5)) :=
    { toFun := π0
      map_add' := π0.map_add
      map_smul' := fun c e => by
        rcases SL2Modules.zmod2_cases c with rfl | rfl
        · simp only [zero_smul, map_zero]
        · simp only [one_smul, RingHom.id_apply] }
  have hle : subZ hV Z ≤ LinearMap.ker π1 := by
    intro x hx
    rw [LinearMap.mem_ker]
    have h1 : ι (Additive.toMul x : ↥V) = 1 := (hιeq _).mpr (hZC hx)
    show toEven (ι (Additive.toMul x : ↥V)) = 0
    rw [h1, toEven_one]
  let π : QMod hV Z →ₗ[ZMod 2] ↥(SL2Modules.evenWeight (Fin 5)) :=
    { toFun := Quotient.lift (s := Submodule.quotientRel (subZ hV Z)) (fun x => π1 x)
        (fun a b hab => by
          have h1 := (Submodule.quotientRel_def (subZ hV Z)).mp hab
          have h2 : π1 (a - b) = 0 := LinearMap.mem_ker.mp (hle h1)
          have h3 : a = (a - b) + b := by abel
          calc π1 a = π1 ((a - b) + b) := by rw [← h3]
            _ = π1 (a - b) + π1 b := map_add _ _ _
            _ = π1 b := by rw [h2, zero_add])
      map_add' := by
        intro a b
        induction a using Submodule.Quotient.induction_on
        induction b using Submodule.Quotient.induction_on
        exact map_add π1 _ _
      map_smul' := by
        intro c a
        induction a using Submodule.Quotient.induction_on
        exact map_smul π1 c _ }
  have hπmk : ∀ v : ↥V, π (mkE Z v) = toEven (ι v) := fun v => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨w, rfl⟩ := toEven_surjective y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (β w)
    refine ⟨mkE Z x, ?_⟩
    rw [hπmk]
    have : ι x = w := by
      apply hsd.inj
      rw [hβι]
      exact hx
    rw [this]
  have hker : ∀ g : ↥Fp, α g = 1 → ρ g = 1 := by
    intro g hg
    have hg1 : θ ⟨g.1, hFpF g.2⟩ = 1 := by
      have := congrArg Subtype.val hg
      rw [hαval] at this
      exact this
    have hgC : (g : G) ∈ cSecIn F C V := (mem_cSecIn_iff_of_ker hθk (hFpF g.2)).mp hg1
    refine LinearEquiv.ext fun e => ?_
    obtain ⟨v, rfl⟩ := mkE_surjective Z e
    rw [hρ]
    show _ = mkE Z v
    rw [mkE_eq_iff]
    exact hQ g hgC v v.2
  have hfix : ∀ (g : ↥Fp) (e : QMod hV Z), π e = 0 → ρ g e = e := by
    intro g e he
    obtain ⟨v, rfl⟩ := mkE_surjective Z e
    rw [hπmk] at he
    have hvC : (v : G) ∈ C := (hιeq v).mp (toEven_injective (he.trans toEven_one.symm))
    rw [hρ, mkE_eq_iff]
    exact hC g g.2 v hvC
  have hπ : ∀ (g : ↥Fp) (e : QMod hV Z), π (ρ g e) =
      SL2Modules.deletedRep (alternatingGroup (Fin 5)) (Fin 5) (α g) (π e) := by
    intro g e
    obtain ⟨v, rfl⟩ := mkE_surjective Z e
    rw [hρ, hπmk, hπmk]
    apply Subtype.ext
    rw [SL2Modules.deletedRep_apply]
    have h1 := hιact ⟨g.1, hFpF g.2⟩ v
    have e1 : MulAction.toPerm (α g) = θ ⟨g.1, hFpF g.2⟩ := by
      rw [← hαval]
      rfl
    rw [e1, h1, toEven_act]
  have hgen : Submodule.span (ZMod 2)
      (Set.range fun p : ↥Fp × QMod hV Z => ρ p.1 p.2 - p.2) = ⊤ := by
    set S₀ := Submodule.span (ZMod 2)
      (Set.range fun p : ↥Fp × QMod hV Z => ρ p.1 p.2 - p.2) with hS₀
    let T : Subgroup G :=
      { carrier := {x | ∃ hx : x ∈ V, mkE Z ⟨x, hx⟩ ∈ S₀}
        one_mem' := ⟨V.one_mem, by
          have : mkE (hV := hV) Z (1 : ↥V) = 0 := mkE_one Z
          show mkE Z (1 : ↥V) ∈ S₀
          rw [this]
          exact S₀.zero_mem⟩
        mul_mem' := fun {x y} hx hy => by
          obtain ⟨hxV, hxm⟩ := hx
          obtain ⟨hyV, hym⟩ := hy
          refine ⟨V.mul_mem hxV hyV, ?_⟩
          show mkE Z (⟨x, hxV⟩ * ⟨y, hyV⟩ : ↥V) ∈ S₀
          rw [mkE_mul]
          exact S₀.add_mem hxm hym
        inv_mem' := fun {x} hx => by
          obtain ⟨hxV, hxm⟩ := hx
          refine ⟨V.inv_mem hxV, ?_⟩
          show mkE Z (⟨x, hxV⟩⁻¹ : ↥V) ∈ S₀
          rw [mkE_inv]
          exact S₀.neg_mem hxm }
    have hcomm : ⁅V, Fp⁆ ≤ T := by
      rw [Subgroup.commutator_le]
      intro v hv f hf
      have hfN : f ∈ Subgroup.normalizer (V : Set G) := hFV (hFpF hf)
      have hfv : f * v * f⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hfN v).mp hv
      have hx : ⁅v, f⁆ ∈ V := by
        have : ⁅v, f⁆ = (f * v * f⁻¹ * v⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact V.inv_mem (V.mul_mem hfv (V.inv_mem hv))
      refine ⟨hx, ?_⟩
      have e1 : (⟨⁅v, f⁆, hx⟩ : ↥V) = (⟨f * v * f⁻¹, hfv⟩ * (⟨v, hv⟩ : ↥V)⁻¹)⁻¹ := by
        apply Subtype.ext
        simp only [commutatorElement_def]
        simp only [Subgroup.coe_inv, Subgroup.coe_mul, mul_inv_rev, inv_inv]
        group
      show mkE Z (⟨⁅v, f⁆, hx⟩ : ↥V) ∈ S₀
      rw [e1, mkE_inv, mkE_mul, mkE_inv]
      have h2 : ρ ⟨f, hf⟩ (mkE Z ⟨v, hv⟩) - mkE Z ⟨v, hv⟩ ∈ S₀ :=
        Submodule.subset_span ⟨(⟨f, hf⟩, mkE Z ⟨v, hv⟩), rfl⟩
      rw [hρ] at h2
      have e2 : -(mkE (hV := hV) Z (⟨f * v * f⁻¹, hfv⟩ : ↥V) + -mkE (hV := hV) Z (⟨v, hv⟩ : ↥V)) =
          -(mkE (hV := hV) Z (⟨f * v * f⁻¹, hfv⟩ : ↥V) - mkE (hV := hV) Z (⟨v, hv⟩ : ↥V)) := by
        rw [sub_eq_add_neg]
      rw [e2]
      exact S₀.neg_mem h2
    have hZT : Z ≤ T := by
      intro z hz
      have hzV : z ∈ V := hCV (hZC hz)
      refine ⟨hzV, ?_⟩
      have : mkE (hV := hV) Z (⟨z, hzV⟩ : ↥V) = 0 := (mkE_eq_zero_iff (hV := hV) Z _).mpr hz
      rw [this]
      exact S₀.zero_mem
    have hVT : V ≤ T := hgen.trans (sup_le hcomm hZT)
    rw [eq_top_iff]
    intro e _
    obtain ⟨v, rfl⟩ := mkE_surjective Z e
    obtain ⟨hx, hm⟩ := hVT v.2
    exact hm
  have hker0 := kernel_bot_of_alt5 α hαs ρ hker π hπs hπ hfix hgen
  intro c hc
  have hcV : c ∈ V := hCV hc
  have h1 : π (mkE Z ⟨c, hcV⟩) = 0 := by
    rw [hπmk, (hιeq ⟨c, hcV⟩).mpr hc, toEven_one]
  have h2 : mkE Z ⟨c, hcV⟩ ∈ LinearMap.ker π := h1
  rw [hker0, Submodule.mem_bot] at h2
  exact (mkE_eq_zero_iff Z _).mp h2

end Bridge

end CFSG.Quasithin.F53B3.O1
