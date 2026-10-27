module

public import CFSG.RankThree.GF2n.Tim81.HBar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Rank
public import CFSG.Quasithin.Background.SmithB45U33Coind
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.RankThree.FFModules.BinaryTransport

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7
open scoped commutatorElement

variable {G : Type} [Group G] {V H : Subgroup G}

@[expose] noncomputable def conjH (V H : Subgroup G) :
    ↥H →* MulAut ↥(Tim79a.xOf V H) :=
  (conjAct (Tim79a.xOf V H)).comp (Subgroup.inclusion (Tim79a.H_le_normalizer_xOf V H))

theorem conjH_apply_coe (h : ↥H) (w : ↥(Tim79a.xOf V H)) :
    ((conjH V H h w : ↥(Tim79a.xOf V H)) : G) = (h : G) * w * (h : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe (Tim79a.xOf V H)
    (Subgroup.inclusion (Tim79a.H_le_normalizer_xOf V H) h) w

theorem conjH_eq_one_of_mem_kOf {z : ↥H} (hz : z ∈ (kOf V H).subgroupOf H) :
    conjH V H z = 1 := by
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [conjH_apply_coe, MulAut.one_apply]
  have hmem : (z : G) ∈ Subgroup.centralizer (Tim79a.xOf V H : Set G) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).2
  have hwz : (w : G) * (z : G) = (z : G) * (w : G) :=
    Subgroup.mem_centralizer_iff.mp hmem w w.2
  rw [← hwz, mul_assoc, mul_inv_cancel, mul_one]

@[expose] noncomputable def conjW (V H : Subgroup G) :
    HBar V H →* MulAut ↥(Tim79a.xOf V H) :=
  QuotientGroup.lift ((kOf V H).subgroupOf H) (conjH V H) fun _ hz =>
    MonoidHom.mem_ker.mpr (conjH_eq_one_of_mem_kOf hz)

theorem conjW_apply (z : ↥H) (w : ↥(Tim79a.xOf V H)) :
    conjW V H (piK V H z) w = conjH V H z w := by
  rw [conjW, piK, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

@[reducible] noncomputable def moduleOfElemAbelian
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)) :
    Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
  CFSG.RankThree.FFModules.moduleOfSq (E := IntMod (Tim79a.xOf V H) hW)
    fun w => IntMod.sq_eq_one w

@[expose] def toW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (v : Additive (IntMod (Tim79a.xOf V H) hW)) : ↥(Tim79a.xOf V H) :=
  @Additive.toMul (IntMod (Tim79a.xOf V H) hW) v

@[expose] def ofW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (w : ↥(Tim79a.xOf V H)) : Additive (IntMod (Tim79a.xOf V H) hW) :=
  @Additive.ofMul (IntMod (Tim79a.xOf V H) hW) w

@[simp] theorem toW_ofW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (w : ↥(Tim79a.xOf V H)) : toW hW (ofW hW w) = w := rfl

@[simp] theorem ofW_toW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (v : Additive (IntMod (Tim79a.xOf V H) hW)) : ofW hW (toW hW v) = v := rfl

theorem toW_injective (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)) :
    Function.Injective (toW hW) := fun x y hxy => by
  rw [← ofW_toW hW x, ← ofW_toW hW y, hxy]

theorem ofW_injective (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)) :
    Function.Injective (ofW hW) := fun x y h => by
  have := congrArg (toW hW) h
  simpa using this

@[simp] theorem toW_add (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (x y : Additive (IntMod (Tim79a.xOf V H) hW)) :
    toW hW (x + y) = toW hW x * toW hW y := rfl

@[simp] theorem toW_zero (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)) :
    toW hW (0 : Additive (IntMod (Tim79a.xOf V H) hW)) = 1 := rfl

@[simp] theorem ofW_mul (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (a b : ↥(Tim79a.xOf V H)) :
    ofW hW (a * b) = ofW hW a + ofW hW b := rfl

@[simp] theorem ofW_inv (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    (a : ↥(Tim79a.xOf V H)) : ofW hW a⁻¹ = -ofW hW a := rfl

@[simp] theorem ofW_one (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)) :
    ofW hW (1 : ↥(Tim79a.xOf V H)) = 0 := rfl

variable (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
variable [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]

@[expose] noncomputable def repW {X : Type} [Group X] (ψ : HBar V H ≃* X) :
    Representation (ZMod 2) X (Additive (IntMod (Tim79a.xOf V H) hW)) :=
  (CFSG.RankThree.FFModules.autRep (IntMod (Tim79a.xOf V H) hW)).comp
    ((conjW V H).comp ψ.symm.toMonoidHom)

theorem repW_apply {X : Type} [Group X] (ψ : HBar V H ≃* X) (x : X)
    (v : Additive (IntMod (Tim79a.xOf V H) hW)) :
    repW hW ψ x v = ofW hW (conjW V H (ψ.symm x) (toW hW v)) := rfl

theorem repW_apply_piK {X : Type} [Group X] (ψ : HBar V H ≃* X) (z : ↥H)
    (v : Additive (IntMod (Tim79a.xOf V H) hW)) :
    repW hW ψ (ψ (piK V H z)) v = ofW hW (conjH V H z (toW hW v)) := by
  rw [repW_apply, MulEquiv.symm_apply_apply, conjW_apply]

theorem repW_apply_piK_ofMul {X : Type} [Group X] (ψ : HBar V H ≃* X) (z : ↥H)
    (w : ↥(Tim79a.xOf V H)) :
    repW hW ψ (ψ (piK V H z)) (ofW hW w) = ofW hW (conjH V H z w) := by
  rw [repW_apply_piK, toW_ofW]

theorem mem_commutator_xOf {z : ↥H} {w : ↥(Tim79a.xOf V H)} :
    ⁅(z : G), (w : G)⁆ ∈ Tim79a.xOf V H := by
  have hzN : (z : G) ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Tim79a.H_le_normalizer_xOf V H z.2
  have hzw : (z : G) * (w : G) * (z : G)⁻¹ ∈ Tim79a.xOf V H :=
    (Subgroup.mem_normalizer_iff.mp hzN (w : G)).mp w.2
  rw [commutatorElement_def]
  exact (Tim79a.xOf V H).mul_mem hzw ((Tim79a.xOf V H).inv_mem w.2)

theorem repW_apply_piK_sub {X : Type} [Group X] (ψ : HBar V H ≃* X) (z : ↥H)
    (w : ↥(Tim79a.xOf V H)) :
    repW hW ψ (ψ (piK V H z)) (ofW hW w) - ofW hW w =
      ofW hW ⟨⁅(z : G), (w : G)⁆, mem_commutator_xOf (z := z) (w := w)⟩ := by
  rw [repW_apply_piK, toW_ofW, sub_eq_add_neg, ← ofW_inv, ← ofW_mul]
  apply congrArg (ofW hW)
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, conjH_apply_coe]
  change (z : G) * (w : G) * (z : G)⁻¹ * (w : G)⁻¹ = ⁅(z : G), (w : G)⁆
  rw [commutatorElement_def]

@[expose] def subgroupOfSubW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))) : Subgroup G where
  carrier := {g | ∃ hg : g ∈ Tim79a.xOf V H, ofW hW ⟨g, hg⟩ ∈ U}
  one_mem' := ⟨(Tim79a.xOf V H).one_mem, by
    have h : (ofW hW ⟨(1 : G), (Tim79a.xOf V H).one_mem⟩ :
        Additive (IntMod (Tim79a.xOf V H) hW)) = 0 := rfl
    rw [h]
    exact U.zero_mem⟩
  mul_mem' := by
    rintro g h ⟨hg, hgu⟩ ⟨hh, hhu⟩
    refine ⟨(Tim79a.xOf V H).mul_mem hg hh, ?_⟩
    have h : (ofW hW ⟨g * h, (Tim79a.xOf V H).mul_mem hg hh⟩ :
        Additive (IntMod (Tim79a.xOf V H) hW)) =
        ofW hW ⟨g, hg⟩ + ofW hW ⟨h, hh⟩ := by
      rw [← ofW_mul]
      exact congrArg (ofW hW) (Subtype.ext rfl)
    rw [h]
    exact U.add_mem hgu hhu
  inv_mem' := by
    rintro g ⟨hg, hgu⟩
    refine ⟨(Tim79a.xOf V H).inv_mem hg, ?_⟩
    have h : (ofW hW ⟨g⁻¹, (Tim79a.xOf V H).inv_mem hg⟩ :
        Additive (IntMod (Tim79a.xOf V H) hW)) = -ofW hW ⟨g, hg⟩ := by
      rw [← ofW_inv]
      exact congrArg (ofW hW) (Subtype.ext rfl)
    rw [h]
    exact U.neg_mem hgu

@[expose] def subW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] (E : Subgroup G) :
    Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) where
  carrier := {x | (toW hW x : G) ∈ E}
  zero_mem' := by
    show (toW hW (0 : Additive (IntMod (Tim79a.xOf V H) hW)) : G) ∈ E
    have h : toW hW (0 : Additive (IntMod (Tim79a.xOf V H) hW)) = 1 := rfl
    rw [h]
    exact E.one_mem
  add_mem' := by
    intro x y hx hy
    show (toW hW (x + y) : G) ∈ E
    rw [toW_add]
    simpa using E.mul_mem hx hy
  smul_mem' := by
    intro c x hx
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · simpa using E.one_mem
    · simpa using hx

theorem mem_subW_iff (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] {E : Subgroup G}
    {w : ↥(Tim79a.xOf V H)} :
    ofW hW w ∈ subW hW E ↔ (w : G) ∈ E :=
  Iff.rfl

theorem mem_subgroupOfSubW_iff (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))} {g : G} :
    g ∈ subgroupOfSubW hW U ↔ ∃ hg : g ∈ Tim79a.xOf V H, ofW hW ⟨g, hg⟩ ∈ U :=
  Iff.rfl

theorem subW_mono {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] {E F : Subgroup G}
    (hEF : E ≤ F) : subW hW E ≤ subW hW F :=
  fun x hx => hEF hx

theorem subW_bot (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] :
    subW hW (⊥ : Subgroup G) = ⊥ := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_bot]
    have h : (toW hW x : G) = 1 := Subgroup.mem_bot.mp hx
    have h' : toW hW x = 1 := Subtype.ext h
    rw [← ofW_toW hW x, h', ofW_one]
  · intro hx
    rw [Submodule.mem_bot] at hx
    rw [hx]
    exact (subW hW ⊥).zero_mem

theorem subW_inf (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] (E F : Subgroup G) :
    subW hW (E ⊓ F) = subW hW E ⊓ subW hW F := by
  ext x
  exact Subgroup.mem_inf

theorem subW_subgroupOfSubW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))) :
    subW hW (subgroupOfSubW hW U) = U := by
  ext x
  change (toW hW x : G) ∈ subgroupOfSubW hW U ↔ x ∈ U
  rw [mem_subgroupOfSubW_iff]
  constructor
  · rintro ⟨hg, hx⟩
    have e : ofW hW ⟨(toW hW x : G), hg⟩ = x := by
      calc ofW hW ⟨(toW hW x : G), hg⟩ = ofW hW (toW hW x) :=
            congrArg (ofW hW) (Subtype.ext rfl)
        _ = x := ofW_toW hW x
    rwa [e] at hx
  · intro hx
    exact ⟨(toW hW x).2, by
      rw [show ofW hW ⟨(toW hW x : G), (toW hW x).2⟩ = x from by
        calc ofW hW ⟨(toW hW x : G), (toW hW x).2⟩ = ofW hW (toW hW x) :=
              congrArg (ofW hW) (Subtype.ext rfl)
          _ = x := ofW_toW hW x]
      exact hx⟩

theorem natCard_subW (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))] {E : Subgroup G}
    (hE : E ≤ Tim79a.xOf V H) : Nat.card (subW hW E) = Nat.card E := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨(toW hW x.1 : G), x.2⟩
      invFun := fun e => ⟨ofW hW ⟨e.1, hE e.2⟩, by
        change (toW hW (ofW hW ⟨e.1, hE e.2⟩) : G) ∈ E
        rw [toW_ofW]
        exact e.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    refine Subtype.ext ?_
    calc ofW hW ⟨(toW hW x.1 : G), hE x.2⟩ = ofW hW (toW hW x.1) :=
          congrArg (ofW hW) (Subtype.ext rfl)
      _ = x.1 := ofW_toW hW x.1
  · intro e
    refine Subtype.ext ?_
    rfl

section General

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Γ : Type} [Group Γ]
  (ρ : Representation (ZMod 2) Γ V) (X₀ : Submodule (ZMod 2) V)
  (hX₀ : ∀ g, ∀ x ∈ X₀, ρ g x ∈ X₀) (A : Subgroup Γ)

private theorem map_fixedSub_subRep :
    (fixedSub (CFSG.Quasithin.B45U33.subRep ρ X₀ hX₀) A).map X₀.subtype =
      fixedSub ρ A ⊓ X₀ := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_fixedSub]
      intro a ha
      have h := congrArg (fun x : X₀ => (x : V)) ((mem_fixedSub.mp hu) a ha)
      rwa [CFSG.Quasithin.B45U33.subRep_apply] at h
    · rw [Submodule.subtype_apply]
      exact u.2
  · rintro ⟨hy, hyX⟩
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    have hy' : ∀ a ∈ A, ρ a y = y := mem_fixedSub.mp hy
    change ∀ a ∈ A, CFSG.Quasithin.B45U33.subRep ρ X₀ hX₀ a ⟨y, hyX⟩ = ⟨y, hyX⟩
    intro a ha
    apply Subtype.ext
    rw [CFSG.Quasithin.B45U33.subRep_apply]
    exact hy' a ha

end General

section Main

variable {X : Type} [Group X] (ψ : HBar V H ≃* X)

theorem normalizer_subW_iff {E : Subgroup G} (hE : E ≤ Tim79a.xOf V H) :
    H ≤ Subgroup.normalizer (E : Set G) ↔
      ∀ x : X, ∀ v ∈ subW hW E, repW hW ψ x v ∈ subW hW E := by
  constructor
  · intro hN x v hv
    obtain ⟨y, rfl⟩ := ψ.surjective x
    obtain ⟨z, rfl⟩ := piK_surjective V H y
    rw [repW_apply_piK, mem_subW_iff, conjH_apply_coe]
    have hv' : (toW hW v : G) ∈ E := hv
    exact (Subgroup.mem_normalizer_iff.mp (hN z.2) (toW hW v)).mp hv'
  · intro hinv z hz
    have hconj : ∀ z : ↥H, ∀ e ∈ E, ((z : G) * e * (z : G)⁻¹) ∈ E := by
      intro z e he
      have hv : ofW hW ⟨e, hE he⟩ ∈ subW hW E := (mem_subW_iff hW).mpr he
      have h := hinv (ψ (piK V H z)) _ hv
      rw [repW_apply_piK, mem_subW_iff, conjH_apply_coe] at h
      simpa using h
    refine Subgroup.mem_normalizer_iff.mpr fun e => ⟨fun he => hconj ⟨z, hz⟩ e he, fun he => ?_⟩
    have h := hconj ⟨z⁻¹, H.inv_mem hz⟩ ((z : G) * e * (z : G)⁻¹) he
    have h' : (z : G)⁻¹ * ((z : G) * e * (z : G)⁻¹) * (z : G) ∈ E := by
      simpa using h
    rwa [show (z : G)⁻¹ * ((z : G) * e * (z : G)⁻¹) * (z : G) = e from by group] at h'

theorem fixedSub_repW {S : Subgroup G} (hS : S ≤ H) :
    fixedSub (repW hW ψ) ((imgK V H S).map ψ) =
      subW hW (Tim79a.xOf V H ⊓ Subgroup.centralizer (S : Set G)) := by
  ext v
  rw [mem_fixedSub]
  constructor
  · intro hv
    change (toW hW v : G) ∈ Tim79a.xOf V H ⊓ Subgroup.centralizer (S : Set G)
    refine Subgroup.mem_inf.mpr ⟨(toW hW v).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hmem : ψ (piK V H ⟨s, hS hs⟩) ∈ (imgK V H S).map ψ := by
      refine Subgroup.mem_map.mpr ⟨piK V H ⟨s, hS hs⟩, ?_, rfl⟩
      exact (mem_imgK_iff).mpr ⟨⟨s, hS hs⟩, hs, rfl⟩
    have h := hv _ hmem
    have h2 : (conjH V H ⟨s, hS hs⟩ (toW hW v) : G) = (toW hW v : G) := by
      have h' : toW hW (repW hW ψ (ψ (piK V H ⟨s, hS hs⟩)) v) = toW hW v :=
        congrArg (toW hW) h
      rw [repW_apply_piK, toW_ofW] at h'
      exact congrArg (fun w : ↥(Tim79a.xOf V H) => (w : G)) h'
    rw [conjH_apply_coe] at h2
    calc (s : G) * (toW hW v : G)
        = ((s : G) * (toW hW v : G) * (s : G)⁻¹) * (s : G) := by group
      _ = (toW hW v : G) * (s : G) := by rw [h2]
  · intro hv a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    rw [mem_imgK_iff] at hy
    obtain ⟨z, hzS, rfl⟩ := hy
    rw [← ofW_toW hW v]
    change repW hW ψ (ψ (piK V H z)) (ofW hW (toW hW v)) = ofW hW (toW hW v)
    rw [repW_apply_piK]
    have hw : (toW hW v : G) ∈ Subgroup.centralizer (S : Set G) :=
      (Subgroup.mem_inf.mp ((mem_subW_iff hW).mp hv)).2
    have hz : ((z : G) * (toW hW v : G) * (z : G)⁻¹) = (toW hW v : G) := by
      have hc := Subgroup.mem_centralizer_iff.mp hw (z : G) hzS
      calc (z : G) * (toW hW v : G) * (z : G)⁻¹
          = ((toW hW v : G) * (z : G)) * (z : G)⁻¹ := by rw [hc]
        _ = (toW hW v : G) := by group
    rw [toW_ofW, show conjH V H z (toW hW v) = toW hW v from by
      refine Subtype.ext ?_
      rw [conjH_apply_coe]
      exact hz]

theorem commSub_repW {S : Subgroup G} (hS : S ≤ H) :
    commSub (repW hW ψ) ((imgK V H S).map ψ) =
      subW hW ⁅Tim79a.xOf V H, S⁆ := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun a => iSup_le fun ha => ?_
    rintro x ⟨v, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨z, hzS, rfl⟩ := (mem_imgK_iff).mp hy
    change repW hW ψ (ψ (piK V H z)) (ofW hW (toW hW v)) -
      ofW hW (toW hW v) ∈ subW hW ⁅Tim79a.xOf V H, S⁆
    rw [repW_apply_piK_sub, mem_subW_iff]
    change ⁅(z : G), ((toW hW v : ↥(Tim79a.xOf V H)) : G)⁆ ∈ ⁅Tim79a.xOf V H, S⁆
    rw [show ⁅(z : G), ((toW hW v : ↥(Tim79a.xOf V H)) : G)⁆ =
        (⁅((toW hW v : ↥(Tim79a.xOf V H)) : G), (z : G)⁆)⁻¹ from
      (commutatorElement_inv ((toW hW v : ↥(Tim79a.xOf V H)) : G) (z : G)).symm]
    exact (⁅Tim79a.xOf V H, S⁆).inv_mem
      (Subgroup.commutator_mem_commutator (toW hW v).2 hzS)
  · have hcomm : ⁅Tim79a.xOf V H, S⁆ ≤
        subgroupOfSubW hW (commSub (repW hW ψ) ((imgK V H S).map ψ)) := by
      rw [Subgroup.commutator_le]
      intro w hw s hs
      have hWN : S ≤ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
        hS.trans (Tim79a.H_le_normalizer_xOf V H)
      have hWmem : ⁅w, s⁆ ∈ Tim79a.xOf V H :=
        Subgroup.commutator_le.mp ((Subgroup.le_normalizer_iff_commutator_le_left).mp hWN) w hw s hs
      let U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
        commSub (repW hW ψ) ((imgK V H S).map ψ)
      change ⁅w, s⁆ ∈ subgroupOfSubW hW U
      rw [mem_subgroupOfSubW_iff]
      refine ⟨hWmem, ?_⟩
      change ofW hW ⟨⁅w, s⁆, hWmem⟩ ∈ U
      have hgen : repW hW ψ (ψ (piK V H ⟨s, hS hs⟩)) (ofW hW ⟨w, hw⟩) -
          ofW hW ⟨w, hw⟩ ∈ U := by
        refine Submodule.mem_iSup_of_mem (ψ (piK V H ⟨s, hS hs⟩)) ?_
        refine Submodule.mem_iSup_of_mem ?_ ⟨ofW hW ⟨w, hw⟩, rfl⟩
        refine Subgroup.mem_map.mpr ⟨piK V H ⟨s, hS hs⟩, ?_, rfl⟩
        exact (mem_imgK_iff).mpr ⟨⟨s, hS hs⟩, hs, rfl⟩
      have hrep : repW hW ψ (ψ (piK V H ⟨s, hS hs⟩)) (ofW hW ⟨w, hw⟩) =
          ofW hW (conjH V H ⟨s, hS hs⟩ ⟨w, hw⟩) := by
        rw [repW_apply_piK, toW_ofW]
      have hval : (⟨⁅w, s⁆, hWmem⟩ : ↥(Tim79a.xOf V H)) =
          ((conjH V H ⟨s, hS hs⟩ ⟨w, hw⟩) * ⟨w, hw⟩⁻¹)⁻¹ := by
        refine Subtype.ext ?_
        change ⁅w, s⁆ = (((conjH V H ⟨s, hS hs⟩ ⟨w, hw⟩) * ⟨w, hw⟩⁻¹ : ↥(Tim79a.xOf V H)) : G)⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_inv, conjH_apply_coe, commutatorElement_def]
        group
      have heq : ofW hW ⟨⁅w, s⁆, hWmem⟩ =
          -(repW hW ψ (ψ (piK V H ⟨s, hS hs⟩)) (ofW hW ⟨w, hw⟩) - ofW hW ⟨w, hw⟩) := by
        rw [hrep]
        rw [show ofW hW ⟨⁅w, s⁆, hWmem⟩ =
            ofW hW ((conjH V H ⟨s, hS hs⟩ ⟨w, hw⟩) * ⟨w, hw⟩⁻¹)⁻¹ from
          congrArg (ofW hW) hval]
        rw [ofW_inv, ofW_mul, ofW_inv, sub_eq_add_neg]
      exact heq ▸ U.neg_mem hgen
    have hle := subW_mono (hW := hW) hcomm
    rwa [subW_subgroupOfSubW hW] at hle

@[expose] noncomputable def subRepW {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) :
    Representation (ZMod 2) X (subW hW W₀) :=
  CFSG.Quasithin.B45U33.subRep (repW hW ψ) (subW hW W₀)
    ((normalizer_subW_iff hW ψ hW₀).mp hN)

theorem fixedSub_subRepW {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {S : Subgroup G} (hS : S ≤ H) :
    (fixedSub (subRepW hW ψ hW₀ hN) ((imgK V H S).map ψ)).map (subW hW W₀).subtype =
      subW hW (W₀ ⊓ Subgroup.centralizer (S : Set G)) := by
  unfold subRepW
  rw [map_fixedSub_subRep, fixedSub_repW hW ψ hS, ← subW_inf]
  congr 1
  have h1 : Subgroup.centralizer (S : Set G) ⊓ W₀ =
      W₀ ⊓ Subgroup.centralizer (S : Set G) := inf_comm _ _
  calc (Tim79a.xOf V H ⊓ Subgroup.centralizer (S : Set G)) ⊓ W₀
      = Tim79a.xOf V H ⊓ (Subgroup.centralizer (S : Set G) ⊓ W₀) :=
          inf_assoc _ _ _
    _ = Tim79a.xOf V H ⊓ (W₀ ⊓ Subgroup.centralizer (S : Set G)) := by rw [h1]
    _ = (Tim79a.xOf V H ⊓ W₀) ⊓ Subgroup.centralizer (S : Set G) :=
          (inf_assoc _ _ _).symm
    _ = W₀ ⊓ Subgroup.centralizer (S : Set G) := by
          congr 1
          exact inf_eq_right.mpr hW₀

private theorem commSub_subRepW_le {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {S : Subgroup G} :
    (commSub (subRepW hW ψ hW₀ hN) ((imgK V H S).map ψ)).map (subW hW W₀).subtype ≤
      subW hW ⁅W₀, S⁆ := by
  let X₀ := subW hW W₀
  let ρ₀ := subRepW hW ψ hW₀ hN
  let A := (imgK V H S).map ψ.toMonoidHom
  rw [Submodule.map_le_iff_le_comap]
  refine iSup_le fun a => iSup_le fun ha => ?_
  rintro x ⟨u, rfl⟩
  change X₀.subtype ((ρ₀ a - 1) u) ∈ subW hW ⁅W₀, S⁆
  have hcoe : X₀.subtype ((ρ₀ a - 1) u) =
      repW hW ψ a (u : Additive (IntMod (Tim79a.xOf V H) hW)) -
        (u : Additive (IntMod (Tim79a.xOf V H) hW)) := by
    rfl
  rw [hcoe]
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨z, hzS, rfl⟩ := (mem_imgK_iff).mp hy
  change repW hW ψ (ψ (piK V H z)) (u : Additive (IntMod (Tim79a.xOf V H) hW)) -
    (u : Additive (IntMod (Tim79a.xOf V H) hW)) ∈ subW hW ⁅W₀, S⁆
  rw [← ofW_toW hW (u : Additive (IntMod (Tim79a.xOf V H) hW)), repW_apply_piK_sub,
    mem_subW_iff]
  have hw₀ : ((toW hW (u : Additive (IntMod (Tim79a.xOf V H) hW)) :
      ↥(Tim79a.xOf V H)) : G) ∈ W₀ := by
    have h := u.2
    rwa [← ofW_toW hW (u : Additive (IntMod (Tim79a.xOf V H) hW)), mem_subW_iff] at h
  change ⁅(z : G), ((toW hW (u : Additive (IntMod (Tim79a.xOf V H) hW)) :
    ↥(Tim79a.xOf V H)) : G)⁆ ∈ ⁅W₀, S⁆
  rw [show ⁅(z : G), ((toW hW (u : Additive (IntMod (Tim79a.xOf V H) hW)) :
      ↥(Tim79a.xOf V H)) : G)⁆ =
      (⁅((toW hW (u : Additive (IntMod (Tim79a.xOf V H) hW)) : ↥(Tim79a.xOf V H)) : G),
        (z : G)⁆)⁻¹ from
    (commutatorElement_inv _ _).symm]
  exact (⁅W₀, S⁆).inv_mem (Subgroup.commutator_mem_commutator hw₀ hzS)

private theorem subW_commutator_le_commSub {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {S : Subgroup G} (hS : S ≤ H) :
    subW hW ⁅W₀, S⁆ ≤
      (commSub (subRepW hW ψ hW₀ hN) ((imgK V H S).map ψ)).map (subW hW W₀).subtype := by
  let X₀ := subW hW W₀
  let ρ₀ := subRepW hW ψ hW₀ hN
  let A := (imgK V H S).map ψ.toMonoidHom
  let U : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    (commSub ρ₀ A).map X₀.subtype
  have hcomm : ⁅W₀, S⁆ ≤ subgroupOfSubW hW U := by
    rw [Subgroup.commutator_le]
    intro w hw s hs
    have hN₀ : S ≤ Subgroup.normalizer (W₀ : Set G) := hS.trans hN
    have hW₀mem : ⁅w, s⁆ ∈ W₀ :=
      Subgroup.commutator_le.mp ((Subgroup.le_normalizer_iff_commutator_le_left).mp hN₀) w hw s hs
    have hWmem : ⁅w, s⁆ ∈ Tim79a.xOf V H := hW₀ hW₀mem
    change ⁅w, s⁆ ∈ subgroupOfSubW hW U
    rw [mem_subgroupOfSubW_iff]
    refine ⟨hWmem, ?_⟩
    change ofW hW ⟨⁅w, s⁆, hWmem⟩ ∈ U
    let u : ↥X₀ := ⟨ofW hW ⟨w, hW₀ hw⟩, (mem_subW_iff hW).mpr hw⟩
    let a : X := ψ (piK V H ⟨s, hS hs⟩)
    have hgen : subRepW hW ψ hW₀ hN a u - u ∈ commSub ρ₀ A := by
      refine Submodule.mem_iSup_of_mem a ?_
      refine Submodule.mem_iSup_of_mem ?_ ⟨u, rfl⟩
      refine Subgroup.mem_map.mpr ⟨piK V H ⟨s, hS hs⟩, ?_, rfl⟩
      exact (mem_imgK_iff).mpr ⟨⟨s, hS hs⟩, hs, rfl⟩
    have hrep : repW hW ψ a (u : Additive (IntMod (Tim79a.xOf V H) hW)) =
        ofW hW (conjH V H ⟨s, hS hs⟩ ⟨w, hW₀ hw⟩) := by
      change repW hW ψ (ψ (piK V H ⟨s, hS hs⟩)) (ofW hW ⟨w, hW₀ hw⟩) = _
      rw [repW_apply_piK, toW_ofW]
    have hcoe : X₀.subtype (subRepW hW ψ hW₀ hN a u - u) =
        repW hW ψ a (u : Additive (IntMod (Tim79a.xOf V H) hW)) -
          (u : Additive (IntMod (Tim79a.xOf V H) hW)) := rfl
    have hval : (⟨⁅w, s⁆, hWmem⟩ : ↥(Tim79a.xOf V H)) =
        ((conjH V H ⟨s, hS hs⟩ ⟨w, hW₀ hw⟩) * ⟨w, hW₀ hw⟩⁻¹)⁻¹ := by
      refine Subtype.ext ?_
      change ⁅w, s⁆ = (((conjH V H ⟨s, hS hs⟩ ⟨w, hW₀ hw⟩) * ⟨w, hW₀ hw⟩⁻¹ :
        ↥(Tim79a.xOf V H)) : G)⁻¹
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjH_apply_coe, commutatorElement_def]
      group
    have heq : ofW hW ⟨⁅w, s⁆, hWmem⟩ = X₀.subtype (-(subRepW hW ψ hW₀ hN a u - u)) := by
      rw [map_neg, hcoe, hrep]
      change ofW hW ⟨⁅w, s⁆, hWmem⟩ =
        -(ofW hW (conjH V H ⟨s, hS hs⟩ ⟨w, hW₀ hw⟩) - ofW hW ⟨w, hW₀ hw⟩)
      rw [show ofW hW ⟨⁅w, s⁆, hWmem⟩ =
          ofW hW ((conjH V H ⟨s, hS hs⟩ ⟨w, hW₀ hw⟩) * ⟨w, hW₀ hw⟩⁻¹)⁻¹ from
        congrArg (ofW hW) hval]
      rw [ofW_inv, ofW_mul, ofW_inv, sub_eq_add_neg]
    exact Submodule.mem_map.mpr ⟨-(subRepW hW ψ hW₀ hN a u - u), (commSub ρ₀ A).neg_mem hgen,
      heq.symm⟩
  have hle := subW_mono (hW := hW) hcomm
  rwa [subW_subgroupOfSubW hW] at hle

theorem commSub_subRepW {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) {S : Subgroup G} (hS : S ≤ H) :
    (commSub (subRepW hW ψ hW₀ hN) ((imgK V H S).map ψ)).map (subW hW W₀).subtype =
      subW hW ⁅W₀, S⁆ := by
  exact le_antisymm (commSub_subRepW_le hW ψ hW₀ hN)
    (subW_commutator_le_commSub hW ψ hW₀ hN hS)

private theorem nontrivial_subW {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hW₀ne : W₀ ≠ ⊥) : Nontrivial ↥(subW hW W₀) := by
  haveI : Nontrivial ↥W₀ := (Subgroup.nontrivial_iff_ne_bot W₀).mpr hW₀ne
  obtain ⟨w₀, hw₀⟩ := exists_ne (1 : ↥W₀)
  let w : ↥(Tim79a.xOf V H) := ⟨(w₀ : G), hW₀ w₀.2⟩
  have hw1 : w ≠ 1 := by
    intro h
    apply hw₀
    exact Subtype.ext (congrArg (fun x : ↥(Tim79a.xOf V H) => (x : G)) h)
  refine ⟨⟨ofW hW w, (mem_subW_iff hW).mpr w₀.2⟩, ⟨0, (subW hW W₀).zero_mem⟩, ?_⟩
  intro h
  apply hw1
  have h' := congrArg (fun x : ↥(subW hW W₀) =>
    toW hW (x : Additive (IntMod (Tim79a.xOf V H) hW))) h
  simpa [toW_ofW, toW_zero] using h'

private theorem subRepW_invariant_eq_bot_or_top {W₀ : Subgroup G}
    (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    ∀ U : Submodule (ZMod 2) (subW hW W₀),
      (∀ x : X, ∀ u ∈ U, subRepW hW ψ hW₀ hN x u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  let X₀ := subW hW W₀
  let ρ₀ := subRepW hW ψ hW₀ hN
  let Uamb : Submodule (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) := U.map X₀.subtype
  have hUamb_inv : ∀ x : X, ∀ v ∈ Uamb, repW hW ψ x v ∈ Uamb := by
    intro x v hv
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨ρ₀ x u, hU x u hu, ?_⟩
    change (↑(((CFSG.Quasithin.B45U33.subRep (repW hW ψ) X₀
      ((normalizer_subW_iff hW ψ hW₀).mp hN)) x) u) :
        Additive (IntMod (Tim79a.xOf V H) hW)) = repW hW ψ x (X₀.subtype u)
    rw [CFSG.Quasithin.B45U33.subRep_apply]
    rfl
  let E : Subgroup G := subgroupOfSubW hW Uamb
  have hEU : subW hW E = Uamb := subW_subgroupOfSubW hW Uamb
  have hE : E ≤ Tim79a.xOf V H := by
    rintro g ⟨hg, -⟩
    exact hg
  have hEx : E ≤ W₀ := by
    intro g hg
    have hg' : ofW hW ⟨g, hE hg⟩ ∈ Uamb := hg.2
    have hle : Uamb ≤ subW hW W₀ := by
      rintro y ⟨u, -, rfl⟩
      exact u.2
    exact (mem_subW_iff hW).mp (hle hg')
  have hnorm : H ≤ Subgroup.normalizer (E : Set G) := by
    rw [normalizer_subW_iff hW ψ hE]
    intro x v hv
    have hv' : v ∈ Uamb := by
      rw [hEU] at hv
      exact hv
    have h := hUamb_inv x v hv'
    rwa [hEU]
  by_cases hbot : E = ⊥
  · left
    have hUamb : Uamb = ⊥ := by rw [← hEU, hbot, subW_bot]
    apply Submodule.ext
    intro u
    constructor
    · intro hu
      rw [Submodule.mem_bot]
      have h : X₀.subtype u ∈ Uamb := Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      rw [hUamb, Submodule.mem_bot] at h
      exact Submodule.subtype_injective (p := X₀) (by simpa using h)
    · intro hu
      rw [Submodule.mem_bot] at hu
      rw [hu]
      exact U.zero_mem
  · have hEtop : E = W₀ := hmin E hEx hbot hnorm
    right
    have hUamb : Uamb = X₀ := by rw [← hEU, hEtop]
    rw [Submodule.eq_top_iff']
    intro u
    have h : X₀.subtype u ∈ Uamb := by rw [hUamb]; exact u.2
    rw [Submodule.mem_map] at h
    obtain ⟨v, hv, hv'⟩ := h
    have hvu : v = u := Submodule.subtype_injective (p := X₀) hv'
    rw [← hvu]
    exact hv
theorem isIrreducible_subRepW {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
      H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀) :
    (subRepW hW ψ hW₀ hN).IsIrreducible := by
  rw [isIrreducible_iff]
  exact ⟨nontrivial_subW hW hW₀ hW₀ne,
    subRepW_invariant_eq_bot_or_top hW ψ hW₀ hN hmin⟩

end Main

theorem exists_minimal_normalized_le [Finite G] {E : Subgroup G} (hEne : E ≠ ⊥)
    (hEN : H ≤ Subgroup.normalizer (E : Set G)) :
    ∃ W₀ : Subgroup G, W₀ ≤ E ∧ W₀ ≠ ⊥ ∧
      H ≤ Subgroup.normalizer (W₀ : Set G) ∧
      ∀ W₁ : Subgroup G, W₁ ≤ W₀ → W₁ ≠ ⊥ →
        H ≤ Subgroup.normalizer (W₁ : Set G) → W₁ = W₀ := by
  classical
  let P : ℕ → Prop := fun n => ∃ W₀ : Subgroup G, W₀ ≤ E ∧ W₀ ≠ ⊥ ∧
    H ≤ Subgroup.normalizer (W₀ : Set G) ∧ Nat.card W₀ = n
  have hP : ∃ n, P n := ⟨Nat.card E, E, le_rfl, hEne, hEN, rfl⟩
  obtain ⟨W₀, hle, hne, hN, hcard⟩ := Nat.find_spec hP
  refine ⟨W₀, hle, hne, hN, ?_⟩
  intro W₁ hle₁ hne₁ hN₁
  have hP₁ : P (Nat.card W₁) := ⟨W₁, hle₁.trans hle, hne₁, hN₁, rfl⟩
  have hmin : Nat.card W₀ ≤ Nat.card W₁ := by
    rw [hcard]
    exact Nat.find_min' hP hP₁
  exact Subgroup.eq_of_le_of_card_ge hle₁ hmin

end CFSG.RankThree.GF2n.Tim81
