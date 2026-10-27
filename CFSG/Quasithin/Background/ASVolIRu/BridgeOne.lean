module

public import CFSG.Milestones.ASVolI.J1
public import CFSG.Quasithin.Recognition.RuTypeSetting
public import CFSG.Quasithin.Background.ASVolIRu.StUniqueDefs
public import CFSG.Quasithin.Vol2.Ch10SecAElemAb
public import CFSG.Open.StatedZModTwo
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK.RuType

namespace BridgeOne

open CFSG.Open CFSG.Open.StatedAPI
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem centerOf_eq (W : Subgroup G) : centerOf W = CFSG.Quasithin.centerOf W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨w, hw⟩
    simpa using congrArg Subtype.val this
  · rintro ⟨hxW, hxc⟩
    refine ⟨⟨x, hxW⟩, Subgroup.mem_center_iff.mpr fun w => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc w w.2)

theorem frattiniOf_eq (W : Subgroup G) : frattiniOf W = CFSG.Quasithin.frattiniOf W := rfl

theorem pCoreOf_le_self (H : Subgroup G) : pCoreOf 2 H ≤ H := Subgroup.map_subtype_le _

theorem subgroupOf_pCoreOf (H : Subgroup G) : (pCoreOf 2 H).subgroupOf H = CFSG.pCore 2 ↥H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem isPGroup_pCoreOf (H : Subgroup G) : IsPGroup 2 ↥(pCoreOf 2 H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).of_equiv
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)

theorem conj_mem_pCoreOf {H : Subgroup G} {l x : G} (hl : l ∈ H) (hx : x ∈ pCoreOf 2 H) :
    l * x * l⁻¹ ∈ pCoreOf 2 H := by
  have hn : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  have hx' : (⟨x, pCoreOf_le_self H hx⟩ : H) ∈ CFSG.pCore 2 ↥H := by
    rw [← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf]
    exact hx
  have := hn.conj_mem _ hx' ⟨l, hl⟩
  rw [← subgroupOf_pCoreOf, Subgroup.mem_subgroupOf] at this
  exact this

theorem det_GL_zmod_two {n : ℕ} (A : GL (Fin n) (ZMod 2)) :
    (A : Matrix (Fin n) (Fin n) (ZMod 2)).det = 1 := by
  have h : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have := congrArg Units.val h
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this

@[expose] noncomputable def glToSL (n : ℕ) :
    GL (Fin n) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) where
  toFun A := ⟨A, det_GL_zmod_two A⟩
  map_one' := by
    ext i j
    rfl
  map_mul' A B := by
    ext i j
    rfl

theorem coe_glToSL {n : ℕ} (A : GL (Fin n) (ZMod 2)) :
    ((glToSL n A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = (A : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl

theorem glToSL_injective (n : ℕ) : Function.Injective (glToSL n) := by
  intro A B h
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) =>
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) i j) h
  simpa [coe_glToSL] using this

theorem glToSL_surjective (n : ℕ) : Function.Surjective (glToSL n) := fun A =>
  ⟨Matrix.SpecialLinearGroup.toGL A, by ext i j; rfl⟩

theorem mulAutPiEquivGL_symm_apply (d : ℕ) (γ : GL (Fin d) (ZMod 2))
    (x : Multiplicative (Fin d → ZMod 2)) :
    (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL d).symm γ x =
      Multiplicative.ofAdd ((γ : Matrix (Fin d) (Fin d) (ZMod 2)).mulVec
        (Multiplicative.toAdd x)) := by
  simp [CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL,
    CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivLinearEquiv,
    LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem mulAutPiEquivGL_mulVec (d : ℕ) (φ : MulAut (Multiplicative (Fin d → ZMod 2)))
    (v : Fin d → ZMod 2) :
    ((CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL d φ : GL (Fin d) (ZMod 2)) :
      Matrix (Fin d) (Fin d) (ZMod 2)).mulVec v =
        Multiplicative.toAdd (φ (Multiplicative.ofAdd v)) := by
  have h := mulAutPiEquivGL_symm_apply d (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL d φ)
    (Multiplicative.ofAdd v)
  rw [MulEquiv.symm_apply_apply] at h
  rw [h]
  rfl

@[expose] def conjAct (L X : Subgroup G) (h : L ≤ Subgroup.normalizer (X : Set G)) :
    ↥L →* MulAut ↥X :=
  X.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem conjAct_coe (L X : Subgroup G) (h : L ≤ Subgroup.normalizer (X : Set G)) (l : ↥L)
    (x : ↥X) : ((conjAct L X h l x : ↥X) : G) = (l : G) * x * (l : G)⁻¹ := rfl

@[expose] noncomputable def repV {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) :
    ↥L →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
  (glToSL n).comp (((MulAut.congr e).trans
    (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL n)).toMonoidHom.comp (conjAct L V hLV))

theorem repV_mulVec {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (l : ↥L) (v w : ↥V)
    (hw : (w : G) = l * v * (l : G)⁻¹) :
    e w = Multiplicative.ofAdd (((repV hLV e l : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Multiplicative.toAdd (e v))) := by
  have hc : conjAct L V hLV l v = w := by
    apply Subtype.ext
    rw [conjAct_coe, hw]
  show e w = Multiplicative.ofAdd (((glToSL n (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL n
    (MulAut.congr e (conjAct L V hLV l))) :
      Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec
      (Multiplicative.toAdd (e v)))
  rw [coe_glToSL, mulAutPiEquivGL_mulVec, MulAut.congr_apply]
  simp [hc]

theorem repV_surjective {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2))
    (hnat : ∀ φ : MulAut ↥V, ∃ l : ↥L, conjAct L V hLV l = φ) :
    Function.Surjective (repV hLV e) := by
  intro A
  obtain ⟨γ, rfl⟩ := glToSL_surjective n A
  obtain ⟨l, hl⟩ := hnat (((MulAut.congr e).trans
    (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL n)).symm γ)
  refine ⟨l, ?_⟩
  show glToSL n (((MulAut.congr e).trans (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL n))
    (conjAct L V hLV l)) = glToSL n γ
  rw [hl, MulEquiv.apply_symm_apply]

theorem repV_ker {L V : Subgroup G} (hLV : L ≤ Subgroup.normalizer (V : Set G)) {n : ℕ}
    (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) :
    (repV hLV e).ker = (Subgroup.centralizer (V : Set G)).subgroupOf L := by
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    have h1 : conjAct L V hLV l = 1 := by
      apply ((MulAut.congr e).trans (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL n)).injective
      apply glToSL_injective n
      rw [map_one, map_one]
      exact h
    have h2 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) h1
    simp only [conjAct_coe, MulAut.one_apply] at h2
    have h2' : (l : G) * v * (l : G)⁻¹ = v := h2
    calc v * l = (l : G) * v * (l : G)⁻¹ * l := by rw [h2']
      _ = l * v := by group
  · intro h
    have h1 : conjAct L V hLV l = 1 := by
      ext v
      rw [conjAct_coe, MulAut.one_apply]
      show (l : G) * v * (l : G)⁻¹ = v
      rw [← h v v.2]
      group
    show glToSL n (((MulAut.congr e).trans (CFSG.Quasithin.Vol2.Ch10.SecA.mulAutPiEquivGL n))
      (conjAct L V hLV l)) = 1
    rw [h1, map_one, map_one]

theorem nonempty_mulEquiv_fin_zmod_two {E : Type*} [Group E] [Finite E]
    (hcomm : ∀ a b : E, a * b = b * a) (hE : ∀ x : E, x ^ 2 = 1) {n : ℕ}
    (hcard : Nat.card E = 2 ^ n) : Nonempty (E ≃* Multiplicative (Fin n → ZMod 2)) := by
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  exact CFSG.Quasithin.Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one hE hcard

theorem card_of_statedClassicalModel {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 3 2 1) : Nat.card X = 168 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  rw [Nat.card_congr e.toEquiv]
  have hbot : (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two hK2, Subgroup.bot_subgroupOf]
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hbot).toEquiv,
    Nat.card_congr (QuotientGroup.quotientBot).toEquiv]
  exact card_statedSL_three_of_card_eq_two hK2

section FromRuType

variable [Finite G] {L V T : Subgroup G}

theorem V_eq_quasithin (h : RuType G L V T) :
    V = CFSG.Quasithin.centerOf (pCoreOf 2 L) :=
  h.V_eq.trans (centerOf_eq _)

theorem L_le_normalizer (h : RuType G L V T) : L ≤ Subgroup.normalizer (V : Set G) :=
  h.L_eq.le

theorem S_comm_V (h : RuType G L V T) {v s : G} (hv : v ∈ V) (hs : s ∈ SRu L) :
    s * v = v * s := by
  rw [h.V_eq] at hv
  obtain ⟨y, hy, rfl⟩ := hv
  have := Subgroup.mem_center_iff.mp hy ⟨s, hs⟩
  simpa using congrArg Subtype.val this

theorem card_L_quotient (h : RuType G L V T) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 :=
  card_of_statedClassicalModel h.LS_L32

theorem conjAct_surjective (h : RuType G L V T) :
    ∀ φ : MulAut ↥V, ∃ l : ↥L, conjAct L V (L_le_normalizer h) l = φ := by
  intro φ
  obtain ⟨l, hl, hv⟩ := h.V_natural φ.symm
  refine ⟨⟨l, hl⟩, ?_⟩
  ext v
  rw [conjAct_coe]
  have e := hv (φ v)
  rw [MulEquiv.symm_apply_apply] at e
  calc (l : G) * v * (l : G)⁻¹ = l * (l⁻¹ * (φ v : G) * l) * l⁻¹ := by rw [e]
    _ = φ v := by group

theorem nonempty_coords (h : RuType G L V T) :
    Nonempty (↥V ≃* Multiplicative (Fin 3 → ZMod 2)) := by
  obtain ⟨hel, hcard⟩ := h.V_E8
  refine nonempty_mulEquiv_fin_zmod_two (fun a b => hel.1.is_comm.comm a b)
    (fun x => Subtype.ext ?_) (by rw [hcard]; norm_num)
  simpa using hel.2 x x.2

theorem ker_repV (h : RuType G L V T) (e : ↥V ≃* Multiplicative (Fin 3 → ZMod 2)) :
    (repV (L_le_normalizer h) e).ker = (pCoreOf 2 L).subgroupOf L := by
  set θ := repV (L_le_normalizer h) e with hθ
  have hsurj : Function.Surjective θ := repV_surjective _ e (conjAct_surjective h)
  have hle : (pCoreOf 2 L).subgroupOf L ≤ θ.ker := by
    rw [hθ, repV_ker]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (S_comm_V h hv hx).symm
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 L).subgroupOf L)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hsurj).toEquiv,
    CFSG.Quasithin.RuType.SL3.card_SL3] at h1
  have hq : Nat.card (↥L ⧸ (pCoreOf 2 L).subgroupOf L) = 168 := by
    rw [subgroupOf_pCoreOf]
    exact card_L_quotient h
  rw [hq] at h2
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

end FromRuType

section Abstract

open CFSG.Quasithin.RuType (IsTraceZero stAct StUniqueStatement)

theorem exists_module_quotient {Q : Type} [Group Q] [Finite Q]
    (hcomm : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center Q)
    (hsq : ∀ x : Q, x ^ 2 ∈ Subgroup.center Q) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod 2) M) (_ : Finite M)
      (π : Q →* Multiplicative M), Function.Surjective π ∧ π.ker = Subgroup.center Q ∧
        Nat.card M = (Subgroup.center Q).index := by
  letI : CommGroup (Q ⧸ Subgroup.center Q) :=
    { (inferInstance : Group (Q ⧸ Subgroup.center Q)) with
      mul_comm := fun a b => by
        refine QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun y => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have := hcomm y⁻¹ x⁻¹
        simpa [mul_assoc] using this }
  have h2 : ∀ m : Additive (Q ⧸ Subgroup.center Q), (2 : ℕ) • m = 0 := by
    intro m
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul m)
    apply Additive.toMul.injective
    rw [toMul_nsmul, ← hx, ← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hsq x)
  letI : Module (ZMod 2) (Additive (Q ⧸ Subgroup.center Q)) := AddCommGroup.zmodModule h2
  let π : Q →* Multiplicative (Additive (Q ⧸ Subgroup.center Q)) :=
    { toFun := fun q => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk q))
      map_one' := rfl
      map_mul' := fun x y => rfl }
  refine ⟨Additive (Q ⧸ Subgroup.center Q), inferInstance, inferInstance, inferInstance, π, ?_, ?_,
    ?_⟩
  · intro m
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul (Multiplicative.toAdd m))
    exact ⟨x, by
      show Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk x)) = m
      rw [hx]
      rfl⟩
  · ext q
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff q).mp h
    · intro h
      exact (QuotientGroup.eq_one_iff q).mpr h
  · exact (Nat.card_congr Additive.toMul).trans (Subgroup.index_eq_card _).symm

noncomputable def inducedEnd {Q M : Type} [Group Q] [AddCommGroup M] [Module (ZMod 2) M]
    (π : Q →* Multiplicative M) (hπs : Function.Surjective π) (σ : MulAut Q)
    (hσ : ∀ q, π q = 1 → π (σ q) = 1) : M →ₗ[ZMod 2] M :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.toMultiplicative.symm
    (MonoidHom.liftOfSurjective π hπs ⟨π.comp σ.toMonoidHom, fun q hq => hσ q hq⟩))

theorem inducedEnd_apply {Q M : Type} [Group Q] [AddCommGroup M] [Module (ZMod 2) M]
    (π : Q →* Multiplicative M) (hπs : Function.Surjective π) (σ : MulAut Q)
    (hσ : ∀ q, π q = 1 → π (σ q) = 1) (q : Q) :
    inducedEnd π hπs σ hσ (Multiplicative.toAdd (π q)) = Multiplicative.toAdd (π (σ q)) :=
  congrArg Multiplicative.toAdd (MonoidHom.liftOfRightInverse_comp_apply π _
    (Function.rightInverse_surjInv hπs) ⟨π.comp σ.toMonoidHom, fun q hq => hσ q hq⟩ q)

theorem end_ext_of_surj {Q M : Type} [Group Q] [AddCommGroup M] [Module (ZMod 2) M]
    (π : Q →* Multiplicative M) (hπs : Function.Surjective π) {f g : M →ₗ[ZMod 2] M}
    (h : ∀ q, f (Multiplicative.toAdd (π q)) = g (Multiplicative.toAdd (π q))) : f = g := by
  refine LinearMap.ext fun m => ?_
  obtain ⟨q, hq⟩ := hπs (Multiplicative.ofAdd m)
  have : m = Multiplicative.toAdd (π q) := by rw [hq]; rfl
  rw [this]
  exact h q

theorem exists_chi (hSt : StUniqueStatement) {K Q : Type} [Group K] [Group Q]
    {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (π : Q →* Multiplicative M) (hπs : Function.Surjective π) (act : K →* MulAut Q)
    (hactker : ∀ (k : K) (q : Q), π q = 1 → π (act k q) = 1)
    (θ : K →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hθs : Function.Surjective θ)
    (hθk : ∀ k : K, θ k = 1 → ∀ q : Q, π (act k q) = π q)
    (hcard : Nat.card M = 2 ^ 8)
    (hirr : ∀ B : Subgroup Q, π.ker ≤ B → (∀ (k : K), ∀ b ∈ B, act k b ∈ B) →
      B = π.ker ∨ B = ⊤) :
    ∃ χ : Q →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)),
      χ.ker = π.ker ∧ (∀ q, IsTraceZero (Multiplicative.toAdd (χ q))) ∧
      (∀ A, IsTraceZero A → ∃ q, χ q = Multiplicative.ofAdd A) ∧
      ∀ (k : K) (q q' : Q), q' = act k q →
        χ q' = Multiplicative.ofAdd (stAct (θ k) (Multiplicative.toAdd (χ q))) := by
  let ρK : K →* (M →ₗ[ZMod 2] M) :=
    { toFun := fun k => inducedEnd π hπs (act k) (hactker k)
      map_one' := end_ext_of_surj π hπs fun q => by
        rw [inducedEnd_apply, map_one, MulAut.one_apply]
        rfl
      map_mul' := fun k₁ k₂ => end_ext_of_surj π hπs fun q => by
        rw [inducedEnd_apply, Module.End.mul_apply, inducedEnd_apply, inducedEnd_apply, map_mul,
          MulAut.mul_apply] }
  have hρK : ∀ (k : K) (q : Q), ρK k (Multiplicative.toAdd (π q)) =
      Multiplicative.toAdd (π (act k q)) := fun k q => inducedEnd_apply π hπs (act k) (hactker k) q
  have hker : θ.ker ≤ ρK.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    exact end_ext_of_surj π hπs fun q => by
      rw [hρK, hθk k hk q]
      rfl
  let ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) M :=
    (QuotientGroup.lift θ.ker ρK hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective θ hθs).symm.toMonoidHom
  have hρ : ∀ (k : K) (m : M), ρ (θ k) m = ρK k m := fun k m => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective θ hθs).symm (θ k) =
        (k : K ⧸ θ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.lift θ.ker ρK hker)
      ((QuotientGroup.quotientKerEquivOfSurjective θ hθs).symm (θ k)) m = ρK k m
    rw [h1, QuotientGroup.lift_mk]
  have hirr' : ∀ N : Submodule (ZMod 2) M,
      (∀ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∀ m ∈ N, ρ g m ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    let B : Subgroup Q :=
      { carrier := {q | Multiplicative.toAdd (π q) ∈ N}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_mul, toAdd_mul]
          exact N.add_mem ha hb
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq, map_inv, toAdd_inv]
          exact N.neg_mem ha }
    have hBmem : ∀ q, q ∈ B ↔ Multiplicative.toAdd (π q) ∈ N := fun q => Iff.rfl
    have hBker : π.ker ≤ B := fun q hq => by
      rw [hBmem]
      rw [MonoidHom.mem_ker] at hq
      rw [hq]
      simp
    have hBinv : ∀ k : K, ∀ b ∈ B, act k b ∈ B := by
      intro k b hb
      rw [hBmem] at hb ⊢
      have := hN (θ k) _ hb
      rwa [hρ, hρK] at this
    rcases hirr B hBker hBinv with hB | hB
    · left
      refine (Submodule.eq_bot_iff N).mpr fun m hm => ?_
      obtain ⟨q, hq⟩ := hπs (Multiplicative.ofAdd m)
      have hmq : m = Multiplicative.toAdd (π q) := by rw [hq]; rfl
      have hqB : q ∈ B := by rw [hBmem, ← hmq]; exact hm
      rw [hB, MonoidHom.mem_ker] at hqB
      rw [hmq, hqB]
      rfl
    · right
      refine (Submodule.eq_top_iff').mpr fun m => ?_
      obtain ⟨q, hq⟩ := hπs (Multiplicative.ofAdd m)
      have hmq : m = Multiplicative.toAdd (π q) := by rw [hq]; rfl
      have hqB : q ∈ B := by rw [hB]; exact Subgroup.mem_top q
      rw [hBmem] at hqB
      rwa [hmq]
  obtain ⟨χ0, hinj, htr, hsurj, hequi⟩ := hSt M ρ hcard hirr'
  refine ⟨(AddMonoidHom.toMultiplicative χ0).comp π, ?_, ?_, ?_, ?_⟩
  · ext q
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have h0 : χ0 (Multiplicative.toAdd (π q)) = 0 := h
      have := hinj (h0.trans (map_zero χ0).symm)
      exact this
    · intro h
      show χ0 (Multiplicative.toAdd (π q)) = 0
      rw [h]
      exact map_zero χ0
  · intro q
    exact htr _
  · intro A hA
    obtain ⟨m, hm⟩ := hsurj A hA
    obtain ⟨q, hq⟩ := hπs (Multiplicative.ofAdd m)
    refine ⟨q, ?_⟩
    show Multiplicative.ofAdd (χ0 (Multiplicative.toAdd (π q))) = Multiplicative.ofAdd A
    rw [hq]
    exact congrArg Multiplicative.ofAdd hm
  · intro k q q' hq'
    subst hq'
    show Multiplicative.ofAdd (χ0 (Multiplicative.toAdd (π (act k q)))) =
      Multiplicative.ofAdd (stAct (θ k) (χ0 (Multiplicative.toAdd (π q))))
    rw [← hρK, ← hρ, hequi]

theorem mulAut_mem_center {Q : Type*} [Group Q] (σ : MulAut Q) {q : Q}
    (hq : q ∈ Subgroup.center Q) : σ q ∈ Subgroup.center Q := by
  rw [Subgroup.mem_center_iff] at hq ⊢
  intro r
  obtain ⟨r', rfl⟩ := σ.surjective r
  rw [← map_mul, ← map_mul, hq r']

end Abstract

section Steinberg

open CFSG.Quasithin.RuType (IsTraceZero stAct StUniqueStatement)

variable [Finite G] {L V T : Subgroup G}

theorem le_normalizer_of_conj_mem {L X : Subgroup G}
    (h : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ ∈ X) : L ≤ Subgroup.normalizer (X : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h l hl x hx, fun hx => ?_⟩
  have := h l⁻¹ (L.inv_mem hl) _ hx
  convert this using 1
  group

theorem L_le_normalizer_S (L : Subgroup G) :
    L ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
  le_normalizer_of_conj_mem fun _ hl _ hx => conj_mem_pCoreOf hl hx

theorem exists_chi_of_ruType (hSt : StUniqueStatement) (h : RuType G L V T)
    (θ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (hθs : Function.Surjective θ)
    (hθk : θ.ker = (pCoreOf 2 L).subgroupOf L) :
    ∃ χ : ↥(pCoreOf 2 L) →* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)),
      χ.ker = V.subgroupOf (pCoreOf 2 L) ∧
      (∀ s, IsTraceZero (Multiplicative.toAdd (χ s))) ∧
      (∀ A, IsTraceZero A → ∃ s, χ s = Multiplicative.ofAdd A) ∧
      ∀ (l : ↥L) (s t : ↥(pCoreOf 2 L)), (t : G) = l * s * (l : G)⁻¹ →
        χ t = Multiplicative.ofAdd (stAct (θ l) (Multiplicative.toAdd (χ s))) := by
  have hVc : V.subgroupOf (pCoreOf 2 L) = Subgroup.center ↥(pCoreOf 2 L) := by
    rw [h.V_eq]
    exact Subgroup.comap_map_eq_self_of_injective (pCoreOf 2 L).subtype_injective _
  have hfc : frattini ↥(pCoreOf 2 L) = Subgroup.center ↥(pCoreOf 2 L) :=
    Subgroup.map_injective (pCoreOf 2 L).subtype_injective h.S_special.1
  have hcommS : ∀ x y : ↥(pCoreOf 2 L), x * y * x⁻¹ * y⁻¹ ∈ Subgroup.center ↥(pCoreOf 2 L) := by
    intro x y
    have h1 : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ ⁅SRu L, SRu L⁆ :=
      Subgroup.commutator_mem_commutator x.2 y.2
    rw [h.S_special.2] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have : z = x * y * x⁻¹ * y⁻¹ := Subtype.ext hzx
    rwa [this] at hz
  have hsqS : ∀ x : ↥(pCoreOf 2 L), x ^ 2 ∈ Subgroup.center ↥(pCoreOf 2 L) := by
    intro x
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (IsPGroup 2 ↥(pCoreOf 2 L)) := ⟨isPGroup_pCoreOf L⟩
    rw [← hfc]
    exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) x
  obtain ⟨M, _, _, _, π, hπs, hπk, hMcard⟩ := exists_module_quotient hcommS hsqS
  let act : ↥L →* MulAut ↥(pCoreOf 2 L) := conjAct L (pCoreOf 2 L) (L_le_normalizer_S L)
  have hactker : ∀ (k : ↥L) (q : ↥(pCoreOf 2 L)), π q = 1 → π (act k q) = 1 := by
    intro k q hq
    have hq' : q ∈ Subgroup.center ↥(pCoreOf 2 L) := by rw [← hπk]; exact hq
    have := mulAut_mem_center (act k) hq'
    rw [← hπk] at this
    exact this
  have hθk' : ∀ k : ↥L, θ k = 1 → ∀ q : ↥(pCoreOf 2 L), π (act k q) = π q := by
    intro k hk q
    have hk' : (k : G) ∈ pCoreOf 2 L := by
      have : k ∈ θ.ker := hk
      rw [hθk, Subgroup.mem_subgroupOf] at this
      exact this
    have e : act k q = (⟨k, hk'⟩ : ↥(pCoreOf 2 L)) * q * (⟨k, hk'⟩ : ↥(pCoreOf 2 L))⁻¹ :=
      Subtype.ext rfl
    have hc : act k q * q⁻¹ ∈ π.ker := by
      rw [hπk, e]
      exact hcommS ⟨k, hk'⟩ q
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hc
    exact hc
  have hcard : Nat.card M = 2 ^ 8 := by
    rw [hMcard, ← hVc]
    exact h.SV_steinberg.1
  have hirr : ∀ B : Subgroup ↥(pCoreOf 2 L), π.ker ≤ B →
      (∀ k : ↥L, ∀ b ∈ B, act k b ∈ B) → B = π.ker ∨ B = ⊤ := by
    intro B hB hBinv
    rw [hπk] at hB ⊢
    have h1 : V ≤ B.map (pCoreOf 2 L).subtype := by
      rw [h.V_eq]
      exact Subgroup.map_mono hB
    have h2 : B.map (pCoreOf 2 L).subtype ≤ SRu L := Subgroup.map_subtype_le B
    have h3 : L ≤ Subgroup.normalizer ((B.map (pCoreOf 2 L).subtype : Subgroup G) : Set G) := by
      refine le_normalizer_of_conj_mem fun l hl x hx => ?_
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨act ⟨l, hl⟩ b, hBinv ⟨l, hl⟩ b hb, rfl⟩
    rcases h.SV_steinberg.2 _ h1 h2 h3 with h4 | h4
    · left
      apply Subgroup.map_injective (pCoreOf 2 L).subtype_injective
      rw [h4, h.V_eq]
      rfl
    · right
      apply Subgroup.map_injective (pCoreOf 2 L).subtype_injective
      rw [h4, Subgroup.map_top]
      exact (Subgroup.range_subtype _).symm
  obtain ⟨χ, hχk, hχt, hχs, hχe⟩ := exists_chi hSt π hπs act hactker θ hθs hθk' hcard hirr
  refine ⟨χ, by rw [hχk, hπk, hVc], hχt, hχs, fun l s t hw => hχe l s t ?_⟩
  exact Subtype.ext (hw.trans (conjAct_coe L (pCoreOf 2 L) _ l s).symm)

end Steinberg

end BridgeOne

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {L V T : Subgroup G}

theorem centralizer_V_le_S (h : RuType G L V T) {l : G} (hl : l ∈ L)
    (hc : ∀ v ∈ V, l * v = v * l) : l ∈ SRu L := by
  obtain ⟨e⟩ := BridgeOne.nonempty_coords h
  have hk := BridgeOne.ker_repV h e
  have hmem : (⟨l, hl⟩ : ↥L) ∈ (BridgeOne.repV (BridgeOne.L_le_normalizer h) e).ker := by
    rw [BridgeOne.repV_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hc v hv).symm
  rw [hk, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem ruOne (hSt : CFSG.Quasithin.RuType.StUniqueStatement) (h : RuType G L V T) :
    CFSG.Quasithin.RuType.RuOne L := by
  have hV : V = CFSG.Quasithin.centerOf (pCoreOf 2 L) := BridgeOne.V_eq_quasithin h
  obtain ⟨e⟩ := BridgeOne.nonempty_coords h
  have hLV := BridgeOne.L_le_normalizer h
  have hθs : Function.Surjective (BridgeOne.repV hLV e) :=
    BridgeOne.repV_surjective hLV e (BridgeOne.conjAct_surjective h)
  have hθk := BridgeOne.ker_repV h e
  obtain ⟨χ, hχk, hχt, hχs, hχe⟩ :=
    BridgeOne.exists_chi_of_ruType hSt h (BridgeOne.repV hLV e) hθs hθk
  refine
    { center_eq_commutator := (BridgeOne.centerOf_eq _).symm.trans h.S_special.2.symm
      center_eq_frattini := (BridgeOne.centerOf_eq _).symm.trans
        (h.S_special.1.symm.trans (BridgeOne.frattiniOf_eq _))
      center_elem := by rw [← hV]; exact h.V_E8.1
      modules := ⟨BridgeOne.repV hLV e, hθs, hθk,
        ⟨(MulEquiv.subgroupCongr hV.symm).trans e,
          fun l v w hw => BridgeOne.repV_mulVec hLV e l _ _ hw⟩,
        ⟨χ, by rw [← hV]; exact hχk, hχt, hχs, hχe⟩⟩
      eq_normalizer := by rw [← hV]; exact h.L_eq }

theorem isTypeRu_of_two (hSt : CFSG.Quasithin.RuType.StUniqueStatement) (h : RuType G L V T)
    {T' : Sylow 2 G} (h2 : CFSG.Quasithin.RuType.RuTwo L T') :
    CFSG.Quasithin.RuType.IsTypeRu G :=
  ⟨L, ruOne hSt h, T', h2⟩

end CFSG.ASVolI.ChIJK.RuType
