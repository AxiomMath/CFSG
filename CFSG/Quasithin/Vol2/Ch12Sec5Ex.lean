module

public import CFSG.Quasithin.Vol2.Ch12Sec5Aut
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep
public import CFSG.Quasithin.Vol2.Ch12Sec4Pre
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Cx
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.B2FactorizationSum
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch12Sec4L5B42
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Wedge
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma7
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma8
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma9Para
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Sporadic.Schreier.J4SSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125 S125ZV S125Aut
open scoped IsMulCommutative

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125Ex

@[reducible, expose] noncomputable def zmod2Module' {V : Type*} [CommGroup V]
    (h2 : ∀ v : V, v ^ 2 = 1) : Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, h2, ofMul_one]

theorem exists_wedge_mulEquiv
    {V : Type*} [CommGroup V] [Finite V] (h2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ 10)
    {H : Subgroup (MulAut V)} (φ : ↥H ≃* SL5)
    (hirr : ∀ W : Subgroup V, (∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (e : V ≃* Multiplicative (Fin 10 → ZMod 2)) (γ : ↥H ≃* SL5),
      ∀ (h : ↥H) (v : V), e ((h : MulAut V) v) =
        Multiplicative.ofAdd (JonesParshall.wedgeRep (γ h) (Multiplicative.toAdd (e v))) := by
  let _ : Module (ZMod 2) (Additive V) := zmod2Module' h2
  have : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  have hsimple := Orbit.isSimpleRep_repOfIso φ hirr
  have hfin : Module.finrank (ZMod 2) (Additive V) = 10 := by
    have : Fintype (Additive V) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h
    change Nat.card V = _ at h
    rw [hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  obtain ⟨β, θ, hβ⟩ : ∃ (β : Additive V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2)) (θ : SL5 ≃* SL5),
      ∀ g v, β (Orbit.repOfIso φ g v) = JonesParshall.wedgeRep (θ g) (β v) := by
    rcases JonesParshall.Curtis.classify_ten hsimple hfin with ⟨β, hβ⟩ | ⟨β, hβ⟩
    · exact ⟨β, MulEquiv.refl _, hβ⟩
    · exact ⟨β, JonesParshall.Curtis.twistα, hβ⟩
  refine ⟨AddEquiv.toMultiplicativeRight β.toAddEquiv, φ.trans θ, fun h v => ?_⟩
  change Multiplicative.ofAdd (β (Additive.ofMul ((h : MulAut V) v))) =
    Multiplicative.ofAdd (JonesParshall.wedgeRep (θ (φ h)) (β (Additive.ofMul v)))
  rw [← Orbit.repOfIso_apply_iso φ h v, hβ]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem irr_autOn (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hirr : IsIrreducibleUnder L V) :
    ∀ W : Subgroup ↥V, (∀ a ∈ autOn L V, ∀ w ∈ W, (a : MulAut ↥V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hconj : ∀ l ∈ L, ∀ x ∈ W.map V.subtype, l * x * l⁻¹ ∈ W.map V.subtype := by
    intro l hl x hx
    obtain ⟨w, hw, rfl⟩ := hx
    have ha : conjAct V ⟨l, hLV hl⟩ ∈ autOn L V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hl)
    exact ⟨conjAct V ⟨l, hLV hl⟩ w, hW _ ha w hw, rfl⟩
  have hnorm : L ≤ Subgroup.normalizer ((W.map V.subtype : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj l hl x, fun hx => ?_⟩
    have := hconj l⁻¹ (L.inv_mem hl) _ hx
    simpa [mul_assoc] using this
  rcases hirr.2 (W.map V.subtype) (Subgroup.map_subtype_le W) hnorm with h | h
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).1 h
  · right
    rw [eq_top_iff]
    intro w _
    have hw : (w : G) ∈ W.map V.subtype := by
      rw [h]
      exact w.2
    obtain ⟨w', hw', hww'⟩ := hw
    rw [show w = w' from Subtype.ext hww'.symm]
    exact hw'

structure Facts125 (G : Type) [Group G] (T L V : Subgroup G) : Prop where
  comm : IsMulCommutative ↥V
  sq : ∀ v ∈ V, v ^ 2 = 1
  normalizes : L ≤ Subgroup.normalizer (V : Set G)
  pCore : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G)
  notCent : ¬ L ≤ Subgroup.centralizer (V : Set G)
  le_T : V ≤ T
  T_le : T ≤ Subgroup.normalizer (V : Set G)
  card : Nat.card V = 2 ^ 10
  irr : IsIrreducibleUnder L V

theorem Facts125.of (h1222 : Stmt12_2_2) (hH : Hyp125 G T L V) : Facts125 G T L V := by
  have hyp := hH.hyp
  obtain ⟨hc, -⟩ := modules_cases_of_hyp1223 h1222 hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -, -⟩ := hall V hyp.irrPlus
  have hcomm : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have h1 := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨v, hVLT hv⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hv)
    simpa using congrArg Subtype.val h2
  refine ⟨hc, hsq, hyp.irrPlus.2.2.1,
    pCoreOf_le_centralizer_of_isPrimeReduced_sup hyp.normalizes hVLT hred, fun h => ?_, hVT, hTV,
    hH.card, hH.irred⟩
  apply hV1
  rw [← hcomm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)

theorem lbar_equiv (hH : Hyp125 G T L V) (hf : Facts125 G T L V) :
    Nonempty (↥(autOn L V) ≃* SL5) := by
  obtain ⟨e⟩ := hH.quot
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
    exact e.isSimpleGroup
  obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_quotient hf.normalizes hf.pCore hs hf.notCent
  exact ⟨eA.trans e⟩

theorem exists_coords
    (hH : Hyp125 G T L V) (hf : Facts125 G T L V) :
    ∃ (e : ↥V ≃* Multiplicative (Fin 10 → ZMod 2)) (γ : ↥(autOn L V) ≃* SL5),
      ∀ (h : ↥(autOn L V)) (v : ↥V), e ((h : MulAut ↥V) v) =
        Multiplicative.ofAdd (JonesParshall.wedgeRep (γ h) (Multiplicative.toAdd (e v))) := by
  have := hf.comm
  obtain ⟨φ⟩ := lbar_equiv hH hf
  exact exists_wedge_mulEquiv (fun v => Subtype.ext (hf.sq v v.2)) hf.card φ
    (irr_autOn hf.normalizes hf.irr)

omit [Finite G] in
theorem mem_lbar_of_normalizes (e : ↥V ≃* Multiplicative (Fin 10 → ZMod 2))
    (γ : ↥(autOn L V) ≃* SL5)
    (hw : ∀ (h : ↥(autOn L V)) (v : ↥V), e ((h : MulAut ↥V) v) =
      Multiplicative.ofAdd (JonesParshall.wedgeRep (γ h) (Multiplicative.toAdd (e v))))
    {x : MulAut ↥V} (hx : x ∈ Subgroup.normalizer (autOn L V : Set (MulAut ↥V))) :
    x ∈ autOn L V := by
  let c : MulAut ↥(autOn L V) := (autOn L V).normalizerMonoidHom ⟨x, hx⟩
  let β : MulAut SL5 := γ.symm.trans (c.trans γ)
  let E : (Fin 10 → ZMod 2) ≃+ (Fin 10 → ZMod 2) :=
    { toFun := fun y => Multiplicative.toAdd (e (x (e.symm (Multiplicative.ofAdd y))))
      invFun := fun y => Multiplicative.toAdd (e (x.symm (e.symm (Multiplicative.ofAdd y))))
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      map_add' := fun y z => by
        rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul] }
  have hc : ∀ h : ↥(autOn L V), ((c h : ↥(autOn L V)) : MulAut ↥V) = x * h * x⁻¹ := fun h => rfl
  have hE : ∀ (g : SL5) y, E (JonesParshall.wedgeRep g y) =
      JonesParshall.wedgeRep (β g) (E y) := by
    intro g y
    set v := e.symm (Multiplicative.ofAdd y) with hv
    have h1 : Multiplicative.ofAdd (JonesParshall.wedgeRep g y) = e ((γ.symm g : MulAut ↥V) v) := by
      rw [hw, MulEquiv.apply_symm_apply, hv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
    have h2 : x ((γ.symm g : MulAut ↥V) v) = ((c (γ.symm g) : ↥(autOn L V)) : MulAut ↥V) (x v) := by
      rw [hc]
      simp [MulAut.mul_apply]
    change Multiplicative.toAdd (e (x (e.symm (Multiplicative.ofAdd
        (JonesParshall.wedgeRep g y))))) = JonesParshall.wedgeRep (γ (c (γ.symm g)))
      (Multiplicative.toAdd (e (x v)))
    rw [h1, MulEquiv.symm_apply_apply, h2, hw, toAdd_ofAdd]
  obtain ⟨a, ha⟩ := eq_wedgeRep_of_intertwines E β hE
  have hxa : x = ((γ.symm a : ↥(autOn L V)) : MulAut ↥V) := by
    refine MulEquiv.ext fun v => ?_
    apply e.injective
    rw [hw, MulEquiv.apply_symm_apply]
    have h := ha (Multiplicative.toAdd (e v))
    change Multiplicative.toAdd (e (x (e.symm (Multiplicative.ofAdd
      (Multiplicative.toAdd (e v)))))) = _ at h
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply] at h
    rw [← h, ofAdd_toAdd]
  rw [hxa]
  exact (γ.symm a).2

@[expose] noncomputable def wedgeAddEquiv (g : SL5) : (Fin 10 → ZMod 2) ≃+ (Fin 10 → ZMod 2) where
  toFun := JonesParshall.wedgeRep g
  invFun := JonesParshall.wedgeRep g⁻¹
  left_inv := wedgeRep_inv_apply g
  right_inv := wedgeRep_apply_inv g
  map_add' := map_add _

end S125Ex

open S125Ex

theorem frame125Exists_of
    (h1222 : Stmt12_2_2) : Frame125Exists := by
  intro G _ _ T L V hH
  have hf := Facts125.of h1222 hH
  obtain ⟨e₁, γ₁, hw₁⟩ := exists_coords hH hf
  have hTL : ∀ (t : G) (ht : t ∈ T), conjAct V ⟨t, hf.T_le ht⟩ ∈ autOn L V := by
    intro t ht
    have hmem : conjAct V ⟨t, hf.T_le ht⟩ ∈ autOn T V :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
    exact mem_lbar_of_normalizes e₁ γ₁ hw₁
      (autOn_le_normalizer_autOn hf.normalizes hf.T_le hH.hyp.normalizes hmem)
  have hTLe : autOn T V ≤ autOn L V := by
    intro a ha
    obtain ⟨t, ht, htT, rfl⟩ := mem_autOn_iff_exists.mp ha
    exact hTL t htT
  set P₀ : Subgroup SL5 := ((autOn T V).subgroupOf (autOn L V)).map γ₁.toMonoidHom with hP₀
  have hP₀2 : IsPGroup 2 P₀ := by
    have h1 : IsPGroup 2 (autOn T V) := CFSG.Quasithin.isPGroup_autOn hH.hyp.sylow.1 hf.T_le
    have h2 : IsPGroup 2 ((autOn T V).subgroupOf (autOn L V)) :=
      h1.of_equiv (Subgroup.subgroupOfEquivOfLe hTLe).symm
    exact h2.map _
  obtain ⟨Q, hQ⟩ := hP₀2.exists_le_sylow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_unitriangular
    (K := ZMod 2) 2 (n := 5) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL5 U Q
  have hconjU : ∀ y ∈ P₀, g⁻¹ * y * g ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular
      5 (ZMod 2) := by
    intro y hy
    have hyQ : y ∈ (Q : Subgroup SL5) := hQ hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hU] at hyQ
    simpa [MulAut.smul_def, MulAut.conj_inv_apply, mul_assoc] using hyQ
  let γ : ↥(autOn L V) ≃* SL5 := γ₁.trans (MulAut.conj g⁻¹)
  let e : ↥V ≃* Multiplicative (Fin 10 → ZMod 2) :=
    e₁.trans (AddEquiv.toMultiplicative (wedgeAddEquiv g⁻¹))
  have he : ∀ v, e v = Multiplicative.ofAdd (JonesParshall.wedgeRep g⁻¹
      (Multiplicative.toAdd (e₁ v))) := fun v => rfl
  have hγ : ∀ h, γ h = g⁻¹ * γ₁ h * g := fun h => by simp [γ]
  have hw : ∀ (h : ↥(autOn L V)) (v : ↥V), e ((h : MulAut ↥V) v) =
      Multiplicative.ofAdd (JonesParshall.wedgeRep (γ h) (Multiplicative.toAdd (e v))) := by
    intro h v
    rw [he, he, hw₁, toAdd_ofAdd, toAdd_ofAdd, hγ, wedgeRep_mul_apply, wedgeRep_mul_apply,
      wedgeRep_apply_inv]
  refine ⟨⟨e, γ, hw, fun t ht => ?_⟩⟩
  let h : ↥(autOn L V) := ⟨conjAct V ⟨t, hf.T_le ht⟩, hTL t ht⟩
  refine ⟨γ h, ?_, fun v w hvw => ?_⟩
  · have hmem : γ₁ h ∈ P₀ := ⟨h, Subgroup.mem_subgroupOf.2
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)), rfl⟩
    have h1 := hconjU _ hmem
    rw [← hγ] at h1
    exact h1.1
  · have hwv : w = (h : MulAut ↥V) v := Subtype.ext hvw
    rw [hwv, hw]

end CFSG.Quasithin.H13
