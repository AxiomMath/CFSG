module

public import CFSG.Quasithin.H13.NQCoreWholeModule
public import CFSG.Quasithin.H13.NQCoreWholeModuleFrattini
public import CFSG.Quasithin.H13.NQCoreRadicalCentralizerProof
public import CFSG.Quasithin.H13.NQRigidCoreQuot
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open scoped IsMulCommutative

section Ambient

variable {G : Type*} [Group G] {E : Subgroup G} (V : Subgroup ↥E) [IsMulCommutative ↥V]
  [Module (ZMod 2) (Additive ↥V)]

@[expose] noncomputable def ambientConjGL :
    ↥(normalizer ((V.map E.subtype : Subgroup G) : Set G)) →*
      LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V) :=
  (mulAutToGL V).comp ((MulAut.congr (V.equivMapOfInjective E.subtype
    E.subtype_injective).symm).toMonoidHom.comp (V.map E.subtype).normalizerMonoidHom)

theorem ambientConjGL_apply_coe (g : ↥(normalizer ((V.map E.subtype : Subgroup G) : Set G)))
    (v : ↥V) :
    (((Additive.toMul (((ambientConjGL V g : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive ↥V)) : Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul v)) : ↥V) : ↥E) :
        G) = (g : G) * ((v : ↥E) : G) * (g : G)⁻¹ := by
  set e := V.equivMapOfInjective E.subtype E.subtype_injective with he
  have h1 : ∀ w : ↥(V.map E.subtype), (((e.symm w : ↥V) : ↥E) : G) = (w : G) := fun w => by
    conv_rhs => rw [← e.apply_symm_apply w]
    rfl
  change (((e.symm ((V.map E.subtype).normalizerMonoidHom g (e v)) : ↥V) : ↥E) : G) = _
  rw [h1, normalizerMonoidHom_apply_apply_coe]
  rfl

theorem ambientConjGL_mul_conjGL [V.Normal]
    (g : ↥(normalizer ((V.map E.subtype : Subgroup G) : Set G))) {x x' : ↥E}
    (hx : (x' : G) = (g : G) * (x : G) * (g : G)⁻¹) :
    ambientConjGL V g * conjGL V x = conjGL V x' * ambientConjGL V g := by
  apply Units.ext
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ : ∃ v : ↥V, Additive.ofMul v = w := ⟨Additive.toMul w, rfl⟩
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, conjGL_apply]
  set u : ↥V := Additive.toMul (((ambientConjGL V g : LinearMap.GeneralLinearGroup (ZMod 2)
    (Additive ↥V)) : Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul v)) with hu
  have hu' : ((u : ↥E) : G) = (g : G) * ((v : ↥E) : G) * (g : G)⁻¹ :=
    ambientConjGL_apply_coe V g v
  change _ = ((conjGL V x' : LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) :
    Additive ↥V →ₗ[ZMod 2] Additive ↥V) (Additive.ofMul u)
  rw [conjGL_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [ambientConjGL_apply_coe]
  simp only [toMul_ofMul, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv, hu', hx]
  group

end Ambient

theorem stmtWholeModuleComparison_of
    (hA7u : U3.SylowNormalizedMaximalLocalUniqueNormalizer)
    (hA7n : NQBlock.SylowNormalizedLocalNormalComponent) : StmtWholeModuleComparison := by
  intro G _ _ T L M D X p hX hne
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp := hX.prime
  have : Fact p.Prime := ⟨hp⟩
  have h := hX.qtnq
  obtain ⟨-, hC⟩ := SNCanonical.of_qtTMaxNQPrime hA7u hA7n hX
  have hTD : T ≤ normalizer (D : Set G) := hX.le_normalizer
  have hTX : T ≤ normalizer (X : Set G) := hC.normalizer_eq ▸ hTD
  have hDX : D ≤ normalizer (X : Set G) := hC.normalizer_eq ▸ le_normalizer
  have hXE : X ≤ X ⊔ T := le_sup_left
  have hTE : T ≤ X ⊔ T := le_sup_right
  have hXn : (X.subgroupOf (X ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXE).mpr (sup_le le_normalizer hTX)
  have hT2 : IsPGroup 2 ↥(T.subgroupOf (X ⊔ T)) :=
    h.sylow.1.of_equiv (subgroupOfEquivOfLe hTE).symm
  have hT2i : ¬ 2 ∣ (T.subgroupOf (X ⊔ T)).index := fun hd =>
    h.sylow.2 (hd.trans (relIndex_dvd_index_of_le hTE))
  set Ts : Sylow 2 ↥(X ⊔ T) := hT2.toSylow hT2i with hTs
  have hXT : X.subgroupOf (X ⊔ T) ⊔ (Ts : Subgroup ↥(X ⊔ T)) = ⊤ := by
    rw [hTs, IsPGroup.toSylow_coe, ← subgroupOf_sup hXE hTE, subgroupOf_self]
  have hXmap : (X.subgroupOf (X ⊔ T)).map (X ⊔ T).subtype = X := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hXE]
  have hVne : ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆ ≠ ⊥ := by
    have hchief : ∀ B A : Subgroup ↥X, CFSG.IsChiefFactor B A → CFSG.pCore 2 ↥X ≤ B →
        (∃ n : ℕ, B.relIndex A = 2 ^ n) → ⁅A, ⊤⁆ ≤ B := by
      rintro B A hBA hqB ⟨n, hn⟩
      exfalso
      have : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hC.isPGroup
      have h1 : 2 ^ n ∣ p ^ k := by
        rw [← hn, ← hk, ← index_eq_card]
        exact (relIndex_dvd_of_le_left (L := A) hqB).trans (relIndex_dvd_index_of_normal _ _)
      have hn0 : n = 0 := by
        by_contra hn0
        have h2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow ((dvd_pow_self 2 hn0).trans h1)
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
        have := hX.five_le
        omega
      rw [hn0, pow_zero, relIndex_eq_one] at hn
      exact lt_irrefl B (hBA.lt.trans_le hn)
    have h1 := (reduced_witness_of_le hXE hXn hC.noTwoQuotient).2 hchief hne
    have hc : (⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆).map (X ⊔ T).subtype =
        ⁅(primeReducedAggregate ↥(X ⊔ T) 2).map (X ⊔ T).subtype, X⁆ := by
      rw [map_commutator, hXmap]
    intro hb
    apply h1
    rw [← hc, hb, Subgroup.map_bot]
  set eQ := NQRigid.coreQuotEquivOfLe hXE with heQ
  have hcompat : ∀ (d : normalizer (X : Set G)) (hdE : (d : G) ∈ X ⊔ T)
      (x : ↥(X.subgroupOf (X ⊔ T))),
      NQRigid.frattiniEquivSubgroupOf hXE (((MulAut.conjNormal (⟨d, hdE⟩ : ↥(X ⊔ T)) x :
        ↥(X.subgroupOf (X ⊔ T))) : ↥(X.subgroupOf (X ⊔ T)) ⧸
          CFSG.pCore 2 ↥(X.subgroupOf (X ⊔ T))) : (↥(X.subgroupOf (X ⊔ T)) ⧸
          CFSG.pCore 2 ↥(X.subgroupOf (X ⊔ T))) ⧸ frattini (↥(X.subgroupOf (X ⊔ T)) ⧸
          CFSG.pCore 2 ↥(X.subgroupOf (X ⊔ T)))) =
        normalizerFrattiniConj X d (NQRigid.frattiniEquivSubgroupOf hXE
          (((x : ↥(X.subgroupOf (X ⊔ T)) ⧸ CFSG.pCore 2 ↥(X.subgroupOf (X ⊔ T))) :
            (↥(X.subgroupOf (X ⊔ T)) ⧸ CFSG.pCore 2 ↥(X.subgroupOf (X ⊔ T))) ⧸
              frattini (↥(X.subgroupOf (X ⊔ T)) ⧸ CFSG.pCore 2 ↥(X.subgroupOf (X ⊔ T)))))) := by
    intro d hdE x
    rw [NQRigid.frattiniEquivSubgroupOf_mk hXE, NQRigid.frattiniEquivSubgroupOf_mk hXE,
      NQRigid.normalizerFrattiniConj_mk_mk, NQRigid.subgroupOfEquivOfLe_conjNormal]
  obtain ⟨hUZ, hBΦ, hV2, hTC, hVn, hVc, hGL⟩ := whole_module_core Ts hXT hp hX.five_le
    (NQRigid.isPGroup_coreQuot_subgroupOf hXE hC.isPGroup)
    (by
      rw [Nat.card_congr eQ.toEquiv]
      rcases hC.shape with ⟨hab, hcard⟩ | ⟨hnab, hcard⟩
      · exact Or.inl ⟨eQ.symm.surjective.isMulCommutative hab, hcard⟩
      · exact Or.inr ⟨fun hab => hnab (eQ.surjective.isMulCommutative hab), hcard⟩)
    (by rw [Monoid.exponent_eq_of_mulEquiv eQ, hC.exponent])
    (by rw [NQRigid.card_frattini_subgroupOf hXE, hC.card_W])
    (by
      intro U hU
      rcases hC.irreducible_T (U.map (NQRigid.frattiniEquivSubgroupOf hXE).toMonoidHom) (by
        rintro d hdT _ ⟨w, hw, rfl⟩
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
        exact ⟨_, hU ⟨d, hTE hdT⟩ hdT x hw, hcompat d (hTE hdT) x⟩) with h0 | ht
      · exact Or.inl ((map_eq_bot_iff_of_injective U
          (NQRigid.frattiniEquivSubgroupOf hXE).injective).mp h0)
      · refine Or.inr (eq_top_iff.mpr fun w _ => ?_)
        have h1 : NQRigid.frattiniEquivSubgroupOf hXE w ∈
            U.map (NQRigid.frattiniEquivSubgroupOf hXE).toMonoidHom := ht ▸ mem_top _
        obtain ⟨w', hw', hww⟩ := h1
        rwa [← (NQRigid.frattiniEquivSubgroupOf hXE).injective hww])
    rfl hVne
  set V := ⁅primeReducedAggregate ↥(X ⊔ T) 2, X.subgroupOf (X ⊔ T)⁆ with hVdef
  refine ⟨hVne, hV2, hTC, hVn, hVc, ?_⟩
  intro _
  obtain ⟨hsolv, hO2, h3, hPn, hΓP, hshapeV, hspan, hirrV⟩ := hGL
  refine ⟨hsolv, hO2, h3, hPn, hΓP, hshapeV, hspan, hirrV, ?_⟩
  obtain ⟨y, -, hyR, hyW⟩ := exists_mem_normalizer_pCoreOf_not_two_power h.sylow hTD
    hX.maximal_local.1.2.1.2.1 hC.le (sup_le hDX hTX) hC.nontrivial
  have hEmap : (CFSG.pCore 2 ↥(X ⊔ T)).map (X ⊔ T).subtype = pCoreOf 2 (X ⊔ T) := by
    rw [pCoreOf]
  have hVg : V.map (X ⊔ T).subtype =
      ⁅BlueprintB2.centerTorsion 2 (pCoreOf 2 (X ⊔ T)), X⁆ := by
    rw [hVdef, map_commutator, hUZ, BlueprintB2.map_centerTorsion _ (X ⊔ T).subtype_injective,
      hEmap, hXmap]
  have hyV : (y : G) ∈ normalizer ((V.map (X ⊔ T).subtype : Subgroup G) : Set G) := by
    have hyR' := LieType.Steinberg.mem_normalizer_iff_map_conj.mp hyR
    have hyX' := LieType.Steinberg.mem_normalizer_iff_map_conj.mp y.2
    rw [hVg, LieType.Steinberg.mem_normalizer_iff_map_conj, map_commutator,
      BlueprintB2.map_centerTorsion (MulAut.conj (y : G)).toMonoidHom
        (MulAut.conj (y : G)).injective, hyR', hyX']
  set yV : ↥(normalizer ((V.map (X ⊔ T).subtype : Subgroup G) : Set G)) := ⟨y, hyV⟩ with hyVdef
  refine ⟨ambientConjGL V yV, ?_, fun k hk => hyW k ?_⟩
  ·
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (y : G) * (x : G) * (y : G)⁻¹ ∈ X := (mem_normalizer_iff.mp y.2 _).mp hx
    refine ⟨⟨_, hXE hx'⟩, hx', ?_⟩
    exact (mul_inv_eq_of_eq_mul (ambientConjGL_mul_conjGL V yV (x := x)
      (x' := ⟨_, hXE hx'⟩) rfl)).symm
  ·
    rw [← map_pow]
    have hφz : ambientConjGL V yV ^ 2 ^ k = ambientConjGL V (yV ^ 2 ^ k) := (map_pow _ _ _).symm
    have hzG : ((yV ^ 2 ^ k : ↥(normalizer ((V.map (X ⊔ T).subtype : Subgroup G) : Set G))) :
        G) = ((y ^ 2 ^ k : ↥(normalizer (X : Set G))) : G) := by
      rw [Subgroup.coe_pow, Subgroup.coe_pow]
    ext w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective w
    rw [NQRigid.normalizerFrattiniConj_mk_mk, MulAut.one_apply]
    have hx'X : ((y ^ 2 ^ k : ↥(normalizer (X : Set G))) : G) * (x0 : G) *
        ((y ^ 2 ^ k : ↥(normalizer (X : Set G))) : G)⁻¹ ∈ X :=
      (mem_normalizer_iff.mp (y ^ 2 ^ k).2 _).mp x0.2
    obtain ⟨a', ha'⟩ : ∃ a' : ↥(X.subgroupOf (X ⊔ T)), ((a' : ↥(X ⊔ T)) : G) =
        ((y ^ 2 ^ k : ↥(normalizer (X : Set G))) : G) * (x0 : G) *
          ((y ^ 2 ^ k : ↥(normalizer (X : Set G))) : G)⁻¹ := ⟨⟨⟨_, hXE hx'X⟩, hx'X⟩, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : ↥(X.subgroupOf (X ⊔ T)), ((a : ↥(X ⊔ T)) : G) = (x0 : G) :=
      ⟨⟨⟨x0, hXE x0.2⟩, x0.2⟩, rfl⟩
    have hρ : conjGL V (a' : ↥(X ⊔ T)) = conjGL V (a : ↥(X ⊔ T)) := by
      have h1 := ambientConjGL_mul_conjGL V (yV ^ 2 ^ k) (x := (a : ↥(X ⊔ T)))
        (x' := (a' : ↥(X ⊔ T))) (by rw [ha', ha, hzG])
      have h2 := hk (conjGL V (a : ↥(X ⊔ T))) ⟨(a : ↥(X ⊔ T)), a.2, rfl⟩
      rw [hφz, h1] at h2
      exact mul_right_cancel h2
    have hker : ((a' * a⁻¹ : ↥(X.subgroupOf (X ⊔ T))) : ↥(X ⊔ T)) ∈
        centralizer (V : Set ↥(X ⊔ T)) := by
      rw [← ker_conjGL V, MonoidHom.mem_ker, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
        map_inv, hρ, mul_inv_cancel]
    have hΦ := hBΦ (mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥(X.subgroupOf (X ⊔ T))))
      (mem_subgroupOf.mpr (mem_inf.mpr ⟨(a' * a⁻¹).2, hker⟩)))
    have h4 : X.normalizerMonoidHom (y ^ 2 ^ k) x0 = subgroupOfEquivOfLe hXE a' :=
      Subtype.ext (by rw [normalizerMonoidHom_apply_apply_coe]; exact ha'.symm)
    have h5 : subgroupOfEquivOfLe hXE a = x0 := Subtype.ext ha
    rw [h4, ← h5, ← NQRigid.frattiniEquivSubgroupOf_mk hXE a',
      ← NQRigid.frattiniEquivSubgroupOf_mk hXE a]
    congr 1
    rw [QuotientGroup.eq_iff_div_mem, ← QuotientGroup.mk_div, div_eq_mul_inv]
    exact hΦ

end CFSG.Quasithin.H13.NQCore
